#!/usr/bin/env python3
"""
unseed.py - verified Java classfile surgery, with a caller-seeded string
extractor as the worked example.

This is NOT a general Java deobfuscator. It does not undo Zelix, Stringer,
Allatori or ProGuard, rename classes, or restore source structure. It defeats
exactly one string-encryption scheme (caller-seeded pairwise XOR, described
above `extract_decryptor`) and reports anything else as "not handled".

Reusable pieces, independent of that scheme:
  * a modified-UTF-8 codec that matches the JVM exactly (NUL is 0xC0 0x80,
    supplementary characters are CESU-8 surrogate pairs);
  * an instruction decoder cross-validated against `javap`;
  * a length-preserving patcher (`ldc_w <const>` + `nop` padding), so branch
    offsets, StackMapTable frames, exception ranges and line numbers stay valid.

Design rule: loud failure over silent guessing. Anything unrecognised raises
`UnseedError`; nothing returns a plausible-looking answer. See README.md.

Usage:
    python3 -I unseed.py selftest
    python3 -I unseed.py scan     INPUT [--json F]
    python3 -I unseed.py strings  INPUT [--json F] [--report F] [--grep PAT]
    python3 -I unseed.py indy     INPUT [--json F] [--worklist F] [--show-resolved]
    python3 -I unseed.py patch    INPUT --out DIR [--json F] [--copy-all]
    python3 -I unseed.py verify   INPUT [--reference F] [--ground-truth S]
                                  [--javap-check N] [--javap-attrib N] [--strict]

INPUT is a .jar/.zip or a directory tree of .class files.

Layout of this file, top to bottom:
    1. constants and errors            8. decryption
    2. modified UTF-8 / UTF-16         9. call-site scan
    3. opcode table and decoder       10. patching
    4. ClassFile                      11. invokedynamic census
    5. ClassSource                    12. self-test and fixture control
    6. the stack interpreter          13. reports and javap cross-checks
    7. decryptor extraction           14. command-line interface
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import re
import struct
import subprocess
import sys
import tempfile
import zipfile
from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import TypedDict

# ==========================================================================
# 1. constants and errors
# ==========================================================================

TOOL_DIR = os.path.dirname(os.path.abspath(__file__))

ACC_STATIC = 0x0008
ACC_NATIVE = 0x0100

STRING_TO_STRING = '(Ljava/lang/String;)Ljava/lang/String;'


class UnseedError(Exception):
    """A shape this tool refuses to guess about."""


# ==========================================================================
# 2. modified UTF-8 (JVM constant pool encoding) and UTF-16 code units
# ==========================================================================

def _combine_surrogates(units, what: str) -> str:
    """UTF-16 code units -> str, joining surrogate pairs.

    Raises on a lone surrogate instead of mangling it: silently substituting a
    replacement character is exactly the failure this tool exists to avoid.
    """
    res = []
    j = 0
    while j < len(units):
        u = units[j]
        if 0xD800 <= u <= 0xDBFF:
            if j + 1 < len(units) and 0xDC00 <= units[j + 1] <= 0xDFFF:
                res.append(chr(0x10000 + ((u - 0xD800) << 10) + (units[j + 1] - 0xDC00)))
                j += 2
                continue
            raise UnseedError(f'lone high surrogate U+{u:04X} in {what}')
        if 0xDC00 <= u <= 0xDFFF:
            raise UnseedError(f'lone low surrogate U+{u:04X} in {what}')
        res.append(chr(u))
        j += 1
    return ''.join(res)


def dec_modified_utf8(b: bytes) -> str:
    """Decode CONSTANT_Utf8 exactly as the JVM specifies. Raises on malformed input.

    Plain `bytes.decode('utf-8', 'replace')` is WRONG here: these ciphertexts are
    arbitrary char sequences, so they contain 0xC0 0x80 (encoded NUL) and CESU-8
    surrogate pairs, both of which 'replace' turns into U+FFFD and silently
    changes the plaintext.
    """
    units = []
    i, n = 0, len(b)

    def is_cont(k: int) -> bool:
        return k < n and 0x80 <= b[k] < 0xC0

    while i < n:
        c = b[i]
        if c == 0:
            raise UnseedError(f'raw 0x00 in CONSTANT_Utf8 at byte {i}')
        if c < 0x80:
            units.append(c)
            i += 1
        elif c < 0xC0:
            raise UnseedError(f'stray continuation byte {c:#x} at {i}')
        elif c < 0xE0:
            if not is_cont(i + 1):
                raise UnseedError(f'truncated 2-byte form at {i}')
            units.append(((c & 0x1F) << 6) | (b[i + 1] & 0x3F))
            i += 2
        elif c < 0xF0:
            if not (is_cont(i + 1) and is_cont(i + 2)):
                raise UnseedError(f'truncated 3-byte form at {i}')
            units.append(((c & 0x0F) << 12) | ((b[i + 1] & 0x3F) << 6) | (b[i + 2] & 0x3F))
            i += 3
        else:
            raise UnseedError(f'4-byte form {c:#x} is not valid modified UTF-8 at {i}')
    return _combine_surrogates(units, 'CONSTANT_Utf8')


def enc_modified_utf8(s: str) -> bytes:
    """Inverse of `dec_modified_utf8`."""
    out = bytearray()
    for ch in s:
        cp = ord(ch)
        if cp == 0:
            out += b'\xc0\x80'                       # NUL is 0xC0 0x80, never 0x00
        elif cp < 0x80:
            out.append(cp)
        elif cp < 0x800:
            out += bytes((0xC0 | (cp >> 6), 0x80 | (cp & 0x3F)))
        elif cp < 0x10000:
            out += bytes((0xE0 | (cp >> 12), 0x80 | ((cp >> 6) & 0x3F), 0x80 | (cp & 0x3F)))
        else:
            v = cp - 0x10000
            for u in (0xD800 + (v >> 10), 0xDC00 + (v & 0x3FF)):
                out += bytes((0xE0 | (u >> 12), 0x80 | ((u >> 6) & 0x3F), 0x80 | (u & 0x3F)))
    return bytes(out)


def to_utf16_units(s: str) -> list:
    """Python str -> list of UTF-16 code units (what Java `charAt` indexes)."""
    raw = s.encode('utf-16-be')
    return list(struct.unpack('>%dH' % (len(raw) // 2), raw))


def from_utf16_units(units) -> str:
    """Code units -> Python str. Raises on a lone surrogate."""
    return _combine_surrogates(units, 'plaintext')


# ==========================================================================
# 3. opcode table and instruction decoder
# ==========================================================================
# Operand formats:
#   ''     none               'b'  int8            'B'    uint8
#   'bb'   uint8, int8        's'  int16           'u2'   constant-pool index
#   'o2'   int16 branch       'i4' int32 branch    'u2bb' invokeinterface/dynamic
#   'u2b'  multianewarray     'switch' | 'wide'    (variable length)

# struct layout of the operand bytes, for the fixed-length formats.
_FIXED_OPERANDS = {'': '>', 'b': '>b', 'B': '>B', 'bb': '>Bb', 's': '>h', 'u2': '>H',
                   'o2': '>h', 'i4': '>i', 'u2bb': '>HBB', 'u2b': '>HB'}

# Minimum total instruction length per format, opcode byte included. 'switch' and
# 'wide' are variable-length, so this records only the bytes their length
# calculation must be able to read.
FMT_MIN_LEN = {fmt: 1 + struct.calcsize(layout) for fmt, layout in _FIXED_OPERANDS.items()}
FMT_MIN_LEN.update({'switch': 5, 'wide': 2})

OPS: dict = {}                      # opcode byte -> (mnemonic, operand format)


def _op(code: int, name: str, fmt: str = '') -> None:
    assert code not in OPS, f'duplicate opcode {code:#x}'
    OPS[code] = (name, fmt)


def _ops(base: int, names, fmt: str = '', stride: int = 1) -> None:
    """Register consecutive opcodes `base`, `base+stride`, ... under `names`."""
    for i, name in enumerate(names):
        _op(base + i * stride, name, fmt)


_op(0x00, 'nop')
_op(0x01, 'aconst_null')
_ops(0x02, ['iconst_m1'] + [f'iconst_{v}' for v in range(6)])
_ops(0x09, ['lconst_0', 'lconst_1'])
_ops(0x0B, ['fconst_0', 'fconst_1', 'fconst_2'])
_ops(0x0E, ['dconst_0', 'dconst_1'])
_op(0x10, 'bipush', 'b')
_op(0x11, 'sipush', 's')
_op(0x12, 'ldc', 'B')
_op(0x13, 'ldc_w', 'u2')
_op(0x14, 'ldc2_w', 'u2')
_ops(0x15, [f'{t}load' for t in 'ilfda'], 'B')
for _t, _base in zip('ilfda', (0x1A, 0x1E, 0x22, 0x26, 0x2A)):
    _ops(_base, [f'{_t}load_{i}' for i in range(4)])
_ops(0x2E, [f'{t}aload' for t in ('i', 'l', 'f', 'd', 'a', 'b', 'c', 's')])
_ops(0x36, [f'{t}store' for t in 'ilfda'], 'B')
for _t, _base in zip('ilfda', (0x3B, 0x3F, 0x43, 0x47, 0x4B)):
    _ops(_base, [f'{_t}store_{i}' for i in range(4)])
_ops(0x4F, [f'{t}astore' for t in ('i', 'l', 'f', 'd', 'a', 'b', 'c', 's')])
_ops(0x57, ['pop', 'pop2', 'dup', 'dup_x1', 'dup_x2', 'dup2', 'dup2_x1', 'dup2_x2', 'swap'])
# add/sub/mul/div/rem/neg: the four types are interleaved, four opcodes apart.
for _off, _t in enumerate('ilfd'):
    _ops(0x60 + _off, [f'{_t}{o}' for o in ('add', 'sub', 'mul', 'div', 'rem', 'neg')],
         stride=4)
# Shifts are grouped by OPERATION with the int/long variants adjacent
# (ishl, lshl, ishr, lshr, iushr, lushr), NOT by type. Reading this range as
# "all four int shifts then all four long shifts" is an easy and silent slip:
# it misnames four of six opcodes, and because ishr/lshl differ in both signedness
# and operand category the interpreter then pops the wrong stack width.
# Verified against javap and against javac's own codegen for >> / >>> / <<.
_ops(0x78, ['ishl', 'lshl', 'ishr', 'lshr', 'iushr', 'lushr',
            'iand', 'land', 'ior', 'lor', 'ixor', 'lxor'])
_op(0x84, 'iinc', 'bb')
_ops(0x85, ['i2l', 'i2f', 'i2d', 'l2i', 'l2f', 'l2d', 'f2i', 'f2l',
            'f2d', 'd2i', 'd2l', 'd2f', 'i2b', 'i2c', 'i2s'])
_ops(0x94, ['lcmp', 'fcmpl', 'fcmpg', 'dcmpl', 'dcmpg'])
_ops(0x99, ['ifeq', 'ifne', 'iflt', 'ifge', 'ifgt', 'ifle',
            'if_icmpeq', 'if_icmpne', 'if_icmplt', 'if_icmpge', 'if_icmpgt', 'if_icmple',
            'if_acmpeq', 'if_acmpne', 'goto', 'jsr'], 'o2')
_op(0xA9, 'ret', 'B')
_op(0xAA, 'tableswitch', 'switch')
_op(0xAB, 'lookupswitch', 'switch')
_ops(0xAC, ['ireturn', 'lreturn', 'freturn', 'dreturn', 'areturn', 'return'])
_ops(0xB2, ['getstatic', 'putstatic', 'getfield', 'putfield',
            'invokevirtual', 'invokespecial', 'invokestatic'], 'u2')
_op(0xB9, 'invokeinterface', 'u2bb')
_op(0xBA, 'invokedynamic', 'u2bb')
_op(0xBB, 'new', 'u2')
_op(0xBC, 'newarray', 'B')
_op(0xBD, 'anewarray', 'u2')
_op(0xBE, 'arraylength')
_op(0xBF, 'athrow')
_op(0xC0, 'checkcast', 'u2')
_op(0xC1, 'instanceof', 'u2')
_op(0xC2, 'monitorenter')
_op(0xC3, 'monitorexit')
_op(0xC4, 'wide', 'wide')
_op(0xC5, 'multianewarray', 'u2b')
_op(0xC6, 'ifnull', 'o2')
_op(0xC7, 'ifnonnull', 'o2')
_op(0xC8, 'goto_w', 'i4')
_op(0xC9, 'jsr_w', 'i4')

BRANCH_OPS = {n for n, f in OPS.values() if f in ('o2', 'i4', 'switch')}

INVOKE_OPS = ('invokevirtual', 'invokespecial', 'invokestatic', 'invokeinterface')
GOTO_OPS = ('goto', 'goto_w', 'jsr', 'jsr_w')
TERMINATORS = frozenset(('return', 'ireturn', 'lreturn', 'freturn', 'dreturn',
                         'areturn', 'athrow'))


class Insn:
    __slots__ = ('off', 'op', 'name', 'fmt', 'operands', 'length', 'target')

    def __init__(self, off, op, name, fmt, operands, length, target=None):
        self.off = off
        self.op = op
        self.name = name
        self.fmt = fmt
        self.operands = operands      # tuple of raw ints
        self.length = length
        self.target = target          # list of absolute branch targets, if any

    def __repr__(self):
        return f'{self.off}:{self.name}{self.operands if self.operands else ""}'


def _switch_len(code: bytes, start: int) -> tuple:
    """Return (total_length, [targets]) for tableswitch/lookupswitch at `start`."""
    pad = (4 - ((start + 1) % 4)) % 4
    p = start + 1 + pad
    default = struct.unpack_from('>i', code, p)[0]
    targets = [start + default]
    if code[start] == 0xAA:                       # tableswitch
        low, high = struct.unpack_from('>ii', code, p + 4)
        if high < low or high - low > 1 << 20:
            raise UnseedError(f'implausible tableswitch range {low}..{high} at {start}')
        for k in range(high - low + 1):
            targets.append(start + struct.unpack_from('>i', code, p + 12 + 4 * k)[0])
        return p + 12 + 4 * (high - low + 1) - start, targets
    npairs = struct.unpack_from('>i', code, p + 4)[0]
    if npairs < 0 or npairs > 1 << 20:
        raise UnseedError(f'implausible lookupswitch npairs {npairs} at {start}')
    for k in range(npairs):
        targets.append(start + struct.unpack_from('>i', code, p + 8 + 8 * k + 4)[0])
    return p + 8 + 8 * npairs - start, targets


def _read_operands(fmt: str, code: bytes, i: int) -> tuple:
    """-> (operands, length, branch_targets_or_None) for the instruction at `i`."""
    if fmt in _FIXED_OPERANDS:
        layout = _FIXED_OPERANDS[fmt]
        operands = struct.unpack_from(layout, code, i + 1) if len(layout) > 1 else ()
        length = 1 + struct.calcsize(layout)
        targets = [i + operands[0]] if fmt in ('o2', 'i4') else None
        return operands, length, targets
    if fmt == 'switch':
        length, targets = _switch_len(code, i)
        return (), length, targets
    if fmt == 'wide':
        op2 = code[i + 1]
        if op2 not in OPS:
            raise UnseedError(f'wide: unknown opcode {op2:#02x} at {i}')
        return (op2,), (6 if op2 == 0x84 else 4), None     # wide iinc has an extra int16
    raise UnseedError(f'unhandled operand format {fmt!r}')


def decode(code: bytes) -> list:
    """Linear decode of a Code attribute body.

    Raises UnseedError on any unknown opcode, any unhandled operand format, and
    any instruction truncated by the end of the Code body. Truncation is checked
    before the operands are read, and the read itself is fenced, so a malformed
    classfile can never escape as a raw struct.error - that would break the
    contract every caller relies on, namely that UnseedError is the only way
    this decoder fails.
    """
    insns = []
    i, n = 0, len(code)
    while i < n:
        op = code[i]
        if op not in OPS:
            raise UnseedError(f'unknown opcode {op:#02x} at bci {i}')
        name, fmt = OPS[op]
        need = FMT_MIN_LEN.get(fmt)
        if need is None:
            raise UnseedError(f'unhandled operand format {fmt!r} at bci {i}')
        if i + need > n:
            raise UnseedError(f'{name} at bci {i} runs past end of code ({n})')
        try:
            operands, length, targets = _read_operands(fmt, code, i)
        except (struct.error, IndexError) as ex:
            raise UnseedError(f'{name} at bci {i} runs past end of code ({n}) '
                              f'while reading its operands') from ex
        if i + length > n:
            raise UnseedError(f'{name} at bci {i} runs past end of code ({n})')
        insns.append(Insn(i, op, name, fmt, operands, length, targets))
        i += length
    return insns


# ==========================================================================
# 4. ClassFile
# ==========================================================================

_CP_NUMBER = {3: ('int', '>i', 4), 4: ('float', '>f', 4),
              5: ('long', '>q', 8), 6: ('double', '>d', 8)}
_CP_ONE_INDEX = {7: 'class', 8: 'string', 16: 'methodtype', 19: 'module', 20: 'package'}
_CP_TWO_INDEX = {9: 'fieldref', 10: 'methodref', 11: 'ifmethodref',
                 12: 'nameandtype', 17: 'dynamic', 18: 'invokedynamic'}
_CP_REF_KINDS = ('fieldref', 'methodref', 'ifmethodref')


class ClassFile:
    """A parsed classfile.

    `cp[i]` is a (kind, a, b) tuple. `methods`/`fields` are dicts with keys
    access, name, desc, attrs (name -> raw bytes) and attr_offs (name -> absolute
    offset of the attribute body).
    """

    def __init__(self, name: str, data: bytes):
        self.name = name              # how it was addressed (zip entry / path)
        self.data = data
        if data[:4] != b'\xca\xfe\xba\xbe':
            raise UnseedError(f'{name}: not a classfile (magic {data[:4].hex()})')
        try:
            self.minor, self.major = struct.unpack_from('>HH', data, 4)
            self._parse_cp()
            self._parse_body()
        except (struct.error, IndexError) as ex:
            raise UnseedError(f'{name}: truncated or malformed classfile ({ex})') from ex

    # -- parsing --
    def _parse_cp(self):
        d = self.data
        count = struct.unpack_from('>H', d, 8)[0]
        self.cp_count = count
        self.cp = [None] * count
        i, p = 1, 10
        while i < count:
            tag = d[p]
            p += 1
            if tag == 1:
                ln = struct.unpack_from('>H', d, p)[0]
                self.cp[i] = ('utf8', d[p + 2:p + 2 + ln], None)   # decoded lazily
                p += 2 + ln
            elif tag in _CP_NUMBER:
                kind, fmt, size = _CP_NUMBER[tag]
                self.cp[i] = (kind, struct.unpack_from(fmt, d, p)[0], None)
                p += size
                if size == 8:
                    i += 1                  # long/double occupy two pool slots
            elif tag in _CP_ONE_INDEX:
                self.cp[i] = (_CP_ONE_INDEX[tag], struct.unpack_from('>H', d, p)[0], None)
                p += 2
            elif tag in _CP_TWO_INDEX:
                a, b = struct.unpack_from('>HH', d, p)
                self.cp[i] = (_CP_TWO_INDEX[tag], a, b)
                p += 4
            elif tag == 15:
                # CONSTANT_MethodHandle: reference_kind u1, reference_index u2.
                # `p` already points past the tag, so the kind is at d[p].
                self.cp[i] = ('methodhandle', d[p], struct.unpack_from('>H', d, p + 1)[0])
                p += 3
            else:
                raise UnseedError(f'{self.name}: bad CP tag {tag} at index {i}')
            i += 1
        self.cp_end = p

    def _parse_body(self):
        d = self.data
        p = self.cp_end
        self.access, this_i, super_i, n_ifaces = struct.unpack_from('>HHHH', d, p)
        p += 8
        self.this = self.class_name(this_i)
        self.super = self.class_name(super_i) if super_i else None
        self.interfaces = [self.class_name(struct.unpack_from('>H', d, p + 2 * k)[0])
                           for k in range(n_ifaces)]
        p += 2 * n_ifaces
        self.fields, p = self._members(p)
        self.methods, p = self._members(p)
        self.attrs, self.class_attr_offs, p = self._attrs(p)
        self.dotted = self.this.replace('/', '.')
        if p != len(d):
            raise UnseedError(f'{self.name}: {len(d) - p} trailing byte(s) after class attrs')

    def _members(self, p):
        cnt = struct.unpack_from('>H', self.data, p)[0]
        p += 2
        out = []
        for _ in range(cnt):
            acc, name_i, desc_i = struct.unpack_from('>HHH', self.data, p)
            p += 6
            attrs, offs, p = self._attrs(p)
            out.append({'access': acc, 'name': self.utf8(name_i),
                        'desc': self.utf8(desc_i), 'attrs': attrs, 'attr_offs': offs})
        return out, p

    def _attrs(self, p):
        d = self.data
        cnt = struct.unpack_from('>H', d, p)[0]
        p += 2
        res, offs = {}, {}
        for _ in range(cnt):
            name_i, ln = struct.unpack_from('>HI', d, p)
            p += 6
            aname = self.utf8(name_i)
            if aname in res:
                raise UnseedError(f'{self.name}: duplicate attribute {aname}')
            res[aname] = d[p:p + ln]
            offs[aname] = p
            p += ln
        return res, offs, p

    # -- constant-pool accessors --
    def _e(self, i):
        if not (0 < i < self.cp_count):
            raise UnseedError(f'{self.name}: CP index {i} out of range')
        e = self.cp[i]
        if e is None:
            raise UnseedError(f'{self.name}: CP index {i} is a wide-slot continuation')
        return e

    def _expect(self, i, *kinds):
        """The pool entry at `i`, which must be one of `kinds`."""
        e = self._e(i)
        if e[0] not in kinds:
            raise UnseedError(f'{self.name}: CP#{i} is {e[0]}, not {"/".join(kinds)}')
        return e

    def utf8(self, i):
        _k, raw, cached = self._expect(i, 'utf8')
        if cached is None:
            cached = dec_modified_utf8(raw)          # decoded on first use, then memoised
            self.cp[i] = ('utf8', raw, cached)
        return cached

    def class_name(self, i):
        return self.utf8(self._expect(i, 'class')[1])

    def string_const(self, i):
        return self.utf8(self._expect(i, 'string')[1])

    def nat(self, i):
        _k, a, b = self._expect(i, 'nameandtype')
        return self.utf8(a), self.utf8(b)

    def ref(self, i):
        """-> (owner_internal, name, desc, kind)"""
        k, a, b = self._expect(i, *_CP_REF_KINDS)
        nm, de = self.nat(b)
        return self.class_name(a), nm, de, k

    def methodhandle(self, i):
        """-> (reference_kind, owner_internal, name, desc)

        Reference kinds 1-4 point at a Fieldref, 5-9 at a (Interface)Methodref.
        An out-of-range kind raises: silently returning '?' is what let a
        constant-pool parsing bug masquerade as "every bootstrap is unknown".
        """
        _k, kind, ref = self._expect(i, 'methodhandle')
        if not 1 <= kind <= 9:
            raise UnseedError(f'{self.name}: CP#{i} has invalid MethodHandle '
                              f'reference_kind {kind}')
        owner, nm, de, rk = self.ref(ref)
        want_field = kind <= 4
        if want_field != (rk == 'fieldref'):
            raise UnseedError(f'{self.name}: CP#{i} kind {kind} needs a '
                              f'{"Fieldref" if want_field else "Methodref"}, got {rk}')
        return kind, owner, nm, de

    def indy(self, i):
        _k, a, b = self._expect(i, 'invokedynamic')
        nm, de = self.nat(b)
        return a, nm, de

    def const_value(self, i):
        """The value an `ldc`/`ldc_w`/`ldc2_w` of CP#i pushes, as (kind, value)."""
        k, v, _ = self._e(i)
        if k in ('int', 'long', 'float', 'double'):
            return k, v
        if k == 'string':
            return 'str', self.utf8(v)
        if k == 'class':
            return 'class', self.utf8(v)
        if k == 'methodtype':
            return 'mtype', self.utf8(v)
        if k == 'methodhandle':
            return ('mhandle',) + self.methodhandle(i)[1:]
        raise UnseedError(f'{self.name}: CP#{i} ({k}) is not an ldc-able constant')

    # -- code and attributes --
    def code_of(self, m):
        """-> (bytecode_bytes, meta_dict) for a method, or (None, {})."""
        raw = m['attrs'].get('Code')
        if raw is None:
            return None, {}
        max_stack, max_locals, clen = struct.unpack_from('>HHI', raw, 0)
        body = raw[8:8 + clen]
        p = 8 + clen
        p += 2 + 8 * struct.unpack_from('>H', raw, p)[0]           # skip exception table
        n_attrs = struct.unpack_from('>H', raw, p)[0]
        p += 2
        sub = {}
        for _ in range(n_attrs):
            name_i, ln = struct.unpack_from('>HI', raw, p)
            sub[self.utf8(name_i)] = raw[p + 6:p + 6 + ln]
            p += 6 + ln
        return body, {'sub': sub, 'max_locals': max_locals, 'max_stack': max_stack,
                      'code_len': clen, 'code_abs_off': m['attr_offs']['Code'] + 8}

    def insns(self, m):
        """-> (decoded instructions or None, meta). None means no Code attribute."""
        body, meta = self.code_of(m)
        if body is None:
            return None, meta
        return decode(body), meta

    def bootstrap_methods(self):
        """-> [(method_handle_cp_index, [static_arg_cp_indexes])]"""
        raw = self.attrs.get('BootstrapMethods')
        if raw is None:
            return []
        p, out = 2, []
        for _ in range(struct.unpack_from('>H', raw, 0)[0]):
            mh, na = struct.unpack_from('>HH', raw, p)
            p += 4
            out.append((mh, [struct.unpack_from('>H', raw, p + 2 * k)[0] for k in range(na)]))
            p += 2 * na
        return out

    @property
    def native_methods(self):
        return {(m['name'], m['desc']) for m in self.methods if m['access'] & ACC_NATIVE}


def load_class(name, data):
    return ClassFile(name, data)


# ==========================================================================
# 5. ClassSource: a jar, or a directory of .class files
# ==========================================================================

class ClassSource:
    def __init__(self, path):
        self.path = os.path.abspath(path)
        self.is_zip = os.path.isfile(self.path) and zipfile.is_zipfile(self.path)
        if self.is_zip:
            self.zf = zipfile.ZipFile(self.path)
            self.entries = [n for n in self.zf.namelist() if n.endswith('.class')]
        else:
            if not os.path.isdir(self.path):
                raise UnseedError(f'{self.path}: not a jar/zip or a directory')
            self.entries = sorted(
                os.path.relpath(os.path.join(root, f), self.path)
                for root, _dirs, files in os.walk(self.path)
                for f in files if f.endswith('.class'))

    def read(self, entry):
        if self.is_zip:
            return self.zf.read(entry)
        with open(os.path.join(self.path, entry), 'rb') as f:
            return f.read()

    def entry_for(self, cfs, internal):
        """The entry name under which class `internal` was loaded into `cfs`."""
        e = internal + '.class'
        if e in cfs:
            return e
        for k, cf in cfs.items():
            if cf.this == internal:
                return k
        raise UnseedError(f'no input entry for {internal}')

    def __len__(self):
        return len(self.entries)


def _report_parse_failures(fails):
    print(f'WARNING: {len(fails)} classfile(s) failed to parse:', file=sys.stderr)
    for e, why in fails[:10]:
        print(f'  {e}: {why}', file=sys.stderr)


def load_all(src: ClassSource, quiet=False):
    """-> (ordered dict entry->ClassFile, list of (entry, reason) failures)."""
    out, fails = {}, []
    for e in src.entries:
        try:
            out[e] = load_class(e, src.read(e))
        except UnseedError as ex:
            fails.append((e, str(ex)))
        except Exception as ex:                      # noqa: BLE001 - report, don't guess
            fails.append((e, f'{type(ex).__name__}: {ex}'))
    if fails and not quiet:
        _report_parse_failures(fails)
    return out, fails


# ==========================================================================
# 6. the small concrete stack machine used ONLY to read a decryptor's constants
# ==========================================================================
# Values are tuples: ('int'|'long'|'float'|'double', v) for concrete numbers,
# ('sym', tag) for anything opaque, ('st', 'ClassName'|'MethodName') for a
# StackTraceElement getter result, ('buf', [parts]) for a StringBuffer under
# construction, ('seed', [parts]) for a finished seed string, ('new', cls, id)
# for an uninitialised objectref, ('null',).
#
# Nothing here guesses: every unimplemented opcode and every shape mismatch
# raises UnseedError. That is deliberate - the characteristic failure mode of a
# hand-written JVM interpreter is that one opcode-table slip yields wrong
# constants and no error at all, surfacing much later as a wrong string in an
# unrelated place.
#
# The stack holds one entry per VALUE, not per slot; `_w` gives a value's width
# so the dup/pop2 family can tell category-1 from category-2 operands.

MAX_INTERP_STEPS = 200_000
MAX_MASK_SEARCH_STEPS = 20_000
MAX_MASK_SEARCH_PATHS = 64

CAT2 = ('long', 'double')

# The seed is built with one of these; append/insert return their own receiver type.
BUFFER_CLASSES = ('java/lang/StringBuffer', 'java/lang/StringBuilder')


def parse_desc(desc):
    """'(Ljava/lang/Object;JJ)V' -> (['Ljava/lang/Object;','J','J'], 'V')"""
    if not desc.startswith('('):
        raise UnseedError(f'malformed method descriptor {desc!r}')
    i, args = 1, []
    while i < len(desc) and desc[i] != ')':
        j = i
        while desc[j] == '[':
            j += 1
            if j >= len(desc):
                raise UnseedError(f'truncated array type in {desc!r}')
        j = desc.index(';', j) + 1 if desc[j] == 'L' else j + 1
        args.append(desc[i:j])
        i = j
    if i >= len(desc) or desc[i] != ')':
        raise UnseedError(f'unterminated args in {desc!r}')
    return args, desc[i + 1:]


def cat2(t):
    return t in ('J', 'D')


def _w(v):
    return 2 if v[0] in CAT2 else 1


def wrap32(x):
    """Wrap a Python int into the signed 32-bit range, as Java int arithmetic does."""
    return ((x + 0x80000000) & 0xFFFFFFFF) - 0x80000000


# Integer binary operators, on Python ints (the caller wraps to 32 bits). Division
# by zero yields None, which the interpreter models as an opaque value.
_INT_BINOPS = {
    'iadd': lambda a, b: a + b, 'isub': lambda a, b: a - b, 'imul': lambda a, b: a * b,
    'ishl': lambda a, b: a << (b & 0x1F), 'ishr': lambda a, b: a >> (b & 0x1F),
    'iushr': lambda a, b: (a & 0xFFFFFFFF) >> (b & 0x1F),
    'iand': lambda a, b: a & b, 'ior': lambda a, b: a | b, 'ixor': lambda a, b: a ^ b,
    'idiv': lambda a, b: a // b if b else None,
    'irem': lambda a, b: a % b if b else None,
}

# long/float/double ops the decryptor prologue may contain but whose *values* we do
# not need: they are modelled as opaque, popping the right number of operands.
_OPAQUE_BINARY = ('ladd', 'lsub', 'lmul', 'ldiv', 'lrem', 'land', 'lor', 'lxor',
                  'lshl', 'lshr', 'lushr', 'fadd', 'fsub', 'fmul', 'fdiv', 'frem',
                  'dadd', 'dsub', 'dmul', 'ddiv', 'drem')
_OPAQUE_UNARY = ('lneg', 'fneg', 'dneg', 'f2l', 'f2d', 'l2f', 'l2d', 'd2f', 'd2l')

_ARRAY_LOADS = tuple(f'{t}aload' for t in 'ilfdabcs')
_ARRAY_STORES = tuple(f'{t}astore' for t in 'ilfdabcs')
_IF_ONE_OPERAND = ('ifeq', 'ifne', 'iflt', 'ifge', 'ifgt', 'ifle', 'ifnull', 'ifnonnull',
                   'tableswitch', 'lookupswitch')
_IF_TWO_OPERANDS = ('if_icmpeq', 'if_icmpne', 'if_icmplt', 'if_icmpge', 'if_icmpgt',
                    'if_icmple', 'if_acmpeq', 'if_acmpne')

# mnemonic -> handler(interp, insn). Filled in by @_handles below.
_HANDLERS: dict = {}


def _handles(*names):
    def register(fn):
        for n in names:
            assert n not in _HANDLERS, f'duplicate interpreter handler for {n}'
            _HANDLERS[n] = fn
        return fn
    return register


def _names_matching(pattern: str):
    rx = re.compile(pattern)
    return [n for n, _f in OPS.values() if rx.fullmatch(n)]


class Interp:
    def __init__(self, cf, nargs_locals):
        self.cf = cf
        self.locals = [('sym', f'arg{i}') for i in range(nargs_locals)]
        self.stack = []
        self.newid = 0
        self.mask_events = []          # [(bci, value, local_or_None)]
        self.steps = 0

    def fail(self, msg):
        return UnseedError(f'{self.cf.dotted}: {msg}')

    # -- stack plumbing (category aware) --
    def push(self, v):
        self.stack.append(v)

    def push_all(self, *vs):
        self.stack.extend(vs)

    def pop(self):
        if not self.stack:
            raise self.fail('stack underflow')
        return self.stack.pop()

    def pop1(self):
        v = self.pop()
        if _w(v) != 1:
            raise self.fail(f'expected a category-1 value, got {v[0]}')
        return v

    def top_is_wide(self):
        return bool(self.stack) and _w(self.stack[-1]) == 2

    def as_int(self, v):
        """Concrete int, or None if not statically known."""
        return v[1] if v[0] == 'int' else None

    def local(self, idx):
        if idx >= len(self.locals):
            raise self.fail(f'load of unallocated local {idx}')
        return self.locals[idx]

    def snapshot(self):
        """Capture state so the mask search can explore both arms of a branch."""
        return (list(self.stack), list(self.locals), list(self.mask_events), self.newid)

    def restore(self, snap):
        self.stack, self.locals, self.mask_events, self.newid = (
            list(snap[0]), list(snap[1]), list(snap[2]), snap[3])

    def seed_part(self, v):
        return v[1] if v[0] == 'st' else '?' + v[0]

    def _origin_of(self, v):
        """Best-effort: was this value loaded from a local? (for reporting only)"""
        for idx, lv in enumerate(self.locals):
            if lv is v:
                return idx
        return None

    def step(self, ins):
        self.steps += 1
        if self.steps > MAX_INTERP_STEPS:
            raise self.fail('interpreter step budget exceeded')
        handler = _HANDLERS.get(ins.name)
        if handler is None:
            raise self.fail(f'interpreter does not implement `{ins.name}` at bci {ins.off}')
        handler(self, ins)

    # ---- constants / loads / stores ----
    @_handles('nop', 'goto', 'goto_w', 'ret', 'return', 'checkcast')
    def _op_noop(self, ins):
        """No stack effect. (For goto/ret the WALKER decides where to go; for
        checkcast the value stays and its type is not tracked.)"""

    @_handles('aconst_null')
    def _op_aconst_null(self, ins):
        self.push(('null',))

    @_handles(*_names_matching(r'[ilfd]const_\w+'))
    def _op_const(self, ins):
        kind = {'i': 'int', 'l': 'long', 'f': 'float', 'd': 'double'}[ins.name[0]]
        text = ins.name[7:]
        value = -1 if text == 'm1' else (float(text) if kind in ('float', 'double')
                                         else int(text))
        self.push((kind, value))

    @_handles('bipush', 'sipush')
    def _op_push_int(self, ins):
        self.push(('int', ins.operands[0]))

    @_handles('ldc', 'ldc_w', 'ldc2_w')
    def _op_ldc(self, ins):
        kind, val = self.cf.const_value(ins.operands[0])
        self.push((kind, val) if kind in ('int', 'long', 'float', 'double')
                  else ('sym', kind))

    @staticmethod
    def _local_index(ins):
        """Index from the `_N` suffix of `iload_2`, else from the operand byte."""
        suffix = ins.name.rpartition('_')[2]
        return int(suffix) if suffix.isdigit() else ins.operands[0]

    @_handles(*_names_matching(r'[ildfa]load(_\d)?'))
    def _op_load(self, ins):
        self.push(self.local(self._local_index(ins)))

    @_handles(*_names_matching(r'[ildfa]store(_\d)?'))
    def _op_store(self, ins):
        idx = self._local_index(ins)
        v = self.pop()
        while len(self.locals) <= idx:
            self.locals.append(('sym', 'unused'))
        self.locals[idx] = v

    @_handles('iinc')
    def _op_iinc(self, ins):
        idx, delta = ins.operands
        cur = self.as_int(self.local(idx))
        # The loop's index/seed locals are symbolic (they derive from a runtime
        # String.length), so iinc must propagate opacity instead of demanding a
        # constant. Only the MASK locals need to be concrete.
        self.locals[idx] = (('int', wrap32(cur + delta)) if cur is not None
                            else ('sym', 'iinc'))

    # ---- stack manipulation ----
    @_handles('pop')
    def _op_pop(self, ins):
        self.pop1()

    @_handles('pop2')
    def _op_pop2(self, ins):
        if self.top_is_wide():
            self.pop()
        else:
            self.pop1()
            self.pop1()

    @_handles('dup')
    def _op_dup(self, ins):
        v = self.pop1()
        self.push_all(v, v)

    @_handles('dup_x1')
    def _op_dup_x1(self, ins):
        v1, v2 = self.pop1(), self.pop1()
        self.push_all(v1, v2, v1)

    @_handles('dup_x2')
    def _op_dup_x2(self, ins):
        v1 = self.pop1()
        if self.top_is_wide():
            v2 = self.pop()
            self.push_all(v1, v2, v1)
        else:
            v2, v3 = self.pop1(), self.pop1()
            self.push_all(v1, v3, v2, v1)

    @_handles('dup2')
    def _op_dup2(self, ins):
        if self.top_is_wide():
            v1 = self.pop()
            self.push_all(v1, v1)
        else:
            v1, v2 = self.pop1(), self.pop1()
            self.push_all(v2, v1, v2, v1)

    @_handles('dup2_x1')
    def _op_dup2_x1(self, ins):
        if self.top_is_wide():
            v1 = self.pop()
            v2 = self.pop1()
            self.push_all(v1, v2, v1)
        else:
            v1, v2, v3 = self.pop1(), self.pop1(), self.pop1()
            self.push_all(v2, v1, v3, v2, v1)

    @_handles('dup2_x2')
    def _op_dup2_x2(self, ins):
        if self.top_is_wide():
            v1 = self.pop()
            if self.top_is_wide():
                v2 = self.pop()
                self.push_all(v1, v2, v1)
            else:
                v2, v3 = self.pop1(), self.pop1()
                self.push_all(v1, v3, v2, v1)
        else:
            v1, v2 = self.pop1(), self.pop1()
            if self.top_is_wide():
                v3 = self.pop()
                self.push_all(v2, v1, v3, v2, v1)
            else:
                v3, v4 = self.pop1(), self.pop1()
                self.push_all(v2, v1, v4, v3, v2, v1)

    @_handles('swap')
    def _op_swap(self, ins):
        v1, v2 = self.pop1(), self.pop1()
        self.push_all(v1, v2)

    # ---- int arithmetic (the mask expressions) ----
    @_handles(*_INT_BINOPS)
    def _op_int_binary(self, ins):
        nm = ins.name
        b = self.pop()
        a = self.pop()
        ca, cb = self.as_int(a), self.as_int(b)
        if nm == 'ixor' and ((ca is not None) != (cb is not None)):
            # Exactly the shape a decryptor mask has: constant ^ char.
            known = ca if cb is None else cb
            loc = self._origin_of(a if cb is None else b)
            self.mask_events.append((ins.off, known & 0xFFFF, loc))
            return self.push(('sym', 'masked'))
        if ca is None or cb is None:
            return self.push(('sym', nm))
        r = _INT_BINOPS[nm](ca, cb)
        self.push(('sym', nm + ':div0') if r is None else ('int', wrap32(r)))

    @_handles('ineg')
    def _op_ineg(self, ins):
        ca = self.as_int(self.pop())
        self.push(('int', wrap32(-ca)) if ca is not None else ('sym', 'ineg'))

    @_handles('i2c', 'i2b', 'i2s', 'i2l', 'l2i', 'f2i', 'd2i')
    def _op_convert(self, ins):
        nm = ins.name
        ca = self.as_int(self.pop())
        if ca is None:
            return self.push(('sym', nm))
        if nm == 'i2l':
            return self.push(('long', ca))
        narrowed = {'i2c': ca & 0xFFFF,
                    'i2b': ((ca + 0x80) & 0xFF) - 0x80,
                    'i2s': ((ca + 0x8000) & 0xFFFF) - 0x8000}.get(nm, ca)
        self.push(('int', narrowed))

    @_handles(*_OPAQUE_BINARY)
    def _op_opaque_binary(self, ins):
        self.pop()
        self.pop()
        self.push(('sym', ins.name))

    @_handles(*_OPAQUE_UNARY)
    def _op_opaque_unary(self, ins):
        self.pop()
        self.push(('sym', ins.name))

    @_handles('lcmp', 'fcmpl', 'fcmpg', 'dcmpl', 'dcmpg')
    def _op_compare(self, ins):
        self.pop()
        self.pop()
        self.push(('sym', ins.name))

    # ---- arrays / objects ----
    @_handles(*_ARRAY_LOADS)
    def _op_array_load(self, ins):
        self.pop()                                  # index
        arr = self.pop()
        self.push(('sym', 'elem:' + arr[0]))

    @_handles(*_ARRAY_STORES)
    def _op_array_store(self, ins):
        for _ in range(3):                          # value, index, arrayref
            self.pop()

    @_handles('arraylength')
    def _op_arraylength(self, ins):
        self.pop()
        self.push(('sym', 'len'))

    @_handles('new')
    def _op_new(self, ins):
        self.newid += 1
        self.push(('new', self.cf.class_name(ins.operands[0]), self.newid))

    @_handles('newarray', 'anewarray')
    def _op_newarray(self, ins):
        self.pop()
        self.push(('sym', 'arr'))

    @_handles('instanceof')
    def _op_instanceof(self, ins):
        self.pop()
        self.push(('sym', 'instanceof'))

    @_handles('athrow', 'monitorenter', 'monitorexit',
              'ireturn', 'lreturn', 'freturn', 'dreturn', 'areturn', *_IF_ONE_OPERAND)
    def _op_pop_one(self, ins):
        self.pop()

    @_handles('putfield', *_IF_TWO_OPERANDS)
    def _op_pop_two(self, ins):
        self.pop()
        self.pop()

    # ---- fields ----
    @_handles('getstatic')
    def _op_getstatic(self, ins):
        _o, _n, de, _k = self.cf.ref(ins.operands[0])
        self.push(('sym', 'static2' if cat2(de) else 'static'))

    @_handles('putstatic')
    def _op_putstatic(self, ins):
        self.cf.ref(ins.operands[0])                # validate the reference
        self.pop()

    @_handles('getfield')
    def _op_getfield(self, ins):
        self.pop()
        self.cf.ref(ins.operands[0])                # validate the reference
        self.push(('sym', 'field'))

    # ---- control flow: the walker decides where to go, but the stack effect
    # still has to be modelled or every later operand is misaligned. ----
    @_handles('jsr', 'jsr_w')
    def _op_jsr(self, ins):
        self.push(('sym', 'returnaddr'))

    # ---- invokes ----
    @_handles('invokedynamic')
    def _op_invokedynamic(self, ins):
        _bsm, _name, desc = self.cf.indy(ins.operands[0])
        for _ in parse_desc(desc)[0]:
            self.pop()
        self.push(('sym', 'indy'))

    @_handles(*INVOKE_OPS)
    def _op_invoke(self, ins):
        nm = ins.name
        owner, mname, mdesc, _kind = self.cf.ref(ins.operands[0])
        args, ret = parse_desc(mdesc)
        popped = [self.pop() for _ in args][::-1]          # now in declaration order
        recv = None if nm == 'invokestatic' else self.pop()

        # The seed-construction chain is dispatched on the RESOLVED ref, never on
        # the receiver's static type.
        if owner == 'java/lang/StackTraceElement' and mdesc == '()Ljava/lang/String;':
            if mname in ('getClassName', 'getMethodName'):
                return self.push(('st', mname[3:]))
            return self.push(('sym', 'ste:' + mname))
        if owner == 'java/lang/Throwable' and mname == 'getStackTrace':
            return self.push(('sym', 'starr'))
        if owner == 'java/lang/RuntimeException' and mname == '<init>':
            return self._init_new(recv, ('sym', 'exc'))
        if owner in BUFFER_CLASSES:
            return self._invoke_buffer(owner, mname, mdesc, recv, popped)
        if mname == 'toString' and mdesc == '()Ljava/lang/String;' \
                and recv is not None and recv[0] == 'buf':
            return self.push(('seed', recv[1]))
        if owner == 'java/lang/String':
            if mname == 'length' and mdesc == '()I':
                return self.push(('sym', 'seedlen' if recv is not None and recv[0] == 'seed'
                                  else 'len'))
            if mname == 'charAt' and mdesc == '(I)C':
                return self.push(('sym', 'char'))
            if mname == '<init>' and recv is not None and recv[0] == 'new':
                return self._init_new(recv, ('sym', 'str'))
        if owner == 'java/lang/Integer' and mname == 'intValue':
            return self.push(('sym', 'int'))
        if owner == 'java/lang/Long' and mname == 'longValue':
            return self.push(('sym', 'long'))
        if ret != 'V':                                     # generic: result is opaque
            self.push(('sym', 'ret'))

    def _invoke_buffer(self, owner, mname, mdesc, recv, popped):
        """StringBuffer/StringBuilder: track the seed's parts and their order."""
        if mname == '<init>':
            if mdesc == '()V':
                value = ('buf', [])
            elif mdesc == '(Ljava/lang/String;)V':
                value = ('buf', [self.seed_part(popped[0])])
            else:
                value = ('sym', 'buf')
            return self._init_new(recv, value)
        if recv is None or recv[0] != 'buf':
            raise self.fail(f'{owner}.{mname} on a non-buffer receiver {recv}')
        if mname == 'toString' and mdesc == '()Ljava/lang/String;':
            return self.push(('seed', recv[1]))
        parts = list(recv[1])
        returns_self = f'L{owner};'
        if mname == 'append' and mdesc == '(Ljava/lang/String;)' + returns_self:
            parts.append(self.seed_part(popped[0]))
        elif mname == 'insert' and mdesc == '(ILjava/lang/String;)' + returns_self:
            if self.as_int(popped[0]) != 0:
                raise self.fail(f'insert at a non-zero offset {self.as_int(popped[0])} '
                                f'- unknown seed order')
            parts.insert(0, self.seed_part(popped[1]))
        else:
            raise self.fail(f'unhandled buffer op {(owner, mname, mdesc)}')
        self.push(('buf', parts))

    def _init_new(self, recv, value):
        """`<init>` turns every copy of that uninitialised ref into the new value."""
        if recv is None or recv[0] != 'new':
            return
        rid = recv[2]
        self.stack = [value if (v[0] == 'new' and v[2] == rid) else v for v in self.stack]


# ==========================================================================
# 7. decryptor extraction
# ==========================================================================
# The scheme handled here keys string encryption on the CALL SITE's identity -
# the enclosing class and method name, read from a stack trace at runtime. A
# ciphertext is therefore meaningful at exactly one place, but a call site's
# identity is known at compile time (`this_class` plus the real method name),
# so it is recoverable statically.
#
# The decryptor shape is `static String d(String)`:
#
#     seed  = new StringBuffer(A).append(B).toString()
#               A, B in {StackTraceElement.getClassName, .getMethodName}
#               (or .insert(0, B), which puts B first)
#     <dead junk: fconst_*/pop/dup/pop2/swap>
#     maskA = <iconst/bipush/sipush + ishl/ixor expression>   stored to a local
#     decoy = <second, UNUSED constant expression>            stored, never read
#     maskB = <third constant expression>
#     loop:  out[i] = (char)(maskA ^ (ct[i] ^ seed[n])); i--
#            out[i] = (char)(maskB ^ (ct[i] ^ seed[n])); i--; n-- (wrap)
#
# Three constant expressions, only two read: masks cannot be picked positionally.
# They are recovered by (a) concretely interpreting the straight-line prologue
# [0, loop_head), leaving concrete ints in the locals, then (b) walking the loop
# body over both branch arms and taking the concrete operand of each `ixor` whose
# OTHER operand is symbolic (a char). Exactly two such events must exist.
#
# The prologue may end by falling through into the loop head (javac's top-tested
# `while`) or with an unconditional jump into the loop region (the rotated loop
# bytecode-level obfuscators tend to emit). Both are accepted; conditional flow,
# a backward jump or an early return in the prologue are hard failures.

@dataclass
class Decryptor:
    owner: str                    # internal class name
    name: str
    desc: str
    seed_parts: list              # e.g. ['ClassName', 'MethodName']
    mask_a: int                   # applied to the HIGHEST index first
    mask_b: int
    mask_locals: list
    provenance: dict

    @property
    def key(self):
        return (self.owner, self.name, self.desc)

    @property
    def simple(self):
        return self.owner.rsplit('/', 1)[-1]

    def seed(self, dotted_class, method_name):
        parts = {'ClassName': dotted_class, 'MethodName': method_name}
        try:
            return ''.join(parts[p] for p in self.seed_parts)
        except KeyError as ex:
            raise UnseedError(f'{self.owner}.d: unresolvable seed part '
                              f'{ex.args[0]!r}') from None

    def to_json(self):
        return {'owner': self.owner, 'method': self.name, 'desc': self.desc,
                'seed_parts': self.seed_parts, 'mask_a': self.mask_a,
                'mask_b': self.mask_b, 'mask_locals': self.mask_locals,
                'provenance': self.provenance}


def loop_bounds(insns):
    """(loop_head, loop_end) from backward branches. Raises if there is no loop."""
    back = [(ins.off, t) for ins in insns for t in (ins.target or ()) if t <= ins.off]
    if not back:
        raise UnseedError('no backward branch - not the expected decryptor loop')
    return min(t for _o, t in back), max(o for o, _t in back)


def run_prologue(interp, insns, loop_head):
    """Interpret the straight-line prologue [0, loop_head).

    Anything other than falling through into the loop head, or an unconditional
    jump forward into the loop region, is a hard failure rather than a guess:
    conditional control flow, a backward jump, or an early return all mean the
    constants cannot be recovered by straight-line interpretation.
    """
    for ins in insns:
        if ins.off >= loop_head:
            return                      # fell through into the loop head
        if ins.name in GOTO_OPS:
            t = ins.target[0]
            if t >= loop_head:
                return                  # prologue complete, jumps to the loop test
            raise UnseedError(f'prologue branches backward to {t} (bci {ins.off})')
        if ins.target or ins.name in ('tableswitch', 'lookupswitch'):
            raise UnseedError(f'prologue has conditional flow at bci {ins.off} '
                              f'({ins.name}) - refusing to guess')
        if ins.name in TERMINATORS:
            raise UnseedError(f'prologue returns at bci {ins.off}')
        interp.step(ins)


def collect_masks(interp, insns, loop_head, loop_end, path_budget=MAX_MASK_SEARCH_PATHS):
    """Walk the loop body over both branch arms, recording every `ixor` whose
    operands are (concrete int, opaque char). Exactly two distinct bcis must be
    found; their order is (maskA at the higher array index, maskB).

    -> (mask_a, mask_b, [local_a, local_b], [bci_a, bci_b])
    """
    by_off = {ins.off: ins for ins in insns}
    found = {}                          # bci -> (value, local)
    work = [loop_head]
    seen = set()
    steps = 0
    while work:
        off = work.pop()
        if off in seen:
            continue
        seen.add(off)
        if len(seen) > path_budget:
            raise UnseedError('mask search: path budget exceeded (loop shape unknown)')
        snap = interp.snapshot()
        cur = off
        while cur in by_off and loop_head <= cur <= loop_end:
            ins = by_off[cur]
            before = len(interp.mask_events)
            interp.step(ins)
            for bci, val, loc in interp.mask_events[before:]:
                if bci in found and found[bci][0] != val:
                    raise UnseedError(f'mask at bci {bci} is not single-valued: '
                                      f'{found[bci][0]} vs {val}')
                found[bci] = (val, loc)
            steps += 1
            if steps > MAX_MASK_SEARCH_STEPS:
                raise UnseedError('mask search: step budget exceeded')
            if ins.name in GOTO_OPS:
                t = ins.target[0]
                if t <= cur:
                    break                       # backedge: body fully covered
                cur = t
                continue
            if ins.target:
                t = ins.target[0]
                if t > cur:
                    work.append(t)              # explore the taken arm too
                elif t < loop_head:
                    raise UnseedError(f'loop branches out of the region to {t}')
                else:
                    break                       # backedge
                cur = ins.off + ins.length
                continue
            if ins.name in TERMINATORS:
                break
            cur = ins.off + ins.length
        interp.restore(snap)
    ordered = sorted(found.items())
    if len(ordered) != 2:
        raise UnseedError(f'expected exactly 2 masked char stores, found {len(ordered)}: '
                          f'{[(b, v[0]) for b, v in ordered]}')
    (bci_a, (val_a, loc_a)), (bci_b, (val_b, loc_b)) = ordered
    return val_a, val_b, [loc_a, loc_b], [bci_a, bci_b]


def find_seed(interp):
    """Locate the ('seed', parts) value the prologue built, in locals or on stack."""
    cands = []
    for v in list(interp.locals) + list(interp.stack):
        if v and v[0] == 'seed' and v[1] not in cands:
            cands.append(v[1])
    if not cands:
        raise UnseedError('no seed string built in the prologue')
    if len(cands) > 1:
        raise UnseedError(f'{len(cands)} distinct seeds built: {cands}')
    parts = cands[0]
    if not parts or any(p not in ('ClassName', 'MethodName') for p in parts):
        raise UnseedError(f'seed is not built purely from the stack-trace frame: {parts}')
    if 'ClassName' not in parts or 'MethodName' not in parts:
        raise UnseedError(f'seed uses only part of the frame: {parts}')
    return parts


def is_decryptor_candidate(m):
    """Shape-only filter, counted separately from the frame check so that a wrong
    frame predicate cannot masquerade as a clean "this jar has no decryptors"."""
    return (m['desc'] == STRING_TO_STRING
            and bool(m['access'] & ACC_STATIC) and not m['access'] & ACC_NATIVE)


def looks_like_decryptor(cf, m, insns):
    """Does the body read a stack-trace frame's class/method name?"""
    if not is_decryptor_candidate(m):
        return False
    refs = set()
    for ins in insns:
        if ins.name in INVOKE_OPS:
            try:
                owner, nm, de, _k = cf.ref(ins.operands[0])
            except UnseedError:
                continue
            refs.add((owner, nm, de))
    # NOTE: the constant pool names the *declared* receiver at the call site, so the
    # frame walk shows up as `java/lang/RuntimeException.getStackTrace`, NOT
    # `java/lang/Throwable.getStackTrace`. Matching on Throwable alone finds nothing
    # and reports it as a clean zero.
    has_frame = any(nm == 'getStackTrace' and de == '()[Ljava/lang/StackTraceElement;'
                    for _o, nm, de in refs)
    has_getter = any(o == 'java/lang/StackTraceElement'
                     and d == '()Ljava/lang/String;'
                     and n in ('getClassName', 'getMethodName')
                     for o, n, d in refs)
    return has_frame and has_getter


def extract_decryptor(cf, m):
    insns, meta = cf.insns(m)
    if insns is None:
        raise UnseedError('decryptor has no Code attribute')
    if not looks_like_decryptor(cf, m, insns):
        raise UnseedError('not a stack-trace-seeded decryptor')
    loop_head, loop_end = loop_bounds(insns)
    interp = Interp(cf, meta['max_locals'])
    run_prologue(interp, insns, loop_head)
    seed_parts = find_seed(interp)
    mask_a, mask_b, mask_locals, mask_bcis = collect_masks(interp, insns,
                                                           loop_head, loop_end)
    return Decryptor(cf.this, m['name'], m['desc'], seed_parts, mask_a, mask_b, mask_locals,
                     {'loop_head': loop_head, 'loop_end': loop_end,
                      'mask_bcis': mask_bcis, 'n_insns': len(insns)})


def find_decryptors(cfs):
    """-> ({(owner,name,desc): Decryptor}, [(class, method, error)], stats)

    Callers must assert stats['extracted'] == stats['frame_shaped']: a frame-shaped
    method that did not extract is recorded in `failures`, never silently skipped.
    """
    table, failures = {}, []
    stats = {'candidates': 0, 'frame_shaped': 0, 'extracted': 0, 'decode_failed': 0}
    for cf in cfs.values():
        for m in cf.methods:
            if not is_decryptor_candidate(m):
                continue
            stats['candidates'] += 1
            try:
                insns, _meta = cf.insns(m)
            except UnseedError as ex:
                stats['decode_failed'] += 1
                failures.append((cf.dotted, m['name'], f'decode: {ex}'))
                continue
            if insns is None:
                stats['decode_failed'] += 1
                failures.append((cf.dotted, m['name'], 'no Code attribute'))
                continue
            if not looks_like_decryptor(cf, m, insns):
                continue
            stats['frame_shaped'] += 1
            try:
                d = extract_decryptor(cf, m)
            except UnseedError as ex:
                failures.append((cf.dotted, m['name'], str(ex)))
                continue
            except Exception as ex:                     # noqa: BLE001
                failures.append((cf.dotted, m['name'], f'{type(ex).__name__}: {ex}'))
                continue
            if d.key in table:
                raise UnseedError(f'duplicate decryptor key {d.key}')
            table[d.key] = d
            stats['extracted'] += 1
    return table, failures, stats


# ==========================================================================
# 8. the decryption itself
# ==========================================================================
# Validated against tests/fixtures/: the generator derives ciphertexts from
# known plaintexts with an independently written inverse, and the test suite
# cross-checks both against what a real JVM produces from the compiled fixture.

def decrypt_units(ct_units, seed_units, mask_a, mask_b):
    """out[i] = maskA ^ (ct[i] ^ seed[n]); pairs share a seed index, which walks
    backwards and wraps. Operates on UTF-16 code units to match Java charAt."""
    if not ct_units:
        return []
    if not seed_units:
        raise UnseedError('empty seed')
    out = [0] * len(ct_units)
    n = n_wrap = len(seed_units) - 1
    i = len(ct_units) - 1
    while i >= 0:
        out[i] = (mask_a ^ (ct_units[i] ^ seed_units[n])) & 0xFFFF
        i -= 1
        if i < 0:
            break
        out[i] = (mask_b ^ (ct_units[i] ^ seed_units[n])) & 0xFFFF
        i -= 1
        n -= 1
        if n < 0:
            n = n_wrap
    return out


def decrypt(ct, seed, mask_a, mask_b):
    return from_utf16_units(decrypt_units(to_utf16_units(ct), to_utf16_units(seed),
                                          mask_a, mask_b))


# ==========================================================================
# 9. call-site scan
# ==========================================================================

class Hit(TypedDict):
    """A fully resolved `ldc <ct> [checkcast] invokestatic D.d` call site."""
    method: str              # enclosing method (part of the seed)
    bci: int                 # offset of the ldc
    span: tuple              # (start, end) offsets of the whole call-site span
    ldc: str                 # 'ldc' or 'ldc_w'
    ldc_cp: int              # constant-pool index the ldc loads
    decryptor: str           # simple name of the decryptor's class
    decryptor_owner: str
    ct: str                  # ciphertext
    plain: str
    seed: str
    code_abs_off: int        # absolute file offset of the method's bytecode


def _literal_operand(cf, insns, k):
    """Find the string literal feeding the decryptor call at insns[k].

    -> (index of the ldc, its CP index, None) or (None, None, reason).
    """
    j = k - 1
    if j >= 0 and insns[j].name == 'checkcast':
        try:
            if cf.class_name(insns[j].operands[0]) != 'java/lang/String':
                return None, None, 'checkcast to a non-String type'
        except UnseedError as ex:
            return None, None, f'checkcast: {ex}'
        j -= 1
    if j < 0 or insns[j].name not in ('ldc', 'ldc_w'):
        return None, None, (f'operand is not a string literal '
                            f'({insns[j].name if j >= 0 else "<method entry>"})')
    ci = insns[j].operands[0]
    e = cf.cp[ci] if 0 < ci < cf.cp_count else None
    if e is None or e[0] != 'string':
        return None, None, f'ldc of CP#{ci} which is {e[0] if e else None}, not string'
    return j, ci, None


def scan_call_sites(cf, dec_table):
    """-> (hits, unsupported). See `Hit` for what a hit holds."""
    hits, unsupported = [], []
    for m in cf.methods:
        try:
            insns, meta = cf.insns(m)
        except UnseedError as ex:
            unsupported.append({'method': m['name'], 'why': f'decode: {ex}'})
            continue
        if insns is None:
            continue
        for k, ins in enumerate(insns):
            if ins.name != 'invokestatic':
                continue
            try:
                owner, nm, de, _kind = cf.ref(ins.operands[0])
            except UnseedError:
                continue
            d = dec_table.get((owner, nm, de))
            if d is None:
                continue
            j, ci, why = _literal_operand(cf, insns, k)
            if why is None:
                ct = cf.string_const(ci)
                seed = d.seed(cf.dotted, m['name'])
                try:
                    plain = decrypt(ct, seed, d.mask_a, d.mask_b)
                except UnseedError as ex:
                    why = f'decrypt: {ex}'
            if why is not None:
                unsupported.append({'method': m['name'], 'bci': ins.off,
                                    'decryptor': d.simple, 'why': why})
                continue
            hits.append({'method': m['name'], 'bci': insns[j].off,
                         'span': (insns[j].off, ins.off + ins.length),
                         'ldc': insns[j].name, 'ldc_cp': ci,
                         'decryptor': d.simple, 'decryptor_owner': d.owner,
                         'ct': ct, 'plain': plain, 'seed': seed,
                         'code_abs_off': meta['code_abs_off']})
    return hits, unsupported


def scan_all(cfs, dec_table, progress=False):
    """-> ({class: [hits]}, {class: [unresolvable sites]}); empty classes omitted."""
    results, unsup = {}, {}
    for cf in cfs.values():
        hits, bad = scan_call_sites(cf, dec_table)
        if hits:
            results[cf.this] = hits
        if bad:
            unsup[cf.this] = bad
        if progress:
            print(f'\r  scanned {len(results)} classes with strings...', end='',
                  file=sys.stderr, flush=True)
    if progress:
        print('', file=sys.stderr)
    return results, unsup


def count_sites(by_class):
    return sum(len(v) for v in by_class.values())


# ==========================================================================
# 10. patching: length-preserving rewrite
# ==========================================================================

def _first_pool_index(cf, kind):
    """{payload: first CP index} for entries of `kind` (payload = entry[1])."""
    index = {}
    for i in range(1, cf.cp_count):
        e = cf.cp[i]
        if e and e[0] == kind:
            index.setdefault(e[1], i)
    return index


def patch_class(cf, data, hits):
    """Rewrite every `ldc <ct> [checkcast] invokestatic D.d` span into
    `ldc_w <plaintext>` + nop padding.

    Length-preserving on purpose: the span is >= 5 bytes and `ldc_w` is 3, so the
    difference is nop padding. Because no instruction's length changes, every
    branch offset, StackMapTable frame, exception-table range and LineNumberTable
    entry stays valid - nothing downstream needs recomputing. New constant-pool
    entries are appended, which shifts no existing index.

    -> (patched_bytes, spans_rewritten, constant_pool_entries_added)
    """
    utf8_index = _first_pool_index(cf, 'utf8')          # raw bytes -> CP index
    string_index = _first_pool_index(cf, 'string')      # utf8 index -> CP index
    extra = bytearray()
    next_idx = cf.cp_count

    def intern(plain):
        """CP index of a CONSTANT_String holding `plain`, appending what's missing."""
        nonlocal next_idx
        raw = enc_modified_utf8(plain)
        ui = utf8_index.get(raw)
        if ui is None:
            ui = utf8_index[raw] = next_idx
            next_idx += 1
            extra.extend(b'\x01' + struct.pack('>H', len(raw)) + raw)
        si = string_index.get(ui)
        if si is None:
            si = string_index[ui] = next_idx
            next_idx += 1
            extra.extend(b'\x08' + struct.pack('>H', ui))
        return si

    # intern first: appended entries must not overlap the code bytes we rewrite
    spans = []
    for h in hits:
        si = intern(h['plain'])
        start, end = h['span']
        n = end - start
        if n < 5:
            raise UnseedError(f'{cf.dotted}: call-site span is only {n} bytes')
        repl = bytes([0x13]) + struct.pack('>H', si) + b'\x00' * (n - 3)   # ldc_w + nops
        spans.append((h['code_abs_off'] + start, repl))

    spans.sort()
    for a, b in zip(spans, spans[1:]):
        if a[0] + len(a[1]) > b[0]:
            raise UnseedError(f'{cf.dotted}: overlapping patch spans at {a[0]:#x}')

    suffix = bytearray(data[cf.cp_end:])
    for pos, repl in spans:
        rel = pos - cf.cp_end
        if rel < 0 or rel + len(repl) > len(suffix):
            raise UnseedError(f'{cf.dotted}: patch offset {pos:#x} outside the class body')
        suffix[rel:rel + len(repl)] = repl

    head = data[:8] + struct.pack('>H', next_idx)
    out = head + data[10:cf.cp_end] + bytes(extra) + bytes(suffix)
    return out, len(spans), next_idx - cf.cp_count


def check_patch(original, patched_data, dec_table, expect_plains):
    """Post-conditions for a patched classfile. Every one must hold; raises otherwise.

    1. identity, member list and every Code length unchanged - proves the rewrite was
       length-preserving, so StackMapTable / exception / line-number tables stay valid
    2. zero surviving decryptor call sites
    3. every expected plaintext is present as a CONSTANT_String in the new pool
    """
    o = load_class('orig', original)
    p = load_class('patched', patched_data)
    if p.this != o.this:
        raise UnseedError(f'identity changed: {o.this} -> {p.this}')
    if len(p.methods) != len(o.methods) or len(p.fields) != len(o.fields):
        raise UnseedError('member count changed')
    for mo, mp in zip(o.methods, p.methods):
        if (mo['name'], mo['desc'], mo['access']) != (mp['name'], mp['desc'], mp['access']):
            raise UnseedError(f'member identity changed: {mo["name"]}{mo["desc"]}')
        bo, _ = o.code_of(mo)
        bp, _m = p.code_of(mp)
        if (bo is None) != (bp is None):
            raise UnseedError(f'{mo["name"]}: Code presence changed')
        if bo is not None and len(bo) != len(bp):
            raise UnseedError(f'{mo["name"]}: code length changed {len(bo)} -> {len(bp)}')
    hits, unsup = scan_call_sites(p, dec_table)
    if hits or unsup:
        raise UnseedError(f'{p.dotted}: {len(hits)} decryptor call site(s) survived, '
                          f'{len(unsup)} unresolvable')
    pool = {p.string_const(i) for i in range(1, p.cp_count)
            if p.cp[i] and p.cp[i][0] == 'string'}
    missing = [s for s in expect_plains if s not in pool]
    if missing:
        raise UnseedError(f'{p.dotted}: {len(missing)} expected plaintext(s) missing from '
                          f'the pool, e.g. {missing[0]!r}')
    return True


# ==========================================================================
# 11. invokedynamic: census, what is statically resolvable, the runtime worklist
# ==========================================================================

LMF = 'java/lang/invoke/LambdaMetafactory'

# Resolutions whose actual target cannot be taken from the constant pool alone;
# these go on the worklist for a runtime `Lookup.find*` capture.
NEEDS_RUNTIME_CAPTURE = ('native-gated', 'unknown-owner', 'static-java', 'malformed')


def _bootstrap_infos(cf, cfs, by_this):
    """One dict per BootstrapMethods entry of `cf`: kind/owner/name/desc/args, plus
    `native` = True/False when the bootstrap's owner is in the input set, else None."""
    infos = []
    for mh, args in cf.bootstrap_methods():
        try:
            kind, owner, name, desc = cf.methodhandle(mh)
        except UnseedError as ex:
            infos.append({'kind': None, 'owner': '?', 'name': '?', 'desc': '?',
                          'args': args, 'error': str(ex), 'native': None})
            continue
        bi = {'kind': kind, 'owner': owner, 'name': name, 'desc': desc, 'args': args}
        own_cf = cfs.get(owner + '.class')
        if own_cf is None:
            own_cf = by_this.get(owner)
        bi['native'] = None if own_cf is None else (name, desc) in own_cf.native_methods
        infos.append(bi)
    return infos


def _classify_site(cf, bi, row):
    """Fill row['resolution'] (and 'target'/'error') for one invokedynamic site."""
    if bi['owner'] == LMF and bi['name'] in ('metafactory', 'altMetafactory'):
        row['resolution'] = 'resolved-lambda'
        args = bi['args']
        if len(args) < 3:
            row['resolution'] = 'malformed'
            row['error'] = f'LambdaMetafactory has {len(args)} static args'
            return
        try:
            _k, o2, n2, d2 = cf.methodhandle(args[1])
            row['target'] = f'{o2}.{n2}{d2}'
        except UnseedError as ex:
            row['resolution'] = 'malformed'
            row['error'] = f'lambda impl handle: {ex}'
    elif bi['native'] is True:
        row['resolution'] = 'native-gated'
    elif bi['native'] is False:
        row['resolution'] = 'static-java'
    else:
        row['resolution'] = 'unknown-owner'


def indy_scan(cfs):
    """Census every invokedynamic site and classify its bootstrap.

    -> (rows, summary, bootstraps). A row's `resolution` is one of:
      resolved-lambda   - LambdaMetafactory: the impl target is in the CP, exact
      static-java       - bootstrap is Java code inside this input set, so it
                          could be emulated statically
      native-gated      - bootstrap is ACC_NATIVE: NOT statically resolvable.
                          Recorded on a worklist for a runtime capture of the
                          Lookup.find* calls it makes, rather than guessed at
      unknown-owner     - bootstrap class is not in the input set
      malformed         - the site or its bootstrap does not parse
    """
    rows = []
    summary = Counter()
    bootstraps = Counter()
    by_this = {cf.this: cf for cf in cfs.values()}
    for cf in cfs.values():
        bs_info = _bootstrap_infos(cf, cfs, by_this)
        if not bs_info:
            continue
        for m in cf.methods:
            try:
                insns, _meta = cf.insns(m)
            except UnseedError:
                continue
            for ins in insns or ():
                if ins.name != 'invokedynamic':
                    continue
                site = {'class': cf.this, 'method': m['name'], 'bci': ins.off}
                try:
                    bidx, iname, idesc = cf.indy(ins.operands[0])
                    if bidx >= len(bs_info):
                        raise UnseedError(f'BSM index {bidx} out of range')
                except UnseedError as ex:
                    rows.append({**site, 'resolution': 'malformed', 'error': str(ex)})
                    summary['malformed'] += 1
                    continue
                bi = bs_info[bidx]
                row = {**site, 'indy_name': iname, 'indy_desc': idesc,
                       'bootstrap': f'{bi["owner"]}.{bi["name"]}{bi["desc"]}',
                       'bootstrap_index': bidx}
                _classify_site(cf, bi, row)
                summary[row['resolution']] += 1
                bootstraps[f'{row["bootstrap"]} [{row["resolution"]}]'] += 1
                rows.append(row)
    return rows, summary, bootstraps


# ==========================================================================
# 12. self-tests
# ==========================================================================
# Two layers, deliberately separated:
#
#   selftest()         - codec round-trips only. Needs no files, no JVM, no
#                        input. Safe to run before touching any artifact.
#   fixture_control()  - the end-to-end positive control: the whole pipeline
#                        over the synthetic class in tests/fixtures/, compared
#                        against expected.json and, when a JVM is available,
#                        against what Java actually produces at runtime. The JVM
#                        is an independent oracle, not a memorised answer.

FIXTURE_DIR = os.path.join(TOOL_DIR, 'tests', 'fixtures')
FIXTURE_EXPECTED = os.path.join(FIXTURE_DIR, 'expected.json')


def selftest():
    """Round-trip the codec helpers. A silent corruption here would poison every
    recovered string, so these run before anything else."""
    cases = ['', 'a', 'NUL:\x00 here', 'ascii /unseed/fixture/SeedFixture',
             'é中퟿', 'supplementary \U0001F600 end',
             '\x00\x01\x7f\x80߿ࠀ￿']
    for s in cases:
        raw = enc_modified_utf8(s)
        if b'\x00' in raw:
            raise UnseedError(f'encoded a raw 0x00 byte for {s!r}')
        back = dec_modified_utf8(raw)
        if back != s:
            raise UnseedError(f'modified-UTF8 round trip failed: {s!r} -> {back!r}')
        u = to_utf16_units(s)
        if from_utf16_units(u) != s:
            raise UnseedError(f'UTF-16 round trip failed for {s!r}')
        if len(u) != len(s.encode('utf-16-be')) // 2:
            raise UnseedError(f'UTF-16 unit count wrong for {s!r}')
        # NUL must go out as 0xC0 0x80 and a supplementary char as a CESU-8
        # pair; both are what Python's utf-8 codec gets wrong.
        if '\x00' in s and b'\xc0\x80' not in raw:
            raise UnseedError(f'NUL was not encoded as 0xC0 0x80 for {s!r}')
        if any(u16 > 0xFFFF for u16 in u):
            raise UnseedError(f'non-BMP unit escaped to UTF-16 for {s!r}')
    return len(cases)


def load_fixture():
    """-> (expected dict, {entry: ClassFile}, ClassSource). Raises if the fixture is absent."""
    if not os.path.isdir(FIXTURE_DIR) or not os.path.isfile(FIXTURE_EXPECTED):
        raise UnseedError(f'bundled fixture not found at {FIXTURE_DIR} - '
                          f'regenerate it with: python3 tests/make_fixture.py')
    with open(FIXTURE_EXPECTED, encoding='utf-8') as f:
        expected = json.load(f)
    src = ClassSource(FIXTURE_DIR)
    cfs, fails = load_all(src, quiet=True)
    if fails:
        raise UnseedError(f'fixture classfile(s) failed to parse: {fails}')
    if not cfs:
        raise UnseedError(f'no .class files under {FIXTURE_DIR} - compile the '
                          f'fixture with: python3 tests/make_fixture.py')
    return expected, cfs, src


def _jvm_oracle(classpath, main_class):
    """Run the fixture under `java` and decode its output back to plaintexts.

    The fixture prints `key=<backslash-u hex escapes>` lines, so the output is
    pure ASCII and survives any console encoding. -> (values dict, stderr) or
    (None, reason) when no JVM is available.
    """
    try:
        proc = subprocess.run(['java', '-cp', classpath, main_class],
                              capture_output=True, text=True, timeout=120)
    except (FileNotFoundError, subprocess.TimeoutExpired) as ex:
        return None, f'{type(ex).__name__}: {ex}'
    if proc.returncode != 0:
        raise UnseedError(f'`java -cp {classpath} {main_class}` exited '
                          f'{proc.returncode}\n{proc.stderr.strip()[-2000:]}')
    values = {}
    for line in proc.stdout.splitlines():
        if not line.strip():
            continue
        key, _, body = line.partition('=')
        units = []
        while body:
            if not body.startswith('\\u') or len(body) < 6:
                raise UnseedError(f'malformed oracle escape in {line!r}')
            units.append(int(body[2:6], 16))
            body = body[6:]
        values[key.strip()] = from_utf16_units(units)
    return values, proc.stderr


def _control_extraction(cfs, expected, summary):
    """Checks 1-2: the decryptor is found, and seed parts and BOTH masks are right."""
    tab, failures, stats = find_decryptors(cfs)
    summary['stats'] = dict(stats)
    d = expected['decryptor']
    key = (d['owner'], d['name'], d['desc'])
    if failures:
        raise UnseedError(f'fixture decryptor failed to extract: {failures}')
    if key not in tab:
        raise UnseedError(f'decryptor {key} not found; stats={stats}')
    dec = tab[key]
    if dec.seed_parts != d['seed_parts']:
        raise UnseedError(f'seed parts {dec.seed_parts} != expected {d["seed_parts"]}')
    if (dec.mask_a, dec.mask_b) != (d['mask_a'], d['mask_b']):
        raise UnseedError(
            f'masks ({dec.mask_a:#x}, {dec.mask_b:#x}) != expected '
            f'({d["mask_a"]:#x}, {d["mask_b"]:#x}) - the unused decoy constant '
            f'({d["decoy"]:#x}) was probably picked up, or masks were selected '
            f'positionally instead of by which constants reach an ixor')
    summary['masks'] = (dec.mask_a, dec.mask_b)
    return tab


def _control_call_sites(cfs, tab, expected, summary):
    """Check 3: every call site decrypts to its expected plaintext."""
    res, unsup = scan_all(cfs, tab)
    if unsup:
        raise UnseedError(f'{count_sites(unsup)} unresolvable '
                          f'call site(s) in the fixture: {unsup}')
    got = sorted((c, h['method'], h['plain']) for c, v in res.items() for h in v)
    want = sorted((s['class'], s['method'], s['plain']) for s in expected['sites'])
    if got != want:
        missing = [w for w in want if w not in got]
        extra = [g for g in got if g not in want]
        raise UnseedError(f'static recovery mismatch: {len(missing)} missing, '
                          f'{len(extra)} unexpected; missing={missing[:2]} '
                          f'unexpected={extra[:2]}')
    summary['sites_recovered'] = len(got)
    return res


def _control_patching(cfs, src, tab, res, summary):
    """Check 4: patching preserves length, drops every call site, keeps each plaintext.
    -> {entry: patched bytes}"""
    patched = {}
    spans = 0
    for entry, cf in cfs.items():
        data = src.read(entry)
        hits = res.get(cf.this, [])
        out_bytes, nspans, _ncp = patch_class(cf, data, hits)
        check_patch(data, out_bytes, tab, [h['plain'] for h in hits])
        patched[entry] = out_bytes
        spans += nspans
    summary['classes_patched'] = len(patched)
    summary['spans'] = spans
    return patched


def _control_jvm(patched, expected, summary):
    """Check 5: the JVM as an independent oracle, on both unpatched and patched code."""
    main_class = expected['main_class']
    want_by_key = {s['token'].lower(): s['plain'] for s in expected['sites']}
    baseline, why = _jvm_oracle(FIXTURE_DIR, main_class)
    if baseline is None:
        summary['jvm'] = f'skipped (no usable JVM: {why})'
        return
    if baseline != want_by_key:
        raise UnseedError(f'the JVM disagrees with expected.json - the fixture '
                          f'generator or expected.json is wrong, not the tool.\n'
                          f'  java said: {baseline}\n  expected:    {want_by_key}')
    summary['jvm'] = f'unpatched run matches expected.json ({len(baseline)} strings)'

    with tempfile.TemporaryDirectory(prefix='unseed-fixture-') as tmp:
        for entry, blob in patched.items():
            _write_file(os.path.join(tmp, entry), blob)
        after, _err = _jvm_oracle(tmp, main_class)
        if after is None:
            raise UnseedError('the unpatched fixture ran under `java` but the '
                              f'patched one could not: {why}')
        if after != baseline:
            raise UnseedError(f'patched classfiles changed behaviour.\n'
                              f'  unpatched: {baseline}\n  patched:   {after}')
    summary['jvm'] += '; patched classfiles re-ran identically (verifier accepted them)'


def fixture_control(run_jvm=True):
    """Run the full pipeline over the bundled fixture and assert every result.

    Raises UnseedError on the first thing that does not hold. Returns a summary
    dict for reporting. Checks, in order:

      1. the decryptor is found and extracted (a recognised shape that failed to
         extract is a failure, never a skip);
      2. recovered seed parts and BOTH masks equal expected.json - this is what
         catches the decoy constant being picked up, or masks being selected
         positionally instead of by which constants reach an ixor;
      3. every call site decrypts to its expected plaintext, with zero
         unresolvable sites;
      4. patching preserves length, drops every call site, and still contains
         each plaintext in the pool (check_patch);
      5. with a JVM: the strings Java really produces match expected.json, and
         the PATCHED classfiles load without VerifyError and print output
         byte-identical to the unpatched run - which is what proves the
         length-preserving rewrite keeps StackMapTable, exception tables and
         line numbers valid, rather than merely asserting it.
    """
    expected, cfs, src = load_fixture()
    summary = {'sites_expected': len(expected['sites'])}
    tab = _control_extraction(cfs, expected, summary)
    res = _control_call_sites(cfs, tab, expected, summary)
    patched = _control_patching(cfs, src, tab, res, summary)
    summary['jvm'] = 'skipped'
    if run_jvm:
        _control_jvm(patched, expected, summary)
    return summary


def cmd_selftest(args):
    print('=== unseed.py selftest ===')
    n = selftest()
    print(f'PASS  codec round-trips ({n} cases: NUL as 0xC0 0x80, CESU-8 '
          f'surrogate pairs, BMP boundaries)')
    try:
        s = fixture_control(run_jvm=not args.no_jvm)
    except UnseedError as ex:
        print(f'FAIL  fixture control: {ex}')
        return 1
    print(f'PASS  decryptor extraction: {s["stats"]["extracted"]}/'
          f'{s["stats"]["frame_shaped"]} frame-shaped, masks '
          f'{s["masks"][0]:#x}/{s["masks"][1]:#x}, 0 failures')
    print(f'PASS  string recovery: {s["sites_recovered"]}/{s["sites_expected"]} '
          f'call sites, 0 unresolvable')
    print(f'PASS  patch: {s["classes_patched"]} class(es), {s["spans"]} span(s), '
          f'length-preserving post-conditions hold')
    rc = 0
    label = 'PASS ' if s['jvm'].startswith('unpatched') else 'SKIP '
    if label == 'SKIP ' and args.require_jvm:
        rc = 1
        label = 'FAIL '
    print(f'{label} JVM oracle: {s["jvm"]}')
    print('OK' if rc == 0 else 'FAILED')
    return rc


# ==========================================================================
# 13. reports and javap cross-checks
# ==========================================================================

def _write_file(path, data: bytes):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'wb') as f:
        f.write(data)


def _write_json(path, obj, **kw):
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(obj, f, indent=1, **kw)


def _by_site(items):
    return sorted(items, key=lambda h: (h['method'], h['bci']))


def printable_ratio(s):
    if not s:
        return 1.0
    return sum(1 for ch in s if 32 <= ord(ch) < 127) / len(s)


def write_strings_json(path, results):
    out = {cls: [{k: h[k] for k in ('method', 'bci', 'decryptor', 'ct', 'plain', 'seed')}
                 for h in _by_site(items)]
           for cls, items in sorted(results.items())}
    _write_json(path, out, ensure_ascii=False)
    return out


def write_strings_report(path, results, decryptors, failures, unsup):
    with open(path, 'w', encoding='utf-8') as f:
        f.write('# unseed.py - recovered string constants\n')
        f.write(f'# decryptors: {len(decryptors)} extracted, {len(failures)} failed\n')
        f.write(f'# classes with strings: {len(results)}   literals: '
                f'{count_sites(results)}\n')
        f.write(f'# unresolvable call sites: {count_sites(unsup)}\n\n')
        for cls, items in sorted(results.items()):
            f.write(f'=== {cls}\n')
            for h in _by_site(items):
                f.write(f'  {h["method"]}  bci {h["bci"]:<6} via {h["decryptor"]}.d  '
                        f'{h["plain"]!r}\n')
            f.write('\n')


def write_indy_json(path, rows, summary, bootstraps):
    _write_json(path, {'summary': dict(summary),
                       'bootstraps': [{'bootstrap': k, 'sites': v}
                                      for k, v in bootstraps.most_common()],
                       'sites': rows})


def write_worklist(path, rows):
    """The rows a runtime `Lookup.find*` capture has to be joined against.

    `indy_name` + `indy_desc` survive in the constant pool even when the actual
    bootstrap target does not, so they are the join keys. Navigate by class +
    signature, never by method name: names are the thing an obfuscator rewrites.
    """
    wl = [{'class': r['class'], 'method': r['method'], 'bci': r['bci'],
           'indy_name': r.get('indy_name'), 'indy_desc': r.get('indy_desc'),
           'bootstrap': r.get('bootstrap'), 'resolution': r['resolution']}
          for r in rows if r['resolution'] in NEEDS_RUNTIME_CAPTURE]
    _write_json(path, wl)
    return len(wl)


def check_plaintext_consistency(res, hi=0.95, lo=0.9):
    """Group sites by (class, method, decryptor) - i.e. by identical seed AND masks.

    A wrong seed or mask corrupts every site in a group the same way, so a group
    cannot be *mixed*. A group holding both readable text and binary is therefore
    positive proof the transform is right for that group, and its binary members are
    real payloads (DES input, key material), not failures. Groups that are entirely
    binary carry no such proof and are reported as unverified rather than passed.
    """
    g = defaultdict(list)
    for cls, items in res.items():
        for h in items:
            g[(cls, h['method'], h['decryptor'])].append(h)
    mixed = all_hi = all_lo = 0
    low_in_mixed = low_total = 0
    unverified = []
    for k, v in g.items():
        r = [printable_ratio(h['plain']) for h in v]
        has_hi = any(x >= hi for x in r)
        has_lo = any(x < lo for x in r)
        low_total += sum(1 for x in r if x < lo)
        if has_hi and has_lo:
            mixed += 1
            low_in_mixed += sum(1 for x in r if x < lo)
        elif has_lo:
            all_lo += 1
            unverified.append((k, len(v)))
        elif has_hi:
            all_hi += 1
    return {'groups': len(g), 'mixed': mixed, 'all_readable': all_hi,
            'all_binary': all_lo, 'low_total': low_total,
            'low_proven': low_in_mixed, 'low_unverified': low_total - low_in_mixed,
            'unverified_groups': sorted(unverified)[:20]}


JAVAP_HEADER = re.compile(r'^  (\S.*);\s*$')
JAVAP_INSN = re.compile(r'^\s+(\d+): ([a-z_0-9]+)')
JAVAP_LDC = re.compile(r'^\s+(\d+): (ldc2?_?w?)\s+#(\d+)')
MAX_JAVAP_PROBLEMS = 20


def _javap_run(files):
    r = subprocess.run(['javap', '-p', '-c'] + files, capture_output=True, text=True)
    if r.returncode != 0:
        raise UnseedError(f'javap failed: {r.stderr[:300]}')
    return r.stdout


def javap_member_blocks(text):
    """Split `javap -p -c` output into member-name -> [rows_of_occurrence_0, ...].

    Two traps, both of which fail silently if ignored:
      * javap prints the class initialiser as `public static {};` and a constructor
        as `<qualified.Name>(args);` - a naive header regex mislabels both.
      * OVERLOADED members share a name. javap emits each occurrence separately, in
        classfile order, so blocks are keyed by (name, occurrence index). Flattening
        them into one list lets the second body's bcis overwrite the first's and
        manufactures bogus "decoder mismatches".
    """
    blocks, cur = {}, None
    for line in text.splitlines():
        h = JAVAP_HEADER.match(line)
        if h:
            hdr = h.group(1).strip()
            if 'static {' in hdr:
                cur = '<clinit>'
            elif '(' not in hdr:
                cur = None                       # field declaration: no Code follows
            else:
                tok = hdr.split('(', 1)[0].split()[-1]
                cur = '<init>' if '.' in tok else tok
            if cur is not None:
                blocks.setdefault(cur, []).append([])   # one list per occurrence
            continue
        m = JAVAP_INSN.match(line)
        if m and cur is not None and blocks[cur]:
            ld = JAVAP_LDC.match(line)
            blocks[cur][-1].append((int(m.group(1)), m.group(2),
                                    int(ld.group(3)) if ld else None))
    if not blocks:
        raise UnseedError('javap produced no member blocks')
    return blocks


def _javap_blocks_for(cls, cf, workdir):
    """Write `cf` into `workdir`, run javap on it, -> javap_member_blocks()."""
    path = os.path.join(workdir, hashlib.sha1(cls.encode()).hexdigest()[:16] + '.class')
    _write_file(path, cf.data)
    return javap_member_blocks(_javap_run([path]))


def check_decoder_vs_javap(cfs, sample, workdir):
    """Every instruction offset+mnemonic this tool decodes must appear in javap's
    output for the same method occurrence. A one-byte length error anywhere shows
    up here as an offset divergence.

    -> (instructions_checked, mismatches, problems)
    """
    checked = mismatches = 0
    problems = []

    def note(cls, msg):
        if len(problems) < MAX_JAVAP_PROBLEMS:
            problems.append((cls, msg))

    for cls, cf in sample:
        try:
            blocks = _javap_blocks_for(cls, cf, workdir)
        except UnseedError as ex:
            problems.append((cls, f'javap: {ex}'))
            continue
        seen_occ = Counter()
        for m in cf.methods:
            occ = seen_occ[m['name']]
            seen_occ[m['name']] += 1
            try:
                insns, _meta = cf.insns(m)
            except UnseedError as ex:
                problems.append((cls, f'{m["name"]}: decode: {ex}'))
                continue
            if insns is None:
                continue
            occs = blocks.get(m['name'])
            if occs is None:
                problems.append((cls, f'{m["name"]}: javap has no such member'))
                continue
            if occ >= len(occs):
                problems.append((cls, f'{m["name"]}#{occ}: javap printed only '
                                      f'{len(occs)} occurrence(s)'))
                continue
            javap_names = {r[0]: r[1] for r in occs[occ]}
            for ins in insns:
                checked += 1
                jn = javap_names.get(ins.off)
                if jn != ins.name:
                    mismatches += 1
                    note(cls, f'{m["name"]}#{occ} bci {ins.off}: tool={ins.name} '
                              f'javap={jn if jn is not None else "<no instruction>"}')
    return checked, mismatches, problems


def check_attribution_vs_javap(cfs, sites, workdir):
    """Confirm the enclosing-method attribution using (bci, ldc, CP index) as an
    exact join key against javap. Returns (confirmed, refuted, unknown)."""
    confirmed = refuted = unknown = 0
    cache = {}
    for cls, hit in sites:
        cf = cfs.get(cls)
        if cf is None:
            unknown += 1
            continue
        if cls not in cache:
            try:
                cache[cls] = _javap_blocks_for(cls, cf, workdir)
            except UnseedError:
                cache[cls] = None
        blocks = cache[cls]
        if blocks is None:
            unknown += 1
            continue
        owners = {nm for nm, occs in blocks.items()
                  for rows in occs
                  if any(r[0] == hit['bci'] and r[2] == hit['ldc_cp']
                         and r[1] in ('ldc', 'ldc_w') for r in rows)}
        if hit['method'] in owners:
            confirmed += 1
        elif owners:
            refuted += 1
        else:
            unknown += 1
    return confirmed, refuted, unknown


# ==========================================================================
# 14. command-line interface
# ==========================================================================

def build(args):
    """Open the input and parse every class. -> (ClassSource, {entry: ClassFile})"""
    src = ClassSource(args.input)
    cfs, _fails = load_all(src, quiet=args.quiet)
    return src, cfs


def get_decryptors(cfs, args):
    tab, failures, stats = find_decryptors(cfs)
    print(f'decryptors: {stats["candidates"]} candidate(s), '
          f'{stats["frame_shaped"]} frame-shaped, {stats["extracted"]} extracted, '
          f'{len(failures)} failed')
    if stats['frame_shaped'] and stats['extracted'] != stats['frame_shaped']:
        # never let a shape we recognised disappear silently
        for c, m, why in failures[:20]:
            print(f'  EXTRACT-FAIL {c}.{m}: {why}', file=sys.stderr)
        if not args.allow_partial:
            raise SystemExit(f'FATAL: {stats["frame_shaped"] - stats["extracted"]} '
                             f'frame-shaped decryptor(s) failed to extract')
    for c, m, why in failures[:20]:
        print(f'  note: {c}.{m} not a decryptor / not extractable: {why}')
    return tab, failures, stats


def _print_counts(counter, limit=None):
    for k, v in counter.most_common(limit):
        print(f'  {v:6d}  {k}')


def cmd_scan(args):
    _src, cfs = build(args)
    tab, failures, stats = get_decryptors(cfs, args)
    rows, summary, bootstraps = indy_scan(cfs)
    res, unsup = scan_all(cfs, tab)
    lits, nunsup = count_sites(res), count_sites(unsup)
    seed_orders = dict(Counter('+'.join(d.seed_parts) for d in tab.values()))
    print(f'\nclasses parsed          : {len(cfs)}')
    print(f'string decryptors       : {len(tab)}  (seed orders: {seed_orders})')
    print(f'obfuscated literals     : {lits} in {len(res)} classes')
    print(f'unresolvable call sites : {nunsup}')
    print(f'\ninvokedynamic sites     : {len(rows)}')
    _print_counts(summary)
    print('\ntop bootstraps:')
    _print_counts(bootstraps, 8)
    if args.json:
        _write_json(args.json, {
            'classes': len(cfs), 'decryptors': [d.to_json() for d in tab.values()],
            'decryptor_stats': stats, 'decryptor_failures': failures,
            'literals': lits, 'classes_with_strings': len(res),
            'unresolvable_call_sites': nunsup,
            'indy_summary': dict(summary),
            'indy_bootstraps': [{'bootstrap': k, 'sites': v}
                                for k, v in bootstraps.most_common()]})
        print(f'\nwrote {args.json}')
    return 0


def cmd_strings(args):
    _src, cfs = build(args)
    tab, failures, _stats = get_decryptors(cfs, args)
    res, unsup = scan_all(cfs, tab)
    nunsup = count_sites(unsup)
    print(f'literals recovered      : {count_sites(res)} in {len(res)} classes')
    print(f'unresolvable call sites : {nunsup}')
    for c, v in list(unsup.items())[:10]:
        for it in v[:3]:
            print(f'  UNSUPPORTED {c}.{it["method"]} bci={it.get("bci")}: {it["why"]}')
    ratios = [printable_ratio(h['plain']) for v in res.values() for h in v]
    if ratios:
        print(f'mean printable ratio    : {sum(ratios) / len(ratios):.4f}')
    if args.grep:
        pat = re.compile(args.grep, re.I)
        print(f'\n=== matching {args.grep!r} ===')
        matches = [(cls, h) for cls, items in sorted(res.items()) for h in items
                   if pat.search(h['plain'])]
        for cls, h in matches:
            print(f'  {cls}.{h["method"]} bci={h["bci"]}: {h["plain"]!r}')
        print(f'  matches: {len(matches)}')
    if args.json:
        write_strings_json(args.json, res)
        print(f'\nwrote {args.json}')
    if args.report:
        write_strings_report(args.report, res, tab, failures, unsup)
        print(f'wrote {args.report}')
    return 0


def cmd_indy(args):
    _src, cfs = build(args)
    rows, summary, bootstraps = indy_scan(cfs)
    print(f'invokedynamic sites: {len(rows)}')
    _print_counts(summary)
    resolvable = summary['resolved-lambda']
    print(f'\nstatically resolved   : {resolvable} '
          f'({100.0 * resolvable / max(1, len(rows)):.1f}%)')
    print(f'NOT statically resolvable (native bootstrap): {summary["native-gated"]}')
    print('\nbootstraps:')
    _print_counts(bootstraps, 12)
    if args.json:
        write_indy_json(args.json, rows, summary, bootstraps)
        print(f'\nwrote {args.json}')
    if args.worklist:
        n = write_worklist(args.worklist, rows)
        print(f'wrote {args.worklist} ({n} sites needing runtime capture)')
    if args.show_resolved:
        print('\n=== resolved lambda targets (first 25) ===')
        shown = [r for r in rows if r['resolution'] == 'resolved-lambda' and 'target' in r]
        for r in shown[:25]:
            print(f'  {r["class"]}.{r["method"]} bci={r["bci"]} -> {r["target"]}')
    return 0


def cmd_patch(args):
    src, cfs = build(args)
    tab, _failures, _stats = get_decryptors(cfs, args)
    res, unsup = scan_all(cfs, tab)
    if unsup:
        print(f'WARNING: {count_sites(unsup)} call site(s) are not statically '
              f'resolvable and will stay obfuscated in the output', file=sys.stderr)
    outdir = os.path.abspath(args.out)
    cdir = os.path.join(outdir, 'classes')
    os.makedirs(cdir, exist_ok=True)
    manifest = []
    total_sites = 0
    for cls, hits in sorted(res.items()):
        entry = src.entry_for(cfs, cls)
        data = src.read(entry)
        patched, nsites, ncp = patch_class(cfs[entry], data, hits)
        check_patch(data, patched, tab, [h['plain'] for h in hits])
        _write_file(os.path.join(cdir, cls + '.class'), patched)
        total_sites += nsites
        manifest.append({'class': cls, 'sites': nsites, 'cp_entries_added': ncp,
                         'size_before': len(data), 'size_after': len(patched),
                         'sha256_before': hashlib.sha256(data).hexdigest(),
                         'sha256_after': hashlib.sha256(patched).hexdigest()})
    # classes with no sites are copied through unchanged so the tree stays complete
    copied = 0
    if args.copy_all:
        for entry in src.entries:
            cf = cfs.get(entry)
            if cf is not None and cf.this not in res:
                _write_file(os.path.join(cdir, cf.this + '.class'), src.read(entry))
                copied += 1
    mpath = args.json or os.path.join(outdir, 'patch-manifest.json')
    _write_json(mpath, {
        'input': src.path, 'classes_patched': len(manifest),
        'call_sites_inlined': total_sites, 'classes_copied_unchanged': copied,
        'note': 'analysis artifact: string constants inlined; no jar is '
                'assembled and nothing is re-signed',
        'classes': manifest})
    print(f'patched {len(manifest)} classes, inlined {total_sites} string constant(s)')
    print(f'copied through unchanged: {copied}')
    print(f'wrote {cdir}/ and {mpath}')
    return 0


# -- verify: one small function per check, each prints its own PASS/FAIL line and
# returns True when it holds. cmd_verify only sequences them. --

def _verify_bundled_control(args):
    """The tool's own positive control, on the bundled synthetic fixture.

    Deliberately run FIRST and independently of the user's input. If this fails,
    the tool is broken on its own known-good test case and nothing reported about
    the input afterwards can be trusted.
    """
    print(f'PASS  codec round-trips ({selftest()} cases)')
    try:
        fc = fixture_control(run_jvm=not args.no_jvm)
    except UnseedError as ex:
        print(f'FAIL  bundled-fixture control: {ex}')
        print('      the tool is broken independently of your input, so nothing '
              'below is meaningful')
        return False
    print(f'PASS  bundled-fixture control: {fc["sites_recovered"]}/'
          f'{fc["sites_expected"]} call sites, masks {fc["masks"][0]:#x}/'
          f'{fc["masks"][1]:#x}, {fc["spans"]} span(s) patched across '
          f'{fc["classes_patched"]} class(es), '
          f'{fc["stats"]["extracted"]}/{fc["stats"]["frame_shaped"]} extracted')
    print(f'      JVM oracle: {fc["jvm"]}')
    return True


def _verify_ground_truth(args, res):
    """Optional input-specific control: a string the user already knows is there."""
    truth = args.ground_truth
    if not truth:
        print('SKIP  known-string control: no --ground-truth given. Pass a string '
              'you already know this input contains (from a URL, an error message, '
              'a config key) for an input-specific control.')
        return True
    hit = [(c, h['method']) for c, v in res.items() for h in v if h['plain'] == truth]
    print(f'{"PASS " if hit else "FAIL "} known-string control {truth!r}: '
          f'{len(hit)} site(s) {hit[:2]}')
    return bool(hit)


def _verify_printable_ratio(args, res):
    ratios = [printable_ratio(h['plain']) for v in res.values() for h in v]
    mean = sum(ratios) / len(ratios) if ratios else 0.0
    low = sum(1 for r in ratios if r < 0.9)
    ok = mean >= args.min_printable
    print(f'{"PASS " if ok else "WARN "} mean printable ratio '
          f'{mean:.4f} (threshold {args.min_printable}); {low}/{len(ratios)} below 0.90')
    return ok or not args.strict            # a low ratio only fails under --strict


def _verify_consistency(res):
    """Is a low-printable literal real data, or a bad mask?"""
    pc = check_plaintext_consistency(res)
    has_power = pc['mixed'] > 0
    print(f'{"PASS " if has_power else "FAIL "} plaintext consistency: '
          f'{pc["groups"]} group(s) sharing one (seed,maskA,maskB) -> '
          f'{pc["all_readable"]} all-readable, {pc["mixed"]} mixed, '
          f'{pc["all_binary"]} all-binary')
    print(f'        {pc["low_proven"]}/{pc["low_total"]} low-printable literal(s) are '
          f'PROVEN data (their group also yielded readable text under the identical '
          f'seed+masks); {pc["low_unverified"]} unproven')
    if not has_power:
        print('        no mixed group exists, so this test has no power to '
              'distinguish "binary payload" from "wrong mask"')
    if pc['unverified_groups']:
        print(f'        unverified all-binary groups: {pc["unverified_groups"][:8]}')
    return has_power


def _verify_decoder_vs_javap(args, cfs, tab, workdir):
    """Cross-check the decoder on N classes: every decryptor class, plus a seeded
    random sample of the rest (so the same input always checks the same classes)."""
    dec_classes = sorted({d.owner + '.class' for d in tab.values()} & set(cfs))
    others = sorted(set(cfs) - set(dec_classes))
    rng = random.Random(20261013)
    extra = rng.sample(others, min(len(others), max(0, args.javap_check - len(dec_classes))))
    sample = [(k, cfs[k]) for k in dec_classes + extra]
    checked, mism, probs = check_decoder_vs_javap(cfs, sample, workdir)
    good = mism == 0 and not probs
    print(f'{"PASS " if good else "FAIL "} instruction decoder vs javap: '
          f'{checked} instruction(s) across {len(sample)} classes, '
          f'{mism} mismatch(es), {len(probs)} problem(s)')
    for p in probs[:8]:
        print(f'    {p[0]}: {p[1]}')
    return good


def _verify_attribution_vs_javap(args, cfs, src, res, workdir):
    """Cross-check that each literal sits in the method claimed (the method name
    is part of the seed, so a wrong attribution means a wrong plaintext)."""
    allsites = [(src.entry_for(cfs, c), h) for c, v in res.items() for h in v]
    sample = random.Random(4242).sample(allsites, min(args.javap_attrib, len(allsites)))
    conf, ref_, unk = check_attribution_vs_javap(cfs, sample, workdir)
    good = ref_ == 0 and conf > 0
    print(f'{"PASS " if good else "FAIL "} method attribution vs javap '
          f'(sample {len(sample)}): confirmed={conf} refuted={ref_} unknown={unk}')
    return good


def cmd_verify(args):
    print('=== unseed.py verify ===')
    if not _verify_bundled_control(args):
        return 2

    src, cfs = build(args)
    tab, failures, stats = get_decryptors(cfs, args)
    ok = stats['extracted'] == stats['frame_shaped'] and not failures
    print(f'{"PASS " if ok else "FAIL "} decryptor extraction: '
          f'{stats["extracted"]}/{stats["frame_shaped"]} frame-shaped, '
          f'{len(failures)} failure(s)')
    if not stats['frame_shaped']:
        print('NOTE  no frame-shaped decryptor in this input. The bundled-fixture '
              'control above PASSED, so the tool is working; the likeliest reading '
              'is that this input does not use the caller-seeded scheme described '
              'in the README. This is not a general deobfuscator - see '
              'the README for what it does and does not handle.')
        return 2

    res, unsup = scan_all(cfs, tab)
    nunsup = count_sites(unsup)
    print(f'{"PASS " if not nunsup else "FAIL "} call sites: {count_sites(res)} '
          f'recovered, {nunsup} unresolvable')

    checks = [ok, not nunsup,
              _verify_ground_truth(args, res),
              _verify_printable_ratio(args, res),
              _verify_consistency(res)]
    with tempfile.TemporaryDirectory() as workdir:
        if args.javap_check:
            checks.append(_verify_decoder_vs_javap(args, cfs, tab, workdir))
        if args.javap_attrib:
            checks.append(_verify_attribution_vs_javap(args, cfs, src, res, workdir))
    if args.reference:
        checks.append(verify_reference(args.reference, res) == 0)

    rc = 0 if all(checks) else 1
    print(f'\nverify: {"PASS" if rc == 0 else "FAIL"}')
    return rc


def verify_reference(path, res):
    """Diff against a reference JSON produced by an independent method.

    The reference format is `{dotted_class: [{method, ct, plain}, ...]}` - i.e.
    the shape `strings --json` writes, so any second implementation of the same
    scheme can be compared.

    A difference is not automatically a regression, and this function does not
    pretend otherwise. Because the seed IS the caller's identity, a reference
    built by scanning *decompiled source* tends to mis-attribute the enclosing
    method wherever its line scan walks past a method header into a `static {`
    block - and a wrong method means a wrong seed, so those plaintexts are wrong
    too. So the diff separates "method agrees but plaintext differs" (a real
    conflict, reported as FAIL) from "site attributed to a different method"
    (reported as a count, with --javap-attrib as the independent tie-breaker).
    """
    try:
        with open(path, encoding='utf-8') as f:
            ref = json.load(f)
    except (OSError, ValueError) as ex:
        print(f'FAIL  cannot read reference {path}: {ex}')
        return 1
    mine_by_key = defaultdict(list)
    for cls, items in res.items():
        for h in items:
            mine_by_key[(cls.replace('/', '.'), h['ct'])].append(h)
    identical = misattributed = ref_only = 0
    plain_conflict = []
    for dcls, items in ref.items():
        for r in items:
            cands = mine_by_key.get((dcls, r['ct']), [])
            same = [h for h in cands if h['method'] == r['method']]
            if same:
                if same[0]['plain'] == r['plain']:
                    identical += 1
                else:
                    plain_conflict.append((dcls, r['method'], same[0]['plain'], r['plain']))
            elif cands:
                misattributed += 1
            else:
                ref_only += 1
    print(f'\nreference diff vs {os.path.basename(path)}:')
    print(f'  reference literals          : {count_sites(ref)}')
    print(f'  this tool                   : {count_sites(res)}')
    print(f'  identical (class,method,ct) : {identical}')
    print(f'  reference method disputed   : {misattributed}')
    print(f'  reference-only sites        : {ref_only}')
    ok = not plain_conflict
    print(f'  {"PASS " if ok else "FAIL "} plaintext conflicts where the method agrees: '
          f'{len(plain_conflict)}')
    for c in plain_conflict[:5]:
        print(f'    {c[0]}.{c[1]}: tool={c[2]!r} ref={c[3]!r}')
    if misattributed:
        print(f'  NOTE  {misattributed} reference literal(s) sit at a site this tool '
              f'attributes to a different method. Since the seed is the caller '
              f'identity, a different method means a different seed, so the '
              f'reference plaintext is the suspect one - typically a source-level '
              f'scan that walked past a method header into a `static {{` block. '
              f'Run --javap-attrib to confirm independently.')
    return 0 if ok else 1


def build_parser():
    """Build the CLI parser. Split out from main() so tests can inspect the
    declared arguments and their defaults without invoking a subcommand."""
    ap = argparse.ArgumentParser(
        prog='unseed.py',
        description='Verified Java classfile surgery, with a caller-seeded string '
                    'extractor as the worked example. Not a general deobfuscator: '
                    'see the module docstring and README for exact scope.')
    sub = ap.add_subparsers(dest='cmd', required=True)

    def add_command(name, fn, help, takes_input=True, jvm_opts=False):
        p = sub.add_parser(name, help=help)
        if takes_input:
            p.add_argument('input', help='jar/zip or a directory of .class files')
            p.add_argument('--json', help='write machine-readable results to this file')
            p.add_argument('--quiet', action='store_true',
                           help='do not warn about classfiles that fail to parse')
            p.add_argument('--allow-partial', action='store_true',
                           help='continue even if a frame-shaped decryptor fails to extract')
        if jvm_opts:
            p.add_argument('--no-jvm', action='store_true',
                           help='skip the JVM oracle checks (never invoke `java`)')
            p.add_argument('--require-jvm', action='store_true',
                           help='fail instead of skipping when no JVM is available')
        p.set_defaults(fn=fn)
        return p

    add_command('selftest', cmd_selftest, takes_input=False, jvm_opts=True,
                help='run the bundled-fixture control; needs no input artifact')
    add_command('scan', cmd_scan, help='census: decryptors + invokedynamic')

    p = add_command('strings', cmd_strings, help='recover every obfuscated string literal')
    p.add_argument('--report', help='write a human-readable report to this file')
    p.add_argument('--grep', help='regex filter on recovered plaintext')

    p = add_command('indy', cmd_indy, help='invokedynamic census + runtime-capture worklist')
    p.add_argument('--worklist', help='write the sites needing runtime capture to this file')
    p.add_argument('--show-resolved', action='store_true',
                   help='list the first resolved lambda targets')

    p = add_command('patch', cmd_patch, help='emit rewritten .class files with plaintext inlined')
    p.add_argument('--out', required=True, help='output directory')
    p.add_argument('--copy-all', action='store_true',
                   help='also copy classes with no obfuscated strings, so the tree is complete')

    p = add_command('verify', cmd_verify, jvm_opts=True,
                    help='run every post-condition and cross-check')
    p.add_argument('--reference',
                   help='reference JSON to diff against, in the format '
                        '`strings --json` writes')
    p.add_argument('--ground-truth',
                   help='a plaintext string you already know this input contains; '
                        'used as an input-specific positive control')
    p.add_argument('--min-printable', type=float, default=0.85,
                   help='warn when the mean printable ratio is below this (default: %(default)s)')
    p.add_argument('--strict', action='store_true',
                   help='treat a low printable ratio as a failure, not a warning')
    p.add_argument('--javap-check', type=int, default=0,
                   help='cross-check the instruction decoder against javap on N classes')
    p.add_argument('--javap-attrib', type=int, default=0,
                   help='cross-check method attribution against javap on N sites')
    p.add_argument('--ref-attrib-sample', type=int, default=0,
                   help='ignored; kept so existing command lines keep working')
    return ap


def main(argv=None):
    args = build_parser().parse_args(argv)
    return args.fn(args)


if __name__ == '__main__':
    sys.exit(main())
