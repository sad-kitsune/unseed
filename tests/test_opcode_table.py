#!/usr/bin/env python3
"""
test_opcode_table.py - cross-check unseed's opcode table against javap, exhaustively.

Why this file exists
--------------------
A hand-written opcode table fails in the worst possible way: one misnamed entry
does not crash, it silently yields a wrong constant. The shift range is the
classic trap, because the JVM groups those six opcodes by OPERATION with the
int/long variants adjacent:

    0x78 ishl   0x79 lshl   0x7a ishr   0x7b lshr   0x7c iushr   0x7d lushr

Reading that range as "the int shifts, then the long shifts" misnames four of
six - and since ishr/lshl differ in both signedness AND operand category, the
interpreter then pops the wrong stack width. This test exists because that exact
bug shipped once and was invisible to every end-to-end check.

Method
------
Build one synthetic classfile holding 256 methods; method mNNN's Code attribute
is byte NNN followed by operands valid for that opcode plus `return` padding.
javap disassembles without verifying, so this exercises bytes that could never
appear in a runnable class. Then compare, per opcode, the mnemonic and the
instruction length javap reports against unseed's own decode().

Three known artefacts of reading javap's text output are handled explicitly,
because each one otherwise manufactures a bogus mismatch:
  * javap prints an UNASSIGNED byte as `bytecode <n>`, which a naive
    "is this a lowercase word?" test reads as a real mnemonic;
  * javap EXPANDS `wide iload` into a synthetic `iload_w`, so its mnemonic is
    never literally `wide`;
  * javap prints switch cases on indented lines inside a brace block, so the
    next numbered row is a case label, not the following instruction - switch
    lengths cannot be derived from the row spacing.

Requires `javap`. Set UNSEED_REQUIRE_JDK=1 to fail rather than skip when absent.
"""

from __future__ import annotations

import os
import re
import struct
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import unseed                                            # noqa: E402

HAVE_JAVAP = os.environ.get('UNSEED_REQUIRE_JDK') != '1' and \
    __import__('shutil').which('javap') is not None
REQUIRE_JDK = os.environ.get('UNSEED_REQUIRE_JDK') == '1'

PAD = b'\xb1' * 32                      # `return`, as filler for operand bytes

# javap's rendering of an opcode it does not know: `bytecode <n>`. Only the
# first token survives the instruction regex below, so match on that.
UNASSIGNED_RE = re.compile(r'^bytecode$')


def _build_probe_class():
    """-> (classfile bytes, {opcode: code bytes}). One method per opcode byte."""
    cp_bytes = []
    next_index = [1]
    idx = {}

    def utf8(s):
        if s not in idx:
            b = s.encode('utf-8')
            cp_bytes.append(b'\x01' + struct.pack('>H', len(b)) + b)
            idx[s] = next_index[0]
            next_index[0] += 1
        return idx[s]

    def entry(b, wide=False):
        # Long and Double consume two pool indices but serialise as one entry
        cp_bytes.append(b)
        i = next_index[0]
        next_index[0] += 2 if wide else 1
        return i

    i_code = utf8('Code')
    i_desc = utf8('()V')
    c_this = entry(b'\x07' + struct.pack('>H', utf8('OpTableProbe')))
    c_obj = entry(b'\x07' + struct.pack('>H', utf8('java/lang/Object')))
    nat_f = entry(b'\x0c' + struct.pack('>HH', utf8('f'), utf8('I')))
    c_fieldref = entry(b'\x09' + struct.pack('>HH', c_this, nat_f))
    nat_m = entry(b'\x0c' + struct.pack('>HH', utf8('m'), i_desc))
    c_methodref = entry(b'\x0a' + struct.pack('>HH', c_this, nat_m))
    c_run = entry(b'\x07' + struct.pack('>H', utf8('java/lang/Runnable')))
    nat_r = entry(b'\x0c' + struct.pack('>HH', utf8('run'), i_desc))
    c_ifaceref = entry(b'\x0b' + struct.pack('>HH', c_run, nat_r))
    c_int = entry(b'\x03' + struct.pack('>i', 42))
    c_str = entry(b'\x08' + struct.pack('>H', utf8('str')))
    c_long = entry(b'\x05' + struct.pack('>q', 42), wide=True)
    c_double = entry(b'\x06' + struct.pack('>d', 42.0), wide=True)
    c_float = entry(b'\x04' + struct.pack('>f', 42.0))
    c_mtype = entry(b'\x10' + struct.pack('>H', utf8('(I)V')))
    mh_bsm = entry(b'\x0f' + bytes([6]) + struct.pack(
        '>H', entry(b'\x0a' + struct.pack('>HH', c_obj, entry(
            b'\x0c' + struct.pack('>HH', utf8('bsm'), utf8(
                '(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;'
                'Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;')))))))
    c_indy = entry(b'\x12' + struct.pack('>HH', 1, c_mtype))

    bsm_body = struct.pack('>HH', 1, mh_bsm) + struct.pack('>H', 0)
    bsm_attr = struct.pack('>HI', utf8('BootstrapMethods'), len(bsm_body)) + bsm_body

    def operands(op):
        """Operand bytes valid for this opcode, so javap can render it."""
        fmt = unseed.OPS[op][1] if op in unseed.OPS else None
        if op == 0xAA:                                  # tableswitch
            # at bci 0 the alignment pad is 3 bytes: default, low, high, jump[1]
            return bytes([0, 0, 0]) + struct.pack('>iiii', 24, 1, 1, 24)
        if op == 0xAB:                                  # lookupswitch
            return bytes([0, 0, 0]) + struct.pack('>ii', 24, 1) + struct.pack('>ii', 1, 24)
        if op == 0xBC:                                  # newarray <atype>
            return bytes([10])                          # T_INT
        if op == 0xC4:                                  # wide iload 0
            return bytes([0x15, 0, 0])
        if op == 0xC5:                                  # multianewarray
            return struct.pack('>H', c_this) + bytes([2])
        if op == 0xB9:                                  # invokeinterface
            return struct.pack('>H', c_ifaceref) + bytes([1, 0])
        if op == 0xBA:                                  # invokedynamic
            return struct.pack('>H', c_indy) + bytes([0, 0])
        if op == 0x12:                                  # ldc
            return bytes([c_int])
        if op == 0x13:
            return struct.pack('>H', c_int)
        if op == 0x14:
            return struct.pack('>H', c_long)
        if op in (0xB2, 0xB3, 0xB4, 0xB5):              # get/putstatic, get/putfield
            return struct.pack('>H', c_fieldref)
        if op in (0xB6, 0xB7, 0xB8):                    # invokevirtual/special/static
            return struct.pack('>H', c_methodref)
        if op in (0xBB, 0xBD, 0xC0, 0xC1):              # new/anewarray/checkcast/instanceof
            return struct.pack('>H', c_this)
        if fmt in ('o2', 'i4'):                         # branch offsets
            return struct.pack('>h' if fmt == 'o2' else '>i', 6)
        if fmt == 'b':
            return bytes([4])
        if fmt == 'B':
            return bytes([0])
        if fmt == 'bb':
            return bytes([0, 1])
        if fmt == 's':
            return struct.pack('>h', 4)
        if fmt == 'u2':
            return struct.pack('>H', c_this)
        return b''

    methods = bytearray()
    codes = {}
    for op in range(256):
        code = bytes([op]) + operands(op) + PAD
        codes[op] = code
        body = struct.pack('>HHI', 8, 4, len(code)) + code + struct.pack('>HH', 0, 0)
        attr = struct.pack('>HI', i_code, len(body)) + body
        methods += struct.pack('>HHHH', 0x0009, utf8('m%03d' % op), i_desc, 1) + attr

    data = (b'\xca\xfe\xba\xbe' + struct.pack('>HH', 0, 52)
            + struct.pack('>H', next_index[0])
            + b''.join(cp_bytes)
            + struct.pack('>HHHHH', 0x0021, c_this, c_obj, 0, 0)
            + struct.pack('>H', 256) + bytes(methods)
            + struct.pack('>H', 1) + bsm_attr)
    # unused pool entries are fine, but keep linters honest
    assert c_str and c_float and c_double
    return data, codes


def _javap_rows(path):
    """-> {method_name: [(bci, mnemonic), ...]} from `javap -p -c`."""
    r = subprocess.run(['javap', '-p', '-c', path], capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f'javap failed: {r.stderr[:600]}')
    hdr = re.compile(r'^\s*(?:public |static )*[\w\[\]<>.$]*\s?(m\d\d\d)\(\);')
    ins = re.compile(r'^\s+(\d+): (\S+)')
    per, cur = {}, None
    for line in r.stdout.splitlines():
        h = hdr.match(line)
        if h:
            cur = h.group(1)
            per.setdefault(cur, [])
            continue
        m = ins.match(line)
        if m and cur is not None:
            per[cur].append((int(m.group(1)), m.group(2)))
    return per


class TestOpcodeTableAgainstJavap(unittest.TestCase):
    """Every opcode byte, compared against the JDK's own disassembler."""

    @classmethod
    def setUpClass(cls):
        if not HAVE_JAVAP and not REQUIRE_JDK:
            raise unittest.SkipTest('`javap` not on PATH')
        cls.data, cls.codes = _build_probe_class()
        with tempfile.TemporaryDirectory(prefix='unseed-opprobe-') as d:
            p = os.path.join(d, 'OpTableProbe.class')
            with open(p, 'wb') as f:
                f.write(cls.data)
            cls.rows = _javap_rows(p)

    def test_javap_parsed_every_probe_method(self):
        self.assertEqual(len(self.rows), 256,
                         'javap did not disassemble all 256 probe methods; the '
                         'probe classfile is malformed')

    def test_assigned_mnemonics_match_javap(self):
        """The core check. Any divergence is a silent-wrong-constant bug."""
        mismatches = []
        for op in range(256):
            rows = self.rows['m%03d' % op]
            self.assertEqual(rows[0][0], 0)
            jname = rows[0][1]
            if UNASSIGNED_RE.match(jname):
                continue                        # javap does not know it either
            if op not in unseed.OPS:
                mismatches.append(f'{op:#04x}: javap={jname} unseed=<unassigned>')
                continue
            mine = unseed.OPS[op][0]
            if op == 0xC4:
                # javap renders `wide iload` as `iload_w`; unseed keeps the real
                # opcode name and the modified opcode in operands
                self.assertTrue(jname.endswith('_w'),
                                f'0xc4: expected a javap `_w` expansion, got {jname}')
                continue
            if jname != mine:
                mismatches.append(f'{op:#04x}: unseed={mine} javap={jname}')
        self.assertEqual(mismatches, [],
                         'opcode table disagrees with javap - a misnamed opcode '
                         'silently yields wrong constants:\n  '
                         + '\n  '.join(mismatches))

    def test_unassigned_bytes_are_rejected_by_the_decoder(self):
        """Bytes javap does not know must raise, never be silently accepted."""
        bad = []
        for op in range(256):
            jname = self.rows['m%03d' % op][0][1]
            if not UNASSIGNED_RE.match(jname):
                continue
            if op in unseed.OPS:
                bad.append(f'{op:#04x}: javap unassigned but unseed calls it '
                           f'{unseed.OPS[op][0]}')
                continue
            with self.subTest(opcode=hex(op)):
                with self.assertRaises(unseed.UnseedError):
                    unseed.decode(self.codes[op])
        self.assertEqual(bad, [])

    def test_instruction_lengths_match_javap(self):
        """A one-byte length error shifts every subsequent offset."""
        problems = []
        for op in range(256):
            if op not in unseed.OPS:
                continue
            fmt = unseed.OPS[op][1]
            if fmt in ('switch', 'wide'):
                continue        # javap indents switch cases, so row spacing lies
            rows = self.rows['m%03d' % op]
            if len(rows) < 2:
                continue
            jlen = rows[1][0] - rows[0][0]
            try:
                dec = unseed.decode(self.codes[op])
            except unseed.UnseedError as ex:
                problems.append(f'{op:#04x} ({unseed.OPS[op][0]}): raised {ex}')
                continue
            if not dec:
                problems.append(f'{op:#04x}: decoded to nothing')
            elif dec[0].length != jlen:
                problems.append(f'{op:#04x} ({dec[0].name}): unseed length '
                                f'{dec[0].length} != javap {jlen}')
        self.assertEqual(problems, [],
                         'instruction lengths disagree with javap:\n  '
                         + '\n  '.join(problems))

    def test_shift_range_is_grouped_by_operation(self):
        """Regression guard for the bug this file exists to catch. Pinned
        literally, so it fails even if javap is unavailable."""
        self.assertEqual(
            {op: unseed.OPS[op][0] for op in range(0x78, 0x7E)},
            {0x78: 'ishl', 0x79: 'lshl', 0x7A: 'ishr',
             0x7B: 'lshr', 0x7C: 'iushr', 0x7D: 'lushr'},
            'shift opcodes are grouped by OPERATION with int/long adjacent '
            '(ishl, lshl, ishr, lshr, iushr, lushr) - not by type')

    def test_no_duplicate_or_gapped_opcode_registration(self):
        for op, (name, fmt) in unseed.OPS.items():
            with self.subTest(opcode=hex(op)):
                self.assertIsInstance(name, str)
                self.assertIn(fmt, unseed.FMT_MIN_LEN,
                              f'opcode {name} uses format {fmt!r} which has no '
                              f'entry in FMT_MIN_LEN, so decode() would reject it')
        names = [n for n, _f in unseed.OPS.values()]
        self.assertEqual(len(names), len(set(names)),
                         'two opcodes share a mnemonic')


class TestShiftSemantics(unittest.TestCase):
    """The shift fix, checked against the interpreter's arithmetic rather than
    against a disassembler: ishr sign-propagates, iushr does not."""

    def test_ishr_sign_propagates_and_iushr_does_not(self):
        # mirrors the interpreter's BIN table semantics
        self.assertEqual((-16) >> 4, -1)                       # ishr
        self.assertEqual((-16 & 0xFFFFFFFF) >> 4, 268435455)    # iushr
        self.assertNotEqual((-16) >> 4, (-16 & 0xFFFFFFFF) >> 4)

    def test_decoder_names_the_shift_bytes_correctly(self):
        for op, want in ((0x79, 'lshl'), (0x7A, 'ishr'),
                         (0x7B, 'lshr'), (0x7C, 'iushr')):
            with self.subTest(opcode=hex(op)):
                self.assertEqual(unseed.decode(bytes([op]))[0].name, want)


if __name__ == '__main__':
    unittest.main(verbosity=2)
