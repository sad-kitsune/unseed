#!/usr/bin/env python3
"""
make_fixture.py - generate the synthetic test fixture for unseed.py.

Why this file exists
--------------------
The fixture is a *synthetic* class carrying the same decryptor shape unseed.py
targets: a `static String d(String)` whose key is derived from the CALLER's
identity (class name + method name, read off a stack-trace frame), and whose
loop is a pairwise XOR over UTF-16 code units with two alternating masks and a
third, unused "decoy" constant in the prologue.

Nothing here comes from any third-party artifact. The class is written from the
documented algorithm, compiled by javac, and shipped in tests/fixtures/ so the
test suite needs no JDK and no proprietary input to prove the tool works.

Provenance / non-circularity
----------------------------
The ciphertexts are produced by `encrypt_units` below, which is the *inverse*
formula written out independently of unseed.py -- not an inversion of the tool's
own code at runtime. `_reference_decrypt_units` is a second, naive
implementation of the decrypt direction, used only to self-check the generator:
if encrypt/decrypt-ref disagree, this script fails before writing anything.

The stronger check happens in the test suite, which runs the compiled fixture
under a real JVM and asserts the strings Java actually produces match
expected.json. So expected.json is corroborated by an independent oracle (the
JVM), not just by this script.

Usage
-----
    python3 tests/make_fixture.py            # write .java + expected.json, compile
    python3 tests/make_fixture.py --no-compile
"""

from __future__ import annotations

import argparse
import json
import os
import struct
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
FIXTURES = os.path.join(HERE, 'fixtures')
JAVA_SRC = os.path.join(FIXTURES, 'SeedFixture.java')
EXPECTED = os.path.join(FIXTURES, 'expected.json')

PACKAGE = 'unseed.fixture'
OUTER = 'SeedFixture'
OUTER_INTERNAL = f'{PACKAGE.replace(".", "/")}/{OUTER}'
OUTER_DOTTED = f'{PACKAGE}.{OUTER}'
NESTED_INTERNAL = f'{OUTER_INTERNAL}$Nested'
NESTED_DOTTED = f'{OUTER_DOTTED}$Nested'

# The three prologue constants. Only MASK_A and MASK_B are read by the loop;
# DECOY is stored to a local and never used. That is the property the extractor
# must respect: masks are identified by which constants reach an `ixor` against
# a char inside the loop, never by their position in the prologue.
MASK_A = 0x5A3C
MASK_B = 0x3C5A
DECOY = 0x1234

# Each mask is emitted as `(base [^ X] ) << 1` so javac cannot constant-fold it
# away (a non-final local is never a "constant variable" per JLS 4.12.4), which
# keeps the real ishl/ixor instructions in the prologue for the interpreter to
# evaluate. XOR_A is folded into maskA's expression purely to exercise ixor.
XOR_A = 0x1111

SEED_PARTS = ['ClassName', 'MethodName']


# --------------------------------------------------------------------------
# UTF-16 code units (what Java charAt indexes)
# --------------------------------------------------------------------------

def utf16_units(s: str) -> list:
    raw = s.encode('utf-16-be')
    return list(struct.unpack('>%dH' % (len(raw) // 2), raw))


def from_utf16_units(units) -> str:
    res = []
    j = 0
    while j < len(units):
        u = units[j]
        if 0xD800 <= u <= 0xDBFF and j + 1 < len(units) and 0xDC00 <= units[j + 1] <= 0xDFFF:
            res.append(chr(0x10000 + ((u - 0xD800) << 10) + (units[j + 1] - 0xDC00)))
            j += 2
        elif 0xD800 <= u <= 0xDFFF:
            raise ValueError(f'lone surrogate U+{u:04X}')
        else:
            res.append(chr(u))
            j += 1
    return ''.join(res)


# --------------------------------------------------------------------------
# the cipher, written independently of unseed.py
# --------------------------------------------------------------------------

def encrypt_units(pt_units, seed_units, mask_a, mask_b):
    """Inverse of the documented decrypt walk.

    decrypt computes, walking i downward from the top and n downward (wrapping):
        out[i] = maskA ^ (ct[i] ^ seed[n]);  i--
        out[i] = maskB ^ (ct[i] ^ seed[n]);  i--;  n-- (wrap)
    XOR is its own inverse, so over the *identical* index walk:
        ct[i]  = maskA ^ (out[i] ^ seed[n])
        ct[i]  = maskB ^ (out[i] ^ seed[n])
    """
    if not pt_units:
        return []
    if not seed_units:
        raise ValueError('empty seed')
    ct = [0] * len(pt_units)
    n = n_wrap = len(seed_units) - 1
    i = len(pt_units) - 1
    while i >= 0:
        ct[i] = (mask_a ^ (pt_units[i] ^ seed_units[n])) & 0xFFFF
        i -= 1
        if i < 0:
            break
        ct[i] = (mask_b ^ (pt_units[i] ^ seed_units[n])) & 0xFFFF
        i -= 1
        n -= 1
        if n < 0:
            n = n_wrap
    return ct


def _reference_decrypt_units(ct_units, seed_units, mask_a, mask_b):
    """A second, naive implementation of the decrypt direction, straight from the
    formula. Used only to self-check `encrypt_units`."""
    if not ct_units:
        return []
    if not seed_units:
        raise ValueError('empty seed')
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


def encrypt(plain: str, seed: str, mask_a=MASK_A, mask_b=MASK_B) -> str:
    ct = encrypt_units(utf16_units(plain), utf16_units(seed), mask_a, mask_b)
    back = _reference_decrypt_units(ct, utf16_units(seed), mask_a, mask_b)
    if from_utf16_units(back) != plain:
        raise AssertionError(f'generator self-check failed for {plain!r}')
    return from_utf16_units(ct)


# --------------------------------------------------------------------------
# Java source-literal escaping
# --------------------------------------------------------------------------

def java_literal(s: str) -> str:
    r"""Render `s` as a Java string literal, pure-ASCII and pre-lexer safe.

    Java translates every \uXXXX escape *before* lexing, so emitting \u000a or
    \u0022 raw would inject a line terminator or a quote into the literal. Those
    four units (plus NUL, for source hygiene) go out as octal escapes instead,
    which are handled by the lexer and are not pre-translated.
    """
    octal = {0x00: r'\0', 0x0A: r'\012', 0x0D: r'\015', 0x22: r'\042', 0x5C: r'\134'}
    out = ['"']
    for u in utf16_units(s):
        if u in octal:
            out.append(octal[u])
        elif 0x20 <= u < 0x7F:
            out.append(chr(u))
        else:
            out.append('\\u%04x' % u)
    out.append('"')
    return ''.join(out)


# --------------------------------------------------------------------------
# the fixture sites
# --------------------------------------------------------------------------

# (token, internal class, method name, plaintext)
#
# The plaintexts are chosen to stress the parts that break silently elsewhere:
#   - a resource-path style string containing '$' and '/'
#   - an embedded NUL, which modified UTF-8 encodes as 0xC0 0x80 (never 0x00)
#   - a supplementary character, which modified UTF-8 stores as a CESU-8 pair
#   - 2-byte and 3-byte BMP forms, including U+007F / U+0080 / U+07FF boundaries
#
# The last two sites deliberately share ONE method. Because the seed is the
# caller's identity, every site in a method shares a seed and masks, so they
# form a single group for the plaintext-consistency check. A group holding both
# readable text and a low-printable payload is positive proof the transform is
# right for that group - which is what distinguishes "this literal really is
# binary data" from "we recovered the wrong mask". Every other site sits in its
# own method, so without this pair no group could ever be mixed and that check
# would have no power at all.
SITES = [
    ('CLINIT', OUTER_INTERNAL, '<clinit>', '/unseed/fixture/SeedFixture'),
    ('METHOD', OUTER_INTERNAL, 'fromMethod', 'hello world'),
    ('INIT', OUTER_INTERNAL, '<init>', 'has\x00NUL inside'),
    ('CAST', OUTER_INTERNAL, 'viaCast', 'emoji \U0001F600 end'),
    ('MAIN', OUTER_INTERNAL, 'main', 'caf\u00e9 \u4e2d\u6587 \x7f\x80\u07ff'),
    ('NESTED', NESTED_INTERNAL, '<clinit>', 'nested $ class name'),
    ('MIXTEXT', OUTER_INTERNAL, 'emitMixed', 'readable text in a shared method'),
    ('MIXBLOB', OUTER_INTERNAL, 'emitMixed', '\x01\x02\x03key\x04\x05\xff'),
]


def seed_for(internal: str, method: str) -> str:
    dotted = internal.replace('/', '.')
    return ''.join(dotted if p == 'ClassName' else method for p in SEED_PARTS)


def build_sites():
    rows = []
    for token, internal, method, plain in SITES:
        seed = seed_for(internal, method)
        ct = encrypt(plain, seed)
        rows.append({'token': token, 'class': internal, 'dotted': internal.replace('/', '.'),
                     'method': method, 'plain': plain, 'seed': seed, 'ct': ct})
    return rows


# --------------------------------------------------------------------------
# Java source
# --------------------------------------------------------------------------

JAVA_TEMPLATE = r'''// GENERATED by tests/make_fixture.py - do not edit by hand.
// Regenerate with:  python3 tests/make_fixture.py
//
// Synthetic fixture for unseed.py. This class is written from the documented
// algorithm and contains no code from any third-party artifact. It carries the
// shape the tool targets:
//
//   * the decryptor's key is the CALLER's identity (class name + method name),
//     read from a stack-trace frame, so a ciphertext is only meaningful at the
//     one call site that produced it;
//   * three constant expressions are computed in the prologue and only two are
//     read by the loop, so masks cannot be recovered positionally;
//   * dead junk sits between the seed construction and the loop.
//
// main() prints every recovered string as backslash-u hex escapes, so a real JVM
// can act as an independent oracle for the static extraction (output is pure
// ASCII and therefore exactly comparable, NUL and supplementary characters
// included). Note this comment cannot spell that escape sequence literally:
// Java translates unicode escapes before lexing, even inside comments.
package __PACKAGE__;

public class __OUTER__ {

    // ---- the decryptor -------------------------------------------------
    // `static String d(String)`, seeded from the caller's stack-trace frame.
    static String d(String s) {
        // frame[0] is d itself; frame[1] is the caller whose identity is the key.
        // The receiver is declared as Throwable on purpose: the constant pool
        // records the *declared* receiver type at the call site.
        Throwable t = new RuntimeException();
        StackTraceElement frame = t.getStackTrace()[1];
        String seed = new StringBuffer(frame.getClassName())
                          .append(frame.getMethodName())
                          .toString();

        // dead junk of the kind that surrounds real decryptors: it must not
        // disturb constant recovery (fconst_1/invokestatic/pop, invokevirtual/pop)
        String.valueOf(1.0f);
        s.hashCode();

        // three constants; DECOY is stored and never read again
        int baseA = __BASE_A__;
        int baseDecoy = __BASE_DECOY__;
        int baseB = __BASE_B__;
        int maskA = (baseA ^ __XOR_A__) << 1;
        int decoy = baseDecoy << 1;
        int maskB = baseB << 1;

        char[] out = new char[s.length()];
        int i = s.length() - 1;
        int n = seed.length() - 1;
        while (i >= 0) {
            out[i] = (char) (maskA ^ (s.charAt(i) ^ seed.charAt(n)));
            i--;
            if (i < 0) {
                break;
            }
            out[i] = (char) (maskB ^ (s.charAt(i) ^ seed.charAt(n)));
            i--;
            n--;
            if (n < 0) {
                n = seed.length() - 1;
            }
        }
        return new String(out);
    }

    // ---- call sites ----------------------------------------------------
    // each ciphertext is only decryptable from the site that holds it, because
    // the seed is that site's class name + method name

    // <clinit>
    static final String FROM_CLINIT = d(__CT_CLINIT__);

    // a plain static method
    static String fromMethod() {
        return d(__CT_METHOD__);
    }

    // <init>
    final String fromInit;

    __OUTER__() {
        fromInit = d(__CT_INIT__);
    }

    // a call site with an explicit `checkcast String` between the ldc and the
    // invokestatic, which the scanner must look through
    static String viaCast() {
        return d((String) (Object) __CT_CAST__);
    }

    // a nested class, so the seed contains a '$'
    static class Nested {
        static final String VALUE = d(__CT_NESTED__);
    }

    // TWO call sites in ONE method. Same method means same seed, so these two
    // form a single group for the plaintext-consistency check: one readable
    // literal plus one low-printable payload proves the recovered masks are
    // right for that group, rather than leaving it merely "all binary".
    static void emitMixed(StringBuilder sb) {
        emit(sb, "mixtext", d(__CT_MIXTEXT__));
        emit(sb, "mixblob", d(__CT_MIXBLOB__));
    }

    // ---- the oracle ----------------------------------------------------
    public static void main(String[] args) {
        __OUTER__ f = new __OUTER__();
        StringBuilder sb = new StringBuilder();
        emit(sb, "clinit", FROM_CLINIT);
        emit(sb, "method", fromMethod());
        emit(sb, "init", f.fromInit);
        emit(sb, "cast", viaCast());
        emit(sb, "main", d(__CT_MAIN__));
        emit(sb, "nested", Nested.VALUE);
        emitMixed(sb);
        System.out.print(sb.toString());
    }

    // Print one recovered string as backslash-u hex escapes: pure ASCII out, so
    // NUL, quotes and supplementary characters all survive the console unchanged.
    static void emit(StringBuilder sb, String key, String value) {
        sb.append(key).append('=');
        for (int i = 0; i < value.length(); i++) {
            int u = value.charAt(i);
            sb.append("\\u");
            sb.append(HEX[(u >> 12) & 0xF]);
            sb.append(HEX[(u >> 8) & 0xF]);
            sb.append(HEX[(u >> 4) & 0xF]);
            sb.append(HEX[u & 0xF]);
        }
        sb.append('\n');
    }

    static final char[] HEX = "0123456789abcdef".toCharArray();
}
'''


def build_java(rows) -> str:
    src = JAVA_TEMPLATE
    subs = {
        '__PACKAGE__': PACKAGE,
        '__OUTER__': OUTER,
        '__BASE_A__': hex((MASK_A >> 1) ^ XOR_A),
        '__BASE_DECOY__': hex(DECOY >> 1),
        '__BASE_B__': hex(MASK_B >> 1),
        '__XOR_A__': hex(XOR_A),
    }
    for r in rows:
        subs[f'__CT_{r["token"]}__'] = java_literal(r['ct'])
    for k, v in subs.items():
        if k not in src:
            raise AssertionError(f'template has no placeholder {k}')
        src = src.replace(k, v)
    leftover = [t for t in ('__CT_', '__BASE_', '__PACKAGE__', '__OUTER__') if t in src]
    if leftover:
        raise AssertionError(f'unsubstituted placeholders: {leftover}')
    return src


# --------------------------------------------------------------------------
# self-checks on the constants
# --------------------------------------------------------------------------

def check_masks():
    """The Java expressions in the template must evaluate to the masks we claim."""
    for name, val, base, xor in (('MASK_A', MASK_A, (MASK_A >> 1) ^ XOR_A, XOR_A),
                                 ('DECOY', DECOY, DECOY >> 1, 0),
                                 ('MASK_B', MASK_B, MASK_B >> 1, 0)):
        if val & 1:
            raise AssertionError(f'{name}={val:#x} is odd; template uses `<< 1`')
        computed = ((base ^ xor) << 1) & 0xFFFFFFFF
        # Java int semantics, then the tool truncates a mask to 16 bits
        if computed >= 0x80000000:
            computed -= 0x100000000
        if computed & 0xFFFF != val:
            raise AssertionError(f'{name}: expression yields {computed:#x}, want {val:#x}')
    if len({MASK_A, MASK_B, DECOY}) != 3:
        raise AssertionError('masks and decoy must be distinct, else the test is vacuous')


def generator_selfcheck():
    """Round-trip the generator's own cipher over adversarial inputs."""
    seeds = ['a', 'ab', 'unseed.fixture.SeedFixture<clinit>', 'x' * 31]
    plains = ['', 'a', 'ab', 'abc', '\x00', '\x00\x00\x00', 'caf\u00e9 \u4e2d\u6587',
              '\U0001F600', 'x' * 200, '\ud7ff\ue000']
    for seed in seeds:
        for plain in plains:
            ct = encrypt_units(utf16_units(plain), utf16_units(seed), MASK_A, MASK_B)
            back = from_utf16_units(
                _reference_decrypt_units(ct, utf16_units(seed), MASK_A, MASK_B))
            if back != plain:
                raise AssertionError(f'round trip failed: seed={seed!r} plain={plain!r}')


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------

def compile_fixture():
    javac = 'javac'
    try:
        proc = subprocess.run([javac, '-g', '-encoding', 'UTF-8', '-d', FIXTURES, JAVA_SRC],
                              capture_output=True, text=True)
    except FileNotFoundError:
        return False, 'javac not found on PATH; fixture .java written but not compiled'
    if proc.returncode != 0:
        return False, f'javac failed:\n{proc.stdout}\n{proc.stderr}'
    return True, proc.stdout + proc.stderr


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[1])
    ap.add_argument('--no-compile', action='store_true',
                    help='write the .java and expected.json but do not run javac')
    args = ap.parse_args(argv)

    check_masks()
    generator_selfcheck()
    print(f'PASS  generator self-check (cipher round-trips over '
          f'{4 * 10} seed/plaintext pairs, masks are distinct)')

    rows = build_sites()
    os.makedirs(FIXTURES, exist_ok=True)

    src = build_java(rows)
    with open(JAVA_SRC, 'w', encoding='ascii') as f:
        f.write(src)
    print(f'WROTE {os.path.relpath(JAVA_SRC, HERE)}')

    expected = {
        'generator': 'tests/make_fixture.py',
        'note': ('Synthetic ground truth. Plaintexts were chosen first and the '
                 'ciphertexts derived from them with an independently written '
                 'inverse; corroborated by running the compiled fixture under a '
                 'real JVM (see tests/test_unseed.py).'),
        'package': PACKAGE,
        'outer_class': OUTER_INTERNAL,
        'nested_class': NESTED_INTERNAL,
        'main_class': f'{PACKAGE}.{OUTER}',
        'decryptor': {'owner': OUTER_INTERNAL, 'name': 'd',
                      'desc': '(Ljava/lang/String;)Ljava/lang/String;',
                      'seed_parts': SEED_PARTS,
                      'mask_a': MASK_A, 'mask_b': MASK_B, 'decoy': DECOY},
        'sites': [{'token': r['token'].lower(), 'class': r['class'],
                   'dotted': r['dotted'], 'method': r['method'],
                   'plain': r['plain'], 'seed': r['seed'],
                   'ct_units': utf16_units(r['ct'])}
                  for r in rows],
    }
    with open(EXPECTED, 'w', encoding='utf-8') as f:
        json.dump(expected, f, indent=1, ensure_ascii=False)
        f.write('\n')
    print(f'WROTE {os.path.relpath(EXPECTED, HERE)}')

    if not args.no_compile:
        ok, msg = compile_fixture()
        if not ok:
            print(f'WARN  {msg}', file=sys.stderr)
            return 1
        print(f'PASS  javac compiled the fixture into {os.path.relpath(FIXTURES, HERE)}'
              + (f' ({msg.strip()})' if msg.strip() else ''))
    return 0


if __name__ == '__main__':
    sys.exit(main())
