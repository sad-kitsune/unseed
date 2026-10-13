#!/usr/bin/env python3
"""
test_unseed.py - test suite for unseed.py.

Run with:
    python3 tests/test_unseed.py           # or: python3 -m unittest discover -s tests

Everything here is self-contained. The fixture in tests/fixtures/ is synthetic
Java written from the documented algorithm (see tests/make_fixture.py); no
third-party artifact is needed, and no test reaches outside this repository.

Tests that need `java` or `javap` skip with an explicit reason when the JDK is
absent. Pass UNSEED_REQUIRE_JDK=1 to turn those skips into failures instead -
useful in CI, where a silent skip would otherwise look like a green run.
"""

from __future__ import annotations

import argparse
import ast
import contextlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import unseed                                            # noqa: E402

FIXTURES = os.path.join(HERE, 'fixtures')
REQUIRE_JDK = os.environ.get('UNSEED_REQUIRE_JDK') == '1'

HAVE_JAVAP = shutil.which('javap') is not None
HAVE_JAVA = shutil.which('java') is not None
HAVE_JAVAC = shutil.which('javac') is not None


def jdk_required(feature):
    """skipUnless that honours UNSEED_REQUIRE_JDK by failing instead of skipping."""
    have = {'java': HAVE_JAVA, 'javap': HAVE_JAVAP, 'javac': HAVE_JAVAC}[feature]
    if have:
        return lambda fn: fn

    def deco(fn):
        def wrapper(self, *a, **kw):
            if REQUIRE_JDK:
                self.fail(f'{fn.__name__} requires `{feature}` and '
                          f'UNSEED_REQUIRE_JDK=1 is set, but it is not on PATH')
            self.skipTest(f'`{feature}` not on PATH')
        wrapper.__name__ = fn.__name__
        wrapper.__doc__ = fn.__doc__
        return wrapper
    return deco


EXPECTED = None
CFS = None
SRC = None


def setUpModule():
    global EXPECTED, CFS, SRC
    EXPECTED, CFS, SRC = unseed.load_fixture()


def fixture_decryptor():
    tab, failures, stats = unseed.find_decryptors(CFS)
    return tab, failures, stats


# ==========================================================================
# 1. the modified UTF-8 codec
# ==========================================================================

class TestModifiedUtf8(unittest.TestCase):
    """CONSTANT_Utf8 is *modified* UTF-8, and Python's codec gets it wrong."""

    def test_round_trips(self):
        cases = ['', 'a', 'hello world', '/unseed/fixture/SeedFixture',
                 'NUL:\x00 here', '\x00\x00\x00',
                 '\u00e9\u4e2d\ud7ff', '\u007f\u0080\u07ff\u0800\uffff',
                 'supplementary \U0001F600 end', '\U0001F600\U0001F4A9']
        for s in cases:
            with self.subTest(s=s):
                raw = unseed.enc_modified_utf8(s)
                self.assertNotIn(b'\x00', raw,
                                 'a raw 0x00 byte is illegal in CONSTANT_Utf8')
                self.assertEqual(unseed.dec_modified_utf8(raw), s)

    def test_nul_is_encoded_as_c0_80(self):
        """The defining difference from standard UTF-8."""
        self.assertEqual(unseed.enc_modified_utf8('\x00'), b'\xc0\x80')
        self.assertEqual(unseed.dec_modified_utf8(b'\xc0\x80'), '\x00')
        # and Python's own codec disagrees, which is the bug this avoids
        self.assertEqual('\x00'.encode('utf-8'), b'\x00')
        self.assertNotEqual(b'\xc0\x80'.decode('utf-8', 'replace'), '\x00')

    def test_supplementary_is_cesu8_surrogate_pair(self):
        """U+1F600 goes out as two 3-byte surrogate halves (6 bytes), not 4."""
        raw = unseed.enc_modified_utf8('\U0001F600')
        self.assertEqual(len(raw), 6)
        self.assertEqual(raw, b'\xed\xa0\xbd\xed\xb8\x80')
        self.assertEqual(unseed.dec_modified_utf8(raw), '\U0001F600')
        # standard UTF-8 would be 4 bytes and this tool must not emit that
        self.assertEqual(len('\U0001F600'.encode('utf-8')), 4)

    def test_python_replace_silently_corrupts(self):
        """Demonstrates the failure mode the codec exists to prevent."""
        raw = unseed.enc_modified_utf8('a\x00b\U0001F600c')
        lossy = raw.decode('utf-8', 'replace')
        self.assertIn('\ufffd', lossy,
                      'expected the naive decode to produce U+FFFD')
        self.assertNotEqual(lossy, 'a\x00b\U0001F600c')
        self.assertEqual(unseed.dec_modified_utf8(raw), 'a\x00b\U0001F600c')

    def test_malformed_input_raises_never_guesses(self):
        bad = {
            'raw NUL byte': b'\x00',
            'truncated 2-byte': b'\xc0',
            'truncated 3-byte': b'\xe0\x80',
            'bad continuation': b'\xc0\x41',
            '4-byte form': b'\xf0\x9f\x98\x80',
            'lone high surrogate': b'\xed\xa0\xbd',
            'lone low surrogate': b'\xed\xb8\x80',
        }
        for label, raw in bad.items():
            with self.subTest(case=label):
                with self.assertRaises(unseed.UnseedError):
                    unseed.dec_modified_utf8(raw)

    def test_utf16_unit_helpers(self):
        for s in ['', 'ascii', 'caf\u00e9', '\U0001F600', 'a\U0001F600b']:
            with self.subTest(s=s):
                units = unseed.to_utf16_units(s)
                self.assertEqual(unseed.from_utf16_units(units), s)
                self.assertEqual(len(units), len(s.encode('utf-16-be')) // 2)
        # a supplementary char is TWO code units, which is what charAt indexes
        self.assertEqual(len(unseed.to_utf16_units('\U0001F600')), 2)
        with self.assertRaises(unseed.UnseedError):
            unseed.from_utf16_units([0xD800])          # lone high surrogate
        with self.assertRaises(unseed.UnseedError):
            unseed.from_utf16_units([0xDC00])          # lone low surrogate


# ==========================================================================
# 2. the instruction decoder
# ==========================================================================

class TestDecoder(unittest.TestCase):

    def test_unknown_opcode_raises(self):
        """0xCB is unassigned in the JVM spec; guessing here is the failure mode
        that silently yields wrong constants."""
        with self.assertRaises(unseed.UnseedError) as ctx:
            unseed.decode(b'\xcb')
        self.assertIn('unknown opcode', str(ctx.exception))
        self.assertIn('0xcb', str(ctx.exception))

    def test_instruction_past_end_of_code_raises(self):
        with self.assertRaises(unseed.UnseedError):
            unseed.decode(b'\x13')                     # ldc_w with no operand

    def test_decodes_a_known_sequence(self):
        # nop; iconst_1; istore_0; return
        insns = unseed.decode(b'\x00\x04\x3b\xb1')
        self.assertEqual([i.name for i in insns],
                         ['nop', 'iconst_1', 'istore_0', 'return'])
        self.assertEqual([i.off for i in insns], [0, 1, 2, 3])

    @jdk_required('javap')
    def test_decoder_agrees_with_javap(self):
        """The JDK's own disassembler as an independent oracle: every offset and
        mnemonic this tool decodes must match javap's for the same member."""
        sample = [(cls, CFS[cls]) for cls in sorted(CFS)]
        with tempfile.TemporaryDirectory(prefix='unseed-javap-') as wd:
            checked, mismatches, problems = unseed.check_decoder_vs_javap(
                CFS, sample, wd)
        self.assertGreater(checked, 100,
                           f'only cross-checked {checked} instructions - too few '
                           f'to be meaningful')
        self.assertEqual(mismatches, 0,
                         f'{mismatches} decoder/javap mismatch(es): {problems[:5]}')
        self.assertEqual(problems, [])

    @jdk_required('javap')
    def test_javap_block_splitting_handles_clinit_and_overloads(self):
        """`public static {};` must map to <clinit>, and overloaded members must
        not have their bcis flattened into one list."""
        text = ('public class X {\n'
                '  static {};\n'
                '    Code:\n'
                '       0: nop\n'
                '       1: return\n'
                '  void f();\n'
                '    Code:\n'
                '       0: iconst_0\n'
                '       1: ireturn\n'
                '  void f(int);\n'
                '    Code:\n'
                '       0: iconst_1\n'
                '       1: ireturn\n'
                '}\n')
        blocks = unseed.javap_member_blocks(text)
        self.assertIn('<clinit>', blocks)
        self.assertEqual(len(blocks['f']), 2, 'overloads must stay separate')
        self.assertEqual(blocks['f'][0][0][1], 'iconst_0')
        self.assertEqual(blocks['f'][1][0][1], 'iconst_1')


# ==========================================================================
# 3. decryptor extraction over the bundled fixture
# ==========================================================================

class TestExtraction(unittest.TestCase):

    def test_decryptor_is_found_and_extracted(self):
        tab, failures, stats = fixture_decryptor()
        d = EXPECTED['decryptor']
        self.assertEqual(failures, [],
                         'a recognised shape that failed to extract is a failure, '
                         'not a skip')
        self.assertEqual(stats['frame_shaped'], 1)
        self.assertEqual(stats['extracted'], 1)
        self.assertIn((d['owner'], d['name'], d['desc']), tab)

    def test_masks_and_seed_parts_match_expected(self):
        """The core anti-guessing property. The fixture computes THREE constants
        in its prologue and reads only two; recovering them positionally, or
        picking up the decoy, breaks this."""
        tab, _failures, _stats = fixture_decryptor()
        d = EXPECTED['decryptor']
        dec = tab[(d['owner'], d['name'], d['desc'])]
        self.assertEqual(dec.seed_parts, d['seed_parts'])
        self.assertEqual(dec.mask_a, d['mask_a'])
        self.assertEqual(dec.mask_b, d['mask_b'])
        self.assertNotEqual(dec.mask_a, d['decoy'],
                            'the unused decoy constant was selected as a mask')
        self.assertNotEqual(dec.mask_b, d['decoy'],
                            'the unused decoy constant was selected as a mask')

    def test_a_non_decryptor_class_yields_an_honest_zero(self):
        """Feeding the extractor a class with no such scheme must report zero
        cleanly - not crash, and not invent a decryptor."""
        nested = EXPECTED['nested_class'] + '.class'
        tab, failures, stats = unseed.find_decryptors({nested: CFS[nested]})
        self.assertEqual(tab, {})
        self.assertEqual(failures, [])
        self.assertEqual(stats['extracted'], 0)

    def test_shape_filter_is_counted_separately_from_frame_check(self):
        """A wrong frame predicate must not masquerade as "this input has no
        decryptors": candidates and frame-shaped are distinct counters."""
        _tab, _failures, stats = fixture_decryptor()
        self.assertEqual(stats['candidates'], 1)
        self.assertEqual(stats['frame_shaped'], 1)
        self.assertEqual(stats['decode_failed'], 0)


# ==========================================================================
# 4. string recovery
# ==========================================================================

class TestStringRecovery(unittest.TestCase):

    def setUp(self):
        self.tab, _failures, _stats = fixture_decryptor()
        self.res, self.unsup = unseed.scan_all(CFS, self.tab)

    def test_every_call_site_recovers_its_expected_plaintext(self):
        got = sorted((c, h['method'], h['plain'])
                     for c, v in self.res.items() for h in v)
        want = sorted((s['class'], s['method'], s['plain'])
                      for s in EXPECTED['sites'])
        self.assertEqual(got, want)

    def test_no_unresolvable_call_sites(self):
        self.assertEqual(self.unsup, {},
                         'the fixture is entirely statically resolvable; an '
                         'unsupported site means the scanner lost one')

    def test_ciphertexts_match_expected_code_units(self):
        """Checks the constant pool really holds the ciphertexts the generator
        wrote, i.e. the modified UTF-8 path is exercised, not bypassed.

        Compared as a multiset of (class, method, ct): two sites share the
        emitMixed method, so a dict keyed on (class, method) would collapse them.
        """
        got = sorted((cls, h['method'], tuple(unseed.to_utf16_units(h['ct'])))
                     for cls, hits in self.res.items() for h in hits)
        want = sorted((s['class'], s['method'], tuple(s['ct_units']))
                      for s in EXPECTED['sites'])
        self.assertEqual(got, want)

    def test_seed_is_the_callers_identity(self):
        for cls, hits in self.res.items():
            dotted = cls.replace('/', '.')
            for h in hits:
                self.assertEqual(h['seed'], dotted + h['method'])

    def test_nul_and_supplementary_survive_the_full_path(self):
        """End-to-end through CP decode -> UTF-16 decrypt -> plaintext."""
        plains = {h['plain'] for v in self.res.values() for h in v}
        self.assertIn('has\x00NUL inside', plains)
        self.assertIn('emoji \U0001F600 end', plains)
        self.assertIn('caf\u00e9 \u4e2d\u6587 \x7f\x80\u07ff', plains)
        self.assertIn('/unseed/fixture/SeedFixture', plains)
        self.assertIn('nested $ class name', plains)

    def test_caller_seeding_is_real(self):
        """The property that makes this scheme interesting: the same ciphertext
        under a different caller's seed must NOT yield the same plaintext. If
        this ever passes trivially, the tool is doing a global decrypt and the
        whole framing is wrong."""
        sites = {(s['class'], s['method']): s for s in EXPECTED['sites']}
        d = EXPECTED['decryptor']
        clinit = sites[(EXPECTED['outer_class'], '<clinit>')]
        other = sites[(EXPECTED['outer_class'], 'fromMethod')]
        ct = unseed.from_utf16_units(clinit['ct_units'])
        wrong_seed = other['seed']
        wrong = unseed.decrypt(ct, wrong_seed, d['mask_a'], d['mask_b'])
        self.assertNotEqual(wrong, clinit['plain'])
        right = unseed.decrypt(ct, clinit['seed'], d['mask_a'], d['mask_b'])
        self.assertEqual(right, clinit['plain'])

    def test_decrypt_matches_expected_on_raw_units(self):
        d = EXPECTED['decryptor']
        for s in EXPECTED['sites']:
            with self.subTest(site=s['token']):
                out = unseed.decrypt_units(s['ct_units'],
                                           unseed.to_utf16_units(s['seed']),
                                           d['mask_a'], d['mask_b'])
                self.assertEqual(out, unseed.to_utf16_units(s['plain']))

    def test_plaintext_consistency_check_has_power(self):
        """The fixture must contain at least one group - one (class, method)
        pair, since the seed is the caller's identity - holding BOTH a readable
        literal and a low-printable one. That mix is the only thing that can
        distinguish "this literal really is binary data" from "we recovered the
        wrong mask", so a fixture without it would let verify pass vacuously."""
        pc = unseed.check_plaintext_consistency(self.res)
        self.assertGreater(pc['mixed'], 0,
                           'no mixed group: the plaintext-consistency check has '
                           'no power on this fixture')
        self.assertGreater(pc['low_proven'], 0,
                           'no low-printable literal was proven to be data')
        # The `main` site is a low-printable singleton group, so it is
        # legitimately unverified - that is the check being honest, not broken.
        # What must hold is that the emitMixed blob IS proven by its readable
        # sibling sharing one seed+masks.
        self.assertEqual(pc['low_unverified'], pc['low_total'] - pc['low_proven'])
        self.assertEqual(pc['low_proven'], 1,
                         'expected exactly the emitMixed blob to be proven')

    def test_shared_method_sites_share_one_seed(self):
        """Both emitMixed sites must land in the same group; if they were
        attributed to different methods the seed would differ and the plaintexts
        would come out as garbage."""
        sites = [h for h in self.res.get(EXPECTED['outer_class'], [])
                 if h['method'] == 'emitMixed']
        self.assertEqual(len(sites), 2, f'expected 2 sites in emitMixed, got {sites}')
        self.assertEqual(len({h['seed'] for h in sites}), 1)
        plains = {h['plain'] for h in sites}
        self.assertIn('readable text in a shared method', plains)
        self.assertIn('\x01\x02\x03key\x04\x05\xff', plains)


# ==========================================================================
# 5. the JVM as an independent oracle
# ==========================================================================

class TestJvmOracle(unittest.TestCase):

    @jdk_required('java')
    def test_fixture_runs_and_matches_expected_json(self):
        """expected.json is corroborated by actually running the compiled Java,
        so the generator cannot be quietly self-consistent-but-wrong."""
        want = {s['token']: s['plain'] for s in EXPECTED['sites']}
        values, _err = unseed._jvm_oracle(FIXTURES, EXPECTED['main_class'])
        self.assertEqual(values, want)

    @jdk_required('java')
    def test_patched_classes_run_identically(self):
        """The strongest test of the length-preserving patcher: the JVM's own
        verifier must accept the rewritten StackMapTable / exception tables /
        line numbers, and behaviour must be unchanged."""
        tab, _failures, _stats = fixture_decryptor()
        res, unsup = unseed.scan_all(CFS, tab)
        self.assertEqual(unsup, {})
        baseline, _err = unseed._jvm_oracle(FIXTURES, EXPECTED['main_class'])
        with tempfile.TemporaryDirectory(prefix='unseed-patched-') as tmp:
            for entry, cf in CFS.items():
                data = SRC.read(entry)
                hits = res.get(cf.this, [])
                out, _spans, _ncp = unseed.patch_class(cf, data, hits)
                unseed.check_patch(data, out, tab, [h['plain'] for h in hits])
                dst = os.path.join(tmp, entry)
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                with open(dst, 'wb') as f:
                    f.write(out)
            after, _err = unseed._jvm_oracle(tmp, EXPECTED['main_class'])
        self.assertEqual(after, baseline,
                         'patching changed observable behaviour')

    def test_fixture_control_passes_end_to_end(self):
        """The same control the `selftest` subcommand runs."""
        s = unseed.fixture_control(run_jvm=HAVE_JAVA)
        self.assertEqual(s['sites_recovered'], s['sites_expected'])
        self.assertEqual(s['stats']['extracted'], s['stats']['frame_shaped'])
        self.assertEqual(s['stats']['extracted'], 1)
        if not HAVE_JAVA:
            if REQUIRE_JDK:
                self.fail('fixture_control skipped the JVM oracle and '
                          'UNSEED_REQUIRE_JDK=1 is set')
            self.assertIn('skipped', s['jvm'])
        else:
            self.assertIn('matches expected.json', s['jvm'])
            self.assertIn('re-ran identically', s['jvm'])


# ==========================================================================
# 6. the length-preserving patcher
# ==========================================================================

class TestPatcher(unittest.TestCase):

    def setUp(self):
        self.tab, _failures, _stats = fixture_decryptor()
        self.res, _unsup = unseed.scan_all(CFS, self.tab)

    def test_patch_preserves_structure_and_drops_call_sites(self):
        """check_patch asserts: identity, member list and every Code length
        unchanged; zero surviving decryptor calls; every plaintext present."""
        for entry, cf in CFS.items():
            with self.subTest(entry=entry):
                data = SRC.read(entry)
                hits = self.res.get(cf.this, [])
                out, nspans, _ncp = unseed.patch_class(cf, data, hits)
                self.assertEqual(nspans, len(hits))
                self.assertTrue(unseed.check_patch(data, out, self.tab,
                                                   [h['plain'] for h in hits]))

    def test_code_attribute_lengths_are_unchanged(self):
        """The invariant that makes recomputation unnecessary."""
        for entry, cf in CFS.items():
            with self.subTest(entry=entry):
                data = SRC.read(entry)
                hits = self.res.get(cf.this, [])
                out, _s, _n = unseed.patch_class(cf, data, hits)
                orig = unseed.load_class('orig', data)
                new = unseed.load_class('new', out)
                self.assertEqual(len(new.methods), len(orig.methods))
                for mo, mn in zip(orig.methods, new.methods):
                    co, _ = orig.code_of(mo)
                    cn, _ = new.code_of(mn)
                    self.assertEqual((co is None), (cn is None), mo['name'])
                    if co is not None:
                        self.assertEqual(len(co), len(cn),
                                         f'{mo["name"]}: Code length changed, so '
                                         f'branch offsets and StackMapTable '
                                         f'entries would need recomputing')

    def test_patched_span_is_ldc_w_plus_nop_padding(self):
        for entry, cf in CFS.items():
            data = SRC.read(entry)
            hits = self.res.get(cf.this, [])
            if not hits:
                continue
            out, _s, _n = unseed.patch_class(cf, data, hits)
            new = unseed.load_class('new', out)
            for h in hits:
                with self.subTest(entry=entry, method=h['method'], bci=h['bci']):
                    m = next(mm for mm in new.methods if mm['name'] == h['method'])
                    code, _meta = new.code_of(m)
                    start = h['bci']
                    span_len = h['span'][1] - h['span'][0]
                    self.assertEqual(code[start], 0x13, 'expected ldc_w')
                    self.assertTrue(all(b == 0x00 for b in
                                        code[start + 3:start + span_len]),
                                    'expected nop padding after ldc_w')

    def test_constant_pool_grows_only_by_appending(self):
        for entry, cf in CFS.items():
            data = SRC.read(entry)
            hits = self.res.get(cf.this, [])
            out, _s, ncp = unseed.patch_class(cf, data, hits)
            orig = unseed.load_class('orig', data)
            new = unseed.load_class('new', out)
            with self.subTest(entry=entry):
                self.assertEqual(new.cp_count, orig.cp_count + ncp)
                for i in range(1, orig.cp_count):
                    self.assertEqual(new.cp[i], orig.cp[i],
                                     f'CP#{i} changed - appended entries must '
                                     f'not shift existing indices')

    def test_missing_plaintext_in_pool_is_detected(self):
        """check_patch must fail loudly if an expected plaintext is absent."""
        entry = EXPECTED['outer_class'] + '.class'
        cf = CFS[entry]
        data = SRC.read(entry)
        hits = self.res.get(cf.this, [])
        out, _s, _n = unseed.patch_class(cf, data, hits)
        with self.assertRaises(unseed.UnseedError):
            unseed.check_patch(data, out, self.tab,
                               [h['plain'] for h in hits] + ['not-in-the-pool'])

    def test_overlapping_spans_are_refused(self):
        entry = EXPECTED['outer_class'] + '.class'
        cf = CFS[entry]
        data = SRC.read(entry)
        hits = self.res.get(cf.this, [])
        if len(hits) < 2:
            self.skipTest('need two call sites in one class')
        dup = [hits[0], dict(hits[0])]                  # same span twice
        with self.assertRaises(unseed.UnseedError):
            unseed.patch_class(cf, data, dup)


# ==========================================================================
# 7. CLI integration
# ==========================================================================

class TestCli(unittest.TestCase):

    def run_cli(self, argv):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
            rc = unseed.main(argv)
        return rc, buf.getvalue()

    def test_selftest_subcommand(self):
        rc, out = self.run_cli(['selftest'] + ([] if HAVE_JAVA else ['--no-jvm']))
        self.assertEqual(rc, 0, out)
        self.assertIn('PASS  codec round-trips', out)
        self.assertIn('PASS  decryptor extraction', out)
        self.assertIn('PASS  string recovery', out)
        self.assertIn('PASS  patch', out)
        self.assertNotIn('FAIL', out)

    def test_selftest_require_jvm_flag(self):
        rc, out = self.run_cli(['selftest', '--require-jvm'])
        if HAVE_JAVA:
            self.assertEqual(rc, 0, out)
            self.assertIn('PASS  JVM oracle', out)
        else:
            self.assertEqual(rc, 1, out)
            self.assertIn('FAIL  JVM oracle', out)

    def test_scan_subcommand(self):
        rc, out = self.run_cli(['scan', FIXTURES])
        self.assertEqual(rc, 0, out)
        self.assertIn('string decryptors       : 1', out)
        self.assertIn(f'obfuscated literals     : {len(EXPECTED["sites"])}', out)

    def test_strings_subcommand_with_json_and_report(self):
        with tempfile.TemporaryDirectory(prefix='unseed-cli-') as tmp:
            j = os.path.join(tmp, 'strings.json')
            r = os.path.join(tmp, 'report.txt')
            rc, out = self.run_cli(['strings', FIXTURES, '--json', j, '--report', r])
            self.assertEqual(rc, 0, out)
            self.assertTrue(os.path.isfile(j) and os.path.isfile(r), out)
            with open(j, encoding='utf-8') as f:
                data = json.load(f)
            plains = sorted(h['plain'] for v in data.values() for h in v)
            self.assertEqual(plains, sorted(s['plain'] for s in EXPECTED['sites']))
            with open(r, encoding='utf-8') as f:
                head = f.read(200)
            self.assertIn('unseed.py', head)
            self.assertNotIn('deobf', head)

    def test_strings_grep_filter(self):
        rc, out = self.run_cli(['strings', FIXTURES, '--grep', 'hello'])
        self.assertEqual(rc, 0, out)
        self.assertIn("'hello world'", out)

    def test_indy_subcommand(self):
        rc, out = self.run_cli(['indy', FIXTURES])
        self.assertEqual(rc, 0, out)
        self.assertIn('invokedynamic sites', out)

    def test_patch_subcommand(self):
        with tempfile.TemporaryDirectory(prefix='unseed-cli-') as tmp:
            out_dir = os.path.join(tmp, 'patched')
            j = os.path.join(tmp, 'patch.json')
            rc, out = self.run_cli(['patch', FIXTURES, '--out', out_dir,
                                    '--json', j, '--copy-all'])
            self.assertEqual(rc, 0, out)
            # cmd_patch writes the rewritten tree under <out>/classes/
            classes = os.path.join(out_dir, 'classes')
            self.assertTrue(os.path.isdir(classes), out)
            produced = []
            for root, _d, files in os.walk(classes):
                produced += [os.path.relpath(os.path.join(root, f), classes)
                             for f in files if f.endswith('.class')]
            self.assertEqual(sorted(produced), sorted(CFS.keys()))
            self.assertTrue(os.path.isfile(j), out)

    def test_verify_subcommand_with_known_string(self):
        rc, out = self.run_cli(['verify', FIXTURES,
                                '--ground-truth', 'hello world']
                               + ([] if HAVE_JAVA else ['--no-jvm']))
        self.assertIn('bundled-fixture control', out)
        self.assertIn("known-string control 'hello world'", out)
        self.assertNotIn('FAIL', out)
        self.assertEqual(rc, 0, out)

    def test_verify_without_ground_truth_reports_skip_not_pass(self):
        """No baked-in default: an omitted control must be reported as skipped,
        never silently counted as a pass."""
        rc, out = self.run_cli(['verify', FIXTURES]
                               + ([] if HAVE_JAVA else ['--no-jvm']))
        self.assertIn('SKIP  known-string control', out)
        self.assertNotIn('PASS  known-string control', out)
        self.assertIn('bundled-fixture control', out)

    def test_verify_fails_on_a_wrong_known_string(self):
        rc, out = self.run_cli(['verify', FIXTURES,
                                '--ground-truth', 'definitely not present']
                               + ([] if HAVE_JAVA else ['--no-jvm']))
        self.assertNotEqual(rc, 0, out)
        self.assertIn('FAIL  known-string control', out)


# ==========================================================================
# 8. honest behaviour on input that does not use this scheme
# ==========================================================================

class TestUnrelatedInput(unittest.TestCase):

    @jdk_required('javac')
    def test_plain_compiled_class_reports_zero_cleanly(self):
        """A stock class must produce a clean zero, not a crash and not an
        invented decryptor. This is the "doesn't work on my jar" case, and the
        correct answer is a legible zero."""
        with tempfile.TemporaryDirectory(prefix='unseed-plain-') as tmp:
            srcdir = os.path.join(tmp, 'src')
            outdir = os.path.join(tmp, 'out')
            os.makedirs(srcdir)
            os.makedirs(outdir)
            with open(os.path.join(srcdir, 'Plain.java'), 'w') as f:
                f.write('public class Plain {\n'
                        '    public static String hello() { return "hello"; }\n'
                        '    public static void main(String[] a) {\n'
                        '        System.out.println(hello());\n'
                        '    }\n'
                        '}\n')
            r = subprocess.run(['javac', '-g', '-d', outdir,
                                os.path.join(srcdir, 'Plain.java')],
                               capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stderr)

            cfs, fails = unseed.load_all(unseed.ClassSource(outdir), quiet=True)
            self.assertEqual(fails, [])
            tab, failures, stats = unseed.find_decryptors(cfs)
            self.assertEqual(tab, {}, 'invented a decryptor on a plain class')
            self.assertEqual(failures, [])
            self.assertEqual(stats['candidates'], 0)
            self.assertEqual(stats['frame_shaped'], 0)
            res, unsup = unseed.scan_all(cfs, tab)
            self.assertEqual(res, {})
            self.assertEqual(unsup, {})

            # and the CLI must say so legibly rather than claiming success
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
                rc = unseed.main(['verify', outdir]
                                 + ([] if HAVE_JAVA else ['--no-jvm']))
            out = buf.getvalue()
            self.assertEqual(rc, 2, out)
            self.assertIn('no frame-shaped decryptor', out)
            self.assertIn('not a general deobfuscator', out)


# ==========================================================================
# 8b. regressions: latent bugs that only malformed or unusual input exposes
# ==========================================================================

class _StubClass:
    """Just enough of ClassFile for Interp.step on instructions that touch no pool."""
    dotted = 'Stub'

    def __init__(self, consts=None):
        self._consts = consts or {}

    def const_value(self, i):
        return self._consts[i]


def _insn(name, *operands):
    op = next(code for code, (n, _f) in unseed.OPS.items() if n == name)
    return unseed.Insn(0, op, name, unseed.OPS[op][1], operands, 1)


class TestRegressions(unittest.TestCase):

    def test_float_constant_loads_as_a_float(self):
        """const_value used to pack a float with '>i' and die with a raw
        struct.error, so any `ldc <float>` in an analysed method failed to
        extract (hsqldb's HashMap.<init> loads a float load factor)."""
        cf = unseed.ClassFile.__new__(unseed.ClassFile)
        cf.name, cf.cp_count, cf.cp = 'synthetic', 2, [None, ('float', 0.75, None)]
        self.assertEqual(cf.const_value(1), ('float', 0.75))

    def test_ldc_of_a_float_pushes_a_float(self):
        it = unseed.Interp(_StubClass({1: ('float', 0.75)}), 0)
        it.step(_insn('ldc', 1))
        self.assertEqual(it.stack, [('float', 0.75)])

    def test_narrowing_conversions_truncate_concrete_ints(self):
        """i2b/i2s used to pass a concrete int through unchanged, so a mask built
        with a narrowing cast would have been silently wrong."""
        for name, given, want in (('i2b', 200, -56), ('i2b', -129, 127),
                                  ('i2s', 40000, -25536), ('i2c', -1, 0xFFFF)):
            with self.subTest(op=name, value=given):
                it = unseed.Interp(_StubClass(), 0)
                it.push(('int', given))
                it.step(_insn(name))
                self.assertEqual(it.stack, [('int', want)])

    def test_stack_underflow_is_an_unseed_error(self):
        for name in ('pop2', 'dup2', 'dup2_x2', 'swap'):
            with self.subTest(op=name):
                with self.assertRaises(unseed.UnseedError):
                    unseed.Interp(_StubClass(), 0).step(_insn(name))

    def test_stray_continuation_byte_is_rejected(self):
        """0x80-0xBF cannot start a character. It used to be read as a 2-byte lead,
        so b'\\x80\\x80' silently decoded to U+0000."""
        with self.assertRaises(unseed.UnseedError):
            unseed.dec_modified_utf8(b'\x80\x80')

    def test_truncated_classfile_raises_unseed_error(self):
        """Not a raw struct.error / IndexError: load_all reports UnseedError cleanly."""
        for blob in (b'\xca\xfe\xba\xbe\x00\x00\x00\x34\x00\x10', b'\xca\xfe\xba\xbe'):
            with self.subTest(length=len(blob)):
                with self.assertRaises(unseed.UnseedError):
                    unseed.load_class('truncated', blob)

    def run_cli(self, argv):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
            rc = unseed.main(argv)
        return rc, buf.getvalue()

    def test_parse_failure_warning_is_printed_once_and_quiet_silences_it(self):
        with tempfile.TemporaryDirectory(prefix='unseed-badclass-') as tmp:
            with open(os.path.join(tmp, 'Bad.class'), 'wb') as f:
                f.write(b'\xca\xfe\xba\xbe\x00\x00\x00\x34\x00\x10')
            rc, out = self.run_cli(['scan', tmp])
            self.assertEqual(rc, 0, out)
            self.assertEqual(out.count('failed to parse'), 1, out)
            rc, out = self.run_cli(['scan', tmp, '--quiet'])
            self.assertEqual(rc, 0, out)
            self.assertNotIn('failed to parse', out)

    @jdk_required('javap')
    def test_javap_check_larger_than_the_class_count_does_not_crash(self):
        """`--javap-check 50` (the README's own example) used to raise ValueError
        from random.sample on any input with fewer than 50 non-decryptor classes."""
        rc, out = self.run_cli(['verify', FIXTURES, '--javap-check', '50', '--no-jvm'])
        self.assertEqual(rc, 0, out)
        self.assertIn('PASS  instruction decoder vs javap', out)


# ==========================================================================
# 9. no leaked provenance
# ==========================================================================

class TestProvenance(unittest.TestCase):
    """Guards the property this cleanup established: the shipped tool embeds no
    ciphertext, plaintext, class name or workspace path taken from any
    third-party artifact.

    These checks are deliberately STRUCTURAL rather than a blocklist of specific
    vendor strings. A blocklist has to name the thing it forbids, which puts the
    name back into the public repository, and it only ever catches the one
    artifact someone remembered to list.
    """

    # Path-ish references in prose: a doc filename, or a dir-qualified source
    # file. Any of these that does not resolve inside this repository is a
    # dangling pointer to a private workspace, which is unreadable for anyone
    # else and leaks internal layout.
    DOC_REF = re.compile(r'[A-Za-z0-9_.\-/]*[A-Za-z0-9_\-]\.md\b')
    SRC_REF = re.compile(r'[A-Za-z0-9_.\-]+/[A-Za-z0-9_.\-/]*\.(?:py|java|json)\b')

    SHIPPED = ('unseed.py', 'README.md', 'LICENSE',
               'tests/make_fixture.py', 'tests/fixtures/SeedFixture.java',
               'tests/fixtures/expected.json')

    def _read(self, rel):
        path = os.path.join(ROOT, rel)
        if not os.path.isfile(path):
            self.skipTest(f'{rel} not present')
        with open(path, encoding='utf-8') as f:
            return f.read()

    def test_every_referenced_path_resolves_inside_the_repository(self):
        """Generic replacement for a blocklist of forbidden names.

        A blocklist has to spell out the private paths it forbids, which puts
        them back into the public repository. This instead asserts the property
        that matters: every doc/source path mentioned in shipped prose must
        exist here, so a public reader can actually follow it.
        """
        dangling = []
        for rel in self.SHIPPED:
            if not os.path.isfile(os.path.join(ROOT, rel)):
                continue
            text = self._read(rel)
            refs = set(self.DOC_REF.findall(text)) | set(self.SRC_REF.findall(text))
            for ref in sorted(refs):
                if ref.startswith(('http://', 'https://')):
                    continue
                if not os.path.exists(os.path.join(ROOT, ref)):
                    dangling.append(f'{rel}: {ref}')
        self.assertEqual(
            dangling, [],
            'shipped files reference paths that do not exist in this repository '
            '(dangling pointers to a private workspace):\n  ' + '\n  '.join(dangling))

    def test_no_hardcoded_ciphertext_control_in_the_tool(self):
        """The regression that actually matters: no call to decrypt()/
        decrypt_units() in the tool passes a string literal.

        A hardcoded (ciphertext, plaintext, class-name) triple is a recorded
        answer tied to one specific artifact. It proves nothing to anyone who
        does not have that artifact, it cannot be audited, and it reproduces
        bytes of third-party origin in this repository. Every control must come
        from tests/fixtures/, which is generated and checked in.
        """
        src = os.path.join(ROOT, 'unseed.py')
        with open(src, encoding='utf-8') as f:
            tree = ast.parse(f.read(), filename=src)
        offenders = []
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            fn = node.func
            name = fn.id if isinstance(fn, ast.Name) else getattr(fn, 'attr', None)
            if name not in ('decrypt', 'decrypt_units'):
                continue
            for a in node.args:
                if isinstance(a, ast.Constant) and isinstance(a.value, str):
                    offenders.append((node.lineno, name, a.value[:40]))
        self.assertEqual(
            offenders, [],
            'the tool embeds a literal ciphertext/plaintext as a control; move it '
            f'into tests/fixtures/ instead: {offenders}')

    def test_ground_truth_control_has_no_embedded_default(self):
        """--ground-truth must default to None. A baked-in default string is how
        an artifact-specific control sneaks back in: it silently makes `verify`
        assert something about one particular jar and fail on every other."""
        ap = unseed.build_parser()
        subs = [a for a in ap._actions if isinstance(a, argparse._SubParsersAction)]
        self.assertEqual(len(subs), 1, 'expected exactly one subparser action')
        vp = subs[0].choices['verify']
        gt = [a for a in vp._actions if a.dest == 'ground_truth']
        self.assertEqual(len(gt), 1, 'verify has no --ground-truth option')
        self.assertIsNone(gt[0].default,
                          '--ground-truth must not carry a default value')

    def test_selftest_control_comes_from_the_bundled_fixture(self):
        """The positive control must be read from tests/fixtures/, never inlined."""
        self.assertEqual(unseed.FIXTURE_DIR,
                         os.path.join(unseed.TOOL_DIR, 'tests', 'fixtures'))
        self.assertTrue(os.path.isfile(unseed.FIXTURE_EXPECTED),
                        'expected.json is missing, so the control cannot run')
        s = unseed.fixture_control(run_jvm=False)
        self.assertGreater(s['sites_recovered'], 0)

    def test_fixture_is_generated_and_reproducible(self):
        """Regenerating the fixture must reproduce the checked-in source exactly,
        so a reviewer can audit what the .class files came from."""
        with open(os.path.join(FIXTURES, 'SeedFixture.java'), encoding='ascii') as f:
            checked_in = f.read()
        sys.path.insert(0, HERE)
        import make_fixture
        rows = make_fixture.build_sites()
        self.assertEqual(make_fixture.build_java(rows), checked_in)


if __name__ == '__main__':
    unittest.main(verbosity=2)
