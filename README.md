# unseed

**English** | [Русский](README.ru.md)

unseed recovers strings from Java classes whose string encryption is keyed on the
caller's class and method name, and can patch the plaintext back into the classes.
It's a single Python file with no dependencies outside the standard library.

## The scheme

Some obfuscators key string encryption on whoever calls the decryptor. The
decryptor finds its caller in a stack trace and uses the class and method names
as the seed:

```java
static String d(String s) {
    StackTraceElement frame = new RuntimeException().getStackTrace()[1];   // caller
    String seed = new StringBuffer(frame.getClassName())
                      .append(frame.getMethodName()).toString();
    ...
    out[i] = (char) (maskA ^ (s.charAt(i) ^ seed.charAt(n)));
}
```

Decrypt the same ciphertext from a different caller and you get garbage, so
calling the decryptor on every constant doesn't work. The caller is known
statically, though: it's the class the call sits in (`this_class`) plus the
method's real name.

unseed runs the decryptor's straight-line prologue on a small stack machine,
walks the loop body to see which constants get XORed against a character, and
works out the seed order from how the `StringBuffer`/`StringBuilder` is built.
It doesn't need a JVM or a decompiler.

## Scope

unseed handles this one scheme and nothing else. It isn't a general
deobfuscator: it won't undo Zelix, Stringer, Allatori or ProGuard, rename
classes, untangle control flow, or strip anti-tamper checks. For that, try
[java-deobfuscator](https://github.com/java-deobfuscator/deobfuscator) or
[threadtear](https://github.com/GraxCode/threadtear).

Run `scan` first. If it reports `0 frame-shaped`, your jar doesn't use this
scheme and unseed can't help.

## Usage

You need Python 3.9 or newer. A JDK is optional and only used for the `javap`
and JVM cross-checks. Input can be a `.jar`, a `.zip`, or a directory of
`.class` files.

```sh
python3 unseed.py selftest                       # runs the bundled fixture, no input needed
python3 unseed.py scan     target.jar            # does this jar use the scheme at all?
python3 unseed.py strings  target.jar --json out.json --report out.txt
python3 unseed.py patch    target.jar --out work/ --copy-all
python3 unseed.py verify   target.jar --javap-check 50 --ground-truth 'a string you know is in there'
python3 unseed.py indy     target.jar --worklist worklist.json
```

- `selftest` checks the codec and runs the bundled fixture.
- `scan` counts decryptors, encrypted literals and `invokedynamic` sites. If the
  jar uses a scheme unseed doesn't handle, it says so.
- `strings` decrypts every literal and records the class, method, bytecode
  index, seed and ciphertext for each one. `--grep` filters the output;
  `--json` and `--report` write it to files.
- `patch` writes `.class` files with the plaintext inlined, plus a SHA-256
  manifest of every file before and after. The patched classes behave the same
  and pass the JVM verifier. `--copy-all` also copies the untouched classes so
  the output tree is complete.
- `indy` sorts `invokedynamic` sites into resolved lambdas, Java bootstraps it
  can emulate, native-gated sites, and unknown owners. It writes a worklist of
  the sites you'll have to capture at runtime.
- `verify` runs every check unseed has, and it's the one to rely on. It runs the
  fixture first, before it reads your input.

`verify` also accepts:

- `--javap-check N` compares the instruction decoder with `javap` on N classes.
- `--javap-attrib N` confirms each literal is in the method unseed says it is.
  This matters because the method name is part of the seed.
- `--reference F` diffs the results against an earlier `strings --json` run.
- `--strict` turns a low printable-character ratio from a warning into a failure.
- `--no-jvm` skips the JVM checks; `--require-jvm` fails if no JVM is available.


## Reusable pieces

Some of the code is useful outside this tool.

- **Modified UTF-8 codec.** The JVM's `CONSTANT_Utf8` stores `U+0000` as
  `0xC0 0x80` and characters outside the BMP as CESU-8 surrogate pairs. Python's
  `decode('utf-8', 'replace')` turns both into `U+FFFD`, which quietly changes
  the string. `dec_modified_utf8` and `enc_modified_utf8` handle them correctly
  and raise on malformed input.
- **Instruction decoder.** `tests/test_opcode_table.py` builds a classfile with
  one method for each of the 256 opcode bytes and checks the decoder's mnemonic
  and instruction length against `javap`.
- **Length-preserving patcher.** Each call site (`ldc <ciphertext>`, an
  optional `checkcast`, then `invokestatic` of the decryptor) is replaced with
  `ldc_w <plaintext>` padded out with `nop`s, so the code doesn't change size.
  Branch offsets, `StackMapTable` frames, exception ranges and
  `LineNumberTable` entries stay valid without being recomputed. New
  constant-pool entries go at the end, so existing indices don't shift.

## Tests

```sh
python3 -m unittest discover -s tests -t .
UNSEED_REQUIRE_JDK=1 python3 -m unittest discover -s tests -t .   # for CI
```

Without a JDK, the JVM tests are skipped. `UNSEED_REQUIRE_JDK=1` makes them
fail instead.

The fixture in `tests/fixtures/` is a synthetic class written from the algorithm
above, with no third-party code in it. Its ciphertexts come from a separately
written encryption function (`encrypt_units` in `tests/make_fixture.py`), not
from unseed's own output. The tests run the compiled fixture on a real JVM and
check that its strings match `expected.json` exactly, including an embedded
`U+0000` and a character outside the BMP. Then they do the same with the
patched classes. If the patcher had changed any instruction lengths, the JVM
verifier would reject them.

## License

MIT, see [LICENSE](LICENSE). The repository contains no third-party or vendor
code.
