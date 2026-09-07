# Build environment for the 0.4395 verification

These files record the configuration used when the 0.4395 proof was verified:

- `lean-toolchain`: Lean version.
- `lake-manifest.json`: exact dependency revisions.
- `lakefile.lean`: package configuration.

They are retained byte-for-byte so that the verification checksums can be
checked. The 0.4395 proof uses shared modules from the 0.45 proof, which is
why the recorded configuration also refers to those modules.

To build the published proof, use the configuration at the
[repository root](../../), not this directory.
