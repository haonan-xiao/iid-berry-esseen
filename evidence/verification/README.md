# Verification records for the 0.4395 bound

The completed verification checked 2,480 modules. The final theorem's axiom
inventory contains 2,407 native-evaluation witnesses and the three standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Records of the completed verification

| File | Contents |
| --- | --- |
| `acceptance.json` | Verification results, dependency versions and checksums identifying the execution archive |
| `source-manifest.tsv` | Checksums of the 0.4395 proof modules and their 102 literal input files |
| `baseline-manifest.tsv` | Checksums of the shared 0.45 modules and package configuration used by the 0.4395 proof |
| `build-order.json` | Module dependencies, compilation order and native theorem names used in the completed verification |
| `final-axioms.txt` | The 2,410 axiom names reported for the verified theorem |
| `promotion.json` | Source checksums recording the replacement of large certificate computations by equivalent smaller computations |

## Correspondence with the published sources

| File | Contents |
| --- | --- |
| `source-layout.json` | Verified-to-published source mapping, checksums, text-input locations and the inventory of unused 0.45 aggregate modules omitted from this version |
| `publication-build-order.json` | Module dependencies and native theorem names in the published layout |
| `publication-axioms.txt` | The expected axiom inventory after renaming; not a second execution result |

The machine-readable execution records retain the names used during the
completed computation. The mapping connects them to the current Lean files.
Run the source correspondence check from the repository root:

```sh
python lean/scripts/replay.py --check-sources
```

This checks source correspondence without repeating the numerical
computations. For a full replay or an audit of the execution archive, see
[FORMALIZATION.md](../../FORMALIZATION.md).
