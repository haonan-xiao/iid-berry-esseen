# Lean source map

The formalization is organized by mathematical role:

| Path | Role |
| --- | --- |
| `Interface.lean` | Probability-law definitions and the theorem interface |
| `Probability/` | Distribution-free estimates, Gaussian inversion, and normalized-sum moments |
| `CharacteristicFunction/` | Moment constraints shared by the modulus bound and the bound for the sine remainder, and the resulting characteristic-function estimate |
| `Smoothing/` | Prawitz smoothing and the analytic scalar reduction |
| `Certificate/Dyadic/` | Exact interval arithmetic and proved-sound elementary bounds |
| `Certificate/Finite/` | Finite-`n` checker, coverage proof, batches, and data for `1 ≤ n < 100` |
| `Certificate/LargeN/` | Large-`n` regions, checker, coverage proof, and three data files |
| `Assembly.lean` | Conditional assembly from the numerical estimate |
| `Theorem.lean` | Exact certificate assembly and the final theorem `iidBerryEsseen45` |

The files under `Certificate/Finite/Data/` are intentionally separate. Each
contains one exact certificate, so Lean can evaluate, cache, and diagnose the
corresponding `native_decide` computation independently. They are proof data,
not separate mathematical arguments.

The package entrypoint is [`../BerryEsseen.lean`](../BerryEsseen.lean). See the
[build and verification guide](../README.md) for the trust boundary and build
command.
