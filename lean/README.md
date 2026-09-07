# Lean proof of the 0.4395 bound

The main theorem is
[`BerryEsseen.iidBerryEsseen879_2000`](BerryEsseen/Theorems/Bound04395.lean).
Its probability assumptions and the paper-to-Lean map are in
[FORMALIZATION.md](../FORMALIZATION.md).

| Directory | Contents |
| --- | --- |
| `BerryEsseen/Probability/` | Probability laws, normalized sums and general bounds |
| `BerryEsseen/Moments/` | Constraints from the first and third absolute moments |
| `BerryEsseen/CharacteristicFunctions/` | Component, modulus and comparison inequalities |
| `BerryEsseen/Analysis/`, `Smoothing/` | Scalar analytic inequalities and the Prawitz reduction |
| `BerryEsseen/Interval/` | Exact interval arithmetic, evaluators and coverage proofs |
| `BerryEsseen/Certificates/` | Concrete computations grouped by sample size and parameter range |
| `BerryEsseen/Theorems/` | Assembly of the 0.4395 result |
| `BerryEsseen/Verification/` | Axiom audits, comparison results and diagnostic checks |
| [certificate-data/](certificate-data/) | Text inputs containing subdivision trees; not compiled Lean modules |
| `scripts/` | Replay and verification-record checking tools |

Build from the repository root using its Lake configuration. There is one
public theorem entrypoint, [BerryEsseen.lean](../BerryEsseen.lean), and one
directory of [verification records](../evidence/).
