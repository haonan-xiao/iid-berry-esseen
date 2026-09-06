# A 0.4395 Upper Bound for the i.i.d. Berry--Esseen Constant

This repository contains a short theorem note and its Lean 4 formalization.
The note proves that the optimal absolute constant in the classical
i.i.d. Berry--Esseen inequality is at most `879/2000 = 0.4395`.

The proof, Lean formalization, exact numerical certificates, and initial
manuscript were developed autonomously using OpenAI Codex, primarily with
GPT-5.6 Sol. The authors supplied the research question and candidate
materials and coordinated the review and preparation of the note.

**Read the note:** [open the 13-page PDF](paper/berry-esseen-04395.pdf).
No LaTeX installation or compilation is required.

## Result

Let `X₁, X₂, ...` be independent and identically distributed real random
variables with mean zero, variance one, and `ρ = E|X₁|³ < ∞`. For

```text
Sₙ = (X₁ + ... + Xₙ) / √n,
```

the note proves, for every integer `n ≥ 1`,

```text
supₓ |P(Sₙ ≤ x) - Φ(x)| ≤ (879/2000) ρ / √n,
```

where `Φ` is the standard normal distribution function.

The improvement from 0.45 is 0.0105, with no additional assumptions.
The argument retains the shared third-moment ratio
`r = E|X-X'|³ / (2E|X|³)`, for independent copies `X, X'` of `X₁`,
and also uses the first absolute moment `E|X|`.
These quantities constrain both parts of the characteristic function and
sharpen its comparison with a symmetric two-point law and with the Gaussian
characteristic function. Prawitz smoothing reduces the result to scalar
inequalities on the full continuous parameter domain, verified by exact
dyadic interval certificates.

## Repository layout

| Path | Contents |
| --- | --- |
| `paper/` | Current PDF, LaTeX source and bibliography |
| `BerryEsseen.lean` | Root entrypoint exporting the 0.4395 theorem |
| `lean/BerryEsseen/` | Proof modules grouped into moments, characteristic functions, smoothing and interval arithmetic |
| `lean/BerryEsseen/Certificates/` | Generated certificates grouped by sample size and parameter region |
| `lean/BerryEsseen/Theorems/`, `Verification/` | Final theorem assembly and axiom audits |
| `FORMALIZATION.md` | Paper-to-Lean map, reproduction instructions and trust boundary |
| `proof-guide.md` | Detailed human proof and correspondence with the Lean lemmas |
| `lean/evidence/`, `evidence/` | Source manifests, relocation map and original execution evidence |

The previous 0.45 note and formalization remain available in the
[initial version](https://github.com/haonan-xiao/iid-berry-esseen/tree/fcdaa7923de9557fdb5744c9a89fa6665c7aab67).

## Verify the Lean development

The repository pins Lean, Mathlib and StatLean in `lean-toolchain` and
`lake-manifest.json`. From the repository root:

```bash
lake exe cache get
lake build BerryEsseen
```

A fresh full build is expensive because it evaluates the exact certificates.
[FORMALIZATION.md](FORMALIZATION.md) gives a concurrency-limited, resumable
replay, lightweight checks, and the mathematical reading order. Run build
commands from the repository root; there is one active Lake configuration.

The original full numerical run passed. The publication layout has been
checked against those exact sources under the recorded renaming and comment
changes, and selected renamed analytic modules have been freshly compiled.
A full numerical replay of the renamed layout has not yet been performed.

The analytic proof and interval-checker soundness are checked by the Lean
kernel. Concrete Boolean certificates use `native_decide`, which additionally
trusts Lean's native compiler. The accepted theorem contains no `sorry` or
user-declared axioms; the full named native-axiom inventory is supplied.

## Rebuild the PDF

With a LaTeX installation providing `latexmk` and BibTeX:

```bash
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error paper/main.tex
```

## License

The source is provided under the [MIT License](LICENSE).
