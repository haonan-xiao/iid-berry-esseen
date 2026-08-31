# A 0.45 Upper Bound for the i.i.d. Berry--Esseen Constant

This repository contains a short theorem note and its Lean 4 formalization.
The note proves that the optimal absolute constant in the classical
i.i.d. Berry--Esseen inequality is at most `0.45`.

OpenAI Codex autonomously developed the proof, formalized it in Lean, generated
the exact numerical certificates, and drafted the initial manuscript. The
authors supplied the research question and candidate materials, reviewed the
result, and prepared this version for arXiv.

**Read the current note:** [open the 10-page PDF](paper/berry-esseen-045.pdf).
No LaTeX installation or compilation is required.

## Result

Let `X₁, X₂, ...` be independent and identically distributed real random
variables with mean zero, variance one, and
`ρ = E|X₁|³ < ∞`. For

```text
Sₙ = (X₁ + ... + Xₙ) / √n,
```

the note proves, for every integer `n ≥ 1`,

```text
supₓ |P(Sₙ ≤ x) - Φ(x)| ≤ 0.45 ρ / √n.
```

The key quantity is the symmetrized third-moment ratio

```text
r = E|X-X'|³ / (2 E|X|³),
```

where `X'` is an independent copy of `X`. The modulus bound weakens as `r`
increases, whereas the bound on the sine remainder `E[sin(uX)-uX]` strengthens.
Preserving this dependence sharpens the single-summand comparison with the
Gaussian characteristic function. Prawitz smoothing then reduces the theorem
to an explicit scalar inequality, proved on the full continuous parameter
domain by exact dyadic interval certificates.

## Read the note

- [Paper PDF](paper/berry-esseen-045.pdf)
- [LaTeX source](paper/main.tex)

## Repository layout

| Path | Contents |
| --- | --- |
| `paper/` | Current PDF, LaTeX source, and bibliography |
| `BerryEsseen/` | Lean modules grouped into probability, characteristic-function, smoothing, and certificate layers |
| `BerryEsseen.lean` | Root Lean module |
| `FORMALIZATION.md` | Map from the paper's proof to the Lean modules and trust boundary |

## Verify the Lean development

The repository pins Lean, Mathlib, and StatLean in `lean-toolchain` and
`lake-manifest.json`.

```bash
lake exe cache get
lake build BerryEsseen
```

A fresh full build is intentionally expensive because it replays the exact
certificates for `n = 1, ..., 99` and three large-sample regions. Incremental
builds reuse Lake's local cache when the relevant sources have not changed.

The analytic proof and the soundness of the interval checker are checked by
the Lean kernel. The closed Boolean certificates are evaluated with
`native_decide`, so this last computation additionally trusts Lean's native
compiler. The source contains no `sorry` declarations or user-declared axioms.

## Rebuild the PDF from source

With a LaTeX installation providing `latexmk` and BibTeX:

```bash
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error paper/main.tex
```

## License

The repository is released under the [MIT License](LICENSE).
