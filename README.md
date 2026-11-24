# Lean 4 companion to *Beilinson–Deligne Periods and Gross–Stark Regulators of 1-Motives*

This repository accompanies Mohammadreza Mohajer's manuscript. A reader can start with any numbered result, find the matching Lean statements, inspect their hypotheses, and reproduce the exact arithmetic. The [correspondence](docs/CORRESPONDENCE.md) covers all 30 numbered items and all 44 labelled equations in the [paper](paper/manuscript.pdf). The [overview](docs/OVERVIEW.md) explains how the proofs fit together.

## What the kernel checks

| Part of the paper | Formal result |
| --- | --- |
| Sections 2–4 | Euler determinants for block matrices, norm diagrams for the critical lattice, pole cancellation, and extraction of leading coefficients in formal power series |
| Sections 5–6 | The dual-lift graph, the principal-minor determinant expansion in arbitrary finite rank, repeated Artin block products, and the Galois fixed-field step for normalized trace values |
| Sections 6–7 | The entire ideal of exponent-fiber binomials, an algebraic-independence criterion for monomials, and independence of determinants of disjoint generic blocks of positive size |
| Section 7 | Scalar descent for an arbitrary family of algebraic rows, polynomial and tail estimates, and elimination at a leading frequency under explicit sample hypotheses |
| Sections 4 and 8 | Finite-field roots and character values, an irreducible real cubic, exact generalized Bernoulli calculations, convergence and differentiation in the integral power-series coordinate, and a first jet modulo 49 |
| Section 9 | Orders and leading coefficients of products with ordinary or split multiplicative elliptic factors, given the stated interpolation coefficients |

Several manuscript arguments require constructions outside this formalization. These include the realization-theoretic comparison for 1-motives, arithmetic local duality, the Gross–Stark leading coefficient, Artin interpolation and the elliptic exceptional-zero formula. The hypotheses of the corresponding Lean declarations show where each arithmetic identification enters. The [foundations and attributions](docs/FOUNDATIONS.md) and the [statement-by-statement correspondence](docs/CORRESPONDENCE.md) identify the outstanding steps. The count of mapped statements measures coverage of the manuscript index.

## Reproduce the verification

Use Git, Python 3.10 or later, and [elan](https://lean-lang.org/install/) with Lean **4.19.0**. Run the following commands from the repository root. The first dependency fetch needs internet access and disk space for the mathlib cache. The Python scripts use the standard library.

```sh
python scripts/check_release.py
python scripts/fetch_cache.py
python scripts/verify.py
```

On systems where Python is named `python3`, use that name for each command. Windows users can use `py -3`. The [toolchain](lean-toolchain) and [Lake manifest](lake-manifest.json) pin the compiler, mathlib and transitive packages. The mathlib commit is `c44e0c8ee63ca166450922a373c7409c5d26b00b`. To limit simultaneous compiler processes on a smaller machine, run `python scripts/verify.py --jobs 1`.

The verifier compiles every project module from source, imports the root, and asks Lean for the axioms of each public theorem. It compares the output of the Lean executable with an independent exact calculation in Python. It then checks that Lean rejects three deliberately false propositions at the expected source lines. The final check compares the generated reports with the release copies. The verifier exits with a nonzero status on a discrepancy.

Generated reports appear in `build/verification/` after a local run. The checked-in [results](results/) can be read immediately. The [GitHub Actions workflow](.github/workflows/verify.yml) runs the same commands to fetch dependencies and verify the proofs, and uploads the fresh reports. `lake build` builds the Lean library. `lake env lean --run scripts/Compute.lean` prints the exact fields after that build.

## Reproduce the derivative calculation

For the quadratic character of discriminant `-687`, the character sum weighted by its argument is `-8244`. The two finite generalized Bernoulli expressions in Proposition 8.2 give `12` at zero and `-10344805682225424` at `-6`. Lean computes these sums using mathlib's Bernoulli polynomials and checks the same numbers by a rational recurrence. The normalized secants at `-6`, `-12`, and `-42` all have residue `42` modulo `49`. The last index is divisible by seven, so the calculation checks the reduced denominator before interpreting the residue. [Bernoulli polynomials](BD/SpecialValues.lean) · [Three secants](BD/Bernoulli.lean)

For an arbitrary integral power series, Lean proves convergence on the open unit ball of the actual p-adic integers, identifies the limit of its difference quotient with its linear coefficient, and proves its reduction modulo the square of the prime. In the 7-adic integers there is a unique `t` satisfying `8⁶(1+t) = 1`. At this point, the residues `24` and `3` force seven times the linear coefficient to equal `28` modulo `49`. Since the inverse of `24` is `47` modulo `49`, the normalized residue is `42`. Applying this calculation to the analytic cyclotomic derivative uses the arithmetic interpolation and the change of variable via the p-adic logarithm described in the paper. [Convergent p-adic series](BD/PadicJet.lean) · [Formal jet](BD/Jet.lean) · [All exact outputs](results/lean-calculations.txt)

## Repository guide

| Path | Contents |
| --- | --- |
| [BD](BD/) and [BD.lean](BD.lean) | Proof sources and the root import |
| [paper](paper/) | Exact PDF and LaTeX snapshots, anchor index, and their digests |
| [docs/CORRESPONDENCE.md](docs/CORRESPONDENCE.md) | Links to the paper and Lean declarations, with the scope of each result |
| [inputs](inputs/) | Arithmetic inputs, false test propositions, and machine-readable statement and equation inventories |
| [scripts](scripts/) | Verification runner, Lean executable, independent exact arithmetic and integrity checks |
| [results/verification.json](results/verification.json) | Run totals, observed kernel axioms, and source identifiers |
| [results/axioms.txt](results/axioms.txt) | Lean's axiom report for each public theorem |
| [results/theorem-types.txt](results/theorem-types.txt) | All public theorem signatures printed by Lean, including their hypotheses |
| [results/negative-controls.json](results/negative-controls.json) | The three false propositions and the verified rejection outcomes |
| [SHA256SUMS](SHA256SUMS) | Digest for each distributed file other than the checksum index |
| [CITATION.md](CITATION.md) | Paper and software citation guidance |

An ordinary verification preserves the reference reports. A maintainer intentionally updating the reference outputs can use `python scripts/verify.py --record` and inspect the diff. To assemble a fresh distribution with a regenerated checksum index, run `python scripts/package_release.py ../companion.zip` with a new output filename. Keeping a matched paper snapshot and regenerated correspondence preserves the meaning of the cross-references.

