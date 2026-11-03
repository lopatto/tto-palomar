# Schatten-class truncated Toeplitz operators

Lean formalization by **Patrick Lopatto**, author and maintainer. Code is licensed
under [Apache-2.0](LICENSE).

The mathematical source is the **local manuscript**, which is not distributed here.
The related
[public paper by Patrick Lopatto and Richard Rochberg](https://arxiv.org/abs/1410.1906)
provides the bibliographic reference; the formalized statements follow the local manuscript.

## Advertised scope

The twelve declarations below are in `TTO.Paper.Proved` in the independent
[Challenge](Challenge.lean) and [Solution](Solution.lean) environments.
[comparator.json](comparator.json) selects all twelve.

| Local manuscript | Declaration | Material scope |
| --- | --- | --- |
| Theorem 1 | `besovClassificationTheorem` | Nonconstant inner function, model-space symbol; both Besov criteria and four uniform norm bounds, every real p>0 |
| Theorem 2 | `compactClassificationTheorem` | Model-space symbol; compactness, VMOA, and a continuous equivalent Hankel symbol |
| Theorem 3 | `interpolatingClassificationTheorem` | Infinite simple interpolating Blaschke zeros; boundedness, compactness, every p>0, quantitative comparisons |
| Theorem 4 | `perturbedKernelBasisClassificationTheorem` | Infinite simple Blaschke zeros, bounded analytic components; perturbed kernel basis, compactness and every p>0 |
| Theorem 5 | `gapSplittingTheorem` | Singular inner representation and an analytic gap; splitting in algebraic two-sided ideals |
| Corollary 1 | `canonicalGapSplittingTheorem` | Canonical-symbol low-frequency form of the gap criterion |
| Theorem 6 | `finiteAtomClassificationTheorem` | Nonempty finite family of distinct positive atoms, p>1; unique scalar corrections, compatible splitting and uniform bounds |
| Theorem 7 | `polynomialClassificationTheorem` | Blaschke, nonatomic singular and atomic singular cases; Blaschke Schatten criterion for p≥2 |
| Theorem 8 | `hilbertSchmidtEnergyTheorem` | Exact bidisk/boundary energy, closed analysis operator, positive operator and form domain |
| Theorem 9 | `differentialRealizationTheorem` | Differential realization, kernel action and exact operator-domain criterion |
| Remark 3 | `coanalyticBesovTheorem` | Coanalytic Besov criteria and four uniform bounds, every p>0 |
| Remark 10 | `squaredKernelQuotientTheorem` | Squared-kernel quotient, norm inequality and equality criterion; refinements as qualified below |

**No additional external mathematical hypotheses are assumed.** Literature inputs
needed by these results are proved in the source closure. The only permitted
axioms are `propext`, `Quot.sound` and `Classical.choice`.

**Conditional refinement:** in the squared-kernel result, universal norm equality
and the concrete operator-domain refinement require the local manuscript's
explicit `KernelGraphCore` hypothesis: the span of the specified kernel graph
pairs is dense in the analysis graph. Universal graph-core validity is not proved.
The quotient, norm inequality and individual equality criterion do not require
that hypothesis. The stronger universal one-variable RKHS characterization
is not claimed.

Material differences from the public paper include the all-p ranges in the
interpolation/basis criteria, scalar-compatible finite-atom splitting, the
possibly nonzero atomic polynomial Hilbert–Schmidt conclusion, and the
energy/operator-domain formulation with the explicit graph-core condition.
The package does not claim the wider Sedlock/Crofoot extension, the cited
thin-sequence characterization, or the stronger infinite-rank illustration.
The separate logarithmic and two-atom counterexamples are also omitted from this
minimal package. Supporting lemmas are included as required by the proof route.

## Build and check

Pins: Lean **v4.35.0**, Mathlib
**56a005855ea17e0b0958f73ec801ae140b0a1679**; transitive dependencies are pinned in
[lake-manifest.json](lake-manifest.json). Install Lean through elan, then run:

~~~sh
lake exe cache get
LEAN_NUM_THREADS=1 lake --no-cache build Challenge
LEAN_NUM_THREADS=1 lake --no-cache --wfail build Solution
LEAN_NUM_THREADS=1 lake --no-cache --wfail build StatementChecks
LEAN_NUM_THREADS=1 lake --no-cache build
~~~

Challenge uses only canonical Mathlib imports and contains twelve intentional
statement placeholders. Its definitions are complete. Solution does not import
Challenge and has no admissions. [StatementChecks.lean](StatementChecks.lean)
checks independent expected types and critical meanings outside Solution's
import closure; it also prints transitive axioms for the advertised results.

These native builds and source checks do not run Palomar's protected verifier.
Comparator isolation, NanoDa and protected Linux checks must run in Palomar's
mandatory verification of the eventual public commit. No registration or
acceptance is claimed. The Challenge is within the hard size limit but exceeds
the preferred size threshold.

## Attribution

Mathlib and Lean supply the base libraries. Narrow Apache-2.0 ports from
[TauCeti](https://github.com/TauCetiProject/TauCeti/tree/d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad)
retain their original copyright and contributor notices in the source;
TauCeti is not a Lake dependency. OpenAI Codex agents contributed proofs and
performed independent agent reviews under the maintainer's direction;
this does not claim external human review or endorsement.
