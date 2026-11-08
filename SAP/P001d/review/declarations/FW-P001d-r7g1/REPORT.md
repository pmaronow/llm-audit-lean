All five declarations are **faithful**, with severity **none**. The current `whole` decisions are correct. The two earlier T62 docstring issues are fixed.

| Declaration | Clause check |
| --- | --- |
| T58 | Both the one-observation signed-kernel example and the continuous triangular-population example are present, including strict decrease, the negative interval bound, CDF-domain failure and absence of a real square root. |
| T59 | The normalized nonnegative density, monotonicity, continuity and both CDF endpoint limits are stated. The range and right-continuity properties follow, so applicability of every functional on CDFs is covered. |
| T60 | The corrected integral and its change-of-variables formula are stated. The rectangular-kernel identity has exactly the necessary lower-endpoint exclusion. |
| T61 | Population calculations, both median weak limits, the unrestricted bounded-direction derivative of the specified functional, both all-size functional weak limits, and both variance obstructions are present. |
| T62 | The marginal normal premise, conditional weak-bootstrap premise, real-cutoff moment equivalence, conditional standard-deviation consequence, finite-variance mean case and all-size local-density median case are present. |

`reading.md` was saved before any claims or review history were opened. `claim-stage.json` was saved before `record.json` was opened. The record required no change to those judgments. I read every closure entry, including generated numeral, typeclass and nonnegativity proofs using `scratch/Blind.lean`. None adds a hidden substantive premise.

For T58 the printed reading is: every even normalized kernel admitted by Definition 3.3.7 yields an integrated estimator to which every statistical functional on CDFs can be applied. The conditions and witness checks are:

- IID continuous data with a common PDF: the continuous triangular probability density is explicitly normalized; its countable product supplies genuine IID observations.
- An even, integrable kernel of mass one: the stated signed kernel has exactly these properties; nonnegativity is absent from the printed hypothesis.
- Positive bandwidth and sample size: the witness uses bandwidth one and every positive size.
- A real functional defined on CDFs: `G↦sqrt(G(0))` is defined throughout that domain. The estimated function is outside the domain almost surely, with a strictly negative value at zero and no real square root.

For T61 the printed reading is: under the usual functional regularity and a root-n Gaussian estimator limit with positive limiting variance, the ideal n-out-of-n bootstrap standard deviation is consistent in the stated scaled sense. Its conditions and witness checks are:

- IID observations: the specified probability mixture has a countable product realization.
- A statistical functional at the true CDF: the specified `T0` is defined on every proper CDF, has value zero at this population, and is locally affine with derivative `h↦h(0)` in every bounded sup-norm direction.
- Marginal normality: the all-positive-size limit is explicitly `N(0,1/4)`; the odd-size median also has its asserted `N(0,4)` limit.
- The printed independent resampling design: all `n^n` label maps have probability `n^(-n)`. Constant label maps are possible outcomes of independently uniform draws; no dependent replication substitutes for independent resampling.
- Defined conditional moments: each sample has a finite resampling distribution of finite real statistic values. Infinite unconditional estimator moments do not invalidate these conditional quantities or the variance of the Gaussian limit.

The lower probability bound `3/16` for scaled variance exceeding 5 contradicts the proposed variance consistency. T58 and T61 establish their canonical counterexample assertions, so their correct package label is `whole`, rather than `refuted`.

The totalized operations do not change these meanings. Positive sizes and bandwidths protect divisions; empirical quantiles are taken over nonempty bounded-below sets; arbitrary nearby functions use the functional's affine branch. The transformed-uniform endpoint has measure zero. Every `toReal` probability is finite. The T62 upper limits concern probabilities in `[0,1]`, so conditional completeness introduces no junk upper limit. The maps used for pushforwards are measurable, excluding `Measure.map`'s arbitrary-Dirac default for a non-a.e.-measurable map on a nonzero measure. The kernel normalization equality excludes the nonintegrable Bochner default.

`scratch/Checks.lean` compiles actual IID product constructions, all rectangular-kernel hypotheses, a positive finite-variance Gaussian mean instance, composite measurability for its observed/resampled means, the median conventions, the excluded-endpoint countertest and a constant-label probability. Population normalization for the two counterexample products uses the certified unconditional normalization conjuncts. The remaining general T62 normal-limit premises are also jointly satisfiable: Gaussian sample means are exactly marginally normal, and empirical variance convergence plus bounded empirical fourth moments gives the conditional Lindeberg condition. The same Gaussian population satisfies the median density and positive-moment premises. These asymptotic nonvacuity facts are argued, not separately reproved as scratch Lean CLTs.

The earlier T62 issue concerned two ambiguous docstrings. Challenge/Part1.lean:42–46 and Defs/WholeW2.lean:200–205 now state the marginal normal premise and explicitly require the equivalent moment/variance conditions for the standard-deviation conclusion, matching the actual implication at Defs/WholeW2.lean:219. Each earlier issue is recorded separately as fixed in `findings.json`.
