# Palomar statement review: P047

There are three targets: two `correct_whole`, one `correct_restricted`, and no adverse findings or omissions.

| Verdict | Count |
| --- | ---: |
| correct_whole | 2 |
| correct_restricted | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

All three severities are `none`. There are no items outside `correct_*` / `omission_ok` to report.

## Order and evidence

The blind expansion was saved in [reading.md](/home/ubuntu/sap/tasks/CHFID-P047-b/reading.md) before opening `claims.json`. The claim-only judgments were then saved in [claim-stage.json](/home/ubuntu/sap/tasks/CHFID-P047-b/claim-stage.json) before opening `record.json`. Reading the record caused no change to a step-2 judgment. The decisions `whole`, `whole`, and `restricted` agree with the independent comparison.

The comparison uses each canonical `statement`, its `definitions_needed`, and the standing assumptions. Neither `note` nor `finite_lemmas` was used to add or remove a clause. In particular, T2 is not required to assert every auxiliary finite lemma listed in the history; and T3 has no separate canonical assertion about statistical testability or sufficiency of restrictions.

The original recapitulation was also checked against the published paper. Its two bullets have the roles described in the supplied canonical claims. The supplied formal readings determine the formulas and uniformity quantifiers audited here. [Published rejoinder, Section 1](https://pmc.ncbi.nlm.nih.gov/articles/PMC12139717/)

## Target decisions

**P047-T1 — correct_whole.** The theorem contains canonical parts (i)–(vi): conditional and unconditional score means, sample unbiasedness, the contribution bound, the exact Hoeffding tail, finite-sample coverage, the deterministic ATE width and its root-n scaling, and the treated-mean component under its one-arm conditions. Its interval uses the observed outcome and known propensity; its center does not use the unknown target parameter. The formal reading expressly allows arbitrary covariate distributions. Arm-by-arm conditional factorization for all measurable integrable tests expresses the stated ignorability. The constant test also calibrates the supplied propensity as the treatment conditional probability, rather than assuming an estimator conclusion.

**P047-T2 — correct_whole.** The supremum is over every positive sample size and every law with the same positive B and epsilon, each paired with its own known propensity. This is the canonical uniform tightness assertion. The strict inequality in that supremum and the weak inequality in the separate exponential tail match the canonical statement. The variance bound and Gaussian convergence are for each fixed law, including variance zero. No uniform normal approximation or positive-variance hypothesis has been substituted.

**P047-T3 — correct_restricted.** The theorem retains all of canonical (a) and (b), including independent randomization, the finite weak-error lower bound at 1/12, failure of uniform consistency formulated with strict errors, and the width-greater-than-1/6 lower bound under the single fixed baseline law. Its model has the exact canonical uniform covariate, binary outcomes, joint ignorability and overlap [1/4,3/4]. Its observation map supplies only W, treatment and observed outcome to a procedure, and the same procedure and independent seed law are used for every population.

The two explicit omissions are precisely the ones disclosed in both the docstring and record: the extension to every model containing this class, and a separate assertion that the concrete baseline law belongs to the class. The former is a monotonicity corollary, but it is not explicitly asserted. The latter is true of the actual definition, as checked below, but is not an additional theorem conclusion. No further substantive restriction was found. Canonical (c) assigns its mathematical content to (a) and (b), so no extra testability or sufficiency clause has been dropped. The restriction is accurate and complete; no statement or docstring repair is needed.

## Nonvacuity and conventions

The command

```text
/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean
```

completed successfully with exit code 0 and no diagnostics. [The scratch proof](/home/ubuntu/sap/tasks/CHFID-P047-b/scratch/Nonvacuity.lean) imports only `SAP.P047.Defs`, uses no Challenge theorem, and contains no `sorry`. It constructs W uniform on (0,1], independent fair treatment, Y(0)=0, Y(1)=1, and propensity 1/2. It proves the full `Ignorable` property for every required test function, `BoundedOverlap` with B=1 and epsilon=1/2, `TreatedMeanModel` with epsilon=1/2, and `UnknownModel`, including joint ignorability. Thus all three model predicates are inhabited without assuming any target conclusion. In this example the ATE score is 0 or 2 with equal probability, its mean is 1 and its variance is 1. Zero outcomes also give the allowed degenerate normal case and a model for any permitted B and epsilon.

The actual baseline construction is the pushforward of independent uniform W and two fair Boolean variables. They become treatment and Y(1), while Y(0)=0. Equipping it with the measurable constant propensity 1/2 gives a `CausalLaw` satisfying `UnknownModel`: conditioning on W leaves treatment independent of the potential-outcome pair. Its ATE is 1/2. This is a direct mathematical check of the definition, not an assertion that the stub itself includes the membership theorem.

The interval coverage premise is also satisfiable. With a one-point seed and the constant finite interval [-1,1], every law in `UnknownModel` has coverage one, because its integrable outcome difference lies in [-1,1] almost surely. Alpha=1/4 is one allowed confidence level. The premise does not impose shrinking width or any of the desired impossibility conclusions.

The relevant Mathlib definitions were followed through conditional expectation, product probability measures, Bochner integrals, real-valued variance, Gaussian laws, convergence in distribution and real extrema/limits. The resulting conventions do not change these statements:

* The covariate sigma algebra is a genuine sub-sigma-algebra, and a probability measure remains finite when trimmed to it. Conditional expectation is therefore not falling back to zero because of an invalid conditioning space.
* Bounds and measurability make every outcome or score integrated by an asserted conclusion integrable; T2 scores also have finite second moments. A control potential outcome need not be integrable in the treated-only component, where it is not integrated by a conclusion. Infinite-variance-to-zero conversion therefore does not falsify the Gaussian interpretation.
* Every finite-sample rate or width assertion has n>=1, and the relevant propensity denominators are bounded away from zero almost surely. Exceptional null-set values of the total real division operation do not affect the claims. All subtraction is in the reals, not truncated natural subtraction.
* Every measure used in a probability is a probability measure, so `.real` cannot convert infinite mass to zero. The scores and observations are measurable; the procedure measurability hypotheses make the error, coverage and width events measurable.
* Every risk or coverage value lies in [0,1]. Inserting zero in a risk supremum or one in a coverage infimum ensures nonemptiness and does not change the intended extremum for the inhabited classes. Hence no unbounded real supremum, limsup or liminf convention is doing the work.
* For finite endpoints the `EReal` comparison `lo + 1/6 < hi` is exactly the event that upper minus lower endpoint exceeds 1/6. It also correctly detects unbounded real intervals. Reversed endpoints or equal infinite endpoints cover no finite parameter and do not create false width events. No endpoint-ordering hypothesis excludes procedures from the impossibility result.

## Independent check of the impossibility constants

For fixed n, partition the uniform covariate into M equal cells and give cells independent fair high/low types. Use propensities 3/4 and 1/4. In family A let the treated-outcome probabilities on the two types be 1/3 and 1; in family B let them be 2/3 and 0. Set Y(0)=0 and draw treatment independently of the potential outcomes conditional on W. These are members of the canonical model.

In either mixture, the probabilities of the observed pairs (A,Y)=(1,1), (1,0), (0,0) are 1/4, 1/4, 1/2. These are also the baseline probabilities. The observed-sample mixture laws agree with the baseline on the no-cell-collision event. The complement has probability at most n(n-1)/(2M), which bounds the relevant total variation distances. A product with an independent seed preserves this bound, so it applies to all the randomized procedures in the stub.

Writing U for the high-cell proportion, the ATEs are 1-(2/3)U and (2/3)U. Their prior means are 2/3 and 1/3, and each prior variance is 1/(9M). Chebyshev gives probability at most 16/M of leaving the respective open bands (7/12,3/4) and (1/4,5/12). Successful estimation within 1/12 on these bands distinguishes the two mixture laws by comparison with 1/2. Consequently, the worst weak-error probability at threshold 1/12 is at least

`1/2 - 16/M - n(n-1)/(4M)`.

Letting M increase proves the asserted finite lower bound 1/2 for each fixed n. Strict error at, for example, 1/24 includes this weak-error event, giving a positive asymptotic limsup.

For an interval with coverage at least c over the model at a fixed n, each of the two bands is intersected with baseline probability at least c-16/M-n(n-1)/(2M). By a union bound the interval intersects both bands with baseline probability at least 2c-1-32/M-n(n-1)/M. Such an interval has width strictly greater than 1/6. Sending M to infinity gives baseline width probability at least 2c-1. Apply this with c equal to the worst-case coverage at n, then take liminf. The canonical lower bound 1-2alpha follows. Thus the fixed-law, strict-width assertion is supported without a uniform-width substitution.

The machine-readable final judgments are in [findings.json](/home/ubuntu/sap/tasks/CHFID-P047-b/findings.json). Both JSON outputs were parsed and checked for exactly one object per target.
