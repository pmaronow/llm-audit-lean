# Palomar statement audit: P002b

Audited 15 targets and 13 Challenge theorems. There is one major issue with
an omission rationale and one minor issue with restriction metadata. No exported
mathematical proposition was found false or vacuous.

| Verdict | Count |
| --- | ---: |
| correct_whole | 10 |
| correct_restricted | 2 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 1 |
| **Total** | **15** |

Severity counts: 13 none, 1 minor, 1 major. T26's mathematical content is
whole; it receives `restriction_inaccurate` because its record and docstring
misidentify an excluded descriptive sentence as a restriction of the target.

**P002-T28 — omission_questionable, major.**

The omission reason in [record.json](/home/ubuntu/sap/tasks/CHFID-P002b-a/record.json:331) says the available row
certifies corrected interval-index pairs while the canonical claim requires
the shifted Step 5 indexing. This contradicts the canonical instruction in
[claims.json](/home/ubuntu/sap/tasks/CHFID-P002b-a/claims.json:206): “formalize Algorithm 2 with the pairs as Step 4
records them, in the corrected form of P002-T22.” The same note explicitly
identifies the shifted Step 5 indexing as a printing error. A row is not
ineligible for this target merely because it follows that required correction.

The complete headline result is still absent. T22 and T23 both assume a
nonempty crossing list. They do not certify T28's no-intersection branch;
T22 also expressly omits termination for every prescribed admissible choice
policy. These are scope gaps that need assessment on their own merits.

Fix: reassess the listed `algorithm_correctness_paper` row against the corrected
canonical target. Export equality of the returned set and the empirical
confidence set for Algorithms 1/3 and corrected Algorithms 2/4, including
empty crossing lists, with termination for every admissible choice policy for
Algorithms 2/4. If only a restricted result can be exported, disclose its actual
scope. Do not justify omission by demanding the known indexing error.

The domain is nonempty. The checked eight-unit examples below admit a
one-crossing run in each branch. Keeping the same observed data and using only
one simulated assignment gives a regular, no-intersection instance: the sole
simulated curve is always critical, and its comparison with the observed curve
is exactly the empirical confidence set.

**P002-T26 — restriction_inaccurate, minor.**

[record.json](/home/ubuntu/sap/tasks/CHFID-P002b-a/record.json:286) labels this target restricted. Its declared
restriction and the [Challenge docstring](/home/ubuntu/sap/tasks/CHFID-P002b-a/SAP/P002b/Challenge/Part1.lean:46)
say that the introductory finite-union-of-intervals sentence is omitted.
However, the canonical note in [claims.json](/home/ubuntu/sap/tasks/CHFID-P002b-a/claims.json:178) explicitly says
this sentence “is descriptive and not part of the target.” The exported theorem
contains all formal content (a)-(c). In particular, the affine contrast is
unconditional on a nonzero receipt contrast, and the Wald and IV conclusions
have the stated guards. The additional nonzero guard in the IV branch is
redundant under the invertible first-stage block matrix.

Fix: leave `T26Statement` unchanged, set the record decision to `whole` and
restriction to `null`, and remove the docstring's Restriction sentence. Suitable
replacement text is:

> The adjusted contrast is affine in the hypothesized effect. When the adjusted
> receipt contrast is nonzero, the Wald ratio has zero statistic and lies in
> the confidence set; under the stated invertibility conditions it equals the
> just-identified IV coefficient.

The nonzero-denominator and invertibility conditions are jointly satisfiable:
the four-unit example below has receipt contrast 1, Wald estimate 24, and
determinant 1/16 for both IV matrices.

The remaining record decisions agree with the audit:

- T16, T17, T18, T19, T23, T24, T25 and T27 cover their canonical mathematical
  content. T16 is an explicit counterexample to the printed maximum equality.
- T20 is correctly restricted: its probabilistic part adds positive oracle
  design variance at every sequence index and invertible control Grams on the
  entire design support. Both additions, and their limitation to the
  probabilistic part, are disclosed. The exact finite oracle expansion remains.
- T22 is correctly restricted to existence and correctness of completed finite
  runs. Its docstring accurately disclaims termination for every prescribed
  sequence of admissible choices. Completion is part of `Algorithm2Run`, rather
  than a termination theorem disguised as a hypothesis.
- T21's omission is justified on the supplied evidence. Its canonical statement
  uses an ordinary inner limit. A limsup bound does not establish that limit's
  existence. The canonical note itself flags this gap. No unavailable source
  theorem was inspected to strengthen the evidence in the record.
- T29 and T30 faithfully refute the printed universal equalities. Their verdicts
  concern the true negations exported by the Challenge, rather than the false
  positive assertions in the paper. Nonempty counterexample classes suffice
  for both refutations, as detailed below.

The blind reading was saved as [reading.md](/home/ubuntu/sap/tasks/CHFID-P002b-a/reading.md) before opening
`claims.json`. The 13 comparisons in [claim-stage.json](/home/ubuntu/sap/tasks/CHFID-P002b-a/claim-stage.json) were
saved and parsed before opening `record.json`. No step-2 verdict was changed
after reading the record. The T26 metadata issue was already identified from
the canonical note during step 2. The cited paper is
[Randomization-based confidence sets for the local average treatment effect](https://arxiv.org/abs/2404.18786);
the supplied canonical excerpts control this audit's target scope.

The checks supporting nonvacuity and definition fidelity are as follows.

1. **Genuine raw and adjusted algorithm inputs.**
   [scratch/Check.lean](/home/ubuntu/sap/tasks/CHFID-P002b-a/scratch/Check.lean) imports only the Defs package and
   constructs eight units, four treated, all units compliers, with identical
   potential outcomes in both receipt states:

       Y = (0,1,2,3,4,2,5,-3),
       O = {0,1,2,3}, T0 = {0,1,2,4}, T1 = {0,1,4,5}.

   It proves `DataGeneratedCoefficients`, regularity of the observed and both
   simulated raw curves, and that `[0]` is the complete sorted intersection
   list. The raw coefficient vectors `(a,b,c,d,e,f)` are

   | Curve | Coefficients |
   | --- | --- |
   | observed | (1/16, 1/16, 1/64, 0, 0, 43/256) |
   | simulated 0 | (1/64, 0, 0, 3/512, 1/128, 87/512) |
   | simulated 1 | (0, 0, 0, 1/128, 1/128, 87/512) |

   The second simulated curve is zero; the first vanishes exactly at zero.
   Both denominator quadratics are everywhere positive. At alpha=1/4 the
   critical curve is simulated 0, including in both closed gap pieces.

   Exact rational arithmetic also checks the adjusted branch on the same data
   with centered covariates `(-7,-5,-3,-1,1,3,5,7)`. All 70 assignments have
   nonsingular Grams in both arms. The adjusted coefficient vectors are

   | Curve | Coefficients |
   | --- | --- |
   | observed | (1, 21/5, 441/100, 0, 0, 109/80) |
   | simulated 0 | (4/25, 0, 0, 3/140, 1/8, 13/8) |
   | simulated 1 | (64/289, 0, 0, 1/136, 1/8, 559/272) |

   All are regular. The only crossing is again zero: after factoring out
   beta squared, the comparison polynomial has negative leading coefficient
   and negative discriminant. At alpha=1/4 the critical curve is simulated 1.
   Both algorithms admit the pieces `[-infinity,0]` and `[0,+infinity]` with
   the corresponding critical index. These witnesses test the actual
   data-generation predicate, rather than arbitrary unattainable quadratics.

2. **Nonzero regression and IV instance.**
   Take n=4, k=1, n1=2, x=(-3,-1,1,3), y_i(0)=y_i(1)=x_i^3,
   d_i(a)=a, and S={0,1}. The treated and control Grams are respectively
   `[[1,-2],[-2,5]]` and `[[1,2],[2,5]]`, each with determinant 1;
   the population Gram has determinant 5. Population coefficients are
   `(0,41/5)`. At beta=0 the feasible contrast is 24 and the oracle contrast
   is 24/5, giving the nonzero difference 96/5 in T18. The treated coefficient
   error is `(-12,-24/5)` and its cross term is -288/5 in T19.
   With D=1_S, the receipt contrast is 1 and both IV determinants are 1/16.
   This supplies instances for T18, T19, T20's finite part, T24, T25 and T26.

3. **A nonempty infinite T20 domain.**
   For every n=j+4 take k=1, n1=floor(n/2),
   x_i=(2i-n+1)/n, identical outcomes x_i^2 in both receipt states,
   all units compliers, and constants
   `(delta,e,A,B,r)=(0,1/4,1,4,1/4)`. The population residual is
   q_i=x_i^2-mean(x^2), since symmetry gives mean(x)=mean(x^3)=0.
   The exact moments give

       mean(x^2) = (n^2-1)/(3n^2) >= 1/4,
       mean(q^2) = 4(n^2-1)(n^2-4)/(45n^4) >= 1/16.

   Covariates and residuals have absolute value at most 1, so their fourth
   moments meet A=1 and B=4. The identical residual arrays have nonnegative
   covariance and positive variance. Every control arm has at least two
   distinct covariates, hence an invertible Gram. The oracle design variance
   is `V(q)*(1/n1+1/n0)>0`. Thus the two extra restrictions do not make
   the limit assertion vacuous.

4. **Coverage refutations without empty classes.**
   For any centered array q at n>=2, the fourth norm is at least
   `sqrt((n-1)/n)*sqrt(V(q))`, by the finite Cauchy inequality. A fourth-norm
   upper bound of `(1/2)*sqrt(V(q))` therefore forces q=0.

   For T29 choose `(delta,r,A)=(0,1/4,1/2)`. Both centered W arrays must
   vanish; at LATE their means agree. Hence every observed adjusted response
   array is constant, every supported statistic and its critical value are
   zero, and coverage is 1. For every n>=2 and every beta, all-complier
   populations with baseline zero, constant effect beta, and n1=floor(n/2)
   lie in the class. The nested infimum is therefore genuinely 1. The Lean
   file additionally proves a concrete Theta instance with these constants.

   For T30 choose `(k,delta,e,A,B,r)=(1,0,1/4,4,1/2,1/4)`.
   Population OLS residuals are centered, and the same inequality forces both
   residual arrays to be zero in every admitted model. On assignments with
   full-rank arms, arm OLS recovers the population coefficients and the
   adjusted contrast at LATE is zero. The chance of a singular arm tends
   uniformly to zero: singularity means its covariates are constant, hence
   its sample second moment equals its squared sample mean. Chebyshev applied
   to the sample means of x and x^2, using mean(x)=0, mean(x^2)>=e,
   mean(x^4)<=A and arm size >=rn, bounds this event by C(e,A,r)/n.
   Thus all coverages are at least `1-C/n` and the nested infimum tends to 1.
   The classes are nonempty for every n>=4 and every beta: use the distinct
   centered grid above, all compliers, baseline zero and constant effect beta.
   Its second moment is at least 1/4 and its fourth moment is at most 1.
   The argument permits the defined rule on singular assignments; no
   unprinted assertion about their regression coefficients is needed.

   These refutations use r=1/4, genuine models at every sufficiently large
   size, and arbitrary real LATEs. They do not need empty-infimum values,
   parity failures at r=1/2, or zero-dimensional covariates.

5. **Conventions and verification.**
   Group covariances for a single complier and the studentized 0/0 value
   agree with the supplied paper conventions. Valid designs ensure positive
   arm and population denominators; all relevant finite maxima have positive
   size. Full-rank and regularity hypotheses guard the matrix inverse and
   rational-curve divisions where those formulas are used. T25's singular
   OLS choice is deterministic and depends only on the inputs permitted by
   its canonical note. Algorithm predicates require sample-point validity,
   leaving interval validity to the theorem conclusions.

   `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` exited successfully.
   Its six printed axiom checks contain only `propext`, `Classical.choice`
   and `Quot.sound`, with no `sorryAx`; see
   [scratch/lean-check.log](/home/ubuntu/sap/tasks/CHFID-P002b-a/scratch/lean-check.log).
   `python3 scratch/check_arithmetic.py` passed all rational checks and wrote
   [scratch/arithmetic-evidence.json](/home/ubuntu/sap/tasks/CHFID-P002b-a/scratch/arithmetic-evidence.json).
   The final JSON files were parsed with Python and checked against all
   15 target IDs and all 13 Challenge theorem names. No Defs or Challenge
   source was changed, and no Solution or external formalization was read.
