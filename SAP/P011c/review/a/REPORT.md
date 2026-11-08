# Palomar statement audit: P011c

Thirteen targets were reviewed: **8 correct_whole, 4 correct_restricted, 1 omission_ok**. All other verdict counts are zero. Severity counts: **13 none, 0 minor, 0 major**. There are no adverse findings or requested fixes.

The eight `correct_whole` verdicts include four correct refutations of printed universal assertions. They do not certify those printed assertions as true. The literal step-2 classifications `different` for T31, T32, T33 and T35 remain unchanged: each theorem negates its printed positive claim. The record correctly identifies each decision as `refuted`.

| Target | Recorded decision | Final verdict | Scope checked |
|---|---|---|---|
| P011-T29 | whole | correct_whole | OLS representation and unbiasedness; general covariance-sum variance identity |
| P011-T30 | omitted | omission_ok | A feasibility-only helper would not establish the computational classification |
| P011-T31 | refuted | correct_whole | Refutation of universal scaled oracle consistency |
| P011-T32 | refuted | correct_whole | Refutation of the combined general/homoskedastic conservativeness contract |
| P011-T33 | refuted | correct_whole | Refutation of the printed general-estimator interval guarantee |
| P011-T34 | restricted | correct_restricted | Only proof component P3, with the other components expressly omitted |
| P011-T35 | refuted | correct_whole | Refutation of the combined OLS variance-and-coverage contract |
| P011-T36 | restricted | correct_restricted | Full displayed Proposition 2; introductory nonconsistency assertion omitted |
| P011-T37 | whole | correct_whole | Both homoskedastic conservativeness limits, without a cap bound |
| P011-T38 | whole | correct_whole | Full CLT plus eventual positive variance |
| P011-T39 | restricted | correct_restricted | Both clipped coverage implications for Borel statistics on raw outcome spaces |
| P011-T40 | whole | correct_whole | Both printed homoskedastic interval guarantees |
| P011-T41 | restricted | correct_restricted | Capacity PSD, normalized nonnegativity for n>0, and fixed-correction maximizer invariance |

## Order and evidence

`reading.md` was saved before opening `claims.json`. It expands every Challenge theorem, the SAP definitions, and the relevant Mathlib conventions. `claim-stage.json` was then saved and parsed before `record.json` was opened. No step-2 verdict was revised after reading the record. No Solution, Comparator, or external formalization source was read.

The canonical comparison uses the supplied final-journal quotations and standing assumptions. A browser request to the [publisher's article](https://projecteuclid.org/journals/electronic-journal-of-statistics/volume-12/issue-2/Confidence-intervals-for-linear-unbiased-estimators-under-constrained-dependence/10.1214/18-EJS1448.full) encountered an access check. The supplied [arXiv identifier](https://arxiv.org/abs/1602.00359) resolved to the older version about means, so it was not used to override the supplied final-journal text.

## Nonvacuity of the shared asymptotic assumptions

For every k take n=k+1 and the uniform product law on {-1,+1}^n. Let all weights be 1, let G and R be empty graphs, and let d=0. Then the rows have dependency graphs, the empty graphs nest, beta=0, every weighted coordinate is bounded by 1, and all coordinate variances are 1. Independence gives Var(betaHat)=1/n exactly. Thus `Scaling F 1 1 1 2`, `Valid F`, and rowwise `Homoskedastic` all hold. There is no zero limiting variance or empty sample.

The empty graph is the unique compatible graph at every outcome, making all V1/V2 maximizer premises satisfiable everywhere. For the two homoskedastic estimators, V2=V2prime=sampleVariance/n. For T39, the deterministic Borel statistic V=1/n equals the true variance, so both conditional antecedents hold. These are actual finite-moment probability laws; totalized integration does no work.

## A counterexample to all four retained V1 contracts

This is an independent mathematical witness, without relying on the record's proof names. Let n=4(k+1). Take G to be k+1 disjoint four-cycles, and put s=(1,-1,1,-1) around each cycle. Let theta=1 and Y_i=s_i+epsilon_i, where the epsilon_i are independent uniform signs times 1/4. Set R=G and d_i=2.

All four scaling constants can be chosen as `(2,2,1/16,2)`. The family nests by adding a four-cycle; the row mean beta is zero; |Y_i|<=5/4; all degrees are 2; and n Var(betaHat)=1/16. All weighted-coordinate variances equal 1/16. A dependency graph is allowed to contain edges between independent outcomes: its definition constrains nonedges, so using independent coordinates is legitimate. Since every vertex's two mandatory edges exhaust its cap, G is the unique compatible graph, for every raw outcome.

To bound V1 on its entire support, write S=I+A_G, P=I-11^T/n, delta=s, and eta=P epsilon. Then S delta=-delta, sum_i delta_i=0, ||S||op=3, and ||eta||²<=||epsilon||²=n/16. Therefore

```
n V1(G,Y)
  = (delta+eta)^T S (delta+eta) / n
  = -1 - 2 delta^T epsilon / n + eta^T S eta / n
  <= -1 + 1/2 + 3/16
  = -5/16.
```

Consequently `n(Var(betaHat)-V1)>=3/8`, so the underestimation event at epsilon=1/4 has probability one at every row; the absolute-error event also has probability one. V1 is negative on the entire support, so the explicitly defined printed-interval coverage is zero at every row and every 0<alpha<1. This establishes actual refutations of the printed claims in T31, T32 and T33.

For T35 take the fixed two-parameter mean model with design row `(1,s_i)` and coefficient vector b=(0,1), selecting the intercept. The Gram matrix is n I_2, the mean model E[Y_i]=s_i is correct, all coordinates are integrable, and the intercept's olsTheta row is identically 1. The preceding bounds therefore refute the OLS contract with a fixed nonempty coefficient index and nonsingular designs. In fact both conjuncts fail for this witness, although the theorem only asserts negation of their conjunction.

T32 likewise negates a combined contract: the general conclusion already implies its homoskedastic specialization, so the theorem alone does not separately assert a homoskedastic refutation. Its docstring says exactly that. The witness above happens to be homoskedastic, providing additional external reassurance without enlarging the theorem's credited scope.

## Correctness and restrictions

The positive asymptotic conclusions agree with their retained claims. For T36, if sigma_n² is the common weighted-coordinate variance and M_n is the average squared deviation of the individual means from beta, the sample variance differs from sigma_n²+M_n by o_p(1). M_n>=0, and covariance domination gives n Var(betaHat)<=sigma_n² g_n with 1<=g_n<=1+c2. This yields the retained one-sided limit without imposing equal means. Pointwise domination then gives both T37 limits without a bound on supplied caps.

For T38, centering each weighted variable at its own expectation gives bounded summands with the same bounded-degree dependency graph; the sum's variance is asymptotic to c3 n. The dependency-graph CLT applies. Positive c3 and positive sizes also imply eventually positive variance. T39 then has the stated Slutsky and one-sided truncation consequences. V2 and V2prime are nonnegative, giving the printed intervals of T40. Although graph selectors have no explicit measurability hypothesis, their maximizing objective values equal finite maxima of continuous functions over fixed nonempty compatible sets and are Borel measurable.

Each restricted decision is accurate and fully disclosed by its Challenge docstring:

* **T34:** retains P3 only; expressly omits P1, P2, P4 and P5 and states that homoskedasticity is unnecessary for P3.
* **T36:** retains the complete displayed probability limit and expressly omits the introductory nonconsistency assertion.
* **T39:** retains both clipped coverage implications, requires raw-space Borel measurability, expressly excludes completion-only statistics, and claims no passage to a.e.-equal versions.
* **T41:** retains the capacity condition with real subtraction, PSD and normalized nonnegativity, and all-maximizer equivalence under a fixed additive correction. It expressly omits the exact matrix decomposition and restricts normalization to n>0. PSD and maximizer invariance still include n=0. No uncompleted asymptotic repair is credited.

For T41, the retained finite assertions follow from the signless-Laplacian identity `K=(A_R+diag(r))+diag(1+h-2r)` and cancellation of the fixed constant in objective comparisons. A nontrivial instance is C4 with r=2 and h=3, giving K=2I+A_C4.

The T30 omission is justified on the permitted evidence. The Challenge and Defs do not contain a faithful complexity assertion or an objective-preserving optimization equivalence. The record describes the unused declaration as a two-endpoint incidence feasibility equivalence; that would not itself prove C1's full optimization encoding, C2's NP-hardness claim or its refutation, or C3's PTAS. No unsupported complexity result is credited.

## Executed checks

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0. The scratch file imports only Defs and contains no `sorry`. It checks C4 degrees and compatibility, zero mean and the negative oracle quadratic form, the exact finite V1 and V2 values, the two-column Gram matrix and its nonzero determinant, a positive-size integrable/L2 mean-model instance, and a nonempty capacity-condition instance. The complete asymptotic families above are mathematical witnesses; they were not compiled as Lean Family instances.

An exact-rational Python enumeration independently checked that the four-cycle is the unique compatible four-vertex graph with R=C4 and d=2, and that n V1 is negative for all sixteen small-noise outcomes (range [-25/16,-9/16]). This finite enumeration supplements the uniform bound above.

Both requested JSON outputs were parsed with Python, and their target/theorem coverage and allowed verdict values were checked. No `lake` command was run; Lean checks ran one process at a time.
