# P017 statement audit

The blind reading is in `reading.md`; it was saved before opening the claims or
record. The claim-only classifications in `claim-stage.json` are all `whole`.
Every named closure declaration, including all generated proofs, was read.

For T1, the printed reading is: every observed empirical realization admits an
admissible full-data weight representing the original clipped estimate. The
conditions and witness checks are:

| Condition | Witness check |
| --- | --- |
| Integrable heterogeneous effect under a probability law | Uniform (0,1), mean 1/2, support [0,1], radius 1/2 |
| Observed empirical data and an estimator using them | Observed pairs (T,Y); IPW estimate is their empirical mean under the specified summand |
| Independent draws from the specified G | Countable product of G; each full-data draw has independent effect, baseline and assignment |
| Positive-variance root-n normality | Bounded IID summands with variance 53/12; the normal limit is stated |
| Original target and admissible weights | Clip to [0,1]; all measurable nonnegative full-data weights with positive finite mean are excluded at the endpoints |

Each of the two bad events has probability 4^(-n)>0. The realized empirical
laws are specified. Thus this is a counterexample under the printed reading.

For T5, the printed reading is: in the Gaussian-plus-small-remainder
decomposition, the Gaussian part minus the **actual target of the shifted
estimate** has the displayed Gaussian-tail nonzero probability and is little-o
in probability of every positive deterministic sequence. The checks are:

| Condition | Witness check |
| --- | --- |
| Integrable heterogeneous population | Effect is symmetric on {-1,1}; mean 0 and radius 1 |
| IID observed empirical data | Independent pairs from N(0,1) times the symmetric effect law; the observed data may be the first coordinate |
| Empirical statistic and normal decomposition | Sample mean A_n, estimate A_n+1/n; sqrt(n) A_n is exactly standard normal |
| Small remainder | sqrt(n)/n tends to zero; all involved functions are measurable with finite moments |
| Definition 2 applied to the estimate | Intermediate error is A_n-clip(A_n+1/n), rather than A_n-clip(A_n) |
| Positive rate | 1/n for n>=1; changing its value at zero to 1 preserves every LittleOp limit |

The intermediate error is nonzero with probability one, but the proposed
Gaussian tail is strictly less than one. On |A_n|<=1/2, n>=2, the intermediate
error is -1/n while the actual clipping error is zero. This refutes the
printed proof assertions and preserves the proposition's actual-error claim.
The journal text agrees with the canonical interpretation of the intermediate
error. [Publisher-provided paper text](https://www.researchgate.net/publication/310050238_Data-Adaptive_Causal_Effects_and_Superefficiency).

T2 includes the exact criterion and both explicit bounded normalized weights.
T3 includes every interior/atom, finite-range and infinite-radius clause and
both probability limits. T4 includes every positive smaller radius, its
existence, all three finite companions, and the larger-radius obstruction.
No conclusion is hidden in a definition. All divisions and extended-real
operations have the required guards or harmless initial-index conventions.

After reading `record.json`, I retain all five claim-stage conclusions. Its
five `whole` decisions and null restrictions are accurate; the docstrings
describe the statements correctly. T1 and T5 are whole formalizations of
canonical counterexample targets. Neither is incorrectly classified as a
refutation of a corrected proposition.

`scratch/Blind.lean` and `scratch/Nonvacuity.lean` compiled with `sap-lean`.
The latter constructs the two-point population with mean zero and radius one,
an admissible constant weight, positive atom/two-sided branches, a finite-range
witness, d=1/2, and a Gaussian estimator satisfying the root-n hypothesis.
It also proves independence of the actual IPW and normal sample coordinates
and verifies the harmless positive-rate extension at zero. Its named proof
dependencies contain only propext, Classical.choice and Quot.sound, with no
sorryAx. The challenge proofs were not used by these checks.

| Declaration | Verdict | Severity |
| --- | --- | --- |
| SAP.P017.T1 | faithful | none |
| SAP.P017.T2 | faithful | none |
| SAP.P017.T3 | faithful | none |
| SAP.P017.T4 | faithful | none |
| SAP.P017.T5 | faithful | none |
