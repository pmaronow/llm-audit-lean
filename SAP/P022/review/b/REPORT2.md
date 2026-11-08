# Delta referee report

All **18 revised targets are accepted**: **10 whole, 6 restricted, 2 refuted; 0 outstanding issues, 0 false statements, 0 accidental vacuity, 0 omissions**. Every earlier adverse finding is fixed.

The requested findings schema has no `correct_refuted` verdict. Accordingly, `findings2.json` uses `correct_whole` for complete, correctly labelled refutations as well as complete positive targets: **12 correct_whole (10 positive/whole + 2 refuted), 6 correct_restricted**, and zero in every adverse or omission category. This encoding does not certify an affirmative version of either false printed assertion. The record decisions remain `refuted` for T5 and T18.

| Finding verdict | Count |
| --- | ---: |
| correct_whole | 12 |
| correct_restricted | 6 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

## Earlier adverse findings

| Earlier finding | Status | Revised assessment |
| --- | --- | --- |
| T1: omitted second counterexample and inaccurate whole-coverage declaration | **Fixed** | The mathematics still retains only witness A. The record now says `restricted`; the docstring discloses all of witness B, A's unstated boundedness/condition-4 and individual CDF/left-CDF facts, finite probability identities, and the partition proof-step assertion. Fixing this finding did not require restoring B once the restricted scope was accurately declared. |
| T5: missing general equality characterization and inaccurate whole-coverage declaration | **Fixed** | The theorem now includes the universally quantified equality iff population CDF equals one half, together with `choose(4,2)=6`. Its classification is `refuted`, and the numerical witness genuinely refutes the printed equation. |
| T18: refutation labelled as a whole proof of the affirmative lemma | **Fixed under the updated rule** | The mathematical negation is unchanged, but the record now says `refuted` and the docstring announces that the printed claim is false. The user now explicitly permits that decision. The original recommendation to omit the affirmative target is therefore unnecessary. |

No earlier adverse finding is only partly fixed or remains unfixed. No new adverse finding was identified.

## Comparison with the saved reading

All revised Defs and Challenge sources were read. The mathematical changes are T5, T6, T8, T10 and T17. The classification/docstring changes additionally affect T1, T7, T9 and T18. Moving T10 to Defs Part6 and adding explicit auto-implicit options are organizational changes. The original `reading.md`, `claim-stage.json`, `findings.json` and `REPORT.md` are preserved.

| Target | Change and judgment |
| --- | --- |
| T1 | Same closed counterexample; complete restriction disclosure added. **Correct restricted.** Its exact CDF distances and divergent tails refute the actual printed conclusions. |
| T5 | Adds the finite allocation count and general equality characterization. **Correct refutation with all canonical counterexample clauses represented.** A valid Design automatically has `m<N`; the characterization cannot exploit the zero coefficient at `m=N`. |
| T6 | Adds `C>0` only before the finite reciprocal CDF-threshold implication. The other finite statements retain `C>=0`. The restriction text states this precisely, keeps the conditional six-rate/lemma hypotheses explicit, discloses function dependence and missing minimization, and discloses the separate lower allocation's omission. **Correct restricted.** |
| T7 | Same two infinite limsups. The restriction now lists the missing finite identities, moment/variance calculations, displayed rate and stronger convergence assertions. **Correct restricted.** Infinite limsup alone does not state probability convergence or full sequence divergence. |
| T8 | Adds `m+k<=N` to the variance-substitution clause. This is the standing canonical population domain, so no valid-design clause is removed. Partition/rank, widths, centered covariance, both variance substitutions and overlap weights are retained. **Correct whole.** |
| T9 | Same all-ones negative output and general discrepancies. The restriction now lists the omitted witness calculations, shifted-weight-sum identity and translation comparison. **Correct restricted.** |
| T10 | Takes the fixed-sample limit along `N=r+(m+k)` and makes `m,k>=2` explicit in the eventual-fixed-arm clause. The first change enumerates all admissible sizes cofinally; the second follows from eventual equality with valid designs. The earlier remainder/example omissions are accurately disclosed. **Correct restricted.** |
| T17 | Adds the defined-law-functional guard, positive limiting upper bound, positivity of every finite upper estimate, and a critical-set guard in the coverage clause. Every new antecedent is disclosed at the correct quantifier scope. The original gamma range, actual-variance limit and studentized CLT remain; coverage is explicitly guarded. Optimality is expressly omitted. **Correct restricted.** |
| T18 | Same negation, correctly classified as `refuted`. The law, integer-function, sequence and allocation quantifier order matches the printed law-dependent-integer reading, and the reciprocal counterexample defeats it. **Correct refutation.** |

The mathematical statements and substantive definitions of T2, T3, T4, T11, T12, T13, T14, T15 and T16 are unchanged; their `whole` decisions remain accepted after checking their canonical clauses. In particular, T14's full sampling is already canonical, T12's contradiction is the intended numerical incompatibility, and the moment assumptions in T15 justify its covariance extrema.

My earlier whole classifications for T7 and T9 did not distinguish every unstated auxiliary assertion from the retained refutations. Under this delta review's explicit clause-completeness requirement, the revised restricted classifications and detailed disclosures are appropriate. T17 now has substantive additional hypotheses, so its restricted classification is warranted independently of the earlier disagreement about how to treat the optimality prose.

## New hypotheses, junk values and nonvacuity

The new [law-functional predicate](/home/ubuntu/sap/tasks/CHFID-P022-b/SAP/P022/Defs/Part4.lean:54) requires, for **every compatible law**, integrability of both coordinates, coordinate squares, centered squares and the centered product. It also requires a nonempty covariance image bounded above and below. These are genuine integral and real-extremum conditions, not aliases for the statistical conclusions. The [critical-set predicate](/home/ubuntu/sap/tasks/CHFID-P022-b/SAP/P022/Defs/Part4.lean:68) requires exactly nonemptiness and boundedness below of the set defining the normal quantile.

For [T17](/home/ubuntu/sap/tasks/CHFID-P022-b/SAP/P022/Defs/Part6.lean:129), the balanced periodic four-corner population satisfies **all** original and new hypotheses. All compatible laws have bounded Bernoulli marginals, so the moment guard holds and covariances lie in `[-1/4,1/4]`; the diagonal coupling attains the upper value. The upper limiting bound is `1` and gamma is `1/2`. Each finite row contains all four corners. If both observed arms were constant with values `a,b`, the corner `(1-a,1-b)` could belong to neither arm, contradicting full sampling. Hence at least one marginal sample variance is positive in every assignment. Its coefficient is positive and the binary sharp upper covariance is `min(p,q)-pq>=0`, proving the finite positivity guard for every row and assignment.

That guard is a real restriction: prepend four zero pairs before the same periodic population. The original asymptotic assumptions and nonsingular limiting law persist, but the first row's estimated upper variance is zero. The revised disclosure says positivity of **every finite estimate**, so it correctly covers this exclusion. It does not assume the CLT or coverage result.

For every `0<alpha<1`, monotonicity and the zero/one Gaussian CDF tail limits make the critical set nonempty and bounded below. This entire alpha-range assertion is independently Lean checked. Thus the coverage clause's added guard is not an empty or impossible statistical domain.

T6's reciprocal denominator is positive under the new `C>0` guard, while the zero-outcome sequence with `C=1` realizes all of its conditional assumptions. T8 and T10 now use valid positive population sizes explicitly. T5's general equality clause has both equality and strict-inequality examples, with a positive coefficient in every valid Design. No changed statement exploits division by zero, truncated indexing, a nonintegrable step-function integral, an unbounded real limsup, an empty assignment type or a hypothesis asserting the statistical conclusion.

[Full nonvacuity and change notes](/home/ubuntu/sap/tasks/CHFID-P022-b/scratch/delta-nonvacuity.md) give the general arguments and exact parameter choices. Their sequence-limit and all-row positivity arguments are mathematical arguments, not claimed Lean certificates.

## Independent verification

`/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean` passed with exit 0. It imports **only Defs**, and checks the positive T5 variance coefficient and equality algebra, the allocation count, the valid cofinal population domains, the T6 denominator, compatible-law image nonemptiness, and `NormalCriticalDefined alpha` throughout `0<alpha<1`. No `lake` command was run.

`python3 scratch/delta_checks.py` passed: **2,397 exact hypergeometric sampled-CDF laws** check the restored T5 characterization; **7,053 exact corner allocations** for `4<=N<=14` support T17's finite positivity; all **six restriction texts** occur verbatim in the Challenge docstrings. There are 28,351 mathematical arithmetic assertions and six disclosure checks. [Results](/home/ubuntu/sap/tasks/CHFID-P022-b/scratch/delta_checks.json) are saved. These finite calculations support the general mathematical arguments; they are not proofs of the asymptotic results.

The architect's report was checked against the declarations and record. Its claims about Solution, bridges, axioms and external certification were not adopted as evidence of statement fidelity, and none of those sources was read. The changed theorem statements themselves, their labels and restriction disclosures are accepted.
