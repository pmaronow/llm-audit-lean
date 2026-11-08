# P013b statement audit

Thirteen canonical targets; twelve theorem stubs. Counts:

| Verdict | Count |
| --- | ---: |
| correct_whole | 11 |
| correct_restricted | 0 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 1 |

Severity: eleven none, one minor, one major. No present theorem was found false or vacuous. The two adverse findings concern the omission rationale and a restriction disclosure.

## P013-T20 — omission_questionable, major

There is no theorem stub for Proposition 3.1. The record excludes the almost-sure-limit rows because mutual independence is allegedly absent from the canonical hypotheses. This directly contradicts `claims.json`, target P013-T20, `canonical_claim.note`, which says: “Formalize with an infinite sequence of independent replicates, each distributed as the design, and almost-sure convergence of each matrix entry”. The note also reiterates independent whole-design replicate draws in its accepted review.

Consequently the stated reason does not justify omission. The finite identities alone do not prove a strong law, as the record correctly observes, but that does not justify discarding the two limit rows for an assumption already required by the canonical reading. Their full theorem types are outside the supplied files, so this audit does not claim they have no other mismatch.

Reassess those rows against iid whole-design draws. The intended statement is almost-sure, entrywise convergence of the two empirical exposure-product matrices, with diagonal additive smoothing and normalization R+1 for the same-exposure matrix and normalization R for the cross-exposure matrix. If omission remains necessary, record the actual mismatch. Independent fair binary replicates on a one-unit population give a standard nonvacuity instance; bounded indicator entries satisfy the strong law.

## P013-T24 — restriction_inaccurate, minor

The conditional scaling identities are mathematically sound, and most restrictions are accurately disclosed. However, the [Challenge docstring](/home/ubuntu/sap/tasks/CHFID-P013b-a/SAP/P013b/Challenge/Part1.lean:49) says the item and survey nonrespondents “and their containment” are hypotheses. The record likewise says containment is explicit. The canonical empirical containment is that the 151 survey nonrespondents are among the 342 item nonrespondents.

The [scaling clause](/home/ubuntu/sap/tasks/CHFID-P013b-a/SAP/P013b/Defs/Part8.lean:116) uses respondent sets `item` and `survey`. The canonical containment would require `item ⊆ survey`. The only containment hypotheses actually present are `item ⊆ S` and `survey ⊆ S`; neither the premise nor the conclusion relates the two respondent sets. This part of the canonical information is omitted, rather than made conditional.

The distinction is substantive even with a nonzero recorded score. With zero-based unit indices, take S={0,…,2049}, item={0,…,1707}, survey={1,…,1898}∪{2049}, weights all 1, and score 1 at unit 1 and 0 elsewhere. These sets have cardinalities 2050,1708,1899; both retain every nonzero score and satisfy all scaling hypotheses. Yet unit 0 is a survey nonrespondent and an item respondent. Both scaling equalities still hold. The construction is checked by [verification.py](/home/ubuntu/sap/tasks/CHFID-P013b-a/scratch/verification.py).

Correct the docstring and record to say explicitly that nesting of the two respondent sets is omitted. Alternatively, add `item ⊆ survey` as an explicit, unverified hypothesis. Suggested replacement restriction text is supplied in `findings.json`; it preserves the other disclosed omissions, including empirical provenance and strictness of the sufficient condition.

## Accepted decisions and checks

All remaining record decisions are supported by the statement reading. In particular, T18's `refuted` decision is correct: its theorem negates the entire printed natural coverage claim, with the literal printed dependency predicate. Its `correct_whole` finding describes a whole-claim refutation, not a positive coverage result. The stage-2 label `different` records the logical polarity and has not been changed. The other ten stage-2 `whole` labels and T24's `narrower` label are also unchanged after reading the record.

An independent T18 witness uses one common fair binary exposure for all N units and fixed potentials y_i(1)=√(i+1)−√i, y_i(0)=0. Treatment totals telescope to √N, N times the true effect-estimator variance is exactly 1, and boundedness and positivity hold uniformly. A diagonal dependency indicator satisfies the literal printed predicate with row bound 1. At the all-control assignment the variance estimate and estimate are zero while the target is positive, so coverage is at most 1/2 at every N. Taking α=1/4 refutes the printed bound. This argument does not use unbounded liminf or undefined critical-value conventions.

The apparent extra symmetry condition in T27 is justified: Section 10 says its school network is an undirected adjacency graph built from within-school nominations. The supplied arXiv version confirms this on PDF p.25. [Paper, Section 10](https://arxiv.org/pdf/1305.6156#page=25).

The blind reading was saved in `reading.md` before opening `claims.json`. `claim-stage.json` was saved and parsed before opening `record.json`. No stage-2 reading or classification was changed after opening the record.

Validation uses [scratch/Check.lean](/home/ubuntu/sap/tasks/CHFID-P013b-a/scratch/Check.lean), importing only Defs and compiled with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It verifies positive-marginal and cross-joint instances, a misspecification witness, the diagonal printed-dependency property and its row bound, zero control-assignment estimate/variance for the T18 witness family, positive probabilities for all five Section 10 exposures, and the count-calibration premise. It does not import or use the Challenge stubs. The final compilation succeeded with no diagnostics; `scratch/lean-check.log` is empty.

`python3 scratch/verification.py` passes 243 signed-outcome/design instances for the covariance/variance inequalities and Hajek bound, independently enumerates the finite example values, verifies the full-size school combinatorial fractions, and checks the T24 nonnesting witness. These finite checks supplement the mathematical statement audit; they are not presented as proofs of the general theorems. JSON parsing and target/theorem coverage are checked with Python 3.
