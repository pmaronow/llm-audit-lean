# Statement audit

Audited 17 canonical targets and 16 Challenge theorems.

| Verdict | Count |
| --- | ---: |
| correct_whole | 12 |
| correct_restricted | 4 |
| omission_ok | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_questionable | 0 |

All severities are `none`. There are no adverse findings requiring a
statement or docstring correction.

The four restricted targets are T41, T43, T45 and T46. Their actual
scope agrees with their docstrings and the architect's record:

| Target | Disclosed restriction |
| --- | --- |
| T41 | Retains HT consistency and its rate; omits both Hájek conclusions. |
| T43 | Retains HT in both design regimes and Hájek only under complete randomization. |
| T45 | Requires attained global moment maxima over varying uniform constants; conditions the Hájek conclusions on nonempty supported arms. |
| T46 | Uses the observed maximum at the common k and an admissible potential exponent; conditions Hájek on nonempty supported arms. |

T40's omission is justified on the supplied evidence. The record declares
its only credited row `wrong_credit`, expressly excluding even component
extraction. Its completion of Hájek is material under the target's arbitrary
designs: marginal probabilities can be uniformly interior while the design
puts probability one on assignments with an empty arm. The omitted
mathematical phenomenon itself has nontrivial examples, including the
complete-design example in `findings.json`. This omission judgment relies
on the supplied row-status declaration; it does not claim an independent
inspection of that unavailable proof.

The order was preserved: `reading.md` was saved before reading
`claims.json`, and `claim-stage.json` was saved before reading `record.json`.
No step-2 verdict was changed after opening the record. The claim stage
classified 12 theorems as whole and four as narrower.

The definition checks found no material division-by-zero convention,
empty index set, non-integrability issue, unbounded supremum, circular
hypothesis, or contradictory antecedent in the asserted conclusions.
In particular, the conditional means in the Bernoulli bias formulas have
positive conditioning masses; all count denominators are positive;
the Rayleigh sphere and coupling set are nonempty and bounded in the
directions required for their real supremum and infimum. The explicit
mixing convention agrees with
[Definition 9 in the paper](https://pmc.ncbi.nlm.nih.gov/articles/PMC8372033/).
The variance results use the actual iterated limits of Definition 10,
including existence of the inner limits. T51 asserts convergence in
distribution to the sharp three-point law and its finite Chebyshev equality;
it adds no unsupported assertion about convergence of tail probabilities
at a discontinuity of that law.

Every target has a nonvacuity instance or explanation in `findings.json`.
The asymptotic witnesses use positive populations tending to infinity:
fair Bernoulli designs, balanced complete designs, and independent
randomized pairs. In the paired zero-outcome example, dAvg=1,
eAvg=1, rSum=0, alphaExt=1/4 and alphaInt=0; the moment maxima are
attained at infinity, and both supported arms are nonempty. Thus even
the additional moment and Hájek-domain requirements in T45 and T46
hold together. Nonzero own-treatment outcomes give msq=1 for both
alternatives of T49 and T50. A concrete bounded-outcome sharp-law
construction is provided for T51.

Validation completed:

* `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` succeeded without
  errors or warnings. It imports only the supplied Defs and checks finite
  laws, regularity, nonzero effects, interference counts, complete and
  paired designs, supported arms, a supported empty Bernoulli arm, and
  the three-point law's moments.
* `python3 scratch/Enumerate.py` checked T36 for all 4,096 directed
  four-unit interference structures with mandatory diagonal, and checked
  the T35 Bernoulli identity and T47 finite bias identity in 100 exact
  rational examples with heterogeneous treatment probabilities.
* Python parsed both output JSON files and checked complete target
  coverage, unique theorem/target identifiers, verdict fields, and
  agreement between the saved claim stage and the final decisions.

These checks support the statement audit; they are not proofs of the
Challenge stubs. The supplied Lean source statements were not changed.
