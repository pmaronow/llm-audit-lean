# Statement referee report

All 17 targets are **correct_restricted**. Each retained statement is a
faithful, mathematically correct restricted version of its canonical claim,
and each restriction is accurately disclosed in its Challenge docstring.
There are no adverse findings and no omitted targets.

| Verdict | Count |
| --- | ---: |
| correct_whole | 0 |
| correct_restricted | 17 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| **Total** | **17** |

Severity counts: none 17, minor 0, major 0. There are no
non-`correct_*`/`omission_ok` items to enumerate. No corrections are required.

The blind readings were saved in `reading.md` before opening `claims.json`.
The 17 step-2 comparisons were saved in `claim-stage.json` before opening
`record.json`. All were classified as narrower than the complete canonical
conjunction. Reading the architect's record caused no changes to those
classifications. All record decisions are `restricted`; each declared
restriction matches its Challenge docstring and the actual retained content.

The reductions include weaker moment-order assertions for the explicit
examples, omitted intermediate identities and chain links, and T6's retention
of a finite construction rather than an assembled nonconvergent sequence.
The added premises in T8, T10, T12 and T14 are disclosed: respectively,
all-index positive true variance, all-index nonempty nondependent pair sets,
eventual nonzero B2 in the relative comparison, and positive own-arm
probabilities in the zero-B1 clause. These hypotheses have joint instances;
in particular, the nonzero-B2 part of T12 has a growing multiplicative-star
witness detailed in `findings.json`.

The retained counterexamples still refute the identified printed steps.
In particular, the positive rescalings omitted from the T15 display preserve
its strict contradiction, the zero covariance sums in T3 refute the actual
weighted inequalities, and T17's hypergeometric values and conditional
probabilities compare positive-denominator ratios on the intended domain.

The definition audit checked the full-cube interference relation, forced
potential responses, finite probability and covariance sums, mixing
suprema, Gaussian CDF, moment orders, and limit quantifiers against Mathlib.
The mixing supremum is nonempty and bounded. The degree and Rayleigh
suprema used in the examples have nonempty bounded domains. T6's limsup
predicate states the ordinary finite limsup; all real liminf uses in T2
are of probabilities in [0,1]. The special mixing power agrees with the
paper's explicit 0^0=0 convention. Relevant real divisors are positive;
the natural subtractions in the cluster construction implement its printed
max/floor formula, and the hypergeometric helper is used only at valid
arguments. The general T2 integrals have explicit integrability hypotheses.

Validation used only the supplied definitions and independent scratch work:

* `scratch/Check.lean` compiles with
  `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It proves an explicit
  product design with regularity, positive arm probabilities and positive
  HT variance, and checks the cluster and hypergeometric special values.
* `scratch/finite_checks.py` passes exact rational enumeration of the
  retained finite counterexamples, selected family members, and a nonzero-B2
  witness. Its results are in `scratch/finite-results.json`. These finite
  checks supplement mathematical reasoning; they do not prove the
  asymptotic universal statements.
* Python parsed both requested JSON artifacts and checked target coverage,
  unique theorem assignments, verdict/severity values and counts.

No Solution or Comparator source was read, and `lake` was not run.
