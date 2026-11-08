# Review of P006-T6 through P006-T10

All five declarations are **faithful**, with severity **none**.

The blind statement and dependency reading is in `reading.md`, saved before
opening `claims.json`. Every closure entry was inspected, including all 38
generated proof declarations. The canonical statement and `definitions_needed`
were then checked independently for each target. Notes were treated as history,
not as conditions that change a claim.

## Claim comparison

- **T6**, `SAP/P006a/Defs/Part5.lean:168`: includes the selected-residual L1
  domain, TT/welfare identities, equality of both argmax sets for any feasible
  class, zero regret for every best response, the unconstrained positive-effect
  rule, and the independent pointwise-unbiased implementation. Per-policy
  `PolicyDesign` needs less independence than the standing model; that is a
  valid generalization, not a restriction. No estimator L1 condition on
  untreated observations is introduced.
- **T7**, `SAP/P006a/Defs/Part5.lean:192`: includes every weighted identity,
  the positive-effect maximizer, the almost-everywhere characterization of
  every maximizer, attained optimal welfare and zero regret. The class is
  unconstrained and g is fixed, measurable and strictly positive. `Standing`
  is applied to the zero-estimator update, so it does not silently require
  integrability of the actual estimator on untreated observations.
- **T8**, `SAP/P006a/Defs/WholeW2.lean:224`: all seven conjuncts were checked
  separately. They cover the main three clauses, selected-mean equivalence,
  independent unbiased implementation, qualified Lemma 2 including the exact
  equal-evaluation-means criterion, conditional-independence/factorization
  qualifications, and both versions of qualified Proposition 10. A common
  evaluation law is assumed only in the general Proposition 10 branch and
  derived in its auxiliary-data branch; it is not added to the main clauses.
  Policy and estimator moment hypotheses are confined to the appropriate
  feasible class. Dropping unnecessary iid assumptions in the per-policy
  branches strengthens the results without changing their conclusions.
- **T9**, `SAP/P006a/Defs/Part5.lean:232`: covers the denominator identity,
  strict dilution, both conditional numerical intervals, both printed-table
  bounds, and all four rounding intervals. The notebook intervals are inputs,
  as in the canonical statement. Filtering the sum to positive effects is
  exactly the stipulated zero-contribution convention for untreated units.

## T10: printed reading and witness check

The printed reading is: with an arbitrary feasible class of treatment rules,
a reward admitting a positive-treatment best response for some distribution
and invariant in expected value under every change of untreated outcomes
preserving the joint law of covariates and treated potential outcomes must
have unbounded regret over the allowed outcome distributions.

The checks below precede accepting the witness as a refutation of that
assertion. They use `SAP/P006a/Defs/Part5.lean:260` and the definitions in
`SAP/P006a/Defs/Part4.lean:47`–`68`.

| Printed condition | Witness check |
| --- | --- |
| Positive sample size and iid treatment population | n=1; a constant covariate and deterministic potential outcomes. Independence between units is automatic for one unit. |
| Measurable fixed policies and arbitrary feasible class | Unit is a singleton covariate space, isomorphic to the specified constant covariate 0. The only feasible policy is the measurable constant 1. Zero treatment is not required by the printed setting. |
| Probability laws, finite potential-outcome means, consistency and treatment randomization | D_B is the Dirac law at ((),(1+B,1)); all moments are finite for every finite real B>0. The Boolean-sum definition uses a fresh Bernoulli coin with propensity π(c) and the consistent observed outcome. For the feasible policy that coin is deterministically true. |
| Reward uses observable treated data | One-unit ATO is y1 when treated and zero otherwise. It uses no untreated outcome. |
| Assumption 3, existence of a positive-treatment best response | Every real objective is maximized at the sole feasible policy; its expected propensity is 1. `NondegenerateReward` is explicitly established. |
| Invariance for every policy and every pair of allowed laws with the same (c,y1) law | The general identity is E[w_ATO]=∫π(c)y1 dD. The pushforward-law equality implies equal expected reward for every admissible policy, not only the feasible one. |
| Failure of the asserted conclusion and withholding step | Welfare and its feasible maximum are both −B. Regret is zero for every real objective, hence under every finite-mean law. No feasible policy with zero treatment exists; the claimed lower bound would read 0≥B with B>0. |

Thus this witness contradicts the canonical printed assertion itself, under
all of its conditions. Its failure is not produced by dependent replicate
draws, nonmeasurability, undefined expectations, or an unintended supremum
convention.

## Verification

The scratch files construct hypotheses directly and do not invoke any of the
five Challenge theorem stubs. `scratch/Nonvacuity.lean` uses a true Bernoulli
treatment experiment with effect one, oracle baseline zero, and the entire
admissible policy class. It checks all T6 and T7 hypotheses and each separate
T8 branch, including actual reward and welfare maximizers for its regret
clause. Treated and untreated policies have welfare one and zero. A half-coin
instance checks the selected-measure and conditional-independence domains.

`scratch/Arithmetic.lean` checks T9 with the two fitted effects [1,0] and with
exact rational interior values for every numerical hypothesis. It also checks
T10's finite-moment witness for every B>0, its nondegeneracy, and its full
treated-data invariance independently of the Challenge stub.

No asserted integral relies on nonintegrability defaults. Every regret
conclusion uses an attained maximum, the normalization n is positive, and
the ATO zero-on-empty convention is explicit and matches the claim.

## Record comparison

`record.json` labels all five targets `whole`, with no restrictions. All five
decisions are correct and their docstrings accurately describe the statements.
For T10, `whole` means the full canonical **counterexample** is proved; it
does not mean the printed impossibility theorem is established. No step-2
conclusion changed after reading the record. The `broader` entries for T6 and
T8 in `claim-stage.json` identify valid generalizations which still cover every
canonical clause, and hence are compatible with `whole` coverage.

Both nonvacuity files compiled successfully (exit 0). The generated-closure
inspection also compiled successfully. No external paper lookup was necessary:
the supplied canonical claims include the relevant printed assertions and
standing conditions. `findings.json` records one clean entry per declaration.
