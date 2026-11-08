# Review report: SAP.P015b.T18 and SAP.P015b.T17

The work: Aronow and Samii, AJPS 2016. Files written: `reading.md` (blind, step 1), `claim-stage.json` (step 2),
`findings.json` (final). Scratch checks: `scratch/Print.lean` (elaborated statements and universes) and
`scratch/Nonvac.lean` (nonvacuity instances). Both compile.

| theorem | record decision | verdict | severity |
|---|---|---|---|
| SAP.P015b.T18 | refuted | faithful | none |
| SAP.P015b.T17 | refuted | faithful | none |

## T18 (`T18Statement := LogisticMLStationarity ∧ SquareLinkFailure`)

**Printed reading of (C).** For any GLM fit by ML in the paper's setting, the ML treatment coefficient equals, to
first order (expanding around m⁻¹(E Y)), the OLS coefficient times a factor that depends only on E[Y]. Its
conditions are a GLM, a true ML estimate, W = (1, D, X), the causal model (1)–(3), and a first-order regime.

**How the witness meets each condition.**
- *GLM:* a Bernoulli GLM with link √μ, i.e. mean function η² on the GLM parameter space {0 < Wθ < 1}.
- *ML estimate:* θ(ε) is the unique interior maximizer of the expected Bernoulli log-likelihood.
- *Design:* the design (1, D−e(X), X) spans the same space as (1, D, X), so the D-coefficient is unchanged.
- *Causal model:* (1), (2) and (3) are all asserted.
- *First-order regime:* the derivative is taken at θ(0) = (1/2, 0, 0). There every fitted index sits exactly at
  m⁻¹(1/4), which is the paper's expansion point.

**Result.** For both a = 0 and a = 1/16, E[Y] = 1/4 and the OLS coefficient is ε. The ML derivative is 1 for a = 0
and 120/119 for a = 1/16, while 1/m'(m⁻¹(1/4)) = 1. So (C) fails for the printed "any GLM", and the `refuted` label
is right.

**Clause (A)** is proved more generally than printed: any design with K+2 columns and binary Y.

**Junk values.** Matrix inverse, log, condExp, Bochner integral and deriv are all genuine here: either a nonzero or
nonsingular value is asserted, or log is only evaluated inside (0,1).

**Docstring and record.** Both are accurate, and the omission of (B) is disclosed.

**Observations (not defects):**
- Over the sign-unrestricted domain of η², a mixed-sign index fits better (−0.5607 vs −0.5623 at ε = 0, found
  numerically). Such indices lie outside the √-link GLM, where η = √μ > 0, and the docstring's "ML branch" signals
  the branch.
- In standard GLM terms the model has a "square-root link" with mean η². "Square-link" is loose shorthand but does
  not change the content.
- The refutation is at the population (probability-limit) level, which is the paper's own level for (7).

## T17 (`DiscretePositivityImplications ∧ SmallWeightFamily ∧ SmallWeightConsistency ∧ FittedZeroFailure ∧ MissingPairFailure`)

**(A)** is proved pointwise at every atom P(X=x) > 0, as the canonical formal reading has it. The restrictions are
countable B with measurable singletons and a global L² treatment. Both are disclosed in the docstring and the record.

**(B)** is refuted on its first consequent ("positivity is violated"), so the whole implication fails, in two ways:
- *Approximately zero population weight:* strict positivity in both strata, a linear potential-outcome model and
  unconfoundedness, yet Q(X=0) < 4ε.
- *Exactly zero estimated sample weight:* a population with positivity; an iid sample with probability 1/256 has a
  well-defined full OLS (det 2) and D̃² = 0 on the X=0 units.

SmallWeightConsistency (known-propensity IPW is consistent at ε = 10⁻⁶) is true and supplementary.

**(C)** is refuted with D ∈ {0,1,2}. P(D=0) and P(D=1) are both positive, the effective law gives Q(X=1) = 4/5, but
Q(D=1|X=1) = 0. In fact every pair of values fails somewhere in the effective sample, so the refutation does not
depend on which pair is of interest.

**Junk values.** All are checked and genuine: the cell divisions are by 1/2; E[w] > 0; the effective-law normalizer
is positive and finite; and the toReal is of a finite 0.

**Docstring and record.** Both are accurate.

**Observation (not a defect).** The docstring does not say that measurability of X and D (a usual condition) is
assumed. The restrictions that go beyond the usual conditions are listed.
