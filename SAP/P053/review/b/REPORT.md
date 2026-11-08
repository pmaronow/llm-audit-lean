# P053 statement audit

Eight targets audited: **6 correct whole, 2 correct restricted, 0 adverse findings**.

| Verdict | Count |
| --- | ---: |
| correct_whole | 6 |
| correct_restricted | 2 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

All severities are `none`. No target is omitted. There are no items outside
`correct_*` or `omission_ok` requiring correction.

## Order and record reconciliation

`reading.md` was saved after reading the Defs and Challenge files and following
the relevant Mathlib definitions, before opening either JSON source.
`claim-stage.json` was then saved against the canonical statements,
definitions_needed and standing assumptions, before opening `record.json`.
Audit-history notes and finite_lemmas were not used to add or remove claim clauses.
The record agrees with all eight independently saved judgments. No stage-2
judgment was changed after reading the record.

| Target | Theorem | Architect decision | Audit verdict |
| --- | --- | --- | --- |
| P053-T1 | SAP.P053.T1 | whole | correct_whole |
| P053-T2 | SAP.P053.T2 | restricted | correct_restricted |
| P053-T3 | SAP.P053.T3 | whole | correct_whole |
| P053-T4 | SAP.P053.T4 | whole | correct_whole |
| P053-T5 | SAP.P053.T5 | whole | correct_whole |
| P053-T6 | SAP.P053.T6 | restricted | correct_restricted |
| P053-T7 | SAP.P053.T7 | whole | correct_whole |
| P053-T8 | SAP.P053.T8 | whole | correct_whole |

## The two disclosed restrictions

**T2.** `Defs/Part4.lean`, `T2Statement` and `RepeatedScaling`, retain both
four-unit statistics, both nonfactorization assertions, every positive repeated
block size, the assignment/table/statistic values, size divergence, allocation
and success-fraction limits, and a raw fourth-moment bound. They do not assert
a full S5 certificate with outcome/effect-variance and average-effect limits,
which canonical clause (v)'s standing-conditions assertion calls for.
`Challenge/Part1.lean:15` explicitly lists this missing certificate and these
missing limits. The record's restriction is accurate and complete. The family
in fact satisfies the missing conditions: its equal potential outcomes are
binary with mean 1/2, variances N/(4(N-1)) tending to 1/4, zero effect variance,
and zero average effect. The theorem simply certifies less.

The counterexamples refute the unrestricted reading admitting labels and fixed
covariates. They do not contradict the corrected table-statistic assertion of
T1. The docstring makes this distinction explicitly and correctly; the record
labels the theorem `restricted`, not `refuted`.

**T6.** `Defs/Part5.lean`, `T6Statement`, adds `PositiveOLS E` only to the
variance-ratio and studentized conclusions. This means eventual strict
positivity at **every supported assignment**, a stronger condition than
positivity with probability tending to one. Canonical parts (a) and (c) do not
assume it. The theorem also omits the Introduction's FRT/Wald test equivalence
under local alternatives: there is no conditional FRT law, quantile, p-value
or comparison of rejection rules. `Challenge/Part1.lean:39` names all of these
restrictions; the record describes their placement accurately. The local
unstudentized variance difference and both constant-effect approximations have
no added positivity hypothesis.

This restriction is real. In a balanced binary sharp-null population with half
successes and half failures, assigning all successes to treatment makes both
within-arm sums of squares zero. Such assignments exist at every population
size despite S5 and a positive limiting outcome variance. They are excluded by
`PositiveOLS`, so the added antecedent is not redundant.

## Definitions, truth checks and nonvacuity

The assignment support is precisely the set of fixed-size subsets and has its
usual binomial cardinality; randomization averages and probabilities are uniform
on it. Table entries use integer subtraction. The one natural subtraction in
T1 is M-a with a<=M on support. The floor in the explicit factor equals the
integer treated-success count at every attained statistic value, and only
chooses an extension elsewhere. Symmetric samples use an increasing bijection
onto the selected units. Thus no empty index set or truncated count is doing
the mathematical work.

The estimators have the canonical N-1 population/sample and N-2 pooled
divisors. S5 is recorded as population conditions, without assuming estimator
consistency or a CLT. The eventual arm-size field follows from interior
allocation and diverging size, so it is not a further restriction. All
asymptotic estimator divisors are positive eventually. T6's added positivity
handles its remaining studentization domain. The Gaussian is a genuine
probability measure of variance one; for 0<alpha<1 its critical-value set is
nonempty and bounded below, so neither conversion of infinite mass to a real
number nor an invalid infimum is involved.

Bounded raw fourth moments give random-sampling consistency of arm means and
second moments. These yield the T5 and T7 variance expansions. The exact
randomization identity

    Var(hat_tau) = S1^2/n1 + S0^2/n0 - Stau^2/N

gives T8's bound and constant-effect equalities. Under the sharp null and a
positive variance limit, the fourth-moment bound also gives the finite-population
CLT condition: the largest squared centered outcome divided by N times the
population variance tends to zero. Studentization and continuity of the normal
CDF then give the retained T6 normal and size assertions. No claim was found
false in these checks.

A single nonconstant family establishes joint satisfiability even of T6's
stronger antecedents. For m=k+1, set N=10m, n1=2m, n0=8m, and Y1=Y0 equal
to +1 on 5m units and -1 on the other 5m. Then

    (p,v1,v0,vt,tauInf) = (1/5,1,1,0,0),
    S1^2 = S0^2 = N/(N-1),
    raw fourth-moment average = 2.

Every 8m-unit control set contains both signs; its centered sum of squares
is at least 15m/2. Consequently V_OLS >= 75/(16*(10m-2)) > 0 on every
assignment. This family satisfies S5, local effects, constant effects, the
sharp null, v0>0 and PositiveOLS simultaneously. The heterogeneous family in
T8 separately has the S5 parameters (1/5,4,1,1,0) and raw fourth-moment
average 17. These are substantive populations with nonempty assignment spaces.

`scratch/Check.lean` imports only Defs and compiles a complete Regularity
instance with zero outcomes and growing positive arms, its sharp-null and
constant-effect hypotheses, and several concrete four-unit support, count,
table and difference checks. It does not use the Challenge stubs.
`scratch/exact_checks.py` independently uses rational arithmetic and verifies:

* T1 identities and table identification in all 5,208 vector/assignment cases
  with 2<=N<=6;
* both T2 statistics for repeated block sizes 1, 2 and 3;
* every stated T3 finite distribution and inclusive p-value;
* 80 T4 parameter cases, including equality and zero boundaries;
* all finite T8 witness formulas by complete enumeration of 45 assignments
  at m=1 and 4,845 at m=2;
* strict all-assignment positivity for the nonconstant sharp-null family at
  m=1,2, and a zero-variance assignment in the balanced binary family.

The exact results are saved in `scratch/exact-results.json`. These checks
support the statement audit; the Challenge proofs themselves are outside it.
