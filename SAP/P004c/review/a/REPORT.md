# Palomar statement audit — P004c

13 targets, 9 Challenge theorems:

| Verdict | Count | Targets |
| --- | ---: | --- |
| correct_whole | 7 | T31, T32, T33, T39, T40, T41, T42 |
| correct_restricted | 2 | T34, T44 |
| omission_ok | 4 | T35, T36, T37, T43 |
| restriction_inaccurate | 0 | |
| not_faithful | 0 | |
| vacuous | 0 | |
| false | 0 | |
| omission_questionable | 0 | |

No adverse finding. All severities are `none`. The seven whole and two
restricted decisions in the record agree with the blind comparison.
No step-2 verdict was changed after opening `record.json`.

## Restrictions checked

**T34:** The docstring correctly excludes the composed bandwidth rate and
vanishing-error conclusion, and excludes the eight-node realization and
the derivation of its cross sum −1/4. The retained final conjunct is only
scalar arithmetic, so it is not credited as a spatial counterexample.
Positive sample size/bandwidth and the zero extension of denominator
error on an empty treated arm are disclosed. The exact identities,
kernel bound and Bernoulli denominator rate remain meaningful.

**T44:** The docstring accurately states both changes to spacing:
`C_b*(1+s^2)` and a single eventual sample-size threshold for all radii.
It expressly disclaims sufficiency of the weaker radiuswise condition.
The metric premise is from Appendix C's standing setting. Positive-size,
well-defined finite unbiasedness and all four headline conclusions are
retained as declared.

## Accepted omissions

* **T35:** As described, a negation over arbitrary metric measurable
  spaces does not locate a counterexample in the canonical
  two-dimensional domain. Neither available negative row establishes a
  positive component of the printed proposition.
* **T36:** The described row concerns fitted-IPW coverage; the printed
  assertion uses Hajek. The canonical claim explicitly warns that the
  former's refutation does not refute the latter.
* **T37:** The described abstract real-table/weight counterexample
  exports no binary spatial realization, common outcome field, ordered
  distance regions or partition. It alone does not refute the specified
  printed interpretation. The empirical estimate and p-value are not
  mathematical targets.
* **T43:** The described negative row likewise supplies no counterexample
  in the canonical spatial domain. Finite oracle variance bounds do not
  prove the printed ordinary-limit coverage claims. A liminf bound
  would not establish existence of those limits either.

These omission assessments concern the evidence supplied in the permitted
files. The underlying declarations named in the record are not included;
their source proofs and exact exported types were not independently read.
No new refutation is credited merely from an architect's row name.

## Nonvacuity and mathematical checks

`reading.md` was saved before reading `claims.json`; `claim-stage.json`
was saved before reading `record.json`. All nine statements were expanded
through their SAP definitions, and relevant Mathlib definitions were
checked directly. Probability is a genuine normalized finite Bernoulli
law, pair conditioning is only used at distinct indices, and spatial
averages have positive finite mass and integrable outcomes wherever
needed. The finite supremum in T34 is nonempty and bounded. Standard
normal convergence uses Mathlib's actual Gaussian measure. Nondegeneracy
implies eventual strictly positive variance denominators.

`scratch/Check.lean` imports only `SAP.P004c.Defs`, uses no admitted
proofs, and checks concrete nonvacuity without invoking any Challenge
theorem. It checks two nonempty arms, an orthonormal matrix, bounded
tables and valid neighborhoods, nonzero finite kernel sums, normalized
weights, and a genuine spatial integral with a nonzero additive effect.
In the two-node example with p=1/2 and fixed outcomes (1,−1), direct
enumeration gives both HT and linearized Hajek variance equal to 2.

For a simultaneous asymptotic instance, take the N points (i,0),
0≤i<N, in the plane with counting measure, singleton nodes,
bands(d)={0}, and deterministic outcomes (−1)^i. Every circle is a
single point. Choose p=1/2, b=2, h(d)=0 and c(r)=2r+1. Locality and
radiuswise spacing hold. The node distances form a metric and
quadratic spacing holds with C_b=2 simultaneously for all radii.
NED holds with ψ=0, g=G=1 and exponent 5: every conditional
approximation error is zero. This does not make the estimators
degenerate: Var(HT)=4/N, and
N Var(linearHajek)=4(1−m_N²)≥3 for N≥2, where m_N is the mean
of the alternating outcomes. Thus T41, T42 and T44 have nondegenerate
instances with genuine averages. This sequence verification is a
mathematical construction; the finite instances above are Lean checked.

Bounded-degree dependency graphs support the two local-interference
Gaussian statements. For T44, size exponent greater than four and the
uniform quadratic ball bound permit approximation by bounded local
functions at radii N^a with 1/(2*exponent)<a<1/8; the normalized L2
approximation error vanishes and the resulting dependency graph has
degree O(N^(2a)). No conclusion is assumed as a hypothesis.
