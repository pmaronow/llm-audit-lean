# Blind reading

This file was written before opening `claims.json` or `record.json`. Sources read:
`closure.json`, both import aggregators, `Challenge/Part1.lean`, and all three
`Defs/Part*.lean` files. The generated declarations in the closure were also
printed with Lean in `scratch/Blind.lean` (successful compilation). No Solution
or Comparator source was read.

## SAP.P035.T1

The declaration at `SAP/P035/Challenge/Part1.lean:12` asserts the closed
proposition `T1Statement`; it has no parameters or hypotheses. Its docstring
describes two hypothetical finite worlds reproducing six released frequencies
but having different campaign effects. It explicitly disclaims a decision about
the initiative's actual effect and specifies raw enrollment mixture weights.

### All objects and definitions

`Year` is the inductive three-element type with constructors `y2012`, `y2014`,
and `y2015`. Write these as 2012, 2014, and 2015. `years` is the finite set of
all three. `PorchAssignment`, `Campaign`, and `Choice` are each the ordinary
two-element type `Bool`. Write porch assignment as z, campaign presence as a,
and outcome as b, with false = 0 and true = 1 when discussing their meaning.
For z, true means the implemented Obama porch package and false the pooled
comparison package; for a, true means initiative present; for b, true means
raisins and false means candy. These are labels on total Boolean functions,
not additional mathematical assumptions about actual children.

`fruitValue(b)` is the rational 1 if b is true and 0 otherwise. `bit(b)` is the
natural number 1 if b is true and 0 otherwise. `PotentialOutcome` is the type
of all total functions Y : Year -> Bool -> Bool -> N -> Bool. Its arguments
are (year, porch, campaign, latent type). There are no other children's
assignments among the arguments. Observed outcomes always evaluate a = true.
The common design is defined below, independently of Y.

Here are all the fixed tables, with columns ordered (false, true):

| year | enrolled n | complete cases m | fruit counts k | latent size N | thresholds t |
| --- | --- | --- | --- | --- | --- |
| 2012 | (69,96) | (69,95) | (14,24) | 6555 | (1330,1656) |
| 2014 | (265,157) | (265,157) | (58,37) | 41605 | (9106,9805) |
| 2015 | (444,192) | (444,192) | (113,61) | 7104 | (1808,2257) |

`releasedFrequency(y,z)` is q_yz = (k_yz : Q)/(m_yz : Q).
`reducedDenominator(y,z)` is d_yz = m_yz / gcd(k_yz,m_yz), where this division
and gcd are natural-number operations. `latentSize` and `threshold` are N
and t in the table. `latentPopulation(y)` is the finite interval
S_y = {r in N : 1 <= r <= N_y} (`Finset.Icc`).

For any f : N -> Q, `uniformMean(y,f)` is
(sum over r in S_y of f(r))/(N_y : Q).
`outcomeMean(Y,y,z,a)` is (sum over S_y of 1{Y(y,z,a,r)=true})/N_y,
with the indicator taking rational values. `successCount(Y,y,z)` is the
natural cardinality of {r in S_y : Y(y,z,true,r)=true}.
`campaignDifference(Y,y,z,r)` is the rational difference
1{Y(y,z,true,r)=true} - 1{Y(y,z,false,r)=true}.
`campaignMean(Y,y,z)` is its sum over S_y divided by N_y.

`exactEffect(y)` is the rational number e_y, respectively
326/6555, 699/41605, and 449/7104.

The fixed worlds are Boolean-valued threshold functions, with inequalities
decided by Lean's ordinary decidable order on N:

* D(y,z,a,r) = 1{r <= t_y0 + bit(z)*(t_y1 - t_y0)};
* C(y,z,a,r) = 1{r <= t_y0 + bit(a)*bit(z)*(t_y1 - t_y0)}.

Here threshold subtraction is natural truncated subtraction. Thus D ignores
a; C agrees with D at a = true, and has threshold t_y0 at a = false for
both z. The formulas also define outcomes at r = 0 and above N_y.

Put n_y = n_y0+n_y1. `yearMass(y)` is p_y = n_y/1223 (rational),
`assignmentMass(y,z)` is alpha_yz = n_yz/n_y (rational),
`conditionalMass(y,z,r)` is alpha_yz/N_y, and
`jointMass(y,z,r)` is p_y*alpha_yz/N_y. The last two expressions are constant
in r; their use as masses is restricted to S_y by the sums. They are NOT
zero-extended probability mass functions on all N. Their finite support,
as used by the observable and the mixture, is explicitly S_y.

For an arbitrary rational function w : Year -> Bool -> N -> Q,
`observedLawWith(Y,w)` is the function (y,z,b) mapping to
sum over r in S_y of w(y,z,r)*1{Y(y,z,true,r)=b}.
`observedRealLawWith` is exactly this expression over R with
w : Year -> Bool -> N -> R. No positivity or normalization is imposed on w.
`observedLaw(Y)` is the rational function obtained by w = jointMass.
`Calibrated(Y)` means forall y : Year, forall z : Bool,
outcomeMean(Y,y,z,true) = q_yz. This calibrates population averages in the
hypothetical world to the supplied complete-case frequencies; it is not an
assertion that those frequencies are known true population probabilities.

`overallCampaignEffect(Y)` is the rational number
sum over the three years of
p_y * (alpha_y0*campaignMean(Y,y,false) +
       alpha_y1*campaignMean(Y,y,true)).

`CampaignIdentified` is the proposition: for every U : PotentialOutcome,
then every V : PotentialOutcome, if Calibrated(U), then if Calibrated(V),
then if observedLaw(U) = observedLaw(V), then for every y : Year,
campaignMean(U,y,true) = campaignMean(V,y,true).
The identified parameter here is the vector of campaign means at porch true,
not the collection of all individual potential outcomes or all porch arms.

The generated closure declarations have no hidden modeling content.
`Year.casesOn` and `Year.rec` perform the three-constructor case split;
`Year.ctorIdx` returns 0,1,2; the constructors are the three elements above.
`enrolled.match_1` is the exhaustive six-case (year,Boolean) eliminator.
`instDecidableEqYear` compares constructor indices; its `_proof_1` proves
equal indices imply equal years, and `_proof_2` proves unequal indices
preclude equality. `instReprYear.repr.match_1` is the three-case eliminator
for representation. These implement ordinary finite sets and equality.

### Conclusion and quantifiers

T1 is the conjunction of all the following assertions. Each listed universal
quantifier is local to its own conjunct; no data are chosen under a hypothesis.
Natural r and s range over all N unless a finite sum restricts them to S_y.

1. For every y, N_y = lcm(d_y0,d_y1) in N.
2. For every y, 0 < N_y, t_y0 <= t_y1, and t_y1 <= N_y.
3. For every y and z, (t_yz : Q) = (N_y : Q)*q_yz.
4. For every y,z,r, alpha_yz/N_y equals
   (sum over s in S_y of alpha_yz/N_y) *
   (alpha_y0/N_y + alpha_y1/N_y). This is the factorization of the
   within-year mass of (assignment,latent type) on its finite support.
5. For every y,z,r, p_y*alpha_yz/N_y >= 0, and the sum over all years and
   both arms and r in S_y of these joint masses is 1.
6. For every y,z,r, C(y,z,true,r) = D(y,z,true,r).
7. For every y,z, successCount(D,y,z) = t_yz,
   successCount(C,y,z) = t_yz, and successCount(D,y,z)/N_y = q_yz.
8. Both D and C are calibrated, in the fully quantified sense above.
9. For every y, outcomeMean(D,y,true,true) -
   outcomeMean(D,y,false,true) = e_y, and this difference is positive.
10. For every y,z,r, campaignDifference(D,y,z,r) = 0.
11. For every y,r, campaignDifference(C,y,false,r) = 0.
12. For every y, campaignMean(C,y,true) = e_y,
    e_y = ((t_y1 - t_y0 : N) : Q)/N_y, and campaignMean(C,y,true) > 0.
13. overallCampaignEffect(D) = 0.
14. overallCampaignEffect(C) equals
    (96/1223)*(326/6555) + (157/1223)*(699/41605) +
    (192/1223)*(449/7104), equals 83755728/5240292055, and is positive.
15. For every rational weight function w, observedLawWith(D,w) =
    observedLawWith(C,w), as functions of every y,z,b.
16. For every real weight function w, observedRealLawWith(D,w) =
    observedRealLawWith(C,w), as functions of every y,z,b.
17. Not CampaignIdentified, with that proposition unfolded above.
18. There does not exist a total function
    f : (Year -> Bool -> Bool -> Q) -> Q such that, for every
    Y : PotentialOutcome, if Y is calibrated, then
    f(observedLaw(Y)) = overallCampaignEffect(Y).

### Junk values and nonemptiness

* Rational division is total and would give zero for division by zero.
  This is not used: N is 6555,41605,7104; complete-case denominators are
  69,95,265,157,444,192; arm totals are 165,422,636; and 1223 is positive.
  The explicit effect denominators are also positive.
* Natural division in reducedDenominator is integer division, with value 0
  for denominator zero. Each gcd is positive and divides the positive
  complete-case count, so neither zero division nor rounding changes it.
* Natural subtraction in D, C, and conjunct 12 saturates at zero. The actual
  threshold differences are 326,699,449, so it agrees with integer
  subtraction. Their ordering is also explicitly asserted in conjunct 2.
* Rational subtraction in campaignDifference and arm contrasts is ordinary
  signed subtraction, not truncated subtraction. Casts from N to Q preserve
  these nonnegative counts exactly; there are no rounding conversions.
* Every S_y is a nonempty finite interval of cardinality N_y. Finite sums
  have no convergence or integrability precondition. Year and Bool are
  nonempty; the potential-outcome function type is inhabited, for example
  by the constantly false function. Universal natural indices include 0,
  and both threshold worlds give true at 0, but 0 is excluded from all means.
* Mass functions are nonzero outside S_y if viewed as functions on N, but
  all probability sums and observables explicitly use S_y. Thus no infinite
  sum of those constant values is asserted to be a probability distribution.
* All matching and outcome functions are total and exhaustive. There is no
  partial-function default, choice of element from an empty set, infimum,
  supremum, liminf/limsup, extended-real conversion, logarithm, square root,
  real power, Bochner integral, or non-integrable expectation. Arbitrary real
  weights occur only in finite sums of real numbers.

## SAP.P035.T2

The declaration at `SAP/P035/Challenge/Part1.lean:22` asserts the closed
proposition `T2Statement`; it has no parameters or hypotheses. The docstring
claims mathematical nonidentification and possible full campaign enablement
of the porch contrast. It explicitly omits an empirical estimate of increased
raisin choice and an instruction to change campaign wording. Campaign means
initiative presence, with no separate health-message mediator.

### All objects and definitions

Year is the ordinary three-element inductive type (2012,2014,2015).
PorchAssignment, Campaign, and Choice are Bool, respectively coding the
implemented porch versus pooled comparison, initiative presence versus
absence, and raisins versus candy. `fruitValue` is the rational indicator
of true. A potential outcome is any total Boolean function
Y : Year -> Bool -> Bool -> N -> Bool, with arguments (y,z,a,r). Its locality
excludes other children's assignments; observation evaluates a = true.

The complete-case frequency q_yz is the rational quotient of the following
fruit count and complete-case count. These are fixed inputs, not quantified
sample estimates. Enrollment counts determine a separate fixed design.

| year | enrollment (false,true) | complete cases (false,true) | fruit counts (false,true) | N_y | e_y |
| --- | --- | --- | --- | --- | --- |
| 2012 | (69,96) | (69,95) | (14,24) | 6555 | 326/6555 |
| 2014 | (265,157) | (265,157) | (58,37) | 41605 | 699/41605 |
| 2015 | (444,192) | (444,192) | (113,61) | 7104 | 449/7104 |

`enrolled`, `completeCases`, `fruitCounts`, `latentSize`, and `exactEffect`
are exactly these tables. `releasedFrequency` is q_yz = k_yz/m_yz in Q.
`latentPopulation(y)` is S_y = {r in N : 1 <= r <= N_y}, a finite interval.
`uniformMean(y,f)` is (sum over r in S_y of f(r))/(N_y : Q).
`outcomeMean(Y,y,z,a)` is the uniform mean of 1{Y(y,z,a,r)=true}.
`campaignDifference(Y,y,z,r)` is the rational difference
1{Y(y,z,true,r)=true} - 1{Y(y,z,false,r)=true}, and
`campaignMean(Y,y,z)` is its sum over S_y divided by N_y.

Writing n_y for the sum of the two enrollment counts, `yearMass(y)` is
p_y = n_y/1223, `assignmentMass(y,z)` is alpha_yz = n_yz/n_y,
`conditionalMass(y,z,r)` is alpha_yz/N_y, and `jointMass(y,z,r)` is
p_y*alpha_yz/N_y, all in Q. The masses are used only on S_y.
`observedLawWith(Y,w)` takes (y,z,b) to
sum over r in S_y of w(y,z,r)*1{Y(y,z,true,r)=b}, with rational w.
`observedLaw(Y)` is this function at w = jointMass. Thus it is the
joint finite mass table of year, porch, and observed choice in the same
independent design for all Y, with the initiative always present.

`Calibrated(Y)` means forall y, forall z,
outcomeMean(Y,y,z,true) = q_yz.
`CampaignIdentified` means forall U : PotentialOutcome,
forall V : PotentialOutcome, Calibrated(U) -> Calibrated(V) ->
observedLaw(U) = observedLaw(V) -> forall y,
campaignMean(U,y,true) = campaignMean(V,y,true).

The generated closure declarations `Year.casesOn` and `Year.rec` are the
ordinary three-way eliminators, and `Year.y2012`, `Year.y2014`, and
`Year.y2015` are its constructors. `enrolled.match_1` exhaustively selects
one of the six year/arm cases. `instReprYear.repr.match_1` is the three-way
representation match. They add no assumptions or modeling data.

### Conclusion and quantifiers

T2 is the conjunction of the following two assertions:

1. There exists U : PotentialOutcome, then exists V : PotentialOutcome,
   such that ALL of the following hold jointly:
   * For every year and porch, both U and V have observed uniform mean q_yz.
   * For every y,z,b, their finite observed masses defined above agree.
   * For every y, then z, then r in all N, the campaign indicator difference
     for U is zero.
   * For every y, campaignMean(V,y,true) > 0,
     campaignMean(V,y,true) = q_y,true - q_y,false, and
     campaignMean(V,y,true) = e_y.
   * For every y, then r in all N, V(y,true,false,r) = V(y,false,false,r).
     Thus, without the initiative, even each individual's porch contrast is
     zero, not merely its average. The treated-arm campaign mean equals the
     entire observed porch contrast. The statement does not separately say
     V's campaign effect is zero at each untreated individual.
2. Not CampaignIdentified, with all quantifiers and implications as above.
   This nonidentification is for year-specific campaign means under porch
   true. T2 does not explicitly state nonidentification of an overall mixture
   effect, individual effects, or effects under every porch assignment.

The same pair U,V is required to meet every clause in item 1. Item 2 is a
separate closed conjunct and follows from different treated campaign means
in that pair. The existential conditions grant consistency and the fixed
within-year independent design through the definitions. They say that some
worlds exist, not that the realized initiative has a known positive effect.

### Junk values and nonemptiness

* Every rational denominator is positive: complete-case sizes
  69,95,265,157,444,192; latent sizes 6555,41605,7104; year enrollment
  totals 165,422,636; and 1223. The explicit e_y denominators are likewise
  positive. Totalized rational zero division is not used.
* No reducedDenominator, threshold, bit, D, C, or natural subtraction occurs
  in T2's dependency closure. All effect subtraction is signed rational
  subtraction. Natural additions and casts to Q preserve the counts exactly.
* S_y is nonempty of cardinality N_y, and Year, Bool, N, and the potential
  outcome function type are inhabited. Every sum is finite. The universally
  quantified r includes 0 and types outside S_y, but observed masses and
  means never use those values.
* conditionalMass and jointMass are not zero outside S_y; their probability
  interpretation is on the explicitly restricted finite support. There is
  no infinite mass sum, implicit integrability assumption, or empty average.
* All functions are total; exhaustive matching introduces no default value.
  There is no real log/sqrt/rpow, integral, infinite extended-real value,
  toReal, infimum/supremum, or limsup/liminf in this closure.

Blind-reading verification next: construct the candidate finite pair D,C
and verify calibration and positive campaign effects independently, then
compare these closed statements with the as-yet unread canonical claims.
