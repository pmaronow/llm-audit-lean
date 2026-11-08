# Blind reading of SAP.P061a.T1–T5

Saved before opening either `claims.json` or `record.json`. Sources inspected: the
five Challenge statements and docstrings, `closure.json`, Defs Parts 1–6, and the
relevant declarations in WholeW1 and WholeW2. The generated closure helpers were
also printed by Lean (`scratch/ClosurePrint.lean`): they are only numeral
`NeZero`/`AtLeastTwo` proofs, together with the ordinary structure constructor and
mass projection. They impose no further statistical assumptions.

## Common notation, fully expanded

The following mathematical abbreviations are used below only to avoid repeating
the same expanded formula. They are not additional hypotheses.

* A design on a type Ω is a real function p:Ω→ℝ, with p(z)≥0, a summable family
  p, and unordered sum ∑z p(z)=1. In particular its positive-mass support is
  countable, even when Ω is not. An assignment is supported exactly when p(z)>0.
* P(B)=∑z 1[B(z)]p(z); E[f]=∑z p(z)f(z), both Mathlib real `tsum`s.
  A finite absolute mean means `Summable (z ↦ p(z)|f(z)|)`.
* Units are `Fin N` (integers 0,…,N−1). Responses y and exposures g are real
  functions of a unit and an assignment. Write π_i(e)=P(g_i=e),
  μ_i(e)=E[1[g_i=e]y_i]/π_i(e), M(e)=N⁻¹∑i μ_i(e), and
  T(e,e′)=M(e)−M(e′). Positive exposure means ∃c>0, ∀i, π_i(e)≥c.
  A targeted absolute moment at e means, for every i, the finite absolute mean
  of 1[g_i=e]y_i.
* The estimate at e is N⁻¹∑i 1[g_i(z)=e]y_i(z)/π_i(e); the contrast
  estimate is the estimate at e minus that at e′. Variance is
  E[(X−E[X])²], covariance E[(X−E[X])(Y−E[Y])].
* Independence of X,Y means P(X∈B,Y∈C)=P(X∈B)P(Y∈C) for every pair
  of predicates B,C. Mutual independence of an N-vector g means
  P(∀i,g_i∈B_i)=∏i P(g_i∈B_i) for every family of predicates B_i.
* Global stability means g_i(z)=g_i(z′) implies y_i(z)=y_i(z′), for all
  assignments; support stability asserts this only when both masses are positive.
* For a real vector z, z_{−i} is its restriction to the subtype of units j≠i.
  Write z^{i←e} for the vector equal to e at i and z elsewhere. On a feasible
  set S⊆ℝ^N, h_i(e,z)=y_i(z^{i←e}) if that vector belongs to S, and **0
  otherwise**. The raw direct average is A=N⁻¹∑i E[h_i(d,Z)−h_i(d′,Z)].
  Coordinate exposure on S is g_i(z)=z_i.
* For varying assignment types/designs, convergence in probability of X_n to a
  is: for every ε>0, P_n(|X_n−a|>ε)→0. Weak convergence to a real Borel
  measure L means E_n[f(X_n)]→∫f dL for every bounded continuous real
  function f. Translation of L by c is its pushforward under x↦x+c.

Real subtraction is not truncated. The sums over units are finite; sums over
assignments are unordered sums, not conditionally convergent ordered series.

## SAP.P061a.T1

Source: Challenge/Part1.lean:8–12; Defs/Part3.lean:12–61, with the common
definitions in Parts 1–2.

There exists a family of designs p_N on `{0,1,2}^N`, for **every** natural N,
whose mass at every vector is 3^(−N). Put g_i(z)=0 if z_i=0 and 1 otherwise,
and y_i(z)=the integer z_i regarded as real. Also let c(z)_i be the
`Fin 3` value 0 when z_i=0 and 1 otherwise. For every N>0 all of the
following hold:

1. The g_i are mutually independent in the all-predicates sense above.
   Every response is between 0 and 2, and depends only on its own raw coordinate.
   Exposures 1 and 0 are positive uniformly over the finite population.
2. For every i, P(z_i=1,g_i=1)/π_i(1)=1/2 and
   P(z_i=2,g_i=1)/π_i(1)=1/2.
3. T(1,0)=3/2. For every i,z, both
   y_i(z^{i←1})−y_i(z^{i←0}) and
   y_i(c(z)^{i←1})−y_i(c(z)^{i←0}) equal 1. Their respective
   expected population averages both equal 1. T(1,0)−1=1/2.
4. For every i, π_i(1)=2/3, π_i(0)=1/3, μ_i(1)=3/2,
   μ_i(0)=0, and μ_i(1)−μ_i(0)=3/2.
5. At every assignment the HT contrast estimate equals
   [3/(2N)]∑i z_i. Its mean is 3/2, its variance is 3/(2N), and for
   every real ε>0, P(|estimate−3/2|≥ε)≤3/(2Nε²).

The same family also has these properties: at N=2 there is **no** real
function H:ℝ²→ℝ with y_0(z)=H(g(z)) for all z. The vectors (1,0) and
(2,0) have equal exposures at **each** unit, but their responses at unit 0
are 1 and 2. Along N=n+1 the gap T−1 tends to 1/2 and does not tend to 0.
This is an existential construction, not a universal failure claim. The
docstring explicitly identifies the raw-assignment-coordinate interpretation as
the reading contradicted.

Junk-value audit: all assignment types are finite; means and second moments
exist. Every denominator involving N is inside N>0, every target cell has
explicit positive probability, and ε²>0 in the tail inequality. N=0 is
allowed only for constructing the normalized empty-vector design; no
`VersionFacts` is required there. The obstruction uses the ordinary finite
vectors at N=2. Finite numeral casts are exact (no arbitrary integer truncation).
No square root, real power, partial function, infimum, supremum, integral, or
limsup/liminf occurs in this statement. Real `tsum`'s nonsummable default is
unreachable here. Finite-vector/function updates are total.

## SAP.P061a.T2

Source: Challenge/Part1.lean:14–18; Defs/Part4.lean:11–58 and Parts 1–2.

Let an assignment be a pair (a,b) of bits. At unit 0, own bit is a and partner
bit is b; at unit 1 these roles reverse. Exposure is own+2·partner and the
response is own. The theorem is the conjunction of two existential assertions.

First, there exists a design on the four bit pairs with mass 1/4 everywhere.
For this design:

* Each unit has each exposure 0,1,2,3 with probability 1/4; μ_i(1)=1,
  μ_i(0)=0, T(1,0)=1; responses are globally and support stable, and
  target exposures 1 and 0 are positive.
* The full exposure image is exactly {(0,0),(2,1),(1,2),(3,3)}, and the
  four inputs (0,0),(0,1),(1,0),(1,1) map to these respective outputs.
* For **every** raw assignment and either chosen unit, the two exposure
  vectors formed by replacing that unit's exposure by 1 and by 0 are not
  both in this exposure image. This does not say each individual hybrid is
  outside the image.
* A vector belongs to the raw bit domain exactly when both entries are 0 or
  1. For replacement in exposure coordinate 0, either replacement yields a
  raw bit vector exactly when a=0; for replacement in coordinate 1 this holds
  exactly when b=0. Thus both replacements are raw bit vectors with probability
  1/2 for each chosen unit.

Second, **for every** natural K>0 there exists a design on K bit pairs
with mass ∏k(1/4)=4^(−K), hence independent uniform pairs. Index the 2K
units by the canonical equivalence `Fin K × Fin 2 ≃ Fin (K*2)`; exposures
and responses use the corresponding pair and member, as above. Every unit
has every exposure with probability 1/4, μ_i(1)=1, μ_i(0)=0,
T(1,0)=1, and global stability holds. For every unit i and assignment z,
the two coordinate replacements in the **entire** exposure vector are not
both in its exposure image. For every i their joint membership in the entire
raw binary cube has probability (1/2)(1/4)^(K−1).

The image tests are genuine existential quantification over raw assignments;
they do not evaluate an outcome at an infeasible argument. The docstring
claims domain failures of two specified hybrid interpretations, not a numerical
inequality between their outcomes.

Junk-value audit: all designs have finite domains, target probabilities are
1/4, and the population means use N=2 or 2K>0. K−1 is natural truncated
subtraction, but K>0 makes it ordinary predecessor here. Finite products and
function updates are total. `Fin` values cast into ℝ as 0,1 or 0,…,3.
No nonsummability, division by zero, infinite `toReal`, extrema, square roots,
real powers, or default extension outside a domain is used. Empty K is
excluded from the repeated-pair assertions.

## SAP.P061a.T3

Source: Challenge/Part1.lean:20–23; Defs/Part5.lean:11–36 and Part1.

The theorem is a conjunction of **two universally quantified implications**.

First, for every N, feasible set S⊆ℝ^N, normalized nonnegative summable
atomic design on S, real response schedule on S, and real d,d′, assume:

1. N>0;
2. for every unit i, P(Z_i=d)>0 and P(Z_i=d′)>0;
3. for every i, both 1[Z_i=d]y_i and 1[Z_i=d′]y_i have finite
   absolute means;
4. for every i, Z_i is independent of the **whole** other-coordinate vector.

Then (a) for every i and e∈{d,d′}, and every other-coordinate vector w with
P(Z_{−i}=w)>0, there exists a positive-mass z∈S equal to (e,w);
(b) for every such i,e, h_i(e,Z) has a finite absolute mean and
μ_i(e)=E[h_i(e,Z)]; and (c) T(d,d′)=N⁻¹∑i E[h_i(d,Z)−h_i(d′,Z)].
The feasibility in (a) is a conclusion, not an assumed rectangular domain.

Second, for every type Ω, N, normalized atomic design on Ω, real exposures
g_i and responses y_i on Ω, functions H_i:ℝ^N→ℝ, and real d,d′,
assume N>0, positive target exposure probabilities for every i, the two
targeted absolute moments, independence of g_i from the **whole** vector
g_{−i} for every i, and this consistency condition: whenever p(z)>0 and
g_i(z)∈{d,d′}, y_i(z)=H_i(g(z)). Then for every i and
e∈{d,d′}, H_i(g(z)^{i←e}) has a finite absolute mean and
μ_i(e)=E[H_i(g(Z)^{i←e})]. The population contrast is the average
expectation of H_i(g(Z)^{i←d})−H_i(g(Z)^{i←d′}). Consistency
is required only on supported target cells, not everywhere. H is total on
all real exposure vectors, and no separate exposure-vector feasibility test
is made in this second part.

Junk-value audit: all specified conditioning cells are strictly positive;
N>0; targeted absolute means are hypotheses. Means of each hybrid are
proved absolutely finite as part of the conclusion. The raw hybrid has a
zero default outside S; (a), atomicity and independence ensure this cannot
contribute at positive-mass assignments. Values at mass-zero assignments
also contribute zero. In the second part H has arbitrary off-support values,
but independence ensures inserted target exposure vectors with positive
mass in the other-coordinate marginal occur in supported target cells.
No hidden countability of Ω is assumed; countable support follows from
the design. Empty S cannot carry a normalized design; N=0 is explicitly
excluded. If d=d′ the identity is the legitimate zero contrast. No infimum,
supremum, root, real power, Bochner integral or extended-real conversion
occurs. Arbitrary unguarded `tsum` values exist definitionally but are not
used as ordinary means without the stated or concluded summability.

## SAP.P061a.T4

Source: Challenge/Part1.lean:25–33; WholeW1.lean:13–89;
Part6.lean:11–37 and Parts 1–2.

There exists a family of normalized designs for every natural m on
`({0,1}²)^(m^8)`. Put K=m^8, N=2K, a_m=1/m for m≥2 and 0 otherwise.
Every assignment z has mass
∏k [(1+a_m)/4 if its pair agrees, (1−a_m)/4 otherwise]. At unit i,
the response is 1+a_m times its partner's bit **added to 1**, that is
y_i=1+a_m z_partner(i); exposure is its own bit. Replacing an own bit
changes only that member of its pair. Write T_m for the conditional-exposure
contrast, A_m for the average expected raw own-bit-replacement difference,
X_m for its HT contrast estimate, s_m=√E[(X_m−E X_m)²], and
V_m=8+16/m+14/m²+2/m³−4/m⁴.

For every m≥2 all these clauses hold:

* Every assignment has positive mass. Each unit's two own-bit cells have
  probability 1/2. Every response lies in [1,3/2]. A unit's own bit is
  independent of the vector of all **other pairs**. The covariance of the two
  bits in any one pair is 1/(4m).
* A_m=0. Every μ_i(1)=1+(1/m)(1+1/m)/2 and
  μ_i(0)=1+(1/m)(1−1/m)/2. T_m=1/m²=E X_m.
* Var(X_m)=V_m/(4m⁸); 8≤V_m<20; s_m>0;
  ((1/m²)/s_m)²=4m⁴/V_m≥m⁴/5.
* P(|X_m−1/m²|≤5s_m)≥24/25. If m≥5,
  P(|X_m|≤5s_m)≤4 Var(X_m)/(1/m²)²
  =V_m/m⁴≤20/m⁴.
* Flattening the pairs to their literal binary vector is bijective. The partner
  operation has no fixed points and is an involution. Own and partner exposures
  are the corresponding literal coordinates, and paired replacement flattens
  to literal single-coordinate replacement.
* For distinct units, assignment dependence means failure of the all-events
  pairwise independence identity. This edge relation holds **exactly** for
  partner units. Interference means there exist two assignments agreeing at all
  units other than j but changing y_i; with i≠j, this too holds **exactly**
  for j=partner(i). Each unit has degree 1 in each relation and each maximum
  degree is 1. Degree is the cardinality of the filtered finite set of adjacent
  units; maximum degree is the `Finset.sup` in ℕ.
* V_m=8(1+1/m)(1+1/m)+(6+2/m)(1/m)²−4(1/m)⁴.
  Exactly (T_m−A_m)(2m⁸)^(1/4)=2^(1/4), with Mathlib real powers.

All limits are along m=n+2 as n→∞: T_m−A_m→0;
(2m⁸)Var(X_m)→4; ((T_m−A_m)/s_m)²→+∞;
P(|X_m−A_m|≤5s_m)→0; (T_m−A_m)/s_m→+∞;
and s_m√(2m⁸)→2. The existential quantifier scopes over the single family
used in every finite and limiting clause. The assertions do not concern every
integer population size, only the stated N=2m⁸ sequence.

Junk-value audit: m=0,1 are present only in the definition of the family and
its mass formula, using a_m=0; none of the finite facts or limit evaluations
uses these m. On m≥2, all 1/m factors are ordinary reciprocals; all cell
probabilities are 1/2; N>0; s_m>0 is explicit. Every assignment domain is
finite, so all moments exist. Real square roots are applied to a nonnegative
variance or a positive population size; the explicit positive variance removes
the zero-root issue. All real-power bases in the claimed identity are positive.
`Finset.sup` would be 0 on the empty set, but these populations are nonempty.
Natural powers and products cannot overflow. No extended-real conversion,
empty/unbounded real extrema, limsup/liminf, nonintegrable integral or partial
function default is involved. Tending to `atTop` is divergence to +∞ as an
order-filter statement, not a real-valued infinity convention.

## SAP.P061a.T5

Source: Challenge/Part1.lean:35–47; WholeW2.lean:13–178, together with
the common definitions and PairInferenceFacts described above. It is a
conjunction of four substantive assertions plus a nonatomic-law observation.

### Population inference

For **every** sequence S_n⊆ℝ^(n+1), normalized atomic designs p_n on
S_n, response schedules y_n, fixed real d,d′, real statistics X_n and
estimated scales ŝ_n on S_n, deterministic real s_n, and probability measure
L on ℝ, impose the following domain hypotheses at every n:

* each unit has positive probability for both coordinate values d,d′;
* both targeted absolute response moments exist;
* for every positive-mass assignment, both own-coordinate replacements
  belong to S_n;
* each hybrid **difference** h_i(d,Z)−h_i(d′,Z) has a finite absolute mean.

Also assume s_n>0, weak convergence (X_n−T_n)/s_n⇒L, and
ŝ_n/s_n→1 in probability, where T_n is the actual coordinate-exposure
conditional contrast and A_n is the actual expected hybrid-difference average.
The conclusion first says P(ŝ_n≤0)→0. It then says:

1. If |T_n−A_n|/s_n→0, both (X_n−A_n)/ŝ_n and
   (X_n−T_n)/ŝ_n converge weakly to L. For **every fixed** q>0 with
   L({−q})=L({q})=0, both actual interval-event probabilities
   P(|X_n−A_n|≤qŝ_n) and P(|X_n−T_n|≤qŝ_n) tend to
   the real value L([−q,q]).
2. For **every** real c≠0, if (T_n−A_n)/s_n→c, then
   (X_n−A_n)/ŝ_n converges weakly to the translate of L by +c.

The hypotheses do not stipulate unbiasedness, a specific estimator, normality,
separate first moments for the two hybrids, or pointwise positivity of ŝ_n.

### Neighborhood bound

For **every** N, feasible S⊆ℝ^N, normalized atomic design p, real
responses y, real targets d,d′, finite sets H_i of units, finite sets K_i
of real configurations on H_i, sets C_i of configurations, and real functions
f_i(e,x), assume:

* N>0; i∉H_i; K_i is nonempty and K_i⊆C_i;
* the restriction x_i(z)=z|H_i belongs to K_i whenever p(z)>0;
* for every i and e∈{d,d′}, the image f_i(e,C_i) has an attained real
  least value and an attained real greatest value;
* both target own-coordinate cells have positive probability;
* both hybrids are feasible at every positive-mass assignment;
* h_i(e,z)=f_i(e,x_i(z)) for supported z and e∈{d,d′}.

Let P_i(x)=P(x_i(Z)=x) and
Q_i^e(x)=P(Z_i=e,x_i(Z)=x)/P(Z_i=e). Define
R_i(e)=sup f_i(e,C_i)−inf f_i(e,C_i), and TV on K_i by
TV(Q,P)=(1/2)∑x∈K_i |Q(x)−P(x)|. The conclusion is exactly

|T−A| ≤ N⁻¹∑i [R_i(d)TV(Q_i^d,P_i)+R_i(d′)TV(Q_i^{d′},P_i)].

Only neighborhood supports are required to be finite; the feasible set,
coordinate alphabets and global positive-mass support need not be finite.
The range domain C_i can be larger than K_i. Integrability of the relevant
responses follows from their finite supported local representation.

### Rate sufficiency and example

For every four real sequences T,A,b,s, if s_n>0, |T_n−A_n|≤b_n
for every n, and b_n/s_n→0, then |T_n−A_n|/s_n→0.

There also exists the exact correlated-pair family with the product masses and
every finite `PairInferenceFacts` clause spelled out in the T4 section above.
Along m=n+2, its raw target gap tends to 0, its **absolute** gap divided by
the exact standard deviation tends to +∞, and its direct-effect interval
coverage at radius 5 times that standard deviation tends to 0. Unlike T4,
this conjunct does not separately assert the flattening bijection, graph-degree
identities or real-power normalization.

Finally, for every measure L whose singleton sets have zero measure, and
every real q, L({−q})=L({q})=0. This conjunct does not itself require L
to be a probability measure.

Junk-value audit: every population in inference has size n+1>0, and the
local bound separately assumes N>0. Every conditioning probability is positive.
The `hybridResponse` zero default outside S affects at most mass-zero
assignments, by explicit feasibility hypotheses. Targeted and hybrid-difference
means in inference are absolutely finite by hypothesis; separate hybrid means
are neither used nor presumed finite. The local bound's finite supported
representation supplies the needed absolute means. The range uses Mathlib
conditionally complete real `sSup` and `sInf`; the attained finite extrema
hypotheses exclude empty images and unbounded images, so their junk values
are excluded. K_i is explicitly nonempty. H_i may be empty, in which case
its configuration type has exactly one empty function and is meaningful.
Studentization uses total real division: it is 0 on ŝ_n=0 and reverses sign
when ŝ_n<0. Consistency and positive s_n imply that the probability of
ŝ_n≤0 tends to 0; coverage uses the actual unstandardized event and the
conclusion includes that negligible-event fact. The limiting-law integral is
of a bounded continuous function against a probability measure, hence is a
finite ordinary integral. L([−q,q]).toReal is only used for a probability
measure, so the value is never infinity. The translated map is continuous
and total. No `Real.log`, unguarded `rpow`, truncated subtraction, limsup or
liminf occurs beyond the finite pair-example conventions already audited for
T4. The final singleton assertion uses no `toReal` and tolerates infinite
measures. No claim is made about coverage at atoms of L at ±q.
