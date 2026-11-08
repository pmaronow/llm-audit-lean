# Blind reading of T12–T16

Saved before opening claims.json or record.json. Sources read: the five docstrings and statements in SAP/P061b/Challenge/Part1.lean; every declaration listed in closure.json; SAP/P061b/Defs/Part1.lean:9–75, Part2.lean:9–56, Part3.lean:9–91, and Part4.lean:10–17. scratch/ClosureTypes.lean successfully checks all 56 distinct closure declarations, including the generated proof declarations. These generated declarations certify finite numeral instances, the two version choices, and the nonnegativity, summability, and normalization of the explicit designs. They do not add statistical assumptions.

## SAP.P061b.T12

### Objects and fully expanded notation

An assignment space Ω is any Lean Type (not supplied with a measurable structure). A design D is a function p : Ω → ℝ with p(z) ≥ 0 for every z, Summable p, and ∑' z, p(z) = 1. Here Summable f means that the net of finite partial sums of f converges to some real number; ∑' is Mathlib's unconditional real sum. Thus the distribution is atomic, even if Ω itself is uncountable. The constructor AtomicDesign.mk and projection AtomicDesign.p introduce no further conditions. N is a natural number; units are i : Fin N, namely integers 0 ≤ i < N. Schedules g and y are arbitrary deterministic functions Fin N → Ω → ℝ.

For any predicate A on Ω, write P_D(A) = ∑' z, if A(z) then p(z) else 0. For any real function X, write E_D(X) = ∑' z, p(z)X(z). The exposure probability is π_D(i,d) = P_D(g(i,z)=d). Define

* m_D(i,d) = E_D(z ↦ if g(i,z)=d then y(i,z) else 0) / π_D(i,d);
* M_D(d) = ((N:ℝ)⁻¹) ∑ i:Fin N, m_D(i,d);
* c_D(i,d,e) = m_D(i,d) − m_D(i,e);
* C_D(d,e) = M_D(d) − M_D(e).

These are exactly exposureMean, averageExposureMean, unitContrast, and averageContrast with every SAP operation replaced by real arithmetic, finite sums, and unconditional sums.

Global stability means: for every i and every z,w in Ω, g(i,z)=g(i,w) implies y(i,z)=y(i,w). No restriction to positive-mass assignments occurs.

### Quantifiers, hypotheses, and conclusions

The statement is the conjunction of the following seven assertions.

1. For every Ω,N,D,g,y and h : Fin N → ℝ → ℝ, if y(i,z)=h(i,g(i,z)) for every i,z, then for every pair of real exposures d,e, if N>0 and π_D(i,d)>0 and π_D(i,e)>0 for every i, then for every i, m_D(i,d)=h(i,d), m_D(i,e)=h(i,e), and c_D(i,d,e)=h(i,d)−h(i,e); also C_D(d,e)=((N:ℝ)⁻¹)∑ i, (h(i,d)−h(i,e)). The same h is fixed before d and e are selected.
2. For every Ω,N and two designs D,D' on the same Ω and the same schedules g,y, global stability implies: for every d,e, if N>0 and every unit has positive probability for both exposures under both designs, then m_D(i,d)=m_D'(i,d) and m_D(i,e)=m_D'(i,e) for every i, and C_D(d,e)=C_D'(d,e).
3. For every Ω,N,D,g,y, global stability implies: for every i,d with π_D(i,d)>0 and every z with g(i,z)=d, m_D(i,d)=y(i,z). The last z need not have positive mass; this is genuinely a global statement.
4. In the concrete household below, g=y=housemate assignment is globally stable.
5. For every atomic design on that household, if both exposures 1 and 0 have positive probability for both units, then C_D(1,0)=1 for g=y=housemate assignment.
6. The same C_D(1,0)=1 for the both-or-neither design.
7. The same C_D(1,0)=1 for the independent design.

The household is Ω=Fin 2 × Fin 2, the four pairs (a,b) with a,b∈{0,1}, and N=2. For i=0, housemate assignment is the real cast of b; for i=1, it is the real cast of a. Both-or-neither assigns mass 1/2 to (0,0),(1,1) and zero to the other pairs. Independent household assigns reciprocal card(Ω)=1/4 to each of the four pairs. The closure also contains finite-instance proofs generated at the definitions of oneTreated and ownAssignment; these just supply numeral instances and carry no extra mathematical assertion into T12.

### Junk conventions and their effect

Real division and inversion are total: a/0=0 and 0⁻¹=0. Every conditional mean asserted in the general clauses has an explicit positive denominator. The concrete designs have exposure margins 1/2; the universal household clause explicitly assumes positivity. Population averages in the general clauses have N>0; concrete averages have N=2. The pointwise clause has no average and uses an actual i:Fin N. There is therefore no use of a zero denominator in an asserted identity.

For a non-summable real family, Mathlib's ∑' returns 0. Event sums are summable by domination by the normalized nonnegative p. No first moment is separately assumed here, but global stability, or the factorization through h in clause 1, makes y constant on each relevant exposure cell. Its weighted cell sum is then a constant times a summable subfamily of p, so the relevant moments exist. Arbitrary behavior on other exposure cells is immaterial. Household sums are finite. Empty Ω cannot admit such a design, since its total sum would be 0 rather than 1. N=0 is excluded wherever an average conclusion is used. Finite numeral casts are exact; Fin literals use their usual modular interpretation but every displayed literal is within the intended bound. No truncated subtraction, logarithm, square root, real power, integral, toReal, infimum/supremum, limit, or partial-function default occurs.

### Docstring reading

The docstring describes global stability, design independence of positive-cell outcomes and contrasts, and a household housemate-exposure AEED of 1. It does not say that the theorem covers nonatomic designs. The formal content above is the entire mathematical statement, independently of that prose.

## SAP.P061b.T13

### Objects, expanded definitions, and quantifier order

For every Ω,N, normalized nonnegative summable mass p on Ω, and schedules g,y : Fin N → Ω → ℝ, the following four assertions hold together. All probabilities, means, and contrasts expand as in T12 to ∑', finite sums and real division. Support membership of z means precisely p(z)>0. Support stability means: for all i,z,w, p(z)>0 and p(w)>0 and g(i,z)=g(i,w) imply y(i,z)=y(i,w). Global stability removes the two positive-mass conditions.

The observed-data event probability for a predicate A : Ω × (Fin N → ℝ) → Prop is

O_D(y,A) = ∑' z, if A(z, i ↦ y(i,z)) then p(z) else 0.

It records the full assignment and full outcome vector. Predicates range over all subsets, with no measurability restriction on their syntax; they are legitimate on the atomic distribution.

1. If y is support-stable, then all of the following hold:
   * For every i,d, if π_D(i,d)>0, then for every z with p(z)>0 and g(i,z)=d, m_D(i,d)=y(i,z).
   * For every i,d,e with π_D(i,d)>0 and π_D(i,e)>0, and then every z,w with p(z)>0, p(w)>0, g(i,z)=d and g(i,w)=e, c_D(i,d,e)=y(i,z)−y(i,w).
   * There exists one schedule y' on the same Ω and units that is globally stable, agrees with y at every i,z with p(z)>0, and satisfies O_D(y,A)=O_D(y',A) for every predicate A. This single y' is chosen before A, so it works for every event simultaneously.
2. Global stability of y implies support stability of y.
3. For every schedule y', if y and y' agree for every unit on every positive-mass assignment, then O_D(y,A)=O_D(y',A) for every A. This assertion does not require stability of either schedule.
4. For every function L : (Ω × (Fin N → ℝ) → Prop) → ℝ, there exists a support-stable w with O_D(w,A)=L(A) for every A if and only if there exists a globally stable w with that property. L is an arbitrary set function; the existential assertions themselves ensure that a realizable L is an actual observed law. The two existential witnesses need not coincide.

### Junk conventions and their effect

The conditional means and contrasts in assertion 1 have strictly positive denominators. Support stability makes each relevant supported exposure cell constant. All zero-mass summands vanish, so the conditional first moments follow automatically despite unrestricted off-support outcomes. Every observed-law event sum is dominated by the summable p. Thus ∑' never supplies its non-summability default to these conclusions. No population division occurs, so N=0 is allowed; the identification clauses then have no unit to quantify over, while the law equivalence concerns the unique empty outcome vector. This legitimate degenerate case does not make the universally quantified theorem vacuous for N>0. Empty Ω cannot carry a normalized design. The globally stable extension may assign an arbitrary real (e.g. 0) to an exposure fiber not meeting the support; that is an existential choice, not a hidden definition or default in the statement, and it cannot change the observed law. Real labels and zero-mass assignment values are otherwise unrestricted. No other listed junk operations occur.

### Docstring reading

The prose promises identification on supported cells and contrasts, the implication from global to support stability, and equality of the possible observed-data laws under a fixed design. The formal statement also explicitly gives support agreement of a globally stable extension and invariance of every observed event under off-support changes.

## SAP.P061b.T14

### Objects and complete expanded statement

There are no free parameters or hypotheses. The assignment type is the four-element household Fin 2 × Fin 2 and the two units are Fin 2. The following table fully specifies the exposure and outcome schedules, including off-support assignments:

| assignment (a,b) | g(0)=own | g(1)=own | y(0)=housemate | y(1)=housemate |
|---|---:|---:|---:|---:|
| (0,0) | 0 | 0 | 0 | 0 |
| (0,1) | 0 | 1 | 1 | 0 |
| (1,0) | 1 | 0 | 0 | 1 |
| (1,1) | 1 | 1 | 1 | 1 |

The one-treated design D₁ assigns mass 1/2 to (0,1),(1,0) and zero elsewhere. The both-or-neither design D₂ assigns mass 1/2 to (0,0),(1,1) and zero elsewhere. The independent design D₃ assigns mass 1/4 everywhere. Each is a nonnegative summable real function with sum 1; all exposures 0 and 1 have marginal probability 1/2 for both units.

For clarity, M_D(d) means (1/2)∑ i∈{0,1}, [∑ z∈{0,1}² p_D(z)(if g(i,z)=d then y(i,z) else 0)] / [∑ z∈{0,1}² (if g(i,z)=d then p_D(z) else 0)]. C_D(1,0)=M_D(1)−M_D(0). Thus these are finite real sums and ratios, not abstract statistical placeholders.

The statement conjoins exactly:

* M_D₁(1)=0 and M_D₁(0)=1;
* C_D₁(1,0)=−1;
* for every i,z,w, p_D₁(z)>0 and p_D₁(w)>0 and g(i,z)=g(i,w) imply y(i,z)=y(i,w);
* it is not the case that for every i,z,w, g(i,z)=g(i,w) implies y(i,z)=y(i,w);
* C_D₂(1,0)=1 and C_D₃(1,0)=0;
* g(0,(1,0))=g(0,(1,1))=1, y(0,(1,0))=0, y(0,(1,1))=1, and not (p_D₁(1,1)>0).

The last line gives an actual same-exposure/different-outcome pair, with the second assignment outside D₁'s support. The statement does not separately assert M_D₂ or M_D₃, nor support stability under D₂ or failure of support stability under D₃.

### Junk conventions and their effect

Every sum is over four assignments or two units and hence is summable. Every displayed conditional denominator is 1/2 and the population denominator is 2. The reciprocal cardinality in D₃ is 1/4. Thus the real zero-division and non-summability defaults are unused. All Fin literals are within bounds and natural-to-real casts are exact. A nonmembership conclusion uses the genuine zero mass at (1,1), not any exceptional support convention. No empty domain, truncated subtraction, logarithm, square root, rpow, integral, toReal, extremum, limit, or partial-function default occurs.

### Docstring reading

The prose advertises the three AEEDs −1,1,0, printed AEPOs, support stability and an explicit off-support failure of global stability. Only D₁'s two AEPOs and support stability appear individually in the formal conjunction; the other two designs appear through their contrasts.

## SAP.P061b.T15

### Objects and expanded binary-household assertions

There are no free parameters or hypotheses. The binary household, own-assignment exposure g, and D₁,D₂ are exactly the finite objects described for T14. Replace the outcome y by either of the following schedules:

| assignment | attenuated y(0),y(1) | amplified y(0),y(1) |
|---|---|---|
| (0,0) | (1/2,1/2) | (0,0) |
| (0,1) | (0,1) | (0,0) |
| (1,0) | (1,0) | (0,0) |
| (1,1) | (1/2,1/2) | (1,1) |

Attenuated means: if a=b then 1/2 else the unit's own assignment. Amplified means: if a=1 and b=1 then 1 else 0, independently of the unit index. For each outcome schedule, M_D and C_D are the finite ratios and population averages given for T14 with that y substituted.

The first conjunct states all of:

* C_D₁(1,0)=1 and C_D₂(1,0)=0 for the attenuated schedule;
* both D₁ and D₂ satisfy support stability for that schedule and own-assignment exposure;
* global stability fails for that schedule and exposure;
* C_D₁(1,0)=0 and C_D₂(1,0)=1 for the amplified schedule;
* both D₁ and D₂ satisfy support stability for that schedule and own-assignment exposure;
* global stability fails for that schedule and exposure.

Every support-stability assertion expands to ∀ i,z,w, p_D(z)>0 → p_D(w)>0 → g(i,z)=g(i,w) → y(i,z)=y(i,w). Global-stability failure is the negation of the same universal assertion without the two p>0 guards. No AEPOs are separately asserted here.

### Objects and expanded hidden-version assertions

The assignment space is now Fin 3 × Fin 3, all nine pairs (a,b) with a,b∈{0,1,2}, still with two units. Write r₀(a,b)=a and r₁(a,b)=b. The real outcome for unit i is the exact natural-to-real cast of rᵢ. The exposure is gᵢ=0 if rᵢ=0 and 1 otherwise. Thus the outcome distinguishes versions 1 and 2 but the exposure groups them.

For v=1 or v=2, define D_v to give mass 1/2 exactly to (0,v) and (v,0), and zero to the other seven assignments. oneVersionTreated accepts the proof v=1 or v=2 to certify normalization; the displayed calls pass the two reflexive disjunction proofs. The definition does not assign arbitrary probability values for an invalid version.

The second conjunct states all of:

* For every i∈{0,1}, under each of D_1 and D_2, the probabilities of exposure 1 and exposure 0 are both 1/2 (four equalities per unit).
* The population mean difference C_D₁(1,0)=1 and C_D₂(1,0)=2, using outcome rᵢ and the category exposure.
* Support stability holds under each of these two designs for that outcome and exposure.
* Global stability fails for that outcome and category exposure on the entire nine-assignment space.
* For every unit i and every z,w in that space, equality rᵢ(z)=rᵢ(w) implies equality of the outcomes y(i,z)=y(i,w). In particular outcomes have no dependence on the other unit's assignment when the full raw version is used.

Here each population mean is exactly (1/2) times the sum of the two conditional means, and each conditional mean is a nine-term weighted exposed-outcome sum divided by a nine-term exposure-probability sum.

### Junk conventions and their effect

All assignment spaces and unit sets are nonempty and finite. Every displayed exposure margin is 1/2; all population denominators are 2. Thus no zero reciprocal, non-summable ∑' default, or empty sum matters. The fixed halves in the attenuated outcome are ordinary rational values. Fin literals 0,1,2 are within their respective bounds, including both valid raw-version choices; casts do not round or truncate. The generated auxiliary proofs in the closure certify positive Fin bounds, version eligibility, and normalized masses. The off-support distinctions establishing global failure use perfectly defined real-valued outcomes. No other listed exceptional operation occurs.

### Docstring reading

The prose describes the attenuation, amplification and hidden-version examples, the contrasts for the two designs, and support stability together with failure of global stability. It does not separately promise a proof that either type of design change must always attenuate or amplify effects.

## SAP.P061b.T16

### Objects, expanded definitions, quantifiers, and hypotheses

For every assignment type Ω, natural number N, normalized nonnegative summable mass p : Ω → ℝ, schedules g,y : Fin N → Ω → ℝ, and real exposure d, assume:

1. N>0;
2. for every i:Fin N, π_D(i,d)=∑' z, if g(i,z)=d then p(z) else 0 is strictly positive;
3. for every i, the real family z ↦ p(z)·|if g(i,z)=d then y(i,z) else 0| is Summable.

The third assumption is the full expansion of ExposureMoment D g y d: each restricted schedule has HasFirstMoment, meaning precisely summability of the nonnegative weighted absolute values. It is not a stability or boundedness assumption. No integrability is required of y off all the exposure cells involved.

For z∈Ω define the estimator

H_d(z) = ((N:ℝ)⁻¹) ∑ i:Fin N, (if g(i,z)=d then y(i,z) else 0)/π_D(i,d).

Define the target

M_d = ((N:ℝ)⁻¹) ∑ i:Fin N, [∑' z, p(z)·(if g(i,z)=d then y(i,z) else 0)]/π_D(i,d).

The first two conclusions are that z ↦ p(z)|H_d(z)| is Summable and that ∑' z, p(z)H_d(z)=M_d.

The third conclusion is universally quantified over every real e after fixing all the above data and assumptions. If π_D(i,e)>0 for every i and the real family p(z)|if g(i,z)=e then y(i,z) else 0| is summable for every i, then p(z)|H_d(z)−H_e(z)| is summable and

∑' z, p(z)(H_d(z)−H_e(z)) = M_d−M_e.

This unfolds htMean, htDifference, designMean, HasFirstMoment, exposureMean, averageExposureMean and averageContrast entirely. There is no condition d≠e. No support or global stability, independence, identical outcome distribution, or pointwise bound is assumed. The targets depend on the design and the full outcome schedule through their conditional cell averages.

### Junk conventions and their effect

Event sums are summable by domination by p. The explicit exposure-restricted absolute first moments ensure that all numerators and the claimed ordinary expectations are genuine summable real families. Finite linear combinations with the fixed positive probability denominators preserve these first moments, so the ∑'=0 default for nonsummable families plays no role. Population and exposure denominators are strictly positive by the hypotheses, so real a/0=0 and 0⁻¹=0 play no role. Empty Ω cannot carry a normalized design, and N=0 is explicitly excluded. No Nat subtraction, problematic cast, logarithm, square root, real power, Bochner integral, toReal, extremum, limsup/liminf, or partial-function default occurs.

### Docstring reading

The prose explicitly calls the exposure-restricted absolute first moments the usual existence conditions and promises finite ordinary expectations and unbiasedness for the HT mean and contrast without stability. The statement proves exactly those integrability and expectation identities on its atomic design domain.
