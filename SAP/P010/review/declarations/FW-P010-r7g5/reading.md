# Blind reading

Written before opening `claims.json` or `record.json`. Sources read: all three target docstrings and statements in `SAP/P010/Challenge/Part1.lean:113–123`; every declaration listed for them in `closure.json`, in `Defs/Part3.lean` and `Defs/Part4.lean`; and the two generated proof declarations, printed by Lean in `scratch/Inspect.lean`.

Throughout, `Fin K` is the finite set of natural numbers less than K, with its usual discrete measurable space. `Fin d → ℝ` has the product Borel measurable space. The population space is the product Borel space

    Ω(K,d) = ℝ^(Fin K) × Bool^(Fin K) × Fin K × ℝ^(Fin d).

Write a point as ω=(y,c,z,x). Write Y_a(ω)=y(a), C_a(ω)=c(a), Z(ω)=z, X(ω)=x. Thus the observed response is R(ω)=y(z), and the observed binary check is S(ω)=c(z). These are coordinate/evaluation functions, with no missing-value convention. All these maps and the events below are measurable. For functions F,G, Mathlib's `IndepFun F G ν` means that for EVERY measurable set B in the codomain of F and EVERY measurable set D in the codomain of G,

    ν({F∈B} ∩ {G∈D}) = ν({F∈B}) ν({G∈D}).

Products, inverse scalars, and measures in this identity are in the extended nonnegative reals. This is an unfolding into Mathlib measure notions, not an assumption that F and G have independent coordinates internally.

## SAP.P010.T21

Source: `Challenge/Part1.lean:113–115`, `Defs/Part4.lean:118–126`.

There EXISTS a Borel measure μ on Ω(2,1) satisfying ALL the following conditions, in the order of the conjunction in the statement:

1. μ is a probability measure: μ(Ω)=1.
2. For EVERY a∈{0,1}, the pair (Y_a,C_a) is independent of Z: for every Borel B⊆ℝ×Bool and every D⊆{0,1}, μ({(Y_a,C_a)∈B}∩{Z∈D})=μ({(Y_a,C_a)∈B})μ({Z∈D}). For every a, μ({Z=a})>0. This is per-arm pair independence; it does not assert independence of the whole vector ((Y_a,C_a))_a from Z, or any independence involving X.
3. For EVERY a∈{0,1}, the real ratio μ({S=true,Z=a})/μ({Z=a}) is strictly positive. In Lean both masses are first converted from extended nonnegative reals to reals. Items 1–3 are exactly the expansion of `populationAssumptions`, `randomAssignment`, `positivePassRates`, and `passRate`.
4. S and Z are independent: for every B⊆Bool and D⊆{0,1}, μ({S∈B}∩{Z∈D})=μ({S∈B})μ({Z∈D}).
5. The event A={C_0=true and C_1=true} has positive μ-mass. This expands `allPass`.
6. E_1={S=true,Z=1} and E_0={S=true,Z=0} both have positive μ-mass. This expands `passed ∩ assigned a`.
7. R is Bochner integrable under μ restricted to E_1, and under μ restricted to E_0. The real function Y_1−Y_0 is Bochner integrable under μ restricted to A.
8. The following real numbers are unequal:

       (∫_{E_1} R dμ)/μ(E_1) − (∫_{E_0} R dμ)/μ(E_0)
          ≠ (∫_A (Y_1−Y_0) dμ)/μ(A).

All denominators in item 8 denote the real conversions of their masses. This expands `meanOn` completely. No particular μ, numeric value of the discrepancy, or condition on X is specified. There is no universal quantifier over populations, and no assumption that all potential checks agree almost surely.

The docstring describes an existential population with check/assignment independence and an unequal selected versus always-passer contrast, with positive masses and ordinary finite means.

### Junk-value audit

`meanOn` is a totalized definition: real division by zero is zero; an infinite event mass has `ENNReal.toReal = 0`; and a nonintegrable Bochner integrand has integral zero. None can affect item 8, because μ is a probability measure, each of A,E_1,E_0 has strictly positive mass, and each restricted integrand is explicitly integrable. Likewise `passRate` uses real division and `toReal`, but all arm masses are finite and positive. Boolean/Fin evaluation is total. Arms 0 and 1 are genuine elements of `Fin 2`; Lean's generated `T11Statement._proof_4 : NeZero (1+1)` is only the proof that the numeral's modulus is nonzero. It adds no population hypothesis. This target uses no truncated subtraction (the contrast is in ℝ), logarithm, square root, real power, infimum/supremum, limit, partial function, infinite index sum, or empty index type. Features have one coordinate. No default or junk value is used to establish the discrepancy.

Closure coverage: `Population`, `potentialOutcome`, `potentialCheck`, `arm`, `response`, `check`, `allPass`, `assigned`, `passed`, `meanOn`, `passRate`, `randomAssignment`, `positivePassRates`, `populationAssumptions`, `T21Statement`, and `T11Statement._proof_4` have all been read and expanded above.

## SAP.P010.T22

Source: `Challenge/Part1.lean:117–119`, `Defs/Part4.lean:129–132`.

For EVERY pair of natural numbers K,d, for EVERY Borel measure μ on Ω(K,d), given, in order:

1. μ is a probability measure;
2. for EVERY a∈Fin K, the triple (Y_a,C_a,X) is independent of Z, and for EVERY a∈Fin K, μ({Z=a})>0;
3. μ({ω : for EVERY a,b∈Fin K, C_a(ω)=C_b(ω)})=1;

the conclusion is: for EVERY b∈Bool, IF μ(B_b)>0 for B_b={S=b}, THEN X is independent of Z under the measure

    ν_b = μ(B_b)⁻¹ • (μ restricted to B_b).

More explicitly, hypothesis 2 means that for every a, every Borel H⊆ℝ×Bool×ℝ^(Fin d), and every D⊆Fin K,

    μ({(Y_a,C_a,X)∈H}∩{Z∈D}) = μ({(Y_a,C_a,X)∈H}) μ({Z∈D}).

The conclusion means that for every b with positive stratum mass, every Borel H⊆ℝ^(Fin d), and every D⊆Fin K,

    ν_b({X∈H}∩{Z∈D}) = ν_b({X∈H}) ν_b({Z∈D}),

where for every measurable E, ν_b(E)=μ(E∩B_b)/μ(B_b), with arithmetic in extended nonnegative reals. This fully expands `covariateRandomAssignment`, `sameCheck`, and `covariateBalance`, as well as the population coordinate definitions. It is conditional independence X ⟂ Z | S for both passing AND failing strata with positive probability, not just equality of coordinate means. It does not assume `positivePassRates`, integrability of potential outcomes, or independence of the whole potential-outcome vector from Z. The potential outcomes are part of an independence hypothesis, although no expectation of them appears in the conclusion.

The docstring states that common potential check status implies covariate balance conditional on observed check status. The explicit statement also carries the probability, per-arm triple randomization, and arm-positivity hypotheses above.

### Junk-value audit

The conditional measure definition uses an ENNReal inverse: 0⁻¹=∞ and ∞⁻¹=0, with extended-real scalar multiplication. It is tested only after μ(B_b)>0, and μ being a probability measure also gives μ(B_b)≤1<∞. Therefore it is the ordinary conditional probability law, not a junk normalization. Zero-mass b strata have no asserted conditional independence. `covariateBalance._proof_1 : IsScalarTower ENNReal ENNReal ENNReal` is a structural proof for scalar multiplication, with no statistical content.

If K=0 then Ω(K,d) is empty because its arm component is `Fin 0`, so no probability μ exists; this is an impossible degenerate parameter case, not inconsistency for all K. If K=1 the arm is constant and the conclusion is automatic, a legitimate special case. If d=0 then the covariate vector is the unique empty function and its independence is automatic; again other dimensions remain quantified. The assertion is nontrivial for K≥2,d≥1. There are no conditional means, real divisions, real conversions of ∞, Bochner integrals, truncated subtractions, logarithms, roots, powers, extrema, limits, Nat/Int-to-real casts, or partial-function defaults in this target's closure.

Closure coverage: `Population`, `potentialOutcome`, `potentialCheck`, `arm`, `features`, `check`, `assigned`, `sameCheck`, `covariateRandomAssignment`, `covariateBalance`, `covariateBalance._proof_1`, and `T22Statement` have all been read and expanded above.

## SAP.P010.T23

Source: `Challenge/Part1.lean:121–123`, `Defs/Part4.lean:135–148`.

There EXISTS a Borel measure μ on Ω(2,1) satisfying ALL the following conditions, in the order of the conjunction:

1. μ is a probability measure.
2. For EVERY a∈{0,1}, μ({S=true,Z=a})/μ({Z=a})>0, with masses converted to reals. This expands `positivePassRates` and `passRate`.
3. For EVERY a∈{0,1}, (Y_a,C_a,X) is independent of Z, in the full measurable-set factorization sense above, and μ({Z=a})>0. This is the full expansion of `covariateRandomAssignment`; it does not assert joint-vector independence across arms.
4. For EVERY b∈Bool with μ({S=b})>0, X is independent of Z under μ({S=b})⁻¹ • μ restricted to {S=b}. For every measurable event E this conditioned measure has mass μ(E∩{S=b})/μ({S=b}); independence quantifies over every Borel covariate set and every subset of the arm labels. This expands `covariateBalance`.
5. Let F={X is the function taking its sole coordinate to 0}; let A={C_0=true,C_1=true}; and let E_a={S=true,Z=a}. All three masses μ(A∩F), μ(E_1∩F), μ(E_0∩F) are strictly positive.
6. R is Bochner integrable under μ restricted to E_1∩F, and under μ restricted to E_0∩F. The real function Y_1−Y_0 is Bochner integrable under μ restricted to A∩F.
7. The following real conditional contrasts are unequal:

       (∫_{E_1∩F} R dμ)/μ(E_1∩F) − (∫_{E_0∩F} R dμ)/μ(E_0∩F)
          ≠ (∫_{A∩F} (Y_1−Y_0) dμ)/μ(A∩F).

Item 7 is precisely the expansion of all three `meanOn` occurrences. `potentialOutcome`, `potentialCheck`, `features`, `response`, `check`, `arm`, `passed`, `assigned`, and `allPass` are the coordinate functions/events described explicitly in these formulas. No agreement of potential checks is assumed, and no numeric discrepancy is specified. X may be constant; neither nondegeneracy of covariates nor continuous covariate distributions is required. The stratum is an actual positive-mass event X=0, so no choice of a conditional-law version at a null point is involved.

The docstring describes existence of a conditionally covariate-balanced population with positive conditioning masses, finite ordinary conditional means, and differing contrasts at zero covariates.

### Junk-value audit

As for T21, `meanOn` has the possible defaults for nonintegrable integrands, zero denominators, and `toReal ∞`, but every one of its actual uses is protected by integrability, positive stratum mass, and the probability assumption. All `passRate` denominators are finite and positive by item 3 and the probability assumption. As for T22, the ENNReal normalization in `covariateBalance` is applied only to strictly positive finite masses; null check strata are skipped. Equality X=0 is equality of functions on `Fin 1`, a genuine Borel singleton. The indices 0,1 in `Fin 2` are valid; the two generated proof declarations are just the nonzero-modulus and scalar-tower proofs already printed, with no hidden population condition. No Nat/Int truncation, log/root/power, empty index, extrema, limits, or partial-function default appears in this existential. None of the inequalities or mean discrepancies can be attributed to a junk value.

Closure coverage: `Population`, `potentialOutcome`, `potentialCheck`, `arm`, `features`, `response`, `check`, `allPass`, `assigned`, `passed`, `meanOn`, `passRate`, `positivePassRates`, `covariateRandomAssignment`, `covariateBalance`, `covariateBalance._proof_1`, `T11Statement._proof_4`, and `T23Statement` have all been read and expanded above.
