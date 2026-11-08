import SAP.P006a.WH.W2.Tools

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace SAP.P006a.WH.W2
noncomputable section

/-- Qualified Lemma 2 on its minimal weighted moment domain (about 80--140 lines).
Use RepairT6T7_unit_outcome_moments and law transport for the outcome term.
The two L1 premises make (T-p)H integrable. Integrate its zero conditional
expectation to equate the two weighted estimator integrals. Consistency rewrites
each reward summand as TY(1)-TH; integrate the finite sum. Do not assume H is L1,
or identical estimator evaluation laws at different units. -/
def T8_L1 : Prop :=
  ∀ {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (π : C → ℝ) (hπ : Admissible π)
    (hS : PolicyDesign E π) (hI : CoinMomentW2 E π),
    E.expectedTT π = ∑ i, (OutcomeMeanW2 E π - EvaluationMeanW2 E π i)

/-- Selection equivalence, including the positive-propensity formulation
(about 180--300 lines). For every covariate-measurable test set, the treated
residual integral equals the residual integral on the measure restricted to
T=true. Its L1 domain and the L1 baseline give H in L1 of that restricted
measure. Apply conditional-expectation uniqueness in both directions.
For the final equivalence, m-measurable sets have treated mass integral p;
therefore their treated null sets coincide with their original null sets on
{p>0}. Apply this to the m-measurable failure set of the two conditional means.
This also handles zero treatment probability and the zero treated measure. -/
def T8_L2 : Prop := SelectedEquivalenceW2

/-- Conditional independence on the correct weighted L1 domain
(about 160--260 lines). Convert conditional independence into the conditional
indicator-product identity using condIndepFun_iff_condExp_inter_preimage_eq_mul.
First integrate bounded truncations of H. Then let the truncation level tend
to infinity, separately dominated by |TH| and |pH|; conditional expectation is
continuous in L1 (use tendsto_condExp_unique). Subtract the two conditional
expectations. The full-H factorization equivalence is already proved in Tools.
Do not apply an L1 theorem directly to an unselected H. -/
def T8_L3 : Prop :=
  ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (T : Ω → Bool) (H p : Ω → ℝ) (hT : Measurable T) (hH : Measurable H)
    (hp : Measurable[m] p) (hpb : ∀ ω, 0 ≤ p ω ∧ p ω ≤ 1)
    (hcoin : μ[(fun ω => bit (T ω)) | m] =ᵐ[μ] p)
    (hTH : Integrable (fun ω => bit (T ω) * H ω) μ)
    (hpH : Integrable (fun ω => p ω * H ω) μ)
    (hi : CondIndepFun m hm T H μ),
    μ[(fun ω => (bit (T ω) - p ω) * H ω) | m] =ᵐ[μ] (fun _ => 0)

/-- Independent unbiased estimation at an arbitrary public baseline
(about 80--140 lines). Adapt T6_independent_estimation_minimal_integrability:
at each feasible policy unpack its independent-estimator representation, use
the whole (X,U,T) design vector, and F(z,design)=T_i*(f(z,C_i)-b0(X_i)).
RepairT6T7_auxiliary_condExp gives conditional mean zero at the vector sigma
algebra using pointwise unbiasedness under that policy's law of the auxiliary
draw. Descend to sigma(X_i,U_i) by
condExp_condExp_of_le. The only evaluated L1 input is the treated residual;
replace the donor's true full-covariate baseline with b0, not with E.μ0. -/
def T8_L4 : Prop := IndependentUnbiasedW2

/-- Derive the common evaluation law and the weighted coin moment from independent
auxiliary data (about 160--280 lines). Independence and fixed marginal laws give
law(Z,C_i)=Q×PX; map by (z,c)↦(c,f(z,c.public)). This proves the first two
conclusions without moment assumptions. For the last conclusion, full evaluated
L1 is supplied explicitly by its premise (the assembly derives it from finite
absolute error). Conditional integration over Z first gives E[H_i|design]=g(C_i),
where g(c)=integral f(z,c.public) dQ, with the required L1 by Fubini.
Pull out bounded T_i and p(C_i), then descend to sigma(C_i) and use its Bernoulli
mean. This gives E[(T_i-p(C_i))H_i|C_i]=0. No unbiasedness is used. -/
def T8_L5 : Prop :=
  ∀ {Ω X U A : Type} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace U] [MeasurableSpace A] {n : ℕ}
    (E : Experiment Ω (X × U) n) (PiSet : Set ((X × U) → ℝ))
    (π : (X × U) → ℝ) (hπ : π ∈ PiSet) (hpa : Admissible π) (S : PolicyDesign E π)
    (Q : Measure A) (Z : Ω → A) (f : A × X → ℝ)
    (hA : AuxiliaryDataW2 E PiSet Q Z f),
    let D := AuxiliaryLawW2 E Q f
    IsProbabilityMeasure D ∧
      (∀ i, IdentDistrib (fun ω => (E.X i ω, E.μhat π ω (E.X i ω)))
        id (E.law π) D) ∧
      ((∀ i, Integrable (fun ω => E.μhat π ω (E.X i ω)) (E.law π)) →
        CoinMomentW2 E π)

/-- Whole corrected T8. The main clauses and all optimization/sum algebra are
proved here or in Tools; only the five stated local mathematical leaves remain. -/
theorem T8_assembly (h1 : T8_L1) (h2 : T8_L2) (h3 : T8_L3)
    (h4 : T8_L4) (h5 : T8_L5) : T8WholeStatement_W2 := by
  have common : CommonLawProposition10W2 := by
    intro Ω C _ _ n E PiSet hPiSet hS hI D _hD hc he
    apply proposition10OfErrorW2 E PiSet (EvaluationErrorW2 E D)
    intro π hπ
    exact commonLawErrorAtW2 E π (hPiSet π hπ) (hS π hπ) D (hc π hπ) he
      (h1 E π (hPiSet π hπ) (hS π hπ) (hI π hπ))
  have factorization : CoinFactorizationW2 := by
    intro Ω mΩ _ μ _ m hm T H p hT hH hp hpb hcoin hTH hpH
    letI : MeasurableSpace Ω := mΩ
    exact ⟨h3 μ m hm T H p hT hH hp hpb hcoin hTH hpH,
      fun hi => factorizationAtW2 μ m T H p hp hTH hpH hi⟩
  refine ⟨informationBoundW2, h2, h4, ?_, factorization, common, ?_⟩
  · intro Ω C _ _ n E π hπ _hS hI
    exact qualifiedAtW2 E π hπ (h1 E π hπ _hS hI)
  · intro Ω X U A _ _ _ _ n E PiSet hPiSet hS Q Z f hA he
    let D := AuxiliaryLawW2 E Q f
    have infrastructure (π : (X × U) → ℝ) (hπ : π ∈ PiSet) :=
      h5 E PiSet π hπ (hPiSet π hπ) (hS π hπ) Q Z f hA
    have hc (π : (X × U) → ℝ) (hπ : π ∈ PiSet) :
        ∀ i, IdentDistrib (fun ω => (E.X i ω, E.μhat π ω (E.X i ω)))
          id (E.law π) D := (infrastructure π hπ).2.1
    have hI (π : (X × U) → ℝ) (hπ : π ∈ PiSet) : CoinMomentW2 E π :=
      (infrastructure π hπ).2.2
        (evaluatedIntegrableW2 E π (hS π hπ) D (hc π hπ) he)
    refine ⟨?_, ?_⟩
    · intro π hπ i
      refine ⟨hc π hπ i, ?_⟩
      exact ((hc π hπ i).comp
        ((measurable_snd.sub ((hS π hπ).means_measurable.1.comp measurable_fst)).abs)).integral_eq
    · by_cases hne : PiSet.Nonempty
      · obtain ⟨π, hπ⟩ := hne
        exact common E PiSet hPiSet hS hI D (infrastructure π hπ).1 hc he
      · refine ⟨?_, ?_⟩
        · intro π hπ
          exact (hne ⟨π, hπ⟩).elim
        · intro b s hb _hs
          exact (hne ⟨b, hb.1⟩).elim

end
end SAP.P006a.WH.W2
