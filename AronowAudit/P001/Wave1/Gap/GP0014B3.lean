import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGP0014B3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-!
The measure-equality argument below is the L¹ extension of event CI: it avoids
both an L² assumption and a standard-Borel assumption on the original sample space.
-/

private theorem t91_ci_map_left {Ω E F G H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace G] [MeasurableSpace H]
    (μ : Measure Ω) (X : Ω → E) (hX : Measurable X)
    (U : Ω → F) (Z : Ω → G) (h : CI μ X hX U Z)
    (f : F → H) (hf : Measurable f) : CI μ X hX (f ∘ U) Z := by
  intro A B hA hB
  simpa only [Function.comp_apply, Set.mem_preimage] using
    h (f ⁻¹' A) B (hf hA) hB

private theorem t91_indicator_integrable {Ω F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace F]
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → F) (hU : Measurable U)
    (A : Set F) (hA : MeasurableSet A) :
    Integrable (fun ω => if U ω ∈ A then (1 : ℝ) else 0) μ := by
  have he : (fun ω => if U ω ∈ A then (1 : ℝ) else 0) =
      (U ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [Set.indicator, Set.mem_preimage]
  rw [he]
  exact (integrable_const (1 : ℝ)).indicator (hU hA)

private theorem t91_indicator_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (I : Ω → ℝ)
    (hI : ∀ ω, I ω = 0 ∨ I ω = 1) :
    (∀ᵐ ω ∂μ, 0 ≤ μ[I | m] ω) ∧
    (∀ᵐ ω ∂μ, ‖μ[I | m] ω‖ ≤ 1) := by
  have h0 : ∀ᵐ ω ∂μ, 0 ≤ I ω := ae_of_all _ (fun ω => by
    rcases hI ω with h | h <;> simp [h])
  have h1 : ∀ᵐ ω ∂μ, I ω ≤ 1 := ae_of_all _ (fun ω => by
    rcases hI ω with h | h <;> simp [h])
  have hc0 := condExp_nonneg (m := m) h0
  have hc1 := condExp_le_nonneg_const (m := m) (by norm_num : (0 : ℝ) ≤ 1) h1
  refine ⟨hc0, ?_⟩
  filter_upwards [hc0, hc1] with ω hω0 hω1
  simpa only [Real.norm_eq_abs, abs_of_nonneg hω0] using hω1

/-- Extend event CI to an integral against an arbitrary measurable real outcome.
The two finite measures on the outcome line agree on every Borel set; integrating
`id` against their common pushforward gives the desired L¹ identity. -/
private theorem t91_event_weight_integral {Ω E G : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace G]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (U : Ω → ℝ) (hU : Measurable U)
    (Z : Ω → G) (hZ : Measurable Z) (hind : CI μ X hX U Z)
    (B : Set G) (hB : MeasurableSet B)
    (p : Ω → ℝ)
    (hpm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] p)
    (hpI : Integrable p μ) (hp0 : ∀ᵐ ω ∂μ, 0 ≤ p ω)
    (hpbound : ∀ᵐ ω ∂μ, ‖p ω‖ ≤ 1)
    (hpce : μ[(fun ω => if Z ω ∈ B then (1 : ℝ) else 0) |
      MeasurableSpace.comap X inferInstance] =ᵐ[μ] p)
    (S : Set Ω) (hS : MeasurableSet[MeasurableSpace.comap X inferInstance] S) :
    (∫ ω in S ∩ Z ⁻¹' B, U ω ∂μ) = ∫ ω in S, U ω * p ω ∂μ := by
  have hm : (MeasurableSpace.comap X inferInstance) ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hpm' : Measurable p := (hpm.mono hm).measurable
  have hpasm : AEStronglyMeasurable p μ := hpm'.stronglyMeasurable.aestronglyMeasurable
  let ν : Measure Ω := (μ.restrict S).withDensity (fun ω => ENNReal.ofReal (p ω))
  have hmap : (μ.restrict (S ∩ Z ⁻¹' B)).map U = ν.map U := by
    apply Measure.ext
    intro A hA
    let IA : Ω → ℝ := fun ω => if U ω ∈ A then 1 else 0
    let IAB : Ω → ℝ := fun ω => if U ω ∈ A ∧ Z ω ∈ B then 1 else 0
    have hIA : Integrable IA μ := t91_indicator_integrable μ U hU A hA
    have hIAB : Integrable IAB μ := by
      have he : IAB = (U ⁻¹' A ∩ Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
        funext ω
        simp only [IAB, Set.indicator, Set.mem_inter_iff, Set.mem_preimage]
      rw [he]
      exact (integrable_const (μ := μ) (1 : ℝ)).indicator ((hU hA).inter (hZ hB))
    have hIAp : Integrable (IA * p) μ := hIA.mul_bdd hpasm hpbound
    have hfactor : μ[IAB | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] μ[IA | (MeasurableSpace.comap X inferInstance)] * p := by
      filter_upwards [hind A B hA hB, hpce] with ω hi hc
      change μ[IAB | (MeasurableSpace.comap X inferInstance)] ω = μ[IA | (MeasurableSpace.comap X inferInstance)] ω * p ω
      exact hi.trans (congrArg (fun z : ℝ => μ[IA | (MeasurableSpace.comap X inferInstance)] ω * z) hc)
    have hpull : μ[IA * p | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] μ[IA | (MeasurableSpace.comap X inferInstance)] * p :=
      condExp_mul_of_stronglyMeasurable_right hpm hIAp hIA
    have hint : (∫ ω in S, IAB ω ∂μ) = ∫ ω in S, IA ω * p ω ∂μ := by
      calc
        (∫ ω in S, IAB ω ∂μ) = ∫ ω in S, μ[IAB | (MeasurableSpace.comap X inferInstance)] ω ∂μ :=
          (setIntegral_condExp hm hIAB hS).symm
        _ = ∫ ω in S, (μ[IA | (MeasurableSpace.comap X inferInstance)] ω * p ω) ∂μ :=
          integral_congr_ae (ae_restrict_of_ae hfactor)
        _ = ∫ ω in S, μ[IA * p | (MeasurableSpace.comap X inferInstance)] ω ∂μ :=
          integral_congr_ae (ae_restrict_of_ae hpull.symm)
        _ = ∫ ω in S, IA ω * p ω ∂μ := setIntegral_condExp hm hIAp hS
    have hleft : (μ.restrict (S ∩ Z ⁻¹' B)).map U A =
        ENNReal.ofReal (∫ ω in S, IAB ω ∂μ) := by
      rw [Measure.map_apply hU hA]
      have hi : (∫ ω in S, IAB ω ∂μ) =
          (μ (U ⁻¹' A ∩ (S ∩ Z ⁻¹' B))).toReal := by
        have he : IAB = (U ⁻¹' A ∩ Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
          funext ω
          simp only [IAB, Set.indicator, Set.mem_inter_iff, Set.mem_preimage]
        rw [he, integral_indicator ((hU hA).inter (hZ hB)), setIntegral_const]
        simp only [smul_eq_mul, mul_one, Measure.real,
          Measure.restrict_apply ((hU hA).inter (hZ hB))]
        have hsets : (U ⁻¹' A ∩ Z ⁻¹' B) ∩ S =
            U ⁻¹' A ∩ (S ∩ Z ⁻¹' B) := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_preimage]
          tauto
        exact congrArg (fun C : Set Ω => (μ C).toReal) hsets
      rw [hi, ENNReal.ofReal_toReal (measure_ne_top μ _)]
      rw [Measure.restrict_apply (hU hA)]
    have hright : ν.map U A = ENNReal.ofReal (∫ ω in S, IA ω * p ω ∂μ) := by
      rw [Measure.map_apply hU hA]
      change (μ.restrict S).withDensity (fun ω => ENNReal.ofReal (p ω)) (U ⁻¹' A) = _
      rw [withDensity_apply _ (hU hA)]
      have he : (∫ ω in S, IA ω * p ω ∂μ) =
          ∫ ω in U ⁻¹' A, p ω ∂μ.restrict S := by
        rw [← integral_indicator (hU hA)]
        apply integral_congr_ae
        filter_upwards with ω
        by_cases hω : U ω ∈ A <;> simp [IA, Set.indicator, hω]
      rw [he]
      exact (ofReal_integral_eq_lintegral_ofReal hpI.integrableOn.integrableOn
        (ae_restrict_of_ae (ae_restrict_of_ae hp0))).symm
    exact hleft.trans ((congrArg ENNReal.ofReal hint).trans hright.symm)
  calc
    (∫ ω in S ∩ Z ⁻¹' B, U ω ∂μ) =
        ∫ u : ℝ, u ∂(μ.restrict (S ∩ Z ⁻¹' B)).map U :=
      (integral_map hU.aemeasurable (measurable_id'.stronglyMeasurable.aestronglyMeasurable)).symm
    _ = ∫ u : ℝ, u ∂ν.map U := by rw [hmap]
    _ = ∫ ω, U ω ∂ν := integral_map hU.aemeasurable
      (measurable_id'.stronglyMeasurable.aestronglyMeasurable)
    _ = ∫ ω in S, (ENNReal.ofReal (p ω)).toReal • U ω ∂μ :=
      integral_withDensity_eq_integral_toReal_smul hpm'.ennreal_ofReal
        (ae_of_all _ (fun ω => ENNReal.ofReal_lt_top)) U
    _ = ∫ ω in S, U ω * p ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hp0] with ω hω
      rw [ENNReal.toReal_ofReal hω, smul_eq_mul, mul_comm]

/-- A sigma(X)-measurable function is constant on each X-fiber. -/
private theorem t91_fiber_integral {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (p U : Ω → ℝ)
    (hpm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] p)
    (x : E) (ω₀ : Ω) (hω₀ : X ω₀ = x) :
    (∫ ω in {ω | X ω = x}, U ω * p ω ∂μ) =
      (∫ ω in {ω | X ω = x}, U ω ∂μ) * p ω₀ := by
  have hC : MeasurableSet {ω | X ω = x} := hX (measurableSet_singleton x)
  calc
    (∫ ω in {ω | X ω = x}, U ω * p ω ∂μ) =
        ∫ ω in {ω | X ω = x}, U ω * p ω₀ ∂μ := by
      apply setIntegral_congr_fun hC
      intro ω hω
      change U ω * p ω = U ω * p ω₀
      rw [hpm.factorsThrough (hω.trans hω₀.symm)]
    _ = (∫ ω in {ω | X ω = x}, U ω ∂μ) * p ω₀ := integral_mul_const _ _

private theorem t91_countable_total_mean {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
    (μ : Measure Ω) (X : Ω → E) (hX : Measurable X)
    (U : Ω → ℝ) (hU : Integrable U μ) :
    mean μ U = ∑' x : E, ∫ ω in {ω | X ω = x}, U ω ∂μ := by
  have hcover : (⋃ x : E, {ω | X ω = x}) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨X ω, rfl⟩
  have hdisj : Pairwise (fun x y : E => Disjoint
      {ω | X ω = x} {ω | X ω = y}) := by
    intro x y hxy
    apply Set.disjoint_left.mpr
    intro ω hx hy
    exact hxy (hx.symm.trans hy)
  have hs := hasSum_integral_iUnion (fun x : E => hX (measurableSet_singleton x))
    hdisj hU.integrableOn
  change HasSum (fun x : E => ∫ ω in {ω | X ω = x}, U ω ∂μ) (∫ ω in ⋃ x : E, {ω | X ω = x}, U ω ∂μ) at hs
  rw [hcover, Measure.restrict_univ] at hs
  exact hs.tsum_eq.symm

theorem positive_mass_dose_identification_proof {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ)
   (hX : Measurable X) (hD : Measurable D) (Y : ℝ → Ω → ℝ)
   (hY : ∀ t,Measurable (Y t)) (hi : ∀ t,Integrable (Y t) μ)
   (hobs : Measurable (fun ω => Y (D ω) ω)) (hobsI : Integrable (fun ω => Y (D ω) ω) μ)
   (hind : CI μ X hX (fun ω t => Y t ω) D) (d : ℝ)
   (hpos : ∀ x,0 < prob μ {ω | X ω=x} → 0 < prob μ {ω | X ω=x ∧ D ω=d}) :
   (∀ x,0 < prob μ {ω | X ω=x} →
     conditionalMeanAt μ X (Y d) x=
       conditionalMeanAt μ (fun ω => (X ω,D ω)) (fun ω => Y (D ω) ω) (x,d)) ∧
   mean μ (Y d)=∑' x : E,
     conditionalMeanAt μ (fun ω => (X ω,D ω)) (fun ω => Y (D ω) ω) (x,d)*prob μ {ω | X ω=x} := by
  let I : Ω → ℝ := fun ω => if D ω ∈ ({d} : Set ℝ) then 1 else 0
  let p : Ω → ℝ := μ[I | (MeasurableSpace.comap X inferInstance)]
  have hI : Integrable I μ :=
    t91_indicator_integrable μ D hD {d} (measurableSet_singleton d)
  have hpM : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] p := stronglyMeasurable_condExp
  have hpI : Integrable p μ := integrable_condExp
  have hpBounds := t91_indicator_bounds μ (MeasurableSpace.comap X inferInstance) I (fun ω => by
    dsimp [I]
    split_ifs <;> simp)
  have hindd : CI μ X hX (Y d) D := by
    exact t91_ci_map_left μ X hX (fun ω t => Y t ω) D hind
      (fun f : ℝ → ℝ => f d) (measurable_pi_apply d)
  have hcell : ∀ x, 0 < prob μ {ω | X ω = x} →
      conditionalMeanAt μ X (Y d) x =
        conditionalMeanAt μ (fun ω => (X ω, D ω)) (fun ω => Y (D ω) ω) (x, d) := by
    intro x hx
    have hr : 0 < prob μ {ω | X ω = x ∧ D ω = d} := hpos x hx
    have hC : MeasurableSet {ω | X ω = x} := hX (measurableSet_singleton x)
    have hCm : MeasurableSet[(MeasurableSpace.comap X inferInstance)] {ω | X ω = x} :=
      ⟨{x}, measurableSet_singleton x, rfl⟩
    have hDC : MeasurableSet ({ω | X ω = x} ∩ D ⁻¹' ({d} : Set ℝ)) :=
      hC.inter (hD (measurableSet_singleton d))
    have hnonempty : Set.Nonempty {ω | X ω = x} := by
      by_contra hn
      have he : {ω | X ω = x} = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      simp [prob, he] at hx
    obtain ⟨ω₀, hω₀⟩ := hnonempty
    have hIc : I = (D ⁻¹' ({d} : Set ℝ)).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      simp only [I, Set.indicator, Set.mem_preimage]
    have hrint : prob μ {ω | X ω = x ∧ D ω = d} =
        ∫ ω in {ω | X ω = x}, I ω ∂μ := by
      rw [hIc, integral_indicator (hD (measurableSet_singleton d)), setIntegral_const]
      simp only [smul_eq_mul, mul_one, Measure.real, prob,
        Measure.restrict_apply (hD (measurableSet_singleton d))]
      have hsets : {ω | X ω = x ∧ D ω = d} =
          D ⁻¹' ({d} : Set ℝ) ∩ {ω | X ω = x} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
          Set.mem_singleton_iff]
        tauto
      exact congrArg (fun C : Set Ω => (μ C).toReal) hsets
    have hcp : prob μ {ω | X ω = x ∧ D ω = d} =
        prob μ {ω | X ω = x} * p ω₀ := by
      calc
        prob μ {ω | X ω = x ∧ D ω = d} =
            ∫ ω in {ω | X ω = x}, I ω ∂μ := hrint
        _ = ∫ ω in {ω | X ω = x}, p ω ∂μ :=
          (setIntegral_condExp hX.comap_le hI hCm).symm
        _ = ∫ _ in {ω | X ω = x}, p ω₀ ∂μ := by
          apply setIntegral_congr_fun hC
          intro ω hω
          exact hpM.factorsThrough (hω.trans hω₀.symm)
        _ = prob μ {ω | X ω = x} * p ω₀ := by
          simp only [setIntegral_const, smul_eq_mul, prob, Measure.real]
    have hweight :
        (∫ ω in {ω | X ω = x} ∩ D ⁻¹' ({d} : Set ℝ), Y d ω ∂μ) =
          (∫ ω in {ω | X ω = x}, Y d ω ∂μ) * p ω₀ := by
      exact (t91_event_weight_integral μ X hX (Y d) (hY d) D hD hindd
        {d} (measurableSet_singleton d) p hpM hpI hpBounds.1 hpBounds.2
        (Filter.EventuallyEq.rfl) _ hCm).trans
          (t91_fiber_integral μ X hX p (Y d) hpM x ω₀ hω₀)
    have hpair : {ω | (X ω, D ω) = (x, d)} =
        {ω | X ω = x} ∩ D ⁻¹' ({d} : Set ℝ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Prod.mk.injEq, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_singleton_iff]
    have hobsCell :
        (∫ ω in {ω | X ω = x} ∩ D ⁻¹' ({d} : Set ℝ), Y (D ω) ω ∂μ) =
          ∫ ω in {ω | X ω = x} ∩ D ⁻¹' ({d} : Set ℝ), Y d ω ∂μ := by
      apply setIntegral_congr_fun hDC
      intro ω hω
      have hd : D ω = d := hω.2
      simp only [hd]
    unfold conditionalMeanAt
    rw [hpair, hobsCell]
    change (∫ ω in {ω | X ω = x}, Y d ω ∂μ) / prob μ {ω | X ω = x} =
      (∫ ω in {ω | X ω = x} ∩ D ⁻¹' ({d} : Set ℝ), Y d ω ∂μ) /
        prob μ {ω | X ω = x ∧ D ω = d}
    apply (div_eq_div_iff hx.ne' hr.ne').mpr
    rw [hweight, hcp]
    ring
  refine ⟨hcell, ?_⟩
  rw [t91_countable_total_mean μ X hX (Y d) (hi d)]
  apply tsum_congr
  intro x
  by_cases hx : 0 < prob μ {ω | X ω = x}
  · rw [← hcell x hx]
    unfold conditionalMeanAt
    exact (div_mul_cancel₀ _ hx.ne').symm
  · have hμ : μ {ω | X ω = x} = 0 := by
      by_contra hne
      exact hx (ENNReal.toReal_pos hne (measure_ne_top μ _))
    have hq : prob μ {ω | X ω = x} = 0 := by simp only [prob, hμ, ENNReal.toReal_zero]
    simp only [hq, mul_zero, Measure.restrict_eq_zero.mpr hμ, integral_zero_measure]

/-! Population mean identification from conditional independence and positive propensity. -/

private theorem t94_ci_congr_left {Ω E F G : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace G]
    (μ : Measure Ω) (X : Ω → E) (hX : Measurable X)
    (U V : Ω → F) (Z : Ω → G) (hUV : U =ᵐ[μ] V)
    (hind : CI μ X hX U Z) : CI μ X hX V Z := by
  intro A B hA hB
  have hi : (fun ω => if V ω ∈ A ∧ Z ω ∈ B then (1 : ℝ) else 0) =ᵐ[μ]
      (fun ω => if U ω ∈ A ∧ Z ω ∈ B then (1 : ℝ) else 0) := by
    filter_upwards [hUV] with ω hω
    rw [hω]
  have hj : (fun ω => if V ω ∈ A then (1 : ℝ) else 0) =ᵐ[μ]
      (fun ω => if U ω ∈ A then (1 : ℝ) else 0) := by
    filter_upwards [hUV] with ω hω
    rw [hω]
  filter_upwards [condExp_congr_ae (m := MeasurableSpace.comap X inferInstance) hi,
    condExp_congr_ae (m := MeasurableSpace.comap X inferInstance) hj,
    hind A B hA hB] with ω hiω hjω hω
  rw [hiω, hjω]
  exact hω

/-- The same weighted integral identity for integrable outcomes, with no separate
measurability hypothesis: replace the outcome by its strongly measurable version. -/
private theorem t94_event_weight_integral {Ω E G : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace G]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (U : Ω → ℝ) (hU : Integrable U μ)
    (Z : Ω → G) (hZ : Measurable Z) (hind : CI μ X hX U Z)
    (B : Set G) (hB : MeasurableSet B) (p : Ω → ℝ)
    (hpm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] p)
    (hpI : Integrable p μ) (hp0 : ∀ᵐ ω ∂μ, 0 ≤ p ω)
    (hpbound : ∀ᵐ ω ∂μ, ‖p ω‖ ≤ 1)
    (hpce : μ[(fun ω => if Z ω ∈ B then (1 : ℝ) else 0) |
      MeasurableSpace.comap X inferInstance] =ᵐ[μ] p)
    (S : Set Ω) (hS : MeasurableSet[MeasurableSpace.comap X inferInstance] S) :
    (∫ ω in S ∩ Z ⁻¹' B, U ω ∂μ) = ∫ ω in S, U ω * p ω ∂μ := by
  let V : Ω → ℝ := hU.aestronglyMeasurable.mk U
  have hV : Measurable V := hU.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hUV : U =ᵐ[μ] V := hU.aestronglyMeasurable.ae_eq_mk
  have hCI : CI μ X hX V Z := t94_ci_congr_left μ X hX U V Z hUV hind
  calc
    (∫ ω in S ∩ Z ⁻¹' B, U ω ∂μ) = ∫ ω in S ∩ Z ⁻¹' B, V ω ∂μ :=
      integral_congr_ae (ae_restrict_of_ae hUV)
    _ = ∫ ω in S, V ω * p ω ∂μ :=
      t91_event_weight_integral μ X hX V hV Z hZ hCI B hB p
        hpm hpI hp0 hpbound hpce S hS
    _ = ∫ ω in S, U ω * p ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hUV] with ω hω
      rw [hω]

/-- Pull an X-measurable integrable function out of an arm indicator. -/
private theorem t94_covariate_weight_integral {Ω E G : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace G]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (Z : Ω → G) (hZ : Measurable Z)
    (B : Set G) (hB : MeasurableSet B)
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable (f ∘ X) μ)
    (p : Ω → ℝ)
    (hpce : μ[(fun ω => if Z ω ∈ B then (1 : ℝ) else 0) |
      MeasurableSpace.comap X inferInstance] =ᵐ[μ] p)
    (S : Set Ω) (hS : MeasurableSet[MeasurableSpace.comap X inferInstance] S) :
    (∫ ω in S ∩ Z ⁻¹' B, f (X ω) ∂μ) =
      ∫ ω in S, f (X ω) * p ω ∂μ := by
  let I : Ω → ℝ := fun ω => if Z ω ∈ B then 1 else 0
  have hXm : Measurable[(MeasurableSpace.comap X inferInstance)] X := measurable_iff_comap_le.mpr le_rfl
  have hfm : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] (f ∘ X) := (hf.comp hXm).stronglyMeasurable
  have hII : Integrable I μ := t91_indicator_integrable μ Z hZ B hB
  have hb : ∀ᵐ ω ∂μ, ‖I ω‖ ≤ 1 := ae_of_all _ (fun ω => by
    dsimp [I]
    split_ifs <;> norm_num)
  have hprod : Integrable ((f ∘ X) * I) μ := hfI.mul_bdd hII.1 hb
  have hpull : μ[(f ∘ X) * I | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] (f ∘ X) * μ[I | (MeasurableSpace.comap X inferInstance)] :=
    condExp_mul_of_stronglyMeasurable_left hfm hprod hII
  have hdef : (fun ω => f (X ω) * I ω) =
      (Z ⁻¹' B).indicator (fun ω => f (X ω)) := by
    funext ω
    by_cases hω : Z ω ∈ B <;> simp [I, Set.indicator, hω]
  calc
    (∫ ω in S ∩ Z ⁻¹' B, f (X ω) ∂μ) =
        ∫ ω in S, f (X ω) * I ω ∂μ := by
      rw [hdef, integral_indicator (hZ hB), Measure.restrict_restrict (hZ hB)]
      rw [Set.inter_comm (Z ⁻¹' B) S]
    _ = ∫ ω in S, μ[(f ∘ X) * I | (MeasurableSpace.comap X inferInstance)] ω ∂μ :=
      (setIntegral_condExp hX.comap_le hprod hS).symm
    _ = ∫ ω in S, f (X ω) * p ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hpull, ae_restrict_of_ae hpce] with ω hω hc
      exact hω.trans (congrArg (fun z : ℝ => f (X ω) * z) hc)

/-- Arm-restricted integral identities identify the population mean under CI and
positive propensity. Both the outcome and the fitted mean need only L¹. -/
private theorem t94_positive_arm_mean {Ω E G : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace G]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (Z : Ω → G) (hZ : Measurable Z)
    (U : Ω → ℝ) (hU : Integrable U μ) (hind : CI μ X hX U Z)
    (B : Set G) (hB : MeasurableSet B)
    (q f : E → ℝ) (hq : Measurable q) (hf : Measurable f)
    (hqI : Integrable (q ∘ X) μ) (hfI : Integrable (f ∘ X) μ)
    (hqpos : ∀ ω, 0 < q (X ω)) (hqbound : ∀ ω, ‖q (X ω)‖ ≤ 1)
    (hqce : μ[(fun ω => if Z ω ∈ B then (1 : ℝ) else 0) |
      MeasurableSpace.comap X inferInstance] =ᵐ[μ] (q ∘ X))
    (harm : ∀ A : Set E, MeasurableSet A →
      (∫ ω in X ⁻¹' A ∩ Z ⁻¹' B, U ω ∂μ) =
        ∫ ω in X ⁻¹' A ∩ Z ⁻¹' B, f (X ω) ∂μ) :
    mean μ U = mean μ (fun ω => f (X ω)) := by
  let u : Ω → ℝ := μ[U | (MeasurableSpace.comap X inferInstance)]
  let w : Ω → ℝ := q ∘ X
  have hXm : Measurable[(MeasurableSpace.comap X inferInstance)] X := measurable_iff_comap_le.mpr le_rfl
  have hwm : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] w := (hq.comp hXm).stronglyMeasurable
  have hfm : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] (f ∘ X) := (hf.comp hXm).stronglyMeasurable
  have hum : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] u := stronglyMeasurable_condExp
  have hwbound : ∀ᵐ ω ∂μ, ‖w ω‖ ≤ 1 := ae_of_all _ hqbound
  have hw0 : ∀ᵐ ω ∂μ, 0 ≤ w ω := ae_of_all _ (fun ω => (hqpos ω).le)
  have hwasm : AEStronglyMeasurable w μ :=
    (hwm.mono hX.comap_le).aestronglyMeasurable
  have hUwI : Integrable (U * w) μ := hU.mul_bdd hwasm hwbound
  have huwI : Integrable (u * w) μ := integrable_condExp.mul_bdd hwasm hwbound
  have hfwI : Integrable ((f ∘ X) * w) μ := hfI.mul_bdd hwasm hwbound
  have hpull : μ[U * w | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] u * w :=
    condExp_mul_of_stronglyMeasurable_right hwm hUwI hU
  have heq : u * w =ᵐ[μ] (f ∘ X) * w := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hX.comap_le
      (fun s hs hfin => huwI.integrableOn)
      (fun s hs hfin => hfwI.integrableOn) ?_
      (hum.mul hwm).aestronglyMeasurable (hfm.mul hwm).aestronglyMeasurable
    intro S hS hfin
    obtain ⟨A, hA, rfl⟩ := hS
    have hpre : MeasurableSet[(MeasurableSpace.comap X inferInstance)] (X ⁻¹' A) := ⟨A, hA, rfl⟩
    calc
      (∫ ω in X ⁻¹' A, (u * w) ω ∂μ) =
          ∫ ω in X ⁻¹' A, μ[U * w | (MeasurableSpace.comap X inferInstance)] ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hpull.symm)
      _ = ∫ ω in X ⁻¹' A, U ω * w ω ∂μ :=
        setIntegral_condExp hX.comap_le hUwI hpre
      _ = ∫ ω in X ⁻¹' A ∩ Z ⁻¹' B, U ω ∂μ :=
        (t94_event_weight_integral μ X hX U hU Z hZ hind B hB w hwm
          hqI hw0 hwbound hqce _ hpre).symm
      _ = ∫ ω in X ⁻¹' A ∩ Z ⁻¹' B, f (X ω) ∂μ := harm A hA
      _ = ∫ ω in X ⁻¹' A, f (X ω) * w ω ∂μ :=
        t94_covariate_weight_integral μ X hX Z hZ B hB f hf hfI w hqce _ hpre
  have huf : u =ᵐ[μ] f ∘ X := by
    filter_upwards [heq] with ω hω
    exact mul_right_cancel₀ (hqpos ω).ne' hω
  unfold mean
  calc
    (∫ ω, U ω ∂μ) = ∫ ω, u ω ∂μ := (integral_condExp hX.comap_le).symm
    _ = ∫ ω, f (X ω) ∂μ := integral_congr_ae huf

/-- Restrict an observed (D,X)-CEF to the measurable rectangle {d} × A. -/
private theorem t94_arm_restriction {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (hX : Measurable X)
    (D O U : Ω → ℝ) (hD : Measurable D) (F : ℝ × E → ℝ)
    (hm : IsCEF μ (fun ω => (D ω, X ω)) O F)
    (d : ℝ) (hobs : ∀ ω, D ω = d → O ω = U ω) :
    ∀ A : Set E, MeasurableSet A →
      (∫ ω in X ⁻¹' A ∩ D ⁻¹' ({d} : Set ℝ), U ω ∂μ) =
        ∫ ω in X ⁻¹' A ∩ D ⁻¹' ({d} : Set ℝ), F (d, X ω) ∂μ := by
  intro A hA
  have hS : MeasurableSet (X ⁻¹' A ∩ D ⁻¹' ({d} : Set ℝ)) :=
    (hX hA).inter (hD (measurableSet_singleton d))
  have he : (fun ω => (D ω, X ω)) ⁻¹' (({d} : Set ℝ) ×ˢ A) =
      X ⁻¹' A ∩ D ⁻¹' ({d} : Set ℝ) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_inter_iff]
    tauto
  have hrect := hm.2.2.2 (({d} : Set ℝ) ×ˢ A) ((measurableSet_singleton d).prod hA)
  rw [he] at hrect
  calc
    (∫ ω in X ⁻¹' A ∩ D ⁻¹' ({d} : Set ℝ), U ω ∂μ) =
        ∫ ω in X ⁻¹' A ∩ D ⁻¹' ({d} : Set ℝ), O ω ∂μ := by
      apply setIntegral_congr_fun hS
      intro ω hω
      exact (hobs ω hω.2).symm
    _ = ∫ ω in X ⁻¹' A ∩ D ⁻¹' ({d} : Set ℝ), F (D ω, X ω) ∂μ := hrect
    _ = ∫ ω in X ⁻¹' A ∩ D ⁻¹' ({d} : Set ℝ), F (d, X ω) ∂μ := by
      apply setIntegral_congr_fun hS
      intro ω hω
      have hd : D ω = d := hω.2
      simp only [hd]

theorem ml_potential_mean_population_identity_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K τ : ℕ} (X : Ω → Fin K → ℝ) (D Y0 Y1 : Ω → ℝ)
   (hX : Measurable X) (hD : Measurable D) (h0 : Integrable Y0 μ) (h1 : Integrable Y1 μ)
   (hbinary : ∀ ω,D ω=0 ∨ D ω=1) (p : (Fin K → ℝ) → ℝ) (hp : IsCEF μ X D p)
   (hpos : ∃ ε : ℝ,0 < ε ∧ ∀ ω,ε < p (X ω) ∧ p (X ω) < 1-ε)
   (hind : CI μ X hX (fun ω => (Y0 ω,Y1 ω)) D)
   (g : ℝ → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ)
   (hm : IsCEF μ (fun ω => (D ω,X ω))
     (fun ω => Y1 ω*D ω+Y0 ω*(1-D ω)) (fun dx => modelConditionalMean g dx.1 dx.2 θ))
   (hmi : ∀ d∈({0,1} : Set ℝ),Integrable (fun ω => modelConditionalMean g d (X ω) θ) μ) :
   mean μ Y0=mean μ (fun ω => modelConditionalMean g 0 (X ω) θ) ∧
   mean μ Y1=mean μ (fun ω => modelConditionalMean g 1 (X ω) θ) := by
  let F : ℝ × (Fin K → ℝ) → ℝ :=
    fun dx => modelConditionalMean g dx.1 dx.2 θ
  let f0 : (Fin K → ℝ) → ℝ := fun x => modelConditionalMean g 0 x θ
  let f1 : (Fin K → ℝ) → ℝ := fun x => modelConditionalMean g 1 x θ
  have hf0 : Measurable f0 := hm.1.comp (measurable_const.prodMk measurable_id)
  have hf1 : Measurable f1 := hm.1.comp (measurable_const.prodMk measurable_id)
  have hf0I : Integrable (f0 ∘ X) μ := hmi 0 (by simp)
  have hf1I : Integrable (f1 ∘ X) μ := hmi 1 (by simp)
  obtain ⟨ε, hε, hεp⟩ := hpos
  have hp01 (ω : Ω) : 0 < p (X ω) ∧ p (X ω) < 1 := by
    constructor <;> linarith [(hεp ω).1, (hεp ω).2]
  have hpbound (ω : Ω) : ‖p (X ω)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (hp01 ω).1]
    exact (hp01 ω).2.le
  have hqbound (ω : Ω) : ‖1 - p (X ω)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (hp01 ω).2)]
    linarith [(hp01 ω).1]
  have hCI0 : CI μ X hX Y0 D :=
    t91_ci_map_left μ X hX (fun ω => (Y0 ω, Y1 ω)) D hind
      Prod.fst measurable_fst
  have hCI1 : CI μ X hX Y1 D :=
    t91_ci_map_left μ X hX (fun ω => (Y0 ω, Y1 ω)) D hind
      Prod.snd measurable_snd
  have hpCE : (p ∘ X) =ᵐ[μ] μ[D | (MeasurableSpace.comap X inferInstance)] := isCEF_condExp μ X hX D p hp
  have hI1 : (fun ω => if D ω ∈ ({1} : Set ℝ) then (1 : ℝ) else 0) = D := by
    funext ω
    rcases hbinary ω with h | h <;> simp [h]
  have hI0 : (fun ω => if D ω ∈ ({0} : Set ℝ) then (1 : ℝ) else 0) =
      (fun ω => 1 - D ω) := by
    funext ω
    rcases hbinary ω with h | h <;> simp [h]
  have hCE1 : μ[(fun ω => if D ω ∈ ({1} : Set ℝ) then (1 : ℝ) else 0) | (MeasurableSpace.comap X inferInstance)]
      =ᵐ[μ] p ∘ X := by
    rw [hI1]
    exact hpCE.symm
  have hCE0 : μ[(fun ω => if D ω ∈ ({0} : Set ℝ) then (1 : ℝ) else 0) | (MeasurableSpace.comap X inferInstance)]
      =ᵐ[μ] (fun ω => 1 - p (X ω)) := by
    rw [hI0]
    have hsub := condExp_sub (integrable_const (1 : ℝ)) hp.2.1 (MeasurableSpace.comap X inferInstance)
    filter_upwards [hsub, hpCE] with ω hs hc
    change μ[(fun ω => 1 - D ω) | (MeasurableSpace.comap X inferInstance)] ω = 1 - p (X ω)
    calc
      μ[(fun ω => 1 - D ω) | (MeasurableSpace.comap X inferInstance)] ω =
          μ[(fun _ : Ω => (1 : ℝ)) | (MeasurableSpace.comap X inferInstance)] ω - μ[D | (MeasurableSpace.comap X inferInstance)] ω := hs
      _ = 1 - p (X ω) := by
        simpa only [condExp_const hX.comap_le, Function.comp_apply] using
          congrArg (fun z : ℝ => 1 - z) hc.symm
  have hobs0 : ∀ ω, D ω = 0 →
      Y1 ω * D ω + Y0 ω * (1 - D ω) = Y0 ω := by
    intro ω hd
    simp only [hd, mul_zero, sub_zero, mul_one, zero_add]
  have hobs1 : ∀ ω, D ω = 1 →
      Y1 ω * D ω + Y0 ω * (1 - D ω) = Y1 ω := by
    intro ω hd
    simp only [hd, mul_one, sub_self, mul_zero, add_zero]
  have hArm0 : ∀ A : Set (Fin K → ℝ), MeasurableSet A →
      (∫ ω in X ⁻¹' A ∩ D ⁻¹' ({0} : Set ℝ), Y0 ω ∂μ) =
        ∫ ω in X ⁻¹' A ∩ D ⁻¹' ({0} : Set ℝ), f0 (X ω) ∂μ :=
    t94_arm_restriction μ X hX D (fun ω => Y1 ω * D ω + Y0 ω * (1 - D ω))
      Y0 hD F hm 0 hobs0
  have hArm1 : ∀ A : Set (Fin K → ℝ), MeasurableSet A →
      (∫ ω in X ⁻¹' A ∩ D ⁻¹' ({1} : Set ℝ), Y1 ω ∂μ) =
        ∫ ω in X ⁻¹' A ∩ D ⁻¹' ({1} : Set ℝ), f1 (X ω) ∂μ :=
    t94_arm_restriction μ X hX D (fun ω => Y1 ω * D ω + Y0 ω * (1 - D ω))
      Y1 hD F hm 1 hobs1
  constructor
  · exact t94_positive_arm_mean μ X hX D hD Y0 h0 hCI0 {0}
      (measurableSet_singleton 0) (fun x => 1 - p x) f0
      (measurable_const.sub hp.1) hf0 ((integrable_const 1).sub hp.2.2.1)
      hf0I (fun ω => sub_pos.mpr (hp01 ω).2) hqbound hCE0 hArm0
  · exact t94_positive_arm_mean μ X hX D hD Y1 h1 hCI1 {1}
      (measurableSet_singleton 1) p f1 hp.1 hf1 hp.2.2.1 hf1I
      (fun ω => (hp01 ω).1) hpbound hCE1 hArm1

end
end AronowAudit.P001.Wave1
