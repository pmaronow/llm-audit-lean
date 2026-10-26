import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ConditionalProbability

/-!
P001-T91: continuous-dose identification with an explicit measurable curve space
and jointly measurable evaluation. No continuity of individual sample paths is used.
-/

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
local instance instDecidableDecisionT91 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-- Normalized cell integration equals the totalized conditional mean. -/
lemma DecisionT91_integral_cell {Ω E : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → E) (f : Ω → ℝ) (x : E) :
    (∫ ω, f ω ∂(ProbabilityTheory.cond μ {ω | X ω = x})) =
      conditionalMeanAt μ X f x := by
  simp [ProbabilityTheory.cond, integral_smul_measure, conditionalMeanAt, prob,
    ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]

/-- A conditional expectation is constant on each positive measurable fiber. -/
lemma DecisionT91_condExp_on_cell {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (f : Ω → ℝ) (hf : Integrable f μ) (x : E)
    (hp : 0 < prob μ {ω | X ω = x}) :
    ∀ ω, X ω = x →
      (μ[f | MeasurableSpace.comap X inferInstance]) ω = conditionalMeanAt μ X f x := by
  intro ω hω
  have hs : MeasurableSet {ξ | X ξ = x} := hX (measurableSet_singleton x)
  have hsm : MeasurableSet[MeasurableSpace.comap X inferInstance] {ξ | X ξ = x} :=
    ⟨{x}, measurableSet_singleton x, rfl⟩
  have hconst : ∀ ξ ∈ {ξ | X ξ = x},
      (μ[f | MeasurableSpace.comap X inferInstance]) ξ =
        (μ[f | MeasurableSpace.comap X inferInstance]) ω := by
    intro ξ hξ
    exact (stronglyMeasurable_condExp.factorsThrough) (hξ.trans hω.symm)
  have heq := setIntegral_condExp hX.comap_le hf hsm
  rw [setIntegral_congr_fun hs hconst, setIntegral_const] at heq
  change prob μ {ξ | X ξ = x} *
    (μ[f | MeasurableSpace.comap X inferInstance]) ω = _ at heq
  unfold conditionalMeanAt
  exact (eq_div_iff (ne_of_gt hp)).mpr (by simpa [mul_comm] using heq)

/-- Conditional independence gives independence under a normalized positive cell. -/
lemma DecisionT91_indep_cell {Ω E V W : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace V] [MeasurableSpace W]
    [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (U : Ω → V) (Z : Ω → W) (hU : Measurable U) (hZ : Measurable Z)
    (hind : CI μ X hX U Z) (x : E) (hp : 0 < prob μ {ω | X ω = x}) :
    IndepFun U Z (ProbabilityTheory.cond μ {ω | X ω = x}) := by
  let s := {ω | X ω = x}
  have hs : MeasurableSet s := hX (measurableSet_singleton x)
  have hs0 : μ s ≠ 0 := by
    intro hz
    simpa [prob, s, hz] using hp
  let ρ := ProbabilityTheory.cond μ s
  let instProbabilityDecisionT91Cell : IsProbabilityMeasure ρ := cond_isProbabilityMeasure hs0
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A B hA hB
  let a : Ω → ℝ := fun ω => if U ω ∈ A then 1 else 0
  let b : Ω → ℝ := fun ω => if Z ω ∈ B then 1 else 0
  let c : Ω → ℝ := fun ω => if U ω ∈ A ∧ Z ω ∈ B then 1 else 0
  have ha : Integrable a μ := by
    exact (integrable_const (1 : ℝ)).indicator (hU hA)
  have hb : Integrable b μ := by
    exact (integrable_const (1 : ℝ)).indicator (hZ hB)
  have hc : Integrable c μ := by
    have hc' : c = (U ⁻¹' A ∩ Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
      ext ξ
      simp only [c, Set.indicator_apply, Set.mem_inter_iff, Set.mem_preimage]
    rw [hc']
    exact (integrable_const (1 : ℝ) (μ := μ)).indicator ((hU hA).inter (hZ hB))
  have heq : (fun _ : Ω => conditionalMeanAt μ X c x) =ᵐ[ρ]
      (fun _ => conditionalMeanAt μ X a x * conditionalMeanAt μ X b x) := by
    apply Measure.ae_smul_measure
    apply (ae_restrict_iff' hs).mpr
    filter_upwards [hind A B hA hB] with ω hω hxs
    change (μ[c | MeasurableSpace.comap X inferInstance]) ω =
      (μ[a | MeasurableSpace.comap X inferInstance]) ω *
      (μ[b | MeasurableSpace.comap X inferInstance]) ω at hω
    simpa only [DecisionT91_condExp_on_cell μ X hX c hc x hp ω hxs,
      DecisionT91_condExp_on_cell μ X hX a ha x hp ω hxs,
      DecisionT91_condExp_on_cell μ X hX b hb x hp ω hxs] using hω
  obtain ⟨ω, hω⟩ := heq.exists
  have hreal : (ρ (U ⁻¹' A ∩ Z ⁻¹' B)).toReal =
      (ρ (U ⁻¹' A)).toReal * (ρ (Z ⁻¹' B)).toReal := by
    rw [← DecisionT91_integral_cell, ← DecisionT91_integral_cell,
      ← DecisionT91_integral_cell] at hω
    have ha' : a = (U ⁻¹' A).indicator (fun _ => (1 : ℝ)) := rfl
    have hb' : b = (Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) := rfl
    have hc' : c = (U ⁻¹' A ∩ Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
      ext ξ
      simp only [c, Set.indicator_apply, Set.mem_inter_iff, Set.mem_preimage]
    change (∫ ξ, c ξ ∂ρ) = (∫ ξ, a ξ ∂ρ) * (∫ ξ, b ξ ∂ρ) at hω
    simpa only [ha', hb', hc', integral_indicator (hU hA),
      integral_indicator (hZ hB), integral_indicator ((hU hA).inter (hZ hB)),
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def] using hω
  calc
    ρ (U ⁻¹' A ∩ Z ⁻¹' B) = ENNReal.ofReal (ρ (U ⁻¹' A ∩ Z ⁻¹' B)).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = ENNReal.ofReal ((ρ (U ⁻¹' A)).toReal * (ρ (Z ⁻¹' B)).toReal) := by rw [hreal]
    _ = ρ (U ⁻¹' A) * ρ (Z ⁻¹' B) := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top _ _),
        ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Jointly measurable evaluation and an independent product law construct a CEF. -/
lemma DecisionT91_curve_cef {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (D : Ω → ℝ) (curve : Ω → V) (hD : Measurable D) (hcurve : Measurable curve)
    (eval : ℝ → V → ℝ) (heval : Measurable (fun z : ℝ × V => eval z.1 z.2))
    (hind : IndepFun D curve ρ)
    (hobs : Integrable (fun ω => eval (D ω) (curve ω)) ρ) :
    IsCEF ρ D (fun ω => eval (D ω) (curve ω))
      (fun t => ∫ v, eval t v ∂ρ.map curve) := by
  let e : ℝ × V → ℝ := fun z => eval z.1 z.2
  let ν := ρ.map D
  let νV := ρ.map curve
  let m : ℝ → ℝ := fun t => ∫ v, eval t v ∂νV
  have hm : Measurable m := heval.stronglyMeasurable.integral_prod_right'.measurable
  have hpair : Measurable (fun ω => (D ω, curve ω)) := hD.prodMk hcurve
  have hprod : ρ.map (fun ω => (D ω, curve ω)) = ν.prod νV :=
    hind.map_prod_eq_prod_map_map hD.aemeasurable hcurve.aemeasurable
  have hi : Integrable e (ν.prod νV) := by
    rw [← hprod]
    exact (integrable_map_measure heval.stronglyMeasurable.aestronglyMeasurable
      hpair.aemeasurable).mpr hobs
  have hmi : Integrable m ν := hi.integral_prod_left
  refine ⟨hm, hobs, hmi.comp_aemeasurable hD.aemeasurable, ?_⟩
  intro A hA
  have hpre : (fun ω => (D ω, curve ω)) ⁻¹' (A ×ˢ Set.univ) = D ⁻¹' A := by
    ext ω
    simp
  have hleft : (∫ z in A ×ˢ Set.univ, e z ∂ρ.map (fun ω => (D ω, curve ω))) =
      ∫ ω in D ⁻¹' A, eval (D ω) (curve ω) ∂ρ := by
    rw [setIntegral_map (hA.prod MeasurableSet.univ)
      heval.stronglyMeasurable.aestronglyMeasurable hpair.aemeasurable, hpre]
  calc
    (∫ ω in D ⁻¹' A, eval (D ω) (curve ω) ∂ρ) =
        ∫ z in A ×ˢ Set.univ, e z ∂ν.prod νV := by rw [← hprod]; exact hleft.symm
    _ = ∫ t in A, m t ∂ν := by
      simpa only [Measure.restrict_univ] using
        setIntegral_prod e (s := A) (t := Set.univ) hi.integrableOn
    _ = ∫ ω in D ⁻¹' A, m (D ω) ∂ρ :=
      setIntegral_map hA hm.stronglyMeasurable.aestronglyMeasurable hD.aemeasurable

/-- Finite scaling preserves the defining CEF identities. -/
lemma DecisionT91_cef_smul {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (D Y : Ω → ℝ) (m : ℝ → ℝ) (h : IsCEF ρ D Y m) :
    IsCEF (c • ρ) D Y m := by
  refine ⟨h.1, h.2.1.smul_measure hc, h.2.2.1.smul_measure hc, ?_⟩
  intro A hA
  simp only [Measure.restrict_smul, integral_smul_measure, h.2.2.2 A hA]

/-- The constructed curve CEF, transferred back to the unnormalized cell. -/
lemma DecisionT91_observable_cell {Ω E V : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace V] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ)
    (hX : Measurable X) (hD : Measurable D)
    (curve : Ω → V) (hcurve : Measurable curve) (eval : ℝ → V → ℝ)
    (heval : Measurable (fun z : ℝ × V => eval z.1 z.2))
    (hind : CI μ X hX curve D)
    (hobs : Integrable (fun ω => eval (D ω) (curve ω)) μ)
    (x : E) (hp : 0 < prob μ {ω | X ω = x}) :
    IsCEF (μ.restrict {ω | X ω = x}) D (fun ω => eval (D ω) (curve ω))
      (fun t => conditionalMeanAt μ X (fun ω => eval t (curve ω)) x) := by
  let s := {ω | X ω = x}
  have hs0 : μ s ≠ 0 := by
    intro hz
    simpa [prob, s, hz] using hp
  let ρ := ProbabilityTheory.cond μ s
  let instProbabilityDecisionT91Observable : IsProbabilityMeasure ρ := cond_isProbabilityMeasure hs0
  have hobsρ : Integrable (fun ω => eval (D ω) (curve ω)) ρ :=
    hobs.restrict.smul_measure (ENNReal.inv_ne_top.mpr hs0)
  have hindρ : IndepFun D curve ρ :=
    (DecisionT91_indep_cell μ X hX curve D hcurve hD hind x hp).symm
  have hcef := DecisionT91_curve_cef ρ D curve hD hcurve eval heval hindρ hobsρ
  have hmean : (fun t => ∫ v, eval t v ∂ρ.map curve) =
      (fun t => conditionalMeanAt μ X (fun ω => eval t (curve ω)) x) := by
    funext t
    have ht : Measurable (fun v => eval t v) :=
      heval.comp (measurable_const.prodMk measurable_id)
    calc
      (∫ v, eval t v ∂ρ.map curve) = ∫ ω, eval t (curve ω) ∂ρ :=
        integral_map hcurve.aemeasurable ht.stronglyMeasurable.aestronglyMeasurable
      _ = _ := DecisionT91_integral_cell μ X _ x
  rw [hmean] at hcef
  have hscale : μ s • ρ = μ.restrict s := by
    simp only [ρ, ProbabilityTheory.cond, smul_smul,
      ENNReal.mul_inv_cancel hs0 (measure_ne_top _ _), one_smul]
  rw [← hscale]
  exact DecisionT91_cef_smul ρ (μ s) (measure_ne_top _ _) _ _ _ hcef

/-- CEF uniqueness also holds for the finite, unnormalized cell measure. -/
lemma DecisionT91_cef_condExp {Ω : Type*} [MeasurableSpace Ω]
    (σ : Measure Ω) [IsFiniteMeasure σ] (D : Ω → ℝ) (hD : Measurable D)
    (Y : Ω → ℝ) (m : ℝ → ℝ) (h : IsCEF σ D Y m) :
    (m ∘ D) =ᵐ[σ] σ[Y | MeasurableSpace.comap D inferInstance] := by
  have hDm : Measurable[MeasurableSpace.comap D inferInstance] D :=
    measurable_iff_comap_le.mpr le_rfl
  refine ae_eq_condExp_of_forall_setIntegral_eq hD.comap_le h.2.1
    (fun s hs hfin => h.2.2.1.integrableOn) ?_
    (h.1.comp hDm).stronglyMeasurable.aestronglyMeasurable
  intro s hs hfin
  rcases hs with ⟨A, hA, rfl⟩
  exact (h.2.2.2 A hA).symm

/-- At a supported dose, continuous CEF versions for a finite measure agree. -/
lemma DecisionT91_supported_value {Ω : Type*} [MeasurableSpace Ω]
    (σ : Measure Ω) [IsFiniteMeasure σ] (D : Ω → ℝ) (hD : Measurable D)
    (Y : Ω → ℝ) (m n : ℝ → ℝ) (hm : IsCEF σ D Y m) (hn : IsCEF σ D Y n)
    (t : ℝ) (hmc : ContinuousAt m t) (hnc : ContinuousAt n t)
    (hsupp : ∀ ε : ℝ, 0 < ε → 0 < σ (D ⁻¹' Metric.ball t ε)) : m t = n t := by
  have heq := (DecisionT91_cef_condExp σ D hD Y m hm).trans
    (DecisionT91_cef_condExp σ D hD Y n hn).symm
  by_contra hne
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp ((hmc.ne_iff_eventually_ne hnc).mp hne)
  have hz : σ {ω | m (D ω) ≠ n (D ω)} = 0 := ae_iff.mp heq
  have hbzero : σ (D ⁻¹' Metric.ball t ε) = 0 :=
    measure_mono_null (fun ω hω => hball hω) hz
  exact (ne_of_gt (hsupp ε hε)) hbzero

/-- Countable covariate cells give an absolutely convergent total-expectation sum. -/
lemma DecisionT91_standardization {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    HasSum (fun x : E => conditionalMeanAt μ X f x * prob μ {ω | X ω = x})
      (mean μ f) := by
  have hcover : (⋃ x : E, {ω | X ω = x}) = Set.univ := by
    ext ω
    simp
  have hdisj : Pairwise (fun x y : E => Disjoint {ω | X ω = x} {ω | X ω = y}) := by
    intro x y hxy
    exact Set.disjoint_left.mpr (fun ω hx hy => hxy (hx.symm.trans hy))
  have heq : ∀ x : E, conditionalMeanAt μ X f x * prob μ {ω | X ω = x} =
      ∫ ω in {ω | X ω = x}, f ω ∂μ := by
    intro x
    by_cases hp : prob μ {ω | X ω = x} = 0
    · have hz : μ {ω | X ω = x} = 0 :=
        (ENNReal.toReal_eq_zero_iff _).mp hp |>.resolve_right (measure_ne_top _ _)
      simp [hp, Measure.restrict_eq_zero.mpr hz]
    · exact div_mul_cancel₀ _ hp
  simp_rw [heq]
  have hsum := hasSum_integral_iUnion
    (s := fun x : E => {ω | X ω = x})
    (fun x => hX (measurableSet_singleton x)) hdisj hf.integrableOn
  simpa only [hcover, Measure.restrict_univ, mean] using hsum

/-- P001-T91: continuous-dose identification with jointly measurable evaluation. -/
theorem continuous_dose_identified_evaluation_ready {Ω E V : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace V]
  [MeasurableSingletonClass E] [Countable E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ)
  (hX : Measurable X) (hD : Measurable D)
  (curve : Ω → V) (hcurve : Measurable curve) (eval : ℝ → V → ℝ)
  (heval : Measurable (fun z : ℝ × V => eval z.1 z.2))
  (hfaithful : Function.Injective (fun v : V => fun t : ℝ => eval t v))
  (hind : CI μ X hX curve D)
  (hi : ∀ t, Integrable (fun ω => eval t (curve ω)) μ)
  (hobs : Integrable (fun ω => eval (D ω) (curve ω)) μ)
  (d d' : ℝ)
  (hm : ∀ x, 0 < prob μ {ω | X ω = x} →
    ContinuousAt (fun t => conditionalMeanAt μ X (fun ω => eval t (curve ω)) x) d ∧
    ContinuousAt (fun t => conditionalMeanAt μ X (fun ω => eval t (curve ω)) x) d')
  (hsupp : ∀ x, 0 < prob μ {ω | X ω = x} → ∀ ε : ℝ, 0 < ε →
    0 < μ {ω | X ω = x ∧ D ω ∈ Metric.ball d ε} ∧
    0 < μ {ω | X ω = x ∧ D ω ∈ Metric.ball d' ε}) :
  let Y := fun t ω => eval t (curve ω)
  let m := fun x t => conditionalMeanAt μ X (Y t) x
  (∀ x, 0 < prob μ {ω | X ω = x} →
    IsCEF (μ.restrict {ω | X ω = x}) D (fun ω => Y (D ω) ω) (m x)) ∧
  mean μ (fun ω => Y d' ω-Y d ω) =
    (∑' x : E, m x d' * prob μ {ω | X ω = x}) -
    (∑' x : E, m x d * prob μ {ω | X ω = x}) ∧
  (∀ mobs : E → ℝ → ℝ,
    (∀ x, 0 < prob μ {ω | X ω = x} →
      IsCEF (μ.restrict {ω | X ω = x}) D (fun ω => Y (D ω) ω) (mobs x) ∧
      ContinuousAt (mobs x) d ∧ ContinuousAt (mobs x) d') →
    (∀ x, 0 < prob μ {ω | X ω = x} → mobs x d = m x d ∧ mobs x d' = m x d') ∧
    mean μ (fun ω => Y d' ω-Y d ω) =
      (∑' x : E, mobs x d' * prob μ {ω | X ω = x}) -
      (∑' x : E, mobs x d * prob μ {ω | X ω = x})) := by
  dsimp only
  let Y := fun t ω => eval t (curve ω)
  let m := fun x t => conditionalMeanAt μ X (Y t) x
  have hcef : ∀ x, 0 < prob μ {ω | X ω = x} →
      IsCEF (μ.restrict {ω | X ω = x}) D (fun ω => Y (D ω) ω) (m x) := by
    intro x hx
    exact DecisionT91_observable_cell μ X D hX hD curve hcurve eval heval hind hobs x hx
  have hcontrast : mean μ (fun ω => Y d' ω - Y d ω) =
      (∑' x : E, m x d' * prob μ {ω | X ω = x}) -
      (∑' x : E, m x d * prob μ {ω | X ω = x}) := by
    change (∫ ω, Y d' ω - Y d ω ∂μ) = _
    rw [integral_sub (hi d') (hi d)]
    exact congrArg₂ (fun a b : ℝ => a - b)
      (DecisionT91_standardization μ X hX (Y d') (hi d')).tsum_eq.symm
      (DecisionT91_standardization μ X hX (Y d) (hi d)).tsum_eq.symm
  refine ⟨hcef, hcontrast, ?_⟩
  intro mobs hversion
  have hvalues : ∀ x, 0 < prob μ {ω | X ω = x} →
      mobs x d = m x d ∧ mobs x d' = m x d' := by
    intro x hx
    have hs : ∀ ε : ℝ, 0 < ε →
        0 < (μ.restrict {ω | X ω = x}) (D ⁻¹' Metric.ball d ε) ∧
        0 < (μ.restrict {ω | X ω = x}) (D ⁻¹' Metric.ball d' ε) := by
      intro ε hε
      have hrestrict (t : ℝ) :
          (μ.restrict {ω | X ω = x}) (D ⁻¹' Metric.ball t ε) =
            μ {ω | X ω = x ∧ D ω ∈ Metric.ball t ε} := by
        rw [Measure.restrict_apply (hD Metric.isOpen_ball.measurableSet)]
        congr 1
        ext ω
        exact and_comm
      rw [hrestrict d, hrestrict d']
      exact hsupp x hx ε hε
    exact ⟨DecisionT91_supported_value _ D hD _ (mobs x) (m x)
        (hversion x hx).1 (hcef x hx) d (hversion x hx).2.1 (hm x hx).1
        (fun ε hε => (hs ε hε).1),
      DecisionT91_supported_value _ D hD _ (mobs x) (m x)
        (hversion x hx).1 (hcef x hx) d' (hversion x hx).2.2 (hm x hx).2
        (fun ε hε => (hs ε hε).2)⟩
  refine ⟨hvalues, ?_⟩
  have hweighted : ∀ x : E,
      mobs x d' * prob μ {ω | X ω = x} = m x d' * prob μ {ω | X ω = x} ∧
      mobs x d * prob μ {ω | X ω = x} = m x d * prob μ {ω | X ω = x} := by
    intro x
    by_cases hx : 0 < prob μ {ω | X ω = x}
    · rw [(hvalues x hx).1, (hvalues x hx).2]
      exact ⟨rfl, rfl⟩
    · have hz : prob μ {ω | X ω = x} = 0 :=
        le_antisymm (le_of_not_gt hx) ENNReal.toReal_nonneg
      simp only [hz, mul_zero, and_self]
  calc
    mean μ (fun ω => Y d' ω - Y d ω) =
        (∑' x : E, m x d' * prob μ {ω | X ω = x}) -
        (∑' x : E, m x d * prob μ {ω | X ω = x}) := hcontrast
    _ = (∑' x : E, mobs x d' * prob μ {ω | X ω = x}) -
        (∑' x : E, mobs x d * prob μ {ω | X ω = x}) :=
      congrArg₂ (fun a b : ℝ => a - b)
        (tsum_congr (fun x => (hweighted x).1.symm))
        (tsum_congr (fun x => (hweighted x).2.symm))

end
end AronowAudit.P001.Wave1
