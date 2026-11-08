import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! Proofs of P001-T100 and P001-T12. -/

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Matrix
noncomputable section
local instance GP0011B1b_instDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-! P001-T100: equality of weighted outcome laws, on arbitrary Ω. -/

private lemma GP0011B1b_t100_propensity_bounds {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (D : Ω → ℝ) (hbinary : ∀ ω, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : IsCEF μ X D p) :
    ∀ᵐ ω ∂μ, 0 ≤ p (X ω) ∧ p (X ω) ≤ 1 := by
  have hD0 : ∀ᵐ ω ∂μ, 0 ≤ D ω := by
    filter_upwards with ω
    rcases hbinary ω with h | h <;> simp [h]
  have hD1 : ∀ᵐ ω ∂μ, D ω ≤ 1 := by
    filter_upwards with ω
    rcases hbinary ω with h | h <;> simp [h]
  have hpCE : (p ∘ X) =ᵐ[μ] μ[D | (MeasurableSpace.comap X inferInstance)] := isCEF_condExp μ X hX D p hp
  have hCE0 : ∀ᵐ ω ∂μ, 0 ≤ μ[D | (MeasurableSpace.comap X inferInstance)] ω := condExp_nonneg hD0
  have hCE1 : ∀ᵐ ω ∂μ, μ[D | (MeasurableSpace.comap X inferInstance)] ω ≤ 1 :=
    condExp_le_nonneg_const (by norm_num : (0 : ℝ) ≤ 1) hD1
  filter_upwards [hpCE, hCE0, hCE1] with ω hpω h0ω h1ω
  change p (X ω) = _ at hpω
  rw [hpω]
  exact ⟨h0ω, h1ω⟩

private lemma GP0011B1b_t100_weighted_apply {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (w : Ω → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ w ω) (S : Set Ω) (hS : MeasurableSet S) :
    (μ.withDensity (fun ω => ENNReal.ofReal (w ω))) S =
      ENNReal.ofReal (∫ ω in S, w ω ∂μ) := by
  rw [withDensity_apply _ hS]
  exact (ofReal_integral_eq_lintegral_ofReal hw.integrableOn
    (ae_restrict_of_ae hw0)).symm

/-- Transport a real integral through a weighted pushforward. The theorem applies
to all measurable real test functions, and so avoids an L2 restriction. -/
private lemma GP0011B1b_t100_weighted_map_integral {Ω F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace F]
    (μ : Measure Ω) (w : Ω → ℝ) (hw : Measurable w)
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ w ω) (U : Ω → F) (hU : Measurable U)
    (v : F → ℝ) (hv : Measurable v) :
    (∫ z, v z ∂(μ.withDensity (fun ω => ENNReal.ofReal (w ω))).map U) =
      ∫ ω, w ω * v (U ω) ∂μ := by
  rw [integral_map_of_stronglyMeasurable hU hv.stronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    hw.ennreal_ofReal (ae_of_all μ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hw0] with ω hω
  simp only [ENNReal.toReal_ofReal hω, smul_eq_mul]

/-- The event-factorization definition of CI gives equality of the two
nonnegative measures on outcome space weighted by D and by p(X). -/
private lemma GP0011B1b_t100_binary_weighted_law {Ω E F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (U : Ω → F) (hU : Measurable U) (D : Ω → ℝ)
    (hbinary : ∀ ω, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : IsCEF μ X D p) (hCI : CI μ X hX U D) :
    (μ.withDensity (fun ω => ENNReal.ofReal (D ω))).map U =
      (μ.withDensity (fun ω => ENNReal.ofReal (p (X ω)))).map U := by
  have hG : (MeasurableSpace.comap X inferInstance) ≤ (inferInstance : MeasurableSpace Ω) := hX.comap_le
  have hXm : Measurable[(MeasurableSpace.comap X inferInstance)] X := measurable_iff_comap_le.mpr le_rfl
  have hpm : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] (p ∘ X) := (hp.1.comp hXm).stronglyMeasurable
  have hpCE : (p ∘ X) =ᵐ[μ] μ[D | (MeasurableSpace.comap X inferInstance)] := isCEF_condExp μ X hX D p hp
  have hD0 : ∀ᵐ ω ∂μ, 0 ≤ D ω := by
    filter_upwards with ω
    rcases hbinary ω with h | h <;> simp [h]
  have hp0 : ∀ᵐ ω ∂μ, 0 ≤ p (X ω) :=
    (GP0011B1b_t100_propensity_bounds μ X hX D hbinary p hp).mono (fun _ h => h.1)
  apply Measure.ext
  intro A hA
  have hUA : MeasurableSet (U ⁻¹' A) := hU hA
  let u : Ω → ℝ := (U ⁻¹' A).indicator (fun _ => 1)
  have hum : Measurable u := measurable_const.indicator hUA
  have hui : Integrable u μ := (integrable_const (1 : ℝ)).indicator hUA
  have hub : ∀ᵐ ω ∂μ, ‖u ω‖ ≤ 1 := by
    filter_upwards with ω
    by_cases h : U ω ∈ A <;> simp [u, h]
  have hud : Integrable (fun ω => u ω * D ω) μ :=
    hp.2.1.bdd_mul hum.aestronglyMeasurable hub
  have hpu : Integrable (fun ω => p (X ω) * u ω) μ :=
    hp.2.2.1.mul_bdd hum.aestronglyMeasurable hub
  have hfactor : μ[(fun ω => u ω * D ω) | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ]
      (fun ω => μ[u | (MeasurableSpace.comap X inferInstance)] ω * μ[D | (MeasurableSpace.comap X inferInstance)] ω) := by
    have hc := hCI A ({1} : Set ℝ) hA (measurableSet_singleton 1)
    convert hc using 1 <;> congr 1
    · funext ω
      by_cases hAω : U ω ∈ A <;>
        rcases hbinary ω with h | h <;> simp [u, hAω, h]
    · funext ω
      congr 1 <;> congr 1 <;> funext t
      rcases hbinary t with h | h <;> simp [h]
  have hpull : μ[(fun ω => p (X ω) * u ω) | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ]
      (fun ω => p (X ω) * μ[u | (MeasurableSpace.comap X inferInstance)] ω) :=
    condExp_mul_of_stronglyMeasurable_left hpm hpu hui
  have hCEeq : μ[(fun ω => u ω * D ω) | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ]
      μ[(fun ω => p (X ω) * u ω) | (MeasurableSpace.comap X inferInstance)] := by
    filter_upwards [hfactor, hpCE, hpull] with ω hfω hpω huω
    change p (X ω) = _ at hpω
    rw [hfω, huω, ← hpω, mul_comm]
  have hint : (∫ ω, u ω * D ω ∂μ) = ∫ ω, p (X ω) * u ω ∂μ := by
    calc
      _ = ∫ ω, μ[(fun ω => u ω * D ω) | (MeasurableSpace.comap X inferInstance)] ω ∂μ := (integral_condExp hG).symm
      _ = ∫ ω, μ[(fun ω => p (X ω) * u ω) | (MeasurableSpace.comap X inferInstance)] ω ∂μ := integral_congr_ae hCEeq
      _ = _ := integral_condExp hG
  have hset : (∫ ω in U ⁻¹' A, D ω ∂μ) = ∫ ω in U ⁻¹' A, p (X ω) ∂μ := by
    calc
      _ = ∫ ω, u ω * D ω ∂μ := by
        rw [← integral_indicator hUA]
        apply integral_congr_ae
        filter_upwards with ω
        by_cases h : U ω ∈ A <;> simp [u, h]
      _ = ∫ ω, p (X ω) * u ω ∂μ := hint
      _ = _ := by
        rw [← integral_indicator hUA]
        apply integral_congr_ae
        filter_upwards with ω
        by_cases h : U ω ∈ A <;> simp [u, h]
  rw [Measure.map_apply hU hA, Measure.map_apply hU hA,
    GP0011B1b_t100_weighted_apply μ D hp.2.1 hD0 _ hUA,
    GP0011B1b_t100_weighted_apply μ (fun ω => p (X ω)) hp.2.2.1 hp0 _ hUA, hset]

theorem att_normalized_propensity_mean_proof {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1) (hD : Measurable D)
   (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ) (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (hpD : 0 < prob μ {ω | D ω=1}) (p : E → ℝ) (hp : IsCEF μ X D p)
   (hCI : CI μ X hX (fun ω => (Y0 ω,Y1 ω)) D) :
   mean μ (p ∘ X)=prob μ {ω | D ω=1} ∧
   mean μ (fun ω => p (X ω)*(Y1 ω-Y0 ω))=mean μ (fun ω => D ω*(Y1 ω-Y0 ω)) ∧
   (∫ ω in {ω | D ω=1},Y1 ω-Y0 ω ∂μ)/prob μ {ω | D ω=1} =
     mean μ (fun ω => p (X ω)*(Y1 ω-Y0 ω))/mean μ (p ∘ X) := by
  let U : Ω → ℝ × ℝ := fun ω => (Y0 ω, Y1 ω)
  have hU : Measurable U := h0.prodMk h1
  let v : ℝ × ℝ → ℝ := fun z => z.2 - z.1
  have hv : Measurable v := measurable_snd.sub measurable_fst
  have hbounds := GP0011B1b_t100_propensity_bounds μ X hX D hbinary p hp
  have hp0 : ∀ᵐ ω ∂μ, 0 ≤ p (X ω) := hbounds.mono (fun _ h => h.1)
  have hD0 : ∀ᵐ ω ∂μ, 0 ≤ D ω := by
    filter_upwards with ω
    rcases hbinary ω with h | h <;> simp [h]
  -- These integrability facts also verify that the displayed means are actual L1 means.
  have hτ : Integrable (fun ω => Y1 ω - Y0 ω) μ := hi1.sub hi0
  have hpτ : Integrable (fun ω => p (X ω) * (Y1 ω - Y0 ω)) μ := by
    apply hτ.bdd_mul (c := 1) (hp.1.comp hX).aestronglyMeasurable
    filter_upwards [hbounds] with ω hω
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2
  have hDτ : Integrable (fun ω => D ω * (Y1 ω - Y0 ω)) μ := by
    apply hτ.bdd_mul (c := 1) hD.aestronglyMeasurable
    filter_upwards with ω
    rcases hbinary ω with h | h <;> simp [h]
  have hlaw := GP0011B1b_t100_binary_weighted_law μ X hX U hU D hbinary p hp hCI
  have hweighted : mean μ (fun ω => p (X ω) * (Y1 ω - Y0 ω)) =
      mean μ (fun ω => D ω * (Y1 ω - Y0 ω)) := by
    unfold mean
    calc
      _ = ∫ z, v z ∂(μ.withDensity (fun ω => ENNReal.ofReal (p (X ω)))).map U :=
        (GP0011B1b_t100_weighted_map_integral μ (p ∘ X) (hp.1.comp hX) hp0 U hU v hv).symm
      _ = ∫ z, v z ∂(μ.withDensity (fun ω => ENNReal.ofReal (D ω))).map U := by rw [hlaw]
      _ = _ := GP0011B1b_t100_weighted_map_integral μ D hD hD0 U hU v hv
  have hS : MeasurableSet {ω | D ω = 1} := hD (measurableSet_singleton 1)
  have hDindicator : D = {ω | D ω = 1}.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    rcases hbinary ω with h | h <;> simp [Set.indicator, h]
  have hmeanD : mean μ D = prob μ {ω | D ω = 1} := by
    calc
      _ = ∫ ω, {ω | D ω = 1}.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
        congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) hDindicator
      _ = _ := by
        rw [integral_indicator_const (1 : ℝ) hS]
        simp only [smul_eq_mul, mul_one, prob, Measure.real]
  have hden : mean μ (p ∘ X) = prob μ {ω | D ω = 1} := by
    have hcef : mean μ D = mean μ (p ∘ X) := by
      simpa only [mean, Set.preimage_univ, setIntegral_univ, Function.comp_apply] using
        hp.2.2.2 Set.univ MeasurableSet.univ
    exact hcef.symm.trans hmeanD
  have hnumerator : (∫ ω in {ω | D ω = 1}, Y1 ω - Y0 ω ∂μ) =
      mean μ (fun ω => D ω * (Y1 ω - Y0 ω)) := by
    rw [← integral_indicator hS]
    unfold mean
    apply integral_congr_ae
    filter_upwards with ω
    rcases hbinary ω with h | h <;> simp [Set.indicator, h]
  exact ⟨hden, hweighted, by rw [hnumerator, ← hweighted, hden]⟩

example : type_of% @AronowAudit.P001.att_normalized_propensity_mean :=
  att_normalized_propensity_mean_proof

/-! P001-T12: apply the scalar residual square to each test vector a. -/

private lemma GP0011B1b_t12_linear_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {τ : ℕ} (f : Ω → Fin τ → ℝ)
    (hf : ∀ j, MemLp (fun ω => f ω j) 2 μ) (a : Fin τ → ℝ) :
    MemLp (fun ω => ∑ j, a j * f ω j) 2 μ := by
  exact memLp_finsetSum Finset.univ (fun j _ => (hf j).const_mul (a j))

/-- Expand the product of two finite L2 linear combinations under the integral.
Every summand is L1 by the L2 Holder inequality. -/
private lemma GP0011B1b_t12_mean_linear_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {τ υ : ℕ} (f : Ω → Fin τ → ℝ) (g : Ω → Fin υ → ℝ)
    (hf : ∀ j, MemLp (fun ω => f ω j) 2 μ)
    (hg : ∀ k, MemLp (fun ω => g ω k) 2 μ)
    (a : Fin τ → ℝ) (b : Fin υ → ℝ) :
    mean μ (fun ω => (∑ j, a j * f ω j) * (∑ k, b k * g ω k)) =
      ∑ j, ∑ k, a j * mean μ (fun ω => f ω j * g ω k) * b k := by
  have hterm (j : Fin τ) (k : Fin υ) :
      Integrable (fun ω => a j * (f ω j * g ω k) * b k) μ :=
    (((hf j).integrable_mul (hg k)).const_mul (a j)).mul_const (b k)
  have hrow (j : Fin τ) :
      Integrable (fun ω => ∑ k, a j * (f ω j * g ω k) * b k) μ := by
    exact integrable_finsetSum Finset.univ (fun k _ => hterm j k)
  have hexpand (ω : Ω) :
      (∑ j, a j * f ω j) * (∑ k, b k * g ω k) =
        ∑ j, ∑ k, a j * (f ω j * g ω k) * b k := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold mean
  simp_rw [hexpand]
  rw [integral_finsetSum Finset.univ (fun j _ => hrow j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _ => hterm j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_mul_const, integral_const_mul]

private lemma GP0011B1b_t12_centered_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {τ : ℕ} (ψ : Ω → Fin τ → ℝ)
    (hψ0 : ∀ j, mean μ (fun ω => ψ ω j) = 0) (j k : Fin τ) :
    covarianceMatrix μ ψ j k = mean μ (fun ω => ψ ω j * ψ ω k) := by
  change (∫ ω, (ψ ω j - mean μ (fun ω => ψ ω j)) *
    (ψ ω k - mean μ (fun ω => ψ ω k)) ∂μ) = _
  rw [hψ0 j, hψ0 k]
  simp only [sub_zero, mean]

theorem regular_influence_information_lower_bound_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {τ : ℕ} (s ψ : Ω → Fin τ → ℝ)
   (hs2 : ∀ j,MemLp (fun ω => s ω j) 2 μ) (hψ2 : ∀ j,MemLp (fun ω => ψ ω j) 2 μ)
   (hs0 : ∀ j,mean μ (fun ω => s ω j)=0) (hψ0 : ∀ j,mean μ (fun ω => ψ ω j)=0)
   (I : Matrix (Fin τ) (Fin τ) ℝ)
   (hI : ∀ j k,I j k=mean μ (fun ω => s ω j*s ω k)) (hpos : I.PosDef)
   (hregular : ∀ j k,mean μ (fun ω => ψ ω j*s ω k)=if j=k then 1 else 0) :
   ∀ a : Fin τ → ℝ,0 ≤ ∑ j,∑ k,a j*(covarianceMatrix μ ψ j k-I⁻¹ j k)*a k := by
  intro a
  -- b is the coefficient vector of the score projection in the direction a.
  let b : Fin τ → ℝ := I⁻¹ *ᵥ a
  have hdet : IsUnit I.det := (Matrix.isUnit_iff_isUnit_det I).mp hpos.isUnit
  have hIb : I *ᵥ b = a := by
    dsimp only [b]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv I hdet, Matrix.one_mulVec]
  have hIb_coord (j : Fin τ) : (∑ k, I j k * b k) = a j := by
    exact congrFun hIb j
  let P : Ω → ℝ := fun ω => ∑ j, a j * ψ ω j
  let S : Ω → ℝ := fun ω => ∑ j, b j * s ω j
  have hP2 : MemLp P 2 μ := GP0011B1b_t12_linear_memLp μ ψ hψ2 a
  have hS2 : MemLp S 2 μ := GP0011B1b_t12_linear_memLp μ s hs2 b
  have hPPi : Integrable (fun ω => P ω * P ω) μ := hP2.integrable_mul hP2
  have hPSi : Integrable (fun ω => P ω * S ω) μ := hP2.integrable_mul hS2
  have hSSi : Integrable (fun ω => S ω * S ω) μ := hS2.integrable_mul hS2
  have hPP : mean μ (fun ω => P ω * P ω) =
      ∑ j, ∑ k, a j * covarianceMatrix μ ψ j k * a k := by
    change mean μ (fun ω => (∑ j, a j * ψ ω j) * (∑ k, a k * ψ ω k)) = _
    rw [GP0011B1b_t12_mean_linear_mul μ ψ ψ hψ2 hψ2 a a]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [GP0011B1b_t12_centered_covariance μ ψ hψ0 j k]
  have hPS : mean μ (fun ω => P ω * S ω) = ∑ j, a j * b j := by
    change mean μ (fun ω => (∑ j, a j * ψ ω j) * (∑ k, b k * s ω k)) = _
    rw [GP0011B1b_t12_mean_linear_mul μ ψ s hψ2 hs2 a b]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [hregular]
    calc
      (∑ k, a j * (if j = k then 1 else 0) * b k) =
          ∑ k, if k = j then a j * b j else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases h : k = j
        · subst k
          simp
        · simp [h, Ne.symm h]
      _ = _ := by simp
  have hSS : mean μ (fun ω => S ω * S ω) = ∑ j, a j * b j := by
    change mean μ (fun ω => (∑ j, b j * s ω j) * (∑ k, b k * s ω k)) = _
    rw [GP0011B1b_t12_mean_linear_mul μ s s hs2 hs2 b b]
    calc
      (∑ j, ∑ k, b j * mean μ (fun ω => s ω j * s ω k) * b k) =
          ∑ j, b j * (∑ k, I j k * b k) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [hI j k]
        ring
      _ = ∑ j, b j * a j := by simp_rw [hIb_coord]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hJ : (∑ j, ∑ k, a j * I⁻¹ j k * a k) = ∑ j, a j * b j := by
    apply Finset.sum_congr rfl
    intro j _
    change (∑ k, a j * I⁻¹ j k * a k) = a j * (∑ k, I⁻¹ j k * a k)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hquadratic : (∑ j, ∑ k, a j * (covarianceMatrix μ ψ j k - I⁻¹ j k) * a k) =
      (∑ j, ∑ k, a j * covarianceMatrix μ ψ j k * a k) - ∑ j, a j * b j := by
    calc
      _ = (∑ j, ∑ k, a j * covarianceMatrix μ ψ j k * a k) -
          (∑ j, ∑ k, a j * I⁻¹ j k * a k) := by
        simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
      _ = _ := by rw [hJ]
  have hresidual : mean μ (fun ω => (P ω - S ω)^2) =
      mean μ (fun ω => P ω * P ω) -
        2 * mean μ (fun ω => P ω * S ω) + mean μ (fun ω => S ω * S ω) := by
    unfold mean
    calc
      _ = ∫ ω, (P ω * P ω - 2 * (P ω * S ω)) + S ω * S ω ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        ring
      _ = _ := by
        rw [integral_add (f := fun ω => P ω * P ω - 2 * (P ω * S ω))
          (hPPi.sub (hPSi.const_mul 2)) hSSi,
          integral_sub (f := fun ω => P ω * P ω) (g := fun ω => 2 * (P ω * S ω))
            hPPi (hPSi.const_mul 2), integral_const_mul]
  calc
    0 ≤ mean μ (fun ω => (P ω - S ω)^2) := integral_nonneg (fun ω => sq_nonneg _)
    _ = _ := by
      rw [hresidual, hPP, hPS, hSS, hquadratic]
      ring

example : type_of% @AronowAudit.P001.regular_influence_information_lower_bound :=
  regular_influence_information_lower_bound_proof

end
end AronowAudit.P001.Wave1
