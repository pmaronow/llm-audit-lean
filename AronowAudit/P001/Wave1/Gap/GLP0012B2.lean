import AronowAudit.P001.Wave1.Cond.CondP001bProofs
import AronowAudit.P001.Wave1.MarSelection.N1
import AronowAudit.P001.Wave1.MarSelection.N2
import AronowAudit.P001.Wave1.MarSelection.N3

/-! P001-T18: binary CEF augmentation and uniqueness of regression coefficients.

Binary conditional independence preserves the conditional mean when covariates
are added on an arbitrary measurable sample space. The augmented CEF yields
the L² risk identity, and a nonsingular Gram matrix yields uniqueness.
-/

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGLP0012B2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-- Binary event conditional independence preserves the conditional mean when
adding the independent covariates. No support or standard-Borel premise is needed. -/
private lemma placebo_linear_cef_correction_binary_ci_enlarge {Ω E F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (W : Ω → F) (D : Ω → ℝ) (hW : Measurable W) (hD : Measurable D)
    (hbinary : ∀ ω, D ω = 0 ∨ D ω = 1) (hCI : CI μ X hX W D)
    (m : E → ℝ) (hcef : IsCEF μ X D m) :
    IsCEF μ (fun ω => (X ω, W ω)) D (fun xw => m xw.1) := by
  have hCE : μ[D | MeasurableSpace.comap (fun ω => (X ω, W ω)) inferInstance] =ᵐ[μ]
      (fun ω => m (X ω)) :=
    (MarSelection.n3_proof MarSelection.n1_proof MarSelection.n2_proof
      μ X hX W D hW hD (ae_of_all μ hbinary) hCI).trans
        (isCEF_condExp μ X hX D m hcef).symm
  refine ⟨hcef.1.comp measurable_fst, hcef.2.1, hcef.2.2.1, ?_⟩
  intro A hA
  calc
    (∫ ω in (fun ω => (X ω, W ω)) ⁻¹' A, D ω ∂μ) =
        ∫ ω in (fun ω => (X ω, W ω)) ⁻¹' A,
          μ[D | MeasurableSpace.comap (fun ω => (X ω, W ω)) inferInstance] ω ∂μ :=
      (setIntegral_condExp (hX.prodMk hW).comap_le hcef.2.1 ⟨A, hA, rfl⟩).symm
    _ = _ := integral_congr_ae (ae_restrict_of_ae hCE)

/-- Shared support-free core. The augmented CEF gives orthogonality and excess
risk; a nonsingular Gram matrix then identifies all coefficient differences. -/
private lemma placebo_linear_cef_correction_support_free {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
   (hX : Measurable X) (hW : Measurable W) (hD : Measurable D)
   (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (hX2 : ∀ k,MemLp (fun ω => X ω k) 2 μ) (hW2 : ∀ k,MemLp (fun ω => W ω k) 2 μ)
   (hCI : CI μ X hX W D) (γ : Fin (K+1) → ℝ) (hcef : IsCEF μ X D (linearPredictor γ))
   (hRank : IsUnit (Matrix.det ((fun j k : Fin (K+L+1) => mean μ (fun ω =>
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) j)*
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) k))) : Matrix (Fin (K+L+1)) (Fin (K+L+1)) ℝ))) :
   IsCEF μ (fun ω => (X ω,W ω)) D (fun xw => linearPredictor γ xw.1) ∧
   (∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     mean μ (fun ω => (D ω-linearPredictor γ (X ω))^2) ≤
       mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)) ∧
   ∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     (mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)=
       mean μ (fun ω => (D ω-linearPredictor γ (X ω))^2)) ↔
       a=γ 0 ∧ (∀ k,b k=γ k.succ) ∧ (∀ k,c k=0) := by
  have hc := placebo_linear_cef_correction_binary_ci_enlarge μ X hX W D hW hD hbinary hCI (linearPredictor γ) hcef
  have hD2 : MemLp D 2 μ := by
    apply MemLp.of_bound hD.aestronglyMeasurable 1
    filter_upwards with ω
    rcases hbinary ω with hω | hω <;> simp [hω]
  have hm2 : MemLp (fun ω => linearPredictor γ (X ω)) 2 μ :=
    CondP001b_linear_memLp μ X hX2 (γ 0) (fun k => γ k.succ)
  let g (a : ℝ) (b : Fin K → ℝ) (c : Fin L → ℝ)
      (xw : (Fin K → ℝ) × (Fin L → ℝ)) :=
    a + (∑ k, b k * xw.1 k) + ∑ k, c k * xw.2 k
  have hg (a : ℝ) (b : Fin K → ℝ) (c : Fin L → ℝ) : Measurable (g a b c) := by
    dsimp [g]
    fun_prop
  have hg2 (a : ℝ) (b : Fin K → ℝ) (c : Fin L → ℝ) :
      MemLp (fun ω => g a b c (X ω, W ω)) 2 μ :=
    (CondP001b_linear_memLp μ X hX2 a b).add
      (memLp_finsetSum _ (fun k _ => (hW2 k).const_mul (c k)))
  have hrisk (a : ℝ) (b : Fin K → ℝ) (c : Fin L → ℝ) :=
    CondP001b_risk μ (fun ω => (X ω, W ω)) (hX.prodMk hW) D hD2
      (fun xw => linearPredictor γ xw.1) hc hm2 (g a b c) (hg a b c) (hg2 a b c)
  refine ⟨hc, ?_, ?_⟩
  · intro a b c
    change mean μ (fun ω => (D ω - linearPredictor γ (X ω))^2) ≤
      mean μ (fun ω => (D ω - g a b c (X ω, W ω))^2)
    rw [hrisk]
    exact le_add_of_nonneg_right (integral_nonneg (fun ω => sq_nonneg _))
  · intro a b c
    constructor
    · intro heq
      change mean μ (fun ω => (D ω - g a b c (X ω, W ω))^2) = _ at heq
      rw [hrisk] at heq
      have hz : mean μ (fun ω => (g a b c (X ω, W ω) - linearPredictor γ (X ω))^2) = 0 :=
        by linarith
      have hsq := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg
        (g a b c (X ω, W ω) - linearPredictor γ (X ω)))
        ((hg2 a b c).sub hm2).integrable_sq).mp hz
      let Z : Ω → Fin (K+L+1) → ℝ :=
        fun ω => Fin.cases 1 (Fin.addCases (X ω) (W ω))
      let v : Fin (K+L+1) → ℝ := Fin.cases (a - γ 0)
        (Fin.addCases (fun k => b k - γ k.succ) c)
      have hZ (j : Fin (K+L+1)) : MemLp (fun ω => Z ω j) 2 μ := by
        refine Fin.cases ?_ (fun i => ?_) j
        · exact memLp_const 1
        · refine Fin.addCases (fun k => ?_) (fun k => ?_) i
          · simpa [Z] using hX2 k
          · simpa [Z] using hW2 k
      have hform (ω : Ω) : (∑ j, v j * Z ω j) =
          g a b c (X ω, W ω) - linearPredictor γ (X ω) := by
        dsimp [v, Z]
        rw [CondP001b_aug_sum]
        simp only [g, linearPredictor, sub_mul, Finset.sum_sub_distrib]
        ring
      have hv : (fun ω => ∑ j, v j * Z ω j) =ᵐ[μ] 0 := by
        filter_upwards [hsq] with ω hω
        rw [hform]
        change (g a b c (X ω, W ω) - linearPredictor γ (X ω))^2 = 0 at hω
        exact sq_eq_zero_iff.mp hω
      have hv0 : v = 0 := CondP001b_gram_unique μ Z hZ hRank v hv
      have ha := congrFun hv0 0
      have hb (k : Fin K) := congrFun hv0 (Fin.castAdd L k).succ
      have hc' (k : Fin L) := congrFun hv0 (Fin.natAdd K k).succ
      simp only [v, Fin.cases_zero, Pi.zero_apply] at ha
      simp only [v, Fin.cases_succ, Fin.addCases_left, Pi.zero_apply] at hb
      simp only [v, Fin.cases_succ, Fin.addCases_right, Pi.zero_apply] at hc'
      exact ⟨sub_eq_zero.mp ha, fun k => sub_eq_zero.mp (hb k), hc'⟩
    · rintro ⟨rfl, hb, hc'⟩
      have hsame : g (γ 0) b c = (fun xw => linearPredictor γ xw.1) := by
        funext xw
        simp [g, linearPredictor, hb, hc']
      change mean μ (fun ω => (D ω - g (γ 0) b c (X ω, W ω))^2) = _
      rw [hsame]

theorem placebo_linear_cef_correction_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
   (hX : Measurable X) (hW : Measurable W) (hD : Measurable D)
   (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (hSupportD : 0 < prob μ {ω | D ω=1} ∧ prob μ {ω | D ω=1} < 1)
   (hX2 : ∀ k,MemLp (fun ω => X ω k) 2 μ) (hW2 : ∀ k,MemLp (fun ω => W ω k) 2 μ)
   (hCI : CI μ X hX W D) (γ : Fin (K+1) → ℝ) (hcef : IsCEF μ X D (linearPredictor γ))
   (hRank : IsUnit (Matrix.det ((fun j k : Fin (K+L+1) => mean μ (fun ω =>
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) j)*
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) k))) : Matrix (Fin (K+L+1)) (Fin (K+L+1)) ℝ))) :
   IsCEF μ (fun ω => (X ω,W ω)) D (fun xw => linearPredictor γ xw.1) ∧
   (∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     mean μ (fun ω => (D ω-linearPredictor γ (X ω))^2) ≤
       mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)) ∧
   ∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     (mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)=
       mean μ (fun ω => (D ω-linearPredictor γ (X ω))^2)) ↔
       a=γ 0 ∧ (∀ k,b k=γ k.succ) ∧ (∀ k,c k=0) := by
  exact placebo_linear_cef_correction_support_free μ X W D hX hW hD hbinary hX2 hW2 hCI γ hcef hRank

theorem placebo_zero_coefficients_unique_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
   (hX : Measurable X) (hW : Measurable W) (hD : Measurable D)
   (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (hX2 : ∀ k,MemLp (fun ω => X ω k) 2 μ) (hW2 : ∀ k,MemLp (fun ω => W ω k) 2 μ)
   (hCI : CI μ X hX W D) (γ : Fin (K+1) → ℝ) (hcef : IsCEF μ X D (linearPredictor γ))
   (hRank : IsUnit (Matrix.det ((fun j k : Fin (K+L+1) => mean μ (fun ω =>
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) j)*
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) k))) : Matrix (Fin (K+L+1)) (Fin (K+L+1)) ℝ))) :
   ∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     (mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)=
       mean μ (fun ω => (D ω-linearPredictor γ (X ω))^2)) ↔
       a=γ 0 ∧ (∀ k,b k=γ k.succ) ∧ (∀ k,c k=0) := by
  exact (placebo_linear_cef_correction_support_free μ X W D hX hW hD hbinary hX2 hW2 hCI γ hcef hRank).2.2

end
end AronowAudit.P001.Wave1
