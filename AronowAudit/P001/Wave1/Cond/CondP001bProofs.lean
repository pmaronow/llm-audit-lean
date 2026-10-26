import AronowAudit.Literature.CondP001b

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
set_option linter.unusedVariables false
set_option pp.universes true

namespace AronowAudit.P001.Wave1

local instance instDecidableCondP001b (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000

/-- Convert the event formulation to a CEF on the enlarged covariate space. -/
lemma CondP001b_enlarge.{u} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (hLit : AronowAudit.Literature.Kallenberg2002Proposition66.{u})
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K L : ℕ}
    (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
    (hX : Measurable X) (hW : Measurable W) (hD : Measurable D)
    (hbinary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (hCI : CI μ X hX W D) (γ : Fin (K+1) → ℝ)
    (hcef : IsCEF μ X D (linearPredictor γ)) :
    IsCEF μ (fun ω => (X ω, W ω)) D (fun xw => linearPredictor γ xw.1) := by
  have hFields : AronowAudit.Literature.eventConditionalIndependence μ
      (MeasurableSpace.comap W inferInstance) (MeasurableSpace.comap X inferInstance)
      (MeasurableSpace.comap D inferInstance) := by
    intro A B hA hB
    rcases hA with ⟨A, hA, rfl⟩
    rcases hB with ⟨B, hB, rfl⟩
    have h1 : Set.indicator (W ⁻¹' A ∩ D ⁻¹' B) (fun _ => (1 : ℝ)) =
        (fun ω => if W ω ∈ A ∧ D ω ∈ B then 1 else 0) := by
      funext ω; simp [Set.indicator]
    have h2 : Set.indicator (W ⁻¹' A) (fun _ => (1 : ℝ)) =
        (fun ω => if W ω ∈ A then 1 else 0) := by
      funext ω; simp [Set.indicator]
    have h3 : Set.indicator (D ⁻¹' B) (fun _ => (1 : ℝ)) =
        (fun ω => if D ω ∈ B then 1 else 0) := by
      funext ω; simp [Set.indicator]
    rw [h1, h2, h3]
    exact hCI A B hA hB
  have hEvent := (hLit Ω mΩ μ _ _ _ hW.comap_le hX.comap_le hD.comap_le).mp hFields
    (D ⁻¹' {1}) ⟨{1}, measurableSet_singleton 1, rfl⟩
  have hInd : (Set.indicator (D ⁻¹' {1}) (fun _ => (1 : ℝ))) =ᵐ[μ] D := by
    filter_upwards [hbinary] with ω hω
    rcases hω with hω | hω <;> simp [Set.indicator, hω]
  have hCE : μ[D | MeasurableSpace.comap (fun ω => (X ω, W ω)) inferInstance] =ᵐ[μ]
      (fun ω => linearPredictor γ (X ω)) := by
    have hJoin : MeasurableSpace.comap (fun ω => (X ω, W ω)) inferInstance =
        MeasurableSpace.comap X inferInstance ⊔ MeasurableSpace.comap W inferInstance :=
      MeasurableSpace.comap_prodMk X W
    rw [hJoin, sup_comm]
    exact (condExp_congr_ae hInd).symm.trans
      (hEvent.trans ((condExp_congr_ae hInd).trans (isCEF_condExp μ X hX D _ hcef).symm))
  refine ⟨hcef.1.comp measurable_fst, hcef.2.1, hcef.2.2.1, ?_⟩
  intro A hA
  calc
    (∫ ω in (fun ω => (X ω, W ω)) ⁻¹' A, D ω ∂μ) =
        ∫ ω in (fun ω => (X ω, W ω)) ⁻¹' A,
          μ[D | MeasurableSpace.comap (fun ω => (X ω, W ω)) inferInstance] ω ∂μ :=
      (setIntegral_condExp (hX.prodMk hW).comap_le hcef.2.1 ⟨A, hA, rfl⟩).symm
    _ = _ := integral_congr_ae (ae_restrict_of_ae hCE)

lemma CondP001b_linear_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (Z : Ω → Fin n → ℝ)
    (hZ : ∀ j, MemLp (fun ω => Z ω j) 2 μ) (a : ℝ) (b : Fin n → ℝ) :
    MemLp (fun ω => a + ∑ j, b j * Z ω j) 2 μ := by
  exact (memLp_const a).add (memLp_finsetSum _ (fun j _ => (hZ j).const_mul (b j)))

/-- The CEF risk identity, with all products justified by square integrability. -/
lemma CondP001b_risk {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → E) (hZ : Measurable Z)
    (Y : Ω → ℝ) (hY : MemLp Y 2 μ) (m : E → ℝ) (hm : IsCEF μ Z Y m)
    (hm2 : MemLp (m ∘ Z) 2 μ) (g : E → ℝ) (hg : Measurable g)
    (hg2 : MemLp (g ∘ Z) 2 μ) :
    mean μ (fun ω => (Y ω - g (Z ω))^2) =
      mean μ (fun ω => (Y ω - m (Z ω))^2) +
      mean μ (fun ω => (g (Z ω) - m (Z ω))^2) := by
  let R := fun ω => Y ω - m (Z ω)
  let T := fun ω => g (Z ω) - m (Z ω)
  have hR : MemLp R 2 μ := hY.sub hm2
  have hT : MemLp T 2 μ := hg2.sub hm2
  obtain ⟨_, hmean, horth⟩ := cef_residual_orthogonality_correction μ Z hZ Y hY m hm hm2
  have ho := horth (fun z => g z - m z) (hg.sub hm.1) hT
  change covariance T R μ = 0 at ho
  rw [covariance_eq_sub hT hR] at ho
  have hzero : mean μ (fun ω => T ω * R ω) = 0 := by
    change mean μ (fun ω => T ω * R ω) - mean μ T * mean μ R = 0 at ho
    change mean μ R = 0 at hmean
    simpa [hmean] using ho
  have hfun : (fun ω => (Y ω - g (Z ω))^2) =
      (fun ω => (R ω)^2 + (T ω)^2 - 2 * (T ω * R ω)) := by
    funext ω; dsimp [R, T]; ring
  rw [hfun]
  unfold mean
  have hsum : Integrable (fun ω => (R ω)^2 + (T ω)^2) μ :=
    hR.integrable_sq.add hT.integrable_sq
  have hmul : Integrable (fun ω => 2 * (T ω * R ω)) μ :=
    (hT.integrable_mul hR).const_mul 2
  change (∫ ω, (R ω)^2 + (T ω)^2 - 2 * (T ω * R ω) ∂μ) = _
  rw [integral_sub hsum hmul,
    integral_add hR.integrable_sq hT.integrable_sq, integral_const_mul]
  change _ + _ - 2 * mean μ (fun ω => T ω * R ω) = _
  rw [hzero]; ring

/-- An invertible Gram matrix makes an almost surely zero linear form trivial. -/
lemma CondP001b_gram_unique {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (Z : Ω → Fin n → ℝ)
    (hZ : ∀ j, MemLp (fun ω => Z ω j) 2 μ)
    (hRank : IsUnit (Matrix.det (fun j k => mean μ (fun ω => Z ω j * Z ω k))))
    (v : Fin n → ℝ) (hv : (fun ω => ∑ j, v j * Z ω j) =ᵐ[μ] 0) : v = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero hRank.ne_zero
  funext j
  change (∑ k, mean μ (fun ω => Z ω j * Z ω k) * v k) = 0
  calc
    (∑ k, mean μ (fun ω => Z ω j * Z ω k) * v k) =
        ∫ ω, ∑ k, (Z ω j * Z ω k) * v k ∂μ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k hk
        exact (integral_mul_const _ _).symm
      · intro k hk
        exact ((hZ j).integrable_mul (hZ k)).mul_const (v k)
    _ = ∫ ω, Z ω j * (∑ k, v k * Z ω k) ∂μ := by
      congr 1; funext ω; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
      intro k hk; ring
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hv] with ω hω
      simp only [Pi.zero_apply] at hω
      simpa only [hω, mul_zero, Pi.zero_apply]

/-- Expand the intercept and the two blocks of augmented coordinates. -/
lemma CondP001b_aug_sum {K L : ℕ} (a : ℝ) (b : Fin K → ℝ) (c : Fin L → ℝ)
    (x : Fin K → ℝ) (w : Fin L → ℝ) :
    (∑ j : Fin (K+L+1), Fin.cases a (Fin.addCases b c) j *
      Fin.cases 1 (Fin.addCases x w) j) = a + (∑ k, b k * x k) + ∑ k, c k * w k := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_add]
  simp
  <;> ring

/-- P001-T18, conditional on the full published sigma-field characterization. -/
theorem placebo_linear_cef_correction_supporting_conditional :
    AronowAudit.P001.placebo_linear_cef_correction_supporting_conditional_statement := by
  intro hLit Ω mΩ μ hμ K L X W D hX hW hD hbinary hSupportD hX2 hW2 hCI γ hcef hRank
  have hc := CondP001b_enlarge hLit μ X W D hX hW hD hbinary hCI γ hcef
  have hD2 : MemLp D 2 μ := by
    apply MemLp.of_bound hD.aestronglyMeasurable 1
    filter_upwards [hbinary] with ω hω
    rcases hω with hω | hω <;> simp [hω]
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

end AronowAudit.P001.Wave1
