import AronowAudit.P001.Wave1.Gap.GP0014B1
import Mathlib.Topology.Instances.Matrix

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableWLP001dB1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! P001-T6: the explicitly specified conditional trace.
The matrix, gating, and conditional-expansion arguments give the diagonal
formula for the CEF rather than choosing an existential version. -/

private def wlp001dB1T6_good {n K : ℕ} (c : ℝ) (P : Matrix (Fin n) (Fin K) ℝ) : Prop :=
  ∀ b : Fin K → ℝ, c*(∑ k, (b k)^2) ≤ (∑ i, (P.mulVec b i)^2)/(n : ℝ)

private lemma wlp001dB1T6_good_measurable {n K : ℕ} (c : ℝ) :
    MeasurableSet {P : Matrix (Fin n) (Fin K) ℝ | wlp001dB1T6_good c P} := by
  apply IsClosed.measurableSet
  simp only [wlp001dB1T6_good, Set.setOf_forall]
  apply isClosed_iInter
  intro b
  exact isClosed_le continuous_const (by unfold Matrix.mulVec dotProduct; fun_prop)

private lemma wlp001dB1T6_inverse_measurable {K : ℕ} :
    Measurable (fun Q : Matrix (Fin K) (Fin K) ℝ => Q⁻¹) := by
  have hi : (fun Q : Matrix (Fin K) (Fin K) ℝ => Q⁻¹) =
      fun Q => Q.det⁻¹ • Q.adjugate := by
    funext Q
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [hi]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

private def wlp001dB1T6_weights {n K : ℕ} (c : ℝ) (P : Matrix (Fin n) (Fin K) ℝ) :
    Matrix (Fin K) (Fin n) ℝ :=
  if wlp001dB1T6_good c P then (P.transpose * P)⁻¹ * P.transpose else 0

private lemma wlp001dB1T6_weights_measurable {n K : ℕ} (c : ℝ) :
    Measurable (wlp001dB1T6_weights (n := n) (K := K) c) := by
  apply Measurable.ite (wlp001dB1T6_good_measurable c) _ measurable_const
  have hQ : Continuous (fun P : Matrix (Fin n) (Fin K) ℝ => P.transpose * P) := by
    exact continuous_id.matrix_transpose.matrix_mul continuous_id
  have hI := wlp001dB1T6_inverse_measurable.comp hQ.measurable
  apply Measurable.of_eval
  intro k
  apply Measurable.of_eval
  intro i
  change Measurable (fun P : Matrix (Fin n) (Fin K) ℝ => ∑ j, ((P.transpose * P)⁻¹) k j * P i j)
  exact Finset.measurable_sum _ (fun j _ =>
    ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hI)).mul
      ((measurable_pi_apply j).comp (measurable_pi_apply i)))

private lemma wlp001dB1T6_row_norm {n K : ℕ} (hn : 0 < n)
    (c : ℝ) (hc : 0 < c) (P : Matrix (Fin n) (Fin K) ℝ)
    (hg : wlp001dB1T6_good c P) (k : Fin K) :
    (∑ i, (wlp001dB1T6_weights c P k i)^2) = (P.transpose * P)⁻¹ k k ∧
    0 ≤ (P.transpose * P)⁻¹ k k ∧
    (P.transpose * P)⁻¹ k k ≤ 1/(c*(n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hu := gram_unit_of_lower_bound hn P c hc hg
  let Q := P.transpose * P
  have hQ : Q.transpose = Q := by simp [Q, Matrix.transpose_mul]
  have hI : Q⁻¹.transpose = Q⁻¹ := by rw [Matrix.transpose_nonsing_inv, hQ]
  let A := Q⁻¹ * P.transpose
  have hAA : A * A.transpose = Q⁻¹ := by
    dsimp [A]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hI]
    calc
      (Q⁻¹ * P.transpose) * (P * Q⁻¹) = (Q⁻¹ * Q) * Q⁻¹ := by
        dsimp [Q]
        simp only [Matrix.mul_assoc]
      _ = Q⁻¹ := by rw [Matrix.nonsing_inv_mul Q hu, Matrix.one_mul]
  have hrowA : (∑ i, (A k i)^2) = Q⁻¹ k k := by
    have he := congrArg (fun M : Matrix (Fin K) (Fin K) ℝ => M k k) hAA
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using he
  have hrow : (∑ i, (wlp001dB1T6_weights c P k i)^2) = Q⁻¹ k k := by
    simpa only [wlp001dB1T6_weights, if_pos hg, A, Q] using hrowA
  let e : Fin K → ℝ := Pi.single k 1
  let w : Fin K → ℝ := Q⁻¹.mulVec e
  have hwk : w k = Q⁻¹ k k := by simp [w, e, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hQw : Q.mulVec w = e := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q hu, Matrix.one_mulVec]
  have henergy : (∑ i, (P.mulVec w i)^2) = Q⁻¹ k k := by
    rw [← gram_quadratic_form]
    change dotProduct w (Q.mulVec w) = _
    rw [hQw]
    simpa [e, dotProduct, Pi.single_apply] using hwk
  have hlower : c*(n : ℝ)*(∑ j, (w j)^2) ≤ Q⁻¹ k k := by
    have h := (le_div_iff₀ hnR).mp (hg w)
    rw [henergy] at h
    nlinarith
  have hsingle : (Q⁻¹ k k)^2 ≤ ∑ j, (w j)^2 := by
    rw [← hwk]
    exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have hnonneg : 0 ≤ Q⁻¹ k k := by rw [← hrow]; positivity
  refine ⟨hrow, hnonneg, ?_⟩
  apply (le_div_iff₀ (mul_pos hc hnR)).mpr
  have hsq : c*(n : ℝ)*(Q⁻¹ k k)^2 ≤ Q⁻¹ k k :=
    (mul_le_mul_of_nonneg_left hsingle (mul_pos hc hnR).le).trans hlower
  by_cases hd : Q⁻¹ k k = 0
  · rw [hd]; norm_num
  · have hp : 0 < Q⁻¹ k k := lt_of_le_of_ne hnonneg (Ne.symm hd)
    nlinarith

private lemma wlp001dB1T6_weight_bound {n K : ℕ} (hn : 0 < n)
    (c : ℝ) (hc : 0 < c) (P : Matrix (Fin n) (Fin K) ℝ) (k : Fin K) (i : Fin n) :
    |wlp001dB1T6_weights c P k i| ≤ Real.sqrt (1/(c*(n : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hg : wlp001dB1T6_good c P
  · have h := wlp001dB1T6_row_norm hn c hc P hg k
    have hs : (wlp001dB1T6_weights c P k i)^2 ≤ 1/(c*(n : ℝ)) := by
      exact (Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)).trans
        (h.1.trans_le h.2.2)
    exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp (by
      simpa only [sq_abs, Real.sq_sqrt (by positivity : 0 ≤ 1/(c*(n : ℝ)))] using hs)
  · simp only [wlp001dB1T6_weights, if_neg hg, Matrix.zero_apply, abs_zero]
    exact Real.sqrt_nonneg _


private lemma wlp001dB1T6_cef_mul {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Ω → E) (hP : Measurable P)
    (Y : Ω → ℝ) (m g : E → ℝ) (h : IsCEF μ P Y m) (hg : Measurable g)
    (hY : Integrable (fun ω => g (P ω)*Y ω) μ)
    (hm : Integrable (fun ω => g (P ω)*m (P ω)) μ) :
    IsCEF μ P (fun ω => g (P ω)*Y ω) (fun p => g p*m p) := by
  have hPm : Measurable[MeasurableSpace.comap P inferInstance] P :=
    measurable_iff_comap_le.mpr le_rfl
  have hCE := condExp_mul_of_stronglyMeasurable_left (hg.comp hPm).stronglyMeasurable hY h.2.1
  simp only [Pi.mul_def, Function.comp_def] at hCE
  have hCE' := isCEF_condExp μ P hP Y m h
  refine ⟨hg.mul h.1, hY, hm, ?_⟩
  intro B hB
  rw [← setIntegral_condExp hP.comap_le hY ⟨B, hB, rfl⟩]
  apply setIntegral_congr_ae (hB.preimage hP)
  filter_upwards [hCE, hCE'] with ω hω hω' _
  change μ[(fun ω => g (P ω)*Y ω) | MeasurableSpace.comap P inferInstance] ω = _
  simpa only [Function.comp_apply, ← hω'] using hω

private lemma wlp001dB1T6_cef_sum {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Fintype ι] (μ : Measure Ω) (P : Ω → E) (Y : ι → Ω → ℝ) (m : ι → E → ℝ)
    (h : ∀ i, IsCEF μ P (Y i) (m i)) :
    IsCEF μ P (fun ω => ∑ i, Y i ω) (fun p => ∑ i, m i p) := by
  refine ⟨Finset.measurable_sum _ (fun i _ => (h i).1),
    integrable_finsetSum _ (fun i _ => (h i).2.1),
    integrable_finsetSum _ (fun i _ => (h i).2.2.1), ?_⟩
  intro B hB
  change (∫ ω in P ⁻¹' B, ∑ i, Y i ω ∂μ) = ∫ ω in P ⁻¹' B, ∑ i, m i (P ω) ∂μ
  rw [integral_finsetSum _ (fun i _ => (h i).2.1.integrableOn),
    integral_finsetSum _ (fun i _ => show Integrable (fun ω => m i (P ω)) (μ.restrict (P ⁻¹' B)) from (h i).2.2.1.integrableOn)]
  exact Finset.sum_congr rfl (fun i _ => (h i).2.2.2 B hB)

private lemma wlp001dB1T6_gram_inverse {n K : ℕ} (hn : 0 < n)
    (c : ℝ) (hc : 0 < c) (P : Matrix (Fin n) (Fin K) ℝ)
    (hg : wlp001dB1T6_good c P) :
    (fixedDesignGram P)⁻¹ = (n : ℝ) • (P.transpose * P)⁻¹ := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let instInvertibleScaleWLP001dB1 : Invertible ((n : ℝ)⁻¹) := invertibleOfNonzero (inv_ne_zero hnR)
  rw [fixedDesignGram, Matrix.inv_smul _ _ (gram_unit_of_lower_bound hn P c hc hg)]
  simp only [invOf_eq_inv, inv_inv]

theorem random_design_noise_conditional_trace {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {n K : ℕ} (hn : 0 < n)
  (P : Ω → Matrix (Fin n) (Fin K) ℝ) (hP : Measurable P)
  (u : Ω → Fin n → ℝ) (hu2 : ∀ i, MemLp (fun ω => u ω i) 2 μ)
  (hu0 : ∀ i, IsCEF μ P (fun ω => u ω i) (fun _ => 0))
  (huncorr : ∀ i j, i ≠ j → IsCEF μ P (fun ω => u ω i * u ω j) (fun _ => 0))
  (v : Matrix (Fin n) (Fin K) ℝ → Fin n → ℝ)
  (hv : ∀ i, IsCEF μ P (fun ω => (u ω i)^2) (fun p => v p i))
  (V c : ℝ) (hV : 0 ≤ V) (hc : 0 < c)
  (hvar : ∀ᵐ ω ∂μ, ∀ i, v (P ω) i ≤ V) :
  let good := fun p : Matrix (Fin n) (Fin K) ℝ =>
    ∀ b : Fin K → ℝ, c * (∑ k, (b k)^2) ≤ (∑ i, (p.mulVec b i)^2) / (n : ℝ)
  let A := fun p : Matrix (Fin n) (Fin K) ℝ => (p.transpose * p)⁻¹ * p.transpose
  let q := fun p : Matrix (Fin n) (Fin K) ℝ =>
    if good p then ∑ k, ∑ i, (A p k i)^2 * v p i else 0
  let Z := fun ω => if good (P ω) then ∑ k, (olsCoef (P ω) (u ω) k)^2 else 0
  IsCEF μ P Z q ∧
  (∀ᵐ ω ∂μ, good (P ω) →
    q (P ω) ≤ V * (∑ k, (fixedDesignGram (P ω))⁻¹ k k) / (n : ℝ) ∧
    V * (∑ k, (fixedDesignGram (P ω))⁻¹ k k) / (n : ℝ) ≤
      V * (K : ℝ) / (c * (n : ℝ))) ∧
  mean μ Z ≤ V * (K : ℝ) / (c * (n : ℝ)) := by
  let A := wlp001dB1T6_weights (n := n) (K := K) c
  let M : Fin n → Fin n → Matrix (Fin n) (Fin K) ℝ → ℝ :=
    fun i j p => if i = j then v p i else 0
  let q : Matrix (Fin n) (Fin K) ℝ → ℝ :=
    fun p => ∑ k, ∑ i, ∑ j, (A p k i*A p k j)*M i j p
  have hA (k : Fin K) (i : Fin n) : Measurable (fun p => A p k i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply k).comp (wlp001dB1T6_weights_measurable c))
  have hprodcef (i j : Fin n) : IsCEF μ P (fun ω => u ω i*u ω j) (M i j) := by
    by_cases h : i = j
    · subst j
      simpa [M, pow_two] using hv i
    · simpa only [M, if_neg h] using huncorr i j h
  have hwbound (k : Fin K) (i j : Fin n) :
      ∀ᵐ ω ∂μ, ‖A (P ω) k i*A (P ω) k j‖ ≤ 1/(c*(n : ℝ)) := by
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_mul]
    have hi := wlp001dB1T6_weight_bound hn c hc (P ω) k i
    have hj := wlp001dB1T6_weight_bound hn c hc (P ω) k j
    calc
      |A (P ω) k i| * |A (P ω) k j| ≤
          Real.sqrt (1/(c*(n : ℝ))) * Real.sqrt (1/(c*(n : ℝ))) :=
        mul_le_mul hi hj (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = 1/(c*(n : ℝ)) := by rw [← pow_two, Real.sq_sqrt (by positivity)]
  have hterm (k : Fin K) (i j : Fin n) :
      IsCEF μ P (fun ω => (A (P ω) k i*A (P ω) k j)*(u ω i*u ω j))
        (fun p => (A p k i*A p k j)*M i j p) := by
    have hwm := ((hA k i).mul (hA k j)).comp hP
    exact wlp001dB1T6_cef_mul μ P hP _ _ _ (hprodcef i j) ((hA k i).mul (hA k j))
      ((hprodcef i j).2.1.bdd_mul hwm.aestronglyMeasurable (hwbound k i j))
      ((hprodcef i j).2.2.1.bdd_mul hwm.aestronglyMeasurable (hwbound k i j))
  have hsum := wlp001dB1T6_cef_sum μ P _ _ (fun k =>
    wlp001dB1T6_cef_sum μ P _ _ (fun i =>
      wlp001dB1T6_cef_sum μ P _ _ (fun j => hterm k i j)))
  have he (ω : Ω) :
      (if wlp001dB1T6_good c (P ω) then ∑ k, (olsCoef (P ω) (u ω) k)^2 else 0) =
      ∑ k, ∑ i, ∑ j, (A (P ω) k i*A (P ω) k j)*(u ω i*u ω j) := by
    by_cases hg : wlp001dB1T6_good c (P ω)
    · simp only [if_pos hg]
      apply Finset.sum_congr rfl
      intro k _
      have hcoef : olsCoef (P ω) (u ω) k = ∑ i, A (P ω) k i*u ω i := by
        simp only [A, wlp001dB1T6_weights, if_pos hg, olsCoef, Matrix.mulVec_mulVec]
        rfl
      rw [hcoef, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · simp [A, wlp001dB1T6_weights, hg]
  have hcef : IsCEF μ P (fun ω => if wlp001dB1T6_good c (P ω)
      then ∑ k, (olsCoef (P ω) (u ω) k)^2 else 0) q := by
    simpa only [he, q] using hsum
  have hq (p : Matrix (Fin n) (Fin K) ℝ) :
      q p = ∑ k, ∑ i, (A p k i)^2 * v p i := by
    simp only [q, M, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, pow_two]
  have htrace (p : Matrix (Fin n) (Fin K) ℝ) (hg : wlp001dB1T6_good c p) :
      V*(∑ k, (fixedDesignGram p)⁻¹ k k)/(n : ℝ) =
        V*∑ k, (p.transpose * p)⁻¹ k k := by
    rw [wlp001dB1T6_gram_inverse hn c hc p hg]
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hupper (p : Matrix (Fin n) (Fin K) ℝ) (hg : wlp001dB1T6_good c p) :
      V*(∑ k, (fixedDesignGram p)⁻¹ k k)/(n : ℝ) ≤ V*(K : ℝ)/(c*(n : ℝ)) := by
    rw [htrace p hg]
    calc
      V*(∑ k, (p.transpose * p)⁻¹ k k) ≤ V*∑ _ : Fin K, 1/(c*(n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hV
        exact Finset.sum_le_sum (fun k _ => (wlp001dB1T6_row_norm hn c hc p hg k).2.2)
      _ = V*(K : ℝ)/(c*(n : ℝ)) := by simp; ring
  have hqbound : ∀ᵐ ω ∂μ, q (P ω) ≤ V*(K : ℝ)/(c*(n : ℝ)) ∧
      (wlp001dB1T6_good c (P ω) → q (P ω) ≤
        V*(∑ k, (fixedDesignGram (P ω))⁻¹ k k)/(n : ℝ)) := by
    filter_upwards [hvar] with ω hω
    by_cases hg : wlp001dB1T6_good c (P ω)
    · have hb : q (P ω) ≤ V*(∑ k, (fixedDesignGram (P ω))⁻¹ k k)/(n : ℝ) := by
        rw [hq, htrace _ hg]
        calc
          (∑ k, ∑ i, (A (P ω) k i)^2*v (P ω) i) ≤
              ∑ k, ∑ i, (A (P ω) k i)^2*V := by
            exact Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun i _ =>
              mul_le_mul_of_nonneg_left (hω i) (sq_nonneg _)))
          _ = V*∑ k, ((P ω).transpose * P ω)⁻¹ k k := by
            have hr (k : Fin K) : (∑ i, (A (P ω) k i)^2) = ((P ω).transpose * P ω)⁻¹ k k :=
              (wlp001dB1T6_row_norm hn c hc (P ω) hg k).1
            simp_rw [← Finset.sum_mul, hr]
            ring
      exact ⟨hb.trans (hupper _ hg), fun _ => hb⟩
    · have hz : q (P ω) = 0 := by simp [q, A, wlp001dB1T6_weights, hg]
      exact ⟨by rw [hz]; positivity, fun h => (hg h).elim⟩
  have hqexplicit : q = fun p => if wlp001dB1T6_good c p then
      ∑ k, ∑ i, (((p.transpose * p)⁻¹ * p.transpose) k i)^2 * v p i else 0 := by
    funext p
    rw [hq]
    by_cases hg : wlp001dB1T6_good c p
    · simp only [A, wlp001dB1T6_weights, if_pos hg]
    · simp [A, wlp001dB1T6_weights, hg]
  dsimp only
  change IsCEF μ P (fun ω => if wlp001dB1T6_good c (P ω)
      then ∑ k, (olsCoef (P ω) (u ω) k)^2 else 0)
      (fun p => if wlp001dB1T6_good c p then
        ∑ k, ∑ i, (((p.transpose * p)⁻¹ * p.transpose) k i)^2 * v p i else 0) ∧ _
  rw [← hqexplicit]
  refine ⟨hcef, ?_, ?_⟩
  · filter_upwards [hqbound] with ω hω hg
    refine ⟨?_, hupper _ hg⟩
    have hraw := hω.2 hg
    rw [hqexplicit] at hraw
    dsimp only at hraw
    split_ifs at hraw with hg'
    · convert hraw using 1 <;> simp only [if_pos hg] <;> congr!
    · exact False.elim (hg' hg)
  · have hemean := hcef.2.2.2 Set.univ MeasurableSet.univ
    simp only [Set.preimage_univ, Measure.restrict_univ] at hemean
    change (∫ ω, _ ∂μ) ≤ _
    simp only [wlp001dB1T6_good] at hemean
    have hb : (∫ ω, q (P ω) ∂μ) ≤ V*(K : ℝ)/(c*(n : ℝ)) := by
      simpa [Function.comp_def] using
        integral_mono_ae hcef.2.2.1 (integrable_const (V*(K : ℝ)/(c*(n : ℝ))))
          (hqbound.mono (fun _ h => h.1))
    have hh := hemean.le.trans hb
    convert hh using 1 <;> congr!

/-! P001-T8: normalized finite averaged KL.
The density identity includes zero-density sets and merely SFinite reference
measures. Its proof takes the RN derivative relative to the normalized finite
model law, so no sigma-finite reference hypothesis is needed. -/

theorem normalized_averaged_kl_entropy_identity {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
  (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX]
  (κ : Measure ℝ) [SFinite κ] (f : ℝ → (Fin K → ℝ) → ℝ)
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ)
  (hf : Measurable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1))
  (hg : Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hfn : ∀ y x, 0 ≤ f y x) (hgn : ∀ y x, 0 ≤ g y x t)
  (hfnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (f y x) ∂κ)=1)
  (hgnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ)=1)
  (htrue : μ.map (fun ω => (X ω,Y ω)) =
    (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)))
  (hdom : ∀ᵐ xy ∂(νX.prod κ), 0 < f xy.2 xy.1 → 0 < g xy.2 xy.1 t)
  (hent : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
    f xy.2 xy.1*Real.log (f xy.2 xy.1)) (νX.prod κ))
  (hcross : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
    f xy.2 xy.1*Real.log (g xy.2 xy.1 t)) (νX.prod κ)) :
  averageKLExt νX κ f g t ≠ ∞ ∧
  (averageKLExt νX κ f g t).toReal =
    (∫ x, ∫ y, f y x*Real.log (f y x) ∂κ ∂νX) - expectedLogLikelihood μ X Y g t ∧
  averageKL νX κ f g t = (averageKLExt νX κ f g t).toReal := by
  exact averaged_kl_entropy_adapter μ X Y (hX.prodMk hY) νX κ f g t
    hf hg hfn hgn hfnorm hgnorm htrue hdom hent hcross

end
end AronowAudit.P001.Wave1
