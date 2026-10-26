import AronowAudit.P018.Wave1.Gap.GP0181B1
import AronowAudit.P018.Wave1.WeightedConsistency.M5
import AronowAudit.P018.Wave1.WeightedConsistency.G3
import AronowAudit.P018.Wave1.WeightedConsistency.G4
import AronowAudit.P018.Wave1.WeightedConsistency.G5
import AronowAudit.P018.Wave1.WeightedConsistency.G7
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.Distributions.Pareto
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! P018-T3(i): bounded design, probability convergence, and infinite inverse moments. -/
noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

lemma inverse_gram_pareto_eq : paretoUnitLaw = paretoMeasure 1 1 := by
  unfold paretoUnitLaw paretoMeasure
  congr 1
  funext t
  simp only [paretoPDF, paretoPDFReal, show -(1 + 1 : ℝ) = -(2 : ℝ) by norm_num,
    Real.one_rpow, one_mul]
  split_ifs with h
  · rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_two]
  · simp

local instance inverse_gram_probability : IsProbabilityMeasure paretoUnitLaw := by
  rw [inverse_gram_pareto_eq]
  exact isProbabilityMeasure_paretoMeasure (by norm_num) (by norm_num)

local instance inverse_gram_noAtoms : NullSingletonClass paretoUnitLaw := by
  unfold paretoUnitLaw
  infer_instance

local instance inverse_gram_kernel_probability : IsProbabilityMeasure inverseKernel.μ :=
  inverse_gram_probability

lemma inverse_gram_tail (a : ℝ) (ha : 1 ≤ a) :
    paretoUnitLaw (Set.Ici a) = ENNReal.ofReal a⁻¹ := by
  rw [paretoUnitLaw, withDensity_apply _ measurableSet_Ici]
  have heq : (∫⁻ t in Set.Ici a,
      if 1 ≤ t then ENNReal.ofReal ((t⁻¹)^2) else 0) =
      ∫⁻ t in Set.Ici a, ENNReal.ofReal (t ^ (-2 : ℝ)) := by
    apply setLIntegral_congr_fun measurableSet_Ici
    intro t ht
    simp [if_pos (ha.trans ht), Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by norm_num) (by linarith : 0 < a)]
    norm_num [Real.rpow_neg_one]
  · change IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ici a) volume
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by linarith : 0 < a)).congr_set_ae Ioi_ae_eq_Ici.symm
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact Real.rpow_nonneg (le_trans (by linarith : 0 ≤ a) ht) _

lemma inverse_gram_support : ∀ᵐ t ∂paretoUnitLaw, 1 ≤ t := by
  rw [ae_iff]
  change paretoUnitLaw (Set.Ici 1)ᶜ = 0
  rw [measure_compl measurableSet_Ici (measure_ne_top _ _), inverse_gram_tail 1 le_rfl]
  norm_num

lemma inverse_gram_exp_bound : ∀ᵐ t ∂paretoUnitLaw, Real.exp (-t) ≤ 1 := by
  filter_upwards [inverse_gram_support] with t ht
  exact Real.exp_le_one_iff.mpr (by linarith)

lemma inverse_gram_pair_bound : ∀ᵐ uv ∂paretoUnitLaw.prod paretoUnitLaw,
    ‖inverseKernel.X uv.1 uv.2‖ ≤ 2 ∧ |inverseKernel.Y uv.1 uv.2| ≤ 2 := by
  have h1 := (measurePreserving_fst (μ := paretoUnitLaw) (ν := paretoUnitLaw)).quasiMeasurePreserving.ae inverse_gram_exp_bound
  have h2 := (measurePreserving_snd (μ := paretoUnitLaw) (ν := paretoUnitLaw)).quasiMeasurePreserving.ae inverse_gram_exp_bound
  filter_upwards [h1, h2] with uv hu hv
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
    intro i
    fin_cases i
    · norm_num [inverseKernel]
    · change |Real.exp (-uv.1) + Real.exp (-uv.2)| ≤ 2
      rw [abs_of_pos (add_pos (Real.exp_pos _) (Real.exp_pos _))]
      linarith
  · norm_num [inverseKernel]

lemma inverse_gram_measurable : Measurable (fun uv : ℝ × ℝ => inverseKernel.X uv.1 uv.2) := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp only [inverseKernel, Matrix.cons_val_zero, Matrix.cons_val_one] <;> fun_prop

lemma inverse_gram_no_constant_exp (c : ℝ) :
    ¬ (∀ᵐ t ∂paretoUnitLaw, Real.exp (-t) = c) := by
  intro h
  obtain ⟨t, ht⟩ := h.exists
  have hn : ∀ᵐ s ∂paretoUnitLaw, s ≠ t := paretoUnitLaw.ae_ne t
  obtain ⟨s, hs, hst⟩ := (h.and hn).exists
  apply hst
  exact neg_injective (Real.exp_injective (hs.trans ht.symm))

lemma inverse_gram_W_lp : MemLp (fun uv : ℝ × ℝ => Real.exp (-uv.1) + Real.exp (-uv.2))
    2 (paretoUnitLaw.prod paretoUnitLaw) := by
  apply MemLp.of_bound (by fun_prop) 2
  filter_upwards [inverse_gram_pair_bound] with uv h
  exact (norm_le_pi_norm (inverseKernel.X uv.1 uv.2) 1).trans h.1

lemma inverse_gram_population_det_pos : 0 < (populationGram inverseKernel).det := by
  let W := fun uv : ℝ × ℝ => Real.exp (-uv.1) + Real.exp (-uv.2)
  have hmat : populationGram inverseKernel =
      !![1, ∫ uv, W uv ∂paretoUnitLaw.prod paretoUnitLaw;
        ∫ uv, W uv ∂paretoUnitLaw.prod paretoUnitLaw,
        ∫ uv, (W uv)^2 ∂paretoUnitLaw.prod paretoUnitLaw] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [populationGram, meanMat, outer, inverseKernel, W, pow_two]
  have hv : 0 < variance W (paretoUnitLaw.prod paretoUnitLaw) := by
    apply lt_of_le_of_ne (variance_nonneg _ _)
    intro hz
    have hc := ae_eq_integral_of_variance_eq_zero inverse_gram_W_lp hz.symm
    obtain ⟨u, hu⟩ := (Measure.ae_ae_of_ae_prod hc).exists
    apply inverse_gram_no_constant_exp ((∫ uv, W uv ∂paretoUnitLaw.prod paretoUnitLaw) - Real.exp (-u))
    filter_upwards [hu] with v hv
    change Real.exp (-u) + Real.exp (-v) = _ at hv
    linarith
  rw [hmat, Matrix.det_fin_two]
  rw [variance_eq_sub inverse_gram_W_lp] at hv
  simpa [pow_two] using hv

lemma inverse_gram_standing : Standing inverseKernel := by
  refine ⟨inverse_gram_probability, inverse_gram_measurable, measurable_const, ?_,
    ⟨2, by norm_num, inverse_gram_pair_bound⟩, ⟨0, fun _ _ => rfl⟩,
    inverse_gram_population_det_pos.ne'⟩
  intro u v
  constructor
  · simp only [inverseKernel, add_comm]
  · rfl

/-- The dyad slope and the first two empirical moments. -/
def inverse_gram_W {N : ℕ} (ω : Fin N → ℝ) (d : Dyad N) : ℝ :=
  Real.exp (-ω (firstUnit d)) + Real.exp (-ω (secondUnit d))

def inverse_gram_A {N : ℕ} (ω : Fin N → ℝ) : ℝ :=
  (Dreal N)⁻¹ * ∑ d, inverse_gram_W ω d

def inverse_gram_B {N : ℕ} (ω : Fin N → ℝ) : ℝ :=
  (Dreal N)⁻¹ * ∑ d, (inverse_gram_W ω d)^2

def inverse_gram_Q {N : ℕ} (ω : Fin N → ℝ) : Mat 2 :=
  (Dreal N)⁻¹ • sampleGram (design inverseKernel ω)

lemma inverse_gram_Q_matrix {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → ℝ) :
    inverse_gram_Q ω = !![1, inverse_gram_A ω; inverse_gram_A ω, inverse_gram_B ω] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverse_gram_Q, sampleGram, design, inverseKernel, outer, inverse_gram_A,
      inverse_gram_B, inverse_gram_W, Matrix.sum_apply, pow_two, printed_card_real, printed_dyads_card_real,
      inv_mul_cancel₀ (printed_Dpos hN).ne']

lemma inverse_gram_det {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → ℝ) :
    (inverse_gram_Q ω).det = inverse_gram_B ω - (inverse_gram_A ω)^2 := by
  rw [inverse_gram_Q_matrix hN, Matrix.det_fin_two]
  simp [pow_two]

lemma inverse_gram_centered_squares {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → ℝ) :
    (∑ d, (inverse_gram_W ω d - inverse_gram_A ω)^2) =
      Dreal N * (inverse_gram_Q ω).det := by
  rw [inverse_gram_det hN]
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, printed_card_real,
    ← Finset.mul_sum, ← Finset.sum_mul]
  unfold inverse_gram_A inverse_gram_B
  field_simp [(printed_Dpos hN).ne']
  <;> ring

lemma inverse_gram_det_nonneg {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → ℝ) :
    0 ≤ (inverse_gram_Q ω).det := by
  have hs : 0 ≤ ∑ d, (inverse_gram_W ω d - inverse_gram_A ω)^2 :=
    sum_nonneg (fun _ _ => sq_nonneg _)
  rw [inverse_gram_centered_squares hN] at hs
  exact nonneg_of_mul_nonneg_right hs (printed_Dpos hN)

lemma inverse_gram_det_pos {N : ℕ} (hN : 3 ≤ N) (ω : Fin N → ℝ)
    (h01 : ω ⟨0, by omega⟩ ≠ ω ⟨1, by omega⟩) : 0 < (inverse_gram_Q ω).det := by
  have hN2 : 2 ≤ N := by omega
  apply lt_of_le_of_ne (inverse_gram_det_nonneg hN2 ω)
  intro hz
  have hs : (∑ d, (inverse_gram_W ω d - inverse_gram_A ω)^2) = 0 := by
    rw [inverse_gram_centered_squares hN2, ← hz, mul_zero]
  have he (d : Dyad N) : inverse_gram_W ω d = inverse_gram_A ω := by
    exact sub_eq_zero.mp (((Finset.sum_sq_eq_zero_iff _ _).mp hs) d (mem_univ _))
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨1, by omega⟩
  let l : Fin N := ⟨2, by omega⟩
  have hil : i < l := by change (0 : ℕ) < 2; omega
  have hjl : j < l := by change (1 : ℕ) < 2; omega
  have heq := (he (printed_mkDyad i l hil.ne)).trans (he (printed_mkDyad j l hjl.ne)).symm
  have hexp : Real.exp (-ω i) = Real.exp (-ω j) := by
    simpa only [inverse_gram_W, (printed_mkDyad_endpoints i l hil).1,
      (printed_mkDyad_endpoints i l hil).2, (printed_mkDyad_endpoints j l hjl).1,
      (printed_mkDyad_endpoints j l hjl).2, add_left_inj] using heq
  exact h01 (neg_injective (Real.exp_injective hexp))

lemma inverse_gram_ae_distinct {N : ℕ} (i j : Fin N) (hij : i < j) :
    ∀ᵐ ω ∂unitSampleLaw inverseKernel N, ω i ≠ ω j := by
  have hp : ∀ᵐ uv ∂paretoUnitLaw.prod paretoUnitLaw, uv.1 ≠ uv.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
    exact ae_of_all _ (fun u => (paretoUnitLaw.ae_ne u).mono (fun v hv => hv.symm))
  have hh := (corrected_pair_preserving inverseKernel (printed_mkDyad i j hij.ne)).quasiMeasurePreserving.ae hp
  simpa only [(printed_mkDyad_endpoints i j hij).1,
    (printed_mkDyad_endpoints i j hij).2] using hh

lemma inverse_gram_sample_rank : SampleRank inverseKernel := by
  refine ⟨3, fun N hN => ?_⟩
  filter_upwards [inverse_gram_ae_distinct (⟨0, by omega⟩ : Fin N)
    (⟨1, by omega⟩ : Fin N) (by change (0 : ℕ) < 1; omega)] with ω hω
  have hpos := inverse_gram_det_pos hN ω hω
  intro hz
  have he : (inverse_gram_Q ω).det = 0 := by
    rw [inverse_gram_Q, Matrix.det_smul, hz, mul_zero]
  exact hpos.ne' he

/-- The set in the Euclidean operator supremum is bounded above. -/
lemma inverse_gram_operator_bdd (M : Mat 2) :
    BddAbove {r : ℝ | ∃ x : Vec 2, euclideanSq x ≤ 1 ∧
      r = Real.sqrt (euclideanSq (M.mulVec x))} := by
  let C := fun a : Fin 2 => |M a 0| + |M a 1|
  refine ⟨Real.sqrt ((C 0)^2 + (C 1)^2), ?_⟩
  rintro r ⟨x, hx, rfl⟩
  have hxs : (x 0)^2 + (x 1)^2 ≤ 1 := by
    simpa [euclideanSq, Fin.sum_univ_two] using hx
  have hx0 : |x 0| ≤ 1 := by nlinarith [sq_abs (x 0), sq_nonneg (x 1), abs_nonneg (x 0)]
  have hx1 : |x 1| ≤ 1 := by nlinarith [sq_abs (x 1), sq_nonneg (x 0), abs_nonneg (x 1)]
  have hy (a : Fin 2) : |M.mulVec x a| ≤ C a := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    calc
      |M a 0 * x 0 + M a 1 * x 1| ≤ |M a 0 * x 0| + |M a 1 * x 1| := abs_add_le _ _
      _ ≤ |M a 0| * 1 + |M a 1| * 1 := by
        simp only [abs_mul]
        gcongr
      _ = C a := by simp [C]
  apply Real.sqrt_le_sqrt
  simp only [euclideanSq, Fin.sum_univ_two]
  have hc0 : 0 ≤ C 0 := by positivity
  have hc1 : 0 ≤ C 1 := by positivity
  have hy0 := hy 0
  have hy1 := hy 1
  nlinarith [sq_abs (M.mulVec x 0), sq_abs (M.mulVec x 1),
    abs_nonneg (M.mulVec x 0), abs_nonneg (M.mulVec x 1)]


lemma inverse_gram_operator_diagonal (M : Mat 2) : |M 1 1| ≤ matrixOperatorNorm M := by
  apply le_csSup_of_le (inverse_gram_operator_bdd M)
    (show Real.sqrt (euclideanSq (M.mulVec (![0, 1] : Vec 2))) ∈
      {r : ℝ | ∃ x : Vec 2, euclideanSq x ≤ 1 ∧ r = Real.sqrt (euclideanSq (M.mulVec x))} from
      ⟨![0, 1], by norm_num [euclideanSq, Fin.sum_univ_two], rfl⟩)
  calc
    |M 1 1| = Real.sqrt ((M 1 1)^2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ _ := by
      apply Real.sqrt_le_sqrt
      simp only [euclideanSq, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero,
        mul_one, zero_add]
      nlinarith [sq_nonneg (M 0 1)]

lemma inverse_gram_inverse_entry {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → ℝ) :
    (inverse_gram_Q ω)⁻¹ 1 1 = ((inverse_gram_Q ω).det)⁻¹ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', inverse_gram_Q_matrix hN,
    Matrix.adjugate_fin_two]
  simp

lemma inverse_gram_W_tail {N : ℕ} (ω : Fin N → ℝ) (m : ℝ)
    (hω : ∀ i, m ≤ ω i) (d : Dyad N) :
    0 < inverse_gram_W ω d ∧ inverse_gram_W ω d ≤ 2 * Real.exp (-m) := by
  constructor
  · exact add_pos (Real.exp_pos _) (Real.exp_pos _)
  · have h1 := Real.exp_le_exp.mpr (neg_le_neg (hω (firstUnit d)))
    have h2 := Real.exp_le_exp.mpr (neg_le_neg (hω (secondUnit d)))
    dsimp [inverse_gram_W]
    linarith

lemma inverse_gram_det_upper {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → ℝ) (m : ℝ)
    (hω : ∀ i, m ≤ ω i) :
    (inverse_gram_Q ω).det ≤ 4 * Real.exp (-2*m) := by
  have hB : inverse_gram_B ω ≤ 4 * Real.exp (-2*m) := by
    unfold inverse_gram_B
    calc
      _ ≤ (Dreal N)⁻¹ * ∑ _d : Dyad N, (2 * Real.exp (-m))^2 := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (printed_Dpos hN).le)
        exact Finset.sum_le_sum (fun d _ =>
          pow_le_pow_left₀ (inverse_gram_W_tail ω m hω d).1.le
            (inverse_gram_W_tail ω m hω d).2 2)
      _ = (2 * Real.exp (-m))^2 := by
        simp only [sum_const, card_univ, nsmul_eq_mul, printed_card_real]
        rw [← mul_assoc, inv_mul_cancel₀ (printed_Dpos hN).ne', one_mul]
      _ = _ := by
        rw [mul_pow, ← Real.exp_nat_mul]
        norm_num only [show (2 : ℝ)^2 = 4 by norm_num]
        congr 2
        ring
  rw [inverse_gram_det hN]
  exact (sub_le_self _ (sq_nonneg _)).trans hB

lemma inverse_gram_pointwise_lower {N : ℕ} (hN : 3 ≤ N) (ω : Fin N → ℝ) (m : ℝ)
    (hω : ∀ i, m ≤ ω i) (hrank : (inverse_gram_Q ω).det ≠ 0) :
    Real.exp (2*m) / 4 ≤ matrixOperatorNorm ((inverse_gram_Q ω)⁻¹) := by
  have hd : 0 < (inverse_gram_Q ω).det :=
    lt_of_le_of_ne (inverse_gram_det_nonneg (by omega) ω) hrank.symm
  have hu := inverse_gram_det_upper (by omega : 2 ≤ N) ω m hω
  have he : Real.exp (2*m) * Real.exp (-2*m) = 1 := by
    rw [← Real.exp_add]
    have hexp : 2*m + -2*m = 0 := by ring
    rw [hexp, Real.exp_zero]
  apply le_trans _ (inverse_gram_operator_diagonal _)
  rw [inverse_gram_inverse_entry (by omega), abs_of_pos (inv_pos.mpr hd)]
  rw [← one_div]
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ (Real.exp (2*m)/4) * (4 * Real.exp (-2*m)) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = 1 := by nlinarith [he]

/-- Bounded two-coordinate kernels satisfy the dyadic weak law. -/
lemma inverse_gram_probability_limit :
    inProbability (unitSampleLaw inverseKernel) (fun N ω =>
      (inverse_gram_Q ω)⁻¹ - (populationGram inverseKernel)⁻¹) := by
  let Z := fun (N : ℕ) (d : Dyad N) (a b : Fin 2) (ω : Fin N → ℝ) =>
    design inverseKernel ω d a * design inverseKernel ω d b
  have hm (N : ℕ) (d : Dyad N) (a b : Fin 2) : Measurable (Z N d a b) := by
    have hp : Measurable (fun ω : Fin N → ℝ => (ω (firstUnit d), ω (secondUnit d))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    have hX : Measurable (fun ω : Fin N → ℝ => design inverseKernel ω d) :=
      inverse_gram_measurable.comp hp
    exact ((measurable_pi_apply a).comp hX).mul ((measurable_pi_apply b).comp hX)
  have hs (N : ℕ) (d : Dyad N) (a b : Fin 2) (ω ω' : Fin N → ℝ)
      (hω : ∀ i ∈ members d, ω i = ω' i) : Z N d a b ω = Z N d a b ω' := by
    simp only [Z, design, hω _ (WeightedConsistency.firstUnit_mem d),
      hω _ (WeightedConsistency.secondUnit_mem d)]
  have hb (N : ℕ) (d : Dyad N) (a b : Fin 2) :
      ∀ᵐ ω ∂unitSampleLaw inverseKernel N, |Z N d a b ω| ≤ 4 := by
    have hh := (corrected_pair_preserving inverseKernel d).quasiMeasurePreserving.ae inverse_gram_pair_bound
    filter_upwards [hh] with ω hω
    have ha : |design inverseKernel ω d a| ≤ 2 := (norm_le_pi_norm _ a).trans hω.1
    have hb : |design inverseKernel ω d b| ≤ 2 := (norm_le_pi_norm _ b).trans hω.1
    dsimp [Z]
    rw [abs_mul]
    nlinarith [abs_nonneg (design inverseKernel ω d a), abs_nonneg (design inverseKernel ω d b)]
  have he (N : ℕ) (ω : Fin N → ℝ) (a b : Fin 2) :
      inverse_gram_Q ω a b = (Dreal N)⁻¹ * ∑ d, Z N d a b ω := by
    simp [inverse_gram_Q, sampleGram, Matrix.sum_apply, outer, Z]
  have hZLp (N : ℕ) (d : Dyad N) (a b : Fin 2) :
      MemLp (Z N d a b) 2 (unitSampleLaw inverseKernel N) := by
    apply MemLp.of_bound (hm N d a b).aestronglyMeasurable 4
    simpa only [Real.norm_eq_abs] using hb N d a b
  have hLp (N : ℕ) (a b : Fin 2) : MemLp (fun ω => inverse_gram_Q ω a b) 2
      (unitSampleLaw inverseKernel N) := by
    simp_rw [he]
    have hsum : MemLp (fun ω => ∑ d : Dyad N, Z N d a b ω) 2
        (unitSampleLaw inverseKernel N) :=
      memLp_finsetSum univ (fun d _ => hZLp N d a b)
    exact hsum.const_mul ((Dreal N)⁻¹)
  have hv (a b : Fin 2) : Tendsto (fun N => variance (fun ω => inverse_gram_Q ω a b)
      (unitSampleLaw inverseKernel N)) atTop (𝓝 0) := by
    simp_rw [he]
    exact WeightedConsistency.dyad_scaled_variance_tendsto WeightedConsistency.g3_proof
      WeightedConsistency.g4_proof paretoUnitLaw (fun N d => Z N d a b) 4
      (fun N d => hm N d a b) (fun N d => hs N d a b) (fun N d => hb N d a b)
  have hc := (WeightedConsistency.g5_proof (unitSampleLaw inverseKernel)).1
    (fun _ ω => inverse_gram_Q ω) hLp hv
  have hmean (N : ℕ) (hN : 2 ≤ N) :
      meanMat (unitSampleLaw inverseKernel N) (inverse_gram_Q (N := N)) = populationGram inverseKernel := by
    change meanMat (unitSampleLaw inverseKernel N)
      (fun ω => (Dreal N)⁻¹ • sampleGram (design inverseKernel ω)) = _
    rw [meanMat_scale, corrected_expected_gram inverseKernel inverse_gram_standing,
      smul_smul, inv_mul_cancel₀ (printed_Dpos hN).ne', one_smul]
  have hQ : inProbability (unitSampleLaw inverseKernel) (fun _ ω =>
      inverse_gram_Q ω - populationGram inverseKernel) := by
    apply WeightedConsistency.inProbability_eventually_eq _ _ hc
    filter_upwards [eventually_ge_atTop 2] with N hN ω
    rw [hmean N hN]
  exact (WeightedConsistency.g7_proof (populationGram inverseKernel)
    inverse_gram_population_det_pos.ne').2 (unitSampleLaw inverseKernel)
      (fun _ ω => inverse_gram_Q ω) hQ

/-- The all-large-unit event has exactly the product Pareto tail probability. -/
lemma inverse_gram_tail_event (N : ℕ) (m : ℝ) (hm : 1 ≤ m) :
    unitSampleLaw inverseKernel N {ω | ∀ i, m ≤ ω i} =
      (ENNReal.ofReal m⁻¹)^N := by
  have he : {ω : Fin N → ℝ | ∀ i, m ≤ ω i} = Set.univ.pi (fun _ => Set.Ici m) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ici]
  rw [he]
  change (Measure.pi (fun _ : Fin N => paretoUnitLaw)) (Set.univ.pi (fun _ => Set.Ici m)) = _
  rw [Measure.pi_pi]
  simp only [inverse_gram_tail m hm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma inverse_gram_integral_lower (N : ℕ) (hN : 3 ≤ N) (m : ℕ) (hm : 1 ≤ m) :
    ENNReal.ofReal (Real.exp (2*m)/(4*(m : ℝ)^N)) ≤
      ∫⁻ ω, ENNReal.ofReal (matrixOperatorNorm ((inverse_gram_Q ω)⁻¹))
        ∂unitSampleLaw inverseKernel N := by
  let E : Set (Fin N → ℝ) := {ω | ∀ i, (m : ℝ) ≤ ω i}
  have hE : MeasurableSet E := by
    have hi (i : Fin N) : MeasurableSet {ω : Fin N → ℝ | (m : ℝ) ≤ ω i} :=
      measurableSet_le measurable_const (measurable_pi_apply i)
    simpa only [E, Set.setOf_forall] using MeasurableSet.iInter hi
  have hr : ∀ᵐ ω ∂unitSampleLaw inverseKernel N, (inverse_gram_Q ω).det ≠ 0 := by
    filter_upwards [inverse_gram_ae_distinct (⟨0, by omega⟩ : Fin N)
      (⟨1, by omega⟩ : Fin N) (by change (0 : ℕ) < 1; omega)] with ω hω
    exact (inverse_gram_det_pos hN ω hω).ne'
  have hcomp : (∫⁻ ω, E.indicator (fun _ => ENNReal.ofReal (Real.exp (2*m)/4)) ω
      ∂unitSampleLaw inverseKernel N) ≤
      ∫⁻ ω, ENNReal.ofReal (matrixOperatorNorm ((inverse_gram_Q ω)⁻¹))
        ∂unitSampleLaw inverseKernel N := by
    apply lintegral_mono_ae
    filter_upwards [hr] with ω hω
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he]
      exact ENNReal.ofReal_le_ofReal (inverse_gram_pointwise_lower hN ω m he hω)
    · rw [Set.indicator_of_notMem he]
      exact bot_le
  rw [lintegral_indicator hE, lintegral_const, Measure.restrict_apply_univ] at hcomp
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hevent := inverse_gram_tail_event N m (by exact_mod_cast hm)
  change unitSampleLaw inverseKernel N E = _ at hevent
  rw [hevent, ← ENNReal.ofReal_pow (inv_nonneg.mpr hmR.le), ← ENNReal.ofReal_mul (by positivity)] at hcomp
  convert hcomp using 1
  congr 1
  simp only [div_eq_mul_inv, inv_pow]
  ring

lemma inverse_gram_integral_top (N : ℕ) (hN : 3 ≤ N) :
    (∫⁻ ω, ENNReal.ofReal (matrixOperatorNorm ((inverse_gram_Q ω)⁻¹))
      ∂unitSampleLaw inverseKernel N) = ∞ := by
  have htR : Tendsto (fun m : ℕ => Real.exp (2*m)/(4*(m : ℝ)^N)) atTop atTop := by
    have ht := (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 4)).mpr
      ((tendsto_exp_mul_div_rpow_atTop (N : ℝ) 2 (by norm_num)).comp
        tendsto_natCast_atTop_atTop)
    simpa only [Function.comp_def, Real.rpow_natCast, div_div, mul_comm] using ht
  have ht := ENNReal.tendsto_ofReal_atTop.comp htR
  apply top_le_iff.mp
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact inverse_gram_integral_lower N hN m hm

/-- The bounded, full-rank dyadic design has infinite inverse-Gram expectation. -/
theorem inverse_gram_counterexample_proof :
    Standing inverseKernel ∧ SampleRank inverseKernel ∧
    inProbability (unitSampleLaw inverseKernel) (fun N ω =>
      ((Dreal N)⁻¹ • sampleGram (design inverseKernel ω))⁻¹ - (populationGram inverseKernel)⁻¹) ∧
    (∀ N : ℕ, 3 ≤ N → ∀ m : ℕ, 1 ≤ m →
      ENNReal.ofReal (Real.exp (2*m)/(4*(m : ℝ)^N)) ≤
        ∫⁻ ω, ENNReal.ofReal (matrixOperatorNorm
          (((Dreal N)⁻¹ • sampleGram (design inverseKernel ω))⁻¹)) ∂ unitSampleLaw inverseKernel N) ∧
    (∀ N : ℕ, 3 ≤ N →
      (∫⁻ ω, ENNReal.ofReal (matrixOperatorNorm
        (((Dreal N)⁻¹ • sampleGram (design inverseKernel ω))⁻¹)) ∂ unitSampleLaw inverseKernel N) = ∞) := by
  exact ⟨inverse_gram_standing, inverse_gram_sample_rank, inverse_gram_probability_limit,
    inverse_gram_integral_lower, inverse_gram_integral_top⟩

end AronowAudit.P018.Wave1
