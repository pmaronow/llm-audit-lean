import AronowAudit.Shared.MapTailB.Gaussian
import AronowAudit.P001.Wave1.SieveRate.N3
import AronowAudit.P001.Wave1.SieveRate.N5
import AronowAudit.P001.Wave1.SieveRate.N6
import AronowAudit.P001.Wave1.SieveRate.N8
import AronowAudit.P001.Wave1.SieveRate.N9
import AronowAudit.P001.Wave1.SieveRate.N10
import AronowAudit.P001.Wave1.SieveRate.N11
import AronowAudit.P001.Wave1.SieveRate.N13
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Real.Pi.Bounds

/-! Local polynomial-sieve escape for arbitrary IID samples and arbitrary least-squares fits. -/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.TailBSieveEscape

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open SieveRate AronowAudit.Shared.MapTailB
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-- The polynomial inner product on the boundary interval. -/
def tb02Region (δ : ℝ) (p q : Polynomial ℝ) : ℝ :=
  ∫ z in Set.Icc (0 : ℝ) δ, p.eval z * q.eval z

def tb02Moments (δ : ℝ) (d : ℕ) (r : Polynomial ℝ) : Fin (d + 1) → ℝ :=
  fun k => tb02Region δ (X ^ (k : ℕ)) r

/-- The Chebyshev polynomial `T_{t³}` composed with
`x ↦ (2x - 1 - 1/(2t⁴)) / (1 - 1/(2t⁴))`. -/
def tb02Cheb (t : ℕ) : Polynomial ℝ :=
  (Chebyshev.T ℝ ((t ^ 3 : ℕ) : ℤ)).comp
    (C (2 / (1 - 1 / (2 * (t : ℝ) ^ 4))) * X -
      C ((1 + 1 / (2 * (t : ℝ) ^ 4)) / (1 - 1 / (2 * (t : ℝ) ^ 4))))

def tb02Design (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 1 / (2 * (n : ℝ)) ≤ x i ∧ x i ≤ 1) ∧ Function.Injective x}

def tb02Bad (t : ℕ) (δ ε : ℝ) :
    Set ((Fin (t ^ 4) → ℝ) × (Fin (t ^ 4) → ℝ)) :=
  {z | z.1 ∈ tb02Design (t ^ 4) ∧
    ε < tb02Region δ (olsPoly (t ^ 3) z.1 z.2) (olsPoly (t ^ 3) z.1 z.2)}

theorem tb02_region_cs (δ : ℝ) (p r : Polynomial ℝ)
    (hr : 0 < tb02Region δ r r) :
    tb02Region δ p r ^ 2 / tb02Region δ r r ≤ tb02Region δ p p := by
  let lam : ℝ := tb02Region δ p r / tb02Region δ r r
  have hpp : IntegrableOn (fun z : ℝ => p.eval z * p.eval z)
      (Set.Icc (0 : ℝ) δ) :=
    (p.continuous.mul p.continuous).integrableOn_Icc
  have hpr : IntegrableOn (fun z : ℝ => p.eval z * r.eval z)
      (Set.Icc (0 : ℝ) δ) :=
    (p.continuous.mul r.continuous).integrableOn_Icc
  have hrr : IntegrableOn (fun z : ℝ => r.eval z * r.eval z)
      (Set.Icc (0 : ℝ) δ) :=
    (r.continuous.mul r.continuous).integrableOn_Icc

  have hexpand :
      (∫ z in Set.Icc (0 : ℝ) δ, (p.eval z - lam * r.eval z) ^ 2) =
        tb02Region δ p p - (2 * lam) * tb02Region δ p r + lam ^ 2 * tb02Region δ r r := by
    calc
      (∫ z in Set.Icc (0 : ℝ) δ, (p.eval z - lam * r.eval z) ^ 2) =
          ∫ z in Set.Icc (0 : ℝ) δ,
            (p.eval z * p.eval z - (2 * lam) * (p.eval z * r.eval z)) +
              lam ^ 2 * (r.eval z * r.eval z) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => by ring)
      _ = _ := by
        have hsub : IntegrableOn (fun z : ℝ => p.eval z * p.eval z -
            (2 * lam) * (p.eval z * r.eval z)) (Set.Icc (0 : ℝ) δ) :=
          hpp.sub (hpr.const_mul (2 * lam))
        rw [integral_add hsub
          (hrr.const_mul (lam ^ 2)),
          integral_sub hpp (hpr.const_mul (2 * lam)),
          integral_const_mul, integral_const_mul]
        rfl

  have hnonneg :
      0 ≤ ∫ z in Set.Icc (0 : ℝ) δ, (p.eval z - lam * r.eval z) ^ 2 :=
    setIntegral_nonneg measurableSet_Icc (fun z _ => sq_nonneg _)
  have halgebra :
      tb02Region δ p p - (2 * lam) * tb02Region δ p r + lam ^ 2 * tb02Region δ r r =
        tb02Region δ p p - tb02Region δ p r ^ 2 / tb02Region δ r r := by
    dsimp only [lam]
    field_simp [ne_of_gt hr] <;> ring
  rw [hexpand, halgebra] at hnonneg
  exact sub_nonneg.mp hnonneg


theorem tb02_region_coeff (δ : ℝ) (d : ℕ) (b : Fin (d + 1) → ℝ)
    (r : Polynomial ℝ) :
    tb02Region δ (coeffPoly b) r = b ⬝ᵥ tb02Moments δ d r := by
  have hint (k : Fin (d + 1)) :
      IntegrableOn (fun z : ℝ => b k * (z ^ (k : ℕ) * r.eval z))
        (Set.Icc (0 : ℝ) δ) :=
    (continuous_const.mul ((continuous_id.pow (k : ℕ)).mul r.continuous)).integrableOn_Icc
  have hexpand (z : ℝ) :
      (coeffPoly b).eval z * r.eval z =
        ∑ k : Fin (d + 1), b k * (z ^ (k : ℕ) * r.eval z) := by
    simp only [coeffPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_assoc _ _ _
  calc
    tb02Region δ (coeffPoly b) r =
        ∫ z in Set.Icc (0 : ℝ) δ,
          ∑ k : Fin (d + 1), b k * (z ^ (k : ℕ) * r.eval z) := by
      unfold tb02Region
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hexpand
    _ = ∑ k : Fin (d + 1),
        ∫ z in Set.Icc (0 : ℝ) δ, b k * (z ^ (k : ℕ) * r.eval z) :=
      integral_finsetSum Finset.univ (fun k _ => hint k)
    _ = ∑ k : Fin (d + 1),
        b k * ∫ z in Set.Icc (0 : ℝ) δ, z ^ (k : ℕ) * r.eval z := by
      apply Finset.sum_congr rfl
      intro k _
      exact integral_const_mul (b k) _
    _ = b ⬝ᵥ tb02Moments δ d r := by
      simp only [dotProduct, tb02Moments, tb02Region, Polynomial.eval_pow,
        Polynomial.eval_X]

theorem tb02_cheb_bounds (t : ℕ) (ht : 2 ≤ t) (δ : ℝ)
    (hstrip : 1 / (8 * (t : ℝ) ^ 4) ≤ δ) :
    (tb02Cheb t).natDegree ≤ t ^ 3 ∧
    (∀ z ∈ Set.Icc (1 / (2 * (t : ℝ) ^ 4)) 1, |(tb02Cheb t).eval z| ≤ 1) ∧
    9 * (t : ℝ) ^ 8 / 209715200 ≤ tb02Region δ (tb02Cheb t) (tb02Cheb t) := by
  classical
  have h10 := n10_proof
  have h11 := n11_proof
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have htne : (t : ℝ) ≠ 0 := ne_of_gt htpos
  have ht4 : (16 : ℝ) ≤ (t : ℝ) ^ 4 := by
    calc
      (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (t : ℝ) ^ 4 := by gcongr
  have hd : 3 ≤ t ^ 3 := by
    have h : (2 : ℕ) ^ 3 ≤ t ^ 3 := by gcongr
    norm_num at h
    omega
  let a : ℝ := 1 / (2 * (t : ℝ) ^ 4)
  let ell : ℝ → ℝ := fun z => (2 * z - 1 - a) / (1 - a)
  let r : Polynomial ℝ := tb02Cheb t
  let B : ℝ := 3 * (t : ℝ) ^ 6 / 5120
  have ha : 0 < a := by dsimp [a]; positivity
  have ha16 : a ≤ 1 / 16 := by
    dsimp [a]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hden : 0 < 1 - a := by linarith
  have hdenne : 1 - a ≠ 0 := ne_of_gt hden
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have heval (z : ℝ) :
      r.eval z = (Chebyshev.T ℝ ((t ^ 3 : ℕ) : ℤ)).eval (ell z) := by
    change (tb02Cheb t).eval z = _
    rw [tb02Cheb, eval_comp]
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    congr 1
    change 2 / (1 - a) * z - (1 + a) / (1 - a) = (2 * z - 1 - a) / (1 - a)
    field_simp [hdenne]
    <;> ring
  have hdeg : r.natDegree ≤ t ^ 3 := by
    let l : Polynomial ℝ := C (2 / (1 - a)) * X - C ((1 + a) / (1 - a))
    have hl : l.natDegree ≤ 1 := by
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · exact (natDegree_C_mul_le _ _).trans (by simp)
      · simp
    calc
      r.natDegree ≤ (Chebyshev.T ℝ ((t ^ 3 : ℕ) : ℤ)).natDegree * l.natDegree :=
        natDegree_comp_le
      _ = t ^ 3 * l.natDegree := by simp
      _ ≤ t ^ 3 * 1 := Nat.mul_le_mul_left _ hl
      _ = t ^ 3 := Nat.mul_one _
  have hbounded : ∀ z ∈ Set.Icc a 1, |r.eval z| ≤ 1 := by
    intro z hz
    have hzL : -1 ≤ ell z := by
      dsimp [ell]
      apply (le_div_iff₀ hden).2
      linarith [hz.1]
    have hzU : ell z ≤ 1 := by
      dsimp [ell]
      apply (div_le_iff₀ hden).2
      linarith [hz.2]
    rw [heval]
    exact h10 (t ^ 3) (ell z) ⟨hzL, hzU⟩
  have hboundary : ∀ z ∈ Set.Icc (0 : ℝ) (a / 4), B ≤ |r.eval z| := by
    intro z hz
    let s : ℝ := -ell z - 1
    have hs_eq : s = (2 * a - 2 * z) / (1 - a) := by
      dsimp [s, ell]
      field_simp [hdenne]
      <;> ring
    have hs0 : 0 ≤ s := by
      rw [hs_eq]
      exact div_nonneg (by linarith [hz.2]) hden.le
    have hs1 : s ≤ 1 := by
      rw [hs_eq]
      apply (div_le_iff₀ hden).2
      linarith [hz.1]
    have hs_lower : (3 / 2 : ℝ) * a ≤ s := by
      rw [hs_eq]
      apply (le_div_iff₀ hden).2
      nlinarith [hz.2, sq_nonneg a]
    have hgrowth := h11 (t ^ 3) hd s hs0 hs1
    have harith : B ≤ ((t ^ 3 : ℕ) : ℝ) ^ 6 * s ^ 3 / 720 := by
      calc
        B = ((t ^ 3 : ℕ) : ℝ) ^ 6 * ((3 / 2 : ℝ) * a) ^ 3 / 720 := by
          dsimp [B, a]
          push_cast
          field_simp [htne]
          <;> ring
        _ ≤ ((t ^ 3 : ℕ) : ℝ) ^ 6 * s ^ 3 / 720 := by
          gcongr
    have hpos_eval : 0 ≤ (Chebyshev.T ℝ ((t ^ 3 : ℕ) : ℤ)).eval (1 + s) :=
      le_trans (by positivity) hgrowth
    have hsign : |((((t ^ 3 : ℕ) : ℤ)).negOnePow : ℝ)| = 1 := by
      simp [Int.cast_negOnePow_natCast, abs_pow]
    have hell : ell z = -(1 + s) := by dsimp [s]; ring
    rw [heval, hell, Chebyshev.T_eval_neg, abs_mul, hsign, one_mul,
      abs_of_nonneg hpos_eval]
    exact harith.trans hgrowth
  let J : Set ℝ := Set.Icc 0 (a / 4)
  have hJsub : J ⊆ Set.Icc (0 : ℝ) δ := by
    intro z hz
    have ha4 : a / 4 = 1 / (8 * (t : ℝ) ^ 4) := by
      dsimp [a]
      ring
    exact ⟨hz.1, le_trans hz.2 (ha4.trans_le hstrip)⟩
  have hcont : Continuous (fun z : ℝ => r.eval z * r.eval z) :=
    r.continuous.mul r.continuous
  have hJint : IntegrableOn (fun z : ℝ => r.eval z * r.eval z) J :=
    hcont.integrableOn_Icc
  have hIint : IntegrableOn (fun z : ℝ => r.eval z * r.eval z)
      (Set.Icc (0 : ℝ) δ) := hcont.integrableOn_Icc
  have hsquare : ∀ z ∈ J, B ^ 2 ≤ r.eval z * r.eval z := by
    intro z hz
    have h := hboundary z hz
    have hsq : B ^ 2 ≤ |r.eval z| ^ 2 := pow_le_pow_left₀ hB h 2
    simpa [sq_abs, pow_two] using hsq
  have hconst : volume.real J * B ^ 2 ≤ ∫ z in J, r.eval z * r.eval z := by
    simpa only [smul_eq_mul] using
      (setIntegral_ge_of_const_le (μ := volume) (s := J)
        (c := B ^ 2) measurableSet_Icc (by simp [J]) hsquare hJint)
  have hmono : (∫ z in J, r.eval z * r.eval z) ≤ tb02Region δ r r := by
    exact setIntegral_mono_set hIint
      (Filter.Eventually.of_forall (fun z => mul_self_nonneg (r.eval z)))
      (Filter.Eventually.of_forall (fun _ hz => hJsub hz))
  have hvol : volume.real J = a / 4 := by
    change volume.real (Set.Icc (0 : ℝ) (a / 4)) = a / 4
    rw [Real.volume_real_Icc_of_le (by positivity)]
    ring
  have hnumeric : volume.real J * B ^ 2 = 9 * (t : ℝ) ^ 8 / 209715200 := by
    rw [hvol]
    dsimp [a, B]
    field_simp [htne]
    <;> ring
  refine ⟨hdeg, hbounded, ?_⟩
  rw [← hnumeric]
  exact hconst.trans hmono


theorem tb02_meas_design (n : ℕ) : MeasurableSet (tb02Design n) := by
  classical
  have hbox : MeasurableSet
      {x : Fin n → ℝ | ∀ i, 1 / (2 * (n : ℝ)) ≤ x i ∧ x i ≤ 1} := by
    have hset : {x : Fin n → ℝ | ∀ i, 1 / (2 * (n : ℝ)) ≤ x i ∧ x i ≤ 1} =
        ⋂ i : Fin n, {x : Fin n → ℝ | 1 / (2 * (n : ℝ)) ≤ x i ∧ x i ≤ 1} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_le measurable_const (measurable_pi_apply i)).inter
        (measurableSet_le (measurable_pi_apply i) measurable_const)
  have hinj : MeasurableSet {x : Fin n → ℝ | Function.Injective x} := by
    have hset : {x : Fin n → ℝ | Function.Injective x} =
        ⋂ i : Fin n, ⋂ j : Fin n, {x : Fin n → ℝ | x i = x j → i = j} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Function.Injective]
    rw [hset]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : i = j
    · simpa [hij] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Fin n → ℝ)))
    · have h : MeasurableSet {x : Fin n → ℝ | x i = x j}ᶜ :=
        (measurableSet_eq_fun (f := fun x : Fin n → ℝ => x i) (g := fun x => x j)
          (measurable_pi_apply i) (measurable_pi_apply j)).compl
      convert h using 1
      ext x
      simp [hij]
  change MeasurableSet
    ({x : Fin n → ℝ | ∀ i, 1 / (2 * (n : ℝ)) ≤ x i ∧ x i ≤ 1} ∩
      {x : Fin n → ℝ | Function.Injective x})
  exact hbox.inter hinj

theorem tb02_meas_ols (n d : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => olsCoef (vand d z.1) z.2) := by
  classical
  let A : ((Fin n → ℝ) × (Fin n → ℝ)) →
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    fun z => (vand d z.1).transpose * vand d z.1
  have hP : Continuous
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => vand d z.1) := by
    exact continuous_pi fun i => continuous_pi fun k =>
      (((continuous_apply i).comp continuous_fst).pow (k : ℕ))
  have hA : Continuous A := hP.matrix_transpose.matrix_mul hP
  have hAi (k l : Fin (d + 1)) : Measurable (fun z => (A z)⁻¹ k l) := by
    have hdet : Measurable (fun z => (A z).det⁻¹) := hA.matrix_det.measurable.inv
    have hadj : Measurable (fun z => (A z).adjugate k l) :=
      (hA.matrix_adjugate.matrix_elem k l).measurable
    simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
      Pi.mul_def] using hdet.mul hadj
  have hPy : Continuous
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (vand d z.1).transpose.mulVec z.2) :=
    hP.matrix_transpose.matrix_mulVec continuous_snd
  apply Measurable.of_eval
  intro k
  change Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    ∑ l : Fin (d + 1), ((A z)⁻¹ k l) * ((vand d z.1).transpose.mulVec z.2 l))
  exact Finset.measurable_sum Finset.univ fun l _ =>
    (hAi k l).mul (((continuous_apply l).comp hPy).measurable)

/-- Integrating a jointly measurable polynomial expression over a fixed interval is
measurable in its coefficient vector. The parameterized-integral theorem does not
require an integrability hypothesis on the parameter space. -/
theorem tb02_meas_region (δ : ℝ) (d : ℕ) :
    Measurable (fun b : Fin (d + 1) → ℝ => tb02Region δ (coeffPoly b) (coeffPoly b)) := by
  classical
  have heval : Measurable
      (fun z : (Fin (d + 1) → ℝ) × ℝ => (coeffPoly z.1).eval z.2) := by
    simp only [coeffPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact Finset.measurable_sum Finset.univ fun k _ =>
      ((measurable_pi_apply k).comp measurable_fst).mul
        (measurable_snd.pow_const (k : ℕ))
  have hprod : StronglyMeasurable
      (fun z : (Fin (d + 1) → ℝ) × ℝ =>
        (coeffPoly z.1).eval z.2 * (coeffPoly z.1).eval z.2) :=
    (heval.mul heval).stronglyMeasurable
  exact (hprod.integral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) δ))).measurable

theorem tb02_meas_bad (t : ℕ) (δ ε : ℝ) : MeasurableSet (tb02Bad t δ ε) := by
  have hrisk : Measurable
      (fun z : (Fin (t ^ 4) → ℝ) × (Fin (t ^ 4) → ℝ) =>
        tb02Region δ (olsPoly (t ^ 3) z.1 z.2) (olsPoly (t ^ 3) z.1 z.2)) :=
    (tb02_meas_region δ (t ^ 3)).comp (tb02_meas_ols (t ^ 4) (t ^ 3))
  exact ((tb02_meas_design (t ^ 4)).preimage measurable_fst).inter
    (measurableSet_lt measurable_const hrisk)

/-- Bernoulli's inequality gives the sharp half-probability design bound. -/
theorem tb02_design_mass (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / 2 ≤ ((unifVec n) (tb02Design n)).toReal := by
  classical
  letI : IsProbabilityMeasure (unifVec n) := by unfold unifVec; infer_instance
  letI : NullSingletonClass (uniformLaw (0 : ℝ) 1) := by
    unfold uniformLaw
    infer_instance
  have hunif : uniformLaw (0 : ℝ) 1 = volume.restrict (Set.Icc (0 : ℝ) 1) := by
    have hdensity :
        (fun x : ℝ => ENNReal.ofReal
          (if x ∈ Set.Icc (0 : ℝ) 1 then (1 - 0)⁻¹ else 0)) =
        (Set.Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) := by
      funext x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [hx]
    rw [uniformLaw, hdensity, withDensity_indicator_one measurableSet_Icc]
  have hdelta_meas : MeasurableSet {z : ℝ × ℝ | z.1 = z.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hdelta : (uniformLaw 0 1).prod (uniformLaw 0 1)
      {z : ℝ × ℝ | z.1 = z.2} = 0 := by
    rw [Measure.prod_apply hdelta_meas]
    have hsection (a : ℝ) :
        Prod.mk a ⁻¹' {z : ℝ × ℝ | z.1 = z.2} = {a} := by
      ext b
      simp [eq_comm]
    simp_rw [hsection]
    simp only [measure_singleton, lintegral_zero]
  have hind : iIndepFun (fun i : Fin n => fun x : Fin n → ℝ => x i) (unifVec n) := by
    exact iIndepFun_pi (μ := fun _ : Fin n => uniformLaw 0 1)
      (X := fun _ : Fin n => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  have hmarg (i : Fin n) :
      (unifVec n).map (fun x : Fin n → ℝ => x i) = uniformLaw 0 1 :=
    (measurePreserving_eval (fun _ : Fin n => uniformLaw 0 1) i).map_eq
  have hzero (i j : Fin n) (hij : i ≠ j) :
      (unifVec n) {x : Fin n → ℝ | x i = x j} = 0 := by
    have hpair : (unifVec n).map (fun x : Fin n → ℝ => (x i, x j)) =
        (uniformLaw 0 1).prod (uniformLaw 0 1) := by
      have heq := (indepFun_iff_map_prod_eq_prod_map_map
        (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable).1 (hind.indepFun hij)
      simpa only [hmarg] using heq
    change (unifVec n) ((fun x : Fin n → ℝ => (x i, x j)) ⁻¹'
      {z : ℝ × ℝ | z.1 = z.2}) = 0
    rw [← Measure.map_apply
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hdelta_meas,
      hpair, hdelta]
  have hpair_ae (i j : Fin n) :
      ∀ᵐ x : Fin n → ℝ ∂(unifVec n), x i = x j → i = j := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ _ => hij
    · have hne : ∀ᵐ x : Fin n → ℝ ∂(unifVec n), x i ≠ x j := by
        apply ae_iff.2
        simpa only [not_not] using hzero i j hij
      filter_upwards [hne] with x hx
      intro hEq
      exact (hx hEq).elim
  have hinj : ∀ᵐ x : Fin n → ℝ ∂(unifVec n), Function.Injective x := by
    have hall : ∀ᵐ x : Fin n → ℝ ∂(unifVec n),
        ∀ i j : Fin n, x i = x j → i = j :=
      ae_all_iff.2 fun i => ae_all_iff.2 fun j => hpair_ae i j
    filter_upwards [hall] with x hx
    intro i j hij
    exact hx i j hij
  let box : Set (Fin n → ℝ) :=
    Set.pi Set.univ (fun _ : Fin n => Set.Icc (1 / (2 * (n : ℝ))) 1)
  have hdesign_box : tb02Design n =ᵐ[unifVec n] box := by
    filter_upwards [hinj] with x hx
    apply propext
    simp [tb02Design, box, Set.mem_pi, hx, Pi.le_def, forall_and]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hq : (0 : ℝ) ≤ 1 - 1 / (2 * (n : ℝ)) := by
    have hdiv : (1 : ℝ) / (2 * (n : ℝ)) ≤ 1 :=
      (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).2 (by linarith)
    linarith
  have hfactor : (uniformLaw 0 1) (Set.Icc (1 / (2 * (n : ℝ))) 1) =
      ENNReal.ofReal (1 - 1 / (2 * (n : ℝ))) := by
    have hsub : Set.Icc (1 / (2 * (n : ℝ))) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      exact ⟨(by positivity : (0 : ℝ) ≤ 1 / (2 * (n : ℝ))).trans hx.1, hx.2⟩
    rw [hunif, Measure.restrict_apply measurableSet_Icc,
      Set.inter_eq_left.mpr hsub, Real.volume_Icc]
  have hbox : (unifVec n) box = ENNReal.ofReal (1 - 1 / (2 * (n : ℝ))) ^ n := by
    rw [unifVec, show box = Set.pi Set.univ (fun _ : Fin n => Set.Icc (1 / (2 * (n : ℝ))) 1) from rfl,
      Measure.pi_pi]
    simp only [hfactor, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [measure_congr hdesign_box, hbox, ENNReal.toReal_pow, ENNReal.toReal_ofReal hq]
  have hb := one_add_mul_sub_le_pow (a := 1 - 1 / (2 * (n : ℝ)))
    (by linarith : -1 ≤ 1 - 1 / (2 * (n : ℝ))) n
  have heq : 1 + (n : ℝ) * ((1 - 1 / (2 * (n : ℝ))) - 1) = 1 / 2 := by
    field_simp [ne_of_gt hnpos]
    <;> ring
  rwa [heq] at hb


/-- A variance lower bound makes a Gaussian quadratic statistic escape every fixed level. -/
theorem tb02_gauss_escape (v : ℝ≥0) (hv : 0 < v) (N B ε : ℝ)
    (hN : 0 < N) (hB : 0 < B) (hε : 0 ≤ ε) (hvar : B * N ≤ (v : ℝ)) :
    1 - 2 * Real.sqrt ε / Real.sqrt B ≤
      ((gaussianReal 0 v) {z : ℝ | ε * N < z ^ 2}).toReal := by
  have hsub : {z : ℝ | z ^ 2 ≤ ε * N} ⊆
      Set.Icc (-Real.sqrt (ε * N)) (Real.sqrt (ε * N)) := by
    intro z hz
    exact ⟨Real.neg_sqrt_le_of_sq_le hz, Real.le_sqrt_of_sq_le hz⟩
  have hd : B * N ≤ 2 * Real.pi * (v : ℝ) := by
    have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    exact hvar.trans (le_mul_of_one_le_left (by positivity) hp)
  have hs : Real.sqrt B * Real.sqrt N ≤ Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    rw [← Real.sqrt_mul hB.le]
    exact Real.sqrt_le_sqrt hd
  have hsmall : ((gaussianReal 0 v) {z : ℝ | z ^ 2 ≤ ε * N}).toReal ≤
      2 * Real.sqrt ε / Real.sqrt B := by
    calc
      _ ≤ ((gaussianReal 0 v)
          (Set.Icc (-Real.sqrt (ε * N)) (Real.sqrt (ε * N)))).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ ≤ 2 * Real.sqrt (ε * N) / Real.sqrt (2 * Real.pi * (v : ℝ)) :=
        TailB_gaussian_small_ball v hv _ (Real.sqrt_nonneg _)
      _ ≤ 2 * Real.sqrt (ε * N) / (Real.sqrt B * Real.sqrt N) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hs
      _ = 2 * Real.sqrt ε / Real.sqrt B := by
        rw [Real.sqrt_mul hε]
        field_simp [ne_of_gt (Real.sqrt_pos.2 hN), ne_of_gt (Real.sqrt_pos.2 hB)]
  have hc : {z : ℝ | ε * N < z ^ 2} = {z : ℝ | z ^ 2 ≤ ε * N}ᶜ := by
    ext z
    simp
  have hmeas : MeasurableSet {z : ℝ | z ^ 2 ≤ ε * N} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [hc, ← measureReal_def, probReal_compl_eq_one_sub hmeas]
  exact sub_le_sub_left hsmall 1

/-- The first-n law, with design and errors split, for an arbitrary IID carrier. -/
theorem tb02_first_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
    (hlaw : μ.map (fun ω => (X 0 ω, Y 0 ω)) =
      (uniformLaw 0 1).prod (gaussianReal 0 1)) (n : ℕ) :
    μ.map (fun ω => ((fun i : Fin n => X i ω), (fun i : Fin n => Y i ω))) =
      (unifVec n).prod (gaussVec n) := by
  let pair : Fin n → Ω → ℝ × ℝ := fun i ω => (X i ω, Y i ω)
  have hmeas (i : Fin n) : Measurable (pair i) := hiid.1 i
  have hind : iIndepFun pair μ :=
    hiid.2.1.precomp (g := fun i : Fin n => (i : ℕ)) Fin.val_injective
  have hmarg (i : Fin n) : μ.map (pair i) =
      (uniformLaw 0 1).prod (gaussianReal 0 1) :=
    (hiid.2.2 i).map_eq.trans hlaw
  have hfinite : μ.map (fun ω => fun i : Fin n => pair i ω) =
      Measure.pi (fun _ : Fin n => (uniformLaw 0 1).prod (gaussianReal 0 1)) := by
    calc
      μ.map (fun ω => fun i : Fin n => pair i ω) =
          Measure.pi (fun i : Fin n => μ.map (pair i)) :=
        hind.map_fun_eq_pi_map (fun i => (hmeas i).aemeasurable)
      _ = _ := by simp only [hmarg]
  let split : (Fin n → ℝ × ℝ) ≃ᵐ (Fin n → ℝ) × (Fin n → ℝ) :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  have hcollect : Measurable (fun ω => fun i : Fin n => pair i ω) :=
    Measurable.of_eval hmeas
  calc
    μ.map (fun ω => ((fun i : Fin n => X i ω), (fun i : Fin n => Y i ω))) =
        (μ.map (fun ω => fun i : Fin n => pair i ω)).map split := by
      exact (Measure.map_map split.measurable hcollect).symm
    _ = (Measure.pi (fun _ : Fin n =>
        (uniformLaw 0 1).prod (gaussianReal 0 1))).map split := by rw [hfinite]
    _ = (unifVec n).prod (gaussVec n) :=
      (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
        (fun _ => uniformLaw 0 1) (fun _ => gaussianReal 0 1)).map_eq

/-- The uniform small-ball error; it tends to zero as the fourth-power index grows. -/
def tb02Q (ε : ℝ) (t : ℕ) : ℝ :=
  2 * Real.sqrt ε / (Real.sqrt (9 / 209715200 : ℝ) * (t : ℝ) ^ 2)

theorem tb02_fixed_escape (t : ℕ) (ht : 2 ≤ t) (δ : ℝ)
    (hstrip : 1 / (8 * (t : ℝ) ^ 4) ≤ δ) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Fin (t ^ 4) → ℝ) (hx : x ∈ tb02Design (t ^ 4)) :
    1 - tb02Q ε t ≤ ((gaussVec (t ^ 4))
      {y | ε < tb02Region δ (olsPoly (t ^ 3) x y) (olsPoly (t ^ 3) x y)}).toReal := by
  classical
  letI instGaussVec : IsProbabilityMeasure (gaussVec (t ^ 4)) := by
    unfold gaussVec
    infer_instance
  have ht0 : 0 < t := by omega
  have htRpos : (0 : ℝ) < t := by positivity
  have hnpos : (0 : ℝ) < (t : ℝ) ^ 4 := by positivity
  have hcols : t ^ 3 + 1 ≤ t ^ 4 := by
    have hp : 1 ≤ t ^ 3 := Nat.one_le_pow _ _ ht0
    calc
      t ^ 3 + 1 ≤ t ^ 3 + t ^ 3 := Nat.add_le_add_left hp _
      _ = 2 * t ^ 3 := by omega
      _ ≤ t * t ^ 3 := Nat.mul_le_mul_right _ ht
      _ = t ^ 4 := by ring
  rcases hx with ⟨hbox, hinj⟩
  let r : Polynomial ℝ := tb02Cheb t
  let P : Matrix (Fin (t ^ 4)) (Fin (t ^ 3 + 1)) ℝ := vand (t ^ 3) x
  let c : Fin (t ^ 3 + 1) → ℝ := fun k => r.coeff (k : ℕ)
  let w : Fin (t ^ 3 + 1) → ℝ := tb02Moments δ (t ^ 3) r
  let N : ℝ := tb02Region δ r r
  let sigma2 : ℝ := w ⬝ᵥ ((P.transpose * P)⁻¹).mulVec w
  let E : ℝ := ∑ i : Fin (t ^ 4), (P.mulVec c i) ^ 2
  let C : ℝ := 9 / 209715200
  rcases tb02_cheb_bounds t ht δ hstrip with ⟨hdegree, hsup, hnorm⟩
  have hc : coeffPoly c = r := by
    change (∑ k : Fin (t ^ 3 + 1), Polynomial.C (r.coeff (k : ℕ)) * X ^ (k : ℕ)) = r
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => Polynomial.C (r.coeff k) * X ^ k)
      (t ^ 3 + 1)]
    exact (r.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hdegree)).symm
  have hP : IsUnit (P.transpose * P).det := n5_proof (t ^ 4) (t ^ 3) x hcols hinj
  have hNdot : c ⬝ᵥ w = N := by
    rw [← tb02_region_coeff δ (t ^ 3) c r, hc]
  have hE0 : 0 ≤ E := Finset.sum_nonneg (fun i _ => sq_nonneg (P.mulVec c i))
  have hEbound : E ≤ (t : ℝ) ^ 4 := by
    calc
      E ≤ ∑ i : Fin (t ^ 4), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have heval : P.mulVec c i = r.eval (x i) := by
          rw [n8_proof.2 (t ^ 3) (t ^ 4) x c i, hc]
        rw [heval]
        have hi : x i ∈ Set.Icc (1 / (2 * (t : ℝ) ^ 4)) 1 := by
          exact ⟨by simpa only [Nat.cast_pow] using (hbox i).1, (hbox i).2⟩
        have hsmall : |r.eval (x i)| ≤ 1 := hsup (x i) hi
        have hsq : |r.eval (x i)| ^ 2 ≤ (1 : ℝ) ^ 2 := by gcongr
        simpa only [sq_abs, one_pow] using hsq
      _ = (t : ℝ) ^ 4 := by simp
  have hCpos : 0 < C := by norm_num [C]
  have hNbound : C * (t : ℝ) ^ 8 ≤ N := by
    simpa only [C, div_mul_eq_mul_div] using hnorm
  have hNpos : 0 < N := (by positivity : 0 < C * (t : ℝ) ^ 8).trans_le hNbound
  have hCS : N ^ 2 ≤ E * sigma2 := by
    have h := n9_proof (t ^ 4) (t ^ 3 + 1) P hP c w
    change (c ⬝ᵥ w) ^ 2 ≤ E * sigma2 at h
    rwa [hNdot] at h
  have hsigma : 0 < sigma2 := by
    by_contra! hnonpos
    have hm := mul_nonpos_of_nonneg_of_nonpos hE0 hnonpos
    have hNsq : 0 < N ^ 2 := pow_pos hNpos 2
    linarith
  have hCSn : N ^ 2 ≤ (t : ℝ) ^ 4 * sigma2 :=
    hCS.trans (mul_le_mul_of_nonneg_right hEbound hsigma.le)
  have hvar : (C * (t : ℝ) ^ 4) * N ≤ sigma2 := by
    apply (mul_le_mul_iff_left₀ hnpos).1
    calc
      (C * (t : ℝ) ^ 4 * N) * (t : ℝ) ^ 4 = (C * (t : ℝ) ^ 8) * N := by ring
      _ ≤ N * N := mul_le_mul_of_nonneg_right hNbound hNpos.le
      _ ≤ sigma2 * (t : ℝ) ^ 4 := by simpa only [pow_two, mul_comm] using hCSn
  let L : (Fin (t ^ 4) → ℝ) → ℝ := fun y => olsCoef P y ⬝ᵥ w
  have hLmeas : Measurable L := by
    dsimp [L, olsCoef]
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hAmeas : MeasurableSet {z : ℝ | ε * N < z ^ 2} :=
    measurableSet_lt measurable_const (measurable_id.pow_const 2)
  have hcoe : ((sigma2.toNNReal : ℝ≥0) : ℝ) = sigma2 := Real.coe_toNNReal sigma2 hsigma.le
  have htail : 1 - tb02Q ε t ≤
      ((gaussVec (t ^ 4)) {y | ε * N < L y ^ 2}).toReal := by
    have hv : 0 < sigma2.toNNReal := Real.toNNReal_pos.2 hsigma
    have hb := tb02_gauss_escape sigma2.toNNReal hv N (C * (t : ℝ) ^ 4) ε
      hNpos (by positivity) hε (by simpa only [hcoe] using hvar)
    have hsqrt : Real.sqrt (C * (t : ℝ) ^ 4) = Real.sqrt C * (t : ℝ) ^ 2 := by
      rw [Real.sqrt_mul hCpos.le, show (t : ℝ) ^ 4 = ((t : ℝ) ^ 2) ^ 2 by ring,
        Real.sqrt_sq (sq_nonneg _)]
    rw [hsqrt] at hb
    change 1 - tb02Q ε t ≤
      ((gaussianReal 0 sigma2.toNNReal) {z : ℝ | ε * N < z ^ 2}).toReal at hb
    have hlaw := n13_proof (t ^ 4) (t ^ 3 + 1) P hP w
    change (gaussVec (t ^ 4)).map L = gaussianReal 0 sigma2.toNNReal at hlaw
    rw [← hlaw, Measure.map_apply hLmeas hAmeas] at hb
    exact hb
  have hsubset : {y : Fin (t ^ 4) → ℝ | ε * N < L y ^ 2} ⊆
      {y | ε < tb02Region δ (olsPoly (t ^ 3) x y) (olsPoly (t ^ 3) x y)} := by
    intro y hy
    have hlinear : tb02Region δ (olsPoly (t ^ 3) x y) r = L y :=
      tb02_region_coeff δ (t ^ 3) (olsCoef P y) r
    have hregional := tb02_region_cs δ (olsPoly (t ^ 3) x y) r hNpos
    rw [hlinear] at hregional
    exact ((lt_div_iff₀ hNpos).2 hy).trans_le hregional
  exact htail.trans
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset))


theorem tb02_product_escape (t : ℕ) (ht : 2 ≤ t) (δ : ℝ)
    (hstrip : 1 / (8 * (t : ℝ) ^ 4) ≤ δ) (ε : ℝ) (hε : 0 ≤ ε)
    (hq : tb02Q ε t ≤ 1) :
    (1 - tb02Q ε t) / 2 ≤
      (((unifVec (t ^ 4)).prod (gaussVec (t ^ 4))) (tb02Bad t δ ε)).toReal := by
  classical
  letI instUnifVec : IsProbabilityMeasure (unifVec (t ^ 4)) := by
    unfold unifVec
    infer_instance
  letI instGaussVec : IsProbabilityMeasure (gaussVec (t ^ 4)) := by
    unfold gaussVec
    infer_instance
  let b : ℝ := 1 - tb02Q ε t
  have hb : 0 ≤ b := sub_nonneg.2 hq
  have hsection (x : Fin (t ^ 4) → ℝ) (hx : x ∈ tb02Design (t ^ 4)) :
      Prod.mk x ⁻¹' tb02Bad t δ ε =
        {y | ε < tb02Region δ (olsPoly (t ^ 3) x y) (olsPoly (t ^ 3) x y)} := by
    ext y
    simp only [Set.mem_preimage, tb02Bad, Set.mem_setOf_eq, hx, true_and]
  have hpoint (x : Fin (t ^ 4) → ℝ) (hx : x ∈ tb02Design (t ^ 4)) :
      ENNReal.ofReal b ≤ (gaussVec (t ^ 4)) (Prod.mk x ⁻¹' tb02Bad t δ ε) := by
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2
    rw [hsection x hx]
    exact tb02_fixed_escape t ht δ hstrip ε hε x hx
  have hint :
      (∫⁻ x, (tb02Design (t ^ 4)).indicator
        (fun _ => ENNReal.ofReal b) x ∂(unifVec (t ^ 4))) ≤
      ∫⁻ x, (gaussVec (t ^ 4)) (Prod.mk x ⁻¹' tb02Bad t δ ε) ∂(unifVec (t ^ 4)) := by
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ tb02Design (t ^ 4)
    · rw [Set.indicator_of_mem hx]
      exact hpoint x hx
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hfubini : ENNReal.ofReal b * (unifVec (t ^ 4)) (tb02Design (t ^ 4)) ≤
      ((unifVec (t ^ 4)).prod (gaussVec (t ^ 4))) (tb02Bad t δ ε) := by
    rw [Measure.prod_apply (tb02_meas_bad t δ ε)]
    calc
      ENNReal.ofReal b * (unifVec (t ^ 4)) (tb02Design (t ^ 4)) =
          ∫⁻ x, (tb02Design (t ^ 4)).indicator
            (fun _ => ENNReal.ofReal b) x ∂(unifVec (t ^ 4)) :=
        (lintegral_indicator_const (tb02_meas_design (t ^ 4)) _).symm
      _ ≤ _ := hint
  have hdesign : ENNReal.ofReal ((1 : ℝ) / 2) ≤
      (unifVec (t ^ 4)) (tb02Design (t ^ 4)) := by
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2
    exact tb02_design_mass _ (Nat.one_le_pow _ _ (by omega : 0 < t))
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1
  calc
    ENNReal.ofReal ((1 - tb02Q ε t) / 2) =
        ENNReal.ofReal b * ENNReal.ofReal ((1 : ℝ) / 2) := by
      rw [← ENNReal.ofReal_mul hb]
      congr 1
      dsimp [b]
      ring
    _ ≤ ENNReal.ofReal b * (unifVec (t ^ 4)) (tb02Design (t ^ 4)) := by gcongr
    _ ≤ _ := hfubini

/-- The measurable canonical event is contained in the event of every pointwise argmin.
The latter is measured by the outer measure, with no selection measurability premise. -/
theorem tb02_sample_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
    (hlaw : μ.map (fun ω => (X 0 ω, Y 0 ω)) =
      (uniformLaw 0 1).prod (gaussianReal 0 1))
    (fit : ℕ → Ω → Polynomial ℝ) (hfit : IsSieveLS X Y sieveJ fit)
    (t : ℕ) (ht : 2 ≤ t) (δ : ℝ) (hstrip : 1 / (8 * (t : ℝ) ^ 4) ≤ δ)
    (ε : ℝ) (hε : 0 ≤ ε) (hq : tb02Q ε t ≤ 1) :
    (1 - tb02Q ε t) / 2 ≤ prob μ
      {ω | ε < ∫ x in Set.Icc 0 δ, ((fit (t ^ 4) ω).eval x) ^ 2} := by
  let F : Ω → (Fin (t ^ 4) → ℝ) × (Fin (t ^ 4) → ℝ) :=
    fun ω => ((fun i : Fin (t ^ 4) => X i ω), (fun i : Fin (t ^ 4) => Y i ω))
  have hF : Measurable F := by
    exact (Measurable.of_eval (fun i : Fin (t ^ 4) => (hiid.1 i).fst)).prodMk
      (Measurable.of_eval (fun i : Fin (t ^ 4) => (hiid.1 i).snd))
  have hlawF : μ.map F = (unifVec (t ^ 4)).prod (gaussVec (t ^ 4)) :=
    tb02_first_law μ X Y hiid hlaw (t ^ 4)
  have hmass : μ (F ⁻¹' tb02Bad t δ ε) =
      ((unifVec (t ^ 4)).prod (gaussVec (t ^ 4))) (tb02Bad t δ ε) := by
    rw [← Measure.map_apply hF (tb02_meas_bad t δ ε), hlawF]
  have hcols : t ^ 3 + 1 ≤ t ^ 4 := by
    have hp : 1 ≤ t ^ 3 := Nat.one_le_pow _ _ (by omega : 0 < t)
    calc
      t ^ 3 + 1 ≤ t ^ 3 + t ^ 3 := Nat.add_le_add_left hp _
      _ = 2 * t ^ 3 := by omega
      _ ≤ t * t ^ 3 := Nat.mul_le_mul_right _ ht
      _ = t ^ 4 := by ring
  have hsub : F ⁻¹' tb02Bad t δ ε ⊆
      {ω | ε < ∫ x in Set.Icc 0 δ, ((fit (t ^ 4) ω).eval x) ^ 2} := by
    intro ω hω
    rcases hω with ⟨hx, hbad⟩
    have hsfit := hfit (t ^ 4) ω
    rw [n3_proof.2.2 t] at hsfit
    have heq : fit (t ^ 4) ω =
        olsPoly (t ^ 3) (fun i : Fin (t ^ 4) => X i ω)
          (fun i : Fin (t ^ 4) => Y i ω) :=
      n6_proof n5_proof (t ^ 4) (t ^ 3) (fun i => X i ω) (fun i => Y i ω)
        (fit (t ^ 4) ω) hcols hx.2 hsfit.1 hsfit.2
    change ε < ∫ x in Set.Icc 0 δ, ((fit (t ^ 4) ω).eval x) ^ 2
    rw [heq]
    simpa only [tb02Region, pow_two] using hbad
  calc
    (1 - tb02Q ε t) / 2 ≤ (μ (F ⁻¹' tb02Bad t δ ε)).toReal := by
      rw [hmass]
      exact tb02_product_escape t ht δ hstrip ε hε hq
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)

theorem tb02_q_tendsto (ε : ℝ) : Tendsto (tb02Q ε) atTop (nhds 0) := by
  have hp : Tendsto (fun t : ℕ => (t : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop
    (hp.const_mul_atTop (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 9 / 209715200)))

theorem tb02_strip_tendsto :
    Tendsto (fun t : ℕ => 1 / (8 * (t : ℝ) ^ 4)) atTop (nhds (0 : ℝ)) := by
  have hp : Tendsto (fun t : ℕ => (t : ℝ) ^ 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop (hp.const_mul_atTop (by norm_num : (0 : ℝ) < 8))


end

end AronowAudit.P001.Wave1.TailBSieveEscape

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open SieveRate TailBSieveEscape
open scoped Topology

/-- The local-L² counterexample, including its universal selection quantifier. -/
theorem TailB_sieve_degree_counterexample :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (X Y : ℕ → Ω → ℝ)
      (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
      (hlaw : μ.map (fun ω => (X 0 ω, Y 0 ω)) = (uniformLaw 0 1).prod (gaussianReal 0 1))
      (fit : ℕ → Ω → Polynomial ℝ)
      (hfit : IsSieveLS X Y (fun (n : ℕ) => Nat.floor ((n : ℝ)^(3/4 : ℝ))) fit),
      Tendsto (fun (n : ℕ) => Nat.floor ((n : ℝ)^(3/4 : ℝ))) atTop atTop ∧
   Tendsto (fun (n : ℕ) => (Nat.floor ((n : ℝ)^(3/4 : ℝ)) : ℝ) / n) atTop (nhds 0) ∧
   ∀ δ : ℝ, 0  <  δ → δ  ≤  1 → ∀ ε : ℝ, 0  <  ε →
     1/2  ≤  Filter.liminf (fun t : ℕ =>
       prob μ {ω | ε  <  ∫ x in Set.Icc 0 δ, ((fit (t^4) ω).eval x)^2}) atTop) := by
  intro Ω instΩ μ instμ X Y hiid hlaw fit hfit
  refine ⟨n3_proof.1, n3_proof.2.1, ?_⟩
  intro δ hδ hδ1 ε hε
  let p : ℕ → ℝ := fun t => prob μ
    {ω | ε < ∫ x in Set.Icc 0 δ, ((fit (t ^ 4) ω).eval x) ^ 2}
  change (1 : ℝ) / 2 ≤ liminf p atTop
  have hlo : IsBoundedUnder (· ≥ ·) atTop p :=
    isBoundedUnder_of ⟨0, fun _ => ENNReal.toReal_nonneg⟩
  have hhi : IsBoundedUnder (· ≤ ·) atTop p :=
    isBoundedUnder_of ⟨1, fun _ => measureReal_le_one⟩
  apply (le_liminf_iff hhi.isCoboundedUnder_ge hlo).2
  intro b hb
  have hlim : Tendsto (fun t => (1 - tb02Q ε t) / 2) atTop (nhds ((1 : ℝ) / 2)) := by
    convert (tendsto_const_nhds.sub (tb02_q_tendsto ε)).div_const (2 : ℝ) using 1
    norm_num
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    tb02_strip_tendsto.eventually_lt_const hδ,
    (tb02_q_tendsto ε).eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    hlim.eventually_const_lt hb] with t ht hstrip hq hb'
  exact hb'.trans_le (tb02_sample_lower μ X Y hiid hlaw fit hfit t ht δ hstrip.le ε hε.le hq.le)

end AronowAudit.P001.Wave1
