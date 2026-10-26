import AronowAudit.P011.Wave1.Gap.GP011B3
import AronowAudit.P011.P011_SampleCompletion

/-!
P011-T16: OLS mean and shift identities, and the root-n rate obtained from
bounded raw responses and a uniformly coercive normalized Gram matrix.
-/
namespace AronowAudit.P011.Wave1

open MeasureTheory ProbabilityTheory Filter Finset
open Causalean.Mathlib.Probability.SteinMethod
open scoped BigOperators Topology Classical Matrix NNReal ENNReal ProbabilityTheory
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

lemma olsr_fits {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ)
    (hrank : (Dᵀ*D).det ≠ 0) (c : Fin p → ℝ) : ols D (D*ᵥc) = c := by
  unfold ols
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hrank), Matrix.one_mulVec]

lemma olsr_add {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ)
    (hrank : (Dᵀ*D).det ≠ 0) (y : Fin n → ℝ) (c : Fin p → ℝ) :
    ols D (y+D*ᵥc) = ols D y+c := by
  have he : ols D (y+D*ᵥc) = ols D y+ols D (D*ᵥc) := by
    simp only [ols, Matrix.mulVec_add]
  rw [he, olsr_fits D hrank c]

lemma olsr_measurable {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) :
    Measurable (ols D) := by
  apply Measurable.of_eval
  intro a
  simp only [ols, Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum Finset.univ fun j _ => measurable_const.mul
    (Finset.measurable_sum Finset.univ fun i _ =>
      measurable_const.mul (measurable_pi_apply i))

lemma olsr_target {n p : ℕ} (hn : 0 < n) (m : Model n)
    (D : Matrix (Fin n) (Fin p) ℝ) (b : Fin p → ℝ) (j : Fin p)
    (hrank : (Dᵀ*D).det ≠ 0) (hm : MeanModel m D b)
    (hθ : ∀ i, m.theta i = olsTheta D j i) :
    (∀ y, betaHat m y = ols D y j) ∧ beta m = b j := by
  have ht (y : Fin n → ℝ) : betaHat m y = ols D y j := by
    rw [(ols_linear_unbiased hn m D b hrank hm).1 j y]
    simp only [betaHat, average, weighted, hθ]
  refine ⟨ht, ?_⟩
  change expectation m (betaHat m) = b j
  rw [show betaHat m = (fun y => ols D y j) from funext ht]
  exact (ols_linear_unbiased hn m D b hrank hm).2 j

lemma olsr_shifts {n p : ℕ} (hn : 0 < n) (m : Model n)
    (D : Matrix (Fin n) (Fin p) ℝ) (b : Fin p → ℝ) (j : Fin p)
    (hrank : (Dᵀ*D).det ≠ 0) (hm : MeanModel m D b)
    (hθ : ∀ i, m.theta i = olsTheta D j i) (y : Fin n → ℝ) (c : Fin p → ℝ) :
    fittedResidual m D (ols D) (y+D*ᵥc) = fittedResidual m D (ols D) y ∧
      centered (weighted m (y+D*ᵥc)) = centered (weighted m y) +
        (fun i => m.theta i*(D*ᵥc) i-c j) := by
  constructor
  · ext i
    simp only [fittedResidual, olsr_add D hrank, Matrix.mulVec_add, Pi.add_apply]
    ring
  · have ha : average (weighted m (y+D*ᵥc)) = average (weighted m y)+c j := by
      change betaHat m (y+D*ᵥc) = betaHat m y+c j
      rw [(olsr_target hn m D b j hrank hm hθ).1,
        (olsr_target hn m D b j hrank hm hθ).1, olsr_add D hrank]
      rfl
    ext i
    simp only [centered, ha, weighted, Pi.add_apply]
    ring

def olsr_score {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) (b : Fin p → ℝ)
    (y : Fin n → ℝ) : Fin p → ℝ := Dᵀ*ᵥ(y-D*ᵥb)

lemma olsr_score_coordinate {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ)
    (b : Fin p → ℝ) (y : Fin n → ℝ) (a : Fin p) :
    olsr_score D b y a = ∑ i, D i a*(y i-(D*ᵥb) i) := by
  rfl

lemma olsr_score_equation {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ)
    (hrank : (Dᵀ*D).det ≠ 0) (b : Fin p → ℝ) (y : Fin n → ℝ) :
    (Dᵀ*D)*ᵥ(ols D y-b) = olsr_score D b y := by
  have he : (Dᵀ*D)*ᵥ(ols D y) = Dᵀ*ᵥy := by
    unfold ols
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hrank), Matrix.one_mulVec]
  rw [Matrix.mulVec_sub, he]
  simp only [olsr_score, Matrix.mulVec_sub, Matrix.mulVec_mulVec]

lemma olsr_quadratic_dot {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ)
    (v : Fin p → ℝ) (t : ℝ) :
    quadratic (t • M) v = t*(∑ a, v a*(M*ᵥv) a) := by
  simp [quadratic, Matrix.smul_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_comm, mul_left_comm]

/-- Coercivity converts the normal equation into a bound on the coefficient error. -/
lemma olsr_error_bound {n p : ℕ} (hn : 0 < n)
    (D : Matrix (Fin n) (Fin p) ℝ) (hrank : (Dᵀ*D).det ≠ 0)
    (b : Fin p → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hG : ∀ z, lam*l2 z^2 ≤ quadratic ((1/(n : ℝ)) • (Dᵀ*D)) z)
    (y : Fin n → ℝ) :
    l2 (ols D y-b) ≤ l2 (olsr_score D b y)/((n : ℝ)*lam) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let v := ols D y-b
  let s := olsr_score D b y
  have hv : 0 ≤ l2 v := DenseCompletion.l2_nonneg _
  have hs : 0 ≤ l2 s := DenseCompletion.l2_nonneg _
  have he : (Dᵀ*D)*ᵥv = s := olsr_score_equation D hrank b y
  have hco := hG v
  rw [olsr_quadratic_dot, he] at hco
  have hcs := (le_abs_self (∑ a, v a*s a)).trans (rrn_dot_bound v s)
  have hc : lam*l2 v^2 ≤ (l2 v*l2 s)/(n : ℝ) := by
    calc
      _ ≤ (1/(n : ℝ))*(∑ a, v a*s a) := hco
      _ ≤ (1/(n : ℝ))*(l2 v*l2 s) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = _ := by ring
  apply (le_div_iff₀ (mul_pos hnR hlam)).mpr
  by_cases hz : l2 v = 0
  · change l2 v*((n : ℝ)*lam) ≤ l2 s
    rw [hz, zero_mul]
    exact hs
  · have hvpos : 0 < l2 v := lt_of_le_of_ne hv (Ne.symm hz)
    have hh := (le_div_iff₀ hnR).mp hc
    have hmul : (l2 v*((n : ℝ)*lam))*l2 v ≤ l2 s*l2 v := by
      nlinarith only [hh]
    exact (mul_le_mul_iff_left₀ hvpos).mp hmul

lemma olsr_coordinate_le_l2 {p : ℕ} (v : Fin p → ℝ) (a : Fin p) :
    |v a| ≤ l2 v := by
  apply (sq_le_sq₀ (abs_nonneg _) (DenseCompletion.l2_nonneg _)).mp
  rw [sq_abs, DenseCompletion.l2_sq]
  exact Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ a)

lemma olsr_raw_mean_bound {n p : ℕ} (m : Model n)
    (D : Matrix (Fin n) (Fin p) ℝ) (b : Fin p → ℝ) (hm : MeanModel m D b)
    (By : ℝ) (hy : ∀ᵐ y ∂m.law, ∀ i, |y i| ≤ By) (i : Fin n) :
    |(D*ᵥb) i| ≤ By := by
  let : IsProbabilityMeasure m.law := m.probability
  rw [← hm.2 i]
  change |∫ y, y i ∂m.law| ≤ By
  calc
    _ ≤ ∫ y, |y i| ∂m.law := abs_integral_le_integral_abs
    _ ≤ ∫ _, By ∂m.law := integral_mono_ae (hm.1 i).abs
      (integrable_const _) (hy.mono fun y h => h i)
    _ = _ := by simp

/-- Every coordinate of the raw OLS score has a bounded second moment.
The synthetic model changes only the deterministic coordinate weights, preserving
the actual outcome law and the full dependency hypothesis. -/
lemma olsr_score_second_moment {n p : ℕ} (m : Model n)
    (D : Matrix (Fin n) (Fin p) ℝ) (b : Fin p → ℝ)
    (hm : MeanModel m D b) (hd : Dependency m)
    (Bx By d : ℝ) (hBx : 0 ≤ Bx) (hBy : 0 ≤ By)
    (hx : ∀ i, l2 (D i) ≤ Bx)
    (hy : ∀ᵐ y ∂m.law, ∀ i, |y i| ≤ By)
    (hdegree : ∀ i, (degree m.G i : ℝ)+1 ≤ d) (a : Fin p) :
    MemLp (fun y => olsr_score D b y a) 2 m.law ∧
      (∫ y, (olsr_score D b y a)^2 ∂m.law) ≤ (n : ℝ)*d*(2*Bx*By)^2 := by
  classical
  let : IsProbabilityMeasure m.law := m.probability
  let w : Model n := {m with theta := fun i => D i a}
  let shift : Fin n → ℝ := fun i => D i a*(D*ᵥb) i
  have hdep : Dependency w := hd
  let dep := msr_dep w hdep shift
  have he (i : Fin n) (y : Fin n → ℝ) :
      msr_shift w shift i y = D i a*(y i-(D*ᵥb) i) := by
    dsimp [msr_shift, weighted, w, shift]
    ring
  have hb (i : Fin n) : ∀ᵐ y ∂m.law, |msr_shift w shift i y| ≤ 2*Bx*By := by
    filter_upwards [hy] with y h
    rw [he, abs_mul]
    have hi : |D i a| ≤ Bx := (olsr_coordinate_le_l2 (D i) a).trans (hx i)
    have hj : |y i-(D*ᵥb) i| ≤ 2*By := by
      calc
        _ ≤ |y i|+|(D*ᵥb) i| := abs_sub _ _
        _ ≤ By+By := add_le_add (h i) (olsr_raw_mean_bound m D b hm By hy i)
        _ = _ := by ring
    calc
      _ ≤ Bx*(2*By) := mul_le_mul hi hj (abs_nonneg _) hBx
      _ = _ := by ring
  have hL2 (i : Fin n) : MemLp (msr_shift w shift i) 2 m.law :=
    SampleCompletion.bounded_memLp m.law _ (dep.meas i) _ (hb i) 2
  have hsum : MemLp (fun y => ∑ i, msr_shift w shift i y) 2 m.law := by
    simpa using memLp_finsetSum Finset.univ (fun i _ => hL2 i)
  have hmeanX (i : Fin n) : (∫ y, msr_shift w shift i y ∂m.law) = 0 := by
    simp only [msr_shift, weighted]
    rw [integral_sub ((hm.1 i).const_mul _) (integrable_const _), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    change D i a*expectation m (fun y => y i) - D i a*(D*ᵥb) i = 0
    rw [hm.2 i, sub_self]
  have hmeanS : (∫ y, (∑ i, msr_shift w shift i y) ∂m.law) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i _ => (hL2 i).integrable (by norm_num))]
    simp only [hmeanX, Finset.sum_const_zero]
  have hnb (i : Fin n) : ((dep.nbhd i).card : ℝ) ≤ d := by
    change (((msr_dep w hdep shift).nbhd i).card : ℝ) ≤ d
    rw [msr_dep_degree]
    simpa only [Nat.cast_add, Nat.cast_one] using hdegree i
  have hv := SampleCompletion.graph_variance_sum m.law _ dep (2*Bx*By) d
    (by positivity) hb hnb
  rw [ProbabilityTheory.variance_eq_sub hsum] at hv
  simp only [Pi.pow_apply, hmeanS, zero_pow (by decide : 2 ≠ 0), sub_zero,
    Fintype.card_fin] at hv
  have hs (y : Fin n → ℝ) : (∑ i, msr_shift w shift i y) = olsr_score D b y a := by
    simp only [he, olsr_score_coordinate]
  exact ⟨by simpa only [hs] using hsum, by simpa only [hs] using hv⟩

lemma olsr_score_norm_moment {n p : ℕ} (hn : 0 < n) (m : Model n)
    (D : Matrix (Fin n) (Fin p) ℝ) (b : Fin p → ℝ)
    (hm : MeanModel m D b) (hd : Dependency m)
    (Bx By d : ℝ) (hBx : 0 ≤ Bx) (hBy : 0 ≤ By)
    (hx : ∀ i, l2 (D i) ≤ Bx)
    (hy : ∀ᵐ y ∂m.law, ∀ i, |y i| ≤ By)
    (hdegree : ∀ i, (degree m.G i : ℝ)+1 ≤ d) :
    Integrable (fun y => (l2 (olsr_score D b y)/Real.sqrt (n : ℝ))^2) m.law ∧
      (∫ y, (l2 (olsr_score D b y)/Real.sqrt (n : ℝ))^2 ∂m.law) ≤
        (p : ℝ)*d*(2*Bx*By)^2 := by
  let : IsProbabilityMeasure m.law := m.probability
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc (a : Fin p) := olsr_score_second_moment m D b hm hd Bx By d hBx hBy hx hy hdegree a
  have hi (a : Fin p) : Integrable (fun y => (olsr_score D b y a)^2) m.law :=
    (hc a).1.integrable_sq
  have he (y : Fin n → ℝ) : (l2 (olsr_score D b y)/Real.sqrt (n : ℝ))^2 =
      (∑ a, (olsr_score D b y a)^2)/(n : ℝ) := by
    rw [div_pow, DenseCompletion.l2_sq, Real.sq_sqrt hnR.le]
  constructor
  · simp_rw [he]
    exact (integrable_finsetSum Finset.univ (fun a _ => hi a)).div_const _
  · simp_rw [he]
    rw [integral_div, integral_finsetSum Finset.univ (fun a _ => hi a)]
    apply (div_le_iff₀ hnR).mpr
    calc
      _ ≤ ∑ _a : Fin p, (n : ℝ)*d*(2*Bx*By)^2 :=
        Finset.sum_le_sum (fun a _ => (hc a).2)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; ring

/-- A uniform second-moment bound implies the changing-row Tight contract. -/
lemma olsr_tight_of_moment (F : Family)
    (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hi : ∀ k, Integrable (fun y => (T k y)^2) (F.model k).law)
    (hb : ∀ k, (∫ y, (T k y)^2 ∂(F.model k).law) ≤ C) : Tight F T := by
  intro ε hε
  let B := Real.sqrt (C/ε)+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hBsq : C ≤ ε*B^2 := by
    have hs := Real.sq_sqrt (div_nonneg hC hε.le)
    have hp := Real.sqrt_nonneg (C/ε)
    have hh : C/ε ≤ B^2 := by dsimp [B]; nlinarith only [hs, hp]
    have hh' := (div_le_iff₀ hε).mp hh
    nlinarith only [hh']
  refine ⟨B, hB, 0, ?_⟩
  intro k _
  let : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  have hsub : {y | |T k y| > B} ⊆ {y | B^2 ≤ (T k y)^2} := by
    intro y hy
    change B < |T k y| at hy
    change B^2 ≤ (T k y)^2
    have hh := (sq_lt_sq₀ hB.le (abs_nonneg (T k y))).mpr hy
    simpa only [sq_abs] using hh.le
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := (F.model k).law) (f := fun y => (T k y)^2)
    (Eventually.of_forall fun y => sq_nonneg (T k y)) (hi k) (B^2)
  have hp : (F.model k).law.real {y | B^2 ≤ (T k y)^2} ≤ ε := by
    have hm' := hm.trans (hb k)
    have hsq : 0 < B^2 := sq_pos_of_pos hB
    exact (mul_le_mul_iff_right₀ hsq).mp (by
      calc
        B^2 * (F.model k).law.real {y | B^2 ≤ (T k y)^2} ≤ C := hm'
        _ ≤ B^2*ε := by nlinarith only [hBsq])
  exact (measureReal_mono (μ := (F.model k).law) hsub (measure_ne_top _ _)).trans hp

lemma olsr_root_n_rate (F : Family) (p : ℕ)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (b : Fin p → ℝ)
    (hrank : ∀ k, ((D k)ᵀ*D k).det ≠ 0)
    (hmean : ∀ k, MeanModel (F.model k) (D k) b)
    (hdep : ∀ k, Dependency (F.model k))
    (Bx By d lam : ℝ) (hBx : 0 ≤ Bx) (hBy : 0 ≤ By) (hd : 0 ≤ d) (hlam : 0 < lam)
    (hx : ∀ k i, l2 (D k i) ≤ Bx)
    (hy : ∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |y i| ≤ By)
    (hdegree : ∀ k i, (degree (F.model k).G i : ℝ)+1 ≤ d)
    (hG : ∀ k z, lam*l2 z^2 ≤ quadratic
      ((1/(F.size k : ℝ)) • ((D k)ᵀ*D k)) z) :
    Tight F (fun k y => Real.sqrt (F.size k : ℝ)*l2 (ols (D k) y-b)) := by
  let S : ∀ k, (Fin (F.size k) → ℝ) → ℝ := fun k y =>
    l2 (olsr_score (D k) b y)/Real.sqrt (F.size k : ℝ)
  have hm (k : ℕ) := olsr_score_norm_moment (F.positive k) (F.model k)
    (D k) b (hmean k) (hdep k) Bx By d hBx hBy (hx k) (hy k) (hdegree k)
  have hs : Tight F S := olsr_tight_of_moment F S ((p : ℝ)*d*(2*Bx*By)^2)
    (by positivity) (fun k => (hm k).1) (fun k => (hm k).2)
  apply rrn_tight_dominated F S _ (1/lam) (by positivity) hs
  intro k
  exact Eventually.of_forall fun y => by
    have hnR : 0 < (F.size k : ℝ) := by exact_mod_cast F.positive k
    have hsq : 0 < Real.sqrt (F.size k : ℝ) := Real.sqrt_pos.mpr hnR
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (DenseCompletion.l2_nonneg _)),
      abs_of_nonneg (div_nonneg (DenseCompletion.l2_nonneg _) (Real.sqrt_nonneg _))]
    calc
      _ ≤ Real.sqrt (F.size k : ℝ)*
          (l2 (olsr_score (D k) b y)/((F.size k : ℝ)*lam)) :=
        mul_le_mul_of_nonneg_left
          (olsr_error_bound (F.positive k) (D k) (hrank k) b lam hlam (hG k) y)
          (Real.sqrt_nonneg _)
      _ = (1/lam)*S k y := by
        dsimp [S]
        field_simp
        rw [Real.sq_sqrt hnR.le]
        ring

/-- The oracle part of residual stability does not require valid degree caps. -/
lemma olsr_residual_oracle (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (p : ℕ)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (b : Fin p → ℝ)
    (hm : ∀ k, MeanModel (F.model k) (D k) b)
    (hbound : ∃ B : ℝ, ∀ k i, l2 (D k i) ≤ B)
    (hrate : Tight F (fun k y => Real.sqrt (F.size k : ℝ)*l2 (ols (D k) y-b))) :
    InProbability F (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (ols (D k)) y)) (scaledTrue F) := by
  obtain ⟨hNest, hc1, hc2, hc3, hc4, hDep, hBound, hDeg, hVar, hTheta⟩ := h
  have hL2 (k : ℕ) (i : Fin (F.size k)) :=
    ProbabilityCompletion.weighted_memLp (F.model k) c1 (hBound k) i
  have hz (k : ℕ) : ∀ᵐ y ∂(F.model k).law,
      ∀ i, |trueResidual (F.model k) (D k) b y i| ≤ 2*c1 := by
    have hb := ProbabilityCompletion.own_centred_bound (F.model k) c1 (hL2 k) (hBound k)
    simpa only [rps_true_eq (F.model k) (D k) b (hm k)] using hb
  obtain ⟨B₀, hB₀⟩ := hbound
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hx (k : ℕ) (i : Fin (F.size k)) : l2 (D k i) ≤ B :=
    (hB₀ k i).trans (le_max_left _ _)
  let E : ∀ k, (Fin (F.size k) → ℝ) → (Fin (F.size k) → ℝ) := fun k y =>
    fittedResidual (F.model k) (D k) (ols (D k)) y-trueResidual (F.model k) (D k) b y
  have he (k : ℕ) (y : Fin (F.size k) → ℝ) :
      l2 (E k y) ≤ (c4*B)*(Real.sqrt (F.size k : ℝ)*l2 (ols (D k) y-b)) :=
    (rrn_error_norm_bounds (F.model k) (D k) b (ols (D k)) c4 B hc4.le hB
      (fun i => (hTheta k i).le) (hx k) y).2
  have ht : Tight F (fun k y => l2 (E k y)) := by
    apply rrn_tight_dominated F
      (fun k y => Real.sqrt (F.size k : ℝ)*l2 (ols (D k) y-b)) _
      (c4*B) (mul_nonneg hc4.le hB) hrate
    intro k
    exact Eventually.of_forall fun y => by
      rw [abs_of_nonneg (DenseCompletion.l2_nonneg _),
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (DenseCompletion.l2_nonneg _))]
      exact he k y
  have herr := rrn_tight_div_sqrt F (fun k y => l2 (E k y)) ht
  exact rps_oracle F c1 c2 c3 c4
    ⟨hNest, hc1, hc2, hc3, hc4, hDep, hBound, hDeg, hVar, hTheta⟩ p D b
    (fun k => ols (D k)) (fun k => olsr_measurable (D k)) hm ⟨2*c1, hz⟩ herr


/-- P011-T16: OLS mean, shift and rate properties. -/
theorem ols_repair_proof (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (p : ℕ) (j : Fin p) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (b : Fin p → ℝ)
    (hrank : ∀ k, ((D k)ᵀ*D k).det ≠ 0)
    (hmean : ∀ k, MeanModel (F.model k) (D k) b)
    (hθ : ∀ k i, (F.model k).theta i = olsTheta (D k) j i) :
    (∀ k i, delta (F.model k) i = olsTheta (D k) j i*(D k*ᵥb) i-b j) ∧
    InProbability F (fun k y => scaledOracle F k y-scaledTrue F k)
      (fun k => meanBias (F.model k)) ∧
    (∀ k y c, fittedResidual (F.model k) (D k) (ols (D k)) (y+D k*ᵥc) =
      fittedResidual (F.model k) (D k) (ols (D k)) y ∧
      centered (weighted (F.model k) (y+D k*ᵥc)) =
        centered (weighted (F.model k) y) +
          (fun i => (F.model k).theta i*(D k*ᵥc) i-c j)) ∧
    ((∃ Bx By lambdaMin : ℝ, 0 < lambdaMin ∧ (∀ k i, l2 (D k i) ≤ Bx) ∧
      (∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |y i| ≤ By) ∧
      (∀ k z, lambdaMin*l2 z^2 ≤ quadratic ((1/(F.size k : ℝ)) • ((D k)ᵀ*D k)) z)) →
      Tight F (fun k y => Real.sqrt (F.size k : ℝ)*l2 (ols (D k) y-b)) ∧
      InProbability F (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (ols (D k)) y)) (scaledTrue F) ∧
      (∀ A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k), Valid F →
        (∀ k y, Maximizes (F.model k).R (F.model k).d
          (fun B => VResidual B (fittedResidual (F.model k) (D k) (ols (D k)) y)) (A k y)) →
        Conservative F (fun k y => VResidual (A k y)
          (fittedResidual (F.model k) (D k) (ols (D k)) y)))) := by
  have ht (k : ℕ) := olsr_target (F.positive k) (F.model k) (D k) b j
    (hrank k) (hmean k) (hθ k)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k i
    unfold delta
    rw [rps_weighted_mean (F.model k) (D k) b (hmean k), (ht k).2, hθ k i]
  · intro ε hε
    have ho := revised_oracle_convergence F c1 c2 c3 c4 h ε hε
    convert ho using 1
    funext k
    congr 1
    ext y
    change (ε < |scaledOracle F k y-scaledTrue F k-meanBias (F.model k)|) ↔
      (ε < |scaledOracle F k y-(scaledTrue F k+meanBias (F.model k))|)
    rw [sub_sub]
  · intro k y c
    exact olsr_shifts (F.positive k) (F.model k) (D k) b j
      (hrank k) (hmean k) (hθ k) y c
  · rintro ⟨Bx₀, By₀, lam, hlam, hx₀, hy₀, hG⟩
    let Bx := max Bx₀ 0
    let By := max By₀ 0
    have hBx : 0 ≤ Bx := le_max_right _ _
    have hBy : 0 ≤ By := le_max_right _ _
    have hx (k : ℕ) (i : Fin (F.size k)) : l2 (D k i) ≤ Bx :=
      (hx₀ k i).trans (le_max_left _ _)
    have hy (k : ℕ) : ∀ᵐ y ∂(F.model k).law, ∀ i, |y i| ≤ By := by
      filter_upwards [hy₀ k] with y hh i
      exact (hh i).trans (le_max_left _ _)
    have hcopy := h
    obtain ⟨hNest, hc1, hc2, hc3, hc4, hDep, hBound, hDeg, hVar, hTheta⟩ := hcopy
    have hrate := olsr_root_n_rate F p D b hrank hmean hDep Bx By (c2+1) lam
      hBx hBy (by positivity) hlam hx hy
      (fun k i => by linarith [hDeg k i]) hG
    have ho := olsr_residual_oracle F c1 c2 c3 c4 h p D b hmean ⟨Bx, hx⟩ hrate
    refine ⟨hrate, ho, ?_⟩
    intro A hv hm
    exact rps_maximum_conservative F
      (fun k y => fittedResidual (F.model k) (D k) (ols (D k)) y) A hv hm ho

end
end AronowAudit.P011.Wave1
