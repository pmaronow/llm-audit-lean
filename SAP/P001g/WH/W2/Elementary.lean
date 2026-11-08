import SAP.P001g.Defs.WholeW2
import AronowAudit.P001.P001_PrintedRefutations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g.WH.W2

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
universe u

theorem sqrtTwoBoundsW2 : (1.41 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.42 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem discBoundsW2 (z : Fin 2 → ℝ) (hz : z ∈ circleDiscW2) :
    (-1 ≤ z 0 ∧ z 0 ≤ 1) ∧ (-1 ≤ z 1 ∧ z 1 ≤ 1) := by
  change z 0 ^ 2 + z 1 ^ 2 ≤ 1 at hz
  constructor <;> constructor <;>
    nlinarith [sq_nonneg (z 0), sq_nonneg (z 1),
      sq_nonneg (z 0 - 1), sq_nonneg (z 0 + 1),
      sq_nonneg (z 1 - 1), sq_nonneg (z 1 + 1)]

theorem affineSumW2 (z : Fin 2 → ℝ) : ∑ y, circleAffineW2 z y = 1 := by
  simp [circleAffineW2, Fin.sum_univ_succ]
  ring

/-- A positive uniform lower bound; in particular all logarithms used by the
blueprint are logarithms of positive real numbers. -/
theorem affineLowerW2 (z : Fin 2 → ℝ) (hz : z ∈ circleDiscW2) (y : Fin 3) :
    (19 / 100 : ℝ) < circleAffineW2 z y := by
  obtain ⟨hs0, hs1⟩ := sqrtTwoBoundsW2
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩ := discBoundsW2 z hz
  have hs : z 0 ^ 2 + z 1 ^ 2 ≤ 1 := hz
  have hdiff : -(3 / 2 : ℝ) < z 1 - z 0 := by
    nlinarith [sq_nonneg (z 0 + z 1)]
  fin_cases y <;> simp [circleAffineW2] <;> linarith

theorem affinePosW2 (z : Fin 2 → ℝ) (hz : z ∈ circleDiscW2) (y : Fin 3) :
    0 < circleAffineW2 z y := lt_trans (by norm_num) (affineLowerW2 z hz y)

theorem mixProjectionW2 (t : Fin 3 → ℝ) :
    circleMixW2 t = circleAffineW2 (circleProjectionW2 t) := by
  ext y
  fin_cases y <;> simp [circleMixW2, circleSecondW2, circleAffineW2,
    circleProjectionW2, circleBaseW2] <;> ring

theorem likeProjectionW2 {n : ℕ} (s : Fin n → Fin 3) (t : Fin 3 → ℝ) :
    circleLikeW2 s t = circleDiscLikeW2 s (circleProjectionW2 t) := by
  simp only [circleLikeW2, circleDiscLikeW2, mixProjectionW2]

theorem projectionMemW2 (t : Fin 3 → ℝ) (ht : t ∈ circleThetaW2) :
    circleProjectionW2 t ∈ circleDiscW2 := by
  obtain ⟨⟨hp0, hp1⟩, hb⟩ := ht
  change ((1 - t 0) * t 1) ^ 2 + ((1 - t 0) * t 2) ^ 2 ≤ 1
  calc
    _ = (1 - t 0) ^ 2 * (t 1 ^ 2 + t 2 ^ 2) := by ring
    _ = (1 - t 0) ^ 2 := by rw [hb, mul_one]
    _ ≤ 1 := by nlinarith

theorem mixTrueW2 (b : Fin 2 → ℝ) : circleMixW2 (circleTruthW2 b) = circleBaseW2 := by
  ext y
  simp [circleMixW2, circleTruthW2]

theorem truthMemW2 (b : Fin 2 → ℝ) (hb : b ∈ circleBoundaryW2) :
    circleTruthW2 b ∈ circleThetaW2 := by
  simpa [circleTruthW2, circleThetaW2, circleBoundaryW2] using hb

theorem baseSumW2 : ∑ y, circleBaseW2 y = 1 := by
  simp [circleBaseW2, Fin.sum_univ_succ]
  ring

theorem basePosW2 (y : Fin 3) : 0 < circleBaseW2 y := by
  have hz : (0 : Fin 2 → ℝ) ∈ circleDiscW2 := by norm_num [circleDiscW2]
  simpa [circleAffineW2, circleBaseW2] using affinePosW2 0 hz y

theorem affineContinuousW2 (y : Fin 3) : Continuous (fun z => circleAffineW2 z y) := by
  fin_cases y <;> simp only [circleAffineW2] <;> fun_prop

theorem discLikeContinuousW2 {n : ℕ} (s : Fin n → Fin 3) :
    Continuous (circleDiscLikeW2 s) := by
  unfold circleDiscLikeW2
  exact continuous_finsetProd _ fun i _ => affineContinuousW2 (s i)

theorem mixContinuousW2 (y : Fin 3) : Continuous (fun t => circleMixW2 t y) := by
  simp only [mixProjectionW2]
  apply (affineContinuousW2 y).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [circleProjectionW2] <;> fun_prop

theorem discCompactW2 : IsCompact circleDiscW2 := by
  have hc : IsClosed circleDiscW2 :=
    isClosed_le (by fun_prop) continuous_const
  apply (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc (a := (-1 : ℝ)) (b := 1)).of_isClosed_subset hc
  intro z hz i _
  fin_cases i
  · exact (discBoundsW2 z hz).1
  · exact (discBoundsW2 z hz).2

theorem thetaCompactW2 : IsCompact circleThetaW2 := by
  have hc : IsClosed circleThetaW2 :=
    (isClosed_Icc.preimage (continuous_apply 0)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  apply (isCompact_univ_pi fun _ : Fin 3 => isCompact_Icc (a := (-1 : ℝ)) (b := 1)).of_isClosed_subset hc
  intro t ht i _
  change -1 ≤ t i ∧ t i ≤ 1
  obtain ⟨⟨hp0, hp1⟩, hb⟩ := ht
  fin_cases i
  · change -1 ≤ t 0 ∧ t 0 ≤ 1
    exact ⟨by linarith, hp1⟩
  · change -1 ≤ t 1 ∧ t 1 ≤ 1
    constructor <;> nlinarith [sq_nonneg (t 2), sq_nonneg (t 1 - 1), sq_nonneg (t 1 + 1)]
  · change -1 ≤ t 2 ∧ t 2 ≤ 1
    constructor <;> nlinarith [sq_nonneg (t 1), sq_nonneg (t 2 - 1), sq_nonneg (t 2 + 1)]

/-- Polar coordinates give a full-vector preimage of every disc point. -/
theorem projectionSurjectiveW2 (z : Fin 2 → ℝ) (hz : z ∈ circleDiscW2) :
    ∃ t ∈ circleThetaW2, circleProjectionW2 t = z := by
  by_cases hzero : z = 0
  · subst z
    refine ⟨![1, 1, 0], ?_, ?_⟩ <;>
      norm_num [circleThetaW2, circleProjectionW2, funext_iff, Fin.forall_fin_two]
  · let r : ℝ := Real.sqrt (z 0 ^ 2 + z 1 ^ 2)
    have hspos : 0 < z 0 ^ 2 + z 1 ^ 2 := by
      by_contra h
      have ha : z 0 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
      have hb : z 1 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
      apply hzero
      ext i
      fin_cases i <;> simp [ha, hb]
    have hr : 0 < r := Real.sqrt_pos.2 hspos
    have hr1 : r ≤ 1 := Real.sqrt_le_one.2 hz
    have hrsq : r ^ 2 = z 0 ^ 2 + z 1 ^ 2 := Real.sq_sqrt hspos.le
    refine ⟨![1 - r, z 0 / r, z 1 / r], ?_, ?_⟩
    · change 1 - r ∈ Set.Icc (0 : ℝ) 1 ∧ (z 0 / r) ^ 2 + (z 1 / r) ^ 2 = 1
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      field_simp
      nlinarith [hrsq]
    · ext i
      fin_cases i <;> simp [circleProjectionW2] <;> field_simp

/-- The only fibre with more than one full vector is the fibre over zero. -/
theorem projectionInjectiveW2 (t v : Fin 3 → ℝ) (ht : t ∈ circleThetaW2)
    (hv : v ∈ circleThetaW2) (heq : circleProjectionW2 t = circleProjectionW2 v)
    (hne : circleProjectionW2 t ≠ 0) : t = v := by
  obtain ⟨⟨ht0, ht1⟩, htc⟩ := ht
  obtain ⟨⟨hv0, hv1⟩, hvc⟩ := hv
  have he0 : (1 - t 0) * t 1 = (1 - v 0) * v 1 := congrFun heq 0
  have he1 : (1 - t 0) * t 2 = (1 - v 0) * v 2 := congrFun heq 1
  have hrsq : (1 - t 0) ^ 2 = (1 - v 0) ^ 2 := by
    calc
      _ = ((1 - t 0) * t 1) ^ 2 + ((1 - t 0) * t 2) ^ 2 := by nlinarith [htc]
      _ = ((1 - v 0) * v 1) ^ 2 + ((1 - v 0) * v 2) ^ 2 := by rw [he0, he1]
      _ = (1 - v 0) ^ 2 := by nlinarith [hvc]
  have hp : t 0 = v 0 := by nlinarith
  have htp : 1 - t 0 ≠ 0 := by
    intro h
    apply hne
    ext i
    fin_cases i <;> simp [circleProjectionW2, h]
  have hb1 : t 1 = v 1 := by rw [← hp] at he0; exact mul_left_cancel₀ htp he0
  have hb2 : t 2 = v 2 := by rw [← hp] at he1; exact mul_left_cancel₀ htp he1
  ext i
  fin_cases i <;> assumption

theorem affineTwoEqualW2 (z v : Fin 2 → ℝ) (a b : Fin 3) (hab : a ≠ b)
    (ha : circleAffineW2 z a = circleAffineW2 v a)
    (hb : circleAffineW2 z b = circleAffineW2 v b) : z = v := by
  have h0 : z 0 = v 0 := by
    fin_cases a <;> fin_cases b <;> simp_all [circleAffineW2]
  have h1 : z 1 = v 1 := by
    fin_cases a <;> fin_cases b <;> simp_all [circleAffineW2]
  ext i
  fin_cases i <;> assumption

theorem countSumW2 {n : ℕ} (s : Fin n → Fin 3) :
    circleCountW2 s 0 + circleCountW2 s 1 + circleCountW2 s 2 = n := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin 3)) s
  simpa [circleCountW2, Fin.sum_univ_succ, Nat.add_assoc] using h

/-- An integer empirical histogram of positive size cannot have the two
stationarity equations at c: these equations would make √2 rational. -/
theorem countsNotCriticalW2 (N : Fin 3 → ℕ) (hn : 0 < N 0 + N 1 + N 2)
    (h01 : (N 0 : ℝ) * circleBaseW2 1 = (N 1 : ℝ) * circleBaseW2 0)
    (h12 : (N 1 : ℝ) * circleBaseW2 2 = (N 2 : ℝ) * circleBaseW2 1) : False := by
  simp only [circleBaseW2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h01 h12
  have hs : 0 < Real.sqrt 2 := by positivity
  have e01 : (N 0 : ℝ) = N 1 := by nlinarith [h01]
  have key : (4 * (N 1 : ℝ)) = Real.sqrt 2 * (2 * N 1 + N 2) := by linarith [h12]
  by_cases hz : (2 * (N 1 : ℝ) + N 2) = 0
  · have h1 : (N 1 : ℝ) = 0 := by
      have a : (0 : ℝ) ≤ N 1 := by positivity
      have b : (0 : ℝ) ≤ N 2 := by positivity
      linarith
    have h2 : (N 2 : ℝ) = 0 := by
      have b : (0 : ℝ) ≤ N 2 := by positivity
      linarith
    have h0 : (N 0 : ℝ) = 0 := by rw [e01, h1]
    have he : ((N 0 + N 1 + N 2 : ℕ) : ℝ) = 0 := by push_cast; linarith
    have he' : N 0 + N 1 + N 2 = 0 := by exact_mod_cast he
    omega
  · apply irrational_sqrt_two
    refine ⟨(4 * (N 1 : ℚ)) / (2 * N 1 + N 2), ?_⟩
    push_cast
    rw [div_eq_iff hz]
    linarith [key]

/-- The actual three-outcome law used to build an infinite i.i.d. stream. -/
def baseLawW2 : Measure (Fin 3) :=
  ∑ y : Fin 3, ENNReal.ofReal (circleBaseW2 y) • Measure.dirac y

instance baseLawProbabilityW2 : IsProbabilityMeasure baseLawW2 := by
  constructor
  simp only [baseLawW2, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem, Set.mem_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => (basePosW2 y).le), baseSumW2]
  norm_num

end
end SAP.P001g.WH.W2
