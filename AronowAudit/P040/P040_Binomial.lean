import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-! P040, manipulation check.  The binomial sampling hypothesis is an additional
assumption of the correction, not the randomized assignment of days.
All probabilities below are actual finite binomial sums, not empirical proportions.
-/

namespace AronowAudit.P040
open scoped BigOperators
noncomputable section

/-- "Fifteen customers were asked" and "all but one ... were able to discern"
(paper p. 3, right column). The possible detection counts are 0 through 15. -/
abbrev DetectionCount := Fin 16

/-- Under the correction's independent common-probability sampling model,
"P_p(X = k) = choose(15,k) p^k (1-p)^(15-k)" (T1/T2).
The paper itself specifies no sampling model. -/
def binomialMass (p : ℝ) (k : DetectionCount) : ℝ :=
  (Nat.choose 15 k.val : ℝ) * p ^ k.val * (1 - p) ^ (15 - k.val)

/-- "P_p(E) = sum ..." (targets S7). Probability of a count event under the
binomial sampling assumption. -/
def countProbability (p : ℝ) (E : DetectionCount → Prop) : ℝ := by
  classical
  exact ∑ k, if E k then binomialMass p k else 0

/-- "coverage of a rule I at p, that is P_p(p ∈ I(X))" (T1 definitions).
A rule can be any deterministic function of the count. -/
def intervalCoverage (p : ℝ) (I : DetectionCount → Set ℝ) : ℝ :=
  countProbability p (fun k => p ∈ I k)

/-- "a real x rounds ... when w - 1/200 ≤ x < w + 1/200" (targets S7).
Two-decimal rounding, including the lower boundary and excluding the upper one. -/
def roundsTwo (x w : ℝ) : Prop := w - 1 / 200 ≤ x ∧ x < w + 1 / 200

/-- "c_k = k/15" (T1 A3), the observed detection proportion. -/
def detectionProportion (k : DetectionCount) : ℝ := (k.val : ℝ) / 15

/-- "r_k = z sqrt(c_k(1-c_k)/15)" (T1 A3–A4).
This reconstructs the printed interval; the paper does not name its method. -/
def waldRadius (z : ℝ) (k : DetectionCount) : ℝ :=
  z * Real.sqrt (detectionProportion k * (1 - detectionProportion k) / 15)

/-- "I_W(k) = [c_k-r_k,c_k+r_k]" (T1 A3).
The multiplier is explicit to cover the robustness assertion A4. -/
def waldInterval (z : ℝ) (k : DetectionCount) : Set ℝ :=
  Set.Icc (detectionProportion k - waldRadius z k)
    (detectionProportion k + waldRadius z k)

/-- The binomial masses are nonnegative for every admissible common detection
probability (finite probability-space lemma for T1 and T2). -/
theorem binomialMass_nonneg {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (k : DetectionCount) : 0 ≤ binomialMass p k := by
  unfold binomialMass
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp.1 _))
    (pow_nonneg (sub_nonneg.mpr hp.2) _)

/-- The binomial masses sum to one (T1/T2 setting, targets S7), including p=0,1. -/
theorem binomialMass_total (p : ℝ) : (∑ k : DetectionCount, binomialMass p k) = 1 := by
  unfold binomialMass
  rw [show (∑ k : DetectionCount,
      (Nat.choose 15 k.val : ℝ) * p ^ k.val * (1 - p) ^ (15 - k.val)) =
      ∑ k ∈ Finset.range 16, (Nat.choose 15 k : ℝ) * p ^ k * (1 - p) ^ (15 - k) from
    Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      (Nat.choose 15 k : ℝ) * p ^ k * (1 - p) ^ (15 - k)) 16]
  calc
    (∑ k ∈ Finset.range 16, (Nat.choose 15 k : ℝ) * p ^ k * (1 - p) ^ (15 - k))
        = (p + (1 - p)) ^ 15 := by
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = 1 := by ring

/-- P040-T1 A1: at p=4/5 the observed count 14 has the exact probability
805306368/6103515625, which exceeds 1/20. -/
theorem observed_count_mass :
    binomialMass (4 / 5) 14 = (805306368 : ℝ) / 6103515625 ∧
    (1 : ℝ) / 20 < binomialMass (4 / 5) 14 := by
  norm_num [binomialMass, Nat.choose]

/-- An event that excludes count 14 has probability at most one minus its mass
(P040-T1 A2), without assumptions about the other counts or interval method. -/
theorem exclude_observed_count_bound (E : DetectionCount → Prop) (hE : ¬ E 14) :
    countProbability (4 / 5) E ≤ (5298209257 : ℝ) / 6103515625 := by
  classical
  have hsum : countProbability (4 / 5) E ≤
      ∑ k ∈ (Finset.univ.erase (14 : DetectionCount)), binomialMass (4 / 5) k := by
    unfold countProbability
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (14 : DetectionCount))]
    simp only [if_neg hE, add_zero]
    apply Finset.sum_le_sum
    intro k hk
    split_ifs
    · exact le_rfl
    · exact binomialMass_nonneg (by norm_num) k
  have htotal := binomialMass_total (4 / 5)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (14 : DetectionCount))] at htotal
  have hm := observed_count_mass.1
  linarith

/-- P040-T1 A2, method-free counterexample: every deterministic interval rule
excluding 4/5 at count 14 has coverage at most .86805860466688, below .95. -/
theorem method_free_counterexample (I : DetectionCount → Set ℝ)
    (hI : (4 / 5 : ℝ) ∉ I 14) :
    intervalCoverage (4 / 5) I ≤ (5298209257 : ℝ) / 6103515625 ∧
    intervalCoverage (4 / 5) I < (19 : ℝ) / 20 := by
  have h := exclude_observed_count_bound (fun k => (4 / 5 : ℝ) ∈ I k) hI
  exact ⟨h, lt_of_le_of_lt h (by norm_num)⟩

/-- P040-T1 A2: the identical obstruction for every deterministic lower bound
whose value at count 14 exceeds .80. -/
theorem lower_bound_counterexample (ell : DetectionCount → ℝ)
    (hell : (4 / 5 : ℝ) < ell 14) :
    countProbability (4 / 5) (fun k => ell k ≤ 4 / 5) ≤
        (5298209257 : ℝ) / 6103515625 ∧
    countProbability (4 / 5) (fun k => ell k ≤ 4 / 5) < (19 : ℝ) / 20 := by
  have h := exclude_observed_count_bound (fun k => ell k ≤ 4 / 5) (not_le.mpr hell)
  exact ⟨h, lt_of_le_of_lt h (by norm_num)⟩

/-- P040-T1 A2: the printed interval and every lower endpoint rounding to .81
exclude .80; this is independent of reconstructing an interval formula. -/
theorem printed_endpoint_excludes_witness :
    (4 / 5 : ℝ) ∉ Set.Ioo (81 / 100 : ℝ) (106 / 100) ∧
    (∀ l : ℝ, roundsTwo l (81 / 100) → (4 / 5 : ℝ) < l) := by
  constructor
  · norm_num
  · intro l hl
    unfold roundsTwo at hl
    linarith [hl.1]

/-- Squaring the Wald radius removes the square root (T1 A3–A4). -/
theorem waldRadius_sq (z : ℝ) (k : DetectionCount) :
    waldRadius z k ^ 2 = z ^ 2 *
      (detectionProportion k * (1 - detectionProportion k) / 15) := by
  have hk : (k.val : ℝ) ≤ 15 := by exact_mod_cast (Nat.le_of_lt_succ k.isLt)
  have hp : 0 ≤ detectionProportion k := by unfold detectionProportion; positivity
  have hq : detectionProportion k ≤ 1 := by unfold detectionProportion; linarith
  have hv : 0 ≤ detectionProportion k * (1 - detectionProportion k) / 15 := by
    exact div_nonneg (mul_nonneg hp (sub_nonneg.mpr hq)) (by norm_num)
  unfold waldRadius
  rw [mul_pow, Real.sq_sqrt hv]

/-- P040-T1 A3: interval membership is precisely the rational squared comparison
when the multiplier is nonnegative. -/
theorem wald_membership_sq (z : ℝ) (hz : 0 ≤ z) (p : ℝ) (k : DetectionCount) :
    p ∈ waldInterval z k ↔
      (p - detectionProportion k) ^ 2 ≤ z ^ 2 *
        (detectionProportion k * (1 - detectionProportion k) / 15) := by
  have hr : 0 ≤ waldRadius z k := mul_nonneg hz (Real.sqrt_nonneg _)
  rw [← waldRadius_sq]
  rw [sq_le_sq, abs_of_nonneg hr, abs_le]
  change _ ↔ _
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- P040-T1 A3(a): the reconstructed lower and upper endpoints lie in the
stated narrow decimal brackets and round to .81 and 1.06; the upper exceeds 1. -/
theorem printed_wald_arithmetic :
    detectionProportion 14 = (14 : ℝ) / 15 ∧
    detectionProportion 14 * (1 - detectionProportion 14) / 15 = (14 : ℝ) / 3375 ∧
    waldRadius (49 / 25) 14 ^ 2 = (33614 : ℝ) / 2109375 ∧
    (8070 / 10000 : ℝ) < detectionProportion 14 - waldRadius (49 / 25) 14 ∧
    detectionProportion 14 - waldRadius (49 / 25) 14 < (8071 / 10000 : ℝ) ∧
    (10595 / 10000 : ℝ) < detectionProportion 14 + waldRadius (49 / 25) 14 ∧
    detectionProportion 14 + waldRadius (49 / 25) 14 < (10596 / 10000 : ℝ) ∧
    roundsTwo (detectionProportion 14 - waldRadius (49 / 25) 14) (81 / 100) ∧
    roundsTwo (detectionProportion 14 + waldRadius (49 / 25) 14) (106 / 100) ∧
    (1 : ℝ) < detectionProportion 14 + waldRadius (49 / 25) 14 ∧
    (4 / 5 : ℝ) ∉ waldInterval (49 / 25) 14 := by
  have hc : detectionProportion 14 = (14 : ℝ) / 15 := by norm_num [detectionProportion]
  have hv : detectionProportion 14 * (1 - detectionProportion 14) / 15 =
      (14 : ℝ) / 3375 := by rw [hc]; norm_num
  have hs : waldRadius (49 / 25) 14 ^ 2 = (33614 : ℝ) / 2109375 := by
    rw [waldRadius_sq, hv]; norm_num
  have hn : 0 ≤ waldRadius (49 / 25) 14 := by unfold waldRadius; positivity
  have hlo : (126235 / 1000000 : ℝ) < waldRadius (49 / 25) 14 := by nlinarith
  have hhi : waldRadius (49 / 25) 14 < (126237 / 1000000 : ℝ) := by nlinarith
  refine ⟨hc, hv, hs, by linarith, by linarith, by linarith, by linarith,
    ?_, ?_, by linarith, ?_⟩
  · unfold roundsTwo; constructor <;> linarith
  · unfold roundsTwo; constructor <;> linarith
  · rw [wald_membership_sq _ (by norm_num)]
    norm_num [hc]

/-- P040-T1 A4: throughout the multiplier interval [1.9599,1.9601], .80 belongs
to the Wald interval exactly for counts 9 through 13. This also proves A3(b). -/
theorem wald_witness_membership (z : ℝ)
    (hzlo : (19599 / 10000 : ℝ) ≤ z) (hzhi : z ≤ (19601 / 10000 : ℝ))
    (k : DetectionCount) :
    (4 / 5 : ℝ) ∈ waldInterval z k ↔ 9 ≤ k.val ∧ k.val ≤ 13 := by
  have hz : 0 ≤ z := by linarith
  have hlo : (19599 / 10000 : ℝ) ^ 2 ≤ z ^ 2 := (sq_le_sq₀ (by norm_num) hz).2 hzlo
  have hhi : z ^ 2 ≤ (19601 / 10000 : ℝ) ^ 2 := (sq_le_sq₀ hz (by norm_num)).2 hzhi
  rw [wald_membership_sq z hz]
  fin_cases k <;> norm_num [detectionProportion] at * <;> nlinarith

/-- P040-T1 A3(d) and A4: the Wald lower endpoint is at most .80 exactly when
the count is at most 13, throughout the stated multiplier range. -/
theorem wald_lower_membership (z : ℝ)
    (hzlo : (19599 / 10000 : ℝ) ≤ z) (hzhi : z ≤ (19601 / 10000 : ℝ))
    (k : DetectionCount) :
    detectionProportion k - waldRadius z k ≤ (4 / 5 : ℝ) ↔ k.val ≤ 13 := by
  have hz : 0 ≤ z := by linarith
  have hr : 0 ≤ waldRadius z k := mul_nonneg hz (Real.sqrt_nonneg _)
  by_cases hk : k.val ≤ 12
  · have hc : detectionProportion k ≤ (4 / 5 : ℝ) := by
      unfold detectionProportion
      have hkr : (k.val : ℝ) ≤ 12 := by exact_mod_cast hk
      linarith
    constructor
    · intro h; omega
    · intro h; linarith
  · have hc : (4 / 5 : ℝ) ≤ detectionProportion k := by
      unfold detectionProportion
      have hkr : (13 : ℝ) ≤ k.val := by exact_mod_cast (show 13 ≤ k.val by omega)
      linarith
    have hu : (4 / 5 : ℝ) ≤ detectionProportion k + waldRadius z k := by linarith
    have hm := wald_witness_membership z hzlo hzhi k
    change (_ ↔ _)
    rw [waldInterval, Set.mem_Icc] at hm
    simpa [hu, show 9 ≤ k.val by omega] using hm

/-- P040-T1 A3(c–d) and A4: the exact two-sided and lower-bound coverage at
p=.80 is .814815425593344 and .832874232578048, respectively, both below .95. -/
theorem wald_coverage_counterexample (z : ℝ)
    (hzlo : (19599 / 10000 : ℝ) ≤ z) (hzhi : z ≤ (19601 / 10000 : ℝ)) :
    intervalCoverage (4 / 5) (waldInterval z) = (24866193408 : ℝ) / 30517578125 ∧
    intervalCoverage (4 / 5) (waldInterval z) < (19 : ℝ) / 20 ∧
    countProbability (4 / 5) (fun k => detectionProportion k - waldRadius z k ≤ 4 / 5) =
      (25417304461 : ℝ) / 30517578125 ∧
    countProbability (4 / 5) (fun k => detectionProportion k - waldRadius z k ≤ 4 / 5) <
      (19 : ℝ) / 20 := by
  have hi : intervalCoverage (4 / 5) (waldInterval z) =
      (24866193408 : ℝ) / 30517578125 := by
    unfold intervalCoverage countProbability
    simp_rw [wald_witness_membership z hzlo hzhi]
    norm_num [Fin.sum_univ_succ, binomialMass, Nat.choose]
  have hl : countProbability (4 / 5)
      (fun k => detectionProportion k - waldRadius z k ≤ 4 / 5) =
        (25417304461 : ℝ) / 30517578125 := by
    unfold countProbability
    simp_rw [wald_lower_membership z hzlo hzhi]
    norm_num [Fin.sum_univ_succ, binomialMass, Nat.choose]
  exact ⟨hi, by rw [hi]; norm_num, hl, by rw [hl]; norm_num⟩

/-- "S_k(p) = P_p(X ≥ k)" (T2; exact-binomial repair). -/
def upperDetectionTail (p : ℝ) (k : DetectionCount) : ℝ :=
  countProbability p (fun j => k ≤ j)

/-- "F_k(p) = P_p(X ≤ k)" (T2; exact-binomial repair). -/
def lowerDetectionTail (p : ℝ) (k : DetectionCount) : ℝ :=
  countProbability p (fun j => j ≤ k)

/-- "C(k) = {p ∈ [0,1] : S_k(p) ≥ 1/40 and F_k(p) ≥ 1/40}"
(T2). Equal-tailed exact 95% confidence set by test inversion. -/
def exactDetectionInterval (k : DetectionCount) : Set ℝ :=
  {p | p ∈ Set.Icc (0 : ℝ) 1 ∧
    (1 : ℝ) / 40 ≤ upperDetectionTail p k ∧ (1 : ℝ) / 40 ≤ lowerDetectionTail p k}

/-- "C⁺(k) = {p ∈ [0,1] : S_k(p) ≥ 1/20}" (T2).
Exact one-sided 95% lower confidence set; no claim about unsampled patrons. -/
def exactDetectionLowerSet (k : DetectionCount) : Set ℝ :=
  {p | p ∈ Set.Icc (0 : ℝ) 1 ∧ (1 : ℝ) / 20 ≤ upperDetectionTail p k}

/-- "S_14(p) = p^14 (15-14p)" (T2(ii)). -/
def observedUpperPolynomial (p : ℝ) : ℝ := p ^ 14 * (15 - 14 * p)

/-- P040-T2(i)/T3(P1): fourteen of fifteen detections rounds to the printed .93. -/
theorem observed_proportion_rounds : roundsTwo (detectionProportion 14) (93 / 100) := by
  norm_num [roundsTwo, detectionProportion]

/-- P040-T2(ii): both observed-count tail functions have their exact polynomial
form. These are identities, not approximations to binomial probabilities. -/
theorem observed_tail_identities (p : ℝ) :
    upperDetectionTail p 14 = observedUpperPolynomial p ∧
    lowerDetectionTail p 14 = 1 - p ^ 15 := by
  constructor
  · unfold upperDetectionTail countProbability observedUpperPolynomial
    norm_num [Fin.sum_univ_succ, binomialMass, Nat.choose]
    ring
  · unfold lowerDetectionTail countProbability
    norm_num [Fin.sum_univ_succ, binomialMass, Nat.choose]
    ring

/-- The observed upper tail is continuous (P040-T2(ii)), proved from its
polynomial form rather than assumed as an axiom. -/
theorem observedUpper_continuous : Continuous observedUpperPolynomial := by
  unfold observedUpperPolynomial
  fun_prop

/-- P040-T2(ii): derivative 210 p^13(1-p) of the observed upper-tail polynomial. -/
theorem observedUpper_hasDerivAt (p : ℝ) :
    HasDerivAt observedUpperPolynomial (210 * p ^ 13 * (1 - p)) p := by
  unfold observedUpperPolynomial
  convert ((hasDerivAt_id p).pow 14).mul
    ((hasDerivAt_const p (15 : ℝ)).sub ((hasDerivAt_id p).const_mul 14)) using 1
  · funext x; simp
  · dsimp; ring

/-- P040-T2(ii): the observed upper tail is strictly increasing on [0,1],
including its endpoints, using the positive derivative on (0,1). -/
theorem observedUpper_strictMono : StrictMonoOn observedUpperPolynomial (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) observedUpper_continuous.continuousOn
  intro p hp
  rw [interior_Icc] at hp
  rw [(observedUpper_hasDerivAt p).deriv]
  exact mul_pos (mul_pos (by norm_num) (pow_pos hp.1 _)) (sub_pos.mpr hp.2)

/-- P040-T2(ii): F_14(p)=1-p^15 is strictly decreasing on [0,1]. -/
theorem observedLower_strictAnti : StrictAntiOn (fun p : ℝ => 1 - p ^ 15) (Set.Icc 0 1) := by
  intro p hp q hq hpq
  have hpow : p ^ 15 < q ^ 15 := pow_lt_pow_left₀ hpq hp.1 (by norm_num)
  linarith

/-- Event inclusion preserves binomial probability (T2 finite probability lemma). -/
theorem countProbability_mono {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {E F : DetectionCount → Prop} (hEF : ∀ k, E k → F k) :
    countProbability p E ≤ countProbability p F := by
  classical
  unfold countProbability
  apply Finset.sum_le_sum
  intro k hk
  by_cases he : E k
  · simp [he, hEF k he]
  · simp only [if_neg he]
    split_ifs
    · exact binomialMass_nonneg hp k
    · exact le_rfl

/-- The probability of an event plus that of its complement is one
(T2 finite probability lemma). -/
theorem countProbability_complement (p : ℝ) (E : DetectionCount → Prop) :
    countProbability p E + countProbability p (fun k => ¬ E k) = 1 := by
  classical
  unfold countProbability
  rw [← Finset.sum_add_distrib]
  convert binomialMass_total p using 1
  apply Finset.sum_congr rfl
  intro k hk
  by_cases he : E k <;> simp [he]

/-- The union bound for the two inverted binomial tail tests (T2(vi)). -/
theorem countProbability_union_le {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (E F : DetectionCount → Prop) :
    countProbability p (fun k => E k ∨ F k) ≤ countProbability p E + countProbability p F := by
  classical
  unfold countProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hm := binomialMass_nonneg hp k
  by_cases he : E k <;> by_cases hf : F k <;> simp [he, hf] <;> linarith

/-- Counts whose upper tail is below α have total probability at most α,
for any α≥0. The smallest such count supplies the upper-tail bound (T2(vi)). -/
theorem upper_tail_rejection_le {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {alpha : ℝ} (ha : 0 ≤ alpha) :
    countProbability p (fun k => upperDetectionTail p k < alpha) ≤ alpha := by
  classical
  let B := Finset.univ.filter (fun k : DetectionCount => upperDetectionTail p k < alpha)
  by_cases hB : B.Nonempty
  · let m := B.min' hB
    have hm : upperDetectionTail p m < alpha := (Finset.mem_filter.mp (B.min'_mem hB)).2
    have hsub : ∀ k, upperDetectionTail p k < alpha → m ≤ k := by
      intro k hk
      exact B.min'_le k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)
    exact (countProbability_mono hp hsub).trans hm.le
  · have hn : ∀ k : DetectionCount, ¬ upperDetectionTail p k < alpha := by
      intro k hk
      exact hB ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
    simpa [countProbability, hn] using ha

/-- Counts whose lower tail is below α have total probability at most α,
for α≥0. The largest such count supplies the lower-tail bound (T2(vi)). -/
theorem lower_tail_rejection_le {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {alpha : ℝ} (ha : 0 ≤ alpha) :
    countProbability p (fun k => lowerDetectionTail p k < alpha) ≤ alpha := by
  classical
  let B := Finset.univ.filter (fun k : DetectionCount => lowerDetectionTail p k < alpha)
  by_cases hB : B.Nonempty
  · let m := B.max' hB
    have hm : lowerDetectionTail p m < alpha := (Finset.mem_filter.mp (B.max'_mem hB)).2
    have hsub : ∀ k, lowerDetectionTail p k < alpha → k ≤ m := by
      intro k hk
      exact B.le_max' k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)
    exact (countProbability_mono hp hsub).trans hm.le
  · have hn : ∀ k : DetectionCount, ¬ lowerDetectionTail p k < alpha := by
      intro k hk
      exact hB ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
    simpa [countProbability, hn] using ha

/-- P040-T2(vi): under the independent common-probability binomial model, both
the exact equal-tailed interval and the exact one-sided lower set cover at least
95% for every p∈[0,1]. No exact equality of coverage is claimed. -/
theorem exact_binomial_coverage {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    intervalCoverage p exactDetectionInterval ≥ (19 : ℝ) / 20 ∧
    intervalCoverage p exactDetectionLowerSet ≥ (19 : ℝ) / 20 := by
  have hu := upper_tail_rejection_le hp (alpha := (1 : ℝ) / 40) (by norm_num)
  have hl := lower_tail_rejection_le hp (alpha := (1 : ℝ) / 40) (by norm_num)
  have hone := upper_tail_rejection_le hp (alpha := (1 : ℝ) / 20) (by norm_num)
  have hb := countProbability_union_le hp
    (fun k => upperDetectionTail p k < (1 : ℝ) / 40)
    (fun k => lowerDetectionTail p k < (1 : ℝ) / 40)
  have hc := countProbability_complement p (fun k => p ∈ exactDetectionInterval k)
  have hc1 := countProbability_complement p (fun k => p ∈ exactDetectionLowerSet k)
  have he : (fun k => ¬p ∈ exactDetectionInterval k) =
      (fun k => upperDetectionTail p k < (1 : ℝ) / 40 ∨
        lowerDetectionTail p k < (1 : ℝ) / 40) := by
    funext k
    apply propext
    change (¬ (p ∈ Set.Icc (0 : ℝ) 1 ∧ (1 : ℝ) / 40 ≤ upperDetectionTail p k ∧
      (1 : ℝ) / 40 ≤ lowerDetectionTail p k)) ↔ _
    simp only [hp, true_and, not_and_or, not_le]
  have he1 : (fun k => ¬p ∈ exactDetectionLowerSet k) =
      (fun k => upperDetectionTail p k < (1 : ℝ) / 20) := by
    funext k
    apply propext
    change (¬ (p ∈ Set.Icc (0 : ℝ) 1 ∧ (1 : ℝ) / 20 ≤ upperDetectionTail p k)) ↔ _
    simp only [hp, true_and, not_le]
  rw [he] at hc
  rw [he1] at hc1
  unfold intervalCoverage
  constructor <;> linarith

/-- P040-T2(iv): exact rational sign checks at the stated six-decimal brackets
for the equal-tailed lower, upper, and one-sided lower endpoints. -/
theorem exact_endpoint_sign_certificates :
    observedUpperPolynomial (680515 / 1000000) < (1 : ℝ) / 40 ∧
    (1 : ℝ) / 40 < observedUpperPolynomial (680516 / 1000000) ∧
    (998313 / 1000000 : ℝ) ^ 15 < (39 : ℝ) / 40 ∧
    (39 : ℝ) / 40 < (998314 / 1000000 : ℝ) ^ 15 ∧
    observedUpperPolynomial (720603 / 1000000) < (1 : ℝ) / 20 ∧
    (1 : ℝ) / 20 < observedUpperPolynomial (720604 / 1000000) := by
  norm_num [observedUpperPolynomial]

/-- P040-T2(v): .80 is contained in both corrected exact confidence sets; the
one-sided exact test's observed upper-tail probability is .167125767421952. -/
theorem exact_interval_contains_eighty_percent :
    upperDetectionTail (4 / 5) 14 = (5100273664 : ℝ) / 30517578125 ∧
    lowerDetectionTail (4 / 5) 14 = (29443836301 : ℝ) / 30517578125 ∧
    (4 / 5 : ℝ) ∈ exactDetectionInterval 14 ∧
    (4 / 5 : ℝ) ∈ exactDetectionLowerSet 14 := by
  have ht := observed_tail_identities (4 / 5)
  norm_num [observedUpperPolynomial] at ht
  refine ⟨ht.1, ht.2, ?_, ?_⟩
  · norm_num [exactDetectionInterval, ht.1, ht.2]
  · norm_num [exactDetectionLowerSet, ht.1]

/-- A continuous strictly increasing function attains any value bracketed by
two points, uniquely in [0,1]. Helper for the genuine endpoints in T2(iii–iv). -/
theorem unique_bracketed_root {f : ℝ → ℝ} (hf : Continuous f)
    (hm : StrictMonoOn f (Set.Icc 0 1)) {a b t : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hab : a ≤ b) (hat : f a < t) (hbt : t < f b) :
    ∃ x, x ∈ Set.Ioo a b ∧ f x = t ∧
      ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = t → y = x := by
  obtain ⟨x, hx, hxt⟩ := intermediate_value_Icc hab hf.continuousOn ⟨hat.le, hbt.le⟩
  have hx01 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  have hxa : a < x := by
    by_contra h
    have hxa' : x ≤ a := le_of_not_gt h
    have hfxa := hm.monotoneOn hx01 ha hxa'
    linarith
  have hxb : x < b := by
    by_contra h
    have hxb' : b ≤ x := le_of_not_gt h
    have hfbx := hm.monotoneOn hb hx01 hxb'
    linarith
  refine ⟨x, ⟨hxa, hxb⟩, hxt, ?_⟩
  intro y hy hyt
  exact hm.injOn hy hx01 (hyt.trans hxt.symm)

/-- P040-T2(iii–iv): unique roots for the two lower endpoints and the upper
endpoint, with the stated six-decimal brackets; the upper root is (39/40)^(1/15).
The equal-tailed and one-sided sets are exactly the closed intervals [L,U]
and [L_one,1]. Strict monotonicity is proved, not a hypothesis of the correction. -/
theorem corrected_binomial_endpoints :
    ∃ L U L_one : ℝ,
      (680515 / 1000000 : ℝ) < L ∧ L < (680516 / 1000000 : ℝ) ∧
      (998313 / 1000000 : ℝ) < U ∧ U < (998314 / 1000000 : ℝ) ∧
      (720603 / 1000000 : ℝ) < L_one ∧ L_one < (720604 / 1000000 : ℝ) ∧
      observedUpperPolynomial L = (1 : ℝ) / 40 ∧
      observedUpperPolynomial L_one = (1 : ℝ) / 20 ∧
      U ^ 15 = (39 : ℝ) / 40 ∧ U = (39 / 40 : ℝ) ^ ((15 : ℝ)⁻¹) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1, observedUpperPolynomial p = (1 : ℝ) / 40 → p = L) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1, observedUpperPolynomial p = (1 : ℝ) / 20 → p = L_one) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1, (1 - p ^ 15 : ℝ) = (1 : ℝ) / 40 → p = U) ∧
      exactDetectionInterval 14 = Set.Icc L U ∧
      exactDetectionLowerSet 14 = Set.Icc L_one 1 ∧
      L < L_one ∧ L_one < (4 / 5 : ℝ) ∧
      roundsTwo L (68 / 100) ∧ roundsTwo U 1 := by
  have hs := exact_endpoint_sign_certificates
  obtain ⟨L, hLbr, hLeq, hLuniq⟩ := unique_bracketed_root observedUpper_continuous
    observedUpper_strictMono (by norm_num : (680515 / 1000000 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (680516 / 1000000 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num) hs.1 hs.2.1
  obtain ⟨Lo, hLobr, hLoeq, hLou⟩ := unique_bracketed_root observedUpper_continuous
    observedUpper_strictMono (by norm_num : (720603 / 1000000 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (720604 / 1000000 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num) hs.2.2.2.2.1 hs.2.2.2.2.2
  have hpowMono : StrictMonoOn (fun p : ℝ => p ^ 15) (Set.Icc 0 1) := by
    intro p hp q hq hpq
    exact pow_lt_pow_left₀ hpq hp.1 (by norm_num)
  obtain ⟨U, hUbr, hUeq, hUu⟩ := unique_bracketed_root (by fun_prop :
      Continuous (fun p : ℝ => p ^ 15)) hpowMono
    (by norm_num : (998313 / 1000000 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (998314 / 1000000 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num) hs.2.2.1 hs.2.2.2.1
  have hL01 : L ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hLbr.1], by linarith [hLbr.2]⟩
  have hLo01 : Lo ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hLobr.1], by linarith [hLobr.2]⟩
  have hU01 : U ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hUbr.1], by linarith [hUbr.2]⟩
  have hLcrit (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
      (1 : ℝ) / 40 ≤ observedUpperPolynomial p ↔ L ≤ p := by
    rw [← hLeq]
    exact observedUpper_strictMono.le_iff_le hL01 hp
  have hLocrit (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
      (1 : ℝ) / 20 ≤ observedUpperPolynomial p ↔ Lo ≤ p := by
    rw [← hLoeq]
    exact observedUpper_strictMono.le_iff_le hLo01 hp
  have hUcrit (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
      (1 : ℝ) / 40 ≤ 1 - p ^ 15 ↔ p ≤ U := by
    have hm := hpowMono.le_iff_le hp hU01
    rw [hUeq] at hm
    constructor <;> intro h
    · exact hm.mp (by linarith)
    · have hh := hm.mpr h; linarith
  have hCI : exactDetectionInterval 14 = Set.Icc L U := by
    ext p
    constructor
    · intro hp
      change p ∈ Set.Icc (0 : ℝ) 1 ∧ _ ∧ _ at hp
      rw [(observed_tail_identities p).1, (observed_tail_identities p).2] at hp
      exact ⟨(hLcrit p hp.1).mp hp.2.1, (hUcrit p hp.1).mp hp.2.2⟩
    · intro hp
      have hp01 : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hL01.1.trans hp.1, hp.2.trans hU01.2⟩
      change p ∈ Set.Icc (0 : ℝ) 1 ∧ _ ∧ _
      rw [(observed_tail_identities p).1, (observed_tail_identities p).2]
      exact ⟨hp01, (hLcrit p hp01).mpr hp.1, (hUcrit p hp01).mpr hp.2⟩
  have hCone : exactDetectionLowerSet 14 = Set.Icc Lo 1 := by
    ext p
    constructor
    · intro hp
      change p ∈ Set.Icc (0 : ℝ) 1 ∧ _ at hp
      rw [(observed_tail_identities p).1] at hp
      exact ⟨(hLocrit p hp.1).mp hp.2, hp.1.2⟩
    · intro hp
      have hp01 : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hLo01.1.trans hp.1, hp.2⟩
      change p ∈ Set.Icc (0 : ℝ) 1 ∧ _
      rw [(observed_tail_identities p).1]
      exact ⟨hp01, (hLocrit p hp01).mpr hp.1⟩
  have hUrpow : U = (39 / 40 : ℝ) ^ ((15 : ℝ)⁻¹) := by
    rw [← hUeq]
    exact (Real.pow_rpow_inv_natCast hU01.1 (by norm_num : (15 : ℕ) ≠ 0)).symm
  refine ⟨L, U, Lo, hLbr.1, hLbr.2, hUbr.1, hUbr.2, hLobr.1, hLobr.2,
    hLeq, hLoeq, hUeq, hUrpow, hLuniq, hLou, ?_, hCI, hCone, ?_, ?_, ?_, ?_⟩
  · intro p hp he
    exact hUu p hp (by linarith)
  · linarith [hLbr.2, hLobr.1]
  · linarith [hLobr.2]
  · unfold roundsTwo; constructor <;> linarith [hLbr.1, hLbr.2]
  · unfold roundsTwo; constructor <;> linarith [hUbr.1, hUbr.2]

/-- P040-T2(ii): the observed upper-tail polynomial takes values zero and one
at the boundaries of the admissible probability interval. -/
theorem observed_upper_boundary_values :
    observedUpperPolynomial 0 = 0 ∧ observedUpperPolynomial 1 = 1 := by
  norm_num [observedUpperPolynomial]

/-- P040-T2(iv): the exact endpoints round to .680515 and .998314 at six
decimals. Root equations and membership in [0,1] identify the actual endpoints;
the statement does not substitute rounded numbers for the roots. -/
theorem corrected_six_decimal_rounding {L U : ℝ}
    (hL01 : L ∈ Set.Icc (0 : ℝ) 1) (hU01 : U ∈ Set.Icc (0 : ℝ) 1)
    (hL : observedUpperPolynomial L = (1 : ℝ) / 40)
    (hU : U ^ 15 = (39 : ℝ) / 40) :
    (680515 / 1000000 - 1 / 2000000 : ℝ) ≤ L ∧
    L < (680515 / 1000000 + 1 / 2000000 : ℝ) ∧
    (998314 / 1000000 - 1 / 2000000 : ℝ) ≤ U ∧
    U < (998314 / 1000000 + 1 / 2000000 : ℝ) := by
  have hlow : observedUpperPolynomial (6805145 / 10000000) < (1 : ℝ) / 40 := by
    norm_num [observedUpperPolynomial]
  have hhigh : (1 : ℝ) / 40 < observedUpperPolynomial (6805155 / 10000000) := by
    norm_num [observedUpperPolynomial]
  have hLlo : (6805145 / 10000000 : ℝ) < L :=
    (observedUpper_strictMono.lt_iff_lt (by norm_num) hL01).mp (by rwa [hL])
  have hLhi : L < (6805155 / 10000000 : ℝ) :=
    (observedUpper_strictMono.lt_iff_lt hL01 (by norm_num)).mp (by rwa [hL])
  have hm : StrictMonoOn (fun p : ℝ => p ^ 15) (Set.Icc 0 1) := by
    intro p hp q hq hpq
    exact pow_lt_pow_left₀ hpq hp.1 (by norm_num)
  have hUlo : (9983135 / 10000000 : ℝ) < U :=
    (hm.lt_iff_lt (by norm_num) hU01).mp (by rw [hU]; norm_num)
  have hUhi : U < (9983145 / 10000000 : ℝ) :=
    (hm.lt_iff_lt hU01 (by norm_num)).mp (by rw [hU]; norm_num)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- P040-T1 auxiliary hypothetical exact-coverage proposition: the interval (.81,1.06)
at count 14 is the value of a deterministic rule with at least 95% coverage for
every p∈[0,1] under the added binomial model. This stronger finite-calibration proposition is FALSE, as the
following refutation proves; it is not attributed to the paper's nominal Wald interpretation. Defining it does not constitute proving it. The paper
does not name an interval rule or supply a sampling scheme for the customers. -/
def printedPatronConfidenceClaim : Prop :=
  ∃ I : DetectionCount → Set ℝ,
    I 14 = Set.Ioo (81 / 100 : ℝ) (106 / 100) ∧
    ∀ p ∈ Set.Icc (0 : ℝ) 1, (19 : ℝ) / 20 ≤ intervalCoverage p I

/-- The auxiliary exact-coverage proposition is refuted by the method-free P040-T1 witness;
this does not refute the paper's conventional approximate confidence interpretation. The printed
arithmetic P1/P2 remains correct; no proposition about the true patron rate
being below .80 is concluded. -/
theorem printed_patron_claim_refuted : ¬ printedPatronConfidenceClaim := by
  rintro ⟨I, hI14, hcalibrated⟩
  have hex : (4 / 5 : ℝ) ∉ I 14 := by rw [hI14]; norm_num
  have hbad := (method_free_counterexample I hex).2
  have hgood := hcalibrated (4 / 5) (by norm_num)
  linarith

/-- P040-T1 consequence: when p=.80, the reconstructed Wald lower endpoint
exceeds .80 with exact probability .167125767421952, throughout the multiplier
range [1.9599,1.9601]. Thus the failure probability exceeds both .05 and .025. -/
theorem wald_lower_failure_probability (z : ℝ)
    (hzlo : (19599 / 10000 : ℝ) ≤ z) (hzhi : z ≤ (19601 / 10000 : ℝ)) :
    countProbability (4 / 5) (fun k => (4 / 5 : ℝ) < detectionProportion k - waldRadius z k) =
        (5100273664 : ℝ) / 30517578125 ∧
    (1 : ℝ) / 20 < countProbability (4 / 5)
      (fun k => (4 / 5 : ℝ) < detectionProportion k - waldRadius z k) ∧
    (1 : ℝ) / 40 < countProbability (4 / 5)
      (fun k => (4 / 5 : ℝ) < detectionProportion k - waldRadius z k) := by
  have hc := countProbability_complement (4 / 5)
    (fun k => detectionProportion k - waldRadius z k ≤ (4 / 5 : ℝ))
  have hcov := (wald_coverage_counterexample z hzlo hzhi).2.2.1
  have he : (fun k => ¬detectionProportion k - waldRadius z k ≤ (4 / 5 : ℝ)) =
      (fun k => (4 / 5 : ℝ) < detectionProportion k - waldRadius z k) := by
    funext k; exact propext not_le
  rw [he, hcov] at hc
  have hfail : countProbability (4 / 5)
      (fun k => (4 / 5 : ℝ) < detectionProportion k - waldRadius z k) =
        (5100273664 : ℝ) / 30517578125 := by linarith
  exact ⟨hfail, by rw [hfail]; norm_num, by rw [hfail]; norm_num⟩

end
end AronowAudit.P040

