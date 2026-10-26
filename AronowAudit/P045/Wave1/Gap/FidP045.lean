import AronowAudit.P045.P045_Spillover

namespace AronowAudit.P045.Wave1
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Finset
noncomputable section

abbrev TractAssignment := Fin 6 → Assignment 75

-- Own-psi groups have 50 treated units; other groups have 25.
def tractRegimeCount (H : Finset (Fin 6)) (g : Fin 6) : ℕ :=
  if g ∈ H then 50 else 25

-- Independent complete randomization in every group, conditional on H.
def tractSecondStageMass (H : Finset (Fin 6)) (w : TractAssignment) : ℝ :=
  ∏ g : Fin 6, crMass 75 (tractRegimeCount H g) (w g)

-- Uniform first stage, followed by the H-dependent second stage.
def tractTwoStageMass (ω : Finset (Fin 6) × TractAssignment) : ℝ :=
  if ω.1 ∈ firstStageSets 6 3 then
    (1 / ((firstStageSets 6 3).card : ℝ)) * tractSecondStageMass ω.1 ω.2
  else 0

-- Exactly the difference of the two pooled arm means of p. 310.
-- The theorem below supplies its nonempty-arm and nonempty-group domain.
def tractDirectEstimator (H : Finset (Fin 6)) (w : TractAssignment) : ℝ :=
  (∑ g ∈ H, tractObservedArm w g true) / (H.card : ℝ) -
    (∑ g ∈ H, tractObservedArm w g false) / (H.card : ℝ)

-- An auxiliary intervention law for defining the psi-psi potential outcomes.
-- H=univ here does not assert that all six groups can be selected in the
-- actual three-of-six first stage.
def tractAllPsiMass (w : TractAssignment) : ℝ :=
  tractSecondStageMass Finset.univ w

def tractPsiPsiPotential (g : Fin 6) (i : Fin 75) (b : Bool) : ℝ :=
  condMean tractAllPsiMass (fun w => w g i = b)
    (fun w => tractOutcome w g i)

-- Three tracts, two groups per tract, matching tractPartner exactly.
def tractGroupAt (t : Fin 3) (s : Fin 2) : Fin 6 :=
  (![![0, 1], ![2, 3], ![4, 5]] : Fin 3 → Fin 2 → Fin 6) t s

-- Equal tract weighting, and 150 equally weighted units in each tract,
-- in the order of the printed definition on p. 311.
def tractPsiPsiTarget : ℝ :=
  mean (fun t : Fin 3 =>
    mean (fun u : Fin 2 × Fin 75 =>
      tractPsiPsiPotential (tractGroupAt t u.1) u.2 true) -
    mean (fun u : Fin 2 × Fin 75 =>
      tractPsiPsiPotential (tractGroupAt t u.1) u.2 false))


attribute [local irreducible] fixedAssignments

/-- Both prescribed saturation counts are strictly between zero and 75. -/
lemma tract_mixture_regime_bounds (H : Finset (Fin 6)) (g : Fin 6) :
    0 < tractRegimeCount H g ∧ tractRegimeCount H g < 75 := by
  unfold tractRegimeCount
  split_ifs <;> norm_num

lemma tract_mixture_second_nonneg (H : Finset (Fin 6)) (w : TractAssignment) :
    0 ≤ tractSecondStageMass H w := by
  apply Finset.prod_nonneg
  intro g hg
  exact (cr_mass_probability (le_of_lt (tract_mixture_regime_bounds H g).2)).1 (w g)

lemma tract_mixture_second_total (H : Finset (Fin 6)) :
    (∑ w : TractAssignment, tractSecondStageMass H w) = 1 := by
  unfold tractSecondStageMass
  rw [← Fintype.prod_sum]
  have ht (g : Fin 6) : (∑ z, crMass 75 (tractRegimeCount H g) z) = 1 :=
    (cr_mass_probability (le_of_lt (tract_mixture_regime_bounds H g).2)).2
  simp only [ht, Finset.prod_const_one]

lemma tract_mixture_second_support (H : Finset (Fin 6)) (w : TractAssignment) :
    0 < tractSecondStageMass H w ↔
      ∀ g : Fin 6, treatedCount (w g) = tractRegimeCount H g := by
  constructor
  · intro hp g
    have hne := Finset.prod_ne_zero_iff.mp (ne_of_gt hp) g (mem_univ g)
    by_contra hc
    have hm : w g ∉ fixedAssignments 75 (tractRegimeCount H g) :=
      fun h => hc ((mem_fixed_assignments_iff (w g)).mp h)
    exact hne (by simp only [crMass, ite_eq_right hm])
  · intro hw
    apply Finset.prod_pos
    intro g hg
    exact cr_mass_positive (w g) ((mem_fixed_assignments_iff (w g)).mpr (hw g))

/-- Expand the actual joint law, allowing the local laws to depend on H. -/
lemma tract_mixture_joint_expect
    (X : Finset (Fin 6) × TractAssignment → ℝ) :
    expect tractTwoStageMass X = average (firstStageSets 6 3)
      (fun H => expect (tractSecondStageMass H) (fun w => X (H, w))) := by
  unfold expect tractTwoStageMass average
  simp only [Fintype.sum_prod_type]
  simp [ite_mul, Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_comm]

lemma tract_mixture_first_card : (firstStageSets 6 3).card = 20 :=
  pooling_empty_subclass.1

lemma tract_mixture_joint_nonneg (ω : Finset (Fin 6) × TractAssignment) :
    0 ≤ tractTwoStageMass ω := by
  unfold tractTwoStageMass
  split_ifs
  · exact mul_nonneg (by positivity) (tract_mixture_second_nonneg _ _)
  · exact le_rfl

lemma tract_mixture_joint_total :
    (∑ ω : Finset (Fin 6) × TractAssignment, tractTwoStageMass ω) = 1 := by
  have h := tract_mixture_joint_expect (fun _ => 1)
  simp only [expect, mul_one, tract_mixture_second_total] at h
  rw [h]
  norm_num [average, tract_mixture_first_card]

lemma tract_mixture_joint_support (ω : Finset (Fin 6) × TractAssignment) :
    0 < tractTwoStageMass ω ↔
      ω.1 ∈ firstStageSets 6 3 ∧
      ∀ g : Fin 6, treatedCount (ω.2 g) = tractRegimeCount ω.1 g := by
  unfold tractTwoStageMass
  by_cases hH : ω.1 ∈ firstStageSets 6 3
  · simp only [hH, ite_true, true_and]
    have hc : 0 < 1 / ((firstStageSets 6 3).card : ℝ) := by
      rw [tract_mixture_first_card]
      norm_num
    rw [mul_pos_iff_of_pos_left hc, tract_mixture_second_support]
  · simp only [hH, ite_false, false_and, lt_self_iff_false]

/-- Positive treated and control counts certify both observed arms. -/
lemma tract_mixture_arms_exist {n : ℕ} (z : Assignment n)
    (hpos : 0 < treatedCount z) (hlt : treatedCount z < n) (b : Bool) :
    armExists b z := by
  classical
  cases b
  · by_contra h
    have hall : ∀ i, z i = true := by
      intro i
      have hi : z i ≠ false := fun hi => h ⟨i, hi⟩
      cases hz : z i <;> simp_all
    have hc : treatedCount z = n := by simp [treatedCount, hall]
    omega
  · obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩

lemma tract_mixture_observed (H : Finset (Fin 6)) (w : TractAssignment)
    (hw : ∀ g : Fin 6, treatedCount (w g) = tractRegimeCount H g)
    (g : Fin 6) (hg : g ∈ H) (b : Bool) :
    armExists b (w g) ∧
    tractObservedArm w g b =
      (if tractPartner g ∈ H then (if b then 9 / 4 else 11 / 8)
      else (if b then 2 else 5 / 4)) := by
  have hb := tract_mixture_regime_bounds H g
  rw [← hw g] at hb
  have hex := tract_mixture_arms_exist (w g) hb.1 hb.2 b
  refine ⟨hex, ?_⟩
  apply observed_arm_constant _ _ _ _ _ hex
  intro i hi
  by_cases hp : tractPartner g ∈ H <;> cases b <;>
    simp [tractOutcome, hw, tractRegimeCount, hg, hp, hi]

lemma tract_mixture_estimator (H : Finset (Fin 6)) (hH : H ∈ firstStageSets 6 3)
    (w : TractAssignment)
    (hw : ∀ g : Fin 6, treatedCount (w g) = tractRegimeCount H g) :
    (∀ g ∈ H, ∀ b : Bool,
      armExists b (w g) ∧
      tractObservedArm w g b =
        (if tractPartner g ∈ H then (if b then 9 / 4 else 11 / 8)
        else (if b then 2 else 5 / 4))) ∧
    tractDirectEstimator H w =
      (∑ g ∈ H, (tractObservedArm w g true - tractObservedArm w g false)) / 3 ∧
    tractDirectEstimator H w =
      ((sameRegimeCount H : ℝ) / 3) * (7 / 8) +
        ((3 - (sameRegimeCount H : ℝ)) / 3) * (3 / 4) := by
  classical
  have hc : H.card = 3 := (Finset.mem_powersetCard.mp hH).2
  have he : tractDirectEstimator H w =
      (∑ g ∈ H, (tractObservedArm w g true - tractObservedArm w g false)) / 3 := by
    simp only [tractDirectEstimator, hc, Nat.cast_ofNat, Finset.sum_sub_distrib, sub_div]
  refine ⟨fun g hg b => tract_mixture_observed H w hw g hg b, he, ?_⟩
  have hcontrast (g : Fin 6) (hg : g ∈ H) :
      tractObservedArm w g true - tractObservedArm w g false =
        if tractPartner g ∈ H then (7 / 8 : ℝ) else 3 / 4 := by
    rw [(tract_mixture_observed H w hw g hg true).2,
      (tract_mixture_observed H w hw g hg false).2]
    by_cases hp : tractPartner g ∈ H <;> norm_num [hp]
  have hsum : (∑ g ∈ H, (tractObservedArm w g true - tractObservedArm w g false)) =
      (sameRegimeCount H : ℝ) * (7 / 8) +
        ((H.filter (fun g => tractPartner g ∉ H)).card : ℝ) * (3 / 4) := by
    calc
      _ = ∑ g ∈ H, if tractPartner g ∈ H then (7 / 8 : ℝ) else 3 / 4 :=
        Finset.sum_congr rfl hcontrast
      _ = _ := by simp [Finset.sum_ite, sameRegimeCount]
  have hpartition := (tract_partition H (fun _ => (0 : ℝ))).1
  have hcast : (sameRegimeCount H : ℝ) +
      ((H.filter (fun g => tractPartner g ∉ H)).card : ℝ) = 3 := by
    exact_mod_cast (show sameRegimeCount H +
      (H.filter (fun g => tractPartner g ∉ H)).card = 3 by
      simpa only [sameRegimeCount, hc] using hpartition.symm)
  rw [he, hsum]
  linarith

/-- Marginalization of one coordinate of a normalized finite product law. -/
lemma tract_mixture_coordinate_expect {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] (q : Ω → ℝ) (hq : ∑ z, q z = 1) (g : I) (f : Ω → ℝ) :
    expect (fun w : I → Ω => ∏ h, q (w h)) (fun w => f (w g)) = expect q f := by
  classical
  let X : I → Ω → ℝ := fun h z => if h = g then f z else 1
  have hX (w : I → Ω) : (∏ h, X h (w h)) = f (w g) := by
    simp only [X, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  have he (h : I) : expect q (X h) = if h = g then expect q f else 1 := by
    by_cases hh : h = g
    · simp only [X, hh, ite_true]
    · simp only [X, ite_eq_right hh, expect, mul_one, hq]
  have h := independent_expect_product q X
  simp_rw [hX, he] at h
  simpa only [Finset.prod_ite_eq', Finset.mem_univ, ite_true] using h

lemma tract_mixture_coordinate_prob {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] (q : Ω → ℝ) (hq : ∑ z, q z = 1) (g : I) (E : Ω → Prop) :
    prob (fun w : I → Ω => ∏ h, q (w h)) (fun w => E (w g)) = prob q E := by
  classical
  unfold prob
  exact tract_mixture_coordinate_expect q hq g (fun z => if E z then 1 else 0)

lemma tract_mixture_psi_probability (g : Fin 6) (i : Fin 75) (b : Bool) :
    prob tractAllPsiMass (fun w => w g i = b) =
      (if b then (2 / 3 : ℝ) else 1 / 3) := by
  classical
  have hm : tractAllPsiMass = fun w : TractAssignment => ∏ h, crMass 75 50 (w h) := by
    funext w
    simp only [tractAllPsiMass, tractSecondStageMass, tractRegimeCount,
      Finset.mem_univ, ite_true]
  rw [hm]
  calc
    _ = prob (crMass 75 50) (fun z => z i = b) :=
      tract_mixture_coordinate_prob (crMass 75 50)
        (cr_mass_probability (by norm_num : 50 ≤ 75)).2 g (fun z => z i = b)
    _ = _ := by
      rw [cr_arm_probability (by norm_num : 0 < 50) (by norm_num : 50 < 75)]
      cases b <;> norm_num

/-- A conditional mean is its support-constant value on a positive event. -/
lemma tract_mixture_cond_constant {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (E : Ω → Prop) (X : Ω → ℝ) (c : ℝ)
    (hnonneg : ∀ w, 0 ≤ p w) (hprob : 0 < prob p E)
    (hX : ∀ w, 0 < p w → E w → X w = c) : condMean p E X = c := by
  classical
  have hnum : expect p (fun w => if E w then X w else 0) = prob p E * c := by
    simp only [prob, expect]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hp : p w = 0
    · simp only [hp, zero_mul]
    · have hp' : 0 < p w := lt_of_le_of_ne (hnonneg w) (Ne.symm hp)
      by_cases he : E w
      · simp only [ite_eq_left he, hX w hp' he, mul_one]
      · simp only [ite_eq_right he, mul_zero, zero_mul]
  rw [condMean, hnum]
  exact mul_div_cancel_left₀ c (ne_of_gt hprob)

lemma tract_mixture_psi_potential (g : Fin 6) (i : Fin 75) (b : Bool) :
    tractPsiPsiPotential g i b = (if b then 9 / 4 else 11 / 8) := by
  have hp : 0 < prob tractAllPsiMass (fun w => w g i = b) := by
    rw [tract_mixture_psi_probability]
    cases b <;> norm_num
  apply tract_mixture_cond_constant tractAllPsiMass _ _ _
    (tract_mixture_second_nonneg Finset.univ) hp
  intro w hw hi
  have hc := (tract_mixture_second_support Finset.univ w).mp hw
  have hg : treatedCount (w g) = 50 := by
    simpa only [tractRegimeCount, Finset.mem_univ, ite_true] using hc g
  have hpartner : treatedCount (w (tractPartner g)) = 50 := by
    simpa only [tractRegimeCount, Finset.mem_univ, ite_true] using hc (tractPartner g)
  cases b <;> simp [tractOutcome, hg, hpartner, hi]

lemma tract_mixture_psi_target : tractPsiPsiTarget = 7 / 8 := by
  simp only [tractPsiPsiTarget, tract_mixture_psi_potential]
  norm_num [mean, Fintype.card_prod]

lemma tract_mixture_expectation :
    expect tractTwoStageMass (fun ω => tractDirectEstimator ω.1 ω.2) = 4 / 5 := by
  rw [tract_mixture_joint_expect]
  calc
    _ = average (firstStageSets 6 3) (fun H =>
        ((sameRegimeCount H : ℝ) / 3) * (7 / 8) +
        ((3 - (sameRegimeCount H : ℝ)) / 3) * (3 / 4)) := by
      unfold average
      apply congrArg (fun x : ℝ => x / ((firstStageSets 6 3).card : ℝ))
      apply Finset.sum_congr rfl
      intro H hH
      let c : ℝ := ((sameRegimeCount H : ℝ) / 3) * (7 / 8) +
        ((3 - (sameRegimeCount H : ℝ)) / 3) * (3 / 4)
      calc
        _ = (∑ w : TractAssignment, tractSecondStageMass H w) * c := by
          unfold expect
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro w _
          change tractSecondStageMass H w * tractDirectEstimator H w =
            tractSecondStageMass H w * c
          by_cases hp : tractSecondStageMass H w = 0
          · simp only [hp, zero_mul]
          · have hpos : 0 < tractSecondStageMass H w :=
              lt_of_le_of_ne (tract_mixture_second_nonneg H w) (Ne.symm hp)
            rw [(tract_mixture_estimator H hH w
              ((tract_mixture_second_support H w).mp hpos)).2.2]
        _ = c := by rw [tract_mixture_second_total, one_mul]
    _ = 4 / 5 := tract_mixture_bias.2.2.1

/-- P045-T15(c): identify the observed estimator and the conditional psi-psi
target from the tract outcome schedule, then compute their design-based bias. -/
theorem tract_mixture_bias_identified :
    (∀ ω : Finset (Fin 6) × TractAssignment, 0 ≤ tractTwoStageMass ω) ∧
    (∑ ω : Finset (Fin 6) × TractAssignment, tractTwoStageMass ω) = 1 ∧
    (∀ ω : Finset (Fin 6) × TractAssignment,
      0 < tractTwoStageMass ω ↔
        ω.1 ∈ firstStageSets 6 3 ∧
        ∀ g : Fin 6, treatedCount (ω.2 g) = tractRegimeCount ω.1 g) ∧
    (∀ H ∈ firstStageSets 6 3, ∀ w : TractAssignment,
      (∀ g : Fin 6, treatedCount (w g) = tractRegimeCount H g) →
      (∀ g ∈ H, ∀ b : Bool,
        armExists b (w g) ∧
        tractObservedArm w g b =
          (if tractPartner g ∈ H then
            (if b then 9 / 4 else 11 / 8)
          else (if b then 2 else 5 / 4))) ∧
      tractDirectEstimator H w =
        (∑ g ∈ H, (tractObservedArm w g true - tractObservedArm w g false)) / 3 ∧
      tractDirectEstimator H w =
        ((sameRegimeCount H : ℝ) / 3) * (7 / 8) +
          ((3 - (sameRegimeCount H : ℝ)) / 3) * (3 / 4)) ∧
    (∀ g : Fin 6, ∀ i : Fin 75, ∀ b : Bool,
      prob tractAllPsiMass (fun w => w g i = b) =
        (if b then (2 / 3 : ℝ) else 1 / 3) ∧
      tractPsiPsiPotential g i b = (if b then 9 / 4 else 11 / 8)) ∧
    tractPsiPsiTarget = 7 / 8 ∧
    average (firstStageSets 6 3)
      (fun H => (sameRegimeCount H : ℝ) / 3) = 2 / 5 ∧
    average (firstStageSets 6 3)
      (fun H => (3 - (sameRegimeCount H : ℝ)) / 3) = 3 / 5 ∧
    expect tractTwoStageMass
      (fun ω => tractDirectEstimator ω.1 ω.2) = 4 / 5 ∧
    expect tractTwoStageMass
      (fun ω => tractDirectEstimator ω.1 ω.2) - tractPsiPsiTarget = -3 / 40 := by
  refine ⟨tract_mixture_joint_nonneg, tract_mixture_joint_total,
    tract_mixture_joint_support, tract_mixture_estimator,
    ?_, tract_mixture_psi_target, tract_mixture_bias.1,
    tract_mixture_bias.2.1, tract_mixture_expectation, ?_⟩
  · intro g i b
    exact ⟨tract_mixture_psi_probability g i b, tract_mixture_psi_potential g i b⟩
  · rw [tract_mixture_expectation, tract_mixture_psi_target]
    norm_num

end
end AronowAudit.P045.Wave1
