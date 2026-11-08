import SAP.P004a.WH.W1.Leaves
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T5_L3

open MeasureTheory Set
open scoped BigOperators Classical ENNReal

theorem zero_distance_iff (r : ℝ) : max (r - 1) 0 = 0 ↔ r ≤ 1 := by
  constructor
  · intro h
    have h' := le_max_left (r - 1) 0
    rw [h] at h'
    linarith
  · intro h
    exact max_eq_right (by linarith)

theorem shell_distance_iff (r t : ℝ) (ht : 1 ≤ t) :
    ( (t - 1) / 2 < max (r - 1) 0 ∧ max (r - 1) 0 ≤ t / 2) ↔
      ((t + 1) / 2 < r ∧ r ≤ (t + 2) / 2) := by
  by_cases hr : r ≤ 1
  · rw [max_eq_right (by linarith : r - 1 ≤ 0)]
    constructor
    · rintro ⟨h, _⟩
      have : 0 ≤ (t - 1) / 2 := by positivity
      linarith
    · rintro ⟨h, _⟩
      have : 1 ≤ (t + 1) / 2 := by nlinarith
      linarith
  · have hr' : 1 < r := lt_of_not_ge hr
    rw [max_eq_left (by linarith : 0 ≤ r - 1)]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith

theorem annulus_eq_sdiff (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    {x : EuclideanSpace ℝ (Fin 2) | a < dist x c ∧ dist x c ≤ b} =
      Metric.closedBall c b \ Metric.closedBall c a := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_sdiff, Metric.mem_closedBall, not_le]
  exact and_comm

theorem disk_volume (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.closedBall c r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [EuclideanSpace.volume_closedBall_fin_two,
    ENNReal.ofReal_mul Real.pi_nonneg, ENNReal.ofReal_pow hr]
  exact mul_comm _ _

theorem annulus_volume (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    volume {x : EuclideanSpace ℝ (Fin 2) | a < dist x c ∧ dist x c ≤ b} =
      ENNReal.ofReal (Real.pi * (b ^ 2 - a ^ 2)) := by
  rw [annulus_eq_sdiff]
  have hsubset : Metric.closedBall c a ⊆ Metric.closedBall c b :=
    Metric.closedBall_subset_closedBall hab
  have hfinite : volume (Metric.closedBall c a) ≠ ⊤ := by
    rw [disk_volume c a ha]
    exact ENNReal.ofReal_ne_top
  rw [measure_sdiff hsubset Metric.isClosed_closedBall.measurableSet.nullMeasurableSet hfinite,
    disk_volume c b (ha.trans hab), disk_volume c a ha,
    ← ENNReal.ofReal_sub (Real.pi * b ^ 2) (by positivity)]
  congr 1
  ring

theorem refined_region (i : Fin 2) (j : Fin 11) :
    region (w1RefinedArea j) i 0 =
      if j = 0 then Metric.closedBall (areaBinaryCenter i) 1 else
        {x : EuclideanSpace ℝ (Fin 2) |
          ((j : ℝ) + 1) / 2 < dist x (areaBinaryCenter i) ∧
          dist x (areaBinaryCenter i) ≤ ((j : ℝ) + 2) / 2} := by
  classical
  by_cases hj : j.val = 0
  · have hj0 : j = 0 := Fin.ext hj
    subst j
    simp only [if_pos rfl]
    ext x
    change Metric.infDist x (Metric.closedBall (areaBinaryCenter i) 1) ∈
        w1RefinedBand (0 : Fin 11) ↔ x ∈ Metric.closedBall (areaBinaryCenter i) 1
    rw [AronowAudit.P004.Wave1.AreaSum.a1_proof]
    simp only [w1RefinedBand, Fin.val_zero, Nat.cast_zero, ↓reduceIte,
      Set.mem_singleton_iff, Metric.mem_closedBall]
    exact zero_distance_iff _
  · have hjpos : 1 ≤ j.val := by omega
    have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjpos
    have hjneq : j ≠ 0 := by
      intro he
      apply hj
      have hv : j.val = 0 := by simpa using congrArg Fin.val he
      exact hv
    simp only [if_neg hjneq]
    ext x
    change Metric.infDist x (Metric.closedBall (areaBinaryCenter i) 1) ∈
        w1RefinedBand j ↔ x ∈ {x : EuclideanSpace ℝ (Fin 2) |
          ((j : ℝ) + 1) / 2 < dist x (areaBinaryCenter i) ∧
          dist x (areaBinaryCenter i) ≤ ((j : ℝ) + 2) / 2}
    rw [AronowAudit.P004.Wave1.AreaSum.a1_proof]
    simp only [w1RefinedBand, if_neg hjneq, Set.mem_Ioc, Set.mem_setOf_eq]
    exact (shell_distance_iff _ _ hjr)

theorem refined_shell_iff (i : Fin 2) (j : Fin 11) (hj : j ≠ 0)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ region (w1RefinedArea j) i 0 ↔
      ((j : ℝ) + 1) / 2 < dist x (areaBinaryCenter i) ∧
      dist x (areaBinaryCenter i) ≤ ((j : ℝ) + 2) / 2 := by
  rw [refined_region]
  simp [hj]

theorem refined_disk_iff (i : Fin 2) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ region (w1RefinedArea 0) i 0 ↔ dist x (areaBinaryCenter i) ≤ 1 := by
  rw [refined_region]
  simp [Metric.mem_closedBall]

theorem refined_measurable (i : Fin 2) (j : Fin 11) :
    MeasurableSet (region (w1RefinedArea j) i 0) := by
  rw [refined_region]
  by_cases hj : j = 0
  · simp [hj, Metric.isClosed_closedBall.measurableSet]
  · simp only [hj, if_false]
    apply (measurableSet_lt measurable_const
      (continuous_id.dist continuous_const).measurable).inter
    exact measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const

theorem refined_volume (i : Fin 2) (j : Fin 11) :
    volume (region (w1RefinedArea j) i 0) =
      if j = 0 then ENNReal.ofReal Real.pi else
        ENNReal.ofReal (Real.pi * (((((j : ℝ) + 2) / 2) ^ 2) - ((((j : ℝ) + 1) / 2) ^ 2))) := by
  by_cases hj : j = 0
  · subst j
    have hset : region (w1RefinedArea 0) i 0 = Metric.closedBall (areaBinaryCenter i) 1 := by
      simpa using refined_region i (0 : Fin 11)
    rw [hset, disk_volume _ _ (by norm_num)]
    simp
  · rw [if_neg hj]
    have hs : region (w1RefinedArea j) i 0 =
        {x : EuclideanSpace ℝ (Fin 2) |
          ((j : ℝ) + 1) / 2 < dist x (areaBinaryCenter i) ∧
          dist x (areaBinaryCenter i) ≤ ((j : ℝ) + 2) / 2} := by
      simpa [hj] using refined_region i j
    have ha : 0 ≤ ((j : ℝ) + 1) / 2 := by
      exact div_nonneg (add_nonneg (Nat.cast_nonneg _) (by norm_num)) (by norm_num)
    have hab : ((j : ℝ) + 1) / 2 ≤ ((j : ℝ) + 2) / 2 := by linarith
    rw [hs, annulus_volume _ _ _ ha hab]

theorem refined_subset_six (i : Fin 2) (j : Fin 11) :
    region (w1RefinedArea j) i 0 ⊆ Metric.closedBall (areaBinaryCenter i) 6 := by
  intro x hx
  by_cases hj : j = 0
  · subst j
    rw [refined_disk_iff] at hx
    exact Metric.mem_closedBall.mpr (by linarith)
  · have hs := (refined_shell_iff i j hj x).mp hx
    have hjvalNat : j.val ≤ 10 := by omega
    have hjval : (j : ℝ) ≤ 10 := by exact_mod_cast hjvalNat
    apply Metric.mem_closedBall.mpr
    linarith

theorem refined_pairwise (i : Fin 2) :
    Pairwise (fun j k : Fin 11 =>
      Disjoint (region (w1RefinedArea j) i 0) (region (w1RefinedArea k) i 0)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro x hxj hxk
  by_cases hj : j = 0
  · subst j
    rw [refined_disk_iff] at hxj
    have hk : k ≠ 0 := by
      intro h
      subst k
      exact hjk rfl
    have hs := (refined_shell_iff i k hk x).mp hxk
    have hkpos : 1 ≤ k.val := by
      have hkval : k.val ≠ 0 := fun h => hk (Fin.ext h)
      omega
    have hkposR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
    have hlow : 1 ≤ ((k : ℝ) + 1) / 2 := by nlinarith
    linarith
  · by_cases hk : k = 0
    · subst k
      rw [refined_disk_iff] at hxk
      have hs := (refined_shell_iff i j hj x).mp hxj
      have hjpos : 1 ≤ j.val := by
        have hjval : j.val ≠ 0 := fun h => hj (Fin.ext h)
        omega
      have hjposR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjpos
      have hlow : 1 ≤ ((j : ℝ) + 1) / 2 := by nlinarith
      linarith
    · have hs₁ := (refined_shell_iff i j hj x).mp hxj
      have hs₂ := (refined_shell_iff i k hk x).mp hxk
      rcases lt_or_gt_of_ne hjk with hlt | hgt
      · have horder : (j : ℝ) + 1 ≤ (k : ℝ) := by
          have hn : j.val + 1 ≤ k.val := by omega
          exact_mod_cast hn
        have : ((k : ℝ) + 1) / 2 ≤ ((j : ℝ) + 2) / 2 := by nlinarith
        linarith
      · have horder : (k : ℝ) + 1 ≤ (j : ℝ) := by
          have hn : k.val + 1 ≤ j.val := by omega
          exact_mod_cast hn
        have : ((j : ℝ) + 1) / 2 ≤ ((k : ℝ) + 2) / 2 := by nlinarith
        linarith

end SAP.P004a.WH.W1.P.T5_L3

open SAP.P004a.WH.W1.P.T5_L3
open MeasureTheory Set

theorem SAP.P004a.WH.W1.T5_L3_proof : SAP.P004a.WH.W1.T5_L3 := by
  intro hgeo
  rcases hgeo with ⟨hbinary, hmeas, _, _, _, _, _, _, _, _, _⟩
  have hbinary' : ∀ x z, (w1AreaCase 0).outcome x z = 0 ∨ (w1AreaCase 0).outcome x z = 1 := hbinary
  have hmeas' : ∀ z, Measurable (fun x => (w1AreaCase 0).outcome x z) := hmeas
  refine ⟨?_, ?_, ?_⟩
  · intro j i
    have hvol := refined_volume i j
    have hmeasSet := refined_measurable i j
    have hpos : 0 < volume (region (w1RefinedArea j) i 0) := by
      rw [hvol]
      by_cases hj : j = 0
      · simp only [if_pos hj]
        exact ENNReal.ofReal_pos.mpr Real.pi_pos
      · simp only [if_neg hj]
        have hjval : 0 < j.val := by
          have hne : j.val ≠ 0 := by intro h; apply hj; exact Fin.ext h
          omega
        have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjval
        have hgap : 0 < (((j : ℝ) + 2) / 2) - (((j : ℝ) + 1) / 2) := by linarith
        have hsum : 0 < (((j : ℝ) + 2) / 2) + (((j : ℝ) + 1) / 2) := by positivity
        have hdiff : 0 < (((j : ℝ) + 2) / 2) ^ 2 - (((j : ℝ) + 1) / 2) ^ 2 := by
          rw [show (((j : ℝ) + 2) / 2) ^ 2 - (((j : ℝ) + 1) / 2) ^ 2 =
            ((((j : ℝ) + 2) / 2) - (((j : ℝ) + 1) / 2)) * ((((j : ℝ) + 2) / 2) + (((j : ℝ) + 1) / 2)) by ring]
          exact mul_pos hgap hsum
        exact ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos hdiff)
    have hfinite : volume (region (w1RefinedArea j) i 0) < ⊤ := by
      rw [hvol]
      by_cases hj : j = 0
      · simp only [if_pos hj]
        exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
      · simp only [if_neg hj]
        exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
    refine ⟨hmeasSet, hpos, hfinite, ?_⟩
    intro z
    apply Measure.integrableOn_of_bounded (M := 1)
      (show volume (region (w1RefinedArea j) i 0) ≠ ⊤ from ne_of_lt hfinite)
      (hmeas' z).aestronglyMeasurable
    refine Filter.Eventually.of_forall ?_
    intro x
    rcases hbinary' x z with hx | hx <;> rw [hx] <;> norm_num
  · intro i
    have hwhole : region (w1AreaCase 0) i 6 = Metric.closedBall (areaBinaryCenter i) 6 := by
      change region areaBinaryPopulation i 6 = Metric.closedBall (areaBinaryCenter i) 6
      exact AronowAudit.P004.Wave1.AreaSum.a2_proof.2 i
    rw [hwhole]
    ext x
    constructor
    · intro hx
      have hr := Metric.mem_closedBall.mp hx
      let r := dist x (areaBinaryCenter i)
      have hr' : r ≤ 6 := by simpa [r] using hr
      by_cases h1 : r ≤ 1
      · refine Set.mem_iUnion.mpr ⟨0, (refined_disk_iff i x).2 ?_⟩
        simpa [r] using h1
      · by_cases h2 : r ≤ 3 / 2
        · refine Set.mem_iUnion.mpr ⟨1, (refined_shell_iff i 1 (by decide) x).2 ?_⟩
          constructor
          · norm_num
            exact lt_of_not_ge h1
          · norm_num
            exact h2
        · by_cases h3 : r ≤ 2
          · refine Set.mem_iUnion.mpr ⟨2, (refined_shell_iff i 2 (by decide) x).2 ?_⟩
            constructor
            · norm_num
              exact lt_of_not_ge h2
            · norm_num
              exact h3
          · by_cases h4 : r ≤ 5 / 2
            · refine Set.mem_iUnion.mpr ⟨3, (refined_shell_iff i 3 (by decide) x).2 ?_⟩
              constructor
              · norm_num
                exact lt_of_not_ge h3
              · norm_num
                exact h4
            · by_cases h5 : r ≤ 3
              · refine Set.mem_iUnion.mpr ⟨4, (refined_shell_iff i 4 (by decide) x).2 ?_⟩
                constructor
                · norm_num
                  exact lt_of_not_ge h4
                · norm_num
                  exact h5
              · by_cases h6 : r ≤ 7 / 2
                · refine Set.mem_iUnion.mpr ⟨5, (refined_shell_iff i 5 (by decide) x).2 ?_⟩
                  constructor
                  · norm_num
                    exact lt_of_not_ge h5
                  · norm_num
                    exact h6
                · by_cases h7 : r ≤ 4
                  · refine Set.mem_iUnion.mpr ⟨6, (refined_shell_iff i 6 (by decide) x).2 ?_⟩
                    constructor
                    · norm_num
                      exact lt_of_not_ge h6
                    · norm_num
                      exact h7
                  · by_cases h8 : r ≤ 9 / 2
                    · refine Set.mem_iUnion.mpr ⟨7, (refined_shell_iff i 7 (by decide) x).2 ?_⟩
                      constructor
                      · norm_num
                        exact lt_of_not_ge h7
                      · norm_num
                        exact h8
                    · by_cases h9 : r ≤ 5
                      · refine Set.mem_iUnion.mpr ⟨8, (refined_shell_iff i 8 (by decide) x).2 ?_⟩
                        constructor
                        · norm_num
                          exact lt_of_not_ge h8
                        · norm_num
                          exact h9
                      · by_cases h10 : r ≤ 11 / 2
                        · refine Set.mem_iUnion.mpr ⟨9, (refined_shell_iff i 9 (by decide) x).2 ?_⟩
                          constructor
                          · norm_num
                            exact lt_of_not_ge h9
                          · norm_num
                            exact h10
                        · refine Set.mem_iUnion.mpr ⟨10, (refined_shell_iff i 10 (by decide) x).2 ?_⟩
                          constructor
                          · norm_num
                            exact lt_of_not_ge h10
                          · norm_num
                            exact hr'
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
      have hsub := refined_subset_six i j hj
      exact hsub
  · exact fun i => refined_pairwise i

