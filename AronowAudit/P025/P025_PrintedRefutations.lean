import AronowAudit.P025.P025_Interval

noncomputable section
namespace AronowAudit.P025

/-- Refutation of printed Proposition 1: its lower stopping rule does not give the minimum. -/
theorem printed_proposition_one_refuted :
    ¬ (∀ {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : Monotone y) (α β : ℝ) (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1),
    ∃ kL kH : Fin n, printedLowerCut y (fun _ => 1) (β/α) kL ∧
      upperCut y (fun _ => 1) (β/α) kH ∧
      IsLeast (attainable y (fun _ => 1) α β) (lowerValue y (fun _ => 1) (β/α) kL.val) ∧
      IsGreatest (attainable y (fun _ => 1) α β) (upperValue y (fun _ => 1) (β/α) kH.val) ∧
      attainable y (fun _ => 1) α β = Set.Icc
        (lowerValue y (fun _ => 1) (β/α) kL.val) (upperValue y (fun _ => 1) (β/α) kH.val)) := by
  intro h
  obtain ⟨kL,kH,hcut,hu,hl,hh,he⟩ := h (by norm_num : 0 < 2) binaryTwo
    sample_sign_counterexample.2.2.1 (1/2) 1 (by norm_num) (by norm_num) (by norm_num)
  have hz : kL = 0 := le_antisymm (hcut.2 (by
    norm_num [binaryTwo, lowerValue, ratio, lowerWeights, Fin.sum_univ_two])) (Fin.zero_le _)
  subst kL
  have hm : (1/3 : ℝ) ∈ attainable binaryTwo (fun _ => 1) (1/2) 1 := by
    rw [sample_counterexample_range.1]
    norm_num
  have hb := hl.2 hm
  norm_num [lowerValue, ratio, lowerWeights, binaryTwo, Fin.sum_univ_two] at hb

/-- Refutation of the printed Proposition 2 formula, including its lower stopping rule. -/
theorem printed_proposition_two_formula_refuted :
    ¬ (∀ {J : ℕ} (hJ : 0 < J) (y mass : Fin J → ℝ)
    (hy : StrictMono y) (hmass : ∀ j, 0 < mass j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1),
    ∃ kL kH : Fin J, printedLowerCut y mass (β/α) kL ∧ upperCut y mass (β/α) kH ∧
      IsLeast (attainable y mass α β) (lowerValue y mass (β/α) kL.val) ∧
      IsGreatest (attainable y mass α β) (upperValue y mass (β/α) kH.val) ∧
      printedLowerExpression y mass (β/α) kL.val = some (lowerEndpoint y mass α β) ∧
      upperEndpoint y mass α β = upperValue y mass (β/α) kH.val) := by
  intro h
  have hp : ∀ i : Fin 2, 0 < twoPi i := by intro i; fin_cases i <;> norm_num [twoPi]
  obtain ⟨kL,kH,hcut,hu,hl,hh,he,heh⟩ := h (by norm_num : 0 < 2) binaryTwo twoPi
    class_sign_counterexample.2.1 hp (1/2) 1 (by norm_num) (by norm_num) (by norm_num)
  have hz : kL = 0 := le_antisymm (hcut.2 (by
    norm_num [binaryTwo, twoPi, lowerValue, ratio, lowerWeights, Fin.sum_univ_two])) (Fin.zero_le _)
  subst kL
  have hm : (1/2 : ℝ) ∈ attainable binaryTwo twoPi (1/2) 1 := by
    refine ⟨![2,1], ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num [weightBox]
    · norm_num [ratio, binaryTwo, twoPi, Fin.sum_univ_two]
  have hb := hl.2 hm
  norm_num [lowerValue, ratio, lowerWeights, binaryTwo, twoPi, Fin.sum_univ_two] at hb

/-- Refutation of sharpness when the absolute class totals are retained. -/
theorem printed_sharpness_absolute_information_refuted :
    ¬ (∀ {J : ℕ} (hJ : 0 < J) (y mass : Fin J → ℝ)
    (hy : StrictMono y) (hmass : ∀ j, 0 < mass j) (α β : ℝ)
    (hα : 0 < α) (hab : α ≤ β) (hb1 : β ≤ 1)
    (hcomp : ∃ m : Fin J → ℕ, absoluteCompatible α β mass m),
    IsGLB (absoluteCompatibleMeans y mass α β) (lowerEndpoint y mass α β) ∧
    IsLUB (absoluteCompatibleMeans y mass α β) (upperEndpoint y mass α β)) := by
  intro h
  have hp : ∀ i : Fin 2, 0 < (![2/3,4/3] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  have hc : ∃ m : Fin 2 → ℕ, absoluteCompatible (1/2) (3/4) ![2/3,4/3] m :=
    ⟨![1,2], (integrality_sharpness_counterexample.1 _).mpr rfl⟩
  have hb := (h (by norm_num : 0 < 2) binaryTwo ![2/3,4/3]
    class_sign_counterexample.2.1 hp (1/2) (3/4) (by norm_num) (by norm_num) (by norm_num) hc).1
  have he : lowerEndpoint binaryTwo ![2/3,4/3] (1/2) (3/4) = 4/7 :=
    sharpness_counterexample_box_extrema.1.csInf_eq
  rw [he] at hb
  exact integrality_mean_set_and_gaps.2.1 hb

end AronowAudit.P025

