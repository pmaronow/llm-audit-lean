import SAP.P026a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace SAP.P026a.WH.W2.P.T7_L8

open SAP.P026a
open Finset
open scoped BigOperators
noncomputable section

def Q0 (w : W2Allocation) : ℚ := w2IPWArmWeight w false
def Q1 (w : W2Allocation) : ℚ := w2IPWArmWeight w true

lemma weight_pos (w : W2Allocation) (i : Fin 16) : 0 < w2IPWWeight w i := by
  unfold w2IPWWeight
  split_ifs <;> norm_num

lemma treated_exists (w : W2Allocation) :
    ∃ i : Fin 16, paperTableUnitDesign.treatment w i = true := by
  rcases w with ⟨a, b⟩
  fin_cases a
  · exact ⟨0, by simp [paperTableUnitDesign, paperTableDesign, paperTableCluster, twoOfFourLaw]⟩
  · exact ⟨0, by simp [paperTableUnitDesign, paperTableDesign, paperTableCluster, twoOfFourLaw]⟩
  · exact ⟨0, by simp [paperTableUnitDesign, paperTableDesign, paperTableCluster, twoOfFourLaw]⟩
  · exact ⟨2, by simp [paperTableUnitDesign, paperTableDesign, paperTableCluster, twoOfFourLaw]⟩
  · exact ⟨2, by simp [paperTableUnitDesign, paperTableDesign, paperTableCluster, twoOfFourLaw]⟩
  · exact ⟨4, by simp [paperTableUnitDesign, paperTableDesign, paperTableCluster, twoOfFourLaw]⟩

lemma control_exists (w : W2Allocation) :
    ∃ i : Fin 16, paperTableUnitDesign.treatment w i = false := by
  rcases w with ⟨a, b⟩
  fin_cases a
  · exact ⟨4, by simp [paperTableUnitDesign, paperTableDesign, paperTableCluster, twoOfFourLaw]⟩
  · exact ⟨2, by simp [paperTableUnitDesign, paperTableDesign, paperTableCluster, twoOfFourLaw]⟩
  · exact ⟨2, by simp [paperTableUnitDesign, paperTableDesign, paperTableCluster, twoOfFourLaw]⟩
  · exact ⟨0, by simp [paperTableUnitDesign, paperTableDesign, paperTableCluster, twoOfFourLaw]⟩
  · exact ⟨0, by simp [paperTableUnitDesign, paperTableDesign, paperTableCluster, twoOfFourLaw]⟩
  · exact ⟨0, by simp [paperTableUnitDesign, paperTableDesign, paperTableCluster, twoOfFourLaw]⟩

lemma Q1_pos (w : W2Allocation) : 0 < Q1 w := by
  unfold Q1 w2IPWArmWeight
  apply Finset.sum_pos'
  · intro i hi
    by_cases h : paperTableUnitDesign.treatment w i = true
    · simpa [h] using (weight_pos w i).le
    · simp [h]
  · obtain ⟨i, hi⟩ := treated_exists w
    exact ⟨i, Finset.mem_univ i, by simpa [hi] using weight_pos w i⟩

lemma Q0_pos (w : W2Allocation) : 0 < Q0 w := by
  unfold Q0 w2IPWArmWeight
  apply Finset.sum_pos'
  · intro i hi
    by_cases h : paperTableUnitDesign.treatment w i = false
    · simpa [h] using (weight_pos w i).le
    · simp [h]
  · obtain ⟨i, hi⟩ := control_exists w
    exact ⟨i, Finset.mem_univ i, by simpa [hi] using weight_pos w i⟩

lemma gram_form (w : W2Allocation) :
    w2Gram (w2IPWDesign w) (w2IPWWeight w) =
      !![Q0 w + Q1 w, Q1 w; Q1 w, Q1 w] := by
  ext j l
  fin_cases j <;> fin_cases l
  · simp [w2Gram, w2IPWDesign, w2Treatment, armIndicator, Q0, Q1,
      w2IPWArmWeight, w2IPWWeight]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ht : paperTableUnitDesign.treatment w i = true <;> simp [ht]
  all_goals
    simp [w2Gram, w2IPWDesign, w2Treatment, armIndicator, Q0, Q1,
      w2IPWArmWeight, w2IPWWeight] <;>
    apply Finset.sum_congr rfl <;> intro i hi <;>
    by_cases ht : paperTableUnitDesign.treatment w i = true <;> simp [ht]

def invCandidate (w : W2Allocation) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1 / Q0 w, -1 / Q0 w; -1 / Q0 w, 1 / Q0 w + 1 / Q1 w]

lemma gram_inv (w : W2Allocation) :
    (w2Gram (w2IPWDesign w) (w2IPWWeight w))⁻¹ = invCandidate w := by
  rw [gram_form w]
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, invCandidate, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt (Q0_pos w), ne_of_gt (Q1_pos w)] <;> ring

def invSandwich (w : W2Allocation) : ℚ :=
  (25/21) * ∑ g : Fin 10,
    (∑ j, invCandidate w 1 j *
      ∑ i ∈ (univ : Finset (Fin 16)).filter (fun i => paperTableCluster i = g),
        w2IPWWeight w i * w2IPWDesign w i j *
          (paperTableY i - w2Predict (w2IPWDesign w) (w2IPWBeta w) i))^2

lemma variance_invSandwich (w : W2Allocation) :
    w2IPWVariance w = invSandwich w := by
  rw [w2IPWVariance, w2ClusterHC1, gram_inv]
  norm_num [invSandwich]

/-- Exact 6 by 15 certificate. The columns repeat in groups of widths 2, 3, 1,
6, and 3, as is visible in the allocation construction. -/
def varianceCache (w : W2Allocation) : ℚ :=
  if w.1.val = 0 then
    if w.2.val < 2 then 386600/5876661 else if w.2.val < 5 then 4631287/68546400 else if w.2.val = 5 then 19925/599781 else if w.2.val < 12 then 80415447200/1240529144421 else 628944625/6608781312
  else if w.1.val = 1 ∨ w.1.val = 3 then
    if w.2.val < 2 then 1815558200/26795786661 else if w.2.val < 5 then 962/15309 else if w.2.val = 5 then 1733/42525 else if w.2.val < 12 then 1824752/24904341 else 55325/551124
  else if w.1.val = 2 ∨ w.1.val = 4 then
    if w.2.val < 2 then 18807800/330812181 else if w.2.val < 5 then 10493/196830 else if w.2.val = 5 then 22571/492075 else if w.2.val < 12 then 2024864/24904341 else 44425/489888
  else
    if w.2.val < 2 then 130369187000/2527437785061 else if w.2.val < 5 then 44193925/898017792 else if w.2.val = 5 then 85954025/1796035584 else if w.2.val < 12 then 106040625200/1124086158741 else 13753/268800

theorem sandwich_cache : ∀ w, invSandwich w = varianceCache w := by
  decide +kernel

theorem variance_cache : ∀ w, w2IPWVariance w = varianceCache w := by
  intro w
  rw [variance_invSandwich]
  exact sandwich_cache w

lemma e_variance_exact : designVariance paperTableDesign w2IPWEstimate =
    13596002132077280844902048265137/177869249303454972322974794880000 := by
  decide +kernel

lemma variance_mean_exact : mean paperTableDesign w2IPWVariance =
    880315389825587736856956203797734595631313956492348529708091/
      12321687845240287109992657554224827360889593657587312525312000 := by
  rw [show w2IPWVariance = varianceCache from funext variance_cache]
  decide +kernel

lemma variance_variance_exact : designVariance paperTableDesign w2IPWVariance =
    3940796349768187138837347942471660454069424991532397013400080969806495724029509521377765463325028706948163907710795039/
      13802181032322020868188286467773417353603838830951772533395950809040642689040283798039748446943031844941487149154304000000 := by
  rw [show w2IPWVariance = varianceCache from funext variance_cache]
  decide +kernel

theorem certificate :
    w2VarianceCertificate w2IPWEstimate w2IPWVariance
      (71/1000) (-5/1000) (17/1000) (18/1000) := by
  unfold w2VarianceCertificate
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [variance_mean_exact]
    norm_num [roundsToThree]
  · rw [variance_mean_exact, e_variance_exact]
    norm_num [roundsToThree]
  · rw [variance_variance_exact]
    norm_num [sdRoundsToThree]
  · rw [variance_mean_exact, e_variance_exact, variance_variance_exact]
    norm_num [sdRoundsToThree]

end
end SAP.P026a.WH.W2.P.T7_L8

theorem SAP.P026a.WH.W2.T7_L8_proof : SAP.P026a.WH.W2.T7_L8 := by
  exact SAP.P026a.WH.W2.P.T7_L8.certificate
