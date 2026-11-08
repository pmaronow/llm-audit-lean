import SAP.P022.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T6_L3

open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal
noncomputable section

lemma probability_nonneg (d : Design) (E : Assignment d → Prop) :
    0 ≤ designProbability d E := by
  classical
  unfold designProbability designExpectation
  apply Finset.expect_nonneg
  intro π hπ
  split_ifs <;> norm_num

lemma probability_mono (d : Design) {E F : Assignment d → Prop}
    (hEF : ∀ π, E π → F π) : designProbability d E ≤ designProbability d F := by
  classical
  unfold designProbability designExpectation
  apply Finset.expect_le_expect
  intro π hπ
  by_cases hE : E π
  · have hF : F π := hEF π hE
    simp [hE, hF]
  · by_cases hF : F π <;> simp [hE, hF]

lemma limsup_finset_sum_le_ofReal {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ℕ → ι → ℝ≥0∞) (b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 ≤ b i)
    (hlim : ∀ i ∈ s, Filter.limsup (fun n => f n i) atTop ≤ ENNReal.ofReal (b i)) :
    Filter.limsup (fun n => s.sum (fun i => f n i)) atTop ≤
      ENNReal.ofReal (s.sum b) := by
  classical
  have hB : 0 ≤ s.sum b := Finset.sum_nonneg fun i hi => hb i hi
  rw [Filter.limsup_le_iff']
  intro y hy
  by_cases hyTop : y = ⊤
  · subst y
    exact Filter.Eventually.of_forall fun _ => le_top
  · have hyEq : ENNReal.ofReal y.toReal = y := ENNReal.ofReal_toReal hyTop
    have hBlt : s.sum b < y.toReal := by
      exact (ENNReal.ofReal_lt_iff_lt_toReal hB hyTop).mp (by simpa [hyEq] using hy)
    let δ : ℝ := (y.toReal - s.sum b) / ((s.card : ℝ) + 1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hev : ∀ᶠ n : ℕ in atTop, ∀ i ∈ s, f n i < ENNReal.ofReal (b i + δ) := by
      apply s.eventually_all.mpr
      intro i hi
      have hlimlt : Filter.limsup (fun n => f n i) atTop < ENNReal.ofReal (b i + δ) := by
        apply lt_of_le_of_lt (hlim i hi)
        apply ENNReal.ofReal_lt_ofReal_iff (by linarith [hb i hi, hδ]) |>.2
        linarith
      exact Filter.eventually_lt_of_limsup_lt hlimlt
    filter_upwards [hev] with n hn
    have hsumlt : s.sum (fun i => f n i) < s.sum (fun i => ENNReal.ofReal (b i + δ)) :=
      ENNReal.sum_lt_sum_of_nonempty hs hn
    have hsumEq : s.sum (fun i => ENNReal.ofReal (b i + δ)) =
        ENNReal.ofReal (s.sum b + (s.card : ℝ) * δ) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        simp [Finset.sum_add_distrib]
      · intro i hi
        linarith [hb i hi, hδ]
    rw [hsumEq] at hsumlt
    have hgap : s.sum b + (s.card : ℝ) * δ < y.toReal := by
      dsimp [δ]
      have hc : 0 < (s.card : ℝ) + 1 := by positivity
      have hc' : (s.card : ℝ) < (s.card : ℝ) + 1 := by linarith
      have hdiff : 0 < y.toReal - s.sum b := by linarith
      have haux : (s.card : ℝ) * ((y.toReal - s.sum b) / ((s.card : ℝ) + 1)) <
          y.toReal - s.sum b := by
        rw [← mul_div_assoc]
        rw [div_lt_iff₀ hc]
        nlinarith
      linarith
    have hypos : 0 < y.toReal := by linarith [hB, hBlt]
    have hltY : ENNReal.ofReal (s.sum b + (s.card : ℝ) * δ) < y := by
      rw [← hyEq]
      exact (ENNReal.ofReal_lt_ofReal_iff hypos).2 hgap
    exact hsumlt.le.trans hltY.le

lemma termRateCoefficient_pos (θ ρ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (i : Fin 8) : 0 < termRateCoefficient θ ρ i := by
  have hA : 0 < 1 - θ * ρ := by
    have hmul := mul_le_mul_of_nonneg_right hθ1 hρ.le
    nlinarith
  have hB : 0 < 1 - θ * (1 - ρ) := by
    have h1ρ : 0 < 1 - ρ := by linarith
    have hmul := mul_le_mul_of_nonneg_right hθ1 h1ρ.le
    nlinarith
  have h1ρ : 0 < 1 - ρ := by linarith
  have hd1 : 0 < θ ^ 3 * ρ ^ 3 := by positivity
  have hd0 : 0 < θ ^ 3 * (1 - ρ) ^ 3 := by positivity
  have hd1' : 0 < θ * ρ := mul_pos hθ hρ
  have hd0' : 0 < θ * (1 - ρ) := mul_pos hθ h1ρ
  fin_cases i
  · simp [termRateCoefficient]
    exact div_pos (by positivity) hd1
  · simp [termRateCoefficient]
    exact div_pos (by positivity) hd1
  · simp [termRateCoefficient]
    exact div_pos (by positivity) hd0
  · simp [termRateCoefficient]
    exact div_pos (by positivity) hd0
  · simp [termRateCoefficient]
    exact div_pos (by positivity) hd1'
  · simp [termRateCoefficient]
    exact div_pos (by positivity) hd0'
  · simp [termRateCoefficient]
    exact div_pos (by positivity) hd1'
  · simp [termRateCoefficient]
    exact div_pos (by positivity) hd0'

lemma sixTermCoefficient_pos (θ ρ : ℝ) (ν : Fin 8 → ℝ) (j : Fin 6)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hν : ∀ i, 0 < ν i) : 0 < sixTermCoefficient θ ρ ν j := by
  have hc (i : Fin 8) : 0 < termRateCoefficient θ ρ i :=
    termRateCoefficient_pos θ ρ hθ hθ1 hρ hρ1 i
  have hn0 : 0 < ν 0 := hν 0
  have hn1 : 0 < ν 1 := hν 1
  have hn2 : 0 < ν 2 := hν 2
  have hn3 : 0 < ν 3 := hν 3
  have hn4 : 0 < ν 4 := hν 4
  have hn5 : 0 < ν 5 := hν 5
  have hn6 : 0 < ν 6 := hν 6
  have hn7 : 0 < ν 7 := hν 7
  fin_cases j
  · simpa [sixTermCoefficient] using div_pos (hc 0) (sq_pos_of_pos hn0)
  · simpa [sixTermCoefficient] using div_pos (hc 1) (sq_pos_of_pos hn1)
  · simpa [sixTermCoefficient] using div_pos (hc 2) (sq_pos_of_pos hn2)
  · simpa [sixTermCoefficient] using div_pos (hc 3) (sq_pos_of_pos hn3)
  · simp only [sixTermCoefficient]
    exact add_pos (div_pos (hc 4) (sq_pos_of_pos hn4)) (div_pos (hc 5) (sq_pos_of_pos hn5))
  · simp only [sixTermCoefficient]
    exact add_pos (div_pos (hc 6) (sq_pos_of_pos hn6)) (div_pos (hc 7) (sq_pos_of_pos hn7))

lemma lastTermRate_nonneg (θ ρ C ε1 ξ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hC : 0 < C) (_hε1 : 0 < ε1) (hξ : 0 < ξ ∧ ξ < ε1 / (16 * C ^ 2)) :
    0 ≤ lastTermRate θ ρ C ε1 ξ := by
  unfold lastTermRate
  have hη : 0 < ε1 / (16 * C ^ 2) - ξ := by
    have hd : 0 < 16 * C ^ 2 := by positivity
    linarith [div_pos _hε1 hd]
  exact add_nonneg
    (marginal_rate_nonneg θ ρ hθ hθ1 hρ hρ1 true _)
    (marginal_rate_nonneg θ ρ hθ hθ1 hρ hρ1 false _)

lemma upperRateSum (θ ρ C ε1 ξ : ℝ) (ν : Fin 8 → ℝ) :
    ∑ j : Fin 7, (if hj : j.val < 6 then
      C ^ 4 * sixTermCoefficient θ ρ ν ⟨j.val, hj⟩
      else lastTermRate θ ρ C ε1 ξ) =
      C ^ 4 * coefficientSum θ ρ ν + lastTermRate θ ρ C ε1 ξ := by
  simp [sixTermCoefficient, coefficientSum, Fin.sum_univ_succ]
  ring

lemma proof_core : SAP.P022.WH.W1.T6_L3 := by
  intro hLast
  unfold UpperConditionalConclusion
  intro S H θ ρ C hCond hC hy hLemma ε1 ξ ν hε1 hξ hξlt hν hνsum hEarlier ε hε
  have hθ := hCond.1
  have hθ1 := hCond.2.1
  have hρ := hCond.2.2.1
  have hρ1 := hCond.2.2.2.1
  have hAllocSum : (∑ j : Fin 7, correctedAllocation ν ε1 j) = ε1 :=
    Bridge.corrected_allocation_sum ν ε1 hνsum
  have hAllocPos : ∀ j : Fin 7, 0 < correctedAllocation ν ε1 j := by
    have hn0 : 0 < ν 0 := hν 0
    have hn1 : 0 < ν 1 := hν 1
    have hn2 : 0 < ν 2 := hν 2
    have hn3 : 0 < ν 3 := hν 3
    have hn4 : 0 < ν 4 := hν 4
    have hn5 : 0 < ν 5 := hν 5
    have hn6 : 0 < ν 6 := hν 6
    have hn7 : 0 < ν 7 := hν 7
    intro j
    fin_cases j <;> simp [correctedAllocation] <;> positivity
  have hcenterEq (q : ℕ) (π : Assignment (S.design q)) :
      |centeredUpperError S q π| = (S.design q).N *
        |estimatedVariance (S.design q) (rowOutcomes S true q)
            (rowOutcomes S false q) .H π -
          populationBound (S.design q) (rowOutcomes S true q)
            (rowOutcomes S false q) .H| := by
    simp [centeredUpperError, rowSize, rowEstimate, rowBound, abs_mul,
      abs_of_nonneg (show 0 ≤ ((S.design q).N : ℝ) by positivity)]
  have hprobBudget (q : ℕ) :
      designProbability (S.design q) (fun π => ε1 ≤ |centeredUpperError S q π|) ≤
      ∑ j : Fin 7, designProbability (S.design q) (fun π =>
        correctedAllocation ν ε1 j ≤ |sevenTerms (S.design q)
          (rowOutcomes S true q) (rowOutcomes S false q) C π j|) := by
    have hyFin : ∀ i : Fin (S.design q).N,
        |rowOutcomes S true q i| ≤ C ∧ |rowOutcomes S false q i| ≤ C := by
      intro i
      exact hy i.val
    have h := (retained_T6.1 (S.design q) (rowOutcomes S true q)
      (rowOutcomes S false q) C (le_of_lt hC) hyFin).2.1
      (correctedAllocation ν ε1) ε1 hAllocPos
      (by rw [hAllocSum])
    have hcenter (π : Assignment (S.design q)) :
        ε1 ≤ (S.design q).N * |estimatedVariance (S.design q)
              (rowOutcomes S true q) (rowOutcomes S false q) .H π -
            populationBound (S.design q) (rowOutcomes S true q)
              (rowOutcomes S false q) .H| ↔
          ε1 ≤ |centeredUpperError S q π| := by rw [hcenterEq]
    simpa only [hcenter] using h
  have hscaledPoint (q : ℕ) :
      ENNReal.ofReal ((S.design q).N * designProbability (S.design q)
        (fun π => ε1 ≤ |centeredUpperError S q π|)) ≤
      ∑ j : Fin 7, ENNReal.ofReal ((S.design q).N * designProbability (S.design q)
        (fun π => correctedAllocation ν ε1 j ≤ |sevenTerms (S.design q)
          (rowOutcomes S true q) (rowOutcomes S false q) C π j|)) := by
    have hmul := mul_le_mul_of_nonneg_left (hprobBudget q)
      (Nat.cast_nonneg (S.design q).N)
    calc
      _ ≤ ENNReal.ofReal ((S.design q).N *
          ∑ j : Fin 7, designProbability (S.design q) (fun π =>
            correctedAllocation ν ε1 j ≤ |sevenTerms (S.design q)
              (rowOutcomes S true q) (rowOutcomes S false q) C π j|)) :=
        ENNReal.ofReal_le_ofReal hmul
      _ = _ := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
        · intro j hj
          exact mul_nonneg (Nat.cast_nonneg _) (probability_nonneg _ _)
  have htermRates : ∀ j : Fin 7,
      scaledProbabilityLimsup S (fun q π => correctedAllocation ν ε1 j ≤
          |sevenTerms (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) C π j|) ≤
        ENNReal.ofReal (if hj : j.val < 6 then
          C ^ 4 * sixTermCoefficient θ ρ ν ⟨j.val, hj⟩
          else lastTermRate θ ρ C ε1 ξ) := by
    intro j
    fin_cases j
    · simpa [correctedAllocation, sixTermCoefficient] using hEarlier ⟨0, by omega⟩
    · simpa [correctedAllocation, sixTermCoefficient] using hEarlier ⟨1, by omega⟩
    · simpa [correctedAllocation, sixTermCoefficient] using hEarlier ⟨2, by omega⟩
    · simpa [correctedAllocation, sixTermCoefficient] using hEarlier ⟨3, by omega⟩
    · simpa [correctedAllocation, sixTermCoefficient] using hEarlier ⟨4, by omega⟩
    · simpa [correctedAllocation, sixTermCoefficient] using hEarlier ⟨5, by omega⟩
    · have hl := hLast S H θ ρ C hCond hC hy hLemma ε1 ξ hε1 hξ hξlt
      simpa [correctedAllocation, sevenTerms] using hl
  have htermNonneg : ∀ j : Fin 7, 0 ≤ (if hj : j.val < 6 then
      C ^ 4 * sixTermCoefficient θ ρ ν ⟨j.val, hj⟩
      else lastTermRate θ ρ C ε1 ξ) := by
    intro j
    by_cases hj : j.val < 6
    · have hp := sixTermCoefficient_pos θ ρ ν ⟨j.val, hj⟩ hθ hθ1 hρ hρ1 hν
      simp [hj]
      positivity
    · have hp := lastTermRate_nonneg θ ρ C ε1 ξ hθ hθ1 hρ hρ1 hC hε1 ⟨hξ, hξlt⟩
      simpa [hj] using hp
  have hlimUnion :
      scaledProbabilityLimsup S (fun q π => ε1 ≤ |centeredUpperError S q π|) ≤
        ENNReal.ofReal (∑ j : Fin 7, (if hj : j.val < 6 then
          C ^ 4 * sixTermCoefficient θ ρ ν ⟨j.val, hj⟩
          else lastTermRate θ ρ C ε1 ξ)) := by
    unfold scaledProbabilityLimsup
    calc
      Filter.limsup (fun q => ENNReal.ofReal ((S.design q).N *
          designProbability (S.design q) (fun π => ε1 ≤ |centeredUpperError S q π|))) atTop ≤
        Filter.limsup (fun q => ∑ j : Fin 7, ENNReal.ofReal ((S.design q).N *
          designProbability (S.design q) (fun π => correctedAllocation ν ε1 j ≤
            |sevenTerms (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) C π j|))) atTop :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall hscaledPoint)
      _ ≤ _ := by
        exact limsup_finset_sum_le_ofReal Finset.univ Finset.univ_nonempty
          (fun q j => ENNReal.ofReal ((S.design q).N *
            designProbability (S.design q) (fun π => correctedAllocation ν ε1 j ≤
              |sevenTerms (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) C π j|)))
          (fun j => if hj : j.val < 6 then
            C ^ 4 * sixTermCoefficient θ ρ ν ⟨j.val, hj⟩
            else lastTermRate θ ρ C ε1 ξ)
          (by intro j hj; exact htermNonneg j)
          (by
            intro j hj
            have hjlim := htermRates j
            simpa [scaledProbabilityLimsup] using hjlim)
  have htermSum :
      (∑ j : Fin 7, (if hj : j.val < 6 then
        C ^ 4 * sixTermCoefficient θ ρ ν ⟨j.val, hj⟩
        else lastTermRate θ ρ C ε1 ξ)) =
        C ^ 4 * coefficientSum θ ρ ν + lastTermRate θ ρ C ε1 ξ :=
    upperRateSum θ ρ C ε1 ξ ν
  have hsecond :
      scaledProbabilityLimsup S (fun q π => ε1 ≤ |centeredUpperError S q π|) ≤
        ENNReal.ofReal (C ^ 4 * coefficientSum θ ρ ν + lastTermRate θ ρ C ε1 ξ) := by
    simpa [htermSum] using hlimUnion
  have hfirst :
      scaledProbabilityLimsup S (fun q π => ε ≤ |centeredUpperError S q π|) ≤
        scaledProbabilityLimsup S (fun q π => ε1 ≤ |centeredUpperError S q π|) := by
    unfold scaledProbabilityLimsup
    apply Filter.limsup_le_limsup
      (Filter.Eventually.of_forall fun q => by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (S.design q).N)
        exact probability_mono _ fun π hp => (le_trans hε.le hp))
      (Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
        (Filter.Frequently.of_forall fun q => by positivity))
      (Filter.isBoundedUnder_of_eventually_le (a := ⊤)
        (Filter.Eventually.of_forall fun _ => le_top))
  exact ⟨hfirst, hsecond⟩

end
end SAP.P022.WH.W1.P.T6_L3

theorem SAP.P022.WH.W1.T6_L3_proof : SAP.P022.WH.W1.T6_L3 :=
  SAP.P022.WH.W1.P.T6_L3.proof_core
