import SAP.P009a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter SAP.P009a.Bridge
open scoped BigOperators Topology Classical

theorem SAP.P009a.WH.W3.T6_L2_proof : SAP.P009a.WH.W3.T6_L2 := by
  unfold SAP.P009a.WH.W3.T6_L2
  intro S k L c hA hL hc hcL hInf
  dsimp
  let F := SAP.P009a.selectedLimsupSequence S L c
  have hk : 0 < k := hA 0 |>.1
  have hbound : ∀ t i z, |(F.experiment t).outcome i z| ≤ 1 / Real.sqrt L := by
    intro t i z
    by_cases hs : c ≤ SAP.P009a.interferenceDensity S t
    · have hfacts := SAP.P009a.WH.W3.finite_limsup_construction
        (S.positive t) (S.experiment t) k L (hA t) hL
      have hb := hfacts.2.2.1 i z
      simpa [F, SAP.P009a.selectedLimsupSequence, hs] using hb
    · simp [F, SAP.P009a.selectedLimsupSequence, hs]
  have hregular : ∀ q s : ℝ, 2 ≤ q → 1 ≤ s →
      ∃ K, 0 < K ∧ SAP.P009a.SequenceRegularity F K q s := by
    intro q s hq hs
    let K := max k (1 / Real.sqrt L)
    refine ⟨K, ?_, ?_⟩
    · dsimp [K]
      exact lt_of_lt_of_le hk (le_max_left _ _)
    · intro t
      have hAt : SAP.P009a.AssignmentBounds (F.experiment t) k := by
        by_cases hsel : c ≤ SAP.P009a.interferenceDensity S t
        · simp only [F, SAP.P009a.selectedLimsupSequence, if_pos hsel]
          exact hA t
        · simp only [F, SAP.P009a.selectedLimsupSequence, if_neg hsel]
          exact hA t
      have hRt := SAP.P009a.WH.W3.regularity_of_uniform_bound
        (F.experiment t) k (1 / Real.sqrt L) q s hAt (hbound t) hq hs
      simpa [K] using hRt
  have hprobInf : Set.Infinite {t |
      SAP.P009a.probability (F.experiment t).design
        (fun z => 1/(2*k) < |SAP.P009a.htEstimate (F.experiment t) z -
          SAP.P009a.expectedATE (F.experiment t)|) = 1} := by
    apply hInf.mono
    intro t ht
    change c ≤ SAP.P009a.interferenceDensity S t at ht
    have hfacts := SAP.P009a.WH.W3.finite_limsup_construction
      (S.positive t) (S.experiment t) k L (hA t) hL
    rcases hfacts with ⟨_, _, _, _, hpoint⟩
    have hE := hpoint
    let E := SAP.P009a.limsupPopulation (S.positive t) (S.experiment t) L
    have hall : ∀ z : SAP.P009a.TreatmentVector (S.N t),
        1/(2*k) < |SAP.P009a.htEstimate E z - SAP.P009a.expectedATE E| := by
      intro z
      have hp := hE z
      have hsmall : 1/(2*k) < k⁻¹ := by
        rw [one_div]
        apply (inv_lt_inv₀ (by positivity) (by positivity)).2
        nlinarith [hk]
      exact lt_of_lt_of_le hsmall hp.2.2
    have hprob : SAP.P009a.probability E.design
        (fun z => 1/(2*k) < |SAP.P009a.htEstimate E z - SAP.P009a.expectedATE E|) = 1 := by
      unfold SAP.P009a.probability SAP.P009a.expectation
      calc
        (∑ z, E.design.mass z *
            (if 1/(2*k) < |SAP.P009a.htEstimate E z - SAP.P009a.expectedATE E|
              then 1 else 0)) = ∑ z, E.design.mass z := by
          apply Finset.sum_congr rfl
          intro z hz
          simp only [if_pos (hall z), mul_one]
        _ = 1 := E.design.total
    have hFE : F.experiment t = E := by
      simp [F, SAP.P009a.selectedLimsupSequence, E, ht]
    change SAP.P009a.probability (F.experiment t).design
      (fun z => 1/(2*k) < |SAP.P009a.htEstimate (F.experiment t) z -
        SAP.P009a.expectedATE (F.experiment t)|) = 1
    rw [hFE]
    exact hprob
  have hnotConv : ¬ SAP.P009a.ConvergesInProbability F
      (fun t z => SAP.P009a.htEstimate (F.experiment t) z -
        SAP.P009a.expectedATE (F.experiment t)) := by
    intro hconv
    have heps : 0 < 1/(2*k) := by positivity
    have hT := hconv (1/(2*k)) heps
    have hev : ∀ᶠ t in atTop,
        SAP.P009a.probability (F.experiment t).design
          (fun z => 1/(2*k) < |SAP.P009a.htEstimate (F.experiment t) z -
            SAP.P009a.expectedATE (F.experiment t)|) < 1/2 := by
      have hlim : Tendsto
          (fun t => SAP.P009a.probability (F.experiment t).design
            (fun z => 1/(2*k) < |SAP.P009a.htEstimate (F.experiment t) z -
              SAP.P009a.expectedATE (F.experiment t)|)) atTop (nhds 0) := by
        simpa using hT
      have hlt : (0 : ℝ) < 1/2 := by norm_num
      exact hlim.eventually_lt tendsto_const_nhds hlt
    have hfreq : ∃ᶠ t in atTop,
        SAP.P009a.probability (F.experiment t).design
          (fun z => 1/(2*k) < |SAP.P009a.htEstimate (F.experiment t) z -
            SAP.P009a.expectedATE (F.experiment t)|) = 1 :=
      (Nat.frequently_atTop_iff_infinite).2 hprobInf
    obtain ⟨t, hEq, hLt⟩ := (hfreq.and_eventually hev).exists
    rw [hEq] at hLt
    norm_num at hLt
  exact ⟨hbound, hregular, hprobInf, hnotConv⟩
