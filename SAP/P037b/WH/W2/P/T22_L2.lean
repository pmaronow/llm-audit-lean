import SAP.P037b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option maxRecDepth 20000
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SAP.P037b.WH.W2.P.T22_L2

lemma iidProbabilityPosW2 {Ω : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (E : (Fin 10000 → Ω) → Prop) (hE : ∃ draws, E draws) :
    0 < iidProbabilityW2 P.mass 10000 E := by
  classical
  unfold iidProbabilityW2 iidExpectationW2
  simp only [iidMassW2]
  exact AronowAudit.P037.Wave1.estimated_cutoff_event_pos
    (fun draws => ∏ j, P.mass (draws j))
    (fun draws => Finset.prod_pos (fun j hj => P.positive (draws j))) E hE

lemma iidComplementSumW2 {Ω : Type} [Fintype Ω] (P : ProbabilityDesign Ω)
    (E : (Fin 10000 → Ω) → Prop) :
    iidProbabilityW2 P.mass 10000 E + iidProbabilityW2 P.mass 10000 (fun draws => ¬ E draws) = 1 := by
  classical
  unfold iidProbabilityW2 iidExpectationW2
  simp only [iidMassW2]
  calc
    _ = ∑ draws : Fin 10000 → Ω,
        ((∏ j, P.mass (draws j)) * (if E draws then (1 : ℝ) else 0) +
          (∏ j, P.mass (draws j)) * (if ¬ E draws then (1 : ℝ) else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro draws _
      apply congrArg (fun x : ℝ =>
        (∏ j, P.mass (draws j)) * (if E draws then (1 : ℝ) else 0) +
          (∏ j, P.mass (draws j)) * x)
      exact ite_cond_congr rfl
    _ = ∑ draws : Fin 10000 → Ω, ∏ j, P.mass (draws j) := by
      apply Finset.sum_congr rfl
      intro draws _
      by_cases h : E draws <;> simp [h]
    _ = 1 := by simpa [iidMassW2] using iidTotalW2 P 10000

end SAP.P037b.WH.W2.P.T22_L2

theorem SAP.P037b.WH.W2.T22_L2_proof : SAP.P037b.WH.W2.T22_L2 := by
  change SAP.P037b.T22JointCutoffW2
  intro Ω I inst P D i hi
  classical
  have hprob (k : Fin 4) : 0 < eventProbability P (fun z => D z i = k.castSucc) ∧
      eventProbability P (fun z => D z i = k.castSucc) < 1 := hi k
  have hexists (k : Fin 4) : ∃ w : Ω, D w i = k.castSucc := by
    apply (AronowAudit.P037.Wave1.analysis_prob_positive_iff (SAP.P037b.Bridge.toProject P)
      (fun z => D z i = k.castSucc)).mp
    rw [← SAP.P037b.Bridge.probability_correspondence]
    exact (hprob k).1
  let reps : Fin 4 → Ω := fun k => Classical.choose (hexists k)
  have hreps (k : Fin 4) : D (reps k) i = k.castSucc := Classical.choose_spec (hexists k)
  have hdistinct : ∀ k l : Fin 4, k.castSucc = l.castSucc → k = l := by
    intro k l h
    exact Fin.castSucc_inj.mp h
  let passingDraws : Fin 10000 → Ω := fun j => reps (balancedScheduleW2 j)
  have hcounts (k : Fin 4) :
      hitCountW2 (fun z => D z i = k.castSucc) passingDraws = 2500 := by
    unfold hitCountW2
    calc
      _ = (Finset.univ.filter (fun j : Fin 10000 => balancedScheduleW2 j = k)).card := by
        apply congrArg Finset.card
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change D (reps (balancedScheduleW2 j)) i = k.castSucc ↔ balancedScheduleW2 j = k
        rw [hreps]
        constructor
        · intro h
          exact hdistinct _ _ h
        · intro h
          subst h
          rfl
      _ = 2500 := balancedScheduleCountW2 k
  have hpassfreq (k : Fin 4) :
      estimatedExposureW2 D passingDraws i k = 1/4 := by
    rw [estimatedFrequencyW2]
    unfold frequencyW2
    rw [hcounts k]
    norm_num
  have hpass : i ∈ exposureProbabilityCutoff (estimatedExposureW2 D passingDraws) (1/100) := by
    intro k
    rw [hpassfreq k]
    norm_num
  have hpassmass : 0 < iidMassW2 P.mass passingDraws := by
    unfold iidMassW2
    exact Finset.prod_pos (fun j hj => P.positive (passingDraws j))
  have hpassWitness :
      ∃ draws : Fin 10000 → Ω,
        (∀ j, ∃ k, draws j = reps k) ∧
        (∀ k : Fin 4, hitCountW2 (fun z => D z i = k.castSucc) draws = 2500) ∧
        i ∈ exposureProbabilityCutoff (estimatedExposureW2 D draws) (1/100) ∧
        0 < iidMassW2 P.mass draws := by
    refine ⟨passingDraws, ?_, hcounts, hpass, hpassmass⟩
    intro j
    exact ⟨balancedScheduleW2 j, rfl⟩

  let badState : Ω := reps 0
  have hbadLabel : D badState i = (0 : Fin 4).castSucc := hreps 0
  have hzero (k : Fin 4) (hk : k ≠ 0) :
      estimatedExposureW2 D (fun _ : Fin 10000 => badState) i k = 0 := by
    unfold estimatedExposureW2
    have hempty : Finset.univ.filter (fun j : Fin 10000 => D badState i = k.castSucc) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j _ heq
      apply hk
      exact hdistinct k 0 (heq.symm.trans hbadLabel)
    rw [hempty]
    norm_num
  have hbadcount : 3 ≤ (Finset.univ.filter (fun k : Fin 4 =>
      estimatedExposureW2 D (fun _ : Fin 10000 => badState) i k = 0)).card := by
    have hsubset : ({(1 : Fin 4), 2, 3} : Finset (Fin 4)) ⊆
        Finset.univ.filter (fun k : Fin 4 =>
          estimatedExposureW2 D (fun _ : Fin 10000 => badState) i k = 0) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hzero k (by
        intro h
        subst k
        rcases hk with h | h | h <;> norm_num at h)
    have hcard : ({(1 : Fin 4), 2, 3} : Finset (Fin 4)).card = 3 := by norm_num
    calc
      3 = ({(1 : Fin 4), 2, 3} : Finset (Fin 4)).card := hcard.symm
      _ ≤ _ := Finset.card_le_card hsubset
  have hbadfail : i ∉ exposureProbabilityCutoff
      (estimatedExposureW2 D (fun _ : Fin 10000 => badState)) (1/100) := by
    intro h
    have hk := h 1
    rw [hzero 1 (by norm_num)] at hk
    norm_num at hk
  have hbadmass : 0 < iidMassW2 P.mass (fun _ : Fin 10000 => badState) := by
    unfold iidMassW2
    exact Finset.prod_pos (fun j hj => P.positive badState)

  have hprobpos : 0 < iidProbabilityW2 P.mass 10000
      (fun draws => i ∈ exposureProbabilityCutoff (estimatedExposureW2 D draws) (1/100)) :=
    SAP.P037b.WH.W2.P.T22_L2.iidProbabilityPosW2 P
      (fun draws => i ∈ exposureProbabilityCutoff (estimatedExposureW2 D draws) (1/100))
      ⟨passingDraws, hpass⟩
  have hcomp : 0 < iidProbabilityW2 P.mass 10000
      (fun draws => ¬ i ∈ exposureProbabilityCutoff (estimatedExposureW2 D draws) (1/100)) :=
    SAP.P037b.WH.W2.P.T22_L2.iidProbabilityPosW2 P
      (fun draws => ¬ i ∈ exposureProbabilityCutoff (estimatedExposureW2 D draws) (1/100))
      ⟨fun _ => badState, hbadfail⟩
  have hsum := SAP.P037b.WH.W2.P.T22_L2.iidComplementSumW2 P
      (fun draws => i ∈ exposureProbabilityCutoff (estimatedExposureW2 D draws) (1/100))
  refine ⟨⟨reps, hreps, hpassWitness⟩, ?_, hprobpos, ?_⟩
  · refine ⟨badState, hbadcount, hbadfail, hbadmass⟩
  · linarith

