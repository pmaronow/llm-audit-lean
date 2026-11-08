import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P005a.WH.W2.P.T7_L5

open Finset SAP.P005a.Bridge
open scoped BigOperators

noncomputable section

theorem spikeR_raw (h : SAP.P005a.WH.W2.T7_L3) (S : Finset (Fin 6))
    (hS : S ∈ SAP.P005a.design 6 3) :
    SAP.P005a.spikeR 6 S =
      SAP.P005a.spikeFit 6 S - SAP.P005a.spikeFit 6 (SAP.P005a.control S) -
        (SAP.P005a.mean S (SAP.P005a.spikeE 6) -
          SAP.P005a.mean (SAP.P005a.control S) (SAP.P005a.spikeE 6)) := by
  have hcard : S.card = 3 := by
    simpa [SAP.P005a.design] using hS
  have hCcard : (SAP.P005a.control S).card = 3 := by
    rw [SAP.P005a.control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp
    omega
  have ht := SAP.P005a.WH.W2.spikeFit_eq 6 (by omega) S (by omega)
  have hc := SAP.P005a.WH.W2.spikeFit_eq 6 (by omega) (SAP.P005a.control S) (by omega)
  have hlead := (h 6 (by omega)).2.2.2.2.2 S hS
  have hate : SAP.P005a.ate (SAP.P005a.spikePopulation 6) = 0 := by
    norm_num [SAP.P005a.ate, SAP.P005a.popMean, SAP.P005a.mean,
      SAP.P005a.spikePopulation, SAP.P005a.spikeV]
  simp only [SAP.P005a.spikePopulation] at ht hc hlead hate
  unfold SAP.P005a.spikeR SAP.P005a.interactedATE
  simp only [SAP.P005a.spikePopulation]
  rw [hate, hlead.1]
  linear_combination ht - hc

theorem mean_control_formula (S : Finset (Fin 6)) (hcard : S.card = 3)
    (f : Fin 6 → ℝ) :
    SAP.P005a.mean (SAP.P005a.control S) f =
      ((∑ i, f i) - (∑ i ∈ S, f i)) / 3 := by
  have hcardC : (Finset.univ \ S).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [hcard]
  have hsum := Finset.sum_sdiff (Finset.subset_univ S) (f := f)
  unfold SAP.P005a.mean SAP.P005a.control
  rw [hcardC]
  apply congrArg (fun x : ℝ => x / 3)
  linarith

theorem minimum_proof (h : SAP.P005a.WH.W2.T7_L3) :
    SAP.P005a.spikeMinimum 6 (4357386/779833) := by
  classical
  have hbraw := (h 6 (by omega)).1
  norm_num at hbraw
  have hb : SAP.P005a.spikeB 6 = (36/433 : ℝ) := hbraw
  have he : SAP.P005a.spikeE 6 =
      fun i => SAP.P005a.spikeV 6 i - (36/433 : ℝ) * SAP.P005a.spikeZ 6 i := by
    funext i
    simp [SAP.P005a.spikeE, hb]
  constructor
  · intro S hS
    rw [spikeR_raw h S hS]
    have hcard : S.card = 3 := by simpa [SAP.P005a.design] using hS
    rw [he]
    unfold SAP.P005a.spikeFit SAP.P005a.scalarSlope SAP.P005a.sampleCov
    simp_rw [mean_control_formula S hcard]
    fin_cases S
    all_goals norm_num [SAP.P005a.design] at hS
    all_goals norm_num [SAP.P005a.mean, SAP.P005a.spikeZ, SAP.P005a.spikeA,
      SAP.P005a.spikeV, Fin.sum_univ_succ] at ⊢
  · let S : Finset (Fin 6) := {0, 1, 2}
    have hS : S ∈ SAP.P005a.design 6 3 := by
      norm_num [S, SAP.P005a.design]
    have hcard : S.card = 3 := by norm_num [S]
    refine ⟨S, hS, ?_⟩
    rw [spikeR_raw h S hS]
    rw [he]
    unfold SAP.P005a.spikeFit SAP.P005a.scalarSlope SAP.P005a.sampleCov
    simp_rw [mean_control_formula S hcard]
    norm_num [S, SAP.P005a.mean, SAP.P005a.spikeZ, SAP.P005a.spikeA,
      SAP.P005a.spikeV, Fin.sum_univ_succ]

end
end SAP.P005a.WH.W2.P.T7_L5

theorem SAP.P005a.WH.W2.T7_L5_proof : SAP.P005a.WH.W2.T7_L5 := by
  intro h
  exact SAP.P005a.WH.W2.P.T7_L5.minimum_proof h
