import SAP.P001a.WH.W1.Leaves
import AronowAudit.External.Causalean.Stat.CLT.ChiSquared

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

noncomputable section

namespace SAP.P001a.WH.W1.P.T18_L11

lemma wholeChiSquare_eq_chiSqDist (L : ℕ) :
    SAP.P001a.wholeChiSquare L = Causalean.Stat.chiSqDist L := by
  unfold SAP.P001a.wholeChiSquare Causalean.Stat.chiSqDist
  rw [Causalean.Mathlib.stdGaussian_map_normSq_eq_pi]
  rw [finrank_euclideanSpace_fin]

lemma cdf_continuousAt_of_noAtoms (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (t : ℝ) : ContinuousAt (ProbabilityTheory.cdf μ) t := by
  have hmono : Monotone (ProbabilityTheory.cdf μ) := monotone_cdf μ
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  have hright : Function.rightLim (ProbabilityTheory.cdf μ) t =
      ProbabilityTheory.cdf μ t :=
    (hmono.continuousWithinAt_Ioi_iff_rightLim_eq).1
      (((ProbabilityTheory.cdf μ).right_continuous t).mono Set.Ioi_subset_Ici_self)
  have hle : Function.leftLim (ProbabilityTheory.cdf μ) t ≤
      ProbabilityTheory.cdf μ t := hmono.leftLim_le le_rfl
  have hge : ProbabilityTheory.cdf μ t ≤ Function.leftLim (ProbabilityTheory.cdf μ) t := by
    have h0 := (ProbabilityTheory.cdf μ).measure_singleton t
    rw [ProbabilityTheory.measure_cdf, measure_singleton, eq_comm,
      ENNReal.ofReal_eq_zero, sub_nonpos] at h0
    exact h0
  rw [le_antisymm hle hge, hright]

end SAP.P001a.WH.W1.P.T18_L11

theorem SAP.P001a.WH.W1.T18_L11_proof : SAP.P001a.WH.W1.T18_L11 := by
  intro Ω _ μ hμ L hL T hm hCD α hα
  let ν := SAP.P001a.wholeChiSquare L
  have hνeq : ν = Causalean.Stat.chiSqDist L :=
    SAP.P001a.WH.W1.P.T18_L11.wholeChiSquare_eq_chiSqDist L
  haveI : IsProbabilityMeasure ν := by
    rw [hνeq]
    infer_instance
  haveI : NullSingletonClass ν := by
    rw [hνeq]
    exact Causalean.Stat.noAtoms_chiSqDist (by omega)
  rcases hα with ⟨hα0, hα1⟩
  have hp0 : 0 < 1 - α := by linarith
  have hp1 : 1 - α < 1 := by linarith
  have hcont : Continuous (ProbabilityTheory.cdf ν) :=
    continuous_iff_continuousAt.mpr
      (fun x => SAP.P001a.WH.W1.P.T18_L11.cdf_continuousAt_of_noAtoms ν x)
  obtain ⟨a, ha⟩ :=
    ((tendsto_cdf_atBot ν).eventually (eventually_lt_nhds hp0)).exists
  obtain ⟨b, hb⟩ :=
    ((tendsto_cdf_atTop ν).eventually (eventually_gt_nhds hp1)).exists
  have hqexists : (1 - α) ∈ Set.range (ProbabilityTheory.cdf ν) :=
    intermediate_value_univ a b hcont ⟨ha.le, hb.le⟩
  obtain ⟨q, hq⟩ := hqexists
  have hquant : prob ν (Set.Iic q) = 1 - α := by
    simpa only [SAP.P001a.prob, ProbabilityTheory.cdf_eq_real, Measure.real] using hq
  have hcontq : ContinuousAt (fun x : ℝ => prob ν (Set.Iic x)) q := by
    convert (SAP.P001a.WH.W1.P.T18_L11.cdf_continuousAt_of_noAtoms ν q) using 1
    funext x
    exact (ProbabilityTheory.cdf_eq_real ν x).symm
  have hlower : Tendsto (fun n => prob μ {ω | T n ω ≤ q}) atTop
      (nhds (1 - α)) := by
    have h := hCD q hcontq
    rw [hquant] at h
    simpa [SAP.P001a.cdf, ν] using h
  have hcomp (n : ℕ) :
      prob μ {ω | q < T n ω} = 1 - prob μ {ω | T n ω ≤ q} := by
    have hset : {ω | q < T n ω} = ({ω | T n ω ≤ q} : Set Ω)ᶜ := by
      ext ω
      simp
    rw [hset]
    change μ.real ({ω | T n ω ≤ q}ᶜ) =
      1 - μ.real {ω | T n ω ≤ q}
    have hmeas : MeasurableSet {ω | T n ω ≤ q} := by
      exact (measurableSet_Iic : MeasurableSet (Set.Iic q)).preimage (hm n)
    rw [measureReal_compl (μ := μ) (s := {ω | T n ω ≤ q}) hmeas]
    simp [Measure.real, measure_univ]
  have hreject : Tendsto (fun n => prob μ {ω | q < T n ω}) atTop (nhds α) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have hbase : Tendsto (fun n => 1 - prob μ {ω | T n ω ≤ q}) atTop
        (nhds α) := by
      simpa using hone.sub hlower
    exact hbase.congr' (Eventually.of_forall (fun n => (hcomp n).symm))
  exact ⟨q, hquant, hreject, hlower⟩
