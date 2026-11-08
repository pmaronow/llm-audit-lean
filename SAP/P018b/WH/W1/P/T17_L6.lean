import SAP.P018b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section
namespace SAP.P018b.WH.W1.P.T17_L6

open Finset Matrix Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

abbrev Input := SAP.P018b.SimulationIndex 20 1 → ℝ
abbrev D := SAP.P018b.Dyad 20
abbrev GMat := SAP.P018b.Mat 2
abbrev BVec := SAP.P018b.Vec 2

end SAP.P018b.WH.W1.P.T17_L6

open SAP.P018b.WH.W1.P.T17_L6
open Finset Matrix Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

theorem SAP.P018b.WH.W1.T17_L6_proof : SAP.P018b.WH.W1.T17_L6 := by
  intro ω hdet
  let G : Input → GMat := fun x => SAP.P018b.sampleGram (SAP.P018b.wholeSimulationDesign x)
  let R : Input → (D → ℝ) := fun x => SAP.P018b.wholeSimulationResponse x
  let H : Input → BVec := fun x =>
    ∑ d : D, SAP.P018b.score (SAP.P018b.wholeSimulationDesign x d) (R x d)
  have hDesign : Continuous (fun x : Input => SAP.P018b.wholeSimulationDesign x) := by
    unfold SAP.P018b.wholeSimulationDesign SAP.P018b.simulationX
    fun_prop
  have hResponse : Continuous R := by
    apply continuous_pi
    intro d
    change Continuous (fun x : Input => SAP.P018b.wholeSimulationResponse x d)
    unfold SAP.P018b.wholeSimulationResponse SAP.P018b.simulationX SAP.P018b.simulationError
    fun_prop
  have hGram : Continuous G := by
    change Continuous (fun x : Input => ∑ d : D,
      SAP.P018b.outer (SAP.P018b.wholeSimulationDesign x d)
        (SAP.P018b.wholeSimulationDesign x d))
    apply continuous_finsetSum Finset.univ
    intro d hd
    unfold SAP.P018b.outer
    fun_prop
  have hScoreSum : Continuous H := by
    change Continuous (fun x : Input => ∑ d : D,
      SAP.P018b.score (SAP.P018b.wholeSimulationDesign x d) (R x d))
    apply continuous_finsetSum Finset.univ
    intro d hd
    unfold SAP.P018b.score
    fun_prop
  have hdetAt : ContinuousAt (fun x : Input => (G x).det) ω :=
    hGram.matrix_det.continuousAt
  have hInv : ContinuousAt (fun x : Input => (G x)⁻¹) ω := by
    have hInvBase : ContinuousAt (fun A : GMat => A⁻¹) (G ω) := by
      apply continuousAt_matrix_inv
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hdet
    exact hInvBase.comp hGram.continuousAt
  have hOLS : ContinuousAt (fun x : Input => (G x)⁻¹.mulVec (H x)) ω := by
    exact (continuous_fst.matrix_mulVec continuous_snd).continuousAt.comp₂ hInv hScoreSum.continuousAt
  have hOLSDef : ContinuousAt
      (fun x : Input => SAP.P018b.sampleOLS (SAP.P018b.wholeSimulationDesign x) (R x)) ω := by
    change ContinuousAt (fun x : Input => (G x)⁻¹.mulVec (H x)) ω
    exact hOLS
  have hDesignAt : ∀ d : D, ContinuousAt (fun x : Input => SAP.P018b.wholeSimulationDesign x d) ω := by
    intro d
    exact (continuousAt_apply d (SAP.P018b.wholeSimulationDesign ω)).comp hDesign.continuousAt
  have hResponseAt : ContinuousAt R ω := hResponse.continuousAt
  have hFit : ContinuousAt
      (fun x : Input => fun d : D =>
        SAP.P018b.fittedResidual (SAP.P018b.wholeSimulationDesign x) (R x) d) ω := by
    apply continuousAt_pi.mpr
    intro d
    change ContinuousAt (fun x : Input =>
      R x d - SAP.P018b.dot (SAP.P018b.wholeSimulationDesign x d)
        (SAP.P018b.sampleOLS (SAP.P018b.wholeSimulationDesign x) (R x))) ω
    apply ContinuousAt.sub
    · exact (continuousAt_pi.mp hResponseAt) d
    · unfold SAP.P018b.dot
      change Tendsto (fun x : Input => ∑ i : Fin 2,
        SAP.P018b.wholeSimulationDesign x d i *
          SAP.P018b.sampleOLS (SAP.P018b.wholeSimulationDesign x) (R x) i)
        (𝓝 ω) (𝓝 (∑ i : Fin 2,
          SAP.P018b.wholeSimulationDesign ω d i *
            SAP.P018b.sampleOLS (SAP.P018b.wholeSimulationDesign ω) (R ω) i))
      apply tendsto_finsetSum (Finset.univ : Finset (Fin 2))
      intro i hi
      exact ((continuousAt_pi.mp (hDesignAt d)) i).mul ((continuousAt_pi.mp hOLSDef) i)
  let Q : Input → (D → BVec) := fun x => fun d =>
    SAP.P018b.score (SAP.P018b.wholeSimulationDesign x d)
      (SAP.P018b.fittedResidual (SAP.P018b.wholeSimulationDesign x) (R x) d)
  let M : Input → GMat := fun x => SAP.P018b.meat SAP.P018b.members (Q x)
  have hScoreAt : ∀ d : D, ContinuousAt (fun x : Input => Q x d) ω := by
    intro d
    apply continuousAt_pi.mpr
    intro i
    unfold Q SAP.P018b.score
    exact ((continuousAt_pi.mp hFit) d).smul ((continuousAt_pi.mp (hDesignAt d)) i)
  have hQ : ContinuousAt Q ω := by
    apply continuousAt_pi.mpr
    exact hScoreAt
  let MeatMap : (D → BVec) → GMat := fun q => SAP.P018b.meat SAP.P018b.members q
  have hMeatMap : Continuous MeatMap := by
    dsimp [MeatMap, SAP.P018b.meat]
    apply continuous_finsetSum (Finset.univ : Finset D)
    intro d hd
    apply continuous_finsetSum (Finset.univ : Finset D)
    intro f hf
    by_cases hov : (SAP.P018b.members d ∩ SAP.P018b.members f).Nonempty
    · simp only [if_pos hov]
      unfold SAP.P018b.outer
      fun_prop
    · simp only [if_neg hov]
      exact continuous_const
  have hMeat : ContinuousAt M ω := by
    change ContinuousAt (fun x : Input => MeatMap (Q x)) ω
    exact hMeatMap.continuousAt.comp hQ
  have hSandwich : ContinuousAt (fun x : Input =>
      SAP.P018b.sandwich ((G x)⁻¹) (M x)) ω := by
    exact (continuous_fst.matrix_mul continuous_snd).continuousAt.comp₂
      ((continuous_fst.matrix_mul continuous_snd).continuousAt.comp₂ hInv hMeat) hInv
  constructor
  · simpa only [G] using hdetAt
  · change ContinuousAt (fun x : Input =>
      (SAP.P018b.sandwich ((G x)⁻¹) (M x)) 1 1) ω
    exact (continuousAt_pi.mp ((continuousAt_pi.mp hSandwich) (1 : Fin 2))) (1 : Fin 2)

end
