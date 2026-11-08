import SAP.P018b.WH.W1.Leaves
import AronowAudit.P018.Wave1.Gap.GP0181B1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace SAP.P018b.WH.W1.P.T17_L4

open Finset Matrix
open scoped BigOperators Matrix.Norms.Elementwise

def point (i : Fin 20) : ℝ :=
  if i.val = 0 then 1 else if i.val = 1 then 2 else if i.val = 2 then 3 else
  if i.val = 3 then 4 else 5 / 2

def z (i j : Fin 20) : ℝ := |point i - point j|

def p (i j : Fin 20) : ℝ :=
  if i.val = 0 ∧ j.val = 1 then 1 else
  if i.val = 0 ∧ j.val = 2 then -1 else
  if i.val = 1 ∧ j.val = 3 then -1 else
  if i.val = 2 ∧ j.val = 3 then 1 else 0

def z2 (i j : Fin 20) : ℝ := z i j * z i j
def zp (i j : Fin 20) : ℝ := z i j * p i j

lemma z_sum : (∑ d : SAP.P018b.Dyad 20,
    z (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) = 74 := by
  change (∑ d : AronowAudit.P018.Dyad 20,
    z (AronowAudit.P018.firstUnit d) (AronowAudit.P018.secondUnit d)) = 74
  rw [AronowAudit.P018.Wave1.printed_upper_sum]
  norm_num [z, point, Fin.sum_univ_succ]

lemma z_sq_sum : (∑ d : SAP.P018b.Dyad 20,
    z2 (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) = 100 := by
  change (∑ d : AronowAudit.P018.Dyad 20,
    z2 (AronowAudit.P018.firstUnit d) (AronowAudit.P018.secondUnit d)) = 100
  rw [AronowAudit.P018.Wave1.printed_upper_sum]
  norm_num [z2, z, point, Fin.sum_univ_succ]

lemma p_sum : (∑ d : SAP.P018b.Dyad 20,
    p (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) = 0 := by
  change (∑ d : AronowAudit.P018.Dyad 20,
    p (AronowAudit.P018.firstUnit d) (AronowAudit.P018.secondUnit d)) = 0
  rw [AronowAudit.P018.Wave1.printed_upper_sum]
  norm_num [p, Fin.sum_univ_succ]

lemma zp_sum : (∑ d : SAP.P018b.Dyad 20,
    zp (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) = -2 := by
  change (∑ d : AronowAudit.P018.Dyad 20,
    zp (AronowAudit.P018.firstUnit d) (AronowAudit.P018.secondUnit d)) = -2
  rw [AronowAudit.P018.Wave1.printed_upper_sum]
  norm_num [zp, z, p, point, Fin.sum_univ_succ]

lemma padded_eq (d : SAP.P018b.Dyad 20) :
    SAP.P018b.wholePaddedY d =
      p (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) := by
  rfl

lemma simX_eq (i : Fin 20) : SAP.P018b.simulationX SAP.P018b.wholeTwentyPoint i = point i := by
  simp [SAP.P018b.simulationX, SAP.P018b.wholeTwentyPoint, point]

lemma design_entries (d : SAP.P018b.Dyad 20) :
    SAP.P018b.wholeSimulationDesign SAP.P018b.wholeTwentyPoint d =
      ![1, z (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)] := by
  simp [SAP.P018b.wholeSimulationDesign, z, point, SAP.P018b.simulationX,
    SAP.P018b.wholeTwentyPoint]

lemma response_entries (d : SAP.P018b.Dyad 20) :
    SAP.P018b.wholeSimulationResponse SAP.P018b.wholeTwentyPoint d =
      z (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) +
        p (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) := by
  rw [SAP.P018b.wholeSimulationResponse, simX_eq, simX_eq]
  simp [SAP.P018b.simulationError, SAP.P018b.wholeTwentyPoint, padded_eq, z, point]

lemma gram_eq :
    SAP.P018b.sampleGram (SAP.P018b.wholeSimulationDesign SAP.P018b.wholeTwentyPoint) =
      !![(190 : ℝ), 74; 74, 100] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [SAP.P018b.sampleGram, Matrix.sum_apply, SAP.P018b.outer, design_entries] using
      (show (∑ d : SAP.P018b.Dyad 20, (1 : ℝ)) = 190 by
        calc
          _ = (Fintype.card (SAP.P018b.Dyad 20) : ℝ) := by simp
          _ = SAP.P018b.Dreal 20 := AronowAudit.P018.Wave1.printed_card_real 20
          _ = 190 := by norm_num [SAP.P018b.Dreal])
  · simpa [SAP.P018b.sampleGram, Matrix.sum_apply, SAP.P018b.outer, design_entries] using z_sum
  · simpa [SAP.P018b.sampleGram, Matrix.sum_apply, SAP.P018b.outer, design_entries] using z_sum
  · simpa [SAP.P018b.sampleGram, Matrix.sum_apply, SAP.P018b.outer, design_entries, z2] using z_sq_sum

lemma response_sums :
    (∑ d : SAP.P018b.Dyad 20,
      SAP.P018b.wholeSimulationResponse SAP.P018b.wholeTwentyPoint d) = 74 ∧
    (∑ d : SAP.P018b.Dyad 20,
      (z (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) *
        SAP.P018b.wholeSimulationResponse SAP.P018b.wholeTwentyPoint d) = 98 := by
  constructor
  · simp_rw [response_entries]
    rw [Finset.sum_add_distrib, z_sum, p_sum]
    norm_num
  · simp_rw [response_entries]
    calc
      _ = ∑ d : SAP.P018b.Dyad 20,
          (z2 (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) +
            zp (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) := by
        apply Finset.sum_congr rfl
        intro d hd
        simp [z2, zp]
        ring
      _ = 98 := by rw [Finset.sum_add_distrib, z_sq_sum, zp_sum]; norm_num

lemma score_sum :
    (∑ d : SAP.P018b.Dyad 20,
      SAP.P018b.score
        (SAP.P018b.wholeSimulationDesign SAP.P018b.wholeTwentyPoint d)
        (SAP.P018b.wholeSimulationResponse SAP.P018b.wholeTwentyPoint d)) = ![74, 98] := by
  ext i
  fin_cases i
  · have h := response_sums.1
    simpa [SAP.P018b.score, design_entries] using h
  · have h := response_sums.2
    simpa [SAP.P018b.score, design_entries, mul_comm] using h

end SAP.P018b.WH.W1.P.T17_L4

theorem SAP.P018b.WH.W1.T17_L4_proof : SAP.P018b.WH.W1.T17_L4 := by
  constructor
  · exact SAP.P018b.WH.W1.P.T17_L4.gram_eq
  · rw [SAP.P018b.sampleOLS, SAP.P018b.WH.W1.P.T17_L4.gram_eq]
    let G : SAP.P018b.Mat 2 := !![(190 : ℝ), 74; 74, 100]
    let B : SAP.P018b.Mat 2 := !![100 / 13524, -74 / 13524; -74 / 13524, 190 / 13524]
    have hB : B * G = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [B, G, Matrix.mul_apply, Fin.sum_univ_succ]
    have hi : G⁻¹ = B := Matrix.inv_eq_left_inv hB
    rw [hi, SAP.P018b.WH.W1.P.T17_L4.score_sum]
    ext i
    fin_cases i <;> norm_num [Matrix.mulVec, B, Fin.sum_univ_succ]
