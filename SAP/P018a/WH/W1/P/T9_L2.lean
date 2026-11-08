import SAP.P018a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section

namespace SAP.P018a.WH.W1.P.T9_L2

open Finset
open scoped BigOperators

end SAP.P018a.WH.W1.P.T9_L2

theorem SAP.P018a.WH.W1.T9_L2_proof : SAP.P018a.WH.W1.T9_L2 := by
  intro N hN
  let i : Fin N := ⟨0, by omega⟩
  have hpair := AronowAudit.P018.Wave1.concentrated_weights_pair_linear
    (N := N) AronowAudit.P018.Wave1.concentrated_weights_q
    (fun _ : Fin N => (1 : ℝ))
  have hleft :
      (∑ d : AronowAudit.P018.Dyad N,
        AronowAudit.P018.Wave1.concentrated_weights_q
            (AronowAudit.P018.firstUnit d) *
          AronowAudit.P018.Wave1.concentrated_weights_q
            (AronowAudit.P018.secondUnit d) * (1 + 1)) =
        2 * AronowAudit.P018.Wave1.concentrated_weights_W N := by
    calc
      _ = ∑ d : AronowAudit.P018.Dyad N,
          2 * AronowAudit.P018.concentratedWeight d := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [← AronowAudit.P018.Wave1.concentrated_weights_factor d]
        norm_num
        ring
      _ = 2 * AronowAudit.P018.Wave1.concentrated_weights_W N := by
        rw [← Finset.mul_sum]
        simp only [AronowAudit.P018.Wave1.concentrated_weights_W]
  have hnum :
      (∑ j : Fin N,
        AronowAudit.P018.Wave1.concentrated_weights_q j *
          ((∑ k : Fin N, AronowAudit.P018.Wave1.concentrated_weights_q k) -
            AronowAudit.P018.Wave1.concentrated_weights_q j)) =
        2 * AronowAudit.P018.Wave1.concentrated_weights_W N := by
    change (∑ j : Fin N,
      AronowAudit.P018.Wave1.concentrated_weights_q j *
        (AronowAudit.P018.Wave1.concentrated_weights_S N -
          AronowAudit.P018.Wave1.concentrated_weights_q j)) =
      2 * AronowAudit.P018.Wave1.concentrated_weights_W N
    calc
      _ = (∑ d : AronowAudit.P018.Dyad N,
          AronowAudit.P018.Wave1.concentrated_weights_q
              (AronowAudit.P018.firstUnit d) *
            AronowAudit.P018.Wave1.concentrated_weights_q
              (AronowAudit.P018.secondUnit d) * (1 + 1)) := by
        simpa only [AronowAudit.P018.Wave1.concentrated_weights_S,
          mul_one] using hpair.symm
      _ = 2 * AronowAudit.P018.Wave1.concentrated_weights_W N := hleft
  have hWpos : 0 < AronowAudit.P018.Wave1.concentrated_weights_W N :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/8)
      (AronowAudit.P018.Wave1.concentrated_weights_W_lower hN)
  have hnumS :
      (∑ j : Fin N,
        AronowAudit.P018.Wave1.concentrated_weights_q j *
          (AronowAudit.P018.Wave1.concentrated_weights_S N -
            AronowAudit.P018.Wave1.concentrated_weights_q j)) =
        2 * AronowAudit.P018.Wave1.concentrated_weights_W N := hnum
  have hsum : (∑ j : Fin N, W1c j) = 2 := by
    change (∑ j : Fin N,
      AronowAudit.P018.Wave1.concentrated_weights_q j *
        (AronowAudit.P018.Wave1.concentrated_weights_S N -
          AronowAudit.P018.Wave1.concentrated_weights_q j) /
        AronowAudit.P018.Wave1.concentrated_weights_W N) = 2
    calc
      _ = (∑ j : Fin N,
          AronowAudit.P018.Wave1.concentrated_weights_q j *
            (AronowAudit.P018.Wave1.concentrated_weights_S N -
              AronowAudit.P018.Wave1.concentrated_weights_q j)) /
            AronowAudit.P018.Wave1.concentrated_weights_W N := by
        rw [← Finset.sum_div]
      _ = 2 := by
        rw [hnumS]
        field_simp [ne_of_gt hWpos]
  have hx := AronowAudit.P018.Wave1.concentrated_weights_x_bounds hN
  have hs : 0 < 1 - AronowAudit.P018.Wave1.concentrated_weights_x N := by
    linarith [hx.2]
  have hs' : 0 < 1 - 2 * AronowAudit.P018.Wave1.concentrated_weights_x N := by
    linarith [hx.2]
  have hfirst : W1c i = 3 / (4 * (1 - W1x N)) := by
    change AronowAudit.P018.Wave1.concentrated_weights_c i =
      3 / (4 * (1 - AronowAudit.P018.Wave1.concentrated_weights_x N))
    have hc : AronowAudit.P018.Wave1.concentrated_weights_c i =
        3 / (4 * (1 - AronowAudit.P018.Wave1.concentrated_weights_x N)) := by
      simp only [AronowAudit.P018.Wave1.concentrated_weights_c,
        AronowAudit.P018.Wave1.concentrated_weights_S_formula,
        AronowAudit.P018.Wave1.concentrated_weights_W_formula,
        AronowAudit.P018.Wave1.concentrated_weights_q, i]
      norm_num
      field_simp
      <;> ring
    exact hc
  have hbound : (3 / 4 : ℝ) ≤ W1c i := by
    rw [hfirst]
    change (3 / 4 : ℝ) ≤ 3 /
      (4 * (1 - AronowAudit.P018.Wave1.concentrated_weights_x N))
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hx.1]
  refine ⟨?_, ?_, ?_⟩
  · exact hsum
  · change W1c i = 3 / (4 * (1 - W1x N))
    exact hfirst
  · change (3 / 4 : ℝ) ≤ W1c i
    exact hbound

