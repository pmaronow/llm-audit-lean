import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P005a.WH.W2.P.T9_L7

noncomputable section
open Finset SAP.P005a.Bridge
open scoped BigOperators

end
end SAP.P005a.WH.W2.P.T9_L7

open Finset SAP.P005a.Bridge
open scoped BigOperators

theorem SAP.P005a.WH.W2.T9_L7_proof : SAP.P005a.WH.W2.T9_L7 := by
  classical
  intro N s hN hs
  constructor
  · intro S f
    let D : Finset (Fin N) := univ.image f
    have hD : D.card ≤ s := by
      dsimp [D]
      calc
        (univ.image f).card ≤ (univ : Finset (Fin s)).card := Finset.card_image_le
        _ = s := by simp
    have hchoose : 0 < (N - D.card).choose (s - D.card) := by
      apply Nat.choose_pos
      exact Nat.sub_le_sub_right hs D.card
    have hpow : 0 < (N : ℝ)^s := pow_pos (by exact_mod_cast hN) _
    have hq : 0 < ((N - D.card).choose (s - D.card) : ℝ) := by
      exact_mod_cast hchoose
    change 0 ≤ (if S ∈ design N s ∧ univ.image f ⊆ S then
      1 / ((N : ℝ)^s * ((N - D.card).choose (s - D.card) : ℝ)) else 0)
    split_ifs <;> positivity
  · intro f
    let D : Finset (Fin N) := univ.image f
    have hD : D.card ≤ s := by
      dsimp [D]
      calc
        (univ.image f).card ≤ (univ : Finset (Fin s)).card := Finset.card_image_le
        _ = s := by simp
    have hDsub : D ⊆ (univ : Finset (Fin N)) := Finset.subset_univ _
    have hcountNat : ((design N s).filter (fun S : Finset (Fin N) => D ⊆ S)).card =
        (N - D.card).choose (s - D.card) := by
      simpa [SAP.P005a.design, Finset.card_univ] using
        (Finset.card_filter_powersetCard_subset D (univ : Finset (Fin N)) s hDsub hD)
    have hchoose : 0 < (N - D.card).choose (s - D.card) := by
      apply Nat.choose_pos
      exact Nat.sub_le_sub_right hs D.card
    have hp : 0 < (N : ℝ)^s := pow_pos (by exact_mod_cast hN) _
    have hq : 0 < ((N - D.card).choose (s - D.card) : ℝ) := by
      exact_mod_cast hchoose
    let p : ℝ := (N : ℝ)^s
    let q : ℝ := ((N - D.card).choose (s - D.card) : ℝ)
    let c : ℝ := 1 / (p * q)
    let A : Finset (Finset (Fin N)) :=
      (design N s).filter (fun S => D ⊆ S)
    have hsum : (∑ S ∈ design N s, samplingWeight N s S f) = (A.card : ℝ) * c := by
      calc
        (∑ S ∈ design N s, samplingWeight N s S f) =
            ∑ S ∈ design N s, if D ⊆ S then c else 0 := by
          apply Finset.sum_congr rfl
          intro S hS
          simp [samplingWeight, D, p, q, c, hS]
        _ = ∑ S ∈ A, c := by
          simp only [A]
          rw [← Finset.sum_filter]
        _ = (A.card : ℝ) * c := by simp [Finset.sum_const, nsmul_eq_mul]
    have hcard : (A.card : ℝ) = q := by
      dsimp [A, q]
      exact_mod_cast hcountNat
    change (∑ S ∈ design N s, samplingWeight N s S f) = 1 / (N : ℝ)^s
    rw [hsum, hcard]
    dsimp [c, p]
    field_simp
    exact mul_inv_cancel₀ (ne_of_gt hq)

