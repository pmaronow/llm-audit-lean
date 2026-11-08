import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2.P.T9_L9

noncomputable section

open Finset SAP.P005a.WH.W2 SAP.P005a
open scoped BigOperators Matrix

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

theorem design_card_pos (N s : ℕ) (hs : s ≤ N) :
    0 < (design N s).card := by
  apply Finset.card_pos.mpr
  apply Finset.powersetCard_nonempty.mpr
  simpa [design] using hs

theorem count_eq_sum_indicators {N s : ℕ} (w : Fin s → Fin N) (i : Fin N) :
    ((Finset.univ.filter (fun j : Fin s => w j = i)).card : ℝ) =
      ∑ j : Fin s, if w j = i then (1 : ℝ) else 0 := by
  rw [Finset.card_eq_sum_ones]
  simp

theorem weighted_drawSum_expand {N k s : ℕ}
    (X : Fin N → Matrix (Fin k) (Fin k) ℝ) (a : (Fin s → Fin N) → ℝ) :
    (∑ w : Fin s → Fin N, a w • drawSum X w) =
      ∑ i : Fin N,
        (∑ w : Fin s → Fin N, a w *
          ((univ.filter (fun j : Fin s => w j = i)).card : ℝ)) • X i := by
  classical
  have hx (w : Fin s → Fin N) (j : Fin s) :
      X (w j) = ∑ i : Fin N, (if w j = i then (1 : ℝ) else 0) • X i := by
    rw [Finset.sum_eq_single (w j)]
    · simp
    · intro i hi hne
      simp [Ne.symm hne]
    · simp
  calc
    (∑ w : Fin s → Fin N, a w • drawSum X w) =
        ∑ w : Fin s → Fin N, ∑ j : Fin s, ∑ i : Fin N,
          (if w j = i then a w else 0) • X i := by
            apply Finset.sum_congr rfl
            intro w hw
            simp only [drawSum, Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [hx]
            simp only [smul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            by_cases h : w j = i <;> simp [h]
    _ = ∑ i : Fin N, ∑ w : Fin s → Fin N, ∑ j : Fin s,
          (if w j = i then a w else 0) • X i := by
            calc
              _ = ∑ w : Fin s → Fin N, ∑ i : Fin N, ∑ j : Fin s,
                    (if w j = i then a w else 0) • X i := by
                      apply Finset.sum_congr rfl
                      intro w hw
                      exact Finset.sum_comm
              _ = ∑ i : Fin N, ∑ w : Fin s → Fin N, ∑ j : Fin s,
                    (if w j = i then a w else 0) • X i := Finset.sum_comm
    _ = ∑ i : Fin N,
          (∑ w : Fin s → Fin N, a w *
            ((Finset.univ.filter (fun j : Fin s => w j = i)).card : ℝ)) • X i := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              (∑ w : Fin s → Fin N, ∑ j : Fin s,
                  (if w j = i then a w else 0) • X i) =
                  ∑ w : Fin s → Fin N,
                    (∑ j : Fin s, if w j = i then a w else 0) • X i := by
                      apply Finset.sum_congr rfl
                      intro w hw
                      rw [Finset.sum_smul]
              _ = ∑ w : Fin s → Fin N,
                    (a w * ((Finset.univ.filter (fun j : Fin s => w j = i)).card : ℝ)) • X i := by
                      apply Finset.sum_congr rfl
                      intro w hw
                      have hcoeff :
                          (∑ j : Fin s, if w j = i then a w else 0) =
                            a w * ((Finset.univ.filter (fun j : Fin s => w j = i)).card : ℝ) := by
                        rw [count_eq_sum_indicators, Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro j hj
                        by_cases h : w j = i <;> simp [h]
                      rw [hcoeff]
              _ = (∑ w : Fin s → Fin N,
                    a w * ((Finset.univ.filter (fun j : Fin s => w j = i)).card : ℝ)) • X i := by
                      rw [Finset.sum_smul]

end

end SAP.P005a.WH.W2.P.T9_L9

open Finset SAP.P005a.WH.W2 SAP.P005a
open SAP.P005a.WH.W2.P.T9_L9
open scoped BigOperators Matrix

theorem SAP.P005a.WH.W2.T9_L9_proof : SAP.P005a.WH.W2.T9_L9 := by
  intro h7 h8 N k s hN hs X hX f hf
  classical
  let 𝒮 := design N s
  let c : ℝ := (design N s).card
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast design_card_pos N s hs
  have hD : (design N s).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa [design] using hs
  have hweights (S : Finset (Fin N)) (hS : S ∈ design N s) (w : Fin s → Fin N) :
      0 ≤ c * samplingWeight N s S w := by
    exact mul_nonneg (le_of_lt hc) ((h7 N s hN hs).1 S w)
  have hjensen (S : Finset (Fin N)) (hS : S ∈ design N s) :
      f (subsetSum X S) ≤
        ∑ w : Fin s → Fin N, (c * samplingWeight N s S w) * f (drawSum X w) := by
    have htotal :
        (∑ w : Fin s → Fin N, c * samplingWeight N s S w) = 1 := by
      have h := (h8 h7 N s hN hs S hS).1
      change (∑ w : Fin s → Fin N, (design N s).card * samplingWeight N s S w) = 1
      rw [← Finset.mul_sum, h]
      have hc' : (design N s).card ≠ 0 := Nat.ne_of_gt (design_card_pos N s hs)
      simp [div_eq_mul_inv, hc']
    have hbary :
        (∑ w : Fin s → Fin N, (c * samplingWeight N s S w) • drawSum X w) =
          subsetSum X S := by
      rw [weighted_drawSum_expand]
      have hsubset :
          (∑ i : Fin N, (if i ∈ S then (1 : ℝ) else 0) • X i) = subsetSum X S := by
        unfold subsetSum
        rw [show S = Finset.univ.filter (fun i : Fin N => i ∈ S) by ext i; simp]
        rw [Finset.sum_filter]
        simp
      rw [← hsubset]
      apply Finset.sum_congr rfl
      intro i hi
      have hcoord := (h8 h7 N s hN hs S hS).2 i
      change (∑ w : Fin s → Fin N, samplingWeight N s S w *
          ((Finset.univ.filter (fun j : Fin s => w j = i)).card : ℝ)) =
            (if i ∈ S then 1 else 0) / c at hcoord
      have hcoord' :
          (∑ w : Fin s → Fin N, (c * samplingWeight N s S w) *
            ((Finset.univ.filter (fun j : Fin s => w j = i)).card : ℝ)) =
              if i ∈ S then 1 else 0 := by
        calc
          _ = c * (∑ w : Fin s → Fin N, samplingWeight N s S w *
                ((Finset.univ.filter (fun j : Fin s => w j = i)).card : ℝ)) := by
                  calc
                    _ = ∑ w : Fin s → Fin N, c * (samplingWeight N s S w *
                          ((Finset.univ.filter (fun j : Fin s => w j = i)).card : ℝ)) := by
                            apply Finset.sum_congr rfl
                            intro w hw
                            ring
                    _ = c * ∑ w : Fin s → Fin N, samplingWeight N s S w *
                          ((Finset.univ.filter (fun j : Fin s => w j = i)).card : ℝ) := by
                            rw [Finset.mul_sum]
          _ = c * ((if i ∈ S then 1 else 0) / c) := by rw [hcoord]
          _ = if i ∈ S then 1 else 0 := by
                split_ifs <;> field_simp [hc.ne']
      rw [hcoord']
    have hmem (w : Fin s → Fin N) (hw : w ∈ (Finset.univ : Finset (Fin s → Fin N))) :
        drawSum X w ∈ hermitianSet k := by
      change (drawSum X w).IsHermitian
      unfold drawSum
      have hsumHerm (t : Finset (Fin s)) : (∑ j ∈ t, X (w j)).IsHermitian := by
        induction t using Finset.induction_on with
        | empty => simp
        | @insert j t hj ih =>
            simp only [Finset.sum_insert hj]
            exact (hX (w j)).add ih
      simpa [drawSum] using hsumHerm Finset.univ
    have hJ := hf.map_sum_le
      (t := (Finset.univ : Finset (Fin s → Fin N)))
      (w := fun w => c * samplingWeight N s S w)
      (p := fun w => drawSum X w)
      (fun w hw => hweights S hS w)
      htotal
      hmem
    rw [hbary] at hJ
    simpa only [smul_eq_mul] using hJ
  have hsum :
      (∑ S ∈ design N s, f (subsetSum X S)) ≤
        c * ((∑ w : Fin s → Fin N, f (drawSum X w)) / (N : ℝ)^s) := by
    calc
      (∑ S ∈ design N s, f (subsetSum X S)) ≤
          ∑ S ∈ design N s,
            ∑ w : Fin s → Fin N,
              (c * samplingWeight N s S w) * f (drawSum X w) := by
                apply Finset.sum_le_sum
                intro S hS
                exact hjensen S hS
      _ = c * ∑ w : Fin s → Fin N,
            (∑ S ∈ design N s, samplingWeight N s S w) * f (drawSum X w) := by
              calc
                _ = ∑ S ∈ design N s, c *
                    (∑ w : Fin s → Fin N, samplingWeight N s S w * f (drawSum X w)) := by
                      apply Finset.sum_congr rfl
                      intro S hS
                      calc
                        _ = ∑ w : Fin s → Fin N, c *
                              (samplingWeight N s S w * f (drawSum X w)) := by
                                apply Finset.sum_congr rfl
                                intro w hw
                                ring
                        _ = c * ∑ w : Fin s → Fin N,
                              samplingWeight N s S w * f (drawSum X w) := by
                                rw [Finset.mul_sum]
                _ = c * ∑ S ∈ design N s,
                    ∑ w : Fin s → Fin N, samplingWeight N s S w * f (drawSum X w) := by
                      rw [Finset.mul_sum]
                _ = c * ∑ w : Fin s → Fin N,
                    ∑ S ∈ design N s, samplingWeight N s S w * f (drawSum X w) := by
                      congr 1
                      exact Finset.sum_comm
                _ = c * ∑ w : Fin s → Fin N,
                    (∑ S ∈ design N s, samplingWeight N s S w) * f (drawSum X w) := by
                      congr 1
                      apply Finset.sum_congr rfl
                      intro w hw
                      rw [Finset.sum_mul]
      _ = c * ∑ w : Fin s → Fin N,
            ((N : ℝ)^s)⁻¹ * f (drawSum X w) := by
              congr 1
              apply Finset.sum_congr rfl
              intro w hw
              rw [(h7 N s hN hs).2 w]
              simp [div_eq_mul_inv]
      _ = c * ((∑ w : Fin s → Fin N, f (drawSum X w)) / (N : ℝ)^s) := by
            congr 1
            calc
              (∑ w : Fin s → Fin N, ((N : ℝ)^s)⁻¹ * f (drawSum X w)) =
                  ((N : ℝ)^s)⁻¹ * ∑ w : Fin s → Fin N, f (drawSum X w) := by
                    rw [Finset.mul_sum]
              _ = (∑ w : Fin s → Fin N, f (drawSum X w)) / (N : ℝ)^s := by ring
  unfold expectation iidAverage
  dsimp [𝒮, c]
  apply (div_le_iff₀ hc).2
  calc
    (∑ S ∈ design N s, f (subsetSum X S)) ≤
      (design N s).card *
        ((∑ w : Fin s → Fin N, f (drawSum X w)) / (N : ℝ)^s) := hsum
    _ = ((∑ w : Fin s → Fin N, f (drawSum X w)) / (N : ℝ)^s) *
        (design N s).card := by ring
