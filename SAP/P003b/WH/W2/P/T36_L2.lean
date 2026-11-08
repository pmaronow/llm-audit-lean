import SAP.P003b.WH.W2.Leaves
import AronowAudit.P003.Wave1.Gap.GLP0032B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W2.P.T36_L2

open SAP.P003b.Bridge
open SAP.P003b.WH.W2

set_option maxHeartbeats 1000000

lemma possible_on_line_iff (o w : Counts) (x : ℤ) (j : ℕ) :
    Possible o w ∧ w.effect = x ∧ w.a + w.b = j ↔
      w.total = o.total ∧ w.effect = x ∧ w.a + w.b = j ∧
        wholeLineGuards o x j ∧
        wholeLineLower o x j ≤ (w.b : ℤ) ∧
        (w.b : ℤ) ≤ wholeLineUpper o x j := by
  constructor
  · rintro ⟨hw, hx, hj⟩
    have hiff := AronowAudit.P003.Wave1.glp0032b2_possible_iff (toCounts o) (toCounts w)
    have hposs : AronowAudit.P003.Possible (toCounts o) (toCounts w) :=
      (possible_eq o w).2 hw
    obtain ⟨ht, i, hi⟩ := hiff.mp hposs
    have ht' : w.total = o.total := by
      simpa [SAP.P003b.Bridge.toCounts, AronowAudit.P003.Counts.total,
        SAP.P003b.Counts.total] using ht
    have htInt : (w.a : ℤ) + w.b + w.c + w.d =
        (o.a : ℤ) + o.b + o.c + o.d := by
      have h := ht'
      dsimp [SAP.P003b.Counts.total] at h
      exact_mod_cast h
    have hi' : 0 ≤ i ∧ i ≤ o.a ∧
      0 ≤ (w.a : ℤ) - i ∧ (w.a : ℤ) - i ≤ o.c ∧
      0 ≤ (w.b : ℤ) + i - o.a ∧ (w.b : ℤ) + i - o.a ≤ o.d ∧
      0 ≤ (w.a : ℤ) + (w.c : ℤ) - i - o.c ∧
        (w.a : ℤ) + (w.c : ℤ) - i - o.c ≤ o.b := by
      simpa [SAP.P003b.Bridge.toCounts] using hi
    clear ht hi hposs hiff
    have hx' : (w.b : ℤ) - w.c = x := by simpa [SAP.P003b.Counts.effect] using hx
    have hj' : (w.a + w.b : ℕ) = j := hj
    rcases hi' with ⟨hi0, hiA, ha0, hac, hb0, hbd, hac0, hab⟩
    refine ⟨ht', hx, hj, ?_, ?_, ?_⟩
    · unfold wholeLineGuards SAP.P003b.Counts.total
      omega
    · unfold wholeLineLower
      rw [max_le_iff, max_le_iff, max_le_iff]
      omega
    · unfold wholeLineUpper SAP.P003b.Counts.total
      rw [le_min_iff, le_min_iff, le_min_iff]
      omega
  · rintro ⟨ht, hx, hj, hg, hlo, hhi⟩
    have hwiff := AronowAudit.P003.Wave1.glp0032b2_possible_iff (toCounts o) (toCounts w)
    apply And.intro
    · apply (possible_eq o w).1
      apply hwiff.mpr
      refine ⟨ht, ?_⟩
      dsimp [SAP.P003b.Bridge.toCounts, AronowAudit.P003.Counts.total,
        SAP.P003b.Counts.total] at *
      let i : ℤ := max (max 0 ((w.a : ℤ) - o.c))
        (max ((o.a : ℤ) - w.b) ((w.a : ℤ) + w.c - o.c - o.b))
      refine ⟨i, ?_⟩
      have hgt := hg
      unfold wholeLineGuards at hgt
      unfold wholeLineLower at hlo
      unfold wholeLineUpper at hhi
      dsimp [SAP.P003b.Counts.effect, SAP.P003b.Counts.total] at hx hj ht hgt hlo hhi
      rcases hgt with ⟨hguard1, hguard2, hguard3, hguard4⟩
      dsimp [i]
      simp only [max_def, min_def] at *
      split_ifs <;> omega
    · exact ⟨hx, hj⟩

end SAP.P003b.WH.W2.P.T36_L2

open SAP.P003b.Bridge
open SAP.P003b
open SAP.P003b.WH.W2
open SAP.P003b.WH.W2.P.T36_L2

theorem SAP.P003b.WH.W2.T36_L2_proof : SAP.P003b.WH.W2.T36_L2 := by
  intro o v x j hv
  have hv' : AronowAudit.P003.firstOnLine (toCounts o) x j = some (toCounts v) := by
    rw [firstOnLine_eq, hv]
    rfl
  have hs := AronowAudit.P003.first_on_line_spec (toCounts o) x j (toCounts v) hv'
  have hvpos : Possible o v := (possible_eq o v).1 hs.1
  have hveff0 : v.effect = x := by
    simpa [SAP.P003b.Bridge.toCounts, AronowAudit.P003.Counts.effect,
      SAP.P003b.Counts.effect] using hs.2.1
  have hvsum0 : v.a + v.b = j := by
    simpa [SAP.P003b.Bridge.toCounts] using hs.2.2.1
  rcases (possible_on_line_iff o v x j).1 ⟨hvpos, hveff0, hvsum0⟩ with
    ⟨hvtotal, hveff, hvsum, hvguards, hvlo, hvhi⟩
  let U := wholeLineUpper o x j
  let M := U.toNat - v.b
  have hU_nonneg : 0 ≤ U := by
    have hvb : (v.b : ℤ) ≤ U := by simpa [U] using hvhi
    exact le_trans (by exact_mod_cast (Nat.zero_le v.b)) hvb
  have hU_nat : (U.toNat : ℤ) = U := Int.toNat_of_nonneg hU_nonneg
  have htotalInt : (v.a : ℤ) + v.b + v.c + v.d =
      (o.a : ℤ) + o.b + o.c + o.d := by
    have h := hvtotal
    dsimp [SAP.P003b.Counts.total] at h
    exact_mod_cast h
  have hjle : j ≤ o.total := by
    rw [← hvtotal]
    dsimp [SAP.P003b.Counts.total]
    rw [← hvsum0]
    omega
  have hUle : U ≤ (j : ℤ) := by
    dsimp [U, wholeLineUpper]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hMle : M ≤ o.total := by
    have hn : U.toNat ≤ j := by
      have hh : (U.toNat : ℤ) ≤ (j : ℤ) := by rw [hU_nat]; exact hUle
      exact_mod_cast hh
    dsimp [M]
    omega
  have hvA : (v.a : ℤ) = (j : ℤ) - v.b := by
    have := hvsum0
    omega
  have hvD : (v.d : ℤ) = (o.total : ℤ) - j - v.b + x := by
    have htot := hvtotal
    have heff := hveff
    dsimp [SAP.P003b.Counts.effect] at heff
    have htotInt := htotalInt
    have hoTotalCast : (o.total : ℤ) = (o.a : ℤ) + o.b + o.c + o.d := by
      simp [SAP.P003b.Counts.total]
    omega
  have hpred (r : ℕ) :
      (r + 1 ≤ v.a ∧ r + 1 ≤ v.d ∧ Possible o (reuseVector v (r + 1))) ↔ r < M := by
    constructor
    · rintro ⟨hra, hrd, hp⟩
      have hreuse : (reuseVector v (r+1)).effect = x ∧
          (reuseVector v (r+1)).a + (reuseVector v (r+1)).b = j := by
        constructor
        · dsimp [reuseVector, Counts.effect] at *
          omega
        · dsimp [reuseVector]
          omega
      have hline := (possible_on_line_iff o (reuseVector v (r+1)) x j).1
        ⟨hp, hreuse.1, hreuse.2⟩
      have hupper := hline.2.2.2.2.2
      dsimp [M]
      have hupper' : ((r + 1 : ℕ) : ℤ) + v.b ≤ U := by
        dsimp [U, reuseVector] at hupper ⊢
        omega
      have hnat : r + 1 ≤ U.toNat := by
        have hh : ((r + 1 : ℕ) : ℤ) ≤ U := by omega
        have hh' : ((r + 1 : ℕ) : ℤ) ≤ (U.toNat : ℤ) := by rw [hU_nat]; exact hh
        exact_mod_cast hh'
      omega
    · intro hr
      have hrNat : r + 1 + v.b ≤ U.toNat := by
        dsimp [M] at hr
        omega
      have hrU : (r + 1 : ℤ) + v.b ≤ U := by
        have hh : ((r + 1 + v.b : ℕ) : ℤ) ≤ (U.toNat : ℤ) := by exact_mod_cast hrNat
        rw [hU_nat] at hh
        simpa [Nat.cast_add, Nat.cast_one] using hh
      have hra : r + 1 ≤ v.a := by
        have h := le_trans hrU hUle
        omega
      have hrd : r + 1 ≤ v.d := by
        have hright : U ≤ (o.total : ℤ) + x - j := by
          dsimp [U, wholeLineUpper]
          exact (min_le_right _ _).trans (min_le_right _ _)
        have h := le_trans hrU hright
        omega
      have hreuse : (reuseVector v (r+1)).effect = x ∧
          (reuseVector v (r+1)).a + (reuseVector v (r+1)).b = j := by
        constructor
        · dsimp [reuseVector, Counts.effect] at *
          omega
        · dsimp [reuseVector]
          omega
      have htot : (reuseVector v (r+1)).total = o.total := by
        have htot := htotalInt
        dsimp [reuseVector, SAP.P003b.Counts.total] at *
        omega
      have hlo : wholeLineLower o x j ≤ ((reuseVector v (r+1)).b : ℤ) := by
        have h := hvlo
        dsimp [reuseVector] at *
        exact le_trans h (by omega)
      have hhi : ((reuseVector v (r+1)).b : ℤ) ≤ U := by
        dsimp [reuseVector]
        omega
      have hposs := (possible_on_line_iff o (reuseVector v (r+1)) x j).2
        ⟨htot, hreuse.1, hreuse.2, hvguards, hlo, by simpa [U] using hhi⟩ |>.1
      exact ⟨hra, hrd, hposs⟩
  classical
  simp only [SAP.P003b.wholeCostReuse, SAP.P003b.reuseLine, List.filter_map]
  have hpredBool (r : ℕ) :
      decide (r + 1 ≤ v.a ∧ r + 1 ≤ v.d ∧ Possible o (reuseVector v (r + 1))) =
        decide (r < M) := by
    rw [decide_eq_decide]
    exact hpred r
  change List.map (fun k => k + 1) (List.range M) =
    List.map (fun k => k + 1) ((List.range o.total).filter fun r =>
      decide (r + 1 ≤ v.a ∧ r + 1 ≤ v.d ∧ Possible o (reuseVector v (r + 1))))
  simp_rw [hpredBool]
  rw [← List.Ico.zero_bot o.total, List.Ico.filter_lt, Nat.min_eq_right hMle,
    List.Ico.zero_bot]

