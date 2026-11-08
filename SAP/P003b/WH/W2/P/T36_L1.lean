import SAP.P003b.WH.W2.Leaves
import AronowAudit.P003.Wave1.Gap.GLP0032B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W2.P.T36_L1

open SAP.P003b.WH.W2
open SAP.P003b.Bridge

theorem bounds_of_possible (o v : Counts) (x : ℤ) (j : ℕ)
    (hp : Possible o v) (he : v.effect = x) (hj : v.a + v.b = j) :
    wholeLineGuards o x j ∧ wholeLineLower o x j ≤ (v.b : ℤ) ∧
      (v.b : ℤ) ≤ wholeLineUpper o x j := by
  have hp' : AronowAudit.P003.Possible (toCounts o) (toCounts v) :=
    (possible_eq o v).2 hp
  have hiff := AronowAudit.P003.Wave1.glp0032b2_possible_iff (toCounts o) (toCounts v)
  rcases hiff.mp hp' with ⟨htD, i, hi0, hia, ha0, hac, hb0, hbd, hab0, hab⟩
  have hi0' : 0 ≤ i := by simpa [toCounts] using hi0
  have hia' : i ≤ o.a := by simpa [toCounts] using hia
  have ha0' : 0 ≤ (v.a : ℤ) - i := by simpa [toCounts] using ha0
  have hac' : (v.a : ℤ) - i ≤ o.c := by simpa [toCounts] using hac
  have hb0' : 0 ≤ (v.b : ℤ) + i - o.a := by simpa [toCounts] using hb0
  have hbd' : (v.b : ℤ) + i - o.a ≤ o.d := by simpa [toCounts] using hbd
  have hab0' : 0 ≤ (v.a : ℤ) + v.c - i - o.c := by simpa [toCounts] using hab0
  have hab' : (v.a : ℤ) + v.c - i - o.c ≤ o.b := by simpa [toCounts] using hab
  have htN : v.a + v.b + v.c + v.d = o.a + o.b + o.c + o.d := by
    simpa [toCounts, AronowAudit.P003.Counts.total] using htD
  have htotal : (v.a : ℤ) + v.b + v.c + v.d =
      (o.a : ℤ) + o.b + o.c + o.d := by exact_mod_cast htN
  have hototal : (o.total : ℤ) = (o.a : ℤ) + o.b + o.c + o.d := by
    simp [SAP.P003b.Counts.total, Nat.cast_add]
  have hline : (v.a : ℤ) + v.b = j := by exact_mod_cast hj
  have heff : (v.b : ℤ) - v.c = x := by
    change (v.b : ℤ) - v.c = x at he
    exact he
  have hraw :
      x + (o.c : ℤ) ≤ j ∧ (o.a : ℤ) ≤ j ∧
      (j : ℤ) + o.b ≤ (o.a : ℤ) + o.b + o.c + o.d ∧
      j ≤ (o.a : ℤ) + x + o.b + o.c ∧
      0 ≤ (v.b : ℤ) ∧ x ≤ v.b ∧
      (j : ℤ) - o.a - o.c ≤ v.b ∧
      (o.a : ℤ) + o.c + x - j ≤ v.b ∧
      (v.b : ℤ) ≤ j ∧ (v.b : ℤ) ≤ (o.a : ℤ) + o.d ∧
      (v.b : ℤ) ≤ o.b + o.c + x ∧
      (v.b : ℤ) ≤ (o.a : ℤ) + o.b + o.c + o.d + x - j := by
    clear hi0 hia ha0 hac hb0 hbd hab0 hab
    omega
  rcases hraw with ⟨hg1,hg2,hg3,hg4,hl1,hl2,hl3,hl4,hu1,hu2,hu3,hu4⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨hg1,hg2,by simpa [hototal] using hg3,hg4⟩
  · change max (max 0 x) (max ((j : ℤ)-o.a-o.c) ((o.a : ℤ)+o.c+x-j)) ≤ _
    simp only [max_le_iff]
    exact ⟨⟨hl1,hl2⟩,⟨hl3,hl4⟩⟩
  · change _ ≤ min (min (j : ℤ) ((o.a : ℤ)+o.d))
      (min ((o.b : ℤ)+o.c+x) ((o.total : ℤ)+x-j))
    simp only [le_min_iff]
    exact ⟨⟨hu1,hu2⟩,⟨hu3,by simpa [hototal] using hu4⟩⟩

theorem possible_of_bounds (o : Counts) (x : ℤ) (j b : ℕ)
    (hg : wholeLineGuards o x j)
    (hl : wholeLineLower o x j ≤ (b : ℤ))
    (hu : (b : ℤ) ≤ wholeLineUpper o x j) :
    Possible o (lineVector o.total j b x) := by
  have hg' :
      x + (o.c : ℤ) ≤ j ∧ (o.a : ℤ) ≤ j ∧
      (j : ℤ) + o.b ≤ o.total ∧ j ≤ (o.a : ℤ) + x + o.b + o.c := by
    simpa [wholeLineGuards] using hg
  have hlo : 0 ≤ (b : ℤ) ∧ x ≤ b ∧
      (j : ℤ) - o.a - o.c ≤ b ∧ (o.a : ℤ) + o.c + x - j ≤ b := by
    simpa [wholeLineLower, max_le_iff] using hl
  have hhi : (b : ℤ) ≤ j ∧ (b : ℤ) ≤ (o.a : ℤ) + o.d ∧
      (b : ℤ) ≤ o.b + o.c + x ∧ (b : ℤ) ≤ o.total + x - j := by
    simpa [wholeLineUpper, le_min_iff] using hu
  rcases hg' with ⟨hg1,hg2,hg3,hg4⟩
  rcases hlo with ⟨hl1,hl2,hl3,hl4⟩
  rcases hhi with ⟨hu1,hu2,hu3,hu4⟩
  clear hg hl hu
  have hb_j : b ≤ j := by
    omega
  have hb_x : x ≤ (b : ℤ) := by
    omega
  have hc0 : 0 ≤ (b : ℤ) - x := by omega
  have hd0 : 0 ≤ (o.total : ℤ) - j - b + x := by
    omega
  have hc : (((b : ℤ) - x).toNat : ℤ) = (b : ℤ) - x := Int.toNat_of_nonneg hc0
  have hd : (((o.total : ℤ) - j - b + x).toNat : ℤ) =
      (o.total : ℤ) - j - b + x := Int.toNat_of_nonneg hd0
  have hd' := hd
  simp only [Counts.total, Nat.cast_add] at hd'
  let v := lineVector o.total j b x
  have ha : (v.a : ℤ) = (j : ℤ) - b := by
    simp [v, lineVector, Nat.cast_sub hb_j]
  have hb : (v.b : ℤ) = b := by simp [v, lineVector]
  have hcv : (v.c : ℤ) = (b : ℤ) - x := by
    simpa [v, lineVector] using hc
  have hdv : (v.d : ℤ) = (o.total : ℤ) - j - b + x := by
    simpa [v, lineVector] using hd
  have hototal : (o.total : ℤ) = (o.a : ℤ) + o.b + o.c + o.d := by
    simp [SAP.P003b.Counts.total, Nat.cast_add]
  have ht : v.total = o.total := by
    apply Nat.cast_injective (R := ℤ)
    change (v.a : ℤ) + v.b + v.c + v.d =
      (o.a : ℤ) + o.b + o.c + o.d
    rw [ha, hb, hcv, hdv]
    rw [hototal]
    omega
  have hv' : AronowAudit.P003.Possible (toCounts o) (toCounts (lineVector o.total j b x)) := by
    apply (AronowAudit.P003.Wave1.glp0032b2_possible_iff (toCounts o) (toCounts v)).mpr
    refine ⟨?_, ?_⟩
    · simpa [toCounts, SAP.P003b.Counts.total, AronowAudit.P003.Counts.total] using ht
    · dsimp [toCounts, lineVector]
      let i : ℤ := max (max 0 ((j : ℤ) - b - o.c))
        (max ((o.a : ℤ) - b) ((j : ℤ) - x - o.c - o.b))
      refine ⟨i, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp [i]; omega
      · dsimp [i]; omega
      · dsimp [i]; omega
      · dsimp [i]; omega
      · dsimp [i]; omega
      · dsimp [i]; omega
      · dsimp [i]; omega
      · dsimp [i]; omega
  exact (possible_eq o (lineVector o.total j b x)).1 hv'

theorem lineVector_line (o : Counts) (x : ℤ) (j b : ℕ)
    (hbj : b ≤ j) (hbx : x ≤ (b : ℤ)) :
    (lineVector o.total j b x).effect = x ∧
      (lineVector o.total j b x).a + (lineVector o.total j b x).b = j := by
  have hc0 : 0 ≤ (b : ℤ) - x := by omega
  have hc : (((b : ℤ) - x).toNat : ℤ) = (b : ℤ) - x := Int.toNat_of_nonneg hc0
  constructor
  · dsimp [Counts.effect, lineVector]
    rw [hc]
    omega
  · dsimp [lineVector]
    omega

theorem lineVector_unique (o v : Counts) (x : ℤ) (j : ℕ)
    (hp : Possible o v) (he : v.effect = x) (hj : v.a + v.b = j) :
    v = lineVector o.total j v.b x := by
  have hpD : AronowAudit.P003.Possible (toCounts o) (toCounts v) :=
    (possible_eq o v).2 hp
  have htD := (AronowAudit.P003.Wave1.glp0032b2_possible_iff
    (toCounts o) (toCounts v)).mp hpD |>.1
  have htN : v.a + v.b + v.c + v.d = o.a + o.b + o.c + o.d := by
    simpa [toCounts, AronowAudit.P003.Counts.total] using htD
  have htotal : (v.a : ℤ) + v.b + v.c + v.d =
      (o.a : ℤ) + o.b + o.c + o.d := by exact_mod_cast htN
  have hline : (v.a : ℤ) + v.b = j := by exact_mod_cast hj
  have heff : (v.b : ℤ) - v.c = x := by
    change (v.b : ℤ) - v.c = x at he
    exact he
  have hbnonneg : 0 ≤ (v.b : ℤ) - x := by omega
  have hdnonneg : 0 ≤ (o.total : ℤ) - j - v.b + x := by
    have hototal : (o.total : ℤ) = (o.a : ℤ) + o.b + o.c + o.d := by
      simp [SAP.P003b.Counts.total, Nat.cast_add]
    rw [hototal]
    omega
  apply Counts.ext
  · change v.a = j - v.b
    omega
  · rfl
  · apply Nat.cast_injective (R := ℤ)
    change (v.c : ℤ) = (((v.b : ℤ) - x).toNat : ℤ)
    rw [Int.toNat_of_nonneg hbnonneg]
    omega
  · apply Nat.cast_injective (R := ℤ)
    change (v.d : ℤ) = (((o.total : ℤ) - j - v.b + x).toNat : ℤ)
    rw [Int.toNat_of_nonneg hdnonneg]
    have hototal : (o.total : ℤ) = (o.a : ℤ) + o.b + o.c + o.d := by
      simp [SAP.P003b.Counts.total, Nat.cast_add]
    rw [hototal]
    omega

theorem first_on_line_spec_local (o : Counts) (x : ℤ) (j : ℕ) (v : Counts)
    (hv : firstOnLine o x j = some v) :
    Possible o v ∧ v.effect = x ∧ v.a + v.b = j ∧
      ∀ u, Possible o u → u.effect = x → u.a + u.b = j → v.b ≤ u.b := by
  have hvD : AronowAudit.P003.firstOnLine (toCounts o) x j = some (toCounts v) := by
    rw [SAP.P003b.Bridge.firstOnLine_eq, hv]
    rfl
  have hs := AronowAudit.P003.first_on_line_spec (toCounts o) x j (toCounts v) hvD
  refine ⟨(possible_eq o v).1 hs.1, ?_, ?_, ?_⟩
  · simpa [toCounts] using hs.2.1
  · simpa [toCounts] using hs.2.2.1
  · intro u hu he huj
    have hm := hs.2.2.2 (toCounts u) ((possible_eq o u).2 hu)
      (by simpa [toCounts] using he) (by simpa [toCounts] using huj)
    simpa [toCounts] using hm

theorem minimumB_some_of_mem (xs : List Counts) (v : Counts) (hv : v ∈ xs) :
    ∃ w, SAP.P003b.minimumB xs = some w := by
  cases xs with
  | nil => simp at hv
  | cons a xs =>
    cases h : SAP.P003b.minimumB xs with
    | none => exact ⟨a, by simp [SAP.P003b.minimumB, h]⟩
    | some u =>
      exact ⟨if a.b ≤ u.b then a else u, by simp [SAP.P003b.minimumB, h]⟩

end SAP.P003b.WH.W2.P.T36_L1

theorem SAP.P003b.WH.W2.T36_L1_proof : SAP.P003b.WH.W2.T36_L1 := by
  classical
  intro o x j
  by_cases hcond : SAP.P003b.wholeLineGuards o x j ∧
      SAP.P003b.wholeLineLower o x j ≤ SAP.P003b.wholeLineUpper o x j
  · let lo := SAP.P003b.wholeLineLower o x j
    have hlo0 : 0 ≤ lo := by
      dsimp [lo, SAP.P003b.wholeLineLower]
      omega
    let b : ℕ := lo.toNat
    have hbcast : (b : ℤ) = lo := by
      dsimp [b]
      exact Int.toNat_of_nonneg hlo0
    have hlow : lo ≤ (b : ℤ) := by rw [hbcast]
    have hup : (b : ℤ) ≤ SAP.P003b.wholeLineUpper o x j := by
      rw [hbcast]
      exact hcond.2
    let vf := SAP.P003b.lineVector o.total j b x
    have hpossible : SAP.P003b.Possible o vf := by
      dsimp [vf]
      exact SAP.P003b.WH.W2.P.T36_L1.possible_of_bounds o x j b hcond.1 hlow hup
    have hline := by
      have hb_j : b ≤ j := by
        have hhi : (b : ℤ) ≤ j ∧ (b : ℤ) ≤ (o.a : ℤ) + o.d ∧
            (b : ℤ) ≤ o.b + o.c + x ∧ (b : ℤ) ≤ o.total + x - j := by
          simpa [SAP.P003b.wholeLineUpper, le_min_iff] using hup
        omega
      have hb_x : x ≤ (b : ℤ) := by
        rw [hbcast]
        dsimp [lo, SAP.P003b.wholeLineLower]
        omega
      exact SAP.P003b.WH.W2.P.T36_L1.lineVector_line o x j b hb_j hb_x
    have hmem : vf ∈ SAP.P003b.lineGroup o x j := by
      apply List.mem_filter.mpr
      exact ⟨hpossible, by simpa using hline⟩
    have hwExists : ∃ w, SAP.P003b.firstOnLine o x j = some w := by
      simpa [SAP.P003b.firstOnLine] using
        (SAP.P003b.WH.W2.P.T36_L1.minimumB_some_of_mem
          (SAP.P003b.lineGroup o x j) vf hmem)
    obtain ⟨w, hw⟩ := hwExists
    have hs := SAP.P003b.WH.W2.P.T36_L1.first_on_line_spec_local o x j w hw
    have hmin := hs.2.2.2 vf hpossible hline.1 hline.2
    have hbounds := SAP.P003b.WH.W2.P.T36_L1.bounds_of_possible o w x j
      hs.1 hs.2.1 hs.2.2.1
    have hbeq : w.b = b := by
      have hlo_w := hbounds.2.1
      have hvb : (vf.b : ℤ) = lo := by
        dsimp [vf, SAP.P003b.lineVector]
        exact hbcast
      have hmcast : (w.b : ℤ) ≤ (vf.b : ℤ) := by exact_mod_cast hmin
      omega
    have hvec : w = vf := by
      have huniq := SAP.P003b.WH.W2.P.T36_L1.lineVector_unique o w x j
        hs.1 hs.2.1 hs.2.2.1
      rw [hbeq] at huniq
      simpa [vf] using huniq
    have hfirst : SAP.P003b.firstOnLine o x j = some vf := by
      rw [hw, hvec]
    have hfast : SAP.P003b.wholeFastBase o x j = some vf := by
      simp [SAP.P003b.wholeFastBase, hcond, vf, b, lo]
    rw [hfast, hfirst]
  · have hnone : SAP.P003b.firstOnLine o x j = none := by
      cases h : SAP.P003b.firstOnLine o x j with
      | none => rfl
      | some v =>
        have hs := SAP.P003b.WH.W2.P.T36_L1.first_on_line_spec_local o x j v h
        have hbounds := SAP.P003b.WH.W2.P.T36_L1.bounds_of_possible o v x j
          hs.1 hs.2.1 hs.2.2.1
        have hc : SAP.P003b.wholeLineGuards o x j ∧
            SAP.P003b.wholeLineLower o x j ≤ SAP.P003b.wholeLineUpper o x j :=
          ⟨hbounds.1, le_trans hbounds.2.1 hbounds.2.2⟩
        exact (hcond hc).elim
    simp [SAP.P003b.wholeFastBase, hcond, hnone]
