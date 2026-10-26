import AronowAudit.P016.P016_Interference
import Mathlib.Order.Interval.Finset.Fin

/-! KS prefix and raw-separation helpers. -/

namespace AronowAudit.P016.Wave1

open scoped BigOperators
open Finset MeasureTheory

private abbrev t7_y : Outcome 8 := fun i => i.val

private theorem t7_sizes (z : Balanced 8 4) (g : Bool) : groupSize z.val g = 4 := by
  have h := group_sizes z.val
  have hz := z.property
  cases g <;> simp_all

private def t7_count (z : Assignment 8) (g : Bool) (i : Fin 8) : ℕ :=
  ((Finset.Iic i).filter (fun j => z j = g)).card

private theorem t7_group_card (z : Assignment 8) (g : Bool) :
    (Finset.univ.filter (fun j => z j = g)).card = groupSize z g := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

private theorem t7_count_le (z : Balanced 8 4) (g : Bool) (i : Fin 8) :
    t7_count z.val g i ≤ 4 := by
  calc
    t7_count z.val g i ≤ (Finset.univ.filter (fun j => z.val j = g)).card := by
      apply Finset.card_le_card
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩
    _ = 4 := (t7_group_card z.val g).trans (t7_sizes z g)

private theorem t7_count_partition (z : Assignment 8) (g : Bool) (i : Fin 8) :
    t7_count z g i + t7_count z (!g) i = i.val + 1 := by
  have hb : ∀ j, (z j = !g) ↔ ¬ z j = g := by
    intro j
    cases z j <;> cases g <;> decide
  simp only [t7_count, hb]
  rw [Finset.card_filter_add_card_filter_not, Fin.card_Iic]

private theorem t7_ecdf_prefix (z : Balanced 8 4) (g : Bool) (i : Fin 8) :
    ecdf t7_y z.val g (t7_y i) = (t7_count z.val g i : ℝ) / 4 := by
  rw [ecdf, t7_sizes]
  congr 1
  rw [← Finset.sum_filter]
  have hs : Finset.univ.filter (fun j => z.val j = g ∧ t7_y j ≤ t7_y i) =
      (Finset.Iic i).filter (fun j => z.val j = g) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic,
      t7_y, Nat.cast_le, Fin.le_iff_val_le_val]
    exact and_comm
  rw [hs]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, t7_count]

private theorem t7_prefix_forces (z : Balanced 8 4) (g : Bool) (i : Fin 8)
    (hfull : t7_count z.val g i = 4) (hempty : t7_count z.val (!g) i = 0) :
    ∀ j : Fin 8, z.val j = g ↔ j.val < 4 := by
  have hi := t7_count_partition z.val g i
  rw [hfull, hempty] at hi
  have hiv : i.val = 3 := by omega
  have hno : ∀ j ∈ Finset.Iic i, z.val j = g := by
    intro j hj
    have he := Finset.card_filter_eq_zero_iff.mp hempty j hj
    cases g <;> cases h : z.val j <;> simp_all
  have heq : Finset.Iic i = Finset.univ.filter (fun j => z.val j = g) := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hno j hj⟩
    · rw [t7_group_card, t7_sizes, Fin.card_Iic, hiv]
  intro j
  have hm := congrArg (fun s : Finset (Fin 8) => j ∈ s) heq
  simpa [Finset.mem_Iic, Fin.le_iff_val_le_val, hiv, Nat.lt_succ_iff] using hm.symm

private def t7_extreme (g : Bool) : Balanced 8 4 :=
  ⟨fun j => if j.val < 4 then g else !g, by
    cases g <;> decide⟩

private theorem t7_prefix_extreme (z : Balanced 8 4) (g : Bool) (i : Fin 8)
    (hfull : t7_count z.val g i = 4) (hempty : t7_count z.val (!g) i = 0) :
    z = t7_extreme g := by
  have hf := t7_prefix_forces z g i hfull hempty
  apply Subtype.ext
  funext j
  change z.val j = if j.val < 4 then g else !g
  by_cases hj : j.val < 4
  · simp only [hj, ↓reduceIte]
    exact (hf j).mpr hj
  · simp only [hj, ↓reduceIte]
    have hn := mt (hf j).mp hj
    cases g <;> cases h : z.val j <;> simp_all

private theorem t7_prefix_gap (z : Balanced 8 4) (g : Bool)
    (hz : z ≠ t7_extreme g) (i : Fin 8) :
    (t7_count z.val g i : ℝ) / 4 - (t7_count z.val (!g) i : ℝ) / 4 ≤ 3/4 := by
  have ha := t7_count_le z g i
  have hb := t7_count_le z (!g) i
  have hgap : t7_count z.val g i ≤ 3 ∨ 1 ≤ t7_count z.val (!g) i := by
    by_contra h
    have haf : t7_count z.val g i = 4 := by omega
    have hbf : t7_count z.val (!g) i = 0 := by omega
    exact hz (t7_prefix_extreme z g i haf hbf)
  rcases hgap with h | h
  · have hr : (t7_count z.val g i : ℝ) ≤ 3 := by exact_mod_cast h
    have hn : (0 : ℝ) ≤ t7_count z.val (!g) i := by positivity
    linarith
  · have hr : (1 : ℝ) ≤ t7_count z.val (!g) i := by exact_mod_cast h
    have har : (t7_count z.val g i : ℝ) ≤ 4 := by exact_mod_cast ha
    linarith

private theorem t7_stats_le (u : Outcome 8) (z : Balanced 8 4) :
    signedKS u z.val ≤ 1 ∧ ks u z.val ≤ 1 := by
  have hb (i : Fin 8) :
      ecdf u z.val true (u i) - ecdf u z.val false (u i) ≤ 1 ∧
      |ecdf u z.val true (u i) - ecdf u z.val false (u i)| ≤ 1 := by
    have ht := ecdf_range u z.val true (u i) (by rw [t7_sizes]; decide)
    have hf := ecdf_range u z.val false (u i) (by rw [t7_sizes]; decide)
    exact ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  constructor
  · apply fold_max_le _ 1 (by norm_num)
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (hb i).1
  · apply fold_max_le _ 1 (by norm_num)
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (hb i).2

private theorem t7_adjusted_gap (z : Balanced 8 4) :
    (z ≠ t7_extreme true → signedKS t7_y z.val ≤ 3/4) ∧
    (z ≠ t7_extreme true → z ≠ t7_extreme false → ks t7_y z.val ≤ 3/4) := by
  constructor
  · intro hz
    apply fold_max_le _ (3/4) (by norm_num)
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    rw [t7_ecdf_prefix, t7_ecdf_prefix]
    exact t7_prefix_gap z true hz i
  · intro hz hz'
    apply fold_max_le _ (3/4) (by norm_num)
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    rw [t7_ecdf_prefix, t7_ecdf_prefix]
    apply abs_le.mpr
    have hp := t7_prefix_gap z true hz i
    have hn := t7_prefix_gap z false hz' i
    simp only [Bool.not_false] at hn
    exact ⟨by linarith, hp⟩

private theorem t7_raw_separation (z : Balanced 8 4) :
    signedKS (additiveGenerate t7_y z.val (-100)) z.val = 1 ∧
    ks (additiveGenerate t7_y z.val (-100)) z.val = 1 := by
  classical
  let G := Finset.univ.filter (fun j => z.val j = true)
  have hcard : G.card = 4 := (t7_group_card _ _).trans (t7_sizes _ _)
  have hne : G.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi, hmax⟩ := G.exists_max_image (fun j => j.val) hne
  have hit : z.val i = true := (Finset.mem_filter.mp hi).2
  let u := additiveGenerate t7_y z.val (-100)
  have hCDF : ecdf u z.val true (u i) = 1 ∧ ecdf u z.val false (u i) = 0 := by
    have ht (j : Fin 8) : (z.val j = true ∧ u j ≤ u i) ↔ z.val j = true := by
      constructor
      · exact And.left
      · intro hj
        refine ⟨hj, ?_⟩
        have hjle := hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
        dsimp [u, additiveGenerate, t7_y, bit]
        simp only [hit, hj, ↓reduceIte]
        have hr : (j.val : ℝ) ≤ i.val := by exact_mod_cast hjle
        linarith
    have hf (j : Fin 8) : ¬ (z.val j = false ∧ u j ≤ u i) := by
      rintro ⟨hj, hle⟩
      have hj0 : (0 : ℝ) ≤ j.val := by positivity
      have hi7 : (i.val : ℝ) ≤ 7 := by exact_mod_cast (show i.val ≤ 7 by omega)
      dsimp [u, additiveGenerate, t7_y, bit] at hle
      simp only [hit, hj, Bool.false_eq_true, ↓reduceIte] at hle
      linarith
    constructor
    · rw [ecdf, t7_sizes]
      simp only [ht]
      have hc : (∑ j, if z.val j = true then (1 : ℝ) else 0) = 4 := by
        exact_mod_cast (t7_sizes z true)
      rw [hc]
      norm_num
    · simp [ecdf, hf]
  have hmem : ecdf u z.val true (u i) - ecdf u z.val false (u i) ∈
      List.ofFn (fun j => ecdf u z.val true (u j) - ecdf u z.val false (u j)) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  have hs := le_fold_max _ _ hmem
  have hd := le_fold_max
    (List.ofFn fun j => |ecdf u z.val true (u j) - ecdf u z.val false (u j)|)
    _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hu := t7_stats_le u z
  change signedKS u z.val = 1 ∧ ks u z.val = 1
  have hs' : 1 ≤ signedKS u z.val := by simpa [signedKS, hCDF] using hs
  have hd' : 1 ≤ ks u z.val := by simpa [ks, hCDF] using hd
  exact ⟨le_antisymm hu.1 hs', le_antisymm hu.2 hd'⟩

private theorem t7_card : Fintype.card (Balanced 8 4) = 70 := by
  rw [balanced_card]
  decide

/-- The two extreme assignments have opposite labels at the first coordinate. -/
private theorem t7_extremes_ne : t7_extreme true ≠ t7_extreme false := by
  intro h
  have h0 := congrArg (fun z : Balanced 8 4 => z.val 0) h
  norm_num [t7_extreme] at h0

/-- Each extreme reaches its appropriate KS bound at the fourth coordinate. -/
private theorem t7_extreme_values :
    signedKS t7_y (t7_extreme true).val = 1 ∧
    ks t7_y (t7_extreme true).val = 1 ∧
    ks t7_y (t7_extreme false).val = 1 := by
  have hCDF (g : Bool) :
      ecdf t7_y (t7_extreme g).val true (t7_y 3) -
        ecdf t7_y (t7_extreme g).val false (t7_y 3) = if g then 1 else -1 := by
    rw [t7_ecdf_prefix, t7_ecdf_prefix]
    have ht : t7_count (t7_extreme g).val true 3 = if g then 4 else 0 := by
      cases g <;> decide
    have hf : t7_count (t7_extreme g).val false 3 = if g then 0 else 4 := by
      cases g <;> decide
    rw [ht, hf]
    cases g <;> norm_num
  have hs : 1 ≤ signedKS t7_y (t7_extreme true).val := by
    have h := le_fold_max
      (List.ofFn fun j => ecdf t7_y (t7_extreme true).val true (t7_y j) -
        ecdf t7_y (t7_extreme true).val false (t7_y j))
      _ (List.mem_ofFn.mpr ⟨3, rfl⟩)
    change (ecdf t7_y (t7_extreme true).val true (t7_y 3) -
      ecdf t7_y (t7_extreme true).val false (t7_y 3)) ≤
        signedKS t7_y (t7_extreme true).val at h
    rw [hCDF] at h
    exact h
  have hd (g : Bool) : 1 ≤ ks t7_y (t7_extreme g).val := by
    have h := le_fold_max
      (List.ofFn fun j => |ecdf t7_y (t7_extreme g).val true (t7_y j) -
        ecdf t7_y (t7_extreme g).val false (t7_y j)|)
      _ (List.mem_ofFn.mpr ⟨3, rfl⟩)
    change |ecdf t7_y (t7_extreme g).val true (t7_y 3) -
      ecdf t7_y (t7_extreme g).val false (t7_y 3)| ≤
        ks t7_y (t7_extreme g).val at h
    rw [hCDF] at h
    cases g <;> norm_num only [Bool.false_eq_true, ↓reduceIte, abs_neg, abs_one] at h ⊢
    all_goals exact h
  exact ⟨le_antisymm (t7_stats_le _ _).1 hs,
    le_antisymm (t7_stats_le _ _).2 (hd true),
    le_antisymm (t7_stats_le _ _).2 (hd false)⟩

private theorem t7_signed_extreme (z : Balanced 8 4) :
    1 ≤ signedKS t7_y z.val ↔ z = t7_extreme true := by
  constructor
  · intro hz
    by_contra h
    have hgap := (t7_adjusted_gap z).1 h
    linarith
  · rintro rfl
    exact t7_extreme_values.1.ge

private theorem t7_absolute_extreme (z : Balanced 8 4) :
    1 ≤ ks t7_y z.val ↔ z = t7_extreme true ∨ z = t7_extreme false := by
  constructor
  · intro hz
    by_contra h
    push Not at h
    have hgap := (t7_adjusted_gap z).2 h.1 h.2
    linarith
  · rintro (rfl | rfl)
    · exact t7_extreme_values.2.1.ge
    · exact t7_extreme_values.2.2.ge

/-- Four assignments with their first three coordinates treated. -/
private def t7_reference (k : Fin 4) : Balanced 8 4 :=
  ⟨fun j => decide (j.val < 3 ∨ j.val = 3 + k.val), by
    fin_cases k <;> decide⟩

private theorem t7_reference_injective : Function.Injective t7_reference := by
  intro k l h
  have hkl := congrArg (fun z : Balanced 8 4 => z.val ⟨3 + k.val, by omega⟩) h
  have hnat : 3 + k.val = 3 + l.val := by
    simpa [t7_reference] using hkl.symm
  exact Fin.ext (by omega)

private theorem t7_reference_high (k : Fin 4) :
    (3/4 : ℝ) ≤ signedKS t7_y (t7_reference k).val ∧
    (3/4 : ℝ) ≤ ks t7_y (t7_reference k).val := by
  have hCDF : ecdf t7_y (t7_reference k).val true (t7_y 2) -
      ecdf t7_y (t7_reference k).val false (t7_y 2) = 3/4 := by
    rw [t7_ecdf_prefix, t7_ecdf_prefix]
    have ht : t7_count (t7_reference k).val true 2 = 3 := by
      fin_cases k <;> decide
    have hf : t7_count (t7_reference k).val false 2 = 0 := by
      fin_cases k <;> decide
    rw [ht, hf]
    norm_num
  constructor
  · have h := le_fold_max
      (List.ofFn fun j => ecdf t7_y (t7_reference k).val true (t7_y j) -
        ecdf t7_y (t7_reference k).val false (t7_y j))
      _ (List.mem_ofFn.mpr ⟨2, rfl⟩)
    change (ecdf t7_y (t7_reference k).val true (t7_y 2) -
      ecdf t7_y (t7_reference k).val false (t7_y 2)) ≤
        signedKS t7_y (t7_reference k).val at h
    rw [hCDF] at h
    exact h
  · have h := le_fold_max
      (List.ofFn fun j => |ecdf t7_y (t7_reference k).val true (t7_y j) -
        ecdf t7_y (t7_reference k).val false (t7_y j)|)
      _ (List.mem_ofFn.mpr ⟨2, rfl⟩)
    change |ecdf t7_y (t7_reference k).val true (t7_y 2) -
      ecdf t7_y (t7_reference k).val false (t7_y 2)| ≤
        ks t7_y (t7_reference k).val at h
    rw [hCDF, abs_of_pos (by norm_num : (0 : ℝ) < 3/4)] at h
    exact h

private noncomputable def t7_eventCount {Ω : Type} [Fintype Ω] (E : Ω → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter E).card

private theorem t7_mass_count (E : Balanced 8 4 → Prop) :
    uniformMass (Balanced 8 4) E =
      (t7_eventCount E : ℝ) / 70 := by
  classical
  unfold uniformMass t7_eventCount
  rw [t7_card, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_ofNat]

private theorem t7_mass_congr (E F : Balanced 8 4 → Prop)
    (h : ∀ z, E z ↔ F z) :
    uniformMass (Balanced 8 4) E = uniformMass (Balanced 8 4) F := by
  classical
  unfold uniformMass
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : E z
  · simp only [if_pos hz, if_pos ((h z).mp hz)]
  · have hf : ¬ F z := mt (h z).mpr hz
    simp only [if_neg hz, if_neg hf]

private theorem t7_mass_single (e : Balanced 8 4) :
    uniformMass (Balanced 8 4) (fun z => z = e) = 1/70 := by
  classical
  have hc : t7_eventCount (fun z : Balanced 8 4 => z = e) = 1 := by
    unfold t7_eventCount
    calc
      _ = ({e} : Finset (Balanced 8 4)).card := by
        congr 1
        ext z
        simp
      _ = 1 := Finset.card_singleton e
  rw [t7_mass_count, hc]
  norm_num

private theorem t7_mass_pair :
    uniformMass (Balanced 8 4)
      (fun z => z = t7_extreme true ∨ z = t7_extreme false) = 1/35 := by
  classical
  have hc : t7_eventCount
      (fun z : Balanced 8 4 => z = t7_extreme true ∨ z = t7_extreme false) = 2 := by
    unfold t7_eventCount
    calc
      _ = ({t7_extreme true, t7_extreme false} : Finset (Balanced 8 4)).card := by
        congr 1
        ext z
        simp
      _ = 2 := Finset.card_pair t7_extremes_ne
  rw [t7_mass_count, hc]
  norm_num

private theorem t7_mass_all :
    uniformMass (Balanced 8 4) (fun _ => True) = 1 := by
  classical
  rw [t7_mass_count]
  simp only [t7_eventCount, Finset.filter_true, Finset.card_univ, t7_card]
  norm_num

private theorem t7_mass_four (E : Balanced 8 4 → Prop)
    (h : ∀ k, E (t7_reference k)) :
    (4/70 : ℝ) ≤ uniformMass (Balanced 8 4) E := by
  classical
  have hsub : Finset.univ.image t7_reference ⊆ Finset.univ.filter E := by
    intro z hz
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h k⟩
  have hc : 4 ≤ (Finset.univ.filter E).card := by
    have hi := Finset.card_le_card hsub
    simpa only [Finset.card_image_of_injective _ t7_reference_injective,
      Finset.card_univ, Fintype.card_fin] using hi
  rw [t7_mass_count]
  change (4 : ℝ) / 70 ≤ ((Finset.univ.filter E).card : ℝ) / 70
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by norm_num)

private theorem t7_extreme_masses :
    uniformMass (Balanced 8 4) (fun z => 1 ≤ signedKS t7_y z.val) = 1/70 ∧
    uniformMass (Balanced 8 4) (fun z => 1 ≤ ks t7_y z.val) = 1/35 := by
  constructor
  · rw [t7_mass_congr _ _ t7_signed_extreme]
    exact t7_mass_single _
  · rw [t7_mass_congr _ _ t7_absolute_extreme]
    exact t7_mass_pair

private theorem t7_signed_rejection (z : Balanced 8 4) :
    uniformMass (Balanced 8 4)
      (fun w => signedKS t7_y z.val ≤ signedKS t7_y w.val) < 1/20 ↔
        z = t7_extreme true := by
  constructor
  · intro hz
    by_contra he
    have hgap := (t7_adjusted_gap z).1 he
    have hlow := t7_mass_four
      (fun w => signedKS t7_y z.val ≤ signedKS t7_y w.val)
      (fun k => hgap.trans (t7_reference_high k).1)
    linarith
  · rintro rfl
    rw [t7_extreme_values.1, t7_extreme_masses.1]
    norm_num

private theorem t7_absolute_rejection (z : Balanced 8 4) :
    uniformMass (Balanced 8 4)
      (fun w => ks t7_y z.val ≤ ks t7_y w.val) < 1/20 ↔
        z = t7_extreme true ∨ z = t7_extreme false := by
  constructor
  · intro hz
    by_contra he
    push Not at he
    have hgap := (t7_adjusted_gap z).2 he.1 he.2
    have hlow := t7_mass_four
      (fun w => ks t7_y z.val ≤ ks t7_y w.val)
      (fun k => hgap.trans (t7_reference_high k).2)
    linarith
  · rintro (rfl | rfl)
    · rw [t7_extreme_values.2.1, t7_extreme_masses.2]
      norm_num
    · rw [t7_extreme_values.2.2, t7_extreme_masses.2]
      norm_num

/-- The literal raw-versus-adjusted KS witness, on all seventy assignments. -/
theorem t7_ks_witness_proof :
    let y : Outcome 8 := fun i => i.val
    let sp := fun z : Balanced 8 4 => signedKS y z.val
    let dp := fun z : Balanced 8 4 => ks y z.val
    Fintype.card (Balanced 8 4) = 70 ∧
    (∀ z : Balanced 8 4,
      additiveAdjust (additiveGenerate y z.val (-100)) z.val (-100) = y ∧
      signedKS (additiveGenerate y z.val (-100)) z.val = 1 ∧
      ks (additiveGenerate y z.val (-100)) z.val = 1) ∧
    uniformMass (Balanced 8 4) (fun z => 1 ≤ sp z) = 1/70 ∧
    uniformMass (Balanced 8 4) (fun z => 1 ≤ dp z) = 1/35 ∧
    uniformMass (Balanced 8 4) (fun z =>
      uniformMass (Balanced 8 4) (fun w => sp z ≤ sp w) < 1/20) = 1/70 ∧
    uniformMass (Balanced 8 4) (fun z =>
      uniformMass (Balanced 8 4) (fun w => dp z ≤ dp w) < 1/20) = 1/35 ∧
    uniformMass (Balanced 8 4) (fun z =>
      uniformMass (Balanced 8 4) (fun w =>
        signedKS (additiveGenerate y z.val (-100)) z.val ≤ sp w) < 1/20) = 1 ∧
    uniformMass (Balanced 8 4) (fun z =>
      uniformMass (Balanced 8 4) (fun w =>
        ks (additiveGenerate y z.val (-100)) z.val ≤ dp w) < 1/20) = 1 := by
  dsimp only
  refine ⟨t7_card, ?_, t7_extreme_masses.1, t7_extreme_masses.2, ?_, ?_, ?_, ?_⟩
  · intro z
    exact ⟨(t8_additive_mapping t7_y z.val (-100) (-100)).2, t7_raw_separation z⟩
  · rw [t7_mass_congr _ _ t7_signed_rejection]
    exact t7_mass_single _
  · rw [t7_mass_congr _ _ t7_absolute_rejection]
    exact t7_mass_pair
  · calc
      _ = uniformMass (Balanced 8 4) (fun _ => True) := by
        apply t7_mass_congr
        intro z
        rw [(t7_raw_separation z).1, t7_extreme_masses.1]
        norm_num
      _ = 1 := t7_mass_all
  · calc
      _ = uniformMass (Balanced 8 4) (fun _ => True) := by
        apply t7_mass_congr
        intro z
        rw [(t7_raw_separation z).2, t7_extreme_masses.2]
        norm_num
      _ = 1 := t7_mass_all

end AronowAudit.P016.Wave1
