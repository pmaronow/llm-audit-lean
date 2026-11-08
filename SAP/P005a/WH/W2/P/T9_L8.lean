import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace SAP.P005a.WH.W2.P.T9_L8

noncomputable section

open Finset SAP.P005a SAP.P005a.WH.W2
open scoped BigOperators

private def drawCount {N s : ℕ} (f : Fin s → Fin N) (i : Fin N) : ℕ :=
  (univ.filter fun j : Fin s => f j = i).card

private def mass (N s : ℕ) (S : Finset (Fin N)) : ℝ :=
  ∑ f : Fin s → Fin N, samplingWeight N s S f

private def coordinateMass (N s : ℕ) (S : Finset (Fin N)) (i : Fin N) : ℝ :=
  ∑ f : Fin s → Fin N,
    samplingWeight N s S f * (drawCount f i : ℝ)

private lemma design_card (N s : ℕ) : (design N s).card = Nat.choose N s := by
  simp [design]

private lemma design_card_pos {N s : ℕ} (hs : s ≤ N) : 0 < (design N s).card := by
  rw [design_card]
  exact Nat.choose_pos hs

private lemma weight_perm (N s : ℕ) (σ : Equiv.Perm (Fin N))
    (S : Finset (Fin N)) (f : Fin s → Fin N) :
    samplingWeight N s (S.image σ) (σ ∘ f) = samplingWeight N s S f := by
  classical
  have hcardS : (S.image σ).card = S.card :=
    (Finset.card_image_iff.mpr σ.injective.injOn)
  have hcardD : (univ.image (σ ∘ f)).card = (univ.image f).card := by
    rw [← Finset.image_image]
    exact Finset.card_image_iff.mpr σ.injective.injOn
  have hsubset : (univ.image (σ ∘ f)) ⊆ S.image σ ↔ (univ.image f) ⊆ S := by
    rw [← Finset.image_image, Finset.image_subset_image_iff σ.injective]
  have hdesign : S.image σ ∈ design N s ↔ S ∈ design N s := by
    simp [design, Finset.mem_powersetCard, hcardS]
  unfold samplingWeight
  dsimp only
  by_cases h : S ∈ design N s ∧ univ.image f ⊆ S
  · have h' : S.image σ ∈ design N s ∧ univ.image (σ ∘ f) ⊆ S.image σ :=
      ⟨hdesign.mpr h.1, hsubset.mpr h.2⟩
    rw [if_pos h', if_pos h]
    rw [hcardD]
  · have h' : ¬(S.image σ ∈ design N s ∧ univ.image (σ ∘ f) ⊆ S.image σ) := by
      intro h'
      exact h ⟨hdesign.mp h'.1, hsubset.mp h'.2⟩
    rw [if_neg h', if_neg h]

private lemma exists_perm_image {N s : ℕ} {S T : Finset (Fin N)}
    (hS : S ∈ design N s) (hT : T ∈ design N s) :
    ∃ σ : Equiv.Perm (Fin N), S.image σ = T := by
  classical
  have hs : S.card = s := by simpa [design] using hS
  have ht : T.card = s := by simpa [design] using hT
  have hcard : S.card = T.card := hs.trans ht.symm
  have hcompl : (univ \ S).card = (univ \ T).card := by
    calc
      (univ \ S).card = univ.card - S.card := Finset.card_sdiff_of_subset (subset_univ S)
      _ = univ.card - T.card := by rw [hcard]
      _ = (univ \ T).card := (Finset.card_sdiff_of_subset (subset_univ T)).symm
  let eS : {x : Fin N // x ∈ S} ≃ {x : Fin N // x ∈ T} := Finset.equivOfCardEq hcard
  let eC : {x : Fin N // x ∉ S} ≃ {x : Fin N // x ∉ T} := by
    have e := Finset.equivOfCardEq hcompl
    simpa using e
  let σ : Equiv.Perm (Fin N) := Equiv.subtypeCongr eS eC
  have happly (x : Fin N) (hx : x ∈ S) : σ x = (eS ⟨x, hx⟩).val := by
    simp [σ, Equiv.subtypeCongr, Equiv.sumCompl, hx]
  refine ⟨σ, ?_⟩
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rw [happly x hx]
    exact (eS ⟨x, hx⟩).property
  · intro hy
    obtain ⟨x, hxe⟩ := eS.surjective ⟨y, hy⟩
    refine Finset.mem_image.mpr ⟨x.val, x.property, ?_⟩
    exact (happly x.val x.property).trans (congrArg Subtype.val hxe)

private lemma mass_eq_of_design {N s : ℕ} {S T : Finset (Fin N)}
    (hS : S ∈ design N s) (hT : T ∈ design N s) :
    mass N s S = mass N s T := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_image hS hT
  let e : (Fin s → Fin N) ≃ (Fin s → Fin N) := Equiv.arrowCongr (Equiv.refl _) σ
  have he (f : Fin s → Fin N) : e f = σ ∘ f := by rfl
  unfold mass
  calc
    (∑ f : Fin s → Fin N, samplingWeight N s S f) =
        ∑ f : Fin s → Fin N, samplingWeight N s T (e f) := by
          apply Finset.sum_congr rfl
          intro f hf
          rw [he, ← hσ]
          exact (weight_perm N s σ S f).symm
    _ = ∑ f : Fin s → Fin N, samplingWeight N s T f := by
          simpa only [he] using (Equiv.sum_comp e (fun f => samplingWeight N s T f))

private lemma total_mass_eq_one {N s : ℕ} (hN : 0 < N) (hs : s ≤ N)
    (h7 : SAP.P005a.WH.W2.T9_L7) :
    (∑ S ∈ design N s, mass N s S) = 1 := by
  classical
  have hmarg := (h7 N s hN hs).2
  unfold mass
  rw [Finset.sum_comm]
  calc
    (∑ f : Fin s → Fin N, ∑ S ∈ design N s, samplingWeight N s S f) =
        ∑ f : Fin s → Fin N, 1 / (N : ℝ)^s := by
          apply Finset.sum_congr rfl
          intro f hf
          exact hmarg f
    _ = 1 := by
          simp [one_div, Fintype.card_fin, hN.ne']

private lemma mass_eq_uniform {N s : ℕ} (hN : 0 < N) (hs : s ≤ N)
    (h7 : SAP.P005a.WH.W2.T9_L7) {S : Finset (Fin N)} (hS : S ∈ design N s) :
    mass N s S = 1 / ((design N s).card : ℝ) := by
  have htotal := total_mass_eq_one hN hs h7
  have hconst : (∑ T ∈ design N s, mass N s T) =
      (design N s).card * mass N s S := by
    calc
      (∑ T ∈ design N s, mass N s T) = ∑ T ∈ design N s, mass N s S := by
        apply Finset.sum_congr rfl
        intro T hT
        exact mass_eq_of_design hT hS
      _ = (design N s).card * mass N s S := by simp
  have hcard : (design N s).card ≠ 0 := (design_card_pos hs).ne'
  have hcardR : (design N s).card ≠ 0 := by exact_mod_cast hcard
  rw [hconst] at htotal
  calc
    mass N s S = ((design N s).card : ℝ) * mass N s S / (design N s).card := by
      field_simp
    _ = 1 / (design N s).card := by rw [htotal]

private lemma sum_drawCount {N s : ℕ} (f : Fin s → Fin N) :
    (∑ i : Fin N, drawCount f i) = s := by
  classical
  simpa [drawCount] using
    (Finset.card_eq_sum_card_fiberwise (f := f) (s := (univ : Finset (Fin s)))
      (t := (univ : Finset (Fin N))) (by intro x hx; simp)).symm

private lemma weightedCount_zero_of_not_mem {N s : ℕ} {S : Finset (Fin N)}
    {i : Fin N} (hi : i ∉ S) (f : Fin s → Fin N) :
    samplingWeight N s S f * (drawCount f i : ℝ) = 0 := by
  classical
  unfold samplingWeight
  dsimp only
  split_ifs with h
  · have hempty : (univ.filter fun j : Fin s => f j = i) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      have hji : f j = i := (Finset.mem_filter.mp hj).2
      apply hi
      exact h.2 (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hji⟩)
    simp [drawCount, hempty]
  · simp

private lemma coordinateMass_zero_of_not_mem {N s : ℕ} {S : Finset (Fin N)}
    {i : Fin N} (hi : i ∉ S) : coordinateMass N s S i = 0 := by
  classical
  unfold coordinateMass
  apply Finset.sum_eq_zero
  intro f hf
  exact weightedCount_zero_of_not_mem hi f

private lemma drawCount_swap {N s : ℕ} {i j : Fin N} (hij : i ≠ j)
    (f : Fin s → Fin N) :
    drawCount (Equiv.swap i j ∘ f) i = drawCount f j := by
  classical
  unfold drawCount
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  by_cases hfi : f x = i <;> by_cases hfj : f x = j <;>
    simp [Equiv.swap_apply_def, hfi, hfj, hij, eq_comm]

private lemma coordinateMass_eq_of_mem {N s : ℕ} {S : Finset (Fin N)}
    {i j : Fin N} (hi : i ∈ S) (hj : j ∈ S) :
    coordinateMass N s S i = coordinateMass N s S j := by
  classical
  by_cases hsame : i = j
  · subst j
    rfl
  · let σ : Equiv.Perm (Fin N) := Equiv.swap i j
    have hmaps : ∀ x ∈ S, σ x ∈ S := by
      intro x hx
      by_cases hxi : x = i
      · subst x
        simpa [σ, Equiv.swap_apply_def] using hj
      · by_cases hxj : x = j
        · subst x
          simpa [σ, Equiv.swap_apply_def] using hi
        · simpa [σ, Equiv.swap_apply_def, hxi, hxj] using hx
    have hmap : S.image σ = S := by
      apply Finset.Subset.antisymm
      · exact Finset.image_subset_iff.mpr hmaps
      · intro x hx
        refine Finset.mem_image.mpr ⟨σ x, hmaps x hx, ?_⟩
        simp [σ]
    let e : (Fin s → Fin N) ≃ (Fin s → Fin N) := Equiv.arrowCongr (Equiv.refl _) σ
    have he (f : Fin s → Fin N) : e f = σ ∘ f := by rfl
    unfold coordinateMass
    calc
      (∑ f : Fin s → Fin N,
          samplingWeight N s S f * (drawCount f i : ℝ)) =
          ∑ f : Fin s → Fin N,
            samplingWeight N s S (e f) * (drawCount (e f) i : ℝ) := by
              symm
              exact Equiv.sum_comp e
                (fun f => samplingWeight N s S f * (drawCount f i : ℝ))
      _ = ∑ f : Fin s → Fin N,
            samplingWeight N s S f * (drawCount f j : ℝ) := by
              apply Finset.sum_congr rfl
              intro f hf
              have hw : samplingWeight N s S (σ ∘ f) = samplingWeight N s S f := by
                calc
                  samplingWeight N s S (σ ∘ f) =
                      samplingWeight N s (S.image σ) (σ ∘ f) := by rw [hmap]
                  _ = samplingWeight N s S f := weight_perm N s σ S f
              rw [he f, hw, drawCount_swap hsame]

private lemma coordinate_sum_eq {N s : ℕ} (S : Finset (Fin N)) :
    (∑ i : Fin N, coordinateMass N s S i) =
      (s : ℝ) * mass N s S := by
  classical
  unfold coordinateMass mass
  rw [Finset.sum_comm]
  calc
    (∑ f : Fin s → Fin N, ∑ i : Fin N,
        samplingWeight N s S f * (drawCount f i : ℝ)) =
        ∑ f : Fin s → Fin N,
          samplingWeight N s S f * (∑ i : Fin N, (drawCount f i : ℝ)) := by
            apply Finset.sum_congr rfl
            intro f hf
            rw [Finset.mul_sum]
    _ = ∑ f : Fin s → Fin N, samplingWeight N s S f * (s : ℝ) := by
          apply Finset.sum_congr rfl
          intro f hf
          rw [← Nat.cast_sum, sum_drawCount]
    _ = (s : ℝ) * ∑ f : Fin s → Fin N, samplingWeight N s S f := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro f hf
          ring

private lemma coordinateMass_eq_mass_of_mem {N s : ℕ} {S : Finset (Fin N)}
    (hS : S ∈ design N s)
    {i : Fin N} (hi : i ∈ S) (hs0 : 0 < s) :
    coordinateMass N s S i = mass N s S := by
  have hcardS : S.card = s := by simpa [design] using hS
  have htotal := coordinate_sum_eq (N := N) (s := s) S
  have hsum : (∑ j ∈ S, coordinateMass N s S j) =
      (s : ℝ) * coordinateMass N s S i := by
    calc
      (∑ j ∈ S, coordinateMass N s S j) =
          ∑ j ∈ S, coordinateMass N s S i := by
            apply Finset.sum_congr rfl
            intro j hj
            exact coordinateMass_eq_of_mem hj hi
      _ = (S.card : ℝ) * coordinateMass N s S i := by simp
      _ = (s : ℝ) * coordinateMass N s S i := by rw [hcardS]
  have hzero : ∀ j ∉ S, coordinateMass N s S j = 0 :=
    fun j hj => coordinateMass_zero_of_not_mem hj
  have hsplit : (∑ j : Fin N, coordinateMass N s S j) =
      (∑ j ∈ S, coordinateMass N s S j) := by
    symm
    apply Finset.sum_subset (subset_univ S)
    intro j hj hjS
    exact hzero j hjS
  rw [hsplit, hsum] at htotal
  have hsR : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hs0
  nlinarith

theorem _root_.SAP.P005a.WH.W2.T9_L8_proof : SAP.P005a.WH.W2.T9_L8 := by
  intro h7 N s hN hs S hS
  constructor
  · simpa [mass] using mass_eq_uniform hN hs h7 hS
  · intro i
    by_cases hi : i ∈ S
    · have hcardS : S.card = s := by simpa [design] using hS
      have hs0 : 0 < s := by
        rw [← hcardS]
        exact Finset.card_pos.mpr ⟨i, hi⟩
      calc
        (∑ f : Fin s → Fin N, samplingWeight N s S f *
            ((univ.filter fun j => f j = i).card : ℝ)) =
            coordinateMass N s S i := by rfl
        _ = mass N s S := coordinateMass_eq_mass_of_mem hS hi hs0
        _ = (if i ∈ S then 1 else 0) / ((design N s).card : ℝ) := by
          simpa [hi] using (mass_eq_uniform hN hs h7 hS)
    · have hz := coordinateMass_zero_of_not_mem (N := N) (s := s) hi
      simpa [coordinateMass, drawCount, hi] using hz

end
end SAP.P005a.WH.W2.P.T9_L8
