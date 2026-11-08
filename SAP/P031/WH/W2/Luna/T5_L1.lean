import SAP.P031.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset
open SAP.P031 SAP.P031.WH.W2

noncomputable section
namespace SAP.P031.WH.W2.Luna

private def prefixW2 (Q : Population) : Finset (Fin Q.N) :=
  (Finset.univ : Finset (Fin Q.N)).filter (fun i => i.val < Q.M)

private def assignmentsW2 (Q : Population) : Finset (Finset (Fin Q.N)) :=
  (Finset.univ : Finset (Fin Q.N)).powersetCard Q.M

private def permutationFiberW2 (Q : Population) (s : Finset (Fin Q.N)) :
    Finset (Equiv.Perm (Fin Q.N)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin Q.N))).filter
    (fun π => permutationTreatedW2 Q π = s)

private theorem prefix_eq_map (Q : Population) :
    prefixW2 Q = (Finset.univ : Finset (Fin Q.M)).map
      (Fin.castLEEmb (populationSizesW2 Q).2.2.1) := by
  classical
  ext i
  constructor
  · intro hi
    have hlt : i.val < Q.M := (Finset.mem_filter.mp hi).2
    refine Finset.mem_map.mpr ⟨⟨i.val, hlt⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl
  · intro hi
    obtain ⟨j, _, hji⟩ := Finset.mem_map.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hval : i.val = j.val := (congrArg Fin.val hji).symm
    omega

private theorem prefix_card (Q : Population) : (prefixW2 Q).card = Q.M := by
  rw [prefix_eq_map]
  simp

private theorem permutationTreated_legal (Q : Population)
    (π : Equiv.Perm (Fin Q.N)) :
    permutationTreatedW2 Q π ∈ assignmentsW2 Q := by
  classical
  have hImageCard :
      ((prefixW2 Q).image π).card = (prefixW2 Q).card :=
    Finset.card_image_of_injective _ π.injective
  change (prefixW2 Q).image π ∈ assignmentsW2 Q
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.image_subset_iff.mpr (fun _ _ => Finset.mem_univ _), ?_⟩
  rw [hImageCard, prefix_card]

private theorem permutationTreated_left (Q : Population)
    (σ π : Equiv.Perm (Fin Q.N)) :
    permutationTreatedW2 Q (σ * π) =
      (permutationTreatedW2 Q π).image σ := by
  simp [permutationTreatedW2, Finset.image_image]

private theorem permutationFiber_card_eq (Q : Population)
    (s t : Finset (Fin Q.N))
    (hs : s ∈ assignmentsW2 Q) (ht : t ∈ assignmentsW2 Q) :
    (permutationFiberW2 Q s).card = (permutationFiberW2 Q t).card := by
  classical
  have hsc := (Finset.mem_powersetCard.mp hs).2
  have htc := (Finset.mem_powersetCard.mp ht).2
  obtain ⟨σ, hσmap⟩ := Equiv.Perm.exists_map_finset_eq s t (hsc.trans htc.symm)
  have hσimage : s.image σ = t := by
    simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using hσmap
  have hσinvimage : t.image (σ⁻¹ : Equiv.Perm (Fin Q.N)) = s := by
    calc
      t.image (σ⁻¹ : Equiv.Perm (Fin Q.N)) =
          (s.image σ).image (σ⁻¹ : Equiv.Perm (Fin Q.N)) := by rw [hσimage]
      _ = s := by simp [Finset.image_image]
  let g : Equiv.Perm (Fin Q.N) → Equiv.Perm (Fin Q.N) := fun π => σ * π
  have hgInjective : Function.Injective g := by
    intro π ρ h
    have := congrArg (fun τ : Equiv.Perm (Fin Q.N) => σ⁻¹ * τ) h
    simpa [g, mul_assoc] using this
  have hgImage : (permutationFiberW2 Q s).image g = permutationFiberW2 Q t := by
    ext ρ
    constructor
    · intro hρ
      obtain ⟨π, hπ, rfl⟩ := Finset.mem_image.mp hρ
      have hπ' := (Finset.mem_filter.mp hπ).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [permutationTreated_left, hπ', hσimage]
    · intro hρ
      have hρ' := (Finset.mem_filter.mp hρ).2
      refine Finset.mem_image.mpr ⟨σ⁻¹ * ρ, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [permutationTreated_left, hρ', hσinvimage]
      · simp [g, mul_assoc]
  rw [← hgImage, Finset.card_image_of_injective _ hgInjective]

theorem T5_L1_solution : T5_L1 := by
  classical
  intro Q f
  let A := assignmentsW2 Q
  let U := prefixW2 Q
  let C := (permutationFiberW2 Q U).card
  have hU : U ∈ A := by
    change U ∈ assignmentsW2 Q
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    exact prefix_card Q
  have hCount : ∀ s ∈ A, (permutationFiberW2 Q s).card = C := by
    intro s hs
    exact permutationFiber_card_eq Q s U hs hU
  have hMaps : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin Q.N))),
      permutationTreatedW2 Q π ∈ A := by
    intro π _
    exact permutationTreated_legal Q π
  have hSumFiber :
      (∑ π : Equiv.Perm (Fin Q.N), f (permutationTreatedW2 Q π)) =
        ∑ s ∈ A, ∑ π ∈ permutationFiberW2 Q s,
          f (permutationTreatedW2 Q π) := by
    symm
    simpa [A, permutationFiberW2] using
      (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (Equiv.Perm (Fin Q.N))))
        (t := A) (g := permutationTreatedW2 Q)
        (fun π _ => hMaps π (Finset.mem_univ _))
        (fun π => f (permutationTreatedW2 Q π)))
  have hInner (s : Finset (Fin Q.N)) (hs : s ∈ A) :
      (∑ π ∈ permutationFiberW2 Q s, f (permutationTreatedW2 Q π)) =
        (permutationFiberW2 Q s).card * f s := by
    have hval : ∀ π ∈ permutationFiberW2 Q s,
        f (permutationTreatedW2 Q π) = f s := by
      intro π hπ
      exact congrArg f (Finset.mem_filter.mp hπ).2
    calc
      _ = ∑ π ∈ permutationFiberW2 Q s, f s := by
        apply Finset.sum_congr rfl
        intro π hπ
        exact hval π hπ
      _ = _ := by simp
  have hSum :
      (∑ π : Equiv.Perm (Fin Q.N), f (permutationTreatedW2 Q π)) =
        (C : ℝ) * (∑ s ∈ A, f s) := by
    rw [hSumFiber]
    calc
      (∑ s ∈ A, ∑ π ∈ permutationFiberW2 Q s,
          f (permutationTreatedW2 Q π)) = ∑ s ∈ A, (C : ℝ) * f s := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [hInner s hs, hCount s hs]
      _ = (C : ℝ) * (∑ s ∈ A, f s) := by rw [Finset.mul_sum]
  have hCardPartition :
      Fintype.card (Equiv.Perm (Fin Q.N)) =
        ∑ s ∈ A, (permutationFiberW2 Q s).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Equiv.Perm (Fin Q.N))))
      (t := A) (f := permutationTreatedW2 Q)
      (fun π _ => hMaps π (Finset.mem_univ _))
    simpa [A, permutationFiberW2] using h
  have hCardPerm :
      Fintype.card (Equiv.Perm (Fin Q.N)) = A.card * C := by
    rw [hCardPartition]
    calc
      (∑ s ∈ A, (permutationFiberW2 Q s).card) = ∑ s ∈ A, C := by
        apply Finset.sum_congr rfl
        intro s hs
        exact hCount s hs
      _ = A.card * C := by simp
  have hCposNat : 0 < C := by
    apply Finset.card_pos.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp [permutationFiberW2, U, prefixW2, permutationTreatedW2]
  have hAposNat : 0 < A.card := Finset.card_pos.mpr ⟨U, hU⟩
  have hCpos : (C : ℝ) ≠ 0 := by exact_mod_cast hCposNat.ne'
  have hApos : (A.card : ℝ) ≠ 0 := by exact_mod_cast hAposNat.ne'
  have hCardPermReal : (Fintype.card (Equiv.Perm (Fin Q.N)) : ℝ) =
      (C : ℝ) * (A.card : ℝ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using hCardPerm)
  change (∑ s ∈ A, f s) / (A.card : ℝ) =
    (∑ π : Equiv.Perm (Fin Q.N), f (permutationTreatedW2 Q π)) /
      (Fintype.card (Equiv.Perm (Fin Q.N)) : ℝ)
  rw [hSum, hCardPermReal]
  field_simp [hCpos, hApos]
  <;> ring

example : T5_L1 := T5_L1_solution

#print axioms T5_L1_solution

end SAP.P031.WH.W2.Luna
end
