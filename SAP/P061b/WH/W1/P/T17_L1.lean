import SAP.P061b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061b.WH.W1.P.T17_L1

open SAP.P061b
open scoped BigOperators Classical

theorem fin2_real_binary (x : Fin 2) :
    ((x.val : ℕ) : ℝ) = 0 ∨ ((x.val : ℕ) : ℝ) = 1 := by
  fin_cases x <;> norm_num

theorem fin2_eq_one_iff (x : Fin 2) :
    ((x.val : ℕ) : ℝ) = 1 ↔ x = 1 := by
  fin_cases x <;> norm_num

theorem fin2_exposure_mask (x : Fin 2) :
    (if ((x.val : ℕ) : ℝ) = 1 then (1 : Fin 2) else 0) = x := by
  fin_cases x <;> norm_num

noncomputable def embed {N : ℕ} {Z : Set (Fin N → ℝ)}
    (hZ : ContainsBinaryCubeW1 Z) (b : Fin N → Fin 2) : Z :=
  ⟨binaryAssignmentW1 b, hZ b⟩

theorem embed_injective {N : ℕ} {Z : Set (Fin N → ℝ)}
    (hZ : ContainsBinaryCubeW1 Z) : Function.Injective (embed hZ) := by
  intro b c h
  funext i
  apply Fin.ext
  have hv := congrFun (congrArg Subtype.val h) i
  simpa [embed, binaryAssignmentW1] using hv

theorem support_binary {N : ℕ} {Z : Set (Fin N → ℝ)}
    {D : AtomicDesign Z} {n : ℕ} (hD : UniformBinaryDesignW1 D n)
    {z : Z} (hz : InSupport D z) :
    (∀ i, z.val i = 0 ∨ z.val i = 1) ∧
      (Finset.univ.filter (fun i => z.val i = 1)).card = n := by
  have hp := hz
  change 0 < D.p z at hp
  rw [hD z] at hp
  split_ifs at hp with h
  · exact h
  · norm_num at hp

theorem support_is_embed {N : ℕ} {Z : Set (Fin N → ℝ)}
    (hZ : ContainsBinaryCubeW1 Z) {D : AtomicDesign Z} {n : ℕ}
    (hD : UniformBinaryDesignW1 D n) {z : Z} (hz : InSupport D z)
    (b : Fin N → Fin 2)
    (hb : exposureMaskW1 coordinateExposureW1 1 z = b) : z = embed hZ b := by
  obtain ⟨hbin, _⟩ := support_binary hD hz
  apply Subtype.ext
  change z.val = binaryAssignmentW1 b
  funext i
  have hb' : b i = if z.val i = 1 then 1 else 0 := by
    have hh := congrFun hb i
    change (if z.val i = 1 then (1 : Fin 2) else 0) = b i at hh
    exact hh.symm
  rcases hbin i with h0 | h1
  · have hb0 : b i = 0 := by simpa [h0] using hb'
    simp [binaryAssignmentW1, h0, hb0]
  · have hb1 : b i = 1 := by simpa [h1] using hb'
    simp [binaryAssignmentW1, h1, hb1]

theorem finite_support {N : ℕ} {Z : Set (Fin N → ℝ)}
    (hZ : ContainsBinaryCubeW1 Z) {D : AtomicDesign Z} {n : ℕ}
    (hD : UniformBinaryDesignW1 D n) : {z : Z | InSupport D z}.Finite := by
  apply (Set.finite_range (embed hZ)).subset
  intro z hz
  have hz' : InSupport D z := hz
  have ⟨hbin, _⟩ := support_binary hD hz'
  let b : Fin N → Fin 2 := fun i => if z.val i = 1 then 1 else 0
  have heq : embed hZ b = z := by
    apply Subtype.ext
    change binaryAssignmentW1 b = z.val
    funext i
    rcases hbin i with h0 | h1
    · simp [b, binaryAssignmentW1, h0]
    · simp [b, binaryAssignmentW1, h1]
  exact ⟨b, heq⟩

theorem mask_event_probability {N : ℕ} {Z : Set (Fin N → ℝ)}
    (hZ : ContainsBinaryCubeW1 Z) {D : AtomicDesign Z} {n : ℕ}
    (hD : UniformBinaryDesignW1 D n) (b : Fin N → Fin 2) :
    eventProbability D (fun z => exposureMaskW1 coordinateExposureW1 1 z = b) =
      if (Finset.univ.filter (fun i => b i = 1)).card = n then
        (Nat.choose N n : ℝ)⁻¹ else 0 := by
  let e := embed hZ b
  have hevent : exposureMaskW1 coordinateExposureW1 1 e = b := by
    change (fun i => if (binaryAssignmentW1 b) i = 1 then (1 : Fin 2) else 0) = b
    funext i
    change (if ((b i).val : ℝ) = 1 then (1 : Fin 2) else 0) = b i
    exact fin2_exposure_mask (b i)
  have hval : ∀ i : Fin N,
      (binaryAssignmentW1 b) i = 0 ∨ (binaryAssignmentW1 b) i = 1 := by
    intro i
    simpa [binaryAssignmentW1] using fin2_real_binary (b i)
  have hfilter :
      Finset.univ.filter (fun i => (binaryAssignmentW1 b) i = 1) =
        Finset.univ.filter (fun i => b i = 1) := by
    apply Finset.filter_congr
    intro i hi
    exact fin2_eq_one_iff (b i)
  calc
    eventProbability D (fun z => exposureMaskW1 coordinateExposureW1 1 z = b) =
        (if exposureMaskW1 coordinateExposureW1 1 e = b then D.p e else 0) := by
      have hs := tsum_eq_single (α := ℝ) (β := Z)
        (L := SummationFilter.unconditional Z)
        (f := fun z : Z =>
          @ite ℝ (exposureMaskW1 coordinateExposureW1 1 z = b)
            (Classical.propDecidable _) (D.p z) 0) e (by
          intro z hne
          by_cases hzmask : exposureMaskW1 coordinateExposureW1 1 z = b
          · by_cases hzpos : InSupport D z
            · exact False.elim (hne (support_is_embed hZ hD hzpos b hzmask))
            · have hp0 : D.p z = 0 := le_antisymm (le_of_not_gt hzpos) (D.nonneg z)
              simp [hzmask, hp0]
          · simp [hzmask])
      simpa [eventProbability, hevent] using hs
    _ = if (Finset.univ.filter (fun i => b i = 1)).card = n then
        (Nat.choose N n : ℝ)⁻¹ else 0 := by
      simp [hevent]
      have hmass : D.p e =
          if (Finset.univ.filter (fun i => b i = 1)).card = n
            then (Nat.choose N n : ℝ)⁻¹ else 0 := by
        have hcond :
            ((∀ i, binaryAssignmentW1 b i = 0 ∨ binaryAssignmentW1 b i = 1) ∧
              (Finset.univ.filter (fun i => binaryAssignmentW1 b i = 1)).card = n) ↔
              (Finset.univ.filter (fun i => b i = 1)).card = n := by
          constructor
          · rintro ⟨_, hc⟩
            simpa only [hfilter] using hc
          · intro hc
            exact ⟨hval, by simpa only [hfilter] using hc⟩
        change D.p ⟨binaryAssignmentW1 b, hZ b⟩ = _
        have hp := hD (⟨binaryAssignmentW1 b, hZ b⟩ : Z)
        change D.p ⟨binaryAssignmentW1 b, hZ b⟩ =
          if (∀ i, binaryAssignmentW1 b i = 0 ∨ binaryAssignmentW1 b i = 1) ∧
            (Finset.univ.filter (fun i => binaryAssignmentW1 b i = 1)).card = n
            then (Nat.choose N n : ℝ)⁻¹ else 0 at hp
        simp only [hcond] at hp
        exact hp
      rw [hmass]

theorem supported_counts {N : ℕ} {Z : Set (Fin N → ℝ)}
    {D : AtomicDesign Z} {n : ℕ} (hn : n < N)
    (hD : UniformBinaryDesignW1 D n) {z : Z} (hz : InSupport D z) :
    (∀ i, coordinateExposureW1 i z = 0 ∨ coordinateExposureW1 i z = 1) ∧
      (Finset.univ.filter (fun i => coordinateExposureW1 i z = 1)).card = n ∧
      (Finset.univ.filter (fun i => coordinateExposureW1 i z = 0)).card = N - n := by
  obtain ⟨hbin, hones⟩ := support_binary hD hz
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun i => z.val i = 0)
  have hfilter :
      Finset.univ.filter (fun i => z.val i ≠ 0) =
        Finset.univ.filter (fun i => z.val i = 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hbin i with h0 | h1
    · simp [h0]
    · simp [h1]
  have hcardfilter := congrArg Finset.card hfilter
  rw [hcardfilter] at hsum
  have hsum' :
      (Finset.univ.filter (fun i => z.val i = 0)).card + n = N := by
    rw [hones] at hsum
    simpa [Fintype.card_fin] using hsum
  refine ⟨?_, hones, ?_⟩
  · intro i
    simpa [coordinateExposureW1] using hbin i
  · have hzcount : (Finset.univ.filter (fun i => z.val i = 0)).card = N - n := by omega
    exact hzcount

end SAP.P061b.WH.W1.P.T17_L1

theorem SAP.P061b.WH.W1.T17_L1_proof : SAP.P061b.WH.W1.T17_L1 := by
  intro N Z D n hZ hn hlt hD
  refine ⟨?_, ?_, ?_⟩
  · exact SAP.P061b.WH.W1.P.T17_L1.finite_support hZ hD
  · intro b
    exact SAP.P061b.WH.W1.P.T17_L1.mask_event_probability hZ hD b
  · intro z hz
    exact SAP.P061b.WH.W1.P.T17_L1.supported_counts hlt hD hz
