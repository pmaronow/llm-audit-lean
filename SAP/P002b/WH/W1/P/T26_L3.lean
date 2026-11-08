import SAP.P002b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P002b.WH.W1.P.T26_L3

open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem probability_congr {n : ℕ} (P : SAP.P002b.Population n)
    {E F : Finset (Fin n) → Prop}
    (h : ∀ S ∈ SAP.P002b.assignments P, E S ↔ F S) :
    SAP.P002b.probability P E = SAP.P002b.probability P F := by
  classical
  unfold SAP.P002b.probability
  have heq : (SAP.P002b.assignments P).filter E =
      (SAP.P002b.assignments P).filter F := by
    ext S
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hS, hE⟩
      exact ⟨hS, (h S hS).mp hE⟩
    · rintro ⟨hS, hF⟩
      exact ⟨hS, (h S hS).mpr hF⟩
  rw [heq]

theorem probability_mono {n : ℕ} (P : SAP.P002b.Population n)
    {E F : Finset (Fin n) → Prop}
    (h : ∀ S ∈ SAP.P002b.assignments P, E S → F S) :
    SAP.P002b.probability P E ≤ SAP.P002b.probability P F := by
  classical
  unfold SAP.P002b.probability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show
    (SAP.P002b.assignments P).filter E ⊆ (SAP.P002b.assignments P).filter F from by
      intro S hS
      rcases Finset.mem_filter.mp hS with ⟨hSA, hE⟩
      exact Finset.mem_filter.mpr ⟨hSA, h S hSA hE⟩)

theorem rank_characterization {n : ℕ} (P : Population n) (hP : ValidDesign P)
    (α : ℝ) (hα : 0 < α ∧ α < 1) (g : Finset (Fin n) → ℝ≥0∞)
    (x : ℝ≥0∞) (hx : x ∈ (assignments P).image g) :
    (x ≤ quantile P g α ↔ probability P (fun T => g T < x) < 1 - α) := by
  classical
  let A : Finset (Finset (Fin n)) := assignments P
  let V : Finset ℝ≥0∞ := A.image g
  let b : ℝ := 1 - α
  have hA : A.Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa [A, assignments] using (Nat.le_of_lt hP.2.2)
  have hAcard : (A.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hA)
  have hV : V.Nonempty := by
    rcases hA with ⟨T, hT⟩
    exact ⟨g T, Finset.mem_image.mpr ⟨T, hT, rfl⟩⟩
  let z : ℝ≥0∞ := V.max' hV
  have hzV : z ∈ V := by
    exact Finset.max'_mem V hV
  have hlemax (T : Finset (Fin n)) (hT : T ∈ A) : g T ≤ z := by
    apply Finset.le_max' V (g T)
    exact Finset.mem_image.mpr ⟨T, hT, rfl⟩
  have hzprob : probability P (fun T => g T ≤ z) = 1 := by
    have hcongr : ∀ T ∈ assignments P, (g T ≤ z) ↔ True := by
      intro T hT
      constructor
      · intro
        trivial
      · intro _
        exact hlemax T (by simpa [A] using hT)
    rw [probability_congr P hcongr]
    simp [probability, hAcard, A]
  let C : Finset ℝ≥0∞ :=
    ((assignments P).image g).filter fun t => 1 - α ≤ probability P (fun T => g T ≤ t)
  have hC : C.Nonempty := by
    refine ⟨z, Finset.mem_filter.mpr ⟨hzV, ?_⟩⟩
    rw [hzprob]
    linarith
  let Q : Finset ℝ≥0∞ :=
    (@Finset.image (Finset (Fin n)) ℝ≥0∞
      (fun a b => Classical.propDecidable (a = b)) g (assignments P)).filter
      fun t => 1 - α ≤ probability P (fun S => g S ≤ t)
  have hQC : Q = C := by
    ext t
    simp [Q, C]
  have hQ : Q.Nonempty := by
    rw [hQC]
    exact hC
  have hquant : quantile P g α = C.min' hC := by
    unfold SAP.P002b.quantile
    dsimp only
    change (if h : Q.Nonempty then Q.min' h else ⊤) = C.min' hC
    rw [dif_pos hQ]
    simpa only [hQC]
  have hqC : quantile P g α ∈ C := by
    rw [hquant]
    exact Finset.min'_mem C hC
  have hnot (y : ℝ≥0∞) (hy : y ∈ V) (hyq : y < quantile P g α) :
      ¬ b ≤ probability P (fun T => g T ≤ y) := by
    intro hby
    have hyC : y ∈ C := Finset.mem_filter.mpr ⟨hy, by simpa [b] using hby⟩
    have hqy : quantile P g α ≤ y := by
      rw [hquant]
      exact Finset.min'_le C y hyC
    exact (not_lt_of_ge hqy) hyq
  have hqprob : b ≤ probability P (fun T => g T ≤ quantile P g α) := by
    simpa [b] using (Finset.mem_filter.mp hqC).2
  have hqV : quantile P g α ∈ V := (Finset.mem_filter.mp hqC).1
  have hchar : x ≤ quantile P g α ↔
      probability P (fun T => g T < x) < b := by
    constructor
    · intro hxq
      let L : Finset ℝ≥0∞ := V.filter fun t => t < x
      by_cases hL : L.Nonempty
      · let m : ℝ≥0∞ := L.max' hL
        have hmL : m ∈ L := Finset.max'_mem L hL
        have hmV : m ∈ V := (Finset.mem_filter.mp hmL).1
        have hmx : m < x := (Finset.mem_filter.mp hmL).2
        have hmq : m < quantile P g α := lt_of_lt_of_le hmx hxq
        have heq : probability P (fun T => g T < x) =
            probability P (fun T => g T ≤ m) := by
          apply probability_congr P
          intro T hT
          constructor
          · intro hTx
            have hgV : g T ∈ V := by
              exact Finset.mem_image.mpr ⟨T, by simpa [A] using hT, rfl⟩
            have hgL : g T ∈ L := Finset.mem_filter.mpr ⟨hgV, hTx⟩
            exact Finset.le_max' L (g T) hgL
          · intro hTm
            exact lt_of_le_of_lt hTm hmx
        have hnotm := hnot m hmV hmq
        have hnotstrict : ¬ b ≤ probability P (fun T => g T < x) := by
          intro hb
          apply hnotm
          rw [← heq]
          exact hb
        exact lt_of_not_ge hnotstrict
      · have heq : probability P (fun T => g T < x) =
            probability P (fun _ : Finset (Fin n) => False) := by
          apply probability_congr P
          intro T hT
          constructor
          · intro hTx
            have hgV : g T ∈ V := by
              exact Finset.mem_image.mpr ⟨T, by simpa [A] using hT, rfl⟩
            exact hL ⟨g T, Finset.mem_filter.mpr ⟨hgV, hTx⟩⟩
          · intro hfalse
            exact False.elim hfalse
        have hzero : probability P (fun _ : Finset (Fin n) => False) = 0 := by
          simp [probability]
        have hnotstrict : ¬ b ≤ probability P (fun T => g T < x) := by
          rw [heq, hzero]
          dsimp [b]
          linarith
        exact lt_of_not_ge hnotstrict
    · intro hxlt
      by_contra hxq
      have hqx : quantile P g α < x := lt_of_not_ge hxq
      have hmono : probability P (fun T => g T ≤ quantile P g α) ≤
          probability P (fun T => g T < x) := by
        apply probability_mono P
        intro T _ hT
        exact lt_of_le_of_lt hT hqx
      have : b ≤ probability P (fun T => g T < x) := le_trans hqprob hmono
      exact (not_lt_of_ge this) hxlt
  simpa [b] using hchar

end SAP.P002b.WH.W1.P.T26_L3

open SAP.P002b
attribute [local instance] Classical.propDecidable

theorem SAP.P002b.WH.W1.T26_L3_proof : SAP.P002b.WH.W1.T26_L3 := by
  intro n P S α hP hS hα g
  have hgs : g S ∈ (assignments P).image g :=
    Finset.mem_image.mpr ⟨S, hS, rfl⟩
  have hg := SAP.P002b.WH.W1.P.T26_L3.rank_characterization P hP α hα g (g S) hgs
  constructor
  · exact hg
  · intro h hh
    have hhs : h S ∈ (assignments P).image h :=
      Finset.mem_image.mpr ⟨S, hS, rfl⟩
    have hhchar := SAP.P002b.WH.W1.P.T26_L3.rank_characterization P hP α hα h (h S) hhs
    have hstrict : probability P (fun T => g T < g S) =
        probability P (fun T => h T < h S) := by
      apply SAP.P002b.WH.W1.P.T26_L3.probability_congr P
      intro T hT
      have horder := hh S hS T hT
      rw [lt_iff_not_ge, lt_iff_not_ge]
      exact not_congr horder
    constructor
    · intro hacc
      apply hhchar.mpr
      rw [← hstrict]
      exact hg.mp hacc
    · intro hacc
      apply hg.mpr
      rw [hstrict]
      exact hhchar.mp hacc

