import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint

/-!
# Theorem 3 for Algorithms 1/3 and 2/4 (P002-T28)

Main p. 17, Theorem 3. The conclusions cover existence of the complete finite
crossing list, an Algorithm 1 run for every complete list, correctness of Algorithm 1,
an Algorithm 2 run for every nonempty list, correctness for every admissible
Algorithm 2 run, and the no-intersection immediate return with an arbitrary sample
point. Both data branches (Assumption 6 unadjusted, Assumption 7 adjusted) are
expressed by `DataGeneratedCoefficients` and `ARRegular`.
-/

namespace AronowAudit.P002.Wave1.AlgorithmCorrectness
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable


def Target : Prop :=
  ∀ (M : ℕ) (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ),
    0 < M → (0 < α ∧ α < 1) → DataGeneratedCoefficients Qf Qg →
    ARRegular Qf → (∀ m, ARRegular (Qg m)) →
    let f := arFunction Qf
    let g := fun m => arFunction (Qg m)
    (∃ J, IntersectionList g J) ∧
    (∀ J, IntersectionList g J → ∃ pieces, Algorithm1Run g α J pieces) ∧
    (∀ J pieces, Algorithm1Run g α J pieces →
      returnedSet f g pieces = mcSet f g α) ∧
    (∀ J, IntersectionList g J → J ≠ [] →
      ∃ pieces, Algorithm2Run g α J pieces) ∧
    (∀ J pieces, Algorithm2Run g α J pieces →
      returnedSet f g pieces = mcSet f g α) ∧
    (∀ J, IntersectionList g J → J = [] →
      ∀ β m, m ∈ mcIndices g α β →
        {x | f x ≤ g m x} = mcSet f g α)

/-- The nodes suffice. -/
theorem assemble (h1 : AlgorithmSupport.N1) (h2 : AlgorithmSupport.N2)
    (h3 : AlgorithmSupport.N3) (h4 : AlgorithmSupport.N4) (h5 : AlgorithmSupport.N5)
    (h6 : AlgorithmSupport.N6) (h7 : AlgorithmSupport.N7) (h8 : AlgorithmSupport.N8)
    (h9 : AlgorithmSupport.N9) (h10 : AlgorithmSupport.N10) (h11 : AlgorithmSupport.N11)
    (h12 : AlgorithmSupport.N12) (h13 : AlgorithmSupport.N13)
    (h14 : AlgorithmSupport.N14) : Target := by
  intro M Qf Qg α hM hα _hdata hQf hQg
  have hreg := arFamily_regular Qg hQg
  have hf : ∀ β, 0 ≤ arFunction Qf β :=
    fun β => div_nonneg (hQf.2 β) (le_of_lt (hQf.1 β))
  have hc : ∀ s, Continuous ((fun m => arFunction (Qg m)) s) := hreg.1
  have hn : ∀ s β, 0 ≤ (fun m => arFunction (Qg m)) s β := hreg.2.1
  have hall : ∀ β, (mcIndices (fun m => arFunction (Qg m)) α β).Nonempty :=
    fun β => (h1 M _ α β hM hα (fun m => hn m β)).1
  refine ⟨h8 M _ hreg, ?_, ?_, ?_, ?_, ?_⟩
  · intro J hJ
    exact h9 M _ α J hJ hall
  · intro J pieces hRun
    exact AlgorithmSupport.glue_algorithm1_returned h2 h3 h4 h5 h6 h7 (arFunction Qf)
      _ α hM hα hc hn hf J pieces hRun
  · intro J hJ hne
    exact AlgorithmSupport.glue_algorithm2_exists h1 h10 h14 _ α hM hα hn J hJ hne
  · intro J pieces hRun
    exact (AlgorithmSupport.glue_algorithm2_props h2 h3 h4 h5 h11 h12 h13 h14 (arFunction Qf)
      _ α hM hα hc hn hf J pieces hRun).2.2.2.2.2.2
  · intro J hJ hJnil β m hm
    -- no crossing anywhere: the whole line is one crossing-free interval
    have hsc : ∀ s, (fun m => arFunction (Qg m)) s ≠ (fun m => arFunction (Qg m)) m →
        ∀ x ∈ openInterval ⊥ ⊤, (fun m => arFunction (Qg m)) s x ≠
          (fun m => arFunction (Qg m)) m x := by
      intro s hs x _ heq
      have hx := (hJ.2 x).mpr ⟨s, m, hs, heq⟩
      rw [hJnil] at hx
      simp at hx
    have hβ : β ∈ openInterval ⊥ ⊤ := ⟨EReal.bot_lt_coe β, EReal.coe_lt_top β⟩
    have hvalid := AlgorithmSupport.glue_closed_valid h2 h3 h4 _ α hM hα hc hn m ⊥ ⊤ β
      hβ hsc hm
    have hp := (h5 M (arFunction Qf) _ α ⟨⊥, ⊤, m⟩ hf hn hvalid).2
    have hall' : ∀ x : ℝ, x ∈ closedInterval ⊥ ⊤ :=
      fun x => ⟨bot_le, le_top⟩
    ext x
    have hx := congrArg (fun S : Set ℝ => x ∈ S) hp
    simp only [pieceSet, Set.mem_ofPred_eq, Set.mem_inter_iff] at hx
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ((hx.mp ⟨hall' x, h⟩).1)
    · intro h
      exact (hx.mpr ⟨h, hall' x⟩).2

end
end AronowAudit.P002.Wave1.AlgorithmCorrectness
