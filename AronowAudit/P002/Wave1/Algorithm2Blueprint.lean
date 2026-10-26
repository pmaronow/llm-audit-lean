import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint

/-!
# Corrected Algorithm 2/4 (P002-T22)

Main p. 16, Algorithm 2, Steps 3–6; Supplement p. 44, Algorithm 4, and p. 45,
Section H.2. Step 5 processes the pairs exactly as Step 4 records them.
The data-generated coefficients satisfy Assumptions 6/7 (`ARRegular` for the
observed and every simulated curve).

The conclusions cover existence of a terminating run, every admissible run,
finite crossing endpoints, coverage of the real line, validity of closed pieces,
the piece identities, and the returned set.
-/

namespace AronowAudit.P002.Wave1.Algorithm2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable


def Target : Prop :=
  ∀ (M : ℕ) (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ),
    0 < M → (0 < α ∧ α < 1) → DataGeneratedCoefficients Qf Qg →
    ARRegular Qf → (∀ m, ARRegular (Qg m)) →
    ∀ (J : List ℝ), IntersectionList (fun m => arFunction (Qg m)) J → J ≠ [] →
    let f := arFunction Qf
    let g := fun m => arFunction (Qg m)
    (∃ pieces, Algorithm2Run g α J pieces) ∧
    ∀ pieces, Algorithm2Run g α J pieces →
      pieces.length ≤ J.length + 1 ∧
      (pieces.map (fun p => p.right)).Pairwise (· < ·) ∧
      (∀ p ∈ pieces, p.right = ⊤ ∨
        ∃ e : ℝ, p.right = (e : EReal) ∧ e ∈ J) ∧
      (∀ β : ℝ, ∃ p ∈ pieces, β ∈ closedInterval p.left p.right) ∧
      (∀ p ∈ pieces, ∀ β ∈ closedInterval p.left p.right,
        p.index ∈ mcIndices g α β) ∧
      (∀ p ∈ pieces, pieceSet f g p =
        mcSet f g α ∩ closedInterval p.left p.right) ∧
      returnedSet f g pieces = mcSet f g α

/-- The nodes suffice. -/
theorem assemble (h1 : AlgorithmSupport.N1) (h2 : AlgorithmSupport.N2)
    (h3 : AlgorithmSupport.N3) (h4 : AlgorithmSupport.N4) (h5 : AlgorithmSupport.N5)
    (h10 : AlgorithmSupport.N10) (h11 : AlgorithmSupport.N11)
    (h12 : AlgorithmSupport.N12) (h13 : AlgorithmSupport.N13)
    (h14 : AlgorithmSupport.N14) : Target := by
  intro M Qf Qg α hM hα _hdata hQf hQg J hJ hne
  have hreg := arFamily_regular Qg hQg
  have hf : ∀ β, 0 ≤ arFunction Qf β :=
    fun β => div_nonneg (hQf.2 β) (le_of_lt (hQf.1 β))
  refine ⟨AlgorithmSupport.glue_algorithm2_exists h1 h10 h14 (fun m => arFunction (Qg m)) α
    hM hα hreg.2.1 J hJ hne, ?_⟩
  intro pieces hRun
  exact AlgorithmSupport.glue_algorithm2_props h2 h3 h4 h5 h11 h12 h13 h14 (arFunction Qf)
    (fun m => arFunction (Qg m)) α hM hα hreg.1 hreg.2.1 hf J pieces hRun

end
end AronowAudit.P002.Wave1.Algorithm2
