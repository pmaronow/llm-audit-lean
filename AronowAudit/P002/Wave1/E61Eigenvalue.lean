import AronowAudit.P002.Wave1.E61EigenvalueBlueprint
import AronowAudit.P002.Wave1.E61Eigenvalue.N1
import AronowAudit.P002.Wave1.E61Eigenvalue.N2
import AronowAudit.P002.Wave1.E61Eigenvalue.N3
import AronowAudit.P002.Wave1.E61Eigenvalue.N4
import AronowAudit.P002.Wave1.E61Eigenvalue.N5
import AronowAudit.P002.Wave1.E61Eigenvalue.N6
import AronowAudit.P002.Wave1.E61Eigenvalue.N7
import AronowAudit.P002.Wave1.E61Eigenvalue.N8
import AronowAudit.P002.Wave1.E61Eigenvalue.N9
import AronowAudit.P002.Wave1.E61Eigenvalue.N10
import AronowAudit.P002.Wave1.E61Eigenvalue.N11
import AronowAudit.P002.Wave1.E61Eigenvalue.N12

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

universe u

/-- Corrected first display in the proof of Lemma 19, Supplement p. 42.
The independent coupling is retained in the paper statement; the proof uses its marginals. -/
theorem corrected_E61_eigenvalue_paper {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ n, CovPopulation (sizes n) k)
    (Z : ∀ n, Ω → Finset (Fin (sizes n))) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hP : ∀ n, Xi (P n) δ e A B r)
    (hZ : RandomizationSequence (fun n => (P n).pop) μ Z)
    (hIndependent : ∀ (I : Finset ℕ) (E : ∀ n, Finset (Fin (sizes n)) → Prop),
      μ {ω | ∀ n ∈ I, E n (Z n ω)} = ∏ n ∈ I, μ {ω | E n (Z n ω)})
    (sub : ℕ → ℕ) (hsub : StrictMono sub) :
    ∀ᵐ ω ∂μ, ∃ err : ℕ → ℝ, Tendsto err atTop (nhds 0) ∧
      ∀ᶠ j in atTop, ∀ a : Bool,
        let N := sub j
        let S := Z N ω
        let q := observedW (P N).pop (late (P N).pop) S
        let b := fitted (P N) q S a - ols (P N).x Finset.univ q
        (min 1 e + err j) * normSq b ≤
          dotProduct b (gram (P N).x (if a then S else Sᶜ) *ᵥ b) :=
  E61Eigenvalue.assemble
    E61Eigenvalue.n1_proof E61Eigenvalue.n2_proof E61Eigenvalue.n3_proof
    E61Eigenvalue.n4_proof E61Eigenvalue.n5_proof E61Eigenvalue.n6_proof
    E61Eigenvalue.n7_proof E61Eigenvalue.n8_proof E61Eigenvalue.n9_proof
    E61Eigenvalue.n10_proof E61Eigenvalue.n11_proof E61Eigenvalue.n12_proof
    μ sizes hsizes k P Z δ e A B r hk hδ he hA hB hr hP hZ hIndependent sub hsub

end
end AronowAudit.P002.Wave1
