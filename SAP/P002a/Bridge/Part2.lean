import SAP.P002a.Bridge.Part1
import AronowAudit.P002.P002_ConfidenceCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace SAP.P002a.Bridge
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology

/-! The only nondefinitional transports change the type indexing a quantifier. -/

theorem infCoverageTheta_eq (n : ℕ) (δ r A α : ℝ) :
    infCoverageTheta n δ r A α = AronowAudit.P002.infCoverageTheta n δ r A α := by
  unfold SAP.P002a.infCoverageTheta AronowAudit.P002.infCoverageTheta
  apply le_antisymm
  · refine le_iInf fun β => le_iInf fun P => ?_
    exact iInf_le_of_le β
      (iInf_le_of_le ⟨fromPopulation P.val, P.property⟩ le_rfl)
  · refine le_iInf fun β => le_iInf fun P => ?_
    exact iInf_le_of_le β
      (iInf_le_of_le ⟨toPopulation P.val, P.property⟩ le_rfl)

theorem infCoverageXi_eq (n k : ℕ) (δ e A B r α : ℝ) :
    infCoverageXi n k δ e A B r α = AronowAudit.P002.infCoverageXi n k δ e A B r α := by
  unfold SAP.P002a.infCoverageXi AronowAudit.P002.infCoverageXi
  apply le_antisymm
  · refine le_iInf fun β => le_iInf fun P => ?_
    exact iInf_le_of_le β
      (iInf_le_of_le ⟨fromCovPopulation P.val, P.property⟩ le_rfl)
  · refine le_iInf fun β => le_iInf fun P => ?_
    exact iInf_le_of_le β
      (iInf_le_of_le ⟨toCovPopulation P.val, P.property⟩ le_rfl)

theorem thetaSizes_eq (δ r A : ℝ) :
    thetaSizes δ r A = {n | ∃ P : AronowAudit.P002.Population n,
      AronowAudit.P002.Theta P δ r A} := by
  ext n
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨toPopulation P, hP⟩
  · rintro ⟨P, hP⟩
    exact ⟨fromPopulation P, hP⟩

theorem xiSizes_eq (k : ℕ) (δ e A B r : ℝ) :
    xiSizes k δ e A B r = {n | ∃ P : AronowAudit.P002.CovPopulation n k,
      AronowAudit.P002.Xi P δ e A B r} := by
  ext n
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨toCovPopulation P, hP⟩
  · rintro ⟨P, hP⟩
    exact ⟨fromCovPopulation P, hP⟩

theorem printedLemma5_correspondence :
    SAP.P002a.PrintedLemma5 ↔ AronowAudit.P002.ConfidenceFollowup.PrintedLemma5 := by
  constructor
  · intro h n P δ r A hδ hr hA hP
    exact h (fromPopulation P) δ r A hδ hr hA hP
  · intro h n P δ r A hδ hr hA hP
    exact h (toPopulation P) δ r A hδ hr hA hP

theorem printedE10_correspondence :
    SAP.P002a.PrintedE10 ↔ AronowAudit.P002.ConfidenceFollowup.PrintedE10 := by
  constructor
  · intro h n k P δ e A B r hk hδ he hA hB hr hP
    exact h (fromCovPopulation P) δ e A B r hk hδ he hA hB hr hP
  · intro h n k P δ e A B r hk hδ he hA hB hr hP
    exact h (toCovPopulation P) δ e A B r hk hδ he hA hB hr hP

end
end SAP.P002a.Bridge
