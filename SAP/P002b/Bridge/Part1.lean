import SAP.P002b.Defs
import AronowAudit.P002.P002_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b.Bridge
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory

/-- Field-for-field adapters; all finite numerical definitions agree by reduction. -/
def toPopulation {n : ℕ} (P : Population n) : AronowAudit.P002.Population n :=
  ⟨P.y, P.d, P.n1⟩

def fromPopulation {n : ℕ} (P : AronowAudit.P002.Population n) : Population n :=
  ⟨P.y, P.d, P.n1⟩

def toCovPopulation {n k : ℕ} (P : CovPopulation n k) : AronowAudit.P002.CovPopulation n k :=
  ⟨toPopulation P.pop, P.x⟩

def fromCovPopulation {n k : ℕ} (P : AronowAudit.P002.CovPopulation n k) : CovPopulation n k :=
  ⟨fromPopulation P.pop, P.x⟩

/-- Reindexing the nested infimum along the population adapter. Empty infima
remain the extended-real top value on both sides. -/
theorem infCoverageTheta_eq (n : ℕ) (δ r A α : ℝ) :
    infCoverageTheta n δ r A α = AronowAudit.P002.infCoverageTheta n δ r A α := by
  unfold infCoverageTheta AronowAudit.P002.infCoverageTheta
  apply le_antisymm
  · refine le_iInf fun β => le_iInf fun P => ?_
    exact iInf_le_of_le β (iInf_le_of_le ⟨fromPopulation P.val, P.property⟩ le_rfl)
  · refine le_iInf fun β => le_iInf fun P => ?_
    exact iInf_le_of_le β (iInf_le_of_le ⟨toPopulation P.val, P.property⟩ le_rfl)

/-- The same structural reindexing for covariate populations. -/
theorem infCoverageXi_eq (n k : ℕ) (δ e A B r α : ℝ) :
    infCoverageXi n k δ e A B r α = AronowAudit.P002.infCoverageXi n k δ e A B r α := by
  unfold infCoverageXi AronowAudit.P002.infCoverageXi
  apply le_antisymm
  · refine le_iInf fun β => le_iInf fun P => ?_
    exact iInf_le_of_le β (iInf_le_of_le ⟨fromCovPopulation P.val, P.property⟩ le_rfl)
  · refine le_iInf fun β => le_iInf fun P => ?_
    exact iInf_le_of_le β (iInf_le_of_le ⟨toCovPopulation P.val, P.property⟩ le_rfl)

/-- The observed and potential responses agree on the fitted arm; transport
through the exported score-congruence lemma and the full-rank OLS formula. -/
theorem fitted_potential {n k : ℕ} (P : CovPopulation n k) (β : ℝ)
    (S : Finset (Fin n)) (a : Bool)
    (h : (gram P.x (if a then S else Sᶜ)).det ≠ 0) :
    fitted P (observedW P.pop β S) S a =
      ols P.x (if a then S else Sᶜ) (w P.pop a β) := by
  have hs : score P.x (if a then S else Sᶜ) (observedW P.pop β S) =
      score P.x (if a then S else Sᶜ) (w P.pop a β) := by
    apply AronowAudit.P002.score_congr
    intro i hi
    cases a
    · exact AronowAudit.P002.observedW_control (toPopulation P.pop) β S i hi
    · exact AronowAudit.P002.observedW_treated (toPopulation P.pop) β S i hi
  simp only [fitted, ols, ite_eq_left h, hs]

/-- The displayed residual cross term is the exported score inner product. -/
theorem corrected_arm_identity {n k : ℕ} (P : CovPopulation n k) (β : ℝ)
    (S : Finset (Fin n)) (a : Bool)
    (h : (gram P.x (if a then S else Sᶜ)).det ≠ 0) :
    let A := if a then S else Sᶜ
    (psi P a β - fitted P (observedW P.pop β S) S a =
      -(gram P.x A)⁻¹ *ᵥ score P.x A (residual P a β)) ∧
    (-2 * groupMean A (fun i => residual P a β i *
        dotProduct (augmented P.x i)
          (fitted P (observedW P.pop β S) S a - psi P a β)) =
      -2 * dotProduct (score P.x A (residual P a β))
        ((gram P.x A)⁻¹ *ᵥ score P.x A (residual P a β))) := by
  dsimp only
  rw [fitted_potential P β S a h]
  have H := AronowAudit.P002.corrected_E41_cross_term P.x (if a then S else Sᶜ)
    (w P.pop a β) (psi P a β) h
  refine ⟨H.1, ?_⟩
  have hs : dotProduct (score P.x (if a then S else Sᶜ) (residual P a β))
      (ols P.x (if a then S else Sᶜ) (w P.pop a β) - psi P a β) =
      groupMean (if a then S else Sᶜ) (fun i => residual P a β i *
        dotProduct (augmented P.x i)
          (ols P.x (if a then S else Sᶜ) (w P.pop a β) - psi P a β)) :=
    AronowAudit.P002.score_dot P.x (if a then S else Sᶜ) (residual P a β) _
  rw [← hs]
  exact H.2

end
end SAP.P002b.Bridge
