import SAP.P024.Defs.WholeW3
import SAP.P024.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024.WH.W3
open scoped BigOperators
open SAP.P024.Bridge
noncomputable section

/-- Assemble the fixed-quota specialization without new leaves. Replace the
actual design probabilities by the stipulated common block marginals and split
on each Boolean treatment to recover the existing `blockedHT`. Apply the
project's allocation identity and unbiasedness theorem. Transfer unbiasedness
to the ordinary observed block means by their pointwise identity. Fixed quotas
and common actual marginals are additional design assumptions; mere
nonempty observed arms would not imply either of them. -/
theorem T8_assembly : T8WholeStatement_W3 := by
  classical
  intro B Ω _ _ _ I _ d m hm hmN z y0 y1 hcount hp
  have hsize (b : B) : (0 : ℝ) < Fintype.card (I b) := by
    exact_mod_cast lt_trans (hm b) (hmN b)
  have hpopulation : 0 < blockPopulation I := by
    unfold blockPopulation
    exact Finset.sum_pos (fun b _ => hsize b) Finset.univ_nonempty
  have hprob (b : B) (i : I b) :
      0 < exposureProbability d (fun ω => z ω b) i ∧
      exposureProbability d (fun ω => z ω b) i < 1 := by
    rw [hp b i]
    constructor
    · exact div_pos (by exact_mod_cast hm b) (hsize b)
    · exact (div_lt_one (hsize b)).mpr (by exact_mod_cast hmN b)
  have hactual : actualBlockedHTW3 I d z y0 y1 = blockedHT I m z y0 y1 := by
    funext ω
    unfold actualBlockedHTW3 blockedHT
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro i _
    rw [hp b i]
    cases hzi : z ω b i <;> simp [indicator, observed, hzi]
  have hidentity (ω : Ω) : blockedHT I m z y0 y1 ω =
      ∑ b, (Fintype.card (I b) : ℝ) / blockPopulation I *
        clusterDIM (fun _ => 1) (y0 b) (y1 b) (z ω b) :=
    AronowAudit.P024.blocked_actual_means_identity I m hm hmN z y0 y1 hcount ω
  have hunbiased : expectation d (blockedHT I m z y0 y1) =
      (∑ b, ∑ i, (y1 b i - y0 b i)) / blockPopulation I :=
    (AronowAudit.P024.blocked_estimator_unbiased I (toDesign d) m hm hmN
      z y0 y1 hcount hp).1
  refine ⟨hpopulation, hprob, ?_, ?_, ?_⟩
  · intro ω
    rw [hactual]
    exact hidentity ω
  · rw [hactual]
    exact hunbiased
  · have heq : (fun ω => ∑ b, (Fintype.card (I b) : ℝ) / blockPopulation I *
        clusterDIM (fun _ => 1) (y0 b) (y1 b) (z ω b)) = blockedHT I m z y0 y1 :=
      funext (fun ω => (hidentity ω).symm)
    rw [heq]
    exact hunbiased

end
end SAP.P024.WH.W3
