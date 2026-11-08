import SAP.P009c.WH.W1.Leaves
import AronowAudit.P009.P009_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009c.WH.W1.P.T41_L1

end SAP.P009c.WH.W1.P.T41_L1

theorem SAP.P009c.WH.W1.T41_L1_proof : SAP.P009c.WH.W1.T41_L1 := by
  intro S X Y a D hD hXY hX
  intro ε hε
  obtain ⟨K, hK, hXtail⟩ := hX (ε / 2) (by linarith)
  have hDtail : ∀ᶠ t in Filter.atTop,
      SAP.P009c.prob (S.experiment t).design (D t) ≤ ε / 2 := by
    exact hD.eventually_le_const (by linarith : (0 : ℝ) < ε / 2)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hXtail, hDtail] with t htX htD
  calc
    SAP.P009c.prob (S.experiment t).design
        (fun z => K * a t ≤ |Y t z|)
        ≤ SAP.P009c.prob (S.experiment t).design
            (fun z => K * a t ≤ |X t z|) +
          SAP.P009c.prob (S.experiment t).design (D t) := by
      have hUnion := AronowAudit.P009.probability_union_bound
        (SAP.P009c.Bridge.toLaw (S.experiment t).design)
        (fun z => K * a t ≤ |Y t z|)
        (fun z => K * a t ≤ |X t z|)
        (D t) (by
          intro z hz
          by_cases hDz : D t z
          · exact Or.inr hDz
          · left
            rw [hXY t z hDz]
            exact hz)
      simpa only [SAP.P009c.Bridge.prob_toLaw] using hUnion
    _ ≤ ε / 2 + ε / 2 := add_le_add htX htD
    _ = ε := by ring
