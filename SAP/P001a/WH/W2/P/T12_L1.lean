import SAP.P001a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

noncomputable section

namespace SAP.P001a.WH.W2.P.T12_L1

end SAP.P001a.WH.W2.P.T12_L1

theorem SAP.P001a.WH.W2.T12_L1_proof : SAP.P001a.WH.W2.T12_L1 := by
  unfold SAP.P001a.WH.W2.T12_L1 SAP.P001a.W2ArgmaxPrinciple
  intro Ω hΩ μ hμ τ Θ hcompact θ hθ L hL hu F T hTmeas hTvalues G hG hmax huniform
  intro ε hε
  obtain ⟨δ, hδ, hsep⟩ :=
    AronowAudit.P001.compact_unique_maximum_separated Θ hcompact θ hθ L hL hu ε hε
  have hlimerr : Tendsto
      (fun n => prob μ {ω | ∃ t ∈ Θ, δ / 3 ≤ |F n ω t - L t|})
      atTop (nhds 0) := huniform (δ / 3) (by positivity)
  have hlim : Tendsto
      (fun n => prob μ {ω | ∃ t ∈ Θ, δ / 3 ≤ |F n ω t - L t|} +
        prob μ (G n)ᶜ) atTop (nhds 0) := by
    simpa only [zero_add] using hlimerr.add hG
  have hbound (n : ℕ) (hn : 0 < n) :
      prob μ {ω | ε ≤ dist (T n ω) θ} ≤
        prob μ {ω | ∃ t ∈ Θ, δ / 3 ≤ |F n ω t - L t|} + prob μ (G n)ᶜ := by
    have hinc : ∀ᵐ ω ∂μ,
        ω ∈ {ω | ε ≤ dist (T n ω) θ} →
          ω ∈ {ω | ∃ t ∈ Θ, δ / 3 ≤ |F n ω t - L t|} ∪ (G n)ᶜ := by
      filter_upwards [hTvalues n hn, hmax n hn] with ω hvalue hmaximize
      intro hbad
      by_cases herr : ω ∈ {ω | ∃ t ∈ Θ, δ / 3 ≤ |F n ω t - L t|}
      · exact Or.inl herr
      · by_cases hgood : ω ∈ G n
        · have hopt : F n ω θ ≤ F n ω (T n ω) := hmaximize hgood θ hθ
          have hTerror : |F n ω (T n ω) - L (T n ω)| < δ / 3 := by
            by_contra hnot
            exact herr ⟨T n ω, hvalue, le_of_not_gt hnot⟩
          have hθerror : |F n ω θ - L θ| < δ / 3 := by
            by_contra hnot
            exact herr ⟨θ, hθ, le_of_not_gt hnot⟩
          have hgap := AronowAudit.P001.argmax_finite_gap L (F n ω)
            (T n ω) θ (δ / 3) 0 hTerror.le hθerror.le (by simpa using hopt)
          have hseparated := hsep (T n ω) hvalue hbad
          linarith
        · exact Or.inr (by simpa only [Set.mem_compl_iff] using hgood)
    calc
      prob μ {ω | ε ≤ dist (T n ω) θ} ≤
          prob μ ({ω | ∃ t ∈ Θ, δ / 3 ≤ |F n ω t - L t|} ∪ (G n)ᶜ) := by
        unfold SAP.P001a.prob
        exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hinc)
      _ ≤ prob μ {ω | ∃ t ∈ Θ, δ / 3 ≤ |F n ω t - L t|} + prob μ (G n)ᶜ :=
        measureReal_union_le _ _
  have hbound_eventually : ∀ᶠ n : ℕ in atTop,
      prob μ {ω | ε ≤ dist (T n ω) θ} ≤
        prob μ {ω | ∃ t ∈ Θ, δ / 3 ≤ |F n ω t - L t|} + prob μ (G n)ᶜ := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact hbound n hn
  exact squeeze_zero' (Eventually.of_forall (fun n => ENNReal.toReal_nonneg))
    hbound_eventually hlim
