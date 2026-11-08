import SAP.P008b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b.WH.W2.P.T27_L1

open scoped BigOperators
open MeasureTheory Filter

noncomputable section

theorem selected_marginal_identity {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (ρ : Plane → Plane → ℝ)
    (i : Fin N) (d : ℝ) (b : Bool)
    (hmass : 0 < ((P.selectedMeasure ρ i d) Set.univ).toReal)
    (hfinite : (P.selectedMeasure ρ i d) Set.univ ≠ ⊤)
    (hint : ∀ z, Q.mass z ≠ 0 →
      Integrable (fun x => P.Y x (Function.update z i b))
        (P.selectedMeasure ρ i d)) :
    marginal Q (P.selectedM ρ i d) i b =
      P.selectedAverage ρ i d (P.marginalY Q i b) := by
  simp only [SpatialModel.selectedM, SpatialModel.selectedAverage,
    SpatialModel.marginalY, marginal, FiniteLaw.expect]
  rw [integral_finsetSum (Finset.univ : Finset (Assignment N))
    (fun z _ => AronowAudit.P008.weighted_integrable _ _ _ (hint z))]
  simp_rw [integral_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem selected_effect_identity {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (ρ : Plane → Plane → ℝ)
    (i : Fin N) (d : ℝ)
    (hmass : 0 < ((P.selectedMeasure ρ i d) Set.univ).toReal)
    (hfinite : (P.selectedMeasure ρ i d) Set.univ ≠ ⊤)
    (hint : ∀ b z, Q.mass z ≠ 0 →
      Integrable (fun x => P.Y x (Function.update z i b))
        (P.selectedMeasure ρ i d)) :
    P.selectedNodeEffect ρ Q i d =
      P.selectedAverage ρ i d (P.pointEffect Q i) := by
  have hi (b : Bool) : Integrable (P.marginalY Q i b)
      (P.selectedMeasure ρ i d) := by
    unfold SpatialModel.marginalY marginal FiniteLaw.expect
    exact integrable_finsetSum _ (fun z _ =>
      AronowAudit.P008.weighted_integrable _ _ _ (hint b z))
  unfold SpatialModel.selectedNodeEffect
  rw [selected_marginal_identity P Q ρ i d true hmass hfinite (hint true),
    selected_marginal_identity P Q ρ i d false hmass hfinite (hint false)]
  unfold SpatialModel.selectedAverage SpatialModel.pointEffect
  rw [integral_sub (hi true) (hi false)]
  ring

end

end SAP.P008b.WH.W2.P.T27_L1

theorem SAP.P008b.WH.W2.T27_L1_proof : SAP.P008b.WH.W2.T27_L1 := by
  intro N P Q ρ i d hvalid
  rcases hvalid with ⟨hmass, hfinite, _hconcentrated, hint⟩
  exact SAP.P008b.WH.W2.P.T27_L1.selected_effect_identity P Q ρ i d
    hmass hfinite hint
