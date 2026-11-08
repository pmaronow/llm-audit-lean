import AronowAudit.P006.Wave1.CorrectedRanking.N2
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

set_option autoImplicit false
universe u v
namespace AronowAudit.P006.Wave1.CorrectedRanking
open AronowAudit.P006 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
noncomputable section

theorem n4_proof : N4.{u,v} := by
  classical
  intro h2 h3 Ω C _ _ n E P0 _ hS hac hτ hU hreward π hπ
  haveI : IsProbabilityMeasure E.PX := hS.px_probability
  haveI : IsProbabilityMeasure (E.law π) := hS.law_probability π hπ
  let g := referenceWeight n P0 E.PX
  have hg : Measurable g :=
    measurable_const.mul (Measure.measurable_rnDeriv P0 E.PX).ennreal_toReal
  have hτm : Measurable E.τ := hS.means_measurable.2.sub hS.means_measurable.1
  have hτπ : Integrable (fun x => E.τ x * π x) P0 := by
    apply hτ.mul_bdd hπ.1.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hπ.2 x).1]
      exact (hπ.2 x).2)
  have hRN := h3 P0 E.PX hac n E.hn (fun x => E.τ x * π x) hτπ
  have hunit (i : Fin n) :
      (∫ ω, (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω) *
        referenceWeight n P0 E.PX (E.X i ω) ∂E.law π) =
        ∫ x, E.τ x * π x * referenceWeight n P0 E.PX x ∂E.PX := by
    let Z : Ω → ℝ := fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω)
    let G : Ω → ℝ := fun ω => g (E.X i ω)
    have hX := (hS.measurable_units π hπ i).1
    have hm : E.covariateSigma i ≤ (inferInstance : MeasurableSpace Ω) := hX.comap_le
    have hG : StronglyMeasurable[E.covariateSigma i] G :=
      (hg.comp (comap_measurable (E.X i))).stronglyMeasurable
    have hZ : Integrable Z (E.law π) := reward_integrable E hS π hπ i
    have hGZ : Integrable (G * Z) (E.law π) := by
      refine (hreward π hπ i).congr (Eventually.of_forall fun ω => ?_)
      show (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω) *
        referenceWeight n P0 E.PX (E.X i ω) = G ω * Z ω
      simp only [G, Z, g]
      ring
    have hpull := condExp_mul_of_stronglyMeasurable_left hG hGZ hZ
    have hmean := h2 E hS hU π hπ i
    have hCE : (E.law π)[fun ω => Z ω * G ω | E.covariateSigma i] =ᵐ[E.law π]
        fun ω => E.τ (E.X i ω) * π (E.X i ω) * g (E.X i ω) := by
      have hcomm : (E.law π)[fun ω => Z ω * G ω | E.covariateSigma i] =ᵐ[E.law π]
          (E.law π)[G * Z | E.covariateSigma i] := by
        apply condExp_congr_ae
        exact Eventually.of_forall (fun ω => mul_comm _ _)
      filter_upwards [hcomm, hpull, hmean] with ω hcomm hpull hmean
      rw [hcomm, hpull]
      simp only [Pi.mul_apply]
      rw [hmean]
      dsimp [G]
      ring
    calc
      _ = ∫ ω, (E.law π)[fun η => Z η * G η | E.covariateSigma i] ω ∂E.law π :=
        (integral_condExp hm).symm
      _ = ∫ ω, E.τ (E.X i ω) * π (E.X i ω) * g (E.X i ω) ∂E.law π := integral_congr_ae hCE
      _ = _ := ((hS.covariate_law π hπ i).comp ((hτm.mul hπ.1).mul hg)).integral_eq
  refine ⟨?_, hRN.2⟩
  unfold Experiment.expectedWeightedTT wWeightedTT
  rw [integral_finsetSum Finset.univ (fun i _ => hreward π hπ i)]
  simp_rw [hunit]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end
end AronowAudit.P006.Wave1.CorrectedRanking
