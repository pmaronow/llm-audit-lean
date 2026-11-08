import SAP.P018a.WH.W3.Leaves
import AronowAudit.P018.Wave1.WeightedConsistency.G4

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section
namespace SAP.P018a.WH.W3.P.T2_L3

open Finset Matrix MeasureTheory ProbabilityTheory
open AronowAudit.P018.Wave1.WeightedConsistency
open scoped BigOperators

private def blockInputScore {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : SAP.P018a.RepeatedKernel U k)
    (w : (d : SAP.P018a.Dyad N) → Fin (R.T N d) → ℝ)
    (β : SAP.P018a.Vec k) (d : SAP.P018a.Dyad N)
    (z : (i : SAP.P018a.members d) → U) : SAP.P018a.Vec k :=
  ∑ t, SAP.P018a.score
    (R.X N d t (z ⟨SAP.P018a.firstUnit d, firstUnit_mem d⟩)
      (z ⟨SAP.P018a.secondUnit d, secondUnit_mem d⟩))
    (w d t * (R.Y N d t (z ⟨SAP.P018a.firstUnit d, firstUnit_mem d⟩)
      (z ⟨SAP.P018a.secondUnit d, secondUnit_mem d⟩) -
      SAP.P018a.dot (R.X N d t (z ⟨SAP.P018a.firstUnit d, firstUnit_mem d⟩)
        (z ⟨SAP.P018a.secondUnit d, secondUnit_mem d⟩)) β))

private theorem blockInputScore_measurable {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : SAP.P018a.RepeatedKernel U k)
    (hR : SAP.P018a.RepeatedAtSize R N)
    (w : (d : SAP.P018a.Dyad N) → Fin (R.T N d) → ℝ)
    (β : SAP.P018a.Vec k) (d : SAP.P018a.Dyad N) :
    Measurable (blockInputScore R w β d) := by
  classical
  apply measurable_pi_iff.mpr
  intro a
  simp only [blockInputScore, Finset.sum_apply, SAP.P018a.score,
    Pi.smul_apply, smul_eq_mul, SAP.P018a.dot]
  apply Finset.measurable_fun_sum
  intro t ht
  let hp : ((i : SAP.P018a.members d) → U) → U × U := fun z =>
    (z ⟨SAP.P018a.firstUnit d, firstUnit_mem d⟩,
      z ⟨SAP.P018a.secondUnit d, secondUnit_mem d⟩)
  have hp_meas : Measurable hp := by
    dsimp [hp]
    exact (measurable_pi_apply
      (⟨SAP.P018a.firstUnit d, firstUnit_mem d⟩ : SAP.P018a.members d)).prodMk
      (measurable_pi_apply
      (⟨SAP.P018a.secondUnit d, secondUnit_mem d⟩ : SAP.P018a.members d))
  have hX (b : Fin k) : Measurable
      (fun z : (i : SAP.P018a.members d) → U =>
        R.X N d t (hp z).1 (hp z).2 b) :=
    (measurable_pi_apply b).comp ((hR.2.2.1 d t).1.comp hp_meas)
  have hY : Measurable (fun z : (i : SAP.P018a.members d) → U =>
      R.Y N d t (hp z).1 (hp z).2) := (hR.2.2.1 d t).2.comp hp_meas
  have hdot : Measurable (fun z : (i : SAP.P018a.members d) → U =>
      ∑ b : Fin k, R.X N d t (hp z).1 (hp z).2 b * β b) := by
    apply Finset.measurable_fun_sum
    intro b hb
    exact (hX b).mul measurable_const
  have hres : Measurable (fun z : (i : SAP.P018a.members d) → U =>
      w d t * (R.Y N d t (hp z).1 (hp z).2 -
        ∑ b : Fin k, R.X N d t (hp z).1 (hp z).2 b * β b)) :=
    measurable_const.mul (hY.sub hdot)
  exact hres.mul (hX a)

end SAP.P018a.WH.W3.P.T2_L3

open SAP.P018a.WH.W3.P.T2_L3
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem SAP.P018a.WH.W3.T2_L3_proof : SAP.P018a.WH.W3.T2_L3 := by
  classical
  intro U _ k N R hR w β d f hdf
  letI : IsProbabilityMeasure R.μ := hR.1
  letI : IsProbabilityMeasure (SAP.P018a.repeatedLaw R N) := by
    unfold SAP.P018a.repeatedLaw
    infer_instance
  have hcoords : iIndepFun
      (fun i : Fin N => fun ω : Fin N → U => ω i)
      (SAP.P018a.repeatedLaw R N) := by
    simpa only [SAP.P018a.repeatedLaw] using
      (iIndepFun_pi (μ := fun _ : Fin N => R.μ)
        (X := fun _ : Fin N => fun x : U => x) (fun _ => aemeasurable_id))
  have hdisj : Disjoint (SAP.P018a.members d) (SAP.P018a.members f) := by
    change ¬ (SAP.P018a.members d ∩ SAP.P018a.members f).Nonempty at hdf
    exact Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hdf)
  have htuples := hcoords.indepFun_finset (SAP.P018a.members d)
    (SAP.P018a.members f) hdisj
    (fun i => measurable_pi_apply (i : Fin N))
  let φ := SAP.P018a.WH.W3.P.T2_L3.blockInputScore R w β d
  let ψ := SAP.P018a.WH.W3.P.T2_L3.blockInputScore R w β f
  have hcomp := htuples.comp
    (SAP.P018a.WH.W3.P.T2_L3.blockInputScore_measurable R hR w β d)
    (SAP.P018a.WH.W3.P.T2_L3.blockInputScore_measurable R hR w β f)
  have hleft : (fun ω : Fin N → U => φ (fun i => ω i)) =
      (fun ω => SAP.P018a.recordWeightedBlockScore R w β ω d) := by
    funext ω
    apply funext
    intro a
    simp [φ, SAP.P018a.WH.W3.P.T2_L3.blockInputScore,
      SAP.P018a.recordWeightedBlockScore, SAP.P018a.repeatedX,
      SAP.P018a.repeatedY]
  have hright : (fun ω : Fin N → U => ψ (fun i => ω i)) =
      (fun ω => SAP.P018a.recordWeightedBlockScore R w β ω f) := by
    funext ω
    apply funext
    intro a
    simp [ψ, SAP.P018a.WH.W3.P.T2_L3.blockInputScore,
      SAP.P018a.recordWeightedBlockScore, SAP.P018a.repeatedX,
      SAP.P018a.repeatedY]
  simpa only [Function.comp_def, φ, ψ, hleft, hright] using hcomp
