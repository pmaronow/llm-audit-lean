import SAP.P018a.WH.W1.Leaves
import AronowAudit.P018.Wave1.WeightedConsistency.G1

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
noncomputable section
namespace SAP.P018a.WH.W1.P.T10_L1

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open AronowAudit.P018.Wave1.WeightedConsistency
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

private theorem endpoints_ne {N : ℕ} (d : SAP.P018a.Dyad N) :
    SAP.P018a.firstUnit d ≠ SAP.P018a.secondUnit d := by
  exact AronowAudit.P018.Wave1.WeightedConsistency.firstUnit_ne_secondUnit d

private theorem recordX_eq {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : SAP.P018a.RepeatedKernel U k) (K : SAP.P018a.Kernel U k)
    (dir : ∀ N : ℕ, (d : SAP.P018a.Dyad N) → Fin (R.T N d) → Bool)
    (hCommon : ∀ N d (t : Fin (R.T N d)) u v,
      R.X N d t u v = (if dir N d t then K.X v u else K.X u v) ∧
      R.Y N d t u v = (if dir N d t then K.Y v u else K.Y u v))
    (d : SAP.P018a.Dyad N) (t : Fin (R.T N d)) (ω : Fin N → U) :
    AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t =
      K.X (ω (if dir N d t then SAP.P018a.secondUnit d else SAP.P018a.firstUnit d))
        (ω (if dir N d t then SAP.P018a.firstUnit d else SAP.P018a.secondUnit d)) := by
  have he := SAP.P018a.Bridge.endpoints_agree d
  change R.X N d t (ω (AronowAudit.P018.firstUnit d))
      (ω (AronowAudit.P018.secondUnit d)) = _
  rw [← he.1, ← he.2]
  have hh := (hCommon N d t (ω (SAP.P018a.firstUnit d)) (ω (SAP.P018a.secondUnit d))).1
  cases hd : dir N d t <;> simpa [hd] using hh

private theorem recordY_eq {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : SAP.P018a.RepeatedKernel U k) (K : SAP.P018a.Kernel U k)
    (dir : ∀ N : ℕ, (d : SAP.P018a.Dyad N) → Fin (R.T N d) → Bool)
    (hCommon : ∀ N d (t : Fin (R.T N d)) u v,
      R.X N d t u v = (if dir N d t then K.X v u else K.X u v) ∧
      R.Y N d t u v = (if dir N d t then K.Y v u else K.Y u v))
    (d : SAP.P018a.Dyad N) (t : Fin (R.T N d)) (ω : Fin N → U) :
    AronowAudit.P018.repeatedY (SAP.P018a.Bridge.toRepeated R) ω d t =
      K.Y (ω (if dir N d t then SAP.P018a.secondUnit d else SAP.P018a.firstUnit d))
        (ω (if dir N d t then SAP.P018a.firstUnit d else SAP.P018a.secondUnit d)) := by
  have he := SAP.P018a.Bridge.endpoints_agree d
  change R.Y N d t (ω (AronowAudit.P018.firstUnit d))
      (ω (AronowAudit.P018.secondUnit d)) = _
  rw [← he.1, ← he.2]
  have hh := (hCommon N d t (ω (SAP.P018a.firstUnit d)) (ω (SAP.P018a.secondUnit d))).2
  cases hd : dir N d t <;> simpa [hd] using hh

theorem T10_L1_main : SAP.P018a.WH.W1.T10_L1 := by
  intro U _ k R K dir v C H hS
  rcases hS with ⟨hK, hDR, _, _, _⟩
  rcases hDR with ⟨hμ, _, hCommon⟩
  haveI : IsProbabilityMeasure K.μ := hK.1
  haveI : IsProbabilityMeasure R.μ := by rw [hμ]; exact hK.1
  constructor
  · constructor
    · intro N d t
      let i : Fin N := if dir N d t then SAP.P018a.secondUnit d else SAP.P018a.firstUnit d
      let j : Fin N := if dir N d t then SAP.P018a.firstUnit d else SAP.P018a.secondUnit d
      have hi : Measurable (fun ω : Fin N → U => ω i) := measurable_pi_apply i
      have hj : Measurable (fun ω : Fin N → U => ω j) := measurable_pi_apply j
      have hp : Measurable (fun ω : Fin N → U => (ω i, ω j)) := hi.prodMk hj
      have hx (ω : Fin N → U) :
          AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t = K.X (ω i) (ω j) := by
        simpa only [i, j] using recordX_eq R K dir hCommon d t ω
      have hy (ω : Fin N → U) :
          AronowAudit.P018.repeatedY (SAP.P018a.Bridge.toRepeated R) ω d t = K.Y (ω i) (ω j) := by
        simpa only [i, j] using recordY_eq R K dir hCommon d t ω
      constructor
      · have hm : Measurable (fun ω : Fin N → U => K.X (ω i) (ω j)) := by
          simpa only [Function.comp_def] using hK.2.1.comp hp
        have heq : (fun ω : Fin N → U =>
            AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t) =
            fun ω => K.X (ω i) (ω j) := funext hx
        rw [heq]
        exact hm
      · have hm : Measurable (fun ω : Fin N → U => K.Y (ω i) (ω j)) := by
          simpa only [Function.comp_def] using hK.2.2.1.comp hp
        have heq : (fun ω : Fin N → U =>
            AronowAudit.P018.repeatedY (SAP.P018a.Bridge.toRepeated R) ω d t) =
            fun ω => K.Y (ω i) (ω j) := funext hy
        rw [heq]
        exact hm
    · obtain ⟨B, hB, hb⟩ := hK.2.2.2.1
      refine ⟨B, hB, ?_⟩
      intro N d t
      let i : Fin N := if dir N d t then SAP.P018a.secondUnit d else SAP.P018a.firstUnit d
      let j : Fin N := if dir N d t then SAP.P018a.firstUnit d else SAP.P018a.secondUnit d
      have hij : i ≠ j := by
        dsimp [i, j]
        split_ifs
        · exact (endpoints_ne d).symm
        · exact endpoints_ne d
      let p : (Fin N → U) → U × U := fun ω => (ω i, ω j)
      have hp : Measurable p := (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      have hlaw : (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N).map p =
          R.μ.prod R.μ := by
        have h0 := AronowAudit.P018.Wave1.WeightedConsistency.g1_proof R.μ i j hij
        simpa [AronowAudit.P018.repeatedLaw, SAP.P018a.Bridge.toRepeated, Function.comp_def] using h0
      have hbR : ∀ᵐ uv ∂(R.μ.prod R.μ),
          ‖K.X uv.1 uv.2‖ ≤ B ∧ |K.Y uv.1 uv.2| ≤ B := by
        simpa only [hμ] using hb
      have hpair : ∀ᵐ ω ∂AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N,
          ‖K.X (ω i) (ω j)‖ ≤ B ∧ |K.Y (ω i) (ω j)| ≤ B := by
        have hh := ae_of_ae_map hp.aemeasurable (by rw [hlaw]; exact hbR)
        simpa only [Function.comp_def] using hh
      have hx (ω : Fin N → U) :
          AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t = K.X (ω i) (ω j) := by
        simpa only [i, j] using recordX_eq R K dir hCommon d t ω
      have hy (ω : Fin N → U) :
          AronowAudit.P018.repeatedY (SAP.P018a.Bridge.toRepeated R) ω d t = K.Y (ω i) (ω j) := by
        simpa only [i, j] using recordY_eq R K dir hCommon d t ω
      filter_upwards [hpair] with ω hω
      simpa only [hx, hy] using hω
  · intro N d t
    let i : Fin N := if dir N d t then SAP.P018a.secondUnit d else SAP.P018a.firstUnit d
    let j : Fin N := if dir N d t then SAP.P018a.firstUnit d else SAP.P018a.secondUnit d
    have hij : i ≠ j := by
      dsimp [i, j]
      split_ifs
      · exact (endpoints_ne d).symm
      · exact endpoints_ne d
    have hlaw : (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N).map
        (fun ω : Fin N → U => (ω i, ω j)) = R.μ.prod R.μ := by
      have h0 := AronowAudit.P018.Wave1.WeightedConsistency.g1_proof R.μ i j hij
      simpa [AronowAudit.P018.repeatedLaw, SAP.P018a.Bridge.toRepeated, Function.comp_def] using h0
    have hx (ω : Fin N → U) :
        AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t = K.X (ω i) (ω j) := by
      simpa only [i, j] using recordX_eq R K dir hCommon d t ω
    have hy (ω : Fin N → U) :
        AronowAudit.P018.repeatedY (SAP.P018a.Bridge.toRepeated R) ω d t = K.Y (ω i) (ω j) := by
      simpa only [i, j] using recordY_eq R K dir hCommon d t ω
    have hp : Measurable (fun ω : Fin N → U => (ω i, ω j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    constructor
    · ext a b
      change (∫ ω, AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t a *
        AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t b ∂
          AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N) =
        ∫ uv : U × U, K.X uv.1 uv.2 a * K.X uv.1 uv.2 b ∂(R.μ.prod R.μ)
      simp_rw [hx]
      rw [← hlaw]
      exact (integral_map_of_stronglyMeasurable hp
        (((measurable_pi_apply a).comp hK.2.1).mul
          ((measurable_pi_apply b).comp hK.2.1)).stronglyMeasurable).symm
    · ext a
      change (∫ ω, AronowAudit.P018.repeatedY (SAP.P018a.Bridge.toRepeated R) ω d t *
        AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t a ∂
          AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N) =
        ∫ uv : U × U, K.Y uv.1 uv.2 * K.X uv.1 uv.2 a ∂(R.μ.prod R.μ)
      simp_rw [hx, hy]
      rw [← hlaw]
      exact (integral_map_of_stronglyMeasurable hp
        (hK.2.2.1.mul ((measurable_pi_apply a).comp hK.2.1)).stronglyMeasurable).symm

end SAP.P018a.WH.W1.P.T10_L1

theorem SAP.P018a.WH.W1.T10_L1_proof : SAP.P018a.WH.W1.T10_L1 :=
  SAP.P018a.WH.W1.P.T10_L1.T10_L1_main
end
