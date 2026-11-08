import SAP.P022.WH.W1.Leaves
import AronowAudit.Shared.MapTailB.QuantileBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P022.WH.W1.P.T17_L3

open SAP.P022 MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

theorem integral_coordinate_eq (H J : JointLaw) (hJ : J ∈ compatibleLaws H)
    (t : Bool) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ p, f (if t then p.1 else p.2) ∂(J : Measure (ℝ × ℝ))) =
      ∫ p, f (if t then p.1 else p.2) ∂(H : Measure (ℝ × ℝ)) := by
  obtain ⟨hfst, hsnd⟩ :=
    (TailB_compatibleLaws_iff_marginals H J).mp hJ
  cases t
  · change (∫ p, f p.2 ∂(J : Measure (ℝ × ℝ))) =
      ∫ p, f p.2 ∂(H : Measure (ℝ × ℝ))
    calc
      _ = ∫ x, f x ∂((J : Measure (ℝ × ℝ)).map Prod.snd) := by
        symm
        exact integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable
      _ = ∫ x, f x ∂((H : Measure (ℝ × ℝ)).map Prod.snd) := by rw [hsnd]
      _ = _ := integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable
  · change (∫ p, f p.1 ∂(J : Measure (ℝ × ℝ))) =
      ∫ p, f p.1 ∂(H : Measure (ℝ × ℝ))
    calc
      _ = ∫ x, f x ∂((J : Measure (ℝ × ℝ)).map Prod.fst) := by
        symm
        exact integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable
      _ = ∫ x, f x ∂((H : Measure (ℝ × ℝ)).map Prod.fst) := by rw [hfst]
      _ = _ := integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable

theorem compatible_class_eq (H J : JointLaw) (hJ : J ∈ compatibleLaws H) :
    compatibleLaws J = compatibleLaws H := by
  apply Set.ext
  intro K
  constructor
  · intro hK t x
    exact (hK t x).trans (hJ t x)
  · intro hK t x
    exact (hK t x).trans (hJ t x).symm

theorem third_moments_of_compatible (H J : JointLaw)
    (hH : LawThirdMomentsFinite H) (hJ : J ∈ compatibleLaws H) :
    LawThirdMomentsFinite J := by
  obtain ⟨hfst, hsnd⟩ :=
    (TailB_compatibleLaws_iff_marginals H J).mp hJ
  intro t
  cases t
  · change Integrable (fun p : ℝ × ℝ => |p.2| ^ 3) (J : Measure (ℝ × ℝ))
    have hf : Measurable (fun x : ℝ => |x| ^ 3) := by fun_prop
    have hmf : AEStronglyMeasurable (fun x : ℝ => |x| ^ 3)
        ((H : Measure (ℝ × ℝ)).map Prod.snd) :=
      hf.aestronglyMeasurable
    have hHmap : Integrable (fun x : ℝ => |x| ^ 3)
        ((H : Measure (ℝ × ℝ)).map Prod.snd) := by
      apply (integrable_map_measure hmf measurable_snd.aemeasurable).2
      simpa [Function.comp_def] using hH false
    have hJmap : Integrable (fun x : ℝ => |x| ^ 3)
        ((J : Measure (ℝ × ℝ)).map Prod.snd) := by
      rw [hsnd]
      exact hHmap
    have hmfJ : AEStronglyMeasurable (fun x : ℝ => |x| ^ 3)
        ((J : Measure (ℝ × ℝ)).map Prod.snd) :=
      hf.aestronglyMeasurable
    simpa [Function.comp_def] using
      (integrable_map_measure hmfJ measurable_snd.aemeasurable).1 hJmap
  · change Integrable (fun p : ℝ × ℝ => |p.1| ^ 3) (J : Measure (ℝ × ℝ))
    have hf : Measurable (fun x : ℝ => |x| ^ 3) := by fun_prop
    have hmf : AEStronglyMeasurable (fun x : ℝ => |x| ^ 3)
        ((H : Measure (ℝ × ℝ)).map Prod.fst) :=
      hf.aestronglyMeasurable
    have hHmap : Integrable (fun x : ℝ => |x| ^ 3)
        ((H : Measure (ℝ × ℝ)).map Prod.fst) := by
      apply (integrable_map_measure hmf measurable_fst.aemeasurable).2
      simpa [Function.comp_def] using hH true
    have hJmap : Integrable (fun x : ℝ => |x| ^ 3)
        ((J : Measure (ℝ × ℝ)).map Prod.fst) := by
      rw [hfst]
      exact hHmap
    have hmfJ : AEStronglyMeasurable (fun x : ℝ => |x| ^ 3)
        ((J : Measure (ℝ × ℝ)).map Prod.fst) :=
      hf.aestronglyMeasurable
    simpa [Function.comp_def] using
      (integrable_map_measure hmfJ measurable_fst.aemeasurable).1 hJmap

theorem variance_eq_of_compatible (H J : JointLaw) (hJ : J ∈ compatibleLaws H)
    (t : Bool) : lawVariance J t = lawVariance H t := by
  have hm := TailB_lawMean_eq_of_compatible H J hJ t
  change lawMean J t = lawMean H t at hm
  unfold lawVariance
  rw [hm]
  exact integral_coordinate_eq H J hJ t (fun x => (x - lawMean H t) ^ 2) (by fun_prop)

theorem limiting_upper_eq_of_compatible (H J : JointLaw) (θ ρ : ℝ)
    (hJ : J ∈ compatibleLaws H) : limitingBound J θ ρ .H = limitingBound H θ ρ .H := by
  have hclass := compatible_class_eq H J hJ
  have hv1 := variance_eq_of_compatible H J hJ true
  have hv0 := variance_eq_of_compatible H J hJ false
  unfold limitingBound
  rw [hv1, hv0, hclass]

end

end SAP.P022.WH.W1.P.T17_L3

open MeasureTheory

theorem SAP.P022.WH.W1.T17_L3_proof : SAP.P022.WH.W1.T17_L3 := by
  classical
  intro H θ ρ hDefined hThird
  have hHH : H ∈ SAP.P022.compatibleLaws H := by
    intro t x
    rfl
  have hDefinedH := hDefined.1 H hHH
  have hL2 (t : Bool) :
      MemLp (fun p : ℝ × ℝ => if t then p.1 else p.2) 2
        (H : Measure (ℝ × ℝ)) := by
    apply (memLp_two_iff_integrable_sq (by
      cases t <;> simp <;> fun_prop)).2
    exact (hDefinedH.1 t).2.1
  have hFrechet :=
    TailB_frechet_covariance_L2 H (hL2 true) (hL2 false)
  refine ⟨?_, ?_⟩
  · intro J hJ
    exact ⟨SAP.P022.WH.W1.P.T17_L3.third_moments_of_compatible H J hThird hJ,
      SAP.P022.WH.W1.P.T17_L3.limiting_upper_eq_of_compatible H J θ ρ hJ⟩
  · rcases hFrechet with ⟨hsup, _hinf, ⟨J, hJ, hcov⟩, _⟩
    refine ⟨J, hJ, ?_⟩
    exact hcov.trans hsup.symm

