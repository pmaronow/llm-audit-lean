import AronowAudit.P001.Wave1.PdaMeanNotIdentifiedBlueprint
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N7
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N9
import Mathlib.Analysis.Calculus.FDeriv.Extend

namespace AronowAudit.P001.Wave1.PdaMeanNotIdentified

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidablePdaMeanNotIdentifiedN8 (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem n8_proof : N8 := by
  have hc : Continuous pdaBump := by
    have hp : Continuous (fun x : ℝ => x * (1 - x ^ 2) ^ 2) := by fun_prop
    unfold pdaBump
    apply Continuous.if _ hp continuous_const
    intro x hx
    have hxabs : |x| = 1 := (frontier_lt_subset_eq continuous_abs continuous_const) hx
    rcases (abs_eq zero_le_one).mp hxabs with hx | hx <;> rw [hx] <;> norm_num
  -- The interval s excludes both endpoints; its derivative agrees with N9's
  -- continuous function. The same helper handles either choice of endpoint.
  have hleft : ∀ (e : ℝ) (s : Set ℝ), s ∈ nhdsWithin e (Set.Iio e) →
      (∀ x ∈ s, |x| ≠ 1) → HasDerivWithinAt pdaBump (pdaBumpDeriv e) (Set.Iic e) e := by
    intro e s hs hne
    have hd : DifferentiableOn ℝ pdaBump s := fun x hx =>
      (n7_proof x (hne x hx)).differentiableAt.differentiableWithinAt
    apply hasDerivWithinAt_Iic_of_tendsto_deriv hd (hc.continuousAt.continuousWithinAt) hs
    have ht : Tendsto pdaBumpDeriv (nhdsWithin e (Set.Iio e))
        (nhds (pdaBumpDeriv e)) := tendsto_inf_left n9_proof.continuousAt
    apply ht.congr'
    filter_upwards [hs] with x hx
    exact (n7_proof x (hne x hx)).deriv.symm
  have hright : ∀ (e : ℝ) (s : Set ℝ), s ∈ nhdsWithin e (Set.Ioi e) →
      (∀ x ∈ s, |x| ≠ 1) → HasDerivWithinAt pdaBump (pdaBumpDeriv e) (Set.Ici e) e := by
    intro e s hs hne
    have hd : DifferentiableOn ℝ pdaBump s := fun x hx =>
      (n7_proof x (hne x hx)).differentiableAt.differentiableWithinAt
    apply hasDerivWithinAt_Ici_of_tendsto_deriv hd (hc.continuousAt.continuousWithinAt) hs
    have ht : Tendsto pdaBumpDeriv (nhdsWithin e (Set.Ioi e))
        (nhds (pdaBumpDeriv e)) := tendsto_inf_left n9_proof.continuousAt
    apply ht.congr'
    filter_upwards [hs] with x hx
    exact (n7_proof x (hne x hx)).deriv.symm
  have h1l := hleft 1 (Set.Ioo 0 1) (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))
    (fun x hx => by rw [abs_of_pos hx.1]; exact ne_of_lt hx.2)
  have h1r := hright 1 (Set.Ioi 1) self_mem_nhdsWithin
    (fun x hx => by
      have hx' : (1 : ℝ) < x := hx
      rw [abs_of_pos (by linarith : 0 < x)]; exact ne_of_gt hx')
  have hml := hleft (-1) (Set.Iio (-1)) self_mem_nhdsWithin
    (fun x hx => by
      have hx' : x < -1 := hx
      rw [abs_of_neg (by linarith : x < 0)]; intro h; linarith)
  have hmr := hright (-1) (Set.Ioo (-1) 0)
    (Ioo_mem_nhdsGT (by norm_num : (-1 : ℝ) < 0))
    (fun x hx => by rw [abs_of_neg hx.2]; intro h; linarith [hx.1])
  constructor
  · simpa [Set.Iic_union_Ici, pdaBumpDeriv] using h1l.union h1r
  · simpa [Set.Iic_union_Ici, pdaBumpDeriv] using hml.union hmr

end
end AronowAudit.P001.Wave1.PdaMeanNotIdentified
