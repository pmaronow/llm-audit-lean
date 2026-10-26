/-
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.DonskerBracketing
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.Characterization
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Envelopes and separability from finite bracketing entropy

This file derives two consequences of a finite bracketing-entropy integral
`J_{[]}(1, F, L₂(P)) < ∞`:

* a square-integrable envelope (`exists_l2_envelope_of_entropyIntegral`);
* separability of the centred Gaussian Hilbert space
  (`separableSpace_gpH_of_entropyIntegral`, via `totallyBounded_L2`).

Infinite-dimensionality of the centred Gaussian Hilbert carrier is not implied
by finite bracketing entropy.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), Theorem 19.5
(book p.270), §19.2.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Square-integrable envelope from a finite bracketing-entropy integral.**

If `J_{[]}(1, F, L₂(P)) < ∞`, then `F` has a measurable, `L²(P)` envelope `G`:
extract a finite `1`-bracketing cover `{[l_i, u_i]}_{i<k}`
(`hasFiniteBracketingCover_of_entropyIntegral_lt_top`) and take
`G := ∑_i (|l_i| + |u_i|)`. Each `f ∈ F` lies in some bracket `[l_i, u_i]`, so
`|f| ≤ |l_i| + |u_i| ≤ G` (the other summands are nonnegative); `G ∈ L²(P)` because
each bracket bound is in `L²(P)`. -/
lemma exists_l2_envelope_of_entropyIntegral
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    ∃ G, IsEnvelope F G ∧ MemLp G 2 P := by
  obtain ⟨k, l, u, hbr, hcov⟩ :=
    hasFiniteBracketingCover_of_entropyIntegral_lt_top h_int (by norm_num : (0 : ℝ) < 1)
  refine ⟨fun x => ∑ i : Fin k, (|l i x| + |u i x|), ?_, ?_⟩
  · -- envelope: `|f x| ≤ |l i x| + |u i x| ≤ ∑ j, (|l j x| + |u j x|)`.
    intro f hf x
    obtain ⟨i, hi⟩ := hcov f hf
    have h_abs_le : |f x| ≤ |l i x| + |u i x| := by
      rcases le_or_gt 0 (f x) with hfx | hfx
      · rw [abs_of_nonneg hfx]
        have h1 : f x ≤ |u i x| := (hi x).2.trans (le_abs_self _)
        linarith [abs_nonneg (l i x)]
      · rw [abs_of_neg hfx]
        have h3 : -(l i x) ≤ |l i x| := neg_le_abs _
        linarith [(hi x).1, abs_nonneg (u i x)]
    refine h_abs_le.trans ?_
    have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin k)), 0 ≤ |l j x| + |u j x| :=
      fun j _ => by positivity
    exact Finset.single_le_sum (f := fun j => |l j x| + |u j x|)
      h_nonneg (Finset.mem_univ i)
  · -- `L²`: a finite sum of `|l i| + |u i| ∈ L²(P)`.
    refine memLp_finsetSum _ ?_
    intro i _
    exact (MemLp.abs (hbr i).memLp_lower).add (MemLp.abs (hbr i).memLp_upper)

/-- **Separability of the centred Gaussian Hilbert space from a finite
bracketing-entropy integral.**

`gpH` is the topological closure of the span of `{centredLp f : f ∈ ↥F}` in
`L²(P)`. A finite bracketing-entropy integral makes `F` totally bounded in the
`L²(P)` semimetric (`totallyBounded_L2`); the centring map `centredLp` is
`1`-Lipschitz (`norm_gpEmbed_sub_le`), so the range of `centredLp` is totally
bounded in `L²(P)`, hence separable (`TotallyBounded.isSeparable`). Separability is
preserved by `Submodule.span` (`TopologicalSpace.IsSeparable.span`) and by
topological `closure` (`TopologicalSpace.IsSeparable.closure`), so `gpH` is a
separable subspace; `TopologicalSpace.IsSeparable.separableSpace` turns that into
`SeparableSpace ↥gpH`.

Thus `hH_sep` follows from `hF_ent` through `totallyBounded_L2`. -/
lemma separableSpace_gpH_of_entropyIntegral
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    (hF_env : ∃ G, IsEnvelope F G ∧ MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f) :
    TopologicalSpace.SeparableSpace ↥(gpH hF_env hF_meas) := by
  classical
  -- The range of the centred embedding `centredLp : ↥F → L²(P)`.
  set R : Set (Lp ℝ 2 P) := Set.range (fun f : ↥F => centredLp hF_env hF_meas f) with hR
  -- STEP 1: `R` is totally bounded in `L²(P)`, by Lipschitz image of totally-bounded `↥F`.
  obtain ⟨G, hG_env, hG⟩ := id hF_env
  let inst := distL2PseudoMetric hG_env hG hF_meas
  have hFtb : @TotallyBounded ↥F inst.toUniformSpace Set.univ :=
    totallyBounded_F hG_env hG hF_meas h_int
  -- `centredLp` is `1`-Lipschitz: `‖centredLp s − centredLp t‖ ≤ dist s t = distL2 P s t`.
  have hLip : @LipschitzWith ↥F (Lp ℝ 2 P) inst.toPseudoEMetricSpace _ 1
      (fun f : ↥F => centredLp hF_env hF_meas f) := by
    rw [@lipschitzWith_iff_dist_le_mul ↥F (Lp ℝ 2 P) inst _ _ _]
    intro s t
    rw [NNReal.coe_one, one_mul]
    -- `dist (centredLp s) (centredLp t) = ‖centredLp s − centredLp t‖`.
    rw [dist_eq_norm]
    -- `‖centredLp s − centredLp t‖_{Lp} = ‖gpEmbed s − gpEmbed t‖_{gpH}` ≤ distL2.
    have hcoe : (centredLp hF_env hF_meas s - centredLp hF_env hF_meas t : Lp ℝ 2 P)
        = ((gpEmbed hF_env hF_meas s - gpEmbed hF_env hF_meas t :
            ↥(gpH hF_env hF_meas)) : Lp ℝ 2 P) := by
      rw [Submodule.coe_sub, coe_gpEmbed, coe_gpEmbed]
    rw [hcoe, Submodule.norm_coe]
    -- `dist s t = distL2 P s t` under the pseudometric.
    change ‖gpEmbed hF_env hF_meas s - gpEmbed hF_env hF_meas t‖ ≤ distL2 P (s : Ω → ℝ) (t : Ω → ℝ)
    exact norm_gpEmbed_sub_le hF_env hF_meas s t
  have hRtb : TotallyBounded R := by
    have := @TotallyBounded.image ↥F (Lp ℝ 2 P) inst.toUniformSpace _ _ _ hFtb
      hLip.uniformContinuous
    rwa [Set.image_univ] at this
  -- STEP 2: totally bounded ⟹ separable.
  have hRsep : TopologicalSpace.IsSeparable R := hRtb.isSeparable
  -- STEP 3: span + closure preserve separability; `gpH` is the closure of the span.
  have hspan : TopologicalSpace.IsSeparable
      (↑(Submodule.span ℝ R) : Set (Lp ℝ 2 P)) := hRsep.span
  have hgpH : TopologicalSpace.IsSeparable (↑(gpH hF_env hF_meas) : Set (Lp ℝ 2 P)) := by
    have : (↑(gpH hF_env hF_meas) : Set (Lp ℝ 2 P))
        = closure (↑(Submodule.span ℝ R) : Set (Lp ℝ 2 P)) := by
      rw [gpH, Submodule.topologicalClosure_coe]
    rw [this]
    exact hspan.closure
  -- STEP 4: separable set ⟹ `SeparableSpace` of the subtype.
  exact hgpH.separableSpace


end AsymptoticStatistics.EmpiricalProcess
