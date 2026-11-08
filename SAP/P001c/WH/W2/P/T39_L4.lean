import SAP.P001c.WH.W2.Leaves
import AronowAudit.P001.Wave1.Gap.GLP0013B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c.WH.W2.P.T39_L4

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001 AronowAudit.P001.Wave1
open scoped BigOperators ENNReal NNReal Topology Classical

noncomputable section

lemma density_marginals (mx my sx sy ρ : ℝ) (hx : 0 < sx) (hy : 0 < sy)
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) :
    let ν := volume.withDensity (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z))
    ν.map Prod.fst = gaussianReal mx (bivariate_normal_sq sx) ∧
    ν.map Prod.snd = gaussianReal my (bivariate_normal_sq sy) := by
  let ν := volume.withDensity (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z))
  let d := sy * Real.sqrt (1 - ρ ^ 2)
  let c := ρ * sy / sx
  let η := bivariate_normal_source mx sx d
  let T := bivariate_normal_transport mx my c
  have hq : 0 < 1 - ρ ^ 2 := bivariate_normal_q_pos ρ hρ
  have hd : 0 < d := mul_pos hy (Real.sqrt_pos.2 hq)
  have hEq : ν = η.map T := by
    simpa [ν, η, T, d, c, bivariate_normal_source, bivariate_normal_transport] using
      (bivariate_normal_eq_map mx my sx sy ρ hx hy hρ)
  have hXlaw : HasLaw Prod.fst (gaussianReal mx (bivariate_normal_sq sx)) η := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    simp [η, bivariate_normal_source]
  have hYlaw : HasLaw Prod.snd (gaussianReal 0 (bivariate_normal_sq d)) η := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    simp [η, bivariate_normal_source]
  have hInd : IndepFun Prod.fst Prod.snd η := by
    change IndepFun Prod.fst Prod.snd
      ((gaussianReal mx (bivariate_normal_sq sx)).prod
        (gaussianReal 0 (bivariate_normal_sq d)))
    exact indepFun_prod measurable_id measurable_id
  have hWlaw : HasLaw (fun z : ℝ × ℝ => c * (z.1 - mx))
      (gaussianReal 0 ((c ^ 2).toNNReal * bivariate_normal_sq sx)) η := by
    have h := gaussianReal_const_mul (gaussianReal_sub_const hXlaw mx) c
    refine ⟨h.aemeasurable, ?_⟩
    have hcoef : bivariate_normal_sq c = (c ^ 2).toNNReal := by
      apply Subtype.ext
      simp [bivariate_normal_sq, Real.coe_toNNReal (c ^ 2) (sq_nonneg c)]
    have hmap := h.map_eq
    rw [show c * (mx - mx) = 0 by ring] at hmap
    change Measure.map (fun z : ℝ × ℝ => c * (z.1 - mx)) η =
      gaussianReal 0 (bivariate_normal_sq c * bivariate_normal_sq sx) at hmap
    rw [← hcoef]
    exact hmap
  have hIndW : (fun z : ℝ × ℝ => c * (z.1 - mx)) ⟂ᵢ[η] Prod.snd := by
    simpa [Function.comp_def] using
      hInd.comp (φ := fun x : ℝ => c * (x - mx)) (ψ := fun y : ℝ => y)
        (by fun_prop) measurable_id
  have hSumLaw := gaussianReal_add_gaussianReal_of_indepFun hIndW hWlaw hYlaw
  have hSumHasLaw : HasLaw (fun z : ℝ × ℝ => c * (z.1 - mx) + z.2)
      (gaussianReal 0 ((c ^ 2).toNNReal * bivariate_normal_sq sx +
        bivariate_normal_sq d)) η := by
    refine ⟨by fun_prop, ?_⟩
    calc
      η.map (fun z : ℝ × ℝ => c * (z.1 - mx) + z.2) =
          η.map ((fun z : ℝ × ℝ => c * (z.1 - mx)) + Prod.snd) := by
        congr 1
      _ = gaussianReal (0 + 0)
          ((c ^ 2).toNNReal * bivariate_normal_sq sx + bivariate_normal_sq d) := hSumLaw
      _ = gaussianReal 0
          ((c ^ 2).toNNReal * bivariate_normal_sq sx + bivariate_normal_sq d) := by simp
  have hTransLaw : HasLaw (fun z : ℝ × ℝ => my + c * (z.1 - mx) + z.2)
      (gaussianReal my
        ((c ^ 2).toNNReal * bivariate_normal_sq sx +
          bivariate_normal_sq d)) η := by
    have h := gaussianReal_add_const hSumHasLaw my
    have hfun : (fun z : ℝ × ℝ => my + c * (z.1 - mx) + z.2) =ᵐ[η]
        (fun z => c * (z.1 - mx) + z.2 + my) :=
      ae_of_all _ fun z => by ring
    simpa [zero_add] using h.congr hfun
  have hscale :
      (c ^ 2).toNNReal * bivariate_normal_sq sx + bivariate_normal_sq d =
        bivariate_normal_sq sy := by
    ext
    change ((c ^ 2).toNNReal : ℝ) * sx ^ 2 + d ^ 2 = sy ^ 2
    rw [Real.coe_toNNReal (c ^ 2) (sq_nonneg c)]
    dsimp [c, d]
    rw [mul_pow, Real.sq_sqrt hq.le]
    field_simp
    ring
  constructor
  · calc
      ν.map Prod.fst = (η.map T).map Prod.fst := by rw [hEq]
      _ = η.map (Prod.fst ∘ T) :=
        Measure.map_map measurable_fst (by
          change Measurable (bivariate_normal_transport mx my c)
          unfold bivariate_normal_transport
          fun_prop)
      _ = gaussianReal mx (bivariate_normal_sq sx) := by
        rw [show Prod.fst ∘ T = Prod.fst by
          funext z
          rfl]
        exact hXlaw.map_eq
  · calc
      ν.map Prod.snd = (η.map T).map Prod.snd := by rw [hEq]
      _ = η.map (Prod.snd ∘ T) :=
        Measure.map_map measurable_snd (by
          change Measurable (bivariate_normal_transport mx my c)
          unfold bivariate_normal_transport
          fun_prop)
      _ = gaussianReal my (bivariate_normal_sq sy) := by
        rw [show Prod.snd ∘ T = (fun z : ℝ × ℝ => my + c * (z.1 - mx) + z.2) by
          funext z
          rfl]
        rw [hTransLaw.map_eq, hscale]

end

end SAP.P001c.WH.W2.P.T39_L4

universe u

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001 AronowAudit.P001.Wave1
open scoped BigOperators ENNReal NNReal Topology Classical

noncomputable section

theorem SAP.P001c.WH.W2.T39_L4_proof : SAP.P001c.WH.W2.T39_L4.{u} := by
  intro Ω mΩ μ hμ X Y hX hY mx my sx sy ρ hsx hsy hρ hjoint
  let ν : Measure (ℝ × ℝ) :=
    volume.withDensity (fun z => ENNReal.ofReal (bivariateNormalPDF mx my sx sy ρ z))
  let F : Ω → ℝ × ℝ := fun z => (X z, Y z)
  have hF : Measurable F := by
    dsimp [F]
    exact Measurable.prodMk hX hY
  have hjoint' : μ.map F = ν := by
    simpa only [F, ν, SAP.P001c.Bridge.bivariatePDF_eq] using hjoint
  have hprob : IsProbabilityMeasure ν := by
    simpa [ν] using (bivariate_normal_probability mx my sx sy ρ hsx hsy hρ).1
  have hmom := bivariate_normal_second_moments mx my sx sy ρ hsx hsy hρ
  have hmemfst : MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 ν := by
    simpa [ν] using hmom.1
  have hmemsnd : MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 ν := by
    simpa [ν] using hmom.2.1
  have hmeanCov := bivariate_normal_means_covariance mx my sx sy ρ hsx hsy hρ
  have hmeanfst : mean ν (Prod.fst : ℝ × ℝ → ℝ) = mx := by
    simpa [ν] using hmeanCov.1
  have hmeansnd : mean ν (Prod.snd : ℝ × ℝ → ℝ) = my := by
    simpa [ν] using hmeanCov.2.1
  have hcov : covariance (Prod.fst : ℝ × ℝ → ℝ) Prod.snd ν = ρ * sx * sy := by
    simpa [ν] using hmeanCov.2.2
  have hscale := bivariate_normal_variance_scales mx my sx sy ρ hsx hsy hρ
  have hrootfst : Real.sqrt (variance (Prod.fst : ℝ × ℝ → ℝ) ν) = sx := by
    simpa [ν, AronowAudit.P001.var] using hscale.1
  have hrootsnd : Real.sqrt (variance (Prod.snd : ℝ × ℝ → ℝ) ν) = sy := by
    simpa [ν, AronowAudit.P001.var] using hscale.2.1
  have hmarg := SAP.P001c.WH.W2.P.T39_L4.density_marginals mx my sx sy ρ hsx hsy hρ
  have hmargfst : ν.map Prod.fst = gaussianReal mx ⟨sx ^ 2, sq_nonneg sx⟩ := by
    simpa [ν, bivariate_normal_sq] using hmarg.1
  have hmargsnd : ν.map Prod.snd = gaussianReal my ⟨sy ^ 2, sq_nonneg sy⟩ := by
    simpa [ν, bivariate_normal_sq] using hmarg.2
  have hmapfst : μ.map X = ν.map Prod.fst := by
    calc
      μ.map X = μ.map (Prod.fst ∘ F) := by rfl
      _ = (μ.map F).map Prod.fst := (Measure.map_map measurable_fst hF).symm
      _ = ν.map Prod.fst := by rw [hjoint']
  have hmapsnd : μ.map Y = ν.map Prod.snd := by
    calc
      μ.map Y = μ.map (Prod.snd ∘ F) := by rfl
      _ = (μ.map F).map Prod.snd := (Measure.map_map measurable_snd hF).symm
      _ = ν.map Prod.snd := by rw [hjoint']
  have hlawX : μ.map X = gaussianReal mx ⟨sx ^ 2, sq_nonneg sx⟩ := hmapfst.trans hmargfst
  have hlawY : μ.map Y = gaussianReal my ⟨sy ^ 2, sq_nonneg sy⟩ := hmapsnd.trans hmargsnd
  have hmemX : MemLp X 2 μ := by
    have hcoord : MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 (μ.map F) := by
      rw [hjoint']
      exact hmemfst
    simpa [F, Function.comp_def] using hcoord.comp_of_map hF.aemeasurable
  have hmemY : MemLp Y 2 μ := by
    have hcoord : MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 (μ.map F) := by
      rw [hjoint']
      exact hmemsnd
    simpa [F, Function.comp_def] using hcoord.comp_of_map hF.aemeasurable
  have hexpectX : expectation μ X = mx := by
    change (∫ z, X z ∂μ) = mx
    calc
      (∫ z, X z ∂μ) = ∫ z, z.1 ∂μ.map F := by
        simpa [F] using
          (integral_map hF.aemeasurable measurable_fst.aestronglyMeasurable).symm
      _ = ∫ z, z.1 ∂ν := by rw [hjoint']
      _ = mx := by simpa [AronowAudit.P001.mean] using hmeanfst
  have hexpectY : expectation μ Y = my := by
    change (∫ z, Y z ∂μ) = my
    calc
      (∫ z, Y z ∂μ) = ∫ z, z.2 ∂μ.map F := by
        simpa [F] using
          (integral_map hF.aemeasurable measurable_snd.aestronglyMeasurable).symm
      _ = ∫ z, z.2 ∂ν := by rw [hjoint']
      _ = my := by simpa [AronowAudit.P001.mean] using hmeansnd
  have hvarX : variance X μ = variance Prod.fst ν := by
    rw [← hjoint']
    simpa [F, Function.comp_def] using
      (variance_map (X := Prod.fst) (Y := F) (by fun_prop) hF.aemeasurable).symm
  have hvarY : variance Y μ = variance Prod.snd ν := by
    rw [← hjoint']
    simpa [F, Function.comp_def] using
      (variance_map (X := Prod.snd) (Y := F) (by fun_prop) hF.aemeasurable).symm
  have hcovXY : covariance X Y μ = covariance (Prod.fst : ℝ × ℝ → ℝ) Prod.snd ν := by
    rw [← hjoint']
    simpa [F, Function.comp_def] using
      (covariance_map (X := Prod.fst) (Y := Prod.snd) (Z := F)
        (by fun_prop) (by fun_prop) hF.aemeasurable).symm
  have hrootX : Real.sqrt (variance X μ) = sx := by rw [hvarX]; exact hrootfst
  have hrootY : Real.sqrt (variance Y μ) = sy := by rw [hvarY]; exact hrootsnd
  have hcor : correlationCoefficient μ X Y = ρ := by
    unfold correlationCoefficient
    rw [hcovXY, hrootX, hrootY]
    rw [hcov]
    field_simp
  refine ⟨hmemX, hmemY, hlawX, hlawY, hexpectX, hexpectY, hrootX, hrootY, hcor, ?_⟩
  intro hzero
  have hρzero : ρ = 0 := hzero
  haveI : IsProbabilityMeasure ν := hprob
  have hIndCoord : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd ν := by
    simpa [ν, hρzero] using
      (bivariate_normal_zero_product mx my sx sy hsx hsy).1
  have hIndMap : ν = (ν.map Prod.fst).prod (ν.map Prod.snd) := by
    simpa using
      (indepFun_iff_map_prod_eq_prod_map_map
        measurable_fst.aemeasurable measurable_snd.aemeasurable).mp hIndCoord
  have hIndPair : μ.map F = (μ.map X).prod (μ.map Y) := by
    calc
      μ.map F = ν := hjoint'
      _ = (ν.map Prod.fst).prod (ν.map Prod.snd) := hIndMap
      _ = (μ.map X).prod (μ.map Y) := by rw [← hmapfst, ← hmapsnd]
  exact (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).2
    (by simpa [F] using hIndPair)
