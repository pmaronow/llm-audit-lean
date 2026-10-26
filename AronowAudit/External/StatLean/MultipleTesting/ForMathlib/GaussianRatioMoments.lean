/-
Local file of llm-audit-lean, not taken from StatLean; it builds on the vendored StatLean code in this directory tree.
-/
import AronowAudit.External.StatLean.MultipleTesting.ForMathlib.ChiSquaredInverseMoment
import AronowAudit.External.Causalean.Stat.CLT.ChiSquaredProjection

/-! Exact Student ratio moment using product-coordinate splitting.
No distributional law or moment identity is assumed. -/

namespace AronowAudit.GaussianCompletion
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators
noncomputable section
set_option maxHeartbeats 1000000

theorem integral_gaussian_ratio_sq {ν : ℕ} (hν : 2<ν) :
    (∫ z : Fin (ν+1)→ℝ,
      (z 0/Real.sqrt ((∑ i∈Finset.univ.erase (0:Fin (ν+1)),(z i)^2)/(ν:ℝ)))^2
      ∂(Measure.pi (fun _:Fin (ν+1)=>gaussianReal 0 1)))=(ν:ℝ)/((ν:ℝ)-2) := by
  let μ : Measure (Fin (ν+1)→ℝ):=Measure.pi (fun _=>gaussianReal 0 1)
  let η : Measure (Fin ν→ℝ):=Measure.pi (fun _=>gaussianReal 0 1)
  let e : (Fin (ν+1)→ℝ) ≃ᵐ ℝ×(Fin ν→ℝ) := MeasurableEquiv.piFinSuccAbove (fun _=>ℝ) 0
  have he : μ.map e=(gaussianReal 0 1).prod η :=
    (measurePreserving_piFinSuccAbove (fun _:Fin (ν+1)=>gaussianReal 0 1) 0).map_eq
  let F : ℝ×(Fin ν→ℝ)→ℝ:=fun p=>p.1^2*((ν:ℝ)*(∑ i,(p.2 i)^2)⁻¹)
  have hfun : (fun z : Fin (ν+1)→ℝ=>
      (z 0/Real.sqrt ((∑ i∈Finset.univ.erase (0:Fin (ν+1)),(z i)^2)/(ν:ℝ)))^2)=F∘e := by
    funext z
    have hs : (∑ i∈Finset.univ.erase (0:Fin (ν+1)),(z i)^2)=
        ∑ j:Fin ν,(z ((0:Fin (ν+1)).succAbove j))^2 := by
      have ha := Fin.sum_univ_succAbove (fun i:Fin (ν+1)=>(z i)^2) 0
      have hb := Finset.sum_erase_add Finset.univ (fun i:Fin (ν+1)=>(z i)^2) (Finset.mem_univ (0:Fin (ν+1)))
      linarith
    change _=(z 0)^2*((ν:ℝ)*(∑ j:Fin ν,(z ((0:Fin (ν+1)).succAbove j))^2)⁻¹)
    have hnS : 0≤(∑ j:Fin ν,(z ((0:Fin (ν+1)).succAbove j))^2)/(ν:ℝ) :=
      div_nonneg (Finset.sum_nonneg (fun i _=>sq_nonneg _)) (Nat.cast_nonneg ν)
    rw [hs,div_pow,Real.sq_sqrt hnS]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  rw [hfun]
  change (∫ z,F (e z) ∂μ)=_
  rw [←integral_map e.measurable.aemeasurable (show AEStronglyMeasurable F (μ.map e) from by
    apply Measurable.aestronglyMeasurable
    dsimp [F]
    fun_prop),he]
  change (∫ p:ℝ×(Fin ν→ℝ),p.1^2*((ν:ℝ)*(∑ i,(p.2 i)^2)⁻¹) ∂(gaussianReal 0 1).prod η)=_
  rw [integral_prod_mul (fun x:ℝ=>x^2) (fun y:Fin ν→ℝ=>(ν:ℝ)*(∑ i,(y i)^2)⁻¹),integral_const_mul]
  have hg : (∫ x:ℝ,x^2 ∂gaussianReal 0 1)=1 := by
    have hv := variance_of_integral_eq_zero (μ:=gaussianReal 0 1) (X:=id) aemeasurable_id (integral_id_gaussianReal (μ:=0) (v:=1))
    rw [variance_id_gaussianReal] at hv
    exact hv.symm
  dsimp only [η]
  rw [hg,one_mul,integral_inv_gaussian_squares hν]
  ring

theorem gaussian_ratio_law_second_moment {ν : ℕ} (hν : 2<ν) :
    (∫ t:ℝ,t^2 ∂((Measure.pi (fun _:Fin (ν+1)=>gaussianReal 0 1)).map
      (fun z=>z 0/Real.sqrt ((∑ i∈Finset.univ.erase (0:Fin (ν+1)),(z i)^2)/(ν:ℝ)))))=
      (ν:ℝ)/((ν:ℝ)-2) := by
  rw [integral_map (show Measurable (fun z:Fin (ν+1)→ℝ=>z 0/Real.sqrt
      ((∑ i∈Finset.univ.erase (0:Fin (ν+1)),(z i)^2)/(ν:ℝ))) from by fun_prop).aemeasurable
    (by fun_prop)]
  exact integral_gaussian_ratio_sq hν

end
end AronowAudit.GaussianCompletion
