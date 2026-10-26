import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Condexp
namespace AronowAudit.P015.ConditionalCompletion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

lemma ae_indep_condExpKernel {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m≤mΩ)
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hi : CondIndepFun m hm f g P) :
    ∀ᵐ s ∂P, IndepFun f g (condExpKernel P m s) := by
  have hh:=ae_of_ae_trim hm ((condIndepFun_iff_map_prod_eq_prod_map_map hf hg).mp hi)
  filter_upwards [hh] with s hs
  apply (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mpr
  rw [Kernel.map_apply _ (hf.prodMk hg),Kernel.prod_apply,Kernel.map_apply _ hf,Kernel.map_apply _ hg] at hs
  exact hs

lemma condExp_product {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m≤mΩ)
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hi : CondIndepFun m hm f g P) (hfi : Integrable f P) (hgi : Integrable g P)
    (hp : Integrable (fun s=>f s*g s) P) :
    P[(fun s=>f s*g s)|m]=ᵐ[P] fun s=>P[f|m] s*P[g|m] s := by
  filter_upwards [ae_indep_condExpKernel P hm f g hf hg hi,
    condExp_ae_eq_integral_condExpKernel hm hfi,
    condExp_ae_eq_integral_condExpKernel hm hgi,
    condExp_ae_eq_integral_condExpKernel hm hp] with s hs hf' hg' hp'
  rw [hp',hf',hg']
  exact hs.integral_fun_mul_eq_mul_integral hf.aestronglyMeasurable hg.aestronglyMeasurable

lemma ae_kernel_constant {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m≤mΩ)
    (f : Ω → ℝ) (hf : Measurable[m] f) :
    ∀ᵐ s ∂P, ∀ᵐ t ∂condExpKernel P m s, f t=f s := by
  letI : MeasurableSpace (Ω×Ω):=m.prod mΩ
  have hh : ∀ᵐ st ∂(P.trim hm) ⊗ₘ condExpKernel P m, f st.2=f st.1 := by
    rw [compProd_trim_condExpKernel hm]
    have hd : @Measurable Ω (Ω×Ω) mΩ (m.prod mΩ) Function.diag :=
      (measurable_id'' hm).prodMk measurable_id
    apply (ae_map_iff hd.aemeasurable (measurableSet_eq_fun
      ((hf.mono hm le_rfl).comp measurable_snd) (hf.comp measurable_fst))).mpr
    exact Eventually.of_forall (fun _=>rfl)
  exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_compProd hh)


end
end AronowAudit.P015.ConditionalCompletion
