import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

namespace AronowAudit.P015.RandomizationKernelCompletion
open MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000

theorem condIndepFun_of_indep_joint {Ω A B C : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Ω → A) (Y : Ω → B) (X : Ω → C)
    (hD : Measurable D) (hY : Measurable Y) (hX : Measurable X)
    (h : IndepFun D (fun s => (Y s,X s)) P) :
    CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le Y D P := by
  classical
  have hYX : Measurable (fun s => (Y s,X s)) := hY.prodMk hX
  let mX := MeasurableSpace.comap X inferInstance
  let mYX := MeasurableSpace.comap (fun s => (Y s,X s)) inferInstance
  have hYX' : Measurable[mYX] (fun s => (Y s,X s)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hY' : Measurable[mYX] Y := measurable_fst.comp hYX'
  have hX' : Measurable[mYX] X := measurable_snd.comp hYX'
  have hXX : mX ≤ mYX := hX'.comap_le
  have hIX : IndepFun D X P := by
    convert h.comp measurable_id measurable_snd using 1 <;> rfl
  apply (condIndepFun_iff_condExp_inter_preimage_eq_mul hY hD).mpr
  intro s t hs ht
  let f : Ω → ℝ := (Y ⁻¹' s).indicator (fun _ => 1)
  let g : Ω → ℝ := (D ⁻¹' t).indicator (fun _ => 1)
  have hfi : Integrable f P := (integrable_const (1:ℝ)).indicator (hY hs)
  have hgi : Integrable g P := (integrable_const (1:ℝ)).indicator (hD ht)
  have hfg_eq : f*g=((Y ⁻¹' s)∩(D ⁻¹' t)).indicator (fun _ => 1) := by
    ext a
    by_cases hy : Y a∈s <;> by_cases hd : D a∈t <;> simp [f,g,hy,hd]
  have hfgi : Integrable (f*g) P := by
    rw [hfg_eq]
    exact (integrable_const (1:ℝ)).indicator ((hY hs).inter (hD ht))
  have hgD : StronglyMeasurable[MeasurableSpace.comap D inferInstance] g := by
    apply stronglyMeasurable_const.indicator
    exact (measurable_iff_comap_le.mpr le_rfl :
      Measurable[MeasurableSpace.comap D inferInstance] D) ht
  have hgYX : P[g|mYX]=ᵐ[P] fun _ => ∫a,g a∂P :=
    condExp_indep_eq hD.comap_le hYX.comap_le hgD ((IndepFun_iff_Indep _ _ _).mp h)
  have hgX : P[g|mX]=ᵐ[P] fun _ => ∫a,g a∂P :=
    condExp_indep_eq hD.comap_le hX.comap_le hgD ((IndepFun_iff_Indep _ _ _).mp hIX)
  have hfYX : StronglyMeasurable[mYX] f := stronglyMeasurable_const.indicator (hY' hs)
  have hprod : P[f*g|mYX]=ᵐ[P] fun a => (∫b,g b∂P)*f a := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hfYX hfgi hgi,hgYX] with a ha hb
    simpa [hb,mul_comm] using ha
  have houter := condExp_congr_ae (m:=mX) hprod
  have htower := condExp_condExp_of_le (μ:=P) (f:=f*g) hXX hYX.comap_le
  have hscale := condExp_smul (μ:=P) (∫a,g a∂P) f mX
  have hresult : P[f*g|mX]=ᵐ[P] fun a => P[f|mX] a*P[g|mX] a := by
    filter_upwards [houter,htower,hscale,hgX] with a ho htw hsc hgx
    change P[P[f*g|mYX]|mX] a=P[(∫b,g b∂P) • f|mX] a at ho
    rw [htw] at ho
    rw [ho,hsc,hgx]
    simp [mul_comm]
  simpa only [hfg_eq] using hresult

end
end AronowAudit.P015.RandomizationKernelCompletion
