import SAP.P037c.Defs.WholeW1
import SAP.P037c.Bridge
import AronowAudit.P037.Wave1.Gap.GLP037B4
import AronowAudit.P037.Wave1.Gap.GP037B4
import AronowAudit.P037.Wave1.Gap.GLP037B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c.WH.W1
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem t35_base : T35Statement := by
  have cert := Bridge.paired_certificate
  have hzero : (∑ i ∈ pairedObserved, directOnly pairedObserved (partner i))/5=0 := by
    norm_num [pairedObserved, directOnly, partner]
  have hnom : pairedObserved.image partner=Finset.univ \ pairedObserved := by
    ext ⟨b,t⟩
    fin_cases b <;> cases t <;> norm_num [pairedObserved, partner]
  refine ⟨cert, Bridge.own_assignment_only,
    AronowAudit.P037.paired_permutation_arithmetic.1, Bridge.split_count,
    Bridge.paired_stat_count, ?_, hzero, ?_, hnom, ?_, ?_, by norm_num⟩
  · intro b
    fin_cases b <;> norm_num [directOnly, pairedObserved]
  · have h := cert.2.2.1
    change (∑ i ∈ pairedObserved, directOnly pairedObserved (partner i))/5-
      (∑ i ∈ Finset.univ \ pairedObserved, directOnly pairedObserved (partner i))/5 = -1 at h
    linarith
  · rw [← hnom]
    have hi : ∀ i, partner (partner i)=i := AronowAudit.P037.Wave1.t35r2_partner_involutive
    simp only [Finset.image_image, Function.comp_def, hi]
    ext i
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact hj
    · intro hi
      exact ⟨i,hi,rfl⟩
  · rw [cert.2.2.2.2.1]
    norm_num

theorem t27_base : T27Statement := by
  have fit := Bridge.regression12_fit
  have sepMean : ∀ weights ∈ ({(![4,4,4,4] : Fin 4 → ℝ),![2,8,8,4]} : Set (Fin 4 → ℝ)),
      ∀ k, regression12SeparateMean weights k=if k=3 then 5 else 5/2 := by
    intro weights hw k
    rcases hw with rfl | rfl <;> fin_cases k <;>
      norm_num [regression12SeparateMean, augmentedExposureMean, regression12Y,
        regression12Potential, regression12X, Fintype.sum_prod_type, Fin.sum_univ_succ]
  refine ⟨Bridge.regression12_design, fit, Bridge.regression12_normal, sepMean, ?_, ?_,
    by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · rw [fit.2.2.2.2.1 3, fit.2.2.2.2.1 2]
    norm_num
  · rw [fit.2.2.2.2.2.1 3, fit.2.2.2.2.2.1 2]
    norm_num
  · intro k
    fin_cases k <;> norm_num [regression12Potential, regression12X,
      Fintype.sum_prod_type, Fin.sum_univ_succ]
  · intro i
    simp only [regression12Y, regression12Potential, sub_self]
  · intro weights hw
    rw [sepMean weights hw 3, sepMean weights hw 2]
    norm_num
  · rcases Bridge.regression12_design with ⟨_, _, _, _, _, _, hpi, _, _⟩
    intro ⟨k,j⟩
    rw [hpi (k,j) k]
    fin_cases k <;> norm_num

theorem t33_base : T33Statement := by
  have cert := Bridge.collapsed_certificate
  rcases cert with ⟨hn, ht, hp, hc, hpi, hX, hpoint, hm, hshift, hfull, hcol, hf0, hf1, hc0, hc1⟩
  refine ⟨Bridge.collapsed_certificate, ?_, ?_, ?_, ?_, Bridge.control_weights_positive,
    Bridge.observed_rank, Bridge.collapsed_rank⟩
  · rw [hfull, hcol]
    exact Bridge.variance_certificates_differ
  · ext ⟨i,j⟩
    change controlY (i,j)-(controlFullRow controlObserved).mulVec controlPoint (i,j)=_
    rw [Bridge.control_prediction, hpoint]
    fin_cases i <;> fin_cases j <;>
      norm_num [controlY, controlObserved, controlPiI, pairReferentRate]
  · have hv : controlVariance (fun z => controlContrast z true (fun i => controlY i+
        controlPointMean (controlExposure z i)-controlPointMean (controlObserved i)))=
        controlVariance (fun z => controlContrast z true controlResidual) := by
      unfold controlVariance
      simp_rw [hshift, sub_eq_add_neg, add_assoc]
      exact AronowAudit.P037.RegressionCompletion.finite_variance_add_const controlMass _ ht _
    exact hv.trans hfull
  · intro i
    simp [controlPi]

end SAP.P037c.WH.W1
