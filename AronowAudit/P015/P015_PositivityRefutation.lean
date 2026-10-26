import AronowAudit.P015.P015_Regression
namespace AronowAudit.P015.PositivityRefutation
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
attribute [local instance] Classical.propDecidable

def P : Measure (Fin 4) := (1/4:ℝ≥0∞) •
  (Measure.dirac 0+Measure.dirac 1+Measure.dirac 2+Measure.dirac 3)
instance : IsProbabilityMeasure P := by
  constructor
  norm_num [P,Measure.smul_apply,Measure.add_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]
def X : Fin 4 → Fin 2 := ![0,0,1,1]
def D : Fin 4 → ℝ := ![0,1,0,2]

lemma integral_finite (μ : Measure (Fin 4)) [IsFiniteMeasure μ] (f : Fin 4 → ℝ) :
    (∫i,f i∂μ)=∑i,μ.real {i}*f i := by
  exact integral_fintype (by simpa using (IntegrableOn.of_finite (s:=Set.univ) (Set.toFinite _)))

lemma cell_means : cellMean P X D 0=1/2 ∧ cellMean P X D 1=1 := by
  have hx (x : Fin 2) : 0<P {i|X i=x} := by
    fin_cases x <;> norm_num [P,X,Measure.smul_apply,Measure.add_apply,Measure.dirac_apply',Set.indicator_apply,Pi.single_apply]
  have hi (x : Fin 2) : IsProbabilityMeasure (cellLaw P X x) :=
    PositivityCompletion.cell_probability P X x (hx x)
  have he (x : Fin 2) : cellMean P X D x=∑i,(cellLaw P X x).real {i}*D i := by
    letI := hi x
    exact integral_finite _ _
  rw [he 0,he 1]
  norm_num [cellLaw,P,X,D,Measure.real,Measure.smul_apply,Measure.add_apply,
    Measure.restrict_apply,Measure.dirac_apply',Set.indicator_apply,Pi.single_apply,Fin.sum_univ_succ]
  norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]

lemma weight_values : discreteWeight P X D = ![1/4,1/4,1,1] := by
  ext i
  fin_cases i
  · change (0-cellMean P X D 0)^2=1/4
    rw [cell_means.1];norm_num
  · change (1-cellMean P X D 0)^2=1/4
    rw [cell_means.1];norm_num
  · change (0-cellMean P X D 1)^2=1
    rw [cell_means.2];norm_num
  · change (2-cellMean P X D 1)^2=1
    rw [cell_means.2];norm_num

lemma weight_integral : (∫i,discreteWeight P X D i∂P)=5/8 := by
  rw [integral_finite]
  rw [weight_values]
  norm_num [P,Measure.real,Measure.smul_apply,Measure.add_apply,Measure.dirac_apply',Set.indicator_apply,Pi.single_apply,Fin.sum_univ_succ]

lemma cell_variance_one : cellVar P X D 1=1 := by
  have hx : 0<P {i|X i=1} := by
    norm_num [P,X,Measure.smul_apply,Measure.add_apply,Measure.dirac_apply',Set.indicator_apply]
  letI := PositivityCompletion.cell_probability P X 1 hx
  unfold cellVar
  rw [cell_means.2,integral_finite]
  norm_num [cellLaw,P,X,D,Measure.real,Measure.smul_apply,Measure.add_apply,
    Measure.restrict_apply,Measure.dirac_apply',Set.indicator_apply,Pi.single_apply,Fin.sum_univ_succ,
    ENNReal.toReal_add,ENNReal.toReal_inv]

lemma weight_integrable : Integrable (discreteWeight P X D) P := by
  simpa using (IntegrableOn.of_finite (s:=Set.univ) (Set.toFinite _))

/-- T17(C), p. 261: under the normalized withDensity effective law,
both endpoints 0 and 1 occur nominally and E[w]>0, but the positive effective
profile X=1 has zero probability at treatment 1. This refutes the printed
automatic pair-specific positivity implication. -/
theorem printed_effective_positivity_refuted :
    Measurable X ∧ Measurable D ∧ MemLp D 2 P ∧
    (0:ℝ)≠1 ∧ 0<P {i|D i=0} ∧ 0<P {i|D i=1} ∧
    Integrable (discreteWeight P X D) P ∧ (0<∫i,discreteWeight P X D i∂P) ∧
    0<discreteEffective P X D {i|X i=1} ∧
    cellProb (discreteEffective P X D) X D 1 1=0 := by
  have hX : Measurable X := measurable_of_countable _
  have hD : Measurable D := measurable_of_countable _
  have hx : 0<P {i|X i=1} := by
    norm_num [P,X,Measure.smul_apply,Measure.add_apply,Measure.dirac_apply',Set.indicator_apply]
  have hp : 0<∫i,discreteWeight P X D i∂P := by rw [weight_integral];norm_num
  have hm := PositivityCompletion.effective_cell_mass P X D hX weight_integrable 1 hx
  rw [weight_integral,cell_variance_one] at hm
  have hPm : (P {i|X i=1}).toReal=1/2 := by
    norm_num [P,X,Measure.smul_apply,Measure.add_apply,Measure.dirac_apply',Set.indicator_apply,
      ENNReal.toReal_add,ENNReal.toReal_inv]
  rw [hPm] at hm
  norm_num at hm
  have hQ : 0<discreteEffective P X D {i|X i=1} :=
    (ENNReal.toReal_pos_iff.mp (by rw [hm];norm_num)).1
  have hz : cellProb P X D 1 1=0 := by
    rw [PositivityCompletion.cellProb_ratio P X D hD]
    norm_num [P,X,D,Measure.smul_apply,Measure.add_apply,Measure.dirac_apply',Set.indicator_apply]
  refine ⟨hX,hD,?_,by norm_num,?_,?_,weight_integrable,hp,hQ,?_⟩
  · apply MemLp.of_bound hD.aestronglyMeasurable 2
    exact Filter.Eventually.of_forall (by intro i;fin_cases i <;> norm_num [D])
  · norm_num [P,D,Measure.smul_apply,Measure.add_apply,Measure.dirac_apply',Set.indicator_apply]
  · norm_num [P,D,Measure.smul_apply,Measure.add_apply,Measure.dirac_apply',Set.indicator_apply]
  · rw [PositivityCompletion.effective_cellProb P X D hX hD weight_integrable hp 1 hx
      (by rw [cell_variance_one];norm_num) 1,hz]
    simp

end
end AronowAudit.P015.PositivityRefutation
