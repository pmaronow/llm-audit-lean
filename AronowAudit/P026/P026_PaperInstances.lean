import AronowAudit.P026.P026_CompletePaper
namespace AronowAudit.P026.PaperScope
open Finset
open scoped BigOperators
noncomputable section

/-- Independent fair assignment is a genuine positive law on the literal
allocation cube, witnessing nonvacuity of the repaired paper model. -/
def fairAssignment (I : Type*) [Fintype I] [DecidableEq I] : UnitExperiment I where
  weight := fun _ => (Fintype.card (I → Bool) : ℝ)⁻¹
  nonnegative := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  normalized := by simp
  positive := by
    intro i
    have hmass : 0 < (Fintype.card (I → Bool) : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
    constructor
    · apply hmass.trans_le
      have hh := Finset.single_le_sum
        (f:=fun w : I→Bool => (Fintype.card (I → Bool) : ℝ)⁻¹ * (if w i=true then 1 else 0))
        (fun w _ => mul_nonneg hmass.le (by split_ifs <;> norm_num))
        (Finset.mem_univ (fun _ : I => true))
      simpa using hh
    · apply hmass.trans_le
      have hh := Finset.single_le_sum
        (f:=fun w : I→Bool => (Fintype.card (I → Bool) : ℝ)⁻¹ * (if w i=false then 1 else 0))
        (fun w _ => mul_nonneg hmass.le (by split_ifs <;> norm_num))
        (Finset.mem_univ (fun _ : I => false))
      simpa using hh

theorem fairAssignment_separated {I : Type*} [Fintype I] [DecidableEq I]
    (i j : I) (hij : i≠j) : 0 < disagreement (fairAssignment I).design i j := by
  have hmass : 0 < (Fintype.card (I → Bool) : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  apply hmass.trans_le
  let w : I→Bool := fun k => if k=i then true else false
  have hh := Finset.single_le_sum
    (f:=fun v : I→Bool => (Fintype.card (I → Bool) : ℝ)⁻¹ * (if v i≠v j then 1 else 0))
    (fun v _ => mul_nonneg hmass.le (by split_ifs <;> norm_num)) (Finset.mem_univ w)
  simpa [disagreement,expectation,UnitExperiment.design,fairAssignment,w,hij.symm] using hh

def unequalFairClusters : ClusterExperiment (Fin 3) (Fin 2) where
  cluster := ![0,0,1]
  covers := by intro c;fin_cases c;exact ⟨0,rfl⟩;exact ⟨2,rfl⟩
  assignment := fairAssignment (Fin 2)

theorem unequalFairClusters_instance :
    probabilityDesign unequalFairClusters.unitDesign ∧
    positiveMarginals unequalFairClusters.unitDesign ∧
    (∀ i j, i≠j → 0 < disagreement unequalFairClusters.clusterDesign i j) :=
  ⟨unequalFairClusters.unit_probability,unequalFairClusters.unit_marginals,
    fairAssignment_separated⟩

lemma fair_product_expectation {I : Type*} [Fintype I] [DecidableEq I]
    (F : I → Bool → ℝ) :
    expectation (fairAssignment I).design (fun w=>∏i,F i (w i))=
      ∏i,((∑b : Bool,F i b)/2) := by
  have hw : (Fintype.card (I → Bool) : ℝ)⁻¹=∏i:I,(1/2:ℝ) := by
    simp [Fintype.card_fun,Nat.cast_pow,inv_pow]
  change (∑w : I→Bool,(Fintype.card (I → Bool) : ℝ)⁻¹*(∏i,F i (w i)))=_
  simp_rw [hw,←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun (i:I) (b:Bool)=>(1/2:ℝ)*F i b)]
  apply prod_congr rfl
  intro i _
  rw [←Finset.mul_sum]
  ring

lemma fair_coordinate_expectation {I : Type*} [Fintype I] [DecidableEq I]
    (j : I) (u : Bool→ℝ) :
    expectation (fairAssignment I).design (fun w=>u (w j))=(∑b : Bool,u b)/2 := by
  let F : I→Bool→ℝ := fun k b=>if k=j then u b else 1
  have hp (w : I→Bool) : (∏k,F k (w k))=u (w j) := by simp [F]
  have hh (k : I) : (∑b : Bool,F k b)/2=if k=j then (∑b : Bool,u b)/2 else 1 := by
    by_cases hk:k=j <;> simp [F,hk,Fintype.sum_bool]
  have he := fair_product_expectation F
  simp_rw [hp,hh] at he
  simpa using he

lemma fair_mutually_independent {I : Type*} [Fintype I] [DecidableEq I] :
    mutuallyIndependentAssignments (fairAssignment I).design := by
  intro F
  rw [show (fun w=>∏i,F i ((fairAssignment I).design.treatment w i))=
      (fun w=>∏i,F i (w i)) from rfl,fair_product_expectation]
  apply prod_congr rfl
  intro i _
  exact (fair_coordinate_expectation i (F i)).symm

lemma fair_singleton_blocks {I : Type*} [Fintype I] [DecidableEq I] :
    mutuallyIndependentBlocks (fairAssignment I).design (fun i : I=>i) := by
  intro F
  have hh (i : I) (w : I→Bool) :
      fittingAssignments (fairAssignment I).design (univ.filter (fun j=>j=i)) w=(fun _=>w i) := by
    funext j
    exact congrArg w (Finset.mem_filter.mp j.property).2
  simp_rw [hh]
  exact fair_mutually_independent (fun i b=>F i (fun _=>b))

lemma fair_joint_positive {I : Type*} [Fintype I] [DecidableEq I]
    (i j : I) (hij : i≠j) (a b : Bool) :
    0<joint (fairAssignment I).design a b i j := by
  have hmass : 0 < (Fintype.card (I → Bool) : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  let w : I→Bool := fun k=>if k=i then a else b
  have hh := Finset.single_le_sum
    (f:=fun v : I→Bool => (Fintype.card (I → Bool) : ℝ)⁻¹ *
      (indicator (fairAssignment I).design a v i*indicator (fairAssignment I).design b v j))
    (fun v _ => mul_nonneg hmass.le (mul_nonneg (by unfold indicator;split_ifs <;> norm_num)
      (by unfold indicator;split_ifs <;> norm_num))) (Finset.mem_univ w)
  apply hmass.trans_le
  simpa [joint,expectation,indicator,UnitExperiment.design,fairAssignment,w,hij.symm] using hh

def allUnitOLSRule {I : Type*} [Fintype I] (K : ℕ) (V : Matrix I (Fin K) ℝ) :
    PredictionRule I K K where
  covariates := V
  fit := fun _ y => (V.transpose*V)⁻¹.mulVec (V.transpose.mulVec y)
  predict := fun x β => dotProduct x β

/-- The actual all-unit OLS fit is one of the permitted fixed data-fitting
rules, and its prediction covariance gives the exact package-estimator bias. -/
theorem all_unit_OLS_bias_T16 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitExperiment I) (K : ℕ) (V : Matrix I (Fin K) ℝ)
    (hV : (V.transpose*V).det≠0) (y1 y0 : I→ℝ) :
    let f := fun w => V.mulVec ((V.transpose*V)⁻¹.mulVec (V.transpose.mulVec (observed E.design y1 y0 w)))
    expectation E.design (generalized E.design (Fintype.card I) y1 y0 f)-ate (Fintype.card I) y1 y0=
      -(∑i,covariance E.design (fun w=>indicator E.design true w i) (fun w=>f w i)*
        (1/marginal E.design true i+1/marginal E.design false i))/(Fintype.card I) :=
  generalized_bias_two_arm_T16 E y1 y0 K K (allUnitOLSRule K V)

lemma fixed_zero_prediction_application {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitExperiment I) (y1 y0 : I→ℝ) :
    expectation E.design (generalized E.design (Fintype.card I) y1 y0 (fun _ _=>0))=
      ate (Fintype.card I) y1 y0 := fixed_prediction_unbiased_T16 E y1 y0 0

/- Fresh applications bind the repaired hypotheses to literal finite laws;
no old arbitrary-Design instance is silently reused. -/
example := corrected_variance_bias_T2 unequalFairClusters
  (fun i j hij=>fairAssignment_separated i j hij) (fun _=>1) (fun _=>0)
example := support_repair_T3 unequalFairClusters
  (fun i j hij=>fairAssignment_separated i j hij)
  (fun i j hij=>fair_joint_positive i j hij true false) (fun _=>1) (fun _=>0)
example := corrected_sharp_null_T2 unequalFairClusters
  (fun i j hij=>fairAssignment_separated i j hij) (fun _=>1)
  (fun i j hij=>⟨fair_joint_positive i j hij true true,fair_joint_positive i j hij false false⟩)
example := mutually_independent_leave_out_T5 (fairAssignment (Fin 3)) fair_mutually_independent 0
example := mutually_independent_other_blocks_T5 (fairAssignment (Fin 3))
  (fun i : Fin 3=>i) fair_singleton_blocks 0
example := all_unit_OLS_bias_T16 (fairAssignment (Fin 3)) 1 (fun _ _=>1)
  (by rw [Matrix.det_fin_one];change (∑i : Fin 3,(1:ℝ)*1)≠0;norm_num [Fin.sum_univ_succ])
  (fun _=>1) (fun _=>0)

#print axioms all_unit_OLS_bias_T16
#print axioms fixed_zero_prediction_application
#print axioms fair_singleton_blocks
#print axioms fair_joint_positive
#print axioms fair_mutually_independent
#print axioms unequalFairClusters_instance
end
end AronowAudit.P026.PaperScope
