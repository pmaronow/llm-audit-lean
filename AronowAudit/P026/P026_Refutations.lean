import AronowAudit.P026.P026_FiniteDesign
namespace AronowAudit.P026.Refutations
open Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

def realAsymmetricTwo : Design (Fin 3) (Fin 2) ℝ where
  weight := fun _ => 1/3
  treatment := ![![false,false],![false,true],![true,true]]

/-- Two actual singleton clusters under the sharp null. Every stated positive
marginal, disagreement and same-arm premise holds; the printed bound fails. -/
theorem asymmetric_real_certificate :
    probabilityDesign realAsymmetricTwo ∧ positiveMarginals realAsymmetricTwo ∧
    (∀ i j : Fin 2, i≠j → 0<disagreement realAsymmetricTwo i j ∧
      0<joint realAsymmetricTwo true true i j ∧ 0<joint realAsymmetricTwo false false i j) ∧
    joint realAsymmetricTwo true false 0 1=0 ∧
    expectation realAsymmetricTwo (printedVariance realAsymmetricTwo 2 (fun _=>1) (fun _=>1))=23/8 ∧
    variance realAsymmetricTwo (ht realAsymmetricTwo 2 (fun _=>1) (fun _=>1))=27/8 := by
  norm_num [probabilityDesign,positiveMarginals,realAsymmetricTwo,disagreement,joint,marginal,
    indicator,expectation,printedVariance,estimatedPair,zeroSum,offSum,epsilon,
    variance,covariance,ht,htTotal,observed,Fin.sum_univ_succ,Fin.forall_fin_succ]

/-- Refutation of the printed universal positivity and variance assertion. -/
theorem printed_cluster_claims_refuted :
    ¬ (∀ (D : Design (Fin 3) (Fin 2) ℝ), probabilityDesign D → positiveMarginals D →
      (∀ i j, i≠j → 0<disagreement D i j) →
      (∀ x z : Fin 2 → ℝ, crossSupport D ∧
        variance D (ht D 2 x z)≤expectation D (printedVariance D 2 x z))) := by
  intro h
  have c := asymmetric_real_certificate
  have hx := (h realAsymmetricTwo c.1 c.2.1 (fun i j hij=>(c.2.2.1 i j hij).1)
    (fun _=>1) (fun _=>1)).2
  rw [c.2.2.2.2.1,c.2.2.2.2.2] at hx
  norm_num at hx

/-- Footnote 9 already fails with the identically zero fitting function. -/
theorem printed_sharp_null_footnote_refuted :
    probabilityDesign realAsymmetricTwo ∧ positiveMarginals realAsymmetricTwo ∧
    (∀ i j : Fin 2, i≠j → 0<disagreement realAsymmetricTwo i j ∧
      0<joint realAsymmetricTwo true true i j ∧ 0<joint realAsymmetricTwo false false i j) ∧
    expectation realAsymmetricTwo (printedVariance realAsymmetricTwo 2 (fun _=>1) (fun _=>1)) ≠
      variance realAsymmetricTwo (generalized realAsymmetricTwo 2 (fun _=>1) (fun _=>1) (fun _ _=>0)) := by
  have c := asymmetric_real_certificate
  refine ⟨c.1,c.2.1,c.2.2.1,?_⟩
  have hg : generalized realAsymmetricTwo 2 (fun _=>1) (fun _=>1) (fun _ _=>0)=
      ht realAsymmetricTwo 2 (fun _=>1) (fun _=>1) := by
    ext w
    simp [generalized,generalizedTotal,ht,htTotal]
  rw [hg,c.2.2.2.2.1,c.2.2.2.2.2]
  norm_num

theorem printed_table_columns_refuted : ¬ (
(∃! β, logitMaximizer false β) ∧ (∃! β, logitMaximizer true β) ∧
    rounded3 (expectation tableDesign feEstimate) (-12/1000) ∧
    rounded3 (variance tableDesign feEstimate) (36/1000) ∧
    roundedSD3 (variance tableDesign feEstimate) (191/1000) ∧
    roundedSD3 (variance tableDesign feEstimate+(expectation tableDesign feEstimate)^2) (191/1000) ∧
    roundedSD3 (variance tableDesign (ht tableDesign 16 tableLinearResidual tableLinearResidual)) (162/1000) ∧
    rounded3 (variance tableDesign (ht tableDesign 16 tableLinearResidual tableLinearResidual)) (26/1000) ∧
    rounded3 (expectation tableDesign (printedVariance tableDesign 16 tableLinearResidual tableLinearResidual)) (26/1000) ∧
    roundedSD3 (variance tableDesign (printedVariance tableDesign 16 tableLinearResidual tableLinearResidual)) (7/1000) ∧
    |Real.sqrt (variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual))-170/1000| ≤ 1/2000 ∧
    |variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual)-29/1000| ≤ 1/2000 ∧
    |expectation realTableDesign (printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual)-29/1000| ≤ 1/2000 ∧
    |Real.sqrt (variance realTableDesign (printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual))-7/1000| ≤ 1/2000) := by
  intro h
  have hx := h.2.2.2.2.2.2.1
  rw [table_linear_moments.2.1] at hx
  norm_num [roundedSD3] at hx

/-- Table 2 corrections for G (Linear), FE (Cov.) moments, HT and G (Prior).
The logistic column is handled by `logit_table_corrected`. -/
theorem table2_correction_T7 :
(expectation tableDesign (ht tableDesign 16 tableLinearResidual tableLinearResidual)=0 ∧
    variance tableDesign (ht tableDesign 16 tableLinearResidual tableLinearResidual)=38307/634880 ∧
    expectation tableDesign (printedVariance tableDesign 16 tableLinearResidual tableLinearResidual)=38307/634880 ∧
    variance tableDesign (printedVariance tableDesign 16 tableLinearResidual tableLinearResidual)=
      2400328658503/15687787688755200)
    ∧ (roundedSD3 (38307/634880) (246/1000) ∧ rounded3 (38307/634880) (60/1000) ∧
    roundedSD3 (2400328658503/15687787688755200) (12/1000))
    ∧ ((-145/10000 : ℚ) < expectation tableDesign feEstimate ∧
    expectation tableDesign feEstimate < -135/10000 ∧
    (775/10000 : ℚ) < variance tableDesign feEstimate ∧
    variance tableDesign feEstimate < 785/10000 ∧
    roundedSD3 (variance tableDesign feEstimate) (279/1000) ∧
    roundedSD3 (variance tableDesign feEstimate+(expectation tableDesign feEstimate)^2) (279/1000) ∧
    (38307/634880 : ℚ) < variance tableDesign feEstimate+(expectation tableDesign feEstimate)^2)
    ∧ ((∀ k, clusterTotal tableCluster tableY k=tableClusterY k ∧
      clusterTotal tableCluster (fun i => tableY i-1/2) k=tablePriorResidual k) ∧
    expectation tableDesign (ht tableDesign 16 tableClusterY tableClusterY)=0 ∧
    variance tableDesign (ht tableDesign 16 tableClusterY tableClusterY)=353/1920 ∧
    expectation tableDesign (printedVariance tableDesign 16 tableClusterY tableClusterY)=353/1920 ∧
    expectation tableDesign (ht tableDesign 16 tablePriorResidual tablePriorResidual)=0 ∧
    variance tableDesign (ht tableDesign 16 tablePriorResidual tablePriorResidual)=233/2560 ∧
    expectation tableDesign (printedVariance tableDesign 16 tablePriorResidual tablePriorResidual)=233/2560 ∧
    rounded3 (353/1920) (184/1000) ∧ rounded3 (233/2560) (91/1000)) :=
  ⟨table_linear_moments,table_linear_corrected_rounding,fe_table_moments,table_unchanged_columns⟩

def realXorThree : Design (Fin 4) (Fin 3) ℝ where
  weight := fun _ => 1/4
  treatment := ![![false,false,false],![false,true,true],![true,false,true],![true,true,false]]

def xorFittingSet : Finset (Fin 3) := univ.erase 0

def xorFit (y : ↥xorFittingSet → ℝ) : ℝ :=
  y ⟨1,by decide⟩+y ⟨2,by decide⟩-2*y ⟨1,by decide⟩*y ⟨2,by decide⟩

lemma xor_pairwise_independent (i j : Fin 3) (hij : i≠j) :
    independent realXorThree (fun w=>realXorThree.treatment w i)
      (fun w=>realXorThree.treatment w j) := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | intro u v
      norm_num [expectation,realXorThree,Fin.sum_univ_succ]
      ring

/-- The pairwise fitting premise holds for each input to the actual XOR
fit of the two other observed outcomes, while its covariance is nonzero. -/
theorem printed_pairwise_fitting_refuted :
    probabilityDesign realXorThree ∧ positiveMarginals realXorThree ∧
    (∀ j∈xorFittingSet, independent realXorThree
      (fun w=>realXorThree.treatment w 0) (fun w=>realXorThree.treatment w j)) ∧
    covariance realXorThree (fun w=>indicator realXorThree true w 0)
      (fun w=>xorFit (fittingOutcomes realXorThree xorFittingSet (fun _=>1) (fun _=>0) w))≠0 := by
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [probabilityDesign,expectation,realXorThree,Fin.sum_univ_succ]
  · norm_num [positiveMarginals,marginal,indicator,expectation,realXorThree,
      Fin.forall_fin_succ,Fin.sum_univ_succ]
  · intro j hj
    exact xor_pairwise_independent 0 j (Finset.mem_erase.mp hj).1.symm
  · norm_num [covariance,expectation,indicator,fittingOutcomes,xorFit,realXorThree,
      observed,Fin.sum_univ_succ]

end
end AronowAudit.P026.Refutations
