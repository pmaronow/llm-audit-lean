import AronowAudit.P011.P011_Audit
namespace AronowAudit.P011.PathFiniteCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

lemma uniform_equiv {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (e : A ≃ B) : (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype B := by
  ext b
  simp only [PMF.map_apply]
  rw [tsum_eq_single (e.symm b)]
  · simp [PMF.uniformOfFintype_apply,Fintype.card_congr e]
  · intro a ha
    have hh : b ≠ e a := by intro hh; apply ha; exact e.injective (hh.symm.trans (e.apply_symm_apply b).symm)
    simp [hh]

lemma uniformLaw_equiv {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    {n : ℕ} (e : A ≃ B) (f : B → Fin n → ℝ) :
    uniformLaw (f ∘ e) = uniformLaw f := by
  unfold uniformLaw
  rw [←PMF.map_comp,uniform_equiv]

lemma path_law (t : ℝ) : (pathModel t 1).law =
    uniformLaw (fun u : Bool×Bool => pathBlock t (sign u.1) (sign u.2)) := by
  let e : (Fin 1 → Fin 2 → Bool) ≃ Bool×Bool :=
    (Equiv.funUnique (Fin 1) (Fin 2 → Bool)).trans (finTwoArrowEquiv Bool)
  trans uniformLaw ((fun u : Bool×Bool=>pathBlock t (sign u.1) (sign u.2)) ∘ e)
  · change uniformLaw _=uniformLaw _
    congr 1
    funext u i
    fin_cases i <;> rfl
  · exact uniformLaw_equiv e _

lemma path_integral (t : ℝ) (g : (Fin 3 → ℝ) → ℝ) (hg : Measurable g) :
    expectation (pathModel t 1) g = pathMean (fun u v=>g (pathBlock t u v)) := by
  unfold expectation
  rw [path_law,uniform_integral _ (measurable_of_finite _) _ hg]
  simp [Fintype.sum_prod_type,Fintype.sum_bool,sign,pathMean]
  ring

lemma path_means (t : ℝ) (i : Fin 3) :
    expectation (pathModel t 1) (fun y=>weighted (pathModel t 1) y i) =
      (![t,-2*t,t] : Fin 3 → ℝ) i := by
  have hw (y : Fin 3 → ℝ) (j : Fin 3) : weighted (pathModel t 1) y j=y j := by simp [weighted,pathModel]
  simp only [hw]
  rw [path_integral _ _ (measurable_pi_apply i)]
  fin_cases i <;> simp [pathMean,pathBlock] <;> ring

lemma path_covariance (i j : Fin 3) : covariance (pathModel 0 1) i j =
    (![![1,3/5,0],![3/5,1,4/5],![0,4/5,1]] : Matrix (Fin 3) (Fin 3) ℝ) i j := by
  unfold covariance
  rw [path_means,path_means]
  have hw (y : Fin 3 → ℝ) (j : Fin 3) : weighted (pathModel 0 1) y j=y j := by simp [weighted,pathModel]
  simp only [hw]
  rw [path_integral _ _ (by fun_prop)]
  fin_cases i <;> fin_cases j <;> norm_num [pathMean,pathBlock]

lemma indep_pushforward {A : Type} [MeasurableSpace A] (μ : Measure A)
    {n : ℕ} (g : A → Fin n → ℝ) (hg : Measurable g)
    (f h : (Fin n → ℝ) → ℝ) (hf : Measurable f) (hh : Measurable h)
    (hi : IndepFun (f ∘ g) (h ∘ g) μ) : IndepFun f h (μ.map g) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  rw [Measure.map_apply hg ((hs.preimage hf).inter (ht.preimage hh)),
    Measure.map_apply hg (hs.preimage hf),Measure.map_apply hg (ht.preimage hh)]
  simpa only [Set.preimage_inter,Set.preimage_preimage,Function.comp_def] using hi.measure_inter_preimage_eq_mul s t hs ht

lemma path_endpoints_independent : IndepFun (fun y : Fin 3 → ℝ=>y 0)
    (fun y=>y 2) (pathModel 0 1).law := by
  let g := fun u : Bool×Bool=>pathBlock 0 (sign u.1) (sign u.2)
  have hg : Measurable g := measurable_of_finite _
  rw [path_law,uniformLaw,←PMF.toMeasure_map g (PMF.uniformOfFintype _) hg]
  apply indep_pushforward _ g hg _ _ (measurable_pi_apply 0) (measurable_pi_apply 2)
  have hprod : (PMF.uniformOfFintype (Bool×Bool)).toMeasure =
      (PMF.uniformOfFintype Bool).toMeasure.prod (PMF.uniformOfFintype Bool).toMeasure := by
    apply Measure.ext_of_singleton
    intro u
    rcases u with ⟨u,v⟩
    rw [←Set.singleton_prod_singleton,Measure.prod_prod]
    simp [PMF.toMeasure_apply_singleton,PMF.uniformOfFintype_apply]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  rw [hprod]
  simpa [Function.comp_def,g,pathBlock] using
    (indepFun_prod (μ:=(PMF.uniformOfFintype Bool).toMeasure)
      (ν:=(PMF.uniformOfFintype Bool).toMeasure) (measurable_of_finite sign) (measurable_of_finite sign))

lemma path_disconnected_cases (S T : Finset (Fin 3)) (hd : Disjoint S T)
    (hs : ∀i∈S,∀j∈T,pathGraph.val i j=false) :
    S=∅ ∨ T=∅ ∨ (S={0} ∧ T={2}) ∨ (S={2} ∧ T={0}) := by
  revert S T
  decide

lemma path_dependency : Dependency (pathModel 0 1) := by
  let : IsProbabilityMeasure (pathModel 0 1).law := (pathModel 0 1).probability
  have hG : (pathModel 0 1).G=pathGraph := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  unfold Dependency VariableDependency
  rw [hG]
  intro S T hd hs
  rcases path_disconnected_cases S T hd hs with hS|hT|⟨hS,hT⟩|⟨hS,hT⟩
  · subst S
    convert indepFun_const_left (μ:=(pathModel 0 1).law) (fun _ : {i : Fin 3 // i∈(∅:Finset (Fin 3))}=>(0:ℝ))
      (fun y : Fin 3 → ℝ=>fun j : {j // j∈T}=>y j.val) using 1
    funext y i
    exact False.elim (Finset.notMem_empty i.val i.property)
  · subst T
    convert indepFun_const_right (μ:=(pathModel 0 1).law)
      (fun y : Fin 3 → ℝ=>fun i : {i // i∈S}=>y i.val)
      (fun _ : {j : Fin 3 // j∈(∅:Finset (Fin 3))}=>(0:ℝ)) using 1
    funext y i
    exact False.elim (Finset.notMem_empty i.val i.property)
  · subst S; subst T
    convert path_endpoints_independent.comp
      (show Measurable (fun x : ℝ=>fun _ : {i : Fin 3 // i∈({0}:Finset (Fin 3))}=>x) by fun_prop)
      (show Measurable (fun x : ℝ=>fun _ : {j : Fin 3 // j∈({2}:Finset (Fin 3))}=>x) by fun_prop) using 1
    · ext y i; have hi : i.val=0 := Finset.mem_singleton.mp i.property; change y i.val=y 0;exact congrArg y hi
    · ext y i; have hi : i.val=2 := Finset.mem_singleton.mp i.property; change y i.val=y 2;exact congrArg y hi
  · subst S; subst T
    convert path_endpoints_independent.symm.comp
      (show Measurable (fun x : ℝ=>fun _ : {i : Fin 3 // i∈({2}:Finset (Fin 3))}=>x) by fun_prop)
      (show Measurable (fun x : ℝ=>fun _ : {j : Fin 3 // j∈({0}:Finset (Fin 3))}=>x) by fun_prop) using 1
    · ext y i; have hi : i.val=2 := Finset.mem_singleton.mp i.property; change y i.val=y 2;exact congrArg y hi
    · ext y i; have hi : i.val=0 := Finset.mem_singleton.mp i.property; change y i.val=y 0;exact congrArg y hi

lemma path_correlation_instance_completed :
    Homoskedastic (pathModel 0 1) ∧ Dependency (pathModel 0 1) ∧
    (∀ i, covariance (pathModel 0 1) i i=1) ∧
    rho (pathModel 0 1) 0 1=3/5 ∧ rho (pathModel 0 1) 1 2=4/5 ∧
    rho (pathModel 0 1) 0 2=0 ∧
    3*var (pathModel 0 1) (betaHat (pathModel 0 1))=29/15 ∧
    meanVariance (pathModel 0 1)*(1+
      (∑ i, ∑ j, adjacency (pathModel 0 1).G i j*rho (pathModel 0 1) i j)/3)=29/15 := by
  have hdiag (i : Fin 3) : covariance (pathModel 0 1) i i=1 := by
    rw [path_covariance];fin_cases i <;> norm_num
  have hmv : meanVariance (pathModel 0 1)=1 := by simp [meanVariance,hdiag]
  have hbeta : beta (pathModel 0 1)=0 := by
    unfold beta
    rw [path_integral _ _ (by unfold betaHat average weighted;fun_prop)]
    norm_num [pathMean,betaHat,average,weighted,pathModel,pathBlock,Fin.sum_univ_succ]
  refine ⟨fun i j=>(hdiag i).trans (hdiag j).symm,path_dependency,hdiag,?_,?_,?_,?_,?_⟩
  · norm_num [rho,hmv,path_covariance]
  · norm_num [rho,hmv,path_covariance]
  · norm_num [rho,hmv,path_covariance]
  · unfold var
    change 3*expectation (pathModel 0 1) (fun y=>(betaHat (pathModel 0 1) y-beta (pathModel 0 1))^2)=29/15
    rw [hbeta,path_integral _ _ (by unfold betaHat average weighted;fun_prop)]
    norm_num [pathMean,betaHat,average,weighted,pathModel,pathBlock,Fin.sum_univ_succ]
  · simp only [rho,hmv,show ¬(1:ℝ)=0 by norm_num,if_false,div_one,path_covariance]
    norm_num [Fin.sum_univ_succ,adjacency,pathModel,blockGraph,pathGraph,localIndex]
end
end AronowAudit.P011.PathFiniteCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
theorem path_correlation_instance :
    Homoskedastic (pathModel 0 1) ∧ Dependency (pathModel 0 1) ∧
    (∀ i, covariance (pathModel 0 1) i i=1) ∧
    rho (pathModel 0 1) 0 1=3/5 ∧ rho (pathModel 0 1) 1 2=4/5 ∧
    rho (pathModel 0 1) 0 2=0 ∧
    3*var (pathModel 0 1) (betaHat (pathModel 0 1))=29/15 ∧
    meanVariance (pathModel 0 1)*(1+
      (∑ i, ∑ j, adjacency (pathModel 0 1).G i j*rho (pathModel 0 1) i j)/3)=29/15 := by
  exact PathFiniteCompletion.path_correlation_instance_completed
end
end AronowAudit.P011

