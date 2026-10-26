import AronowAudit.P011.P011_QuadraticCompletion

namespace AronowAudit.P011.ThreePointCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000


@[simp] lemma model_law (n : ℕ) : (threePointModel n).law =
    uniformLaw (fun u : Fin n → Fin 3 => fun i => ((u i).val:ℝ)) := rfl
@[simp] lemma model_theta (n : ℕ) (i : Fin n) : (threePointModel n).theta i=1 := rfl
@[simp] lemma model_G (n : ℕ) : (threePointModel n).G=emptyGraph n := rfl
@[simp] lemma model_R (n : ℕ) : (threePointModel n).R=emptyGraph n := rfl
@[simp] lemma model_d (n : ℕ) (i : Fin n) : (threePointModel n).d i=0 := rfl
@[simp] lemma family_size (k : ℕ) : threePointFamily.size k=k+1 := rfl
@[simp] lemma family_model (k : ℕ) : threePointFamily.model k=threePointModel (k+1) := rfl
@[simp] lemma weighted_value {n : ℕ} (y : Fin n → ℝ) (i : Fin n) :
    weighted (threePointModel n) y i=y i := by simp [weighted]

lemma uniform_marginal {n : ℕ} (A : Type) [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : A → ℝ) (hf : Measurable f)
    (i : Fin n) :
    (uniformLaw (fun u : Fin n → A => fun j => f (u j))).map (fun y => y i) =
      (PMF.uniformOfFintype A).toMeasure.map f := by
  classical
  let g := fun (u : Fin n → A) (j : Fin n) => f (u j)
  have hg : Measurable g := Measurable.of_eval fun j => hf.comp (measurable_pi_apply j)
  change (uniformLaw g).map (fun y => y i) = _
  rw [uniformLaw,←PMF.toMeasure_map g (PMF.uniformOfFintype (Fin n → A)) hg,
    Measure.map_map (measurable_pi_apply i) hg]
  have he : (fun y : Fin n → ℝ => y i) ∘ g = f ∘ (fun u : Fin n → A => u i) := rfl
  rw [he,←Measure.map_map hf (measurable_pi_apply i)]
  have hu : (PMF.uniformOfFintype (Fin n → A)).toMeasure =
      Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype A).toMeasure) := by
    apply Measure.ext_of_singleton
    intro u
    simp [Measure.pi_singleton,PMF.uniformOfFintype_apply,ENNReal.inv_pow]
  rw [hu]
  rw [(measurePreserving_eval (fun _ : Fin n => (PMF.uniformOfFintype A).toMeasure) i).map_eq]

lemma coord_integral {n : ℕ} (i : Fin n) (g : ℝ → ℝ) (hg : Measurable g) :
    expectation (threePointModel n) (fun y => g (y i)) =
      (∑ u : Fin 3, g (u.val:ℝ))/3 := by
  have hcast : Measurable (fun u : Fin 3 => (u.val:ℝ)) := measurable_of_finite _
  have hmap := uniform_marginal (Fin 3) (fun u => (u.val:ℝ)) hcast i
  change (threePointModel n).law.map (fun y => y i) = _ at hmap
  unfold expectation
  rw [← integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable,hmap,
    integral_map hcast.aemeasurable hg.aestronglyMeasurable,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Fintype.card_fin,smul_eq_mul]
  rw [←Finset.mul_sum]
  ring

lemma coordinate_mean {n : ℕ} (i : Fin n) :
    expectation (threePointModel n) (fun y => y i) = 1 := by
  have h := coord_integral i (fun x => x) measurable_id
  norm_num [Fin.sum_univ_succ] at h
  exact h

lemma ae_bound (n : ℕ) : ∀ᵐ y ∂(threePointModel n).law, ∀ i, |y i-1| ≤ 1 := by
  classical
  let g := fun (u : Fin n → Fin 3) (i : Fin n) => ((u i).val:ℝ)
  have hg : Measurable g := measurable_of_finite _
  have hp : (threePointModel n).law =
      (PMF.uniformOfFintype (Fin n → Fin 3)).toMeasure.map g := by
    exact (PMF.toMeasure_map g (PMF.uniformOfFintype (Fin n → Fin 3)) hg).symm
  rw [hp]
  have hset : MeasurableSet {y : Fin n → ℝ | ∀ i,|y i-1|≤1} := by
    simpa only [Set.setOf_forall] using MeasurableSet.iInter (fun i : Fin n =>
      measurableSet_le (show Measurable (fun y : Fin n→ℝ=>|y i-1|) by fun_prop)
        (measurable_const : Measurable (fun _ : Fin n→ℝ=>(1:ℝ))))
  apply (ae_map_iff hg.aemeasurable hset).mpr
  filter_upwards [] with u i
  dsimp [g]
  have h0 : (0:ℝ) ≤ (u i).val := Nat.cast_nonneg _
  have h2 : ((u i).val:ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ (u i).isLt
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma coordinate_memLp {n : ℕ} (i : Fin n) :
    MemLp (fun y : Fin n → ℝ => y i) 2 (threePointModel n).law := by
  let : IsProbabilityMeasure (threePointModel n).law := (threePointModel n).probability
  apply MemLp.of_bound (measurable_pi_apply i).aestronglyMeasurable 2
  filter_upwards [ae_bound n] with y hy
  rw [Real.norm_eq_abs]
  have hh := abs_le.mp (hy i)
  exact abs_le.mpr ⟨by linarith [hh.1],by linarith [hh.2]⟩

lemma dependency (n : ℕ) : Dependency (threePointModel n) := by
  exact uniform_coordinate_dependency (Fin 3) (fun _ u => (u.val:ℝ))
    (fun _ => measurable_of_finite _)

lemma off_diag_indep {n : ℕ} (i j : Fin n) (hij : i≠j) :
    IndepFun (fun y : Fin n → ℝ => y i) (fun y => y j) (threePointModel n).law := by
  classical
  have hi := dependency n {i} {j} (by simpa using hij) (by simp [threePointModel,emptyGraph])
  exact hi.comp (measurable_pi_apply ⟨i,by simp⟩) (measurable_pi_apply ⟨j,by simp⟩)

lemma covariance_diagonal {n : ℕ} (i : Fin n) : covariance (threePointModel n) i i=2/3 := by
  have hm : expectation (threePointModel n) (fun y => weighted (threePointModel n) y i)=1 :=
    by simpa only [weighted_value] using coordinate_mean i
  unfold covariance
  rw [hm]
  simp only [weighted_value]
  change expectation (threePointModel n) (fun y => (y i-1)*(y i-1))=2/3
  rw [coord_integral i (fun x => (x-1)*(x-1)) (by fun_prop)]
  norm_num [Fin.sum_univ_succ]

lemma covariance_formula {n : ℕ} (i j : Fin n) :
    covariance (threePointModel n) i j=if i=j then 2/3 else 0 := by
  classical
  by_cases h : i=j
  · subst j; simp [covariance_diagonal]
  · rw [if_neg h,QuadraticCompletion.covariance_eq_mathlib]
    simp only [weighted_value]
    change cov[fun y => y i,fun y => y j;(threePointModel n).law]=0
    exact (off_diag_indep i j h).covariance_eq_zero (coordinate_memLp i) (coordinate_memLp j)

lemma beta_mean {n : ℕ} (hn : 0 < n) : beta (threePointModel n)=1 := by
  let : IsProbabilityMeasure (threePointModel n).law := (threePointModel n).probability
  unfold beta betaHat average
  simp only [weighted_value]
  change (∫ y, (∑ i, y i)/(n:ℝ) ∂(threePointModel n).law)=1
  rw [integral_div,integral_finsetSum Finset.univ
    (fun i _ => (coordinate_memLp i).integrable (by norm_num))]
  change (∑ i, expectation (threePointModel n) (fun y => y i))/(n:ℝ)=1
  simp [coordinate_mean,Nat.ne_of_gt hn]

lemma scaled_variance {n : ℕ} (hn : 0 < n) :
    (n:ℝ)*var (threePointModel n) (betaHat (threePointModel n))=2/3 := by
  let : IsProbabilityMeasure (threePointModel n).law := (threePointModel n).probability
  have hL2 (i : Fin n) : MemLp (fun y => weighted (threePointModel n) y i) 2 (threePointModel n).law :=
    by simpa only [weighted_value] using coordinate_memLp i
  rw [QuadraticCompletion.beta_variance _ hL2]
  have ht : QuadraticCompletion.total (covariance (threePointModel n))=(n:ℝ)*(2/3) := by
    unfold QuadraticCompletion.total
    simp [covariance_formula]
  rw [ht]
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  field_simp


lemma helper_witness_scaling_completed :
    Scaling threePointFamily 1 1 (2/3) 2 ∧ Valid threePointFamily ∧
    (∀ k, Homoskedastic (threePointFamily.model k) ∧ beta (threePointFamily.model k)=1 ∧
      scaledTrue threePointFamily k=2/3) := by
  have hm (k : ℕ) : Homoskedastic (threePointFamily.model k) := by
    intro i j
    exact (covariance_diagonal i).trans (covariance_diagonal j).symm
  have hb (k : ℕ) : beta (threePointFamily.model k)=1 := beta_mean (n:=k+1) (Nat.succ_pos k)
  have hv (k : ℕ) : scaledTrue threePointFamily k=2/3 := scaled_variance (n:=k+1) (Nat.succ_pos k)
  refine ⟨?_,?_,fun k => ⟨hm k,hb k,hv k⟩⟩
  · refine ⟨?_,by norm_num,by norm_num,by norm_num,by norm_num,
      (fun k => dependency (k+1)),?_,?_,?_,?_⟩
    · constructor
      · intro a b hab
        exact Nat.succ_le_succ hab
      · intro k
        exact ⟨Fin.castSuccEmb,fun _ _ => rfl⟩
    · intro k
      rw [hb k]
      change ∀ᵐ y ∂(threePointModel (k+1)).law, ∀ i,|weighted (threePointModel (k+1)) y i-1|≤1
      simpa only [weighted_value] using ae_bound (k+1)
    · intro k i
      norm_num [degree,emptyGraph]
    · have he : (fun k => (threePointFamily.size k:ℝ)*
          var (threePointFamily.model k) (betaHat (threePointFamily.model k))) = fun _ => (2/3:ℝ) :=
        funext hv
      rw [he]
      exact tendsto_const_nhds
    · intro k i
      norm_num
  · intro k
    constructor
    · intro i j h
      simp [emptyGraph] at h
    · intro i
      simp [degree,emptyGraph]

lemma witness_probability : probability (threePointModel 3)
    {y | y=(![0,1,2] : Fin 3 → ℝ)}=1/27 := by
  classical
  let g : (Fin 3 → Fin 3) → (Fin 3 → ℝ) := fun u i => (u i).val
  let u0 : Fin 3 → Fin 3 := ![0,1,2]
  have hg : Measurable g := measurable_of_finite _
  have hpre : g ⁻¹' {(![0,1,2] : Fin 3 → ℝ)}={u0} := by
    ext u
    change g u=(![0,1,2] : Fin 3 → ℝ) ↔ u=u0
    constructor
    · intro h
      funext i
      apply Fin.ext
      have hi := congrFun h i
      fin_cases i <;> norm_num [g,u0] at hi ⊢ <;> exact_mod_cast hi
    · intro h
      subst u
      funext i
      fin_cases i <;> norm_num [g,u0]
  unfold probability
  change (uniformLaw g).real {(![0,1,2] : Fin 3 → ℝ)}=1/27
  rw [Measure.real,uniformLaw,←PMF.toMeasure_map g (PMF.uniformOfFintype (Fin 3 → Fin 3)) hg,
    Measure.map_apply hg (measurableSet_singleton _),hpre]
  simp [PMF.uniformOfFintype_apply,ENNReal.toReal_inv]

lemma helper_witness_law_completed :
    beta (threePointModel 3)=1 ∧ 3*var (threePointModel 3) (betaHat (threePointModel 3))=2/3 ∧
    Homoskedastic (threePointModel 3) ∧ Dependency (threePointModel 3) ∧
    probability (threePointModel 3) {y | y=(![0,1,2] : Fin 3 → ℝ)}=1/27 := by
  exact ⟨beta_mean (by decide),scaled_variance (by decide),
    fun i j => (covariance_diagonal i).trans (covariance_diagonal j).symm,
    dependency 3,witness_probability⟩

end
end AronowAudit.P011.ThreePointCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
theorem helper_witness_scaling :
    Scaling threePointFamily 1 1 (2/3) 2 ∧ Valid threePointFamily ∧
    (∀ k, Homoskedastic (threePointFamily.model k) ∧ beta (threePointFamily.model k)=1 ∧
      scaledTrue threePointFamily k=2/3) := by
  exact ThreePointCompletion.helper_witness_scaling_completed

theorem helper_witness_law :
    beta (threePointModel 3)=1 ∧ 3*var (threePointModel 3) (betaHat (threePointModel 3))=2/3 ∧
    Homoskedastic (threePointModel 3) ∧ Dependency (threePointModel 3) ∧
    probability (threePointModel 3) {y | y=(![0,1,2] : Fin 3 → ℝ)}=1/27 := by
  exact ThreePointCompletion.helper_witness_law_completed

end AronowAudit.P011

