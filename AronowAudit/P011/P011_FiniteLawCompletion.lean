/- Finite uniform-law bridges and the P011 T10 mean-mixture moments. -/
import AronowAudit.P011.P011_ThreePointCompletion
namespace AronowAudit.P011.NewFiniteCompletion
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

lemma finite_memLp {A : Type} [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] {n : ℕ} (f : A → Fin n → ℝ)
    (g : (Fin n → ℝ) → ℝ) (hg : Measurable g) (p : ENNReal) : MemLp g p (uniformLaw f) := by
  classical
  have hf : Measurable f := measurable_of_finite _
  have hm : uniformLaw f = (PMF.uniformOfFintype A).toMeasure.map f :=
    (PMF.toMeasure_map f (PMF.uniformOfFintype A) hf).symm
  rw [hm]
  apply MemLp.of_bound hg.aestronglyMeasurable (∑ a, |g (f a)|)
  apply (ae_map_iff hf.aemeasurable (measurableSet_le (by fun_prop) measurable_const)).mpr
  filter_upwards [] with a
  simpa only [Real.norm_eq_abs] using Finset.single_le_sum
    (fun b (_ : b ∈ (Finset.univ : Finset A)) => abs_nonneg (g (f b))) (Finset.mem_univ a)

lemma coord_integral {n : ℕ} (A : Type) [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : Fin n → A → ℝ)
    (i : Fin n) (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ y, g (y i) ∂uniformLaw (fun u : Fin n → A => fun j => f j (u j))) =
      (∑ a, g (f i a))/(Fintype.card A : ℝ) := by
  let k := fun (u : Fin n → A) j => f j (u j)
  have hk : Measurable k := measurable_of_finite _
  have he : (fun y : Fin n → ℝ => g (y i)) ∘ k = (g ∘ f i) ∘ (fun u => u i) := rfl
  rw [uniformLaw,←PMF.toMeasure_map k (PMF.uniformOfFintype _) hk]
  have hg' : Measurable (fun y : Fin n → ℝ=>g (y i)) := hg.comp (measurable_pi_apply i)
  rw [integral_map hk.aemeasurable hg'.aestronglyMeasurable]
  have hu : (PMF.uniformOfFintype (Fin n → A)).toMeasure =
      Measure.pi (fun _ : Fin n=>(PMF.uniformOfFintype A).toMeasure) := by
    apply Measure.ext_of_singleton
    intro u
    rw [(PMF.uniformOfFintype _).toMeasure_apply_singleton u (measurableSet_singleton u),Measure.pi_singleton]
    have hs (a : A) : (PMF.uniformOfFintype A).toMeasure {a}=(Fintype.card A:ENNReal)⁻¹ := by
      rw [(PMF.uniformOfFintype A).toMeasure_apply_singleton a (measurableSet_singleton a),PMF.uniformOfFintype_apply]
    simp_rw [hs]
    simp [PMF.uniformOfFintype_apply,Fintype.card_fun,ENNReal.inv_pow]
  rw [hu]
  change (∫ u, g (f i (u i)) ∂Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype A).toMeasure)) = _
  rw [←integral_map (φ:=fun u : Fin n → A=>u i) (f:=fun a=>g (f i a))
    (measurable_pi_apply i).aemeasurable (measurable_of_finite (fun a=>g (f i a))).aestronglyMeasurable,
    (measurePreserving_eval (fun _ : Fin n => (PMF.uniformOfFintype A).toMeasure) i).map_eq]
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,smul_eq_mul]
  rw [←Finset.mul_sum]
  simp only [div_eq_mul_inv,mul_comm]

lemma coordinate_moments {n : ℕ} (hn : 0<n) (m : Model n)
    (A : Type) [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (f : Fin n → A → ℝ) (hlaw : m.law=uniformLaw (fun u : Fin n → A => fun i => f i (u i)))
    (hθ : ∀i,m.theta i=1) (hG : m.G=emptyGraph n) (mu : Fin n → ℝ) (v : ℝ)
    (hm : ∀i,(∑ a,f i a)/(Fintype.card A:ℝ)=mu i)
    (hv : ∀i,(∑ a,(f i a-mu i)^2)/(Fintype.card A:ℝ)=v) :
    (∀i,expectation m (fun y=>y i)=mu i ∧ covariance m i i=v) ∧
    beta m=average mu ∧ (n:ℝ)*var m (betaHat m)=v := by
  classical
  let : IsProbabilityMeasure m.law := m.probability
  have hw (y : Fin n → ℝ) (i : Fin n) : weighted m y i=y i := by simp [weighted,hθ]
  have hL2 (i : Fin n) : MemLp (fun y : Fin n → ℝ => y i) 2 m.law := by
    rw [hlaw]
    exact finite_memLp _ _ (measurable_pi_apply i) _
  have hmean (i : Fin n) : expectation m (fun y=>y i)=mu i := by
    unfold expectation
    rw [hlaw,coord_integral A f i (fun x=>x) measurable_id]
    exact hm i
  have hdiag (i : Fin n) : covariance m i i=v := by
    unfold covariance
    simp only [hw,hmean]
    unfold expectation
    rw [hlaw,coord_integral A f i (fun x=>(x-mu i)*(x-mu i)) (by fun_prop)]
    simpa only [←pow_two] using hv i
  have hdep : Dependency m := by
    unfold Dependency
    rw [hlaw,hG]
    exact uniform_coordinate_dependency A f (fun i=>measurable_of_finite _)
  have hcov (i j : Fin n) : covariance m i j=if i=j then v else 0 := by
    by_cases hij : i=j
    · subst j; simp [hdiag]
    · rw [if_neg hij,QuadraticCompletion.covariance_eq_mathlib]
      have hi := hdep {i} {j} (by simpa using hij) (by simp [hG,emptyGraph])
      have hh : IndepFun (fun y : Fin n → ℝ=>y i) (fun y=>y j) m.law := by
        simpa only [Function.comp_def] using hi.comp (measurable_pi_apply ⟨i,by simp⟩) (measurable_pi_apply ⟨j,by simp⟩)
      simpa only [hw] using hh.covariance_eq_zero (hL2 i) (hL2 j)
  refine ⟨fun i=>⟨hmean i,hdiag i⟩,?_,?_⟩
  · unfold beta expectation betaHat average
    simp only [hw]
    rw [integral_div,integral_finsetSum Finset.univ (fun i _=>(hL2 i).integrable (by norm_num))]
    change (∑i,expectation m (fun y=>y i))/(n:ℝ)=average mu
    simp only [hmean]
    rfl
  · rw [QuadraticCompletion.beta_variance m (fun i=>by simpa only [hw] using hL2 i)]
    unfold QuadraticCompletion.total
    simp only [hcov]
    simp
    field_simp [show (n:ℝ)≠0 by exact_mod_cast Nat.ne_of_gt hn]

lemma mixture_finite_moments_completed (a b : ℝ) (s : ℕ → Bool) (n : ℕ) (hn : 0 < n) :
    (∀ i, expectation (fixedMeanModel a b s n) (fun y => y i)=a*sign (s i.val) ∧
      covariance (fixedMeanModel a b s n) i i=b^2) ∧
    beta (fixedMeanModel a b s n)=average (fun i : Fin n => a*sign (s i.val)) ∧
    (n : ℝ)*var (fixedMeanModel a b s n) (betaHat (fixedMeanModel a b s n))=b^2 ∧
    (∀ i, expectation (mixtureModel a b n) (fun y => y i)=0 ∧
      covariance (mixtureModel a b n) i i=a^2+b^2) ∧
    beta (mixtureModel a b n)=0 ∧
    (n : ℝ)*var (mixtureModel a b n) (betaHat (mixtureModel a b n))=a^2+b^2 := by
  have hfixed := coordinate_moments hn (fixedMeanModel a b s n) Bool
    (fun i u=>a*sign (s i.val)+b*sign u) rfl (fun _=>rfl) rfl
    (fun i=>a*sign (s i.val)) (b^2)
    (by intro i; simp [Fintype.sum_bool,sign] <;>ring)
    (by intro i; simp [Fintype.sum_bool,sign] <;>ring)
  let e : ((Fin n → Bool) × (Fin n → Bool)) ≃ (Fin n → Bool×Bool) :=
    {toFun:=fun u i=>(u.1 i,u.2 i), invFun:=fun u=>(fun i=>(u i).1,fun i=>(u i).2),
     left_inv:=by intro u;rfl, right_inv:=by intro u;rfl}
  have hlaw : (mixtureModel a b n).law =
      uniformLaw (fun u : Fin n → Bool×Bool => fun i=>a*sign (u i).1+b*sign (u i).2) := by
    change uniformLaw ((fun u : Fin n → Bool×Bool=>fun i=>a*sign (u i).1+b*sign (u i).2) ∘ e) = _
    exact uniformLaw_equiv e (fun u : Fin n → Bool×Bool=>fun i=>a*sign (u i).1+b*sign (u i).2)
  have hmix := coordinate_moments hn (mixtureModel a b n) (Bool×Bool)
    (fun _ u=>a*sign u.1+b*sign u.2) hlaw (fun _=>rfl) rfl
    (fun _=>0) (a^2+b^2)
    (by intro i; simp [Fintype.sum_prod_type,Fintype.sum_bool,sign] <;>ring)
    (by intro i; simp [Fintype.sum_prod_type,Fintype.sum_bool,sign] <;>ring)
  exact ⟨hfixed.1,hfixed.2.1,hfixed.2.2,hmix.1,by simpa [average] using hmix.2.1,hmix.2.2⟩
end
end AronowAudit.P011.NewFiniteCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
theorem mixture_finite_moments (a b : ℝ) (s : ℕ → Bool) (n : ℕ) (hn : 0 < n) :
    (∀ i, expectation (fixedMeanModel a b s n) (fun y => y i)=a*sign (s i.val) ∧
      covariance (fixedMeanModel a b s n) i i=b^2) ∧
    beta (fixedMeanModel a b s n)=average (fun i : Fin n => a*sign (s i.val)) ∧
    (n : ℝ)*var (fixedMeanModel a b s n) (betaHat (fixedMeanModel a b s n))=b^2 ∧
    (∀ i, expectation (mixtureModel a b n) (fun y => y i)=0 ∧
      covariance (mixtureModel a b n) i i=a^2+b^2) ∧
    beta (mixtureModel a b n)=0 ∧
    (n : ℝ)*var (mixtureModel a b n) (betaHat (mixtureModel a b n))=a^2+b^2 := by
  exact NewFiniteCompletion.mixture_finite_moments_completed a b s n hn
end
end AronowAudit.P011

