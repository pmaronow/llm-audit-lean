/- P011 T2/T15: exact path/star block-law means and OLS intercept formulas. -/
import AronowAudit.P011.P011_StarCompletion
import AronowAudit.P011.P011_PathFiniteCompletion
import AronowAudit.P011.P011_ThreePointCompletion
import AronowAudit.P011.P011_FiniteLawCompletion
namespace AronowAudit.P011.BlockOLSCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
lemma local_sum {q K : ℕ} (hq : 0<q) (f : Fin q→ℝ) :
    (∑i : Fin (q*K),f (localIndex hq i))=(K:ℝ)*∑j,f j := by
  rw [←(StarCompletion.blockEquiv q K).sum_comp,Fintype.sum_prod_type]
  simp only [StarCompletion.block_local]
  simp

lemma centered_design_intercept {n : ℕ} (hn : 0<n) (z : Fin n→ℝ)
    (hz : (∑i,z i)=0) (hzz : (∑i,z i^2)≠0) (y : Fin n→ℝ) :
    ols (fun (i : Fin n) (j : Fin 2)=>if j=0 then 1 else z i) y 0=average y := by
  let D : Matrix (Fin n) (Fin 2) ℝ := fun i j=>if j=0 then 1 else z i
  let s := ∑i,z i^2
  let B : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal (![(n:ℝ)⁻¹,s⁻¹])
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hs0 : s≠0 := hzz
  have hGram : Dᵀ*D=Matrix.diagonal (![(n:ℝ),s]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,D,hz,s,Matrix.diagonal_apply,pow_two]
  have hinv : (Dᵀ*D)⁻¹=B := by
    apply Matrix.inv_eq_left_inv
    rw [hGram]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal_apply,Matrix.one_apply,hn0,hs0]
  change ols D y 0=average y
  unfold ols
  rw [hinv]
  simp [B,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.diagonal_apply,Matrix.transpose_apply,D,average,div_eq_mul_inv,mul_comm]

lemma uniform_evaluation_integral {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (i : I) (f : A→ℝ) :
    (∫u : I→A,f (u i)∂(PMF.uniformOfFintype (I→A)).toMeasure)=
    (∑a,f a)/(Fintype.card A:ℝ) := by
  have hf : Measurable f := measurable_of_finite _
  have hu : (PMF.uniformOfFintype (I→A)).toMeasure=
      Measure.pi (fun _ : I=>(PMF.uniformOfFintype A).toMeasure) := by
    apply Measure.ext_of_singleton
    intro u
    rw [(PMF.uniformOfFintype _).toMeasure_apply_singleton u (measurableSet_singleton u),Measure.pi_singleton]
    have hs (a : A) : (PMF.uniformOfFintype A).toMeasure {a}=(Fintype.card A:ENNReal)⁻¹ := by
      rw [(PMF.uniformOfFintype A).toMeasure_apply_singleton a (measurableSet_singleton a),PMF.uniformOfFintype_apply]
    simp_rw [hs]
    simp [PMF.uniformOfFintype_apply,Fintype.card_fun,ENNReal.inv_pow]
  rw [hu]
  rw [←integral_map (φ:=fun u : I→A=>u i) (f:=f) (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable,
    (measurePreserving_eval (fun _ : I => (PMF.uniformOfFintype A).toMeasure) i).map_eq,
    PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,smul_eq_mul]
  rw [←Finset.mul_sum]
  simp only [div_eq_mul_inv,mul_comm]

lemma block_coordinate_integral {A : Type} [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] {q K : ℕ} (hq : 0<q) (f : A→Fin q→ℝ)
    (i : Fin (q*K)) :
    (∫y,y i∂uniformLaw (fun u : Fin K→A=>fun j=>f (u (blockIndex hq j)) (localIndex hq j)))=
    (∑a,f a (localIndex hq i))/(Fintype.card A:ℝ) := by
  let g := fun u : Fin K→A=>fun j=>f (u (blockIndex hq j)) (localIndex hq j)
  have hg : Measurable g := measurable_of_finite _
  rw [uniformLaw,←PMF.toMeasure_map g (PMF.uniformOfFintype _) hg,
    integral_map hg.aemeasurable (measurable_pi_apply i).aestronglyMeasurable]
  exact uniform_evaluation_integral (blockIndex hq i) (fun a=>f a (localIndex hq i))

lemma sum_path_means (t : ℝ) (r : Fin 3) :
    (∑u : Fin 2→Bool,pathBlock t (sign (u 0)) (sign (u 1)) r)/4=
    (![t,-2*t,t] : Fin 3→ℝ) r := by
  rw [←(finTwoArrowEquiv Bool).symm.sum_comp]
  fin_cases r <;> norm_num [Fintype.sum_prod_type,Fintype.sum_bool,finTwoArrowEquiv,pathBlock,sign] <;>ring

lemma path_coordinate_mean (t : ℝ) (K : ℕ) (i : Fin (3*K)) :
    expectation (pathModel t K) (fun y=>y i)=
      (![t,-2*t,t] : Fin 3→ℝ) (localIndex (by decide) i) := by
  unfold expectation
  change (∫y,y i∂uniformLaw _)=_
  rw [block_coordinate_integral (q:=3) (K:=K) (by decide) (fun u : Fin 2→Bool=>pathBlock t (sign (u 0)) (sign (u 1))) i]
  norm_num only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin, pow_two]
  exact sum_path_means t _

lemma threshold_sum (N c : ℕ) (h : c≤N) :
    (∑v : Fin N, if v.val<c then (1:ℝ) else 0)=(c:ℝ) := by
  simp only [←Finset.sum_filter]
  simp [Fin.card_filter_val_lt,Nat.min_eq_right h]

lemma uniform_coordinate_sum {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (i : I) (f : A→ℝ) :
    (∑u : I→A,f (u i))/(Fintype.card (I→A):ℝ)=(∑a,f a)/(Fintype.card A:ℝ) := by
  have hh := uniform_evaluation_integral i f
  rw [PMF.integral_eq_sum] at hh
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul] at hh
  rw [←Finset.mul_sum] at hh
  simpa only [div_eq_mul_inv,mul_comm] using hh

lemma star_leaves_mean (upper : Bool) (j : Fin 3) :
    (∑u : Fin 3→Fin 4,starLeaves upper u j)=
      64*(if upper then (![3/4,1/4,1/2] : Fin 3→ℝ) j else 1/4) := by
  let c := if upper then (![3,1,2] : Fin 3→ℕ) j else 1
  have hc : c≤4 := by cases upper <;> fin_cases j <;> norm_num [c]
  have hh := uniform_coordinate_sum j (fun v : Fin 4=>if v.val<c then (1:ℝ) else 0)
  rw [threshold_sum 4 c hc] at hh
  change (∑u : Fin 3→Fin 4,starLeaves upper u j)/64=(c:ℝ)/4 at hh
  have hs : (∑u : Fin 3→Fin 4,starLeaves upper u j)=16*(c:ℝ) := by linarith
  rw [hs]
  cases upper <;> fin_cases j <;> norm_num [c]

lemma star_center_sum (upper : Bool) (u : Fin 3→Fin 4) :
    (∑v : Fin 48, starBlock upper u v 0)=
      (if upper then 18 else 33)+4*(∑j,starLeaves upper u j) := by
  let c : ℕ := ∑j : Fin 3, if starLeaves upper u j=1 then 1 else 0
  have hc : c≤3 := by
    calc
      c ≤ ∑_j : Fin 3,(1:ℕ) := Finset.sum_le_sum (fun j _=>by split_ifs <;> omega)
      _ = 3 := by simp
  have hcount : (c:ℝ)=∑j,starLeaves upper u j := by
    dsimp [c]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    unfold starLeaves
    split_ifs <;> simp_all
  have hthreshold : (if upper then 18 else 33)+4*c≤48 := by cases upper <;> dsimp <;> omega
  have hs := threshold_sum 48 ((if upper then 18 else 33)+4*c) hthreshold
  change (∑v : Fin 48, if v.val<(if upper then 18 else 33)+4*c then (1:ℝ) else 0)=_
  rw [hs]
  push_cast
  rw [hcount]

lemma star_source_mean (upper : Bool) (r : Fin 4) :
    (∑u : (Fin 3→Fin 4)×Fin 48,starBlock upper u.1 u.2 r)/3072=
      (if upper then (![1/2,3/4,1/4,1/2] : Fin 4→ℝ) else ![3/4,1/4,1/4,1/4]) r := by
  rw [Fintype.sum_prod_type]
  have hleaf (j : Fin 3) :
      (∑u : Fin 3→Fin 4,∑v : Fin 48,starBlock upper u v j.succ)/3072=
        (if upper then (![3/4,1/4,1/2] : Fin 3→ℝ) j else 1/4) := by
    have he (u : Fin 3→Fin 4) (v : Fin 48) : starBlock upper u v j.succ=starLeaves upper u j := by
      fin_cases j <;> rfl
    simp_rw [he]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [←Finset.mul_sum,star_leaves_mean]
    ring
  fin_cases r
  · change (∑u : Fin 3→Fin 4,∑v : Fin 48,starBlock upper u v 0)/3072=_
    simp_rw [star_center_sum]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_comm]
    simp_rw [star_leaves_mean]
    cases upper <;> norm_num [Fin.sum_univ_succ]
  · cases upper <;> simpa using hleaf 0
  · cases upper <;> simpa using hleaf 1
  · cases upper <;> simpa using hleaf 2

lemma star_coordinate_mean (upper : Bool) (K : ℕ) (i : Fin (4*K)) :
    expectation (starModel upper K) (fun y=>y i)=
      (if upper then (![1/2,3/4,1/4,1/2] : Fin 4→ℝ) else ![3/4,1/4,1/4,1/4])
        (localIndex (by decide) i) := by
  unfold expectation
  change (∫y,y i∂uniformLaw _)=_
  rw [block_coordinate_integral (q:=4) (K:=K) (by decide)
    (fun u : (Fin 3→Fin 4)×Fin 48=>starBlock upper u.1 u.2) i]
  norm_num only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
  exact star_source_mean upper _

lemma block_ols_representations_completed :
    (∀ t : ℝ, (t=1 ∨ t=2) → ∀ K : ℕ, 0 < K →
      let D : Matrix (Fin (3*K)) (Fin 2) ℝ := fun i j =>
        if j=0 then 1 else (![t,-2*t,t] : Fin 3 → ℝ) (localIndex (by decide) i)
      MeanModel (pathModel t K) D (![0,1] : Fin 2 → ℝ) ∧
      (∀ y, ols D y 0 = average y)) ∧
    (∀ upper : Bool, ∀ K : ℕ, 0 < K →
      let D : Matrix (Fin (4*K)) (Fin 2) ℝ := fun i j => if j=0 then 1 else
        (if upper then (![0,1,-1,0] : Fin 4 → ℝ) else ![3,-1,-1,-1]) (localIndex (by decide) i)
      MeanModel (starModel upper K) D (if upper then ![1/2,1/4] else ![3/8,1/8]) ∧
      (∀ y, ols D y 0 = average y)) := by
  constructor
  · intro t ht K hK
    let : IsProbabilityMeasure (pathModel t K).law := (pathModel t K).probability
    let z := fun i : Fin (3*K)=>(![t,-2*t,t] : Fin 3→ℝ) (localIndex (by decide) i)
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i
      have hp : MemLp (fun y : Fin (3*K)→ℝ=>y i) 2 (pathModel t K).law :=
        NewFiniteCompletion.finite_memLp
          (fun u : Fin K→Fin 2→Bool=>fun j=>pathBlock t (sign (u (blockIndex (by decide) j) 0))
            (sign (u (blockIndex (by decide) j) 1)) (localIndex (by decide) j))
          (fun y=>y i) (measurable_pi_apply i) 2
      exact hp.integrable (by norm_num)
    · intro i
      rw [path_coordinate_mean]
      simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    · intro y
      apply centered_design_intercept (by omega)
      · rw [local_sum (by decide : 0<3)]
        have hz0 : (∑r : Fin 3,(![t,-2*t,t] : Fin 3→ℝ) r)=0 := by
          norm_num [Fin.sum_univ_succ]
          ring
        rw [hz0,mul_zero]
      · change (∑i : Fin (3*K),z i^2)≠0
        have hs : (∑i : Fin (3*K),z i^2)=(K:ℝ)*(6*t^2) := by
          rw [local_sum (by decide : 0<3) (fun r=>(![t,-2*t,t] : Fin 3→ℝ) r^2)]
          congr 1
          norm_num [Fin.sum_univ_succ]
          ring
        rw [hs]
        rcases ht with rfl|rfl <;> positivity
  · intro upper K hK
    let : IsProbabilityMeasure (starModel upper K).law := (starModel upper K).probability
    let w : Fin 4→ℝ := if upper then ![0,1,-1,0] else ![3,-1,-1,-1]
    let z := fun i : Fin (4*K)=>w (localIndex (by decide) i)
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i
      have hp : MemLp (fun y : Fin (4*K)→ℝ=>y i) 2 (starModel upper K).law :=
        NewFiniteCompletion.finite_memLp
          (fun u : Fin K→((Fin 3→Fin 4)×Fin 48)=>fun j=>starBlock upper
            (u (blockIndex (by decide) j)).1 (u (blockIndex (by decide) j)).2 (localIndex (by decide) j))
          (fun y=>y i) (measurable_pi_apply i) 2
      exact hp.integrable (by norm_num)
    · intro i
      rw [star_coordinate_mean]
      generalize hr : localIndex (by decide : 0<4) i=r
      cases upper <;> fin_cases r <;> norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hr]
    · intro y
      apply centered_design_intercept (by omega)
      · rw [local_sum (by decide : 0<4)]
        cases upper <;> norm_num [Fin.sum_univ_succ]
      · change (∑i : Fin (4*K),z i^2)≠0
        have hs : (∑i : Fin (4*K),z i^2)=(K:ℝ)*(∑r,w r^2) :=
          local_sum (by decide : 0<4) (fun r=>w r^2)
        rw [hs]
        cases upper <;> norm_num [w,Fin.sum_univ_succ] <;> positivity
end
end AronowAudit.P011.BlockOLSCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
theorem block_ols_representations :
    (∀ t : ℝ, (t=1 ∨ t=2) → ∀ K : ℕ, 0 < K →
      let D : Matrix (Fin (3*K)) (Fin 2) ℝ := fun i j =>
        if j=0 then 1 else (![t,-2*t,t] : Fin 3 → ℝ) (localIndex (by decide) i)
      MeanModel (pathModel t K) D (![0,1] : Fin 2 → ℝ) ∧
      (∀ y, ols D y 0 = average y)) ∧
    (∀ upper : Bool, ∀ K : ℕ, 0 < K →
      let D : Matrix (Fin (4*K)) (Fin 2) ℝ := fun i j => if j=0 then 1 else
        (if upper then (![0,1,-1,0] : Fin 4 → ℝ) else ![3,-1,-1,-1]) (localIndex (by decide) i)
      MeanModel (starModel upper K) D (if upper then ![1/2,1/4] else ![3/8,1/8]) ∧
      (∀ y, ols D y 0 = average y)) := by
  exact BlockOLSCompletion.block_ols_representations_completed
end
end AronowAudit.P011

