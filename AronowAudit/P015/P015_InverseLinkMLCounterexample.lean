import AronowAudit.P015.P015_Regression
namespace AronowAudit.P015.InverseLinkMLCounterexample
noncomputable section
open Matrix Finset Filter Set
open scoped BigOperators Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

lemma log_tangent (p q : ℝ) (hp : 0<p) (hq : 0<q) :
    Real.log q ≤ Real.log p+(q-p)/p := by
  have h := Real.log_le_sub_one_of_pos (div_pos hq hp)
  rw [Real.log_div hq.ne' hp.ne'] at h
  have he : q/p-1=(q-p)/p := by field_simp <;> ring
  rw [he] at h
  linarith

lemma bernoulli_identity_tangent (y p q : ℝ) (hy : y=0 ∨ y=1)
    (hp : 0<p) (hpu : p<1) (hq : 0<q) (hqu : q<1) :
    binomialLogLikelihood id 1 y q ≤ binomialLogLikelihood id 1 y p+
      (y/p-(1-y)/(1-p))*(q-p) := by
  rcases hy with rfl | rfl
  · have h := log_tangent (1-p) (1-q) (sub_pos.mpr hpu) (sub_pos.mpr hqu)
    simp only [binomialLogLikelihood,id_eq,zero_mul,sub_zero,one_mul,zero_div,zero_sub]
    convert h using 1 <;> ring
  · simpa [binomialLogLikelihood,div_eq_mul_inv,mul_comm] using log_tangent p q hp hq

lemma identity_score_global_max {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (Y : N → ℝ) (hY : ∀ i,Y i=0 ∨ Y i=1)
    (θ : Q → ℝ) (hθ : ∀ i,0<W.mulVec θ i ∧ W.mulVec θ i<1)
    (hscore : ∀ j, ∑ i,W i j*(Y i/W.mulVec θ i-(1-Y i)/(1-W.mulVec θ i))=0) :
    ∀ γ : Q → ℝ, (∀ i,0<W.mulVec γ i ∧ W.mulVec γ i<1) →
      groupedLikelihood W (fun _=>1) Y id γ ≤ groupedLikelihood W (fun _=>1) Y id θ := by
  intro γ hγ
  let c : N → ℝ := fun i => Y i/W.mulVec θ i-(1-Y i)/(1-W.mulVec θ i)
  have hlin : (∑ i,c i*(W.mulVec γ i-W.mulVec θ i))=0 := by
    have he : (fun i => W.mulVec γ i-W.mulVec θ i)=W.mulVec (γ-θ) := by
      rw [Matrix.mulVec_sub]
      rfl
    change (∑ i,c i*((fun i=>W.mulVec γ i-W.mulVec θ i) i))=0
    rw [he]
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    rw [Finset.sum_comm]
    have hf (j : Q) : (∑ i,c i*(W i j*(γ-θ) j))=(γ-θ) j*(∑ i,W i j*c i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp only [hf,hscore,mul_zero,Finset.sum_const_zero,c]
  unfold groupedLikelihood
  calc
    (∑ i,binomialLogLikelihood id 1 (Y i) (W.mulVec γ i)) ≤
      ∑ i,(binomialLogLikelihood id 1 (Y i) (W.mulVec θ i)+c i*(W.mulVec γ i-W.mulVec θ i)) := by
        exact Finset.sum_le_sum (fun i _ => bernoulli_identity_tangent (Y i)
          (W.mulVec θ i) (W.mulVec γ i) (hY i) (hθ i).1 (hθ i).2 (hγ i).1 (hγ i).2)
    _ = _ := by rw [Finset.sum_add_distrib,hlin,add_zero]

def W : Matrix (Fin 3) (Fin 2) ℝ := !![1,3/4;1,2/3;1,3/5]
def Y : Fin 3 → ℝ := ![1,0,1]
def theta : Fin 2 → ℝ := ![0,1]
def domain : Set ℝ := Set.Ioo 0 1

lemma binary_data : ∀ i,Y i=0 ∨ Y i=1 := by
  intro i
  fin_cases i <;> norm_num [Y]
lemma intercept : ∀ i,W i 0=1 := by
  intro i
  fin_cases i <;> norm_num [W]
lemma admissible : ∀ i,W.mulVec theta i ∈ domain := by
  intro i
  fin_cases i <;> norm_num [W,theta,domain,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
lemma genuine_score_zero : ∀ j, ∑ i,W i j*(Y i/W.mulVec theta i-(1-Y i)/(1-W.mulVec theta i))=0 := by
  intro j
  fin_cases j <;> norm_num [W,Y,theta,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

lemma actual_global_ML : ∀ γ : Fin 2 → ℝ, (∀ i,W.mulVec γ i ∈ domain) →
    groupedLikelihood W (fun _=>1) Y id γ ≤ groupedLikelihood W (fun _=>1) Y id theta := by
  exact identity_score_global_max W Y binary_data theta admissible genuine_score_zero

lemma residual_intercept : groupedResidual W (fun _=>1) Y id theta 0=-(1/60:ℝ) := by
  norm_num [groupedResidual,W,Y,theta,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
lemma residual_nonzero : groupedResidual W (fun _=>1) Y id theta≠0 := by
  intro h
  have hh := congrFun h 0
  rw [residual_intercept] at hh
  norm_num at hh

/-- P015-T18(B), Appendix C, p. 265: a concrete interior global ML fit
of an injective smooth Bernoulli inverse link has nonzero substituted residual.
This refutes the printed implication from an ML maximizer to the substituted
residual equation; it is not merely a failure at an arbitrary parameter point. -/
theorem identity_link_ML_counterexample :
    (∀ i,Y i=0 ∨ Y i=1) ∧ (∀ i,W i 0=1) ∧
    IsOpen domain ∧ DifferentiableOn ℝ id domain ∧ Function.Injective (domain.restrict id) ∧
    (∀ η ∈ domain, 0 < id η ∧ id η < 1) ∧ (∀ i,W.mulVec theta i∈domain) ∧
    (∀ γ : Fin 2 → ℝ, (∀ i,W.mulVec γ i∈domain) →
      groupedLikelihood W (fun _=>1) Y id γ ≤ groupedLikelihood W (fun _=>1) Y id theta) ∧
    groupedResidual W (fun _=>1) Y id theta≠0 := by
  refine ⟨binary_data,intercept,isOpen_Ioo,differentiable_id.differentiableOn,?_,?_,admissible,
    actual_global_ML,residual_nonzero⟩
  · intro a b h
    exact Subtype.ext h
  · intro η hη
    exact hη

theorem printed_inverse_link_claim_false : ¬(∀ (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K+2)) ℝ) (Y : Fin N → ℝ)
    (hY : ∀ i,Y i=0 ∨ Y i=1) (hW : ∀ i,W i 0=1)
    (I : Set ℝ) (hI : IsOpen I) (m : ℝ→ℝ)
    (hm : DifferentiableOn ℝ m I) (hinverse : Function.Injective (I.restrict m))
    (hprob : ∀ η∈I,0<m η ∧ m η<1) (θ : Fin (K+2) → ℝ)
    (hθ : ∀ i,W.mulVec θ i∈I)
    (hML : ∀ γ : Fin (K+2) → ℝ, (∀ i,W.mulVec γ i∈I) →
      groupedLikelihood W (fun _=>1) Y m γ ≤ groupedLikelihood W (fun _=>1) Y m θ),
    groupedResidual W (fun _=>1) Y m θ=0) := by
  intro h
  obtain ⟨hb,hi,ho,hd,hinj,hp,ha,hm,hn⟩ := identity_link_ML_counterexample
  exact hn (h 3 0 W Y hb hi domain ho id hd hinj hp theta ha hm)

end
end AronowAudit.P015.InverseLinkMLCounterexample
