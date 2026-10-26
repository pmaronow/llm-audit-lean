import AronowAudit.P009.P009_MixingBasics
import AronowAudit.P009.P009_NormalCompletion
namespace AronowAudit.P009.DiagonalCompletion
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

lemma alpha_zero_of_block_functions {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    {A B : Type*} (X : Assignment n → A) (Y : Assignment n → B) (s : Set (Fin n))
    (hX : ∀ z w, (∀ i ∈ s,z i=w i) → X z=X w)
    (hY : ∀ z w, (∀ i ∈ sᶜ,z i=w i) → Y z=Y w) : alpha E.design X Y=0 := by
  apply le_antisymm
  · apply MixingBasics.alpha_le_of_event_bound
    intro S T
    have hf : DependsOn (fun z=>if X z∈S then (1:ℝ) else 0) s := by
      intro z w h
      change (if X z∈S then (1:ℝ) else 0)=(if X w∈S then 1 else 0)
      rw [hX z w h]
    have hg : DependsOn (fun z=>if Y z∈T then (1:ℝ) else 0) sᶜ := by
      intro z w h
      change (if Y z∈T then (1:ℝ) else 0)=(if Y w∈T then 1 else 0)
      rw [hY z w h]
    have hp' : prob E.design (fun z=>X z∈S ∧ Y z∈T)=
        mean E.design (fun z=>(if X z∈S then (1:ℝ) else 0)*(if Y z∈T then 1 else 0)) := by
      unfold prob
      congr 1
      funext z
      by_cases hs : X z∈S <;> by_cases ht : Y z∈T <;> simp [hs,ht]
    have hp : prob E.design (fun z=>X z∈S ∧ Y z∈T)=
        prob E.design (fun z=>X z∈S)*prob E.design (fun z=>Y z∈T) := by
      rw [hp']
      exact BernoulliCompletion.mean_product_of_dependsOn E hBER s _ _ hf hg
    rw [hp,sub_self,abs_zero]
  · exact MixingBasics.alpha_nonnegative _ _ _

lemma noI_mask {n : ℕ} (E : Experiment n) (hNo : NoInterference E)
    (i : Fin n) (z : Assignment n) : masked E i z=fun j=>if j=i then z i else false := by
  funext j
  simp only [masked,SparseCompletion.noI_interferes E hNo]
  by_cases h : j=i <;> simp [h]

lemma noI_alpha_ext {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (hNo : NoInterference E) (θ : ℝ) : alphaExt E θ=0 := by
  have he (i j : Fin n) : (1-d E i j)*mixPower (alpha E.design (masked E i) (masked E j)) θ=0 := by
    by_cases hij : i=j
    · simp [SparseCompletion.noI_d E hNo,hij]
    · have ha : alpha E.design (masked E i) (masked E j)=0 := by
        apply alpha_zero_of_block_functions E hBER _ _ ({i}:Set (Fin n))
        · intro z w h
          rw [noI_mask E hNo,noI_mask E hNo,h i (Set.mem_singleton i)]
        · intro z w h
          rw [noI_mask E hNo,noI_mask E hNo,h j (by simpa using (Ne.symm hij))]
      simp [ha,mixPower]
  simp [alphaExt,he]

lemma noI_alpha_int {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (hNo : NoInterference E) (θ : ℝ) : alphaInt E θ=0 := by
  have he (i : Fin n) : maskedOthers E i=fun _ _=>false := by
    funext z j
    simp only [maskedOthers,noI_mask E hNo,Function.update_apply]
    split_ifs <;> simp_all
  have ha (i : Fin n) : alpha E.design (fun z=>z i) (maskedOthers E i)=0 := by
    apply alpha_zero_of_block_functions E hBER _ _ ({i}:Set (Fin n))
    · intro z w h; exact h i (Set.mem_singleton i)
    · intro z w h; rw [he]
  simp [alphaInt,ha,mixPower]

lemma identity_noI (n : ℕ) : NoInterference (identityExperiment n) := by
  intro i z w h
  exact congrArg bit h

lemma coordinate_covariance (n : ℕ) (i j : Fin n) :
    cov (fairLaw n) (fun z=>bit (z i)) (fun z=>bit (z j))=if i=j then 1/4 else 0 := by
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl,BernoulliCompletion.covariance_product_formula]
    rw [SparseCompletion.fair_coordinate n i (fun b=>bit b*bit b),
      SparseCompletion.fair_coordinate n i bit]
    norm_num [bit]
  · rw [if_neg hij,BernoulliCompletion.covariance_product_formula]
    have hi : DependsOn (fun z : Assignment n=>bit (z i)) ({i}:Set (Fin n)) := by
      intro z w h; exact congrArg bit (h i (Set.mem_singleton i))
    have hj : DependsOn (fun z : Assignment n=>bit (z j)) ({i}:Set (Fin n))ᶜ := by
      intro z w h; exact congrArg bit (h j (by simpa using (Ne.symm hij)))
    have hh := BernoulliCompletion.mean_product_of_dependsOn (identityExperiment n)
      (SparseCompletion.fair_BER n _) _ _ _ hi hj
    have hh' : mean (fairLaw n) (fun z=>bit (z i)*bit (z j))=
        mean (fairLaw n) (fun z=>bit (z i))*mean (fairLaw n) (fun z=>bit (z j)) := by
      simpa only [identityExperiment,fairExperiment] using hh
    rw [hh',sub_self]

lemma identity_regular : RegularSequence identityStudy 2 4 1 := by
  intro t
  exact SparseCompletion.fair_regular_bounded (t+1) _ (by intro i z; cases z i <;> norm_num [bit])

lemma identity_maximal : MaximalMoments identityStudy ⊤ ⊤ := by
  refine ⟨?_,by simp,?_,by simp⟩
  · refine ⟨by simp,2,by norm_num,?_⟩
    intro t i
    simp only [MomentBound,ite_true]
    intro z hz
    change |bit (z i)|≤2
    cases z i <;> norm_num [bit]
  · refine ⟨by simp,2,by norm_num,?_⟩
    intro t i b
    simp only [MomentBound,ite_true]
    intro z hz
    change |bit ((Function.update z i b) i)|≤2
    cases b <;> norm_num [bit]

theorem diagonal_omission_family_completed :
    RegularSequence identityStudy 2 4 1 ∧ MaximalMoments identityStudy ⊤ ⊤ ∧
    (∀ t, Bernoulli (identityStudy.experiment t) ∧ NoInterference (identityStudy.experiment t) ∧
      dAvg (identityStudy.experiment t) = 1) ∧ Restricted identityStudy ∧
    LittleO (fun t => alphaExt (identityStudy.experiment t) 1) (size identityStudy) ∧
    LittleO (fun t => alphaInt (identityStudy.experiment t) 1) (size identityStudy) ∧
    (∀ t, let E := identityStudy.experiment t
      4*(∑ i, ∑ j, cov E.design (fun z => bit (z i)) (fun z => bit (z j))) = size identityStudy t ∧
      4*(∑ i, ∑ j, if j = i then 0 else alpha E.design (fun z => z i) (fun z => z j)) = 0 ∧
      0 < size identityStudy t) := by
  have hb (t : ℕ) : Bernoulli (identityStudy.experiment t) := SparseCompletion.fair_BER _ _
  have hn (t : ℕ) : NoInterference (identityStudy.experiment t) := identity_noI _
  have hd (t : ℕ) : dAvg (identityStudy.experiment t)=1 :=
    SparseCompletion.noI_dAvg (identityStudy.positive t) _ (hn t)
  refine ⟨identity_regular,identity_maximal,fun t=>⟨hb t,hn t,hd t⟩,?_,?_,?_,?_⟩
  · unfold Restricted
    change Tendsto (fun t=>dAvg (identityStudy.experiment t)/size sparseStudy t) atTop (nhds 0)
    simp_rw [hd]
    exact SparseCompletion.inv_size_zero
  · unfold LittleO
    simp only [noI_alpha_ext _ (hb _) (hn _),zero_div]
    exact tendsto_const_nhds
  · unfold LittleO
    simp only [noI_alpha_int _ (hb _) (hn _),zero_div]
    exact tendsto_const_nhds
  · intro t
    dsimp only
    refine ⟨?_,?_,by dsimp [size,identityStudy,sparseStudy]; positivity⟩
    · change 4*(∑ i : Fin (t+1),∑ j : Fin (t+1),cov (fairLaw (t+1)) (fun z=>bit (z i)) (fun z=>bit (z j)))=(t+1:ℕ)
      simp [coordinate_covariance]
      ring
    · have ha (i j : Fin (t+1)) (hij : j≠i) :
          alpha (fairLaw (t+1)) (fun z=>z i) (fun z=>z j)=0 := by
        apply alpha_zero_of_block_functions (identityExperiment (t+1)) (hb t) _ _ ({i}:Set (Fin (t+1)))
        · intro z w h; exact h i (Set.mem_singleton i)
        · intro z w h; exact h j (by simpa using hij)
      change 4*(∑ i : Fin (t+1),∑ j : Fin (t+1),if j=i then 0 else alpha (fairLaw (t+1)) (fun z=>z i) (fun z=>z j))=0
      have he (i j : Fin (t+1)) : (if j=i then (0:ℝ) else alpha (fairLaw (t+1)) (fun z=>z i) (fun z=>z j))=0 := by
        by_cases hij : j=i <;> simp [hij,ha]
      simp [he]
end
end AronowAudit.P009.DiagonalCompletion

namespace AronowAudit.P009
open scoped BigOperators
open Filter
noncomputable section
theorem diagonal_omission_family :
    RegularSequence identityStudy 2 4 1 ∧ MaximalMoments identityStudy ⊤ ⊤ ∧
    (∀ t, Bernoulli (identityStudy.experiment t) ∧ NoInterference (identityStudy.experiment t) ∧
      dAvg (identityStudy.experiment t) = 1) ∧ Restricted identityStudy ∧
    LittleO (fun t => alphaExt (identityStudy.experiment t) 1) (size identityStudy) ∧
    LittleO (fun t => alphaInt (identityStudy.experiment t) 1) (size identityStudy) ∧
    (∀ t, let E := identityStudy.experiment t
      4*(∑ i, ∑ j, cov E.design (fun z => bit (z i)) (fun z => bit (z j))) = size identityStudy t ∧
      4*(∑ i, ∑ j, if j = i then 0 else alpha E.design (fun z => z i) (fun z => z j)) = 0 ∧
      0 < size identityStudy t) := by
  exact DiagonalCompletion.diagonal_omission_family_completed
end
end AronowAudit.P009
