import AronowAudit.P026.P026_FiniteDesign
/-! Full finite-vector independence from mutual product-test factorization. -/
namespace AronowAudit.P026.IndependenceCompletion
open Finset
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {Ω I R:Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]

lemma product_delta {J α:Type*} [Fintype J] [DecidableEq α] (s t:J→α):
    (∏j, if s j=t j then (1:R) else 0)=if s=t then 1 else 0:=by
  classical
  by_cases h:s=t
  · subst t
    simp
  · obtain ⟨j,hj⟩:=Function.ne_iff.mp h
    rw [ite_eq_right h]
    exact prod_eq_zero (mem_univ j) (by simp [hj])

lemma product_factor_rest {J α:Type*} [Fintype J] [DecidableEq J] [DecidableEq α]
    (i:J) (u:α→R) (t:({j:J//j≠i}→α)) (x:J→α):
    (∏j, if h:j=i then u (x j) else if x j=t ⟨j,h⟩ then (1:R) else 0)=
      u (x i)*(if (fun j:{j:J//j≠i}=>x j)=t then 1 else 0):=by
  classical
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  simp only [dite_true]
  congr 1
  calc
    _=(∏j:{j:J//j≠i},if x j=t j then (1:R) else 0):=by
      apply prod_congr rfl
      intro j _
      simp only [dite_eq_right j.2]
    _= _:=product_delta (fun j:{j:J//j≠i}=>x j) t

lemma product_factor_test {J α:Type*} [Fintype J] [DecidableEq J] [DecidableEq α]
    (D:Design Ω I R) (hD:probabilityDesign D) (X:J→Ω→α)
    (h:∀F:J→α→R,expectation D (fun w=>∏j,F j (X j w))=
      ∏j,expectation D (fun w=>F j (X j w)))
    (i:J) (u:α→R) (t:({j:J//j≠i}→α)):
    expectation D (fun w=>u (X i w)*(if (fun j:{j:J//j≠i}=>X j w)=t then 1 else 0))=
      expectation D (fun w=>u (X i w))*
        expectation D (fun w=>if (fun j:{j:J//j≠i}=>X j w)=t then 1 else 0):=by
  classical
  let F:J→α→R:=fun j a=>if hj:j=i then u a else if a=t ⟨j,hj⟩ then 1 else 0
  have hu:=h F
  have hleft:(fun w=>∏j,F j (X j w))=
      (fun w=>u (X i w)*(if (fun j:{j:J//j≠i}=>X j w)=t then 1 else 0)):=by
    funext w
    exact product_factor_rest i u t (fun j=>X j w)
  rw [hleft,Fintype.prod_eq_mul_prod_subtype_ne _ i] at hu
  simp only [F,dite_true] at hu
  have hv:=h (fun j a=>if hj:j=i then (1:R) else if a=t ⟨j,hj⟩ then 1 else 0)
  have hone:(fun w=>∏j,if hj:j=i then (1:R) else if X j w=t ⟨j,hj⟩ then 1 else 0)=
      (fun w=>if (fun j:{j:J//j≠i}=>X j w)=t then 1 else 0):=by
    funext w
    simpa using product_factor_rest i (fun _=>(1:R)) t (fun j=>X j w)
  rw [hone,Fintype.prod_eq_mul_prod_subtype_ne _ i] at hv
  simp only [dite_true,expectation_const D hD,one_mul] at hv
  have hu2:expectation D (fun w=>u (X i w)*(if (fun j:{j:J//j≠i}=>X j w)=t then 1 else 0))=
      expectation D (fun w=>u (X i w))*
        (∏j:{j:J//j≠i},expectation D (fun w=>if X j w=t j then (1:R) else 0)):=by
    rw [hu]
    congr 1
    apply prod_congr rfl
    intro j _
    congr 1
    funext w
    simp only [dite_eq_right j.2]
  have hv2:expectation D (fun w=>if (fun j:{j:J//j≠i}=>X j w)=t then (1:R) else 0)=
      (∏j:{j:J//j≠i},expectation D (fun w=>if X j w=t j then (1:R) else 0)):=by
    rw [hv]
    apply prod_congr rfl
    intro j _
    congr 1
    funext w
    simp only [dite_eq_right j.2]
  rw [hv2]
  exact hu2

lemma product_independent_rest {J α:Type*} [Fintype J] [DecidableEq J]
    [Fintype α] [DecidableEq α]
    (D:Design Ω I R) (hD:probabilityDesign D) (X:J→Ω→α)
    (h:∀F:J→α→R,expectation D (fun w=>∏j,F j (X j w))=
      ∏j,expectation D (fun w=>F j (X j w))) (i:J):
    independent D (X i) (fun w=>fun j:{j:J//j≠i}=>X j w):=by
  classical
  intro u v
  have expand:(fun w=>u (X i w)*v (fun j:{j:J//j≠i}=>X j w))=
      (fun w=>∑t:({j:J//j≠i}→α),
        (u (X i w)*(if (fun j:{j:J//j≠i}=>X j w)=t then 1 else 0))*v t):=by
    funext w
    simp
  rw [expand,expectation_sum]
  simp_rw [expectation_mul_const,product_factor_test D hD X h i]
  simp_rw [mul_assoc]
  rw [←mul_sum]
  congr 1
  simp_rw [←expectation_mul_const]
  rw [←expectation_sum]
  congr 1
  funext w
  simp

lemma independent_maps {α β γ δ:Type*} (D:Design Ω I R)
    (f:Ω→α) (g:Ω→β) (h:independent D f g) (φ:α→γ) (ψ:β→δ):
    independent D (fun w=>φ (f w)) (fun w=>ψ (g w)):=by
  intro u v
  exact h (fun a=>u (φ a)) (fun b=>v (ψ b))

lemma mutually_independent_leave_out_completed (D:Design Ω I R)
    (hD:probabilityDesign D) (h:mutuallyIndependentAssignments D) (i:I):
    independent D (fun w=>D.treatment w i) (fittingAssignments D (univ.erase i)):=by
  classical
  have hi:=product_independent_rest D hD (fun j w=>D.treatment w j) h i
  let ψ:({j:I//j≠i}→Bool)→(↥(univ.erase i)→Bool):=
    fun t j=>t ⟨j,(Finset.mem_erase.mp j.2).1⟩
  exact independent_comp D _ _ hi ψ

def paddedBlock {B:Type*} [DecidableEq B] (c:I→B) (b:B)
    (t:↥(univ.filter (fun j=>c j=b))→Bool):I→Bool:=
  fun j=>if h:c j=b then t ⟨j,by simp [h]⟩ else false

lemma mutually_independent_other_blocks_completed {B:Type*} [Fintype B] [DecidableEq B]
    (D:Design Ω I R) (hD:probabilityDesign D) (c:I→B)
    (h:mutuallyIndependentBlocks D c) (i:I):
    independent D (fun w=>D.treatment w i)
      (fittingAssignments D (univ.filter (fun j=>c j≠c i))):=by
  classical
  let X:B→Ω→(I→Bool):=fun b w=>
    paddedBlock c b (fittingAssignments D (univ.filter (fun j=>c j=b)) w)
  have hX:∀F:B→(I→Bool)→R,expectation D (fun w=>∏b,F b (X b w))=
      ∏b,expectation D (fun w=>F b (X b w)):=by
    intro F
    exact h (fun b t=>F b (paddedBlock c b t))
  have hi:=product_independent_rest D hD X hX (c i)
  let φ:(I→Bool)→Bool:=fun t=>t i
  let ψ:({b:B//b≠c i}→I→Bool)→(↥(univ.filter (fun j=>c j≠c i))→Bool):=
    fun t j=>t ⟨c j,(Finset.mem_filter.mp j.2).2⟩ j
  have hm:=independent_maps D _ _ hi φ ψ
  convert hm using 1
  · funext w
    simp [φ,X,paddedBlock,fittingAssignments]
  · funext w j
    simp [ψ,X,paddedBlock,fittingAssignments]

end
end AronowAudit.P026.IndependenceCompletion

namespace AronowAudit.P026
open Finset
variable {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]


end AronowAudit.P026
