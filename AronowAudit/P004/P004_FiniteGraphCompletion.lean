import AronowAudit.P004.P004_RegressionCompletion
import Mathlib.Logic.Function.DependsOn

namespace AronowAudit.P004.GraphCompletion
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem depends_of_update {ι β γ : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → β) → γ) (S : Set ι)
    (hf : ∀ x k, k ∉ S → ∀ b, F (Function.update x k b) = F x) : DependsOn F S := by
  have haux : ∀ T : Finset ι, ∀ x y : ι → β,
      (∀ k ∈ S, x k=y k) → (∀ k, k ∉ T → x k=y k) → F x=F y := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro x y hxy he
      congr 1
      funext k
      exact he k (by simp)
    | @insert i T hi ih =>
      intro x y hxy he
      let x' := Function.update x i (y i)
      have hxF : F x'=F x := by
        dsimp only [x']
        by_cases his : i ∈ S
        · rw [← hxy i his, Function.update_eq_self]
        · exact hf x i his (y i)
      have hxS : ∀ k ∈ S, x' k=y k := by
        intro k hk
        by_cases hki : k=i
        · subst k; simp [x']
        · simpa [x',Function.update_of_ne hki] using hxy k hk
      have hxT : ∀ k, k ∉ T → x' k=y k := by
        intro k hk
        by_cases hki : k=i
        · subst k; simp [x']
        · rw [show x' k=x k from Function.update_of_ne hki _ _]
          exact he k (by simp [hki,hk])
      exact hxF.symm.trans (ih x' y hxS hxT)
  intro x y hxy
  exact haux Finset.univ x y hxy (by simp)

 def cubeWeight {ι : Type*} [Fintype ι] (p : ι → ℝ) (z : ι → Bool) : ℝ :=
  ∏ i, coin (p i) (z i)

theorem cube_normalized {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    (∑ z : ι → Bool, cubeWeight p z)=1 := by
  unfold cubeWeight
  rw [← Fintype.prod_sum]
  simp [coin,Fintype.sum_bool]

 def join {N : ℕ} (S : Set (Fin N)) (a : S → Bool) (b : {i : Fin N // i ∉ S} → Bool) : Assignment N :=
  (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Bool)).symm (a,b)

theorem join_left {N : ℕ} (S : Set (Fin N)) (a : S → Bool) (b : {i : Fin N // i ∉ S} → Bool) (i : S) :
    join S a b i=a i := by simp [join,Equiv.piEquivPiSubtypeProd,i.property]

theorem join_right {N : ℕ} (S : Set (Fin N)) (a : S → Bool) (b : {i : Fin N // i ∉ S} → Bool) (i : {i : Fin N // i ∉ S}) :
    join S a b i=b i := by simp [join,Equiv.piEquivPiSubtypeProd,i.property]

theorem weight_join {N : ℕ} (p : Fin N → ℝ) (S : Set (Fin N)) (a : S → Bool) (b : {i : Fin N // i ∉ S} → Bool) :
    designWeight p (join S a b)=cubeWeight (fun i:S=>p i) a*cubeWeight (fun i:{i : Fin N // i ∉ S}=>p i) b := by
  unfold designWeight cubeWeight
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [join_left]
  · apply Finset.prod_congr rfl
    intro i _
    rw [join_right]

theorem expect_split {N : ℕ} (p : Fin N → ℝ) (S : Set (Fin N)) (F : Assignment N → ℝ) :
    expect p F=∑ a : S → Bool, ∑ b : {i : Fin N // i ∉ S} → Bool,
      cubeWeight (fun i:S=>p i) a*cubeWeight (fun i:{i : Fin N // i ∉ S}=>p i) b*F (join S a b) := by
  unfold expect
  rw [← (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Bool)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ a : S → Bool, ∑ b : {i : Fin N // i ∉ S} → Bool, designWeight p (join S a b)*F (join S a b)) = _
  simp_rw [weight_join]

theorem expect_left {N : ℕ} (p : Fin N → ℝ) (S : Set (Fin N)) (F : Assignment N → ℝ)
    (hF : DependsOn F S) :
    expect p F=∑ a : S → Bool, cubeWeight (fun i:S=>p i) a*F (join S a (fun _=>false)) := by
  rw [expect_split p S]
  apply Finset.sum_congr rfl
  intro a _
  have he : ∀ b, F (join S a b)=F (join S a (fun _=>false)) := by
    intro b
    apply hF
    intro i hi
    exact (join_left S a b ⟨i,hi⟩).trans (join_left S a (fun _=>false) ⟨i,hi⟩).symm
  simp_rw [he]
  calc
    _ = (cubeWeight (fun i:S=>p i) a*F (join S a (fun _=>false)))*
        ∑ b : {i : Fin N // i ∉ S} → Bool, cubeWeight (fun i:{i : Fin N // i ∉ S}=>p i) b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by
      have hh := congrArg (fun t : ℝ => (cubeWeight (fun i:S=>p i) a*F (join S a (fun _=>false)))*t)
        (cube_normalized (fun i:{i : Fin N // i ∉ S}=>p i))
      convert hh using 1 <;> simp
      left
      apply Finset.sum_congr (by ext z; simp)
      intro z _
      unfold cubeWeight
      apply Finset.prod_congr (by ext i; simp)
      intro i _
      rfl

theorem expect_right {N : ℕ} (p : Fin N → ℝ) (S : Set (Fin N)) (G : Assignment N → ℝ)
    (hG : DependsOn G (Sᶜ)) :
    expect p G=∑ b : {i : Fin N // i ∉ S} → Bool, cubeWeight (fun i:{i : Fin N // i ∉ S}=>p i) b*G (join S (fun _=>false) b) := by
  rw [expect_split p S]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have he : ∀ a, G (join S a b)=G (join S (fun _=>false) b) := by
    intro a
    apply hG
    intro i hi
    exact (join_right S a b ⟨i,hi⟩).trans (join_right S (fun _=>false) b ⟨i,hi⟩).symm
  simp_rw [he]
  calc
    _ = (∑ a : S → Bool, cubeWeight (fun i:S=>p i) a)*
        (cubeWeight (fun i:{i : Fin N // i ∉ S}=>p i) b*G (join S (fun _=>false) b)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      have hh := congrArg (fun t : ℝ => t*(cubeWeight (fun i:{i : Fin N // i ∉ S}=>p i) b*G (join S (fun _=>false) b)))
        (cube_normalized (fun i:S=>p i))
      convert hh using 1 <;> simp
      left
      apply Finset.sum_congr (by ext z; simp)
      intro z _
      unfold cubeWeight
      apply Finset.prod_congr (by ext i; simp)
      intro i _
      rfl

theorem expect_mul_of_disjoint_depends {N : ℕ} (p : Fin N → ℝ) (S : Set (Fin N))
    (F G : Assignment N → ℝ) (hF : DependsOn F S) (hG : DependsOn G (Sᶜ)) :
    expect p (fun z=>F z*G z)=expect p F*expect p G := by
  rw [expect_split p S,expect_left p S F hF,expect_right p S G hG,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have heF : F (join S a b)=F (join S a (fun _=>false)) := by
    apply hF
    intro i hi
    exact (join_left S a b ⟨i,hi⟩).trans (join_left S a (fun _=>false) ⟨i,hi⟩).symm
  have heG : G (join S a b)=G (join S (fun _=>false) b) := by
    apply hG
    intro i hi
    exact (join_right S a b ⟨i,hi⟩).trans (join_right S (fun _=>false) b ⟨i,hi⟩).symm
  rw [heF,heG]
  ring

 def sources {N : ℕ} (R : CircleTable N) (I : Finset (Fin N)) : Set (Fin N) :=
  {k | ∃ i ∈ I, interferes R i k}

theorem residual_family_depends {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (I : Finset (Fin N)) :
    DependsOn (fun z (i:I)=>residualContrast p R g i z) (sources R I) := by
  apply depends_of_update
  intro z k hk b
  funext i
  have hni : ¬interferes R i k := by
    intro h
    exact hk ⟨i,i.property,h⟩
  have hki : k ≠ i := by
    intro h
    subst k
    exact hni (Or.inl rfl)
  have hr : R i (Function.update z k b)=R i z := by
    by_contra h
    apply hni
    right
    refine ⟨Function.update z k b,z,?_,h⟩
    intro l hl
    exact Function.update_of_ne hl _ _
  simp only [residualContrast,Function.update_of_ne hki.symm,hr]

end
end AronowAudit.P004.GraphCompletion

namespace AronowAudit.P004
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem design_dependency_graph {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N))
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hself : ∀ i, i ∈ B i)
    (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (houtside : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    FiniteDependencyGraph p (fun i z => residualContrast p R g i z) B := by
  refine ⟨hself,hsymm,?_⟩
  intro I J hsep A C
  let S:=GraphCompletion.sources R I
  have hd : Disjoint (GraphCompletion.sources R I) (GraphCompletion.sources R J) := by
    rw [Set.disjoint_left]
    intro k hkI hkJ
    obtain ⟨i,hi,hik⟩:=hkI
    obtain ⟨j,hj,hjk⟩:=hkJ
    exact houtside i j (hsep i hi j hj) ⟨k,hik,hjk⟩
  have hI := GraphCompletion.residual_family_depends p R g I
  have hJ := GraphCompletion.residual_family_depends p R g J
  have hF : DependsOn (fun z=>if A (fun i=>residualContrast p R g i z) then (1:ℝ) else 0) S := by
    intro x y hxy
    exact congrArg (fun v : I → ℝ => if A v then (1:ℝ) else 0) (hI hxy)
  have hG : DependsOn (fun z=>if C (fun j=>residualContrast p R g j z) then (1:ℝ) else 0) (Sᶜ) := by
    intro x y hxy
    have he : (fun j:J=>residualContrast p R g j x)=(fun j:J=>residualContrast p R g j y) := by
      apply hJ
      intro k hk
      exact hxy k (Set.disjoint_right.mp hd hk)
    exact congrArg (fun v : J → ℝ => if C v then (1:ℝ) else 0) he
  dsimp only [prob]
  calc
    _ = expect p (fun z=>(if A (fun i=>residualContrast p R g i z) then (1:ℝ) else 0)*
      (if C (fun j=>residualContrast p R g j z) then (1:ℝ) else 0)) := by
      apply congrArg (expect p)
      funext z
      split_ifs <;> simp_all
    _ = _ := GraphCompletion.expect_mul_of_disjoint_depends p S _ _ hF hG

end
end AronowAudit.P004
