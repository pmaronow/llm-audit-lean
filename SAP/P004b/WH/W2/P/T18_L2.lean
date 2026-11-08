import SAP.P004b.WH.W2.Leaves
import AronowAudit.P004.Wave1.Gap.GP0041B3
import AronowAudit.P004.Wave1.Gap.TailBIpwThreeType

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2.P.T18_L2

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000

private def leftIndex {m : ℕ} (i : Fin m) : Fin (2*m) :=
  ⟨i.val, by omega⟩

private def rightIndex {m : ℕ} (i : Fin m) : Fin (2*m) :=
  ⟨m+i.val, by omega⟩

private def pairDiff {m : ℕ} (i : Fin m) (z : Assignment (2*m)) : ℝ :=
  bit (z (leftIndex i))-bit (z (rightIndex i))

def blockSum {m : ℕ} (s : Finset (Fin m)) (z : Assignment (2*m)) : ℝ :=
  ∑ i ∈ s, pairDiff i z

private def blockSupport {m : ℕ} (s : Finset (Fin m)) : Set (Fin (2*m)) :=
  {k | ∃ i, i ∈ s ∧ (k=leftIndex i ∨ k=rightIndex i)}

private lemma left_eq_left {m : ℕ} (i j : Fin m) (h : leftIndex i = leftIndex j) : i=j := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [leftIndex] using hv

private lemma right_eq_right {m : ℕ} (i j : Fin m) (h : rightIndex i = rightIndex j) : i=j := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [rightIndex] using hv

private lemma left_ne_right {m : ℕ} (i j : Fin m) : leftIndex i ≠ rightIndex j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [leftIndex, rightIndex, Fin.val_mk] at hv
  omega

private lemma right_ne_left {m : ℕ} (i j : Fin m) : rightIndex i ≠ leftIndex j := by
  intro h
  exact left_ne_right j i h.symm

private lemma pair_mean {m : ℕ} (i : Fin m) :
    AronowAudit.P004.expect (fun _ : Fin (2*m) => (1/4 : ℝ)) (pairDiff i) = 0 := by
  unfold pairDiff
  change AronowAudit.P004.expect (fun _ : Fin (2*m) => (1/4 : ℝ))
    (fun z => bit (z (leftIndex i))-bit (z (rightIndex i))) = 0
  rw [AronowAudit.P004.expect_sub,
    AronowAudit.P004.Wave1.t18_expect_coordinate,
    AronowAudit.P004.Wave1.t18_expect_coordinate]
  norm_num [bit]

private lemma pair_square_pointwise {m : ℕ} (i : Fin m) :
    (fun z : Assignment (2*m) => (pairDiff i z)^2) = fun z =>
      bit (z (leftIndex i))+bit (z (rightIndex i))-
        2*(bit (z (leftIndex i))*bit (z (rightIndex i))) := by
  funext z
  cases h₁ : z (leftIndex i) <;> cases h₂ : z (rightIndex i) <;>
    norm_num [pairDiff, bit, h₁, h₂]

private lemma pair_cube_pointwise {m : ℕ} (i : Fin m) :
    (fun z : Assignment (2*m) => (pairDiff i z)^3) = pairDiff i := by
  funext z
  cases h₁ : z (leftIndex i) <;> cases h₂ : z (rightIndex i) <;>
    norm_num [pairDiff, bit, h₁, h₂]

private lemma pair_fourth_pointwise {m : ℕ} (i : Fin m) :
    (fun z : Assignment (2*m) => (pairDiff i z)^4) = fun z => (pairDiff i z)^2 := by
  funext z
  cases h₁ : z (leftIndex i) <;> cases h₂ : z (rightIndex i) <;>
    norm_num [pairDiff, bit, h₁, h₂]

private lemma pair_moments {m : ℕ} (i : Fin m) :
    AronowAudit.P004.expect (fun _ : Fin (2*m) => (1/4 : ℝ)) (fun z => (pairDiff i z)^2) = 3/8 ∧
    AronowAudit.P004.expect (fun _ : Fin (2*m) => (1/4 : ℝ)) (fun z => (pairDiff i z)^3) = 0 ∧
    AronowAudit.P004.expect (fun _ : Fin (2*m) => (1/4 : ℝ)) (fun z => (pairDiff i z)^4) = 3/8 := by
  let p : Fin (2*m) → ℝ := fun _ => 1/4
  have hF : ∀ z : Assignment (2*m), ∀ b : Bool,
      bit (Function.update z (leftIndex i) b (rightIndex i)) =
      bit (z (rightIndex i)) := by
    intro z b
    have hki : rightIndex i ≠ leftIndex i := by
      exact right_ne_left i i
    simp only [Function.update_of_ne hki]
  have hprod : AronowAudit.P004.expect p
      (fun z => bit (z (leftIndex i))*bit (z (rightIndex i))) = 1/16 := by
    rw [AronowAudit.P004.Wave1.TailBIpw_factor_coordinate p
      (by intro j; constructor <;> norm_num) (leftIndex i) bit
      (fun z => bit (z (rightIndex i))) hF,
      AronowAudit.P004.Wave1.t18_expect_coordinate]
    norm_num [p, bit]
  have hsq := pair_square_pointwise i
  have hleft : AronowAudit.P004.expect p (fun z => bit (z (leftIndex i))) = 1/4 := by
    change AronowAudit.P004.expect p (fun z => bit (z (leftIndex i))) = 1/4
    rw [AronowAudit.P004.Wave1.t18_expect_coordinate]
    norm_num [p, bit]
  have hright : AronowAudit.P004.expect p (fun z => bit (z (rightIndex i))) = 1/4 := by
    change AronowAudit.P004.expect p (fun z => bit (z (rightIndex i))) = 1/4
    rw [AronowAudit.P004.Wave1.t18_expect_coordinate]
    norm_num [p, bit]
  have h2 : AronowAudit.P004.expect p (fun z => (pairDiff i z)^2) = 3/8 := by
    change AronowAudit.P004.expect p (fun z => (pairDiff i z)^2) = 3/8
    rw [hsq, AronowAudit.P004.expect_sub, AronowAudit.P004.expect_add,
      AronowAudit.P004.expect_mul, hleft, hright, hprod]
    norm_num
  have h3 : AronowAudit.P004.expect p (fun z => (pairDiff i z)^3) = 0 := by
    rw [pair_cube_pointwise, pair_mean]
  have h4 : AronowAudit.P004.expect p (fun z => (pairDiff i z)^4) = 3/8 := by
    rw [pair_fourth_pointwise, h2]
  exact ⟨h2, h3, h4⟩

private lemma expect_finset_sum {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin N → ℝ) (s : Finset ι) (F : ι → Assignment N → ℝ) :
    AronowAudit.P004.expect p (fun z => ∑ i ∈ s, F i z) =
      ∑ i ∈ s, AronowAudit.P004.expect p (F i) := by
  induction s using Finset.induction_on with
  | empty => simp [AronowAudit.P004.expect]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, AronowAudit.P004.expect_add, ih]

theorem block_moments {m : ℕ} (s : Finset (Fin m)) :
    AronowAudit.P004.expect (fun _ : Fin (2*m) => (1/4 : ℝ)) (fun z => (blockSum s z)^2) =
        (3/8 : ℝ)*(s.card : ℝ) ∧
    AronowAudit.P004.expect (fun _ : Fin (2*m) => (1/4 : ℝ)) (fun z => (blockSum s z)^4) ≤
        (27/64 : ℝ)*(s.card : ℝ)^2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      constructor <;> simp [blockSum, AronowAudit.P004.expect]
  | @insert i s hi ih =>
      let p : Fin (2*m) → ℝ := fun _ => 1/4
      let U : Assignment (2*m) → ℝ := fun z => blockSum s z
      let X : Assignment (2*m) → ℝ := fun z => pairDiff i z
      have hUdep (l : ℕ) : DependsOn (fun z => (U z)^l) (blockSupport s) := by
        apply AronowAudit.P004.GraphCompletion.depends_of_update
        intro z k hk b
        change (blockSum s (Function.update z k b))^l = (blockSum s z)^l
        congr 1
        unfold blockSum
        apply Finset.sum_congr rfl
        intro j hj
        have hL : leftIndex j ≠ k := by
          intro he
          exact hk ⟨j,hj,Or.inl he.symm⟩
        have hR : rightIndex j ≠ k := by
          intro he
          exact hk ⟨j,hj,Or.inr he.symm⟩
        simp only [pairDiff, Function.update_of_ne hL, Function.update_of_ne hR]
      have hXdep (l : ℕ) : DependsOn (fun z => (X z)^l) (blockSupport s)ᶜ := by
        apply AronowAudit.P004.GraphCompletion.depends_of_update
        intro z k hk b
        have hkS : k ∈ blockSupport s := by
          by_contra h
          exact hk (by simpa using h)
        rcases hkS with ⟨j,hj,hcoord⟩
        have hji : j ≠ i := by
          intro h
          subst j
          exact hi hj
        have hL : leftIndex i ≠ k := by
          intro he
          rcases hcoord with hc | hc
          · exact hji (left_eq_left i j (he.trans hc)).symm
          · exact left_ne_right i j (he.trans hc)
        have hR : rightIndex i ≠ k := by
          intro he
          rcases hcoord with hc | hc
          · exact right_ne_left i j (he.trans hc)
          · exact hji (right_eq_right i j (he.trans hc)).symm
        change (pairDiff i (Function.update z k b))^l = (pairDiff i z)^l
        simp only [pairDiff, Function.update_of_ne hL, Function.update_of_ne hR]
      have hfac (k l : ℕ) :
          AronowAudit.P004.expect p (fun z => (X z)^k*(U z)^l) =
            AronowAudit.P004.expect p (fun z => (X z)^k)*AronowAudit.P004.expect p (fun z => (U z)^l) := by
        have hh := AronowAudit.P004.GraphCompletion.expect_mul_of_disjoint_depends
          p (blockSupport s) (fun z => (U z)^l) (fun z => (X z)^k)
          (hUdep l) (hXdep k)
        calc
          _ = expect p (fun z => (U z)^l*(X z)^k) := by
            congr 1
            funext z
            ring
          _ = expect p (fun z => (U z)^l)*expect p (fun z => (X z)^k) := hh
          _ = _ := by exact mul_comm _ _
      have hUm : AronowAudit.P004.expect p U = 0 := by
        change AronowAudit.P004.expect p (fun z => ∑ j ∈ s, pairDiff j z) = 0
        rw [expect_finset_sum]
        apply Finset.sum_eq_zero
        intro j hj
        exact pair_mean j
      have hXm : AronowAudit.P004.expect p X = 0 := by
        exact pair_mean i
      have hX3 : AronowAudit.P004.expect p (fun z => (X z)^3) = 0 := by
        change AronowAudit.P004.expect p (fun z => (pairDiff i z)^3) = 0
        rw [pair_cube_pointwise, pair_mean]
      have hX2 : AronowAudit.P004.expect p (fun z => (X z)^2) = 3/8 := (pair_moments i).1
      have hX4 : AronowAudit.P004.expect p (fun z => (X z)^4) = 3/8 := (pair_moments i).2.2
      have hodd (l : ℕ) : AronowAudit.P004.expect p (fun z => X z*(U z)^l) = 0 := by
        simpa only [pow_one, hXm, zero_mul] using hfac 1 l
      have h31 : AronowAudit.P004.expect p (fun z => (X z)^3*U z) = 0 := by
        simpa only [pow_one, hX3, hUm, zero_mul, mul_zero] using hfac 3 1
      have hU2 : AronowAudit.P004.expect p (fun z => (U z)^2) = (3/8 : ℝ)*(s.card : ℝ) := by
        exact ih.1
      have he2 : AronowAudit.P004.expect p (fun z => (U z+X z)^2) =
          AronowAudit.P004.expect p (fun z => (U z)^2)+AronowAudit.P004.expect p (fun z => (X z)^2) := by
        have he : (fun z => (U z+X z)^2) = fun z =>
            (U z)^2+2*(X z*(U z)^1)+(X z)^2 := by
          funext z
          ring
        rw [he, AronowAudit.P004.expect_add, AronowAudit.P004.expect_add,
          AronowAudit.P004.expect_mul, hodd 1]
        ring
      have he4 : AronowAudit.P004.expect p (fun z => (U z+X z)^4) =
          AronowAudit.P004.expect p (fun z => (U z)^4)+
            6*(AronowAudit.P004.expect p (fun z => (X z)^2)*AronowAudit.P004.expect p (fun z => (U z)^2))+
            AronowAudit.P004.expect p (fun z => (X z)^4) := by
        have he : (fun z => (U z+X z)^4) = fun z =>
            (U z)^4+4*(X z*(U z)^3)+6*((X z)^2*(U z)^2)+
              4*((X z)^3*U z)+(X z)^4 := by
          funext z
          ring
        rw [he, AronowAudit.P004.expect_add, AronowAudit.P004.expect_add,
          AronowAudit.P004.expect_add, AronowAudit.P004.expect_add,
          AronowAudit.P004.expect_mul, AronowAudit.P004.expect_mul,
          AronowAudit.P004.expect_mul,
          hodd 3, hfac 2 2, h31]
        ring
      have heq : blockSum (insert i s) = fun z => U z+X z := by
        funext z
        change (∑ j ∈ insert i s, pairDiff j z) = U z+X z
        rw [Finset.sum_insert hi]
        change pairDiff i z + blockSum s z = blockSum s z + pairDiff i z
        ring
      rw [heq]
      constructor
      · rw [he2, hU2, hX2, Finset.card_insert_of_notMem hi]
        push_cast
        ring
      · rw [he4, hU2, hX2, hX4, Finset.card_insert_of_notMem hi]
        push_cast
        nlinarith [ih.2]

private def halvesEquiv (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2*m) where
  toFun x := ⟨(finSumFinEquiv (m:=m) (n:=m) x).val, by
    have hh := (finSumFinEquiv (m:=m) (n:=m) x).isLt
    omega⟩
  invFun x := (finSumFinEquiv (m:=m) (n:=m)).symm
    ⟨x.val, by omega⟩
  left_inv x := by
    apply (finSumFinEquiv (m:=m) (n:=m)).injective
    apply Fin.ext
    simp
  right_inv x := by
    apply Fin.ext
    simp

private lemma sum_halves {m : ℕ} (f : Fin (2*m) → ℝ) :
    (∑ i : Fin (2*m), f i) =
      (∑ i : Fin m, f (leftIndex i))+(∑ i : Fin m, f (rightIndex i)) := by
  rw [← Equiv.sum_comp (halvesEquiv m) f, Fintype.sum_sum_type]
  have hL (i : Fin m) : halvesEquiv m (Sum.inl i) = leftIndex i := by
    apply Fin.ext
    rfl
  have hR (i : Fin m) : halvesEquiv m (Sum.inr i) = rightIndex i := by
    apply Fin.ext
    rfl
  simp_rw [hL, hR]

private lemma balanced_sign_sum (m : ℕ) :
    (∑ i : Fin (2*m), balancedSign (2*m) i) = 0 := by
  rw [sum_halves]
  have hL : (∑ i : Fin m, balancedSign (2*m) (leftIndex i)) = (m : ℝ) := by
    simp [balancedSign, leftIndex]
  have hR : (∑ i : Fin m, balancedSign (2*m) (rightIndex i)) = -(m : ℝ) := by
    simp [balancedSign, rightIndex]
  rw [hL, hR]
  ring

private lemma balanced_weighted_sum (m : ℕ) (z : Assignment (2*m)) :
    (∑ i : Fin (2*m), bit (z i)*balancedSign (2*m) i) = blockSum Finset.univ z := by
  rw [sum_halves]
  simp [blockSum, pairDiff, balancedSign, leftIndex, rightIndex,
    Finset.sum_sub_distrib]
  <;> ring

private lemma balanced_marginal {m : ℕ} (i : Fin (2*m)) (a : Bool) :
    marginal (fun _ => (1/4 : ℝ)) (balancedTable (2*m)) i a =
      balancedSign (2*m) i := by
  unfold marginal
  change AronowAudit.P004.expect (fun _ : Fin (2*m) => (1/4 : ℝ))
      (fun z => if z i = a then balancedSign (2*m) i else 0) /
        AronowAudit.P004.coin (1/4) a = balancedSign (2*m) i
  have he := AronowAudit.P004.Wave1.t18_expect_coordinate
    (fun _ : Fin (2*m) => (1/4 : ℝ)) i
    (fun b => if b=a then balancedSign (2*m) i else 0)
  rw [he]
  cases a <;> norm_num [AronowAudit.P004.coin]

private lemma balanced_means (m : ℕ) :
    barMu (fun _ => (1/4 : ℝ)) (balancedTable (2*m)) true = 0 ∧
    barMu (fun _ => (1/4 : ℝ)) (balancedTable (2*m)) false = 0 := by
  constructor <;> unfold barMu
  · simp_rw [balanced_marginal]
    rw [balanced_sign_sum]
    simp
  · simp_rw [balanced_marginal]
    rw [balanced_sign_sum]
    simp

private lemma balanced_difference_formula {m : ℕ} (hm : 0 < m)
    (z : Assignment (2*m)) :
    printedLinear (1/4) (balancedTable (2*m)) z -
      linearHajek (fun _ => (1/4 : ℝ)) (balancedTable (2*m)) z =
        ((8/3 : ℝ)/(2*m))*blockSum Finset.univ z := by
  let p : Fin (2*m) → ℝ := fun _ => 1/4
  let R : CircleTable (2*m) := balancedTable (2*m)
  have hmu := balanced_means m
  have hmuT : barMu (fun _ => (1/4 : ℝ)) R true = 0 := by
    simpa [R] using hmu.1
  have hmuF : barMu (fun _ => (1/4 : ℝ)) R false = 0 := by
    simpa [R] using hmu.2
  have hsum : (∑ i : Fin (2*m), nodeEffect p R i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    change marginal (fun _ => (1/4 : ℝ)) (balancedTable (2*m)) i true -
      marginal (fun _ => (1/4 : ℝ)) (balancedTable (2*m)) i false = 0
    rw [balanced_marginal, balanced_marginal]
    ring
  have hame : ame p R = 0 := by
    simp [ame, hsum]
  have hfalse :
      (∑ i : Fin (2*m), (1-bit (z i))*balancedSign (2*m) i) =
        -blockSum Finset.univ z := by
    calc
      _ = (∑ i : Fin (2*m), balancedSign (2*m) i) -
            (∑ i : Fin (2*m), bit (z i)*balancedSign (2*m) i) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
      _ = _ := by rw [balanced_sign_sum, balanced_weighted_sum]; ring
  have hprint : printedLinear (1/4) R z =
      (∑ i : Fin (2*m),
        (bit (z i)*balancedSign (2*m) i/(1/4) -
          (1-bit (z i))*balancedSign (2*m) i/(1/4)))/(2*m : ℝ) := by
    unfold printedLinear
    rw [hame]
    rw [hmuT, hmuF]
    simp [R, balancedTable]
  have hcorrected : linearHajek p R z =
      (∑ i : Fin (2*m),
        (bit (z i)*balancedSign (2*m) i/(1/4) -
          (1-bit (z i))*balancedSign (2*m) i/(1-1/4)))/(2*m : ℝ) := by
    unfold linearHajek augmented
    dsimp
    rw [hmuT, hmuF]
    simp [p, R, balancedTable]
  have hnumerator :
      (∑ i : Fin (2*m),
        (bit (z i)*balancedSign (2*m) i/(1/4) -
          (1-bit (z i))*balancedSign (2*m) i/(1/4))) -
      (∑ i : Fin (2*m),
        (bit (z i)*balancedSign (2*m) i/(1/4) -
          (1-bit (z i))*balancedSign (2*m) i/(1-1/4))) =
        -(8/3 : ℝ)*(∑ i : Fin (2*m),
          (1-bit (z i))*balancedSign (2*m) i) := by
    calc
      _ = ∑ i : Fin (2*m),
          ((bit (z i)*balancedSign (2*m) i/(1/4) -
            (1-bit (z i))*balancedSign (2*m) i/(1/4)) -
          (bit (z i)*balancedSign (2*m) i/(1/4) -
            (1-bit (z i))*balancedSign (2*m) i/(1-1/4))) := by
        rw [← Finset.sum_sub_distrib]
      _ = ∑ i : Fin (2*m),
          (-(8/3 : ℝ)*((1-bit (z i))*balancedSign (2*m) i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        field_simp
        ring
      _ = _ := by
        exact (Finset.mul_sum (Finset.univ : Finset (Fin (2*m)))
          (fun i => (1-bit (z i))*balancedSign (2*m) i) (-(8/3 : ℝ))).symm
  rw [hprint, hcorrected, ← sub_div, hnumerator, hfalse]
  ring

theorem scaled_error_eq {m : ℕ} (hm : 0 < m)
    (z : Assignment (2*m)) :
    Real.sqrt (2*m : ℕ) *
      (printedLinear (1/4) (balancedTable (2*m)) z -
        linearHajek (fun _ => (1/4 : ℝ)) (balancedTable (2*m)) z) =
      ((8/3 : ℝ)/Real.sqrt (2*m : ℝ))*blockSum Finset.univ z := by
  have hn : (0:ℝ) < (2*m : ℝ) := by positivity
  have hs : (Real.sqrt (2*m : ℝ))^2 = (2*m : ℝ) := Real.sq_sqrt hn.le
  have hcoef : Real.sqrt (2*m : ℝ)*((8/3 : ℝ)/(2*m : ℝ)) =
      (8/3 : ℝ)/Real.sqrt (2*m : ℝ) := by
    field_simp [hn.ne', (Real.sqrt_pos.2 hn).ne']
    nlinarith [hs]
  rw [balanced_difference_formula hm z]
  calc
    _ = (Real.sqrt (2*m : ℝ)*((8/3 : ℝ)/(2*m : ℝ)))*blockSum Finset.univ z := by
      push_cast
      ring
    _ = _ := by
      push_cast
      rw [hcoef]

end
end SAP.P004b.WH.W2.P.T18_L2

open SAP.P004b.WH.W2.P.T18_L2

theorem SAP.P004b.WH.W2.T18_L2_proof : SAP.P004b.WH.W2.T18_L2 := by
  intro m hm
  let p : Fin (2*m) → ℝ := fun _ => 1/4
  let X : Assignment (2*m) → ℝ := fun z =>
    Real.sqrt (2*m : ℕ) *
      (printedLinear (1/4) (balancedTable (2*m)) z -
        linearHajek (fun _ => (1/4 : ℝ)) (balancedTable (2*m)) z)
  let S : Assignment (2*m) → ℝ := blockSum Finset.univ
  let c : ℝ := (8/3 : ℝ)/Real.sqrt (2*m : ℝ)
  let A : Assignment (2*m) → Prop := fun z => (1/2 : ℝ) < |X z|
  have hn : (0:ℝ) < (2*m : ℝ) := by positivity
  have hmpos : (0:ℝ) < (m:ℝ) := Nat.cast_pos.mpr hm
  have hs : (Real.sqrt (2*m : ℝ))^2 = (2*m : ℝ) := Real.sq_sqrt hn.le
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos (by norm_num) (Real.sqrt_pos.2 hn)
  have hc2 : c^2 = 64/(9*(2*m : ℝ)) := by
    dsimp [c]
    rw [div_pow, hs]
    field_simp [hn.ne']
    ring
  have hc4 : c^4 = 4096/(81*(2*m : ℝ)^2) := by
    calc
      c^4 = (c^2)^2 := by ring
      _ = (64/(9*(2*m : ℝ)))^2 := by rw [hc2]
      _ = 4096/(81*(2*m : ℝ)^2) := by ring
  have hS2 : AronowAudit.P004.expect p (fun z => (S z)^2) =
      (3/8 : ℝ)*(m:ℝ) := by
    have hh := (SAP.P004b.WH.W2.P.T18_L2.block_moments (m:=m) Finset.univ).1
    simpa [S, p] using hh
  have hS4 : AronowAudit.P004.expect p (fun z => (S z)^4) ≤
      (27/64 : ℝ)*(m:ℝ)^2 := by
    have hh := (SAP.P004b.WH.W2.P.T18_L2.block_moments (m:=m) Finset.univ).2
    simpa [S, p] using hh
  have hXeq (z : Assignment (2*m)) : X z = c*S z := by
    simpa [X, S, c] using SAP.P004b.WH.W2.P.T18_L2.scaled_error_eq hm z
  have hX2 : AronowAudit.P004.expect p (fun z => (X z)^2) = 4/3 := by
    calc
      _ = AronowAudit.P004.expect p (fun z => c^2*(S z)^2) := by
        congr 1
        funext z
        rw [hXeq z]
        ring
      _ = c^2*AronowAudit.P004.expect p (fun z => (S z)^2) :=
        AronowAudit.P004.expect_mul p (c^2) (fun z => (S z)^2)
      _ = 4/3 := by
        rw [hS2, hc2]
        field_simp [Nat.cast_ne_zero.mpr (by omega : 2*m ≠ 0)]
        ring
  have hX4 : AronowAudit.P004.expect p (fun z => (X z)^4) ≤ 16/3 := by
    calc
      _ = c^4*AronowAudit.P004.expect p (fun z => (S z)^4) := by
        calc
          _ = AronowAudit.P004.expect p (fun z => c^4*(S z)^4) := by
            congr 1
            funext z
            rw [hXeq z]
            ring
          _ = _ := AronowAudit.P004.expect_mul p (c^4) (fun z => (S z)^4)
      _ ≤ c^4*((27/64 : ℝ)*(m:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hS4 (pow_nonneg hcpos.le 4)
      _ = 16/3 := by
        rw [hc4]
        field_simp [Nat.cast_ne_zero.mpr (by omega : 2*m ≠ 0)]
        ring
  have hpoint (z : Assignment (2*m)) :
      8*(X z)^2 ≤ 2+(X z)^4+14*(if A z then (1:ℝ) else 0) := by
    by_cases ht : A z
    · rw [if_pos ht]
      nlinarith [sq_nonneg ((X z)^2-4)]
    · have habs : |X z| ≤ (1/2 : ℝ) := le_of_not_gt ht
      have hx2 : (X z)^2 ≤ (1/2 : ℝ)^2 := by
        have hh := (sq_le_sq₀ (abs_nonneg (X z)) (by norm_num : (0:ℝ) ≤ 1/2)).2 habs
        nlinarith [sq_abs (X z)]
      rw [if_neg ht]
      nlinarith [sq_nonneg ((X z)^2)]
  have hmono := AronowAudit.P004.expect_mono p
      (by intro i; constructor <;> norm_num) _ _ hpoint
  have hineq : 8*AronowAudit.P004.expect p (fun z => (X z)^2) ≤
      2+AronowAudit.P004.expect p (fun z => (X z)^4)+14*AronowAudit.P004.prob p A := by
    change AronowAudit.P004.expect p (fun z => 8*(X z)^2) ≤
      AronowAudit.P004.expect p (fun z => 2+(X z)^4+14*(if A z then (1:ℝ) else 0)) at hmono
    rw [AronowAudit.P004.expect_mul, AronowAudit.P004.expect_add,
      AronowAudit.P004.expect_add, AronowAudit.P004.expect_const,
      AronowAudit.P004.expect_mul] at hmono
    change 8*AronowAudit.P004.expect p (fun z => (X z)^2) ≤
      2+AronowAudit.P004.expect p (fun z => (X z)^4)+
        14*AronowAudit.P004.prob p A
    exact hmono
  have htail : (5/21 : ℝ) ≤ AronowAudit.P004.prob p A := by
    rw [hX2] at hineq
    nlinarith [hineq, hX4]
  have htailSAP : (5/21 : ℝ) ≤ prob (fun _ : Fin (2*m) => (1/4 : ℝ)) A := by
    change (5/21 : ℝ) ≤ AronowAudit.P004.prob p A
    exact htail
  change (1/8 : ℝ) ≤ prob (fun _ : Fin (2*m) => (1/4 : ℝ)) A
  exact (by norm_num : (1/8 : ℝ) ≤ 5/21).trans htailSAP
