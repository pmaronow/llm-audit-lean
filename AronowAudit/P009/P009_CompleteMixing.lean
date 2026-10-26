import Mathlib.GroupTheory.Perm.Basic
import AronowAudit.P004.P004_FiniteGraphCompletion
import AronowAudit.P009.P009_MixingBasics
import AronowAudit.P009.P009_CompleteSampling

/-!
# Complete-randomization block mixing

The finite design is invariant under coordinate permutations. Averaging arbitrary bounded
block tests over independent uniform coordinate labels is constant on injective label
samples; on every supported assignment, recoloring iid labels yields a
Bernoulli(m/n) product law. The collision probability therefore controls every joint
and marginal event. Three event errors give the full alpha supremum bound.

Incoming masks are embedded jointly by their disjoint union, and Function.extend
reconstructs the original masked vectors. Full block independence holds
under the reference law. The result with denominator n is stronger than
the bound with denominator n-K+1.
-/

namespace AronowAudit.P009.CompleteMixing
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000

def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) : Assignment n ≃ Assignment n where
  toFun z := fun i => z (σ i)
  invFun z := fun i => z (σ.symm i)
  left_inv z := by funext i; simp
  right_inv z := by funext i; simp

lemma treated_count_relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : Assignment n) :
    (∑ i, if z (σ i) then (1:ℕ) else 0) = ∑ i, if z i then (1:ℕ) else 0 :=
  Equiv.sum_comp σ (fun i => if z i then (1:ℕ) else 0)

lemma complete_mass_relabel {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (σ : Equiv.Perm (Fin n)) (z : Assignment n) : E.design.mass (relabel σ z)=E.design.mass z := by
  rw [hCR.2.2, hCR.2.2]
  change (if (∑ i, if z (σ i) then (1:ℕ) else 0)=m then _ else _) = _
  rw [treated_count_relabel]

lemma complete_mean_relabel {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (σ : Equiv.Perm (Fin n)) (F : Assignment n → ℝ) :
    mean E.design (fun z=>F (relabel σ z))=mean E.design F := by
  simpa only [mean, complete_mass_relabel E m hCR σ] using
    (relabel σ).sum_comp (fun z=>E.design.mass z*F z)

lemma product_fiber {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (q : ι → α → ℝ) (f : ι → α → β) (w : ι → β) :
    (∑ a : ι→α, if (fun i=>f i (a i))=w then ∏ i, q i (a i) else 0) =
      ∏ i, ∑ x, if f i x=w i then q i x else 0 := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (fun i=>f i (a i))=w
  · have hh (i) : f i (a i)=w i := congrFun h i
    simp only [h,ite_true,hh]
  · rw [if_neg h]
    symm
    obtain ⟨i,hi⟩ : ∃ i, f i (a i)≠w i := by
      by_contra hn
      apply h
      funext i
      exact not_ne_iff.mp (not_exists.mp hn i)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma product_recolor {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (q : ι → α → ℝ) (f : ι → α → β) (F : (ι → β) → ℝ) :
    (∑ a : ι→α, (∏ i, q i (a i))*F (fun i=>f i (a i))) =
      ∑ w : ι→β, (∏ i, ∑ x, if f i x=w i then q i x else 0)*F w := by
  calc
    _ = ∑ a : ι→α, ∑ w : ι→β,
        if (fun i=>f i (a i))=w then (∏ i,q i (a i))*F w else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp [eq_comm]
    _ = ∑ w : ι→β, ∑ a : ι→α,
        if (fun i=>f i (a i))=w then (∏ i,q i (a i))*F w else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      rw [← product_fiber q f w, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp

def colorMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

def binaryProduct (k : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : Law (Assignment k) where
  mass w := ∏ i, colorMass p (w i)
  nonneg w := Finset.prod_nonneg (fun i _=> by cases w i <;> simp [colorMass,hp.1,sub_nonneg.mpr hp.2])
  total := by
    rw [←Fintype.prod_sum]
    simp [colorMass,Fintype.sum_bool]

lemma color_frequency {n : ℕ} (hn : 0<n) (m : ℕ) (z : Assignment n)
    (hz : (∑ i, if z i then (1:ℕ) else 0)=m) (b : Bool) :
    (∑ x, if z x=b then (n:ℝ)⁻¹ else 0) = colorMass ((m:ℝ)/n) b := by
  have hnr : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have ht : (∑ x, if z x=true then (1:ℝ) else 0)=(m:ℝ) := by
    exact_mod_cast hz
  have hc : (∑ x, if z x=false then (1:ℝ) else 0)=(n:ℝ)-(m:ℝ) := by
    have hpoint (x : Fin n) : (if z x=false then (1:ℝ) else 0) = 1-(if z x=true then 1 else 0) := by
      cases z x <;> simp
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib,ht]
    simp
  cases b
  · simp only [colorMass,Bool.false_eq_true,ite_false]
    calc
      _ = (∑ x, if z x=false then (1:ℝ) else 0)*(n:ℝ)⁻¹ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> simp
      _ = _ := by rw [hc]; field_simp
  · simp only [colorMass,ite_true]
    calc
      _ = (∑ x, if z x=true then (1:ℝ) else 0)*(n:ℝ)⁻¹ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> simp
      _ = _ := by rw [ht]; ring

lemma recolor_iid {n k : ℕ} (hn : 0<n) (m : ℕ) (z : Assignment n)
    (hz : (∑ i, if z i then (1:ℕ) else 0)=m) (F : Assignment k→ℝ) :
    (∑ a : Fin k→Fin n, ((n:ℝ)⁻¹)^k*F (fun i=>z (a i))) =
      ∑ w : Assignment k, (∏ i,colorMass ((m:ℝ)/n) (w i))*F w := by
  have hh := product_recolor (fun (_ : Fin k) (_ : Fin n)=>(n:ℝ)⁻¹)
    (fun (_ : Fin k) (x : Fin n)=>z x) F
  calc
    _ = ∑ w : Assignment k, (∏ i, ∑ x, if z x=w i then (n:ℝ)⁻¹ else 0)*F w := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
      convert hh using 1
      all_goals
        apply Finset.sum_congr (by ext; simp)
        intro w _
        first
        | rfl
        | congr 1
          apply Finset.prod_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro x _
          by_cases heq : z x=w i <;> simp [heq]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact color_frequency hn m z hz (w i)

lemma mean_comm {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] (P : Law Ω) (Q : Law Λ)
    (F : Ω→Λ→ℝ) : mean P (fun x=>mean Q (F x))=mean Q (fun y=>mean P (fun x=>F x y)) := by
  unfold mean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma mean_labels_injective {n k : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (b a : Fin k→Fin n) (hb : Function.Injective b) (ha : Function.Injective a)
    (F : Assignment k→ℝ) :
    mean E.design (fun z=>F (fun i=>z (a i))) = mean E.design (fun z=>F (fun i=>z (b i))) := by
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair b a hb ha
  have heq (z : Assignment n) : (fun i=>z (a i))=(fun i=>relabel σ z (b i)) := by
    funext i
    change z (a i)=z (σ (b i))
    rw [hσ]
  simp_rw [heq]
  exact complete_mean_relabel E m hCR σ (fun z=>F (fun i=>z (b i)))

lemma binary_product_factor {k : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (S : Set (Fin k))
    (F G : Assignment k→ℝ) (hF : DependsOn F S) (hG : DependsOn G Sᶜ) :
    mean (binaryProduct k p hp) (fun w=>F w*G w)=
      mean (binaryProduct k p hp) F * mean (binaryProduct k p hp) G := by
  change AronowAudit.P004.expect (fun _=>p) (fun w=>F w*G w)=
    AronowAudit.P004.expect (fun _=>p) F*AronowAudit.P004.expect (fun _=>p) G
  exact AronowAudit.P004.GraphCompletion.expect_mul_of_disjoint_depends (fun _=>p) S F G hF hG

lemma disjoint_incoming_embedding {n : ℕ} (E : Experiment n) (i j : Fin n)
    (hij : d E i j=0) :
    ∃ b : Fin (incoming E i+incoming E j)→Fin n, Function.Injective b ∧
      ∀ l, Interferes E l i ∨ Interferes E l j → ∃ r,b r=l := by
  let S := Finset.univ.filter (fun l=>Interferes E l i)
  let T := Finset.univ.filter (fun l=>Interferes E l j)
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro l hlS hlT
    have hh : Dependent E i j := ⟨l,(Finset.mem_filter.mp hlS).2,(Finset.mem_filter.mp hlT).2⟩
    simp [d,hh] at hij
  have hc : (S∪T).card=incoming E i+incoming E j := by
    rw [Finset.card_union_of_disjoint hd]
    rfl
  let e := (S∪T).equivFinOfCardEq hc
  refine ⟨fun r=>(e.symm r).val,?_,?_⟩
  · intro a b hab
    exact e.symm.injective (Subtype.ext hab)
  · intro l hl
    have hu : l∈S∪T := by simpa [S,T] using hl
    refine ⟨e ⟨l,hu⟩,?_⟩
    simp

lemma masked_extend_reconstruct {n k : ℕ} (E : Experiment n) (i : Fin n)
    (b : Fin k→Fin n) (hb : Function.Injective b)
    (hc : ∀ l,Interferes E l i→∃ r,b r=l) (z : Assignment n) :
    masked E i (Function.extend b (fun r=>z (b r)) (fun _=>false))=masked E i z := by
  funext l
  unfold masked
  by_cases hl : Interferes E l i
  · obtain ⟨r,rfl⟩ := hc l hl
    simp only [hl,ite_true,hb.extend_apply]
  · simp [hl]

lemma masked_extend_depends {n k : ℕ} (E : Experiment n) (i : Fin n)
    (b : Fin k→Fin n) (hb : Function.Injective b)
    (hc : ∀ l,Interferes E l i→∃ r,b r=l) :
    DependsOn (fun w : Assignment k=>masked E i (Function.extend b w (fun _=>false)))
      {r|Interferes E (b r) i} := by
  intro w v hw
  funext l
  unfold masked
  by_cases hl : Interferes E l i
  · obtain ⟨r,rfl⟩ := hc l hl
    simp only [hl,ite_true,hb.extend_apply]
    exact hw r hl
  · simp [hl]

lemma masked_extend_pair_factor {n k : ℕ} (E : Experiment n) (i j : Fin n)
    (hij : d E i j=0) (b : Fin k→Fin n) (hb : Function.Injective b)
    (hc : ∀ l,Interferes E l i ∨ Interferes E l j→∃ r,b r=l)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (S T : Set (Assignment n)) :
    prob (binaryProduct k p hp) (fun w=>masked E i (Function.extend b w (fun _=>false))∈S ∧
      masked E j (Function.extend b w (fun _=>false))∈T) =
    prob (binaryProduct k p hp) (fun w=>masked E i (Function.extend b w (fun _=>false))∈S)*
    prob (binaryProduct k p hp) (fun w=>masked E j (Function.extend b w (fun _=>false))∈T) := by
  let X := fun w : Assignment k=>masked E i (Function.extend b w (fun _=>false))
  let Y := fun w : Assignment k=>masked E j (Function.extend b w (fun _=>false))
  let F := fun w=>if X w∈S then (1:ℝ) else 0
  let G := fun w=>if Y w∈T then (1:ℝ) else 0
  have hX := masked_extend_depends E i b hb (fun l hl=>hc l (Or.inl hl))
  have hY := masked_extend_depends E j b hb (fun l hl=>hc l (Or.inr hl))
  have hF : DependsOn F {r|Interferes E (b r) i} := by
    intro w v hw
    dsimp [F,X]
    have heq := hX hw
    dsimp only at heq
    simp only [heq]
  have hG : DependsOn G ({r|Interferes E (b r) i}ᶜ) := by
    intro w v hw
    dsimp [G,Y]
    have heq := hY (fun r hr=>hw r (by
      intro hi
      have hh : Dependent E i j := ⟨b r,hi,hr⟩
      simp [d,hh] at hij))
    dsimp only at heq
    simp only [heq]
  have hh := binary_product_factor p hp {r|Interferes E (b r) i} F G hF hG
  convert hh using 1
  unfold prob
  congr 1
  funext w
  dsimp [F,G,X,Y]
  split_ifs <;> simp_all
  all_goals rfl

lemma complete_recolor_average {n k : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (hp : 0 ≤ (m:ℝ)/n ∧ (m:ℝ)/n ≤ 1) (F : Assignment k→ℝ) :
    (∑ a : Fin k→Fin n, ((n:ℝ)⁻¹)^k * mean E.design (fun z=>F (fun i=>z (a i)))) =
      mean (binaryProduct k ((m:ℝ)/n) hp) F := by
  have hn : 0<n := lt_trans hCR.1 hCR.2.1
  calc
    _ = ∑ z, E.design.mass z * (∑ a : Fin k→Fin n, ((n:ℝ)⁻¹)^k*F (fun i=>z (a i))) := by
      unfold mean
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ z, E.design.mass z * mean (binaryProduct k ((m:ℝ)/n) hp) F := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : (∑ i, if z i then (1:ℕ) else 0)=m
      · rw [recolor_iid hn m z hz F]
        rfl
      · have hm : E.design.mass z=0 := by rw [hCR.2.2 z]; exact if_neg hz
        simp [hm]
    _ = _ := by rw [←Finset.sum_mul,E.design.total,one_mul]

lemma mean_unit_interval {Ω : Type*} [Fintype Ω] (P : Law Ω) (F : Ω→ℝ)
    (hF : ∀ w,0 ≤ F w ∧ F w ≤ 1) : 0 ≤ mean P F ∧ mean P F ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun w _=>mul_nonneg (P.nonneg w) (hF w).1)
  · rw [←mean_const P 1]
    apply Finset.sum_le_sum
    intro w _
    exact mul_le_mul_of_nonneg_left (hF w).2 (P.nonneg w)

lemma fixed_count_fraction {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m) :
    0 ≤ (m:ℝ)/n ∧ (m:ℝ)/n ≤ 1 := by
  have hn : (0:ℝ)<n := by exact_mod_cast (lt_trans hCR.1 hCR.2.1)
  constructor
  · positivity
  · exact (div_le_one hn).mpr (by exact_mod_cast hCR.2.1.le)

lemma complete_sampling_event_bound {n k : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (b : Fin k→Fin n) (hb : Function.Injective b) (F : Assignment k→ℝ)
    (hF : ∀ w,0 ≤ F w ∧ F w ≤ 1) :
    |mean E.design (fun z=>F (fun r=>z (b r))) -
      mean (binaryProduct k ((m:ℝ)/n) (fixed_count_fraction E m hCR)) F|  ≤ 
      (k:ℝ)*((k:ℝ)-1)/(2*n) := by
  have hn : 0<n := lt_trans hCR.1 hCR.2.1
  let L := fun a : Fin k→Fin n=>mean E.design (fun z=>F (fun r=>z (a r)))
  let c := mean E.design (fun z=>F (fun r=>z (b r)))
  have hL (a) : 0 ≤ L a ∧ L a ≤ 1 := mean_unit_interval E.design _ (fun z=>hF _)
  have hc : 0 ≤ c ∧ c ≤ 1 := mean_unit_interval E.design _ (fun z=>hF _)
  have hi (a : Fin k→Fin n) (ha : Function.Injective a) : L a=c :=
    mean_labels_injective E m hCR b a hb ha F
  have htest := CompleteSampling.bounded_test_comparison n k hn L c hL hc hi
  have hav : mean (CompleteSampling.labelLaw n k hn) L =
      mean (binaryProduct k ((m:ℝ)/n) (fixed_count_fraction E m hCR)) F := by
    exact complete_recolor_average E m hCR (fixed_count_fraction E m hCR) F
  rw [hav,abs_sub_comm] at htest
  exact htest.trans (CompleteSampling.noninjective_probability_le n k hn)

lemma complete_sampling_probability_bound {n k : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (b : Fin k→Fin n) (hb : Function.Injective b) (A : Assignment k→Prop) :
    |prob E.design (fun z=>A (fun r=>z (b r))) -
      prob (binaryProduct k ((m:ℝ)/n) (fixed_count_fraction E m hCR)) A| ≤
      (k:ℝ)*((k:ℝ)-1)/(2*n) :=
  complete_sampling_event_bound E m hCR b hb (fun w=>if A w then 1 else 0)
    (fun w=>by split_ifs <;> norm_num)

lemma complete_mask_alpha_collision {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (i j : Fin n) (hij : d E i j=0) :
    alpha E.design (masked E i) (masked E j) ≤
      3*((incoming E i+incoming E j:ℕ):ℝ)*(((incoming E i+incoming E j:ℕ):ℝ)-1)/(2*n) := by
  let k := incoming E i+incoming E j
  obtain ⟨b,hb,hcover⟩ := disjoint_incoming_embedding E i j hij
  let Q := binaryProduct k ((m:ℝ)/n) (fixed_count_fraction E m hCR)
  let X := fun w : Assignment k=>masked E i (Function.extend b w (fun _=>false))
  let Y := fun w : Assignment k=>masked E j (Function.extend b w (fun _=>false))
  have hX (z : Assignment n) : X (fun r=>z (b r))=masked E i z :=
    masked_extend_reconstruct E i b hb (fun l hl=>hcover l (Or.inl hl)) z
  have hY (z : Assignment n) : Y (fun r=>z (b r))=masked E j z :=
    masked_extend_reconstruct E j b hb (fun l hl=>hcover l (Or.inr hl)) z
  apply MixingBasics.alpha_le_of_event_bound
  intro S T
  have ha := complete_sampling_probability_bound E m hCR b hb (fun w=>X w∈S)
  have hbb := complete_sampling_probability_bound E m hCR b hb (fun w=>Y w∈T)
  have hjoint := complete_sampling_probability_bound E m hCR b hb (fun w=>X w∈S ∧ Y w∈T)
  have hpa : (fun z : Assignment n=>X (fun r=>z (b r))∈S)=(fun z=>masked E i z∈S) := by
    funext z
    exact congrArg (fun w : Assignment n=>w∈S) (hX z)
  have hpb : (fun z : Assignment n=>Y (fun r=>z (b r))∈T)=(fun z=>masked E j z∈T) := by
    funext z
    exact congrArg (fun w : Assignment n=>w∈T) (hY z)
  have hpab : (fun z : Assignment n=>X (fun r=>z (b r))∈S ∧ Y (fun r=>z (b r))∈T)=
      (fun z=>masked E i z∈S ∧ masked E j z∈T) := by
    funext z
    exact congrArg₂ And (congrArg (fun w : Assignment n=>w∈S) (hX z))
      (congrArg (fun w : Assignment n=>w∈T) (hY z))
  rw [hpa] at ha
  rw [hpb] at hbb
  rw [hpab] at hjoint
  have hind : prob Q (fun w=>X w∈S ∧ Y w∈T)=
      prob Q (fun w=>X w∈S)*prob Q (fun w=>Y w∈T) :=
    masked_extend_pair_factor E i j hij b hb hcover ((m:ℝ)/n) (fixed_count_fraction E m hCR) S T
  change |_ - prob Q (fun w=>X w∈S ∧ Y w∈T)| ≤ _ at hjoint
  rw [hind] at hjoint
  have hh := MixingBasics.three_error_transfer _ _ _ _ _ _
    ⟨probability_nonnegative E.design (fun z=>masked E i z∈S),
      MixingBasics.probability_le_one E.design (fun z=>masked E i z∈S)⟩
    ⟨probability_nonnegative Q (fun w=>Y w∈T),
      MixingBasics.probability_le_one Q (fun w=>Y w∈T)⟩ hjoint ha hbb
  convert hh using 1 <;> ring

lemma incoming_positive {n : ℕ} (E : Experiment n) (i : Fin n) : 1 ≤ incoming E i := by
  apply Finset.one_le_card.mpr
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,Or.inl rfl⟩⟩

theorem complete_mask_mixing_finite_completed {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (i j : Fin n) (hij : d E i j = 0)
    (hsmall : incoming E i+incoming E j ≤ n) :
    let K := (incoming E i+incoming E j : ℕ)
    alpha E.design (masked E i) (masked E j) ≤
      3*(K:ℝ)*((K:ℝ)-1)/(2*((n:ℝ)-K+1)) := by
  dsimp only
  let k := incoming E i+incoming E j
  have hk : 1 ≤ k := by
    dsimp [k]
    have hi := incoming_positive E i
    omega
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hsmallr : (k:ℝ) ≤ n := by exact_mod_cast hsmall
  have hnum : 0 ≤ (k:ℝ)*((k:ℝ)-1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hd : 0 < 2*((n:ℝ)-k+1) := by linarith
  have hd' : 2*((n:ℝ)-k+1) ≤ 2*n := by linarith
  have hdiv := div_le_div_of_nonneg_left hnum hd hd'
  calc
    _ ≤ 3*(k:ℝ)*((k:ℝ)-1)/(2*n) := complete_mask_alpha_collision E m hCR i j hij
    _ = 3*((k:ℝ)*((k:ℝ)-1)/(2*n)) := by ring
    _ ≤ 3*((k:ℝ)*((k:ℝ)-1)/(2*((n:ℝ)-k+1))) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ = _ := by dsimp only [k]; ring

end
end AronowAudit.P009.CompleteMixing

namespace AronowAudit.P009
open Filter
open scoped Topology BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
theorem complete_mask_mixing_finite {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (i j : Fin n) (hij : d E i j = 0)
    (hsmall : incoming E i+incoming E j ≤ n) :
    let K := (incoming E i+incoming E j : ℕ)
    alpha E.design (masked E i) (masked E j) ≤
      3*(K:ℝ)*((K:ℝ)-1)/(2*((n:ℝ)-K+1)) := by
  exact CompleteMixing.complete_mask_mixing_finite_completed E m hCR i j hij hsmall

end
end AronowAudit.P009
