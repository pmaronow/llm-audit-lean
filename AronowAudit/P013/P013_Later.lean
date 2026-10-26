import Mathlib.Tactic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators

/-!
Finite school randomization models for P013. The school labels below are invented
positions in fourteen blocks; no data file or actual school identifier is used.
Uniform laws are represented by finite sums over their exact supports.
-/
namespace AronowAudit.P013
open scoped BigOperators
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- "56 schools ... via block randomization", Section 10, p. 1934.
The model has fourteen four-school blocks (P013-N016).
School (b,r) has artificial one-based label 4b+r+1. -/
abbrev School := Fin 14 × Fin 4

/-- The six equally likely two-of-four selections in a block. P013-N016, correction P013-T26; the article states block randomization. -/
def schoolBlockChoices : Finset (Finset (Fin 4)) := univ.powersetCard 2

/-- Design B: one independent uniform two-of-four selection per block,
with all fourteen selections retained in the support. P013-N016, P013-T26. -/
def schoolBSupport : Finset (Fin 14 → Finset (Fin 4)) :=
  Fintype.piFinset (fun _ => schoolBlockChoices)

/-- Design C: every size-28 subset of the 56 schools, equally likely.
This is the released school call's target law, not its 10,000-draw frequencies.
P013-N016, P013-T25,T26. -/
def schoolCSupport : Finset (Finset School) := (univ : Finset School).powersetCard 28

/-- Hosting vector corresponding to a block-selection array; this embeds
B's support into complete school assignments. P013-N016, P013-T26(a). -/
def blockSchoolHosts (z : Fin 14 → Finset (Fin 4)) : Finset School :=
  univ.filter (fun a => a.2 ∈ z a.1)

/-- Exact expectation under a uniform finite randomization support. Only
nonempty supports are used below. P013-N016, P013-T25,T26. -/
def uniformSchoolMean {α : Type*} (S : Finset α) (X : α → ℝ) : ℝ :=
  (∑ z ∈ S, X z) / (S.card : ℝ)

/-- Exact event probability = favourable count / support count under a
uniform finite design. P013-N016, P013-T25,T26. -/
def uniformSchoolProbability {α : Type*} (S : Finset α) (A : α → Prop) [DecidablePred A] : ℝ :=
  ((S.filter A).card : ℝ) / (S.card : ℝ)

/-- Exact randomization variance E[X²]−E[X]² under the uniform school law,
expression (2), p. 1919; P013-N016, P013-T25. -/
def uniformSchoolVariance {α : Type*} (S : Finset α) (X : α → ℝ) : ℝ :=
  uniformSchoolMean S (fun z => X z ^ 2) - (uniformSchoolMean S X)^2

/-- Probability is the expectation of its 0--1 event indicator. Supporting
finite identity for P013-T25,T26, P013-N016. -/
theorem uniform_school_probability_mean {α : Type*} (S : Finset α) (A : α → Prop) [DecidablePred A] :
    uniformSchoolProbability S A = uniformSchoolMean S (fun z => if A z then 1 else 0) := by
  classical
  simp [uniformSchoolProbability, uniformSchoolMean, sum_boole]

/-- A uniform expectation preserves constants on a nonempty support.
Supporting finite identity for P013-T25,T26, P013-N016. -/
theorem uniform_school_mean_const {α : Type*} (S : Finset α) (hS : S.Nonempty) (c : ℝ) :
    uniformSchoolMean S (fun _ => c) = c := by
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (card_pos.mpr hS)
  simp [uniformSchoolMean, hn]

/-- Uniform expectation distributes over addition. Supporting finite
identity for P013-T25,T26, P013-N016. -/
theorem uniform_school_mean_add {α : Type*} (S : Finset α) (X Y : α → ℝ) :
    uniformSchoolMean S (fun z => X z + Y z) =
      uniformSchoolMean S X + uniformSchoolMean S Y := by
  simp [uniformSchoolMean, sum_add_distrib, add_div]

/-- Uniform expectation distributes over subtraction. Supporting finite
identity for P013-T25,T26, P013-N016. -/
theorem uniform_school_mean_sub {α : Type*} (S : Finset α) (X Y : α → ℝ) :
    uniformSchoolMean S (fun z => X z - Y z) =
      uniformSchoolMean S X - uniformSchoolMean S Y := by
  simp [uniformSchoolMean, sum_sub_distrib, sub_div]

/-- A constant factor leaves uniform expectation. Supporting finite
identity for P013-T25,T26, P013-N016. -/
theorem uniform_school_mean_mul {α : Type*} (S : Finset α) (X : α → ℝ) (c : ℝ) :
    uniformSchoolMean S (fun z => c * X z) = c * uniformSchoolMean S X := by
  simp [uniformSchoolMean, ← mul_sum, mul_div_assoc]

/-- The one-block support has six assignments. P013-T26(a), P013-N016. -/
theorem school_block_choice_count : schoolBlockChoices.card = 6 := by
  norm_num [schoolBlockChoices, card_powersetCard, Nat.choose]

/-- Exact assignment counts of B and C, without enumerating either
large support. P013-T26(a), P013-N016. -/
theorem school_assignment_counts :
    schoolBSupport.card = 6^14 ∧ schoolBSupport.card = 78364164096 ∧
    schoolCSupport.card = Nat.choose 56 28 ∧ schoolCSupport.card = 7648690600760440 := by
  have hb : schoolBSupport.card = 6^14 := by
    simp [schoolBSupport, Fintype.card_piFinset, school_block_choice_count]
  have hc : schoolCSupport.card = Nat.choose 56 28 := by
    simp [schoolCSupport, card_powersetCard, School]
  refine ⟨hb, ?_, hc, ?_⟩
  · rw [hb]; norm_num
  · rw [hc, Nat.choose_eq_factorial_div_factorial (by norm_num : 28 ≤ 56)]
    norm_num [Nat.factorial]

/-- B and C have nonempty exact supports. Supporting domain fact for
P013-T25,T26, P013-N016. -/
theorem school_supports_nonempty : schoolBSupport.Nonempty ∧ schoolCSupport.Nonempty := by
  constructor
  · apply card_pos.mp; rw [school_assignment_counts.2.1]; norm_num
  · apply card_pos.mp; rw [school_assignment_counts.2.2.2]; norm_num

/-- A given school is selected in three of the six assignments of its
block. P013-T26(b), P013-N016. -/
theorem school_local_marginal_count (a : Fin 4) :
    (schoolBlockChoices.filter (fun S => a ∈ S)).card = 3 := by
  have he : schoolBlockChoices.filter (fun S => a ∈ S) =
      schoolBlockChoices.filter (fun S => ({a} : Finset (Fin 4)) ⊆ S) := by
    ext S; simp
  rw [he, schoolBlockChoices,
    card_filter_powersetCard_subset {a} univ 2 (by simp) (by simp)]
  norm_num [Nat.choose]

/-- A fixed pair of distinct schools of one block is selected together
in one of the six assignments. P013-T26(c), P013-N016. -/
theorem school_local_joint_count (a b : Fin 4) (hab : a ≠ b) :
    (schoolBlockChoices.filter (fun S => a ∈ S ∧ b ∈ S)).card = 1 := by
  have he : schoolBlockChoices.filter (fun S => a ∈ S ∧ b ∈ S) =
      schoolBlockChoices.filter (fun S => ({a,b} : Finset (Fin 4)) ⊆ S) := by
    ext S; simp only [mem_filter, insert_subset_iff, singleton_subset_iff]
  rw [he, schoolBlockChoices,
    card_filter_powersetCard_subset {a,b} univ 2 (by simp) (by simp [hab])]
  norm_num [hab]

/-- Restricting a single block restricts just that coordinate in the exact
product support. Supporting counting lemma for P013-T26(b,c), P013-N016. -/
theorem school_filter_one_block (b : Fin 14) (A : Finset (Fin 4) → Prop) [DecidablePred A] :
    schoolBSupport.filter (fun z => A (z b)) =
      Fintype.piFinset (fun t => if t = b then schoolBlockChoices.filter A else schoolBlockChoices) := by
  classical
  ext z
  simp only [schoolBSupport, mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hz, hA⟩ t
    by_cases ht : t = b
    · subst t; simp [hz b,hA]
    · simp [ht,hz t]
  · intro hz
    have hb := hz b
    simp only [ite_true, mem_filter] at hb
    refine ⟨?_, hb.2⟩
    intro t
    by_cases ht : t = b
    · subst t; exact hb.1
    · simpa [ht] using hz t

/-- Two different block restrictions constrain their own coordinates of
B's product support. Supporting counting lemma for P013-T26(c), P013-N016. -/
theorem school_filter_two_blocks (b c : Fin 14) (hbc : b ≠ c)
    (A B : Finset (Fin 4) → Prop) [DecidablePred A] [DecidablePred B] :
    schoolBSupport.filter (fun z => A (z b) ∧ B (z c)) =
      Fintype.piFinset (fun t => if t = b then schoolBlockChoices.filter A
        else if t = c then schoolBlockChoices.filter B else schoolBlockChoices) := by
  classical
  ext z
  simp only [schoolBSupport, mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hz, hA, hB⟩ t
    by_cases ht : t = b
    · subst t; simp [hz b,hA]
    · by_cases hc : t = c
      · subst t; simp [Ne.symm hbc,hz c,hB]
      · simp [ht,hc,hz t]
  · intro hz
    have hb := hz b
    have hc := hz c
    simp only [ite_true, mem_filter] at hb
    simp only [Ne.symm hbc, ite_false, ite_true, mem_filter] at hc
    refine ⟨?_, hb.2, hc.2⟩
    intro t
    by_cases ht : t = b
    · subst t; exact hb.1
    · by_cases hc' : t = c
      · subst t; exact hc.1
      · simpa [ht, hc'] using hz t

/-- One exceptional factor in fourteen independent block counts.
Supporting finite count identity, P013-T26(b,c), P013-N016. -/
theorem school_product_one (b : Fin 14) (m n : ℕ) :
    (∏ t : Fin 14, if t = b then m else n) = m * n^13 := by
  rw [← prod_erase_mul _ _ (mem_univ b)]
  have hp : (∏ t ∈ univ.erase b, if t = b then m else n) = n^13 := by
    calc
      _ = ∏ _t ∈ (univ : Finset (Fin 14)).erase b, n := by
        apply prod_congr rfl
        intro t ht; simp [(mem_erase.mp ht).1]
      _ = n^13 := by simp
  rw [hp]; simp; ring

/-- Two exceptional factors in fourteen independent block counts.
Supporting finite count identity, P013-T26(c), P013-N016. -/
theorem school_product_two (b c : Fin 14) (hbc : b ≠ c) (m n k : ℕ) :
    (∏ t : Fin 14, if t = b then m else if t = c then n else k) = m * n * k^12 := by
  rw [← prod_erase_mul _ _ (mem_univ b)]
  rw [← prod_erase_mul _ _ (by simp [Ne.symm hbc] : c ∈ (univ : Finset (Fin 14)).erase b)]
  have hp : (∏ t ∈ (univ.erase b).erase c, if t = b then m else if t = c then n else k) = k^12 := by
    calc
      _ = ∏ _t ∈ ((univ : Finset (Fin 14)).erase b).erase c, k := by
        apply prod_congr rfl
        intro t ht
        simp [(mem_erase.mp (mem_erase.mp ht).2).1, (mem_erase.mp ht).1]
      _ = k^12 := by simp [hbc, Ne.symm hbc]
  rw [hp]; simp [hbc, Ne.symm hbc]; ring

/-- Exact marginal probability 1/2 under the stated blocked lottery.
P013-T26(b), P013-N016. -/
theorem school_B_marginal (a : School) :
    uniformSchoolProbability schoolBSupport (fun z => a.2 ∈ z a.1) = 1/2 := by
  unfold uniformSchoolProbability
  rw [school_filter_one_block a.1 (fun S => a.2 ∈ S), Fintype.card_piFinset]
  simp only [apply_ite, school_local_marginal_count, school_block_choice_count]
  rw [school_product_one, school_assignment_counts.1]
  norm_num

/-- B's joint hosting probability is 1/6 in one block and 1/4 across
blocks. P013-T26(c), P013-N016. -/
theorem school_B_joint (a b : School) (hab : a ≠ b) :
    uniformSchoolProbability schoolBSupport
      (fun z => a.2 ∈ z a.1 ∧ b.2 ∈ z b.1) =
      if a.1 = b.1 then 1/6 else 1/4 := by
  by_cases hblock : a.1 = b.1
  · have hlocal : a.2 ≠ b.2 := fun h => hab (Prod.ext hblock h)
    simp only [hblock, ite_true]
    unfold uniformSchoolProbability
    rw [school_filter_one_block b.1 (fun S => a.2 ∈ S ∧ b.2 ∈ S), Fintype.card_piFinset]
    simp only [apply_ite, school_local_joint_count _ _ hlocal, school_block_choice_count]
    rw [school_product_one, school_assignment_counts.1]
    norm_num
  · simp only [hblock, ite_false]
    unfold uniformSchoolProbability
    rw [school_filter_two_blocks a.1 b.1 hblock (fun S => a.2 ∈ S) (fun S => b.2 ∈ S), Fintype.card_piFinset]
    have hcount : (fun t : Fin 14 =>
        (if t = a.1 then schoolBlockChoices.filter (fun S => a.2 ∈ S)
         else if t = b.1 then schoolBlockChoices.filter (fun S => b.2 ∈ S)
         else schoolBlockChoices).card) =
        (fun t => if t = a.1 then 3 else if t = b.1 then 3 else 6) := by
      funext t
      by_cases ha : t = a.1
      · simp only [ha,ite_true,school_local_marginal_count]
      · by_cases hb : t = b.1
        · simp only [hb,Ne.symm hblock,ite_false,ite_true,school_local_marginal_count]
        · simp only [ha,hb,ite_false,school_block_choice_count]
    rw [hcount]
    rw [school_product_two _ _ hblock, school_assignment_counts.1]
    norm_num

/-- C's single-school hosting probability is C(55,27)/C(56,28)=1/2,
computed by fixing the chosen school. P013-T26(b), P013-N016. -/
theorem school_C_marginal (a : School) :
    uniformSchoolProbability schoolCSupport (fun z => a ∈ z) = 1/2 := by
  have he : schoolCSupport.filter (fun z => a ∈ z) =
      schoolCSupport.filter (fun z => ({a} : Finset School) ⊆ z) := by
    ext z; simp
  unfold uniformSchoolProbability
  rw [he, schoolCSupport,
    card_filter_powersetCard_subset {a} univ 28 (by simp) (by simp), card_powersetCard]
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin, card_singleton]
  norm_num only
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num : 27 ≤ 55),
    Nat.choose_eq_factorial_div_factorial (by norm_num : 28 ≤ 56)]
  norm_num [Nat.factorial]

/-- C's distinct-school joint is C(54,26)/C(56,28)=27/110,
computed by fixing both hosts. P013-T26(d), P013-N016. -/
theorem school_C_joint (a b : School) (hab : a ≠ b) :
    uniformSchoolProbability schoolCSupport (fun z => a ∈ z ∧ b ∈ z) = 27/110 := by
  have he : schoolCSupport.filter (fun z => a ∈ z ∧ b ∈ z) =
      schoolCSupport.filter (fun z => ({a,b} : Finset School) ⊆ z) := by
    ext z; simp only [mem_filter, insert_subset_iff, singleton_subset_iff]
  unfold uniformSchoolProbability
  rw [he, schoolCSupport,
    card_filter_powersetCard_subset {a,b} univ 28 (by simp) (by simp [hab]), card_powersetCard]
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin, card_pair hab]
  norm_num only
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num : 26 ≤ 54),
    Nat.choose_eq_factorial_div_factorial (by norm_num : 28 ≤ 56)]
  norm_num [Nat.factorial]

/-- The released law's exact joint differences from the stated law are
13/165 in one block and −1/220 across blocks. P013-T26(e), P013-N016. -/
theorem school_joint_differences :
    (27/110 : ℝ) - 1/6 = 13/165 ∧ (27/110 : ℝ) - 1/4 = -(1/220) := by norm_num


/-- With both hosting marginals 1/2, a joint probability p determines the
other three pair probabilities. Supporting identity for P013-T26(f), P013-N016. -/
theorem uniform_school_pair_law {α : Type*} (S : Finset α) (hS : S.Nonempty)
    (A B : α → Prop) [DecidablePred A] [DecidablePred B] (p : ℝ)
    (hA : uniformSchoolProbability S A = 1/2)
    (hB : uniformSchoolProbability S B = 1/2)
    (hp : uniformSchoolProbability S (fun z => A z ∧ B z) = p) :
    uniformSchoolProbability S (fun z => ¬ A z ∧ ¬ B z) = p ∧
    uniformSchoolProbability S (fun z => ¬ A z ∧ B z) = 1/2-p ∧
    uniformSchoolProbability S (fun z => A z ∧ ¬ B z) = 1/2-p := by
  have h00 : (fun z => if ¬ A z ∧ ¬ B z then (1 : ℝ) else 0) =
      (fun z => 1 - (if A z then 1 else 0) - (if B z then 1 else 0) +
        (if A z ∧ B z then 1 else 0)) := by
    funext z; by_cases ha : A z <;> by_cases hb : B z <;> simp [ha,hb]
  have h01 : (fun z => if ¬ A z ∧ B z then (1 : ℝ) else 0) =
      (fun z => (if B z then 1 else 0) - (if A z ∧ B z then 1 else 0)) := by
    funext z; by_cases ha : A z <;> by_cases hb : B z <;> simp [ha,hb]
  have h10 : (fun z => if A z ∧ ¬ B z then (1 : ℝ) else 0) =
      (fun z => (if A z then 1 else 0) - (if A z ∧ B z then 1 else 0)) := by
    funext z; by_cases ha : A z <;> by_cases hb : B z <;> simp [ha,hb]
  refine ⟨?_, ?_, ?_⟩
  · rw [uniform_school_probability_mean, h00, uniform_school_mean_add,
      uniform_school_mean_sub, uniform_school_mean_sub, uniform_school_mean_const S hS,
      ← uniform_school_probability_mean, ← uniform_school_probability_mean,
      ← uniform_school_probability_mean, hA, hB, hp]
    ring
  · rw [uniform_school_probability_mean, h01, uniform_school_mean_sub,
      ← uniform_school_probability_mean, ← uniform_school_probability_mean, hB, hp]
  · rw [uniform_school_probability_mean, h10, uniform_school_mean_sub,
      ← uniform_school_probability_mean, ← uniform_school_probability_mean, hA, hp]

/-- The full (00),(01),(10),(11) hosting pair law under B, with same-block
p=1/6 or different-block p=1/4. P013-T26(f), P013-N016. -/
theorem school_B_pair_distribution (a b : School) (hab : a ≠ b) :
    let p : ℝ := if a.1 = b.1 then 1/6 else 1/4
    uniformSchoolProbability schoolBSupport (fun z => a.2 ∉ z a.1 ∧ b.2 ∉ z b.1) = p ∧
    uniformSchoolProbability schoolBSupport (fun z => a.2 ∉ z a.1 ∧ b.2 ∈ z b.1) = 1/2-p ∧
    uniformSchoolProbability schoolBSupport (fun z => a.2 ∈ z a.1 ∧ b.2 ∉ z b.1) = 1/2-p ∧
    uniformSchoolProbability schoolBSupport (fun z => a.2 ∈ z a.1 ∧ b.2 ∈ z b.1) = p := by
  dsimp only
  exact ⟨(uniform_school_pair_law schoolBSupport school_supports_nonempty.1
    (fun z => a.2 ∈ z a.1) (fun z => b.2 ∈ z b.1) _
    (school_B_marginal a) (school_B_marginal b) (school_B_joint a b hab)).1,
    (uniform_school_pair_law schoolBSupport school_supports_nonempty.1
    (fun z => a.2 ∈ z a.1) (fun z => b.2 ∈ z b.1) _
    (school_B_marginal a) (school_B_marginal b) (school_B_joint a b hab)).2.1,
    (uniform_school_pair_law schoolBSupport school_supports_nonempty.1
    (fun z => a.2 ∈ z a.1) (fun z => b.2 ∈ z b.1) _
    (school_B_marginal a) (school_B_marginal b) (school_B_joint a b hab)).2.2,
    school_B_joint a b hab⟩

/-- C's full pair distribution is (27/110,14/55,14/55,27/110) for
any distinct schools. P013-T26(f), P013-N016. -/
theorem school_C_pair_distribution (a b : School) (hab : a ≠ b) :
    uniformSchoolProbability schoolCSupport (fun z => a ∉ z ∧ b ∉ z) = 27/110 ∧
    uniformSchoolProbability schoolCSupport (fun z => a ∉ z ∧ b ∈ z) = 14/55 ∧
    uniformSchoolProbability schoolCSupport (fun z => a ∈ z ∧ b ∉ z) = 14/55 ∧
    uniformSchoolProbability schoolCSupport (fun z => a ∈ z ∧ b ∈ z) = 27/110 := by
  have h := uniform_school_pair_law schoolCSupport school_supports_nonempty.2
    (fun z => a ∈ z) (fun z => b ∈ z) (27/110)
    (school_C_marginal a) (school_C_marginal b) (school_C_joint a b hab)
  norm_num at h
  exact ⟨h.1,h.2.1,h.2.2,school_C_joint a b hab⟩

/-- Every supported blocked assignment has 28 hosts and is supported by C.
P013-T26(a), P013-N016. -/
theorem school_B_embeds_C (z : Fin 14 → Finset (Fin 4)) (hz : z ∈ schoolBSupport) :
    blockSchoolHosts z ∈ schoolCSupport := by
  have hlocal : ∀ b, (z b).card = 2 := by
    intro b
    exact (mem_powersetCard.mp (Fintype.mem_piFinset.mp hz b)).2
  have hcard : (blockSchoolHosts z).card = 28 := by
    rw [blockSchoolHosts, card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
    have hs : ∀ b : Fin 14, (∑ r : Fin 4, if r ∈ z b then 1 else 0 : ℕ) = 2 := by
      intro b
      simpa using hlocal b
    simp_rw [hs]
    norm_num
  exact mem_powersetCard.mpr ⟨subset_univ _,hcard⟩

/-- B's array representation does not duplicate hosting assignments.
Supporting finite support lemma for P013-T25,T26(a), P013-N016. -/
theorem block_school_hosts_injective : Function.Injective blockSchoolHosts := by
  intro z w h
  funext b
  ext r
  have he := congrArg (fun S : Finset School => (b,r) ∈ S) h
  simpa [blockSchoolHosts] using he

/-- The invented assignment with schools 1--28 hosting: all four hosts
in each of the first seven blocks and none in the last seven. P013-N016,
P013-T25(a); these numbers are artificial labels, not released identifiers. -/
def schoolBadHosts : Finset School :=
  (univ.filter (fun b : Fin 14 => b.val < 7)).product univ

/-- Schools 1--28 give a size-28 assignment under C, but no B assignment
has this hosting vector. Exact support counterexample P013-T25(a). -/
theorem school_support_counterexample :
    schoolBadHosts.card = 28 ∧ schoolBadHosts ∈ schoolCSupport ∧
    (∀ z ∈ schoolBSupport, blockSchoolHosts z ≠ schoolBadHosts) ∧
    uniformSchoolProbability schoolCSupport (fun z => z = schoolBadHosts) =
      1/7648690600760440 ∧
    0 < uniformSchoolProbability schoolCSupport (fun z => z = schoolBadHosts) ∧
    uniformSchoolProbability schoolBSupport (fun z => blockSchoolHosts z = schoolBadHosts) = 0 := by
  have h7 : (univ.filter (fun b : Fin 14 => b.val < 7)).card = 7 := by decide
  have hc : schoolBadHosts.card = 28 := by
    simp [schoolBadHosts, card_product, h7]
  have hC : schoolBadHosts ∈ schoolCSupport := mem_powersetCard.mpr ⟨subset_univ _,hc⟩
  have hB : ∀ z ∈ schoolBSupport, blockSchoolHosts z ≠ schoolBadHosts := by
    intro z hz h
    have hz0 : (z 0).card = 2 :=
      (mem_powersetCard.mp (Fintype.mem_piFinset.mp hz 0)).2
    have he : z 0 = univ := by
      ext r
      have hi : ((0 : Fin 14),r) ∈ blockSchoolHosts z := by
        rw [h]; simp [schoolBadHosts]
      simpa [blockSchoolHosts] using hi
    rw [he] at hz0
    norm_num at hz0
  have hpC : uniformSchoolProbability schoolCSupport (fun z => z = schoolBadHosts) =
      1/7648690600760440 := by
    unfold uniformSchoolProbability
    have hf : schoolCSupport.filter (fun z => z = schoolBadHosts) = {schoolBadHosts} := by
      ext z
      simp only [mem_filter,mem_singleton]
      constructor
      · exact fun h => h.2
      · intro h; subst z; exact ⟨hC,rfl⟩
    rw [hf,card_singleton,school_assignment_counts.2.2.2]
    norm_num
  have hpB : uniformSchoolProbability schoolBSupport
      (fun z => blockSchoolHosts z = schoolBadHosts) = 0 := by
    have he : schoolBSupport.filter (fun z => blockSchoolHosts z = schoolBadHosts) = ∅ := by
      apply filter_eq_empty_iff.mpr
      exact hB
    simp [uniformSchoolProbability,he]
  refine ⟨hc,hC,hB,hpC,?_,hpB⟩
  rw [hpC]; norm_num

/-- The artificial population on the 56 schools has outcome 1 for two
specified schools at hosting exposure and 0 for the other 54; all control
outcomes are 0. P013-N016, P013-T25(b). -/
def schoolActiveOutcome (a b i : School) : ℝ := if i = a then 1 else if i = b then 1 else 0

/-- Binary hosting indicator as a real number, used in the exact source
formulas (1) and (7). P013-N016, P013-T25(b). -/
def schoolHostBit {α : Type*} (hosts : α → School → Bool) (z : α) (i : School) : ℝ :=
  if hosts z i then 1 else 0

/-- Expression (1) on all 56 schools, correct marginals 1/2, with the two
nonzero hosting outcomes of the invented population. P013-N016, P013-T25(b). -/
def schoolTwoHT {α : Type*} (hosts : α → School → Bool) (a b : School) (z : α) : ℝ :=
  ∑ i : School, schoolHostBit hosts z i * (schoolActiveOutcome a b i / (1/2))

/-- Expression (7) on all 56 schools with correct marginals 1/2 and supplied
q in place of distinct-school joints. Only the two active schools can
contribute off diagonal. P013-N016, P013-T25(b); q=27/110 is the released call. -/
def schoolTwoVarianceInput {α : Type*} (hosts : α → School → Bool)
    (a b : School) (q : ℝ) (z : α) : ℝ :=
  (∑ i : School, schoolHostBit hosts z i * (1 - (1/2 : ℝ)) *
    (schoolActiveOutcome a b i / (1/2))^2) +
  ∑ i : School, ∑ j ∈ univ.erase i,
    (schoolHostBit hosts z i * schoolHostBit hosts z j) *
      ((q - (1/2 : ℝ)*(1/2)) / q) *
      (schoolActiveOutcome a b i / (1/2)) * (schoolActiveOutcome a b j / (1/2))

/-- A sum with exactly two possibly nonzero terms reduces to those terms.
Supporting finite certificate for expression (7), P013-T25(b), P013-N016. -/
theorem school_sum_two (a b : School) (hab : a ≠ b) (f : School → ℝ)
    (hz : ∀ i, i ≠ a → i ≠ b → f i = 0) :
    (∑ i, f i) = f a + f b := by
  calc
    _ = ∑ i ∈ ({a,b} : Finset School), f i := by
      symm
      apply sum_subset (subset_univ _)
      intro i _ hi
      simp only [mem_insert,mem_singleton,not_or] at hi
      exact hz i hi.1 hi.2
    _ = f a + f b := by simp [hab,Ne.symm hab]

/-- The actual 56-unit HT sum reduces to 2(S_a+S_b); the population total
is 2. P013-T25(b), P013-N016. -/
theorem school_two_HT_reduction {α : Type*} (hosts : α → School → Bool)
    (a b : School) (hab : a ≠ b) (z : α) :
    schoolTwoHT hosts a b z = 2 * (schoolHostBit hosts z a + schoolHostBit hosts z b) ∧
    (∑ i : School, schoolActiveOutcome a b i) = 2 := by
  constructor
  · unfold schoolTwoHT
    rw [school_sum_two a b hab _ (by intro i ha hb; simp [schoolActiveOutcome,ha,hb])]
    simp [schoolActiveOutcome,hab,Ne.symm hab]
    ring
  · rw [school_sum_two a b hab _ (by intro i ha hb; simp [schoolActiveOutcome,ha,hb])]
    norm_num [schoolActiveOutcome,hab,Ne.symm hab]

/-- The actual ordered-pair expression (7) reduces to its two active
school terms: 2(S_a+S_b)+8S_aS_b(q−1/4)/q. P013-T25(b), P013-N016. -/
theorem school_two_variance_reduction {α : Type*} (hosts : α → School → Bool)
    (a b : School) (hab : a ≠ b) (q : ℝ) (z : α) :
    schoolTwoVarianceInput hosts a b q z =
      2 * (schoolHostBit hosts z a + schoolHostBit hosts z b) +
        8 * schoolHostBit hosts z a * schoolHostBit hosts z b * ((q - 1/4)/q) := by
  let diag : School → ℝ := fun i => schoolHostBit hosts z i * (1-(1/2 : ℝ)) *
    (schoolActiveOutcome a b i / (1/2))^2
  let term : School → School → ℝ := fun i j =>
    (schoolHostBit hosts z i * schoolHostBit hosts z j) * ((q-(1/2 : ℝ)*(1/2))/q) *
      (schoolActiveOutcome a b i/(1/2)) * (schoolActiveOutcome a b j/(1/2))
  change (∑ i, diag i) + (∑ i, ∑ j ∈ univ.erase i, term i j) = _
  rw [school_sum_two a b hab diag (by intro i ha hb; simp [diag,schoolActiveOutcome,ha,hb])]
  rw [school_sum_two a b hab (fun i => ∑ j ∈ univ.erase i, term i j)
    (by intro i ha hb; simp [term,schoolActiveOutcome,ha,hb])]
  have hia : (∑ j ∈ univ.erase a, term a j) = term a b := by
    apply sum_eq_single b
    · intro j hj hjb
      have hja : j ≠ a := (mem_erase.mp hj).1
      simp [term,schoolActiveOutcome,hja,hjb]
    · intro h; exact (h (by simp [Ne.symm hab])).elim
  have hib : (∑ j ∈ univ.erase b, term b j) = term b a := by
    apply sum_eq_single a
    · intro j hj hja
      have hjb : j ≠ b := (mem_erase.mp hj).1
      simp [term,schoolActiveOutcome,hja,hjb]
    · intro h; exact (h (by simp [hab])).elim
  rw [hia,hib]
  norm_num [diag,term,schoolActiveOutcome,hab,Ne.symm hab]
  ring

/-- For any actual school law with fair marginals and joint p, the HT total
has mean 2 and variance 8p, and (7) supplied with q has mean
2+8p(q−1/4)/q. This computes moments over the full assignment support.
P013-T25(b), P013-N016. -/
theorem school_two_moments {α : Type*} (S : Finset α)
    (hosts : α → School → Bool) (a b : School) (hab : a ≠ b) (p q : ℝ)
    (ha : uniformSchoolProbability S (fun z => hosts z a = true) = 1/2)
    (hb : uniformSchoolProbability S (fun z => hosts z b = true) = 1/2)
    (hp : uniformSchoolProbability S (fun z => hosts z a = true ∧ hosts z b = true) = p) :
    uniformSchoolMean S (schoolTwoHT hosts a b) = 2 ∧
    uniformSchoolVariance S (schoolTwoHT hosts a b) = 8*p ∧
    uniformSchoolMean S (schoolTwoVarianceInput hosts a b q) = 2+8*p*((q-1/4)/q) := by
  have hma : uniformSchoolMean S (fun z => schoolHostBit hosts z a) = 1/2 := by
    rw [uniform_school_probability_mean] at ha
    simpa [schoolHostBit] using ha
  have hmb : uniformSchoolMean S (fun z => schoolHostBit hosts z b) = 1/2 := by
    rw [uniform_school_probability_mean] at hb
    simpa [schoolHostBit] using hb
  have hprod : uniformSchoolMean S (fun z => schoolHostBit hosts z a * schoolHostBit hosts z b) = p := by
    rw [uniform_school_probability_mean] at hp
    have he : (fun z => schoolHostBit hosts z a * schoolHostBit hosts z b) =
        (fun z => if hosts z a = true ∧ hosts z b = true then (1 : ℝ) else 0) := by
      funext z; cases ha' : hosts z a <;> cases hb' : hosts z b <;> simp [schoolHostBit,ha',hb']
    rw [he]; exact hp
  have hT : schoolTwoHT hosts a b =
      fun z => 2 * (schoolHostBit hosts z a + schoolHostBit hosts z b) := by
    funext z; exact (school_two_HT_reduction hosts a b hab z).1
  have hmean : uniformSchoolMean S (schoolTwoHT hosts a b) = 2 := by
    rw [hT, uniform_school_mean_mul, uniform_school_mean_add, hma, hmb]; norm_num
  have hsq : (fun z => (schoolTwoHT hosts a b z)^2) =
      fun z => 4 * schoolHostBit hosts z a + 4 * schoolHostBit hosts z b +
        8 * (schoolHostBit hosts z a * schoolHostBit hosts z b) := by
    funext z; rw [hT]
    cases ha' : hosts z a <;> cases hb' : hosts z b <;> norm_num [schoolHostBit, ha',hb']
  have hV : schoolTwoVarianceInput hosts a b q = fun z =>
      2 * (schoolHostBit hosts z a + schoolHostBit hosts z b) +
        (8*((q-1/4)/q)) * (schoolHostBit hosts z a * schoolHostBit hosts z b) := by
    funext z; rw [school_two_variance_reduction hosts a b hab q z]; ring
  refine ⟨hmean, ?_, ?_⟩
  · rw [uniformSchoolVariance, hmean, hsq, uniform_school_mean_add,
      uniform_school_mean_add, uniform_school_mean_mul, uniform_school_mean_mul,
      uniform_school_mean_mul, hma,hmb,hprod]; ring
  · rw [hV, uniform_school_mean_add, uniform_school_mean_mul, uniform_school_mean_add,
      uniform_school_mean_mul, hma,hmb,hprod]; ring

/-- B hosting indicator is membership in the appropriate block selection.
P013-T25(b), P013-N016. -/
def schoolBHosts (z : Fin 14 → Finset (Fin 4)) (a : School) : Bool := decide (a.2 ∈ z a.1)

/-- C hosting indicator is membership in the uniform size-28 subset.
P013-T25(b), P013-N016. -/
def schoolCHosts (z : Finset School) (a : School) : Bool := decide (a ∈ z)

/-- Explicit schools 1,2 (one block) and 1,5 (different blocks): with the
released q=27/110, (7) has mean 160/81 versus variance 4/3, or mean 53/27
versus variance 2. The latter is not conservative. Under C both are 108/55.
This is an invented 56-school counterexample to wrong-design inputs, not
an evaluation or refutation of Table 2 or Lemma 5.1. P013-T25(c,d,e). -/
theorem school_wrong_joint_counterexample :
    uniformSchoolMean schoolBSupport (schoolTwoHT schoolBHosts (0,0) (0,1)) = 2 ∧
    uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (0,1)) = 4/3 ∧
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (0,1) (27/110)) = 160/81 ∧
    uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (1,0)) = 2 ∧
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (1,0) (27/110)) = 53/27 ∧
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (1,0) (27/110)) <
        uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (1,0)) ∧
    uniformSchoolVariance schoolCSupport (schoolTwoHT schoolCHosts (0,0) (0,1)) = 108/55 ∧
    uniformSchoolMean schoolCSupport
      (schoolTwoVarianceInput schoolCHosts (0,0) (0,1) (27/110)) = 108/55 := by
  have hs := school_two_moments schoolBSupport schoolBHosts (0,0) (0,1) (by decide)
    (1/6) (27/110) (by simpa [schoolBHosts] using school_B_marginal (0,0))
    (by simpa [schoolBHosts] using school_B_marginal (0,1))
    (by simpa [schoolBHosts] using school_B_joint (0,0) (0,1) (by decide))
  have hd := school_two_moments schoolBSupport schoolBHosts (0,0) (1,0) (by decide)
    (1/4) (27/110) (by simpa [schoolBHosts] using school_B_marginal (0,0))
    (by simpa [schoolBHosts] using school_B_marginal (1,0))
    (by simpa [schoolBHosts] using school_B_joint (0,0) (1,0) (by decide))
  have hc := school_two_moments schoolCSupport schoolCHosts (0,0) (0,1) (by decide)
    (27/110) (27/110) (by simpa [schoolCHosts] using school_C_marginal (0,0))
    (by simpa [schoolCHosts] using school_C_marginal (0,1))
    (by simpa [schoolCHosts] using school_C_joint (0,0) (0,1) (by decide))
  norm_num at hs hd hc
  refine ⟨hs.1,hs.2.1,hs.2.2,hd.2.1,hd.2.2,?_,hc.2.1,hc.2.2⟩
  rw [hd.2.1,hd.2.2]; norm_num

/-- Hosting merely selects between two values of a function: a fair school
lottery averages them equally. P013-T26(g), P013-N016. -/
theorem school_local_mean {α : Type*} (S : Finset α) (hS : S.Nonempty)
    (hosts : α → School → Bool) (a : School) (X : Bool → ℝ)
    (ha : uniformSchoolProbability S (fun z => hosts z a = true) = 1/2) :
    uniformSchoolMean S (fun z => X (hosts z a)) = (X false + X true)/2 := by
  have he : (fun z => X (hosts z a)) =
      fun z => X false + (X true - X false) * schoolHostBit hosts z a := by
    funext z; cases h : hosts z a <;> simp [schoolHostBit,h]
  have hm : uniformSchoolMean S (fun z => schoolHostBit hosts z a) = 1/2 := by
    rw [uniform_school_probability_mean] at ha
    simpa [schoolHostBit] using ha
  rw [he,uniform_school_mean_add,uniform_school_mean_const S hS,
    uniform_school_mean_mul,hm]
  ring

/-- Section 10's exposure conditional on hosting: if the school does not
host the label is d000; if it hosts, the student lottery and fixed network
choose among d001,d011,d101,d111. Labels 0--4 follow that order.
The four-way hosted code absorbs own assignment and the peer indicator
of the printed mapping, p. 1934. P013-T26(g,h). -/
def schoolHostedExposure (host : Bool) (studentCode : Fin 4) : Fin 5 :=
  if host then ⟨studentCode.val + 1, by omega⟩ else 0

/-- Exposure under the school lottery and an independent student lottery.
The studentCode function and its law are identical under B and C; any
finite student-level law is allowed. P013-N016, P013-T26(g,h). -/
def schoolStudentExposure {Ξ : Type*} {N : ℕ} {α : Type*}
    (hosts : α → School → Bool) (school : Fin N → School)
    (studentCode : Ξ → Fin N → Fin 4) (z : α) (x : Ξ) (i : Fin N) : Fin 5 :=
  schoolHostedExposure (hosts z (school i)) (studentCode x i)

/-- Exact joint exposure probability under the product of the uniform school
law and the common independent student law Q. Equal labels give π_ij(d);
unequal labels give π_ij(d,d'). P013-N016, P013-T26(g,h). -/
def schoolStudentJoint {Ξ : Type*} [Fintype Ξ] {N : ℕ} {α : Type*}
    (S : Finset α) (hosts : α → School → Bool) (Q : Ξ → ℝ)
    (school : Fin N → School) (studentCode : Ξ → Fin N → Fin 4)
    (i j : Fin N) (d e : Fin 5) : ℝ :=
  uniformSchoolMean S (fun z => ∑ x, Q x *
    (if schoolStudentExposure hosts school studentCode z x i = d ∧
        schoolStudentExposure hosts school studentCode z x j = e then 1 else 0))

/-- Individual exposure probabilities are the joint probabilities at i=j,
d=e. This is exactly the marginal, since a conjunction with itself is
unchanged. pp. 1916--1917; P013-T26(g). -/
def schoolStudentMarginal {Ξ : Type*} [Fintype Ξ] {N : ℕ} {α : Type*}
    (S : Finset α) (hosts : α → School → Bool) (Q : Ξ → ℝ)
    (school : Fin N → School) (studentCode : Ξ → Fin N → Fin 4)
    (i : Fin N) (d : Fin 5) : ℝ :=
  schoolStudentJoint S hosts Q school studentCode i i d d

/-- Changing the school lottery B to C preserves every student's marginal
and every same-school pair's same- or cross-exposure probability, for any
common independent student law. P013-T26(g), P013-N016. -/
theorem school_exposure_probabilities_unchanged {Ξ : Type*} [Fintype Ξ] {N : ℕ}
    (_hN : 0 < N) (Q : Ξ → ℝ) (_hQ : ∀ x, 0 ≤ Q x) (_htotal : ∑ x, Q x = 1)
    (school : Fin N → School) (studentCode : Ξ → Fin N → Fin 4) :
    (∀ i d, schoolStudentMarginal schoolBSupport schoolBHosts Q school studentCode i d =
      schoolStudentMarginal schoolCSupport schoolCHosts Q school studentCode i d) ∧
    (∀ i j d e, school i = school j →
      schoolStudentJoint schoolBSupport schoolBHosts Q school studentCode i j d e =
        schoolStudentJoint schoolCSupport schoolCHosts Q school studentCode i j d e) := by
  have hj : ∀ i j d e, school i = school j →
      schoolStudentJoint schoolBSupport schoolBHosts Q school studentCode i j d e =
        schoolStudentJoint schoolCSupport schoolCHosts Q school studentCode i j d e := by
    intro i j d e hschool
    let X : Bool → ℝ := fun s => ∑ x, Q x *
      (if schoolHostedExposure s (studentCode x i) = d ∧
        schoolHostedExposure s (studentCode x j) = e then 1 else 0)
    have hB : schoolStudentJoint schoolBSupport schoolBHosts Q school studentCode i j d e =
        uniformSchoolMean schoolBSupport (fun z => X (schoolBHosts z (school i))) := by
      simp [schoolStudentJoint,schoolStudentExposure,hschool,X]
    have hC : schoolStudentJoint schoolCSupport schoolCHosts Q school studentCode i j d e =
        uniformSchoolMean schoolCSupport (fun z => X (schoolCHosts z (school i))) := by
      simp [schoolStudentJoint,schoolStudentExposure,hschool,X]
    rw [hB,hC,school_local_mean schoolBSupport school_supports_nonempty.1 schoolBHosts
      (school i) X (by simpa [schoolBHosts] using school_B_marginal (school i)),
      school_local_mean schoolCSupport school_supports_nonempty.2 schoolCHosts
      (school i) X (by simpa [schoolCHosts] using school_C_marginal (school i))]
  exact ⟨fun i d => hj i i d d rfl,hj⟩

/-- Under the printed Section 10 mapping, d000 occurs exactly when the
school does not host. p. 1934; P013-T26(g,h). -/
theorem school_hosted_no_exposure (host : Bool) (studentCode : Fin 4) :
    schoolHostedExposure host studentCode = 0 ↔ host = false := by
  cases host
  · constructor <;> intro _ <;> rfl
  · constructor
    · intro h
      have hc := congrArg Fin.val h
      change studentCode.val + 1 = 0 at hc
      omega
    · intro h; exact Bool.noConfusion h

/-- Cross-school d000 joints inherit the school 00 probabilities exactly:
1/6 for same-block schools, 1/4 across blocks under B, 27/110 under C.
Individual d000 probabilities are 1/2 under both. P013-T26(g,h), P013-N016. -/
theorem school_no_exposure_probabilities {Ξ : Type*} [Fintype Ξ] {N : ℕ}
    (Q : Ξ → ℝ) (_hQ : ∀ x, 0 ≤ Q x) (htotal : ∑ x, Q x = 1)
    (school : Fin N → School) (studentCode : Ξ → Fin N → Fin 4) :
    (∀ i, schoolStudentMarginal schoolBSupport schoolBHosts Q school studentCode i 0 = 1/2 ∧
      schoolStudentMarginal schoolCSupport schoolCHosts Q school studentCode i 0 = 1/2) ∧
    (∀ i j, school i ≠ school j →
      schoolStudentJoint schoolBSupport schoolBHosts Q school studentCode i j 0 0 =
        (if (school i).1 = (school j).1 then 1/6 else 1/4) ∧
      schoolStudentJoint schoolCSupport schoolCHosts Q school studentCode i j 0 0 = 27/110) := by
  have hj : ∀ {α : Type} (S : Finset α) (hosts : α → School → Bool) (i j : Fin N),
      schoolStudentJoint S hosts Q school studentCode i j 0 0 =
        uniformSchoolProbability S (fun z => hosts z (school i) = false ∧ hosts z (school j) = false) := by
    intro α S hosts i j
    rw [uniform_school_probability_mean]
    unfold schoolStudentJoint
    congr 1
    funext z
    simp only [schoolStudentExposure, school_hosted_no_exposure]
    rw [← sum_mul,htotal,one_mul]
  constructor
  · intro i
    rw [schoolStudentMarginal,schoolStudentMarginal,hj schoolBSupport schoolBHosts i i,
      hj schoolCSupport schoolCHosts i i]
    have hBm := (school_B_marginal (school i))
    have hCm := (school_C_marginal (school i))
    have hBc := uniform_school_pair_law schoolBSupport school_supports_nonempty.1
      (fun z => (school i).2 ∈ z (school i).1) (fun z => (school i).2 ∈ z (school i).1)
      (1/2) hBm hBm (by simpa using hBm)
    have hCc := uniform_school_pair_law schoolCSupport school_supports_nonempty.2
      (fun z => school i ∈ z) (fun z => school i ∈ z) (1/2) hCm hCm (by simpa using hCm)
    exact ⟨by simpa [schoolBHosts] using hBc.1, by simpa [schoolCHosts] using hCc.1⟩
  · intro i j hij
    rw [hj schoolBSupport schoolBHosts i j,hj schoolCSupport schoolCHosts i j]
    exact ⟨by simpa [schoolBHosts] using (school_B_pair_distribution (school i) (school j) hij).1,
      by simpa [schoolCHosts] using (school_C_pair_distribution (school i) (school j) hij).1⟩

/-- Complete binary-exposure potential outcomes for the invented 56-school
example: y_i(1) is the active-school outcome, y_i(0)=0. These depend only
on the exposure, as Condition 1 requires. P013-T25(b), P013-N016. -/
def schoolPotentialOutcome (a b i : School) (d : Bool) : ℝ :=
  if d then schoolActiveOutcome a b i else 0

/-- Condition 2 for the invented example: the observed outcome is its
school potential outcome at the actual hosting exposure.
P013-T25(b), P013-N016; no empirical outcome is used. -/
def schoolExampleObserved {α : Type*} (hosts : α → School → Bool)
    (a b : School) (z : α) (i : School) : ℝ :=
  schoolPotentialOutcome a b i (hosts z i)

/-- The example's complete potentials are binary, the hosting total is 2,
all control outcomes are zero, and masking the observed outcome gives the
active hosting contribution in (1) and (7). P013-T25(b), P013-N016. -/
theorem school_example_potential_hypotheses (a b : School) (hab : a ≠ b) :
    (∀ i d, schoolPotentialOutcome a b i d = 0 ∨ schoolPotentialOutcome a b i d = 1) ∧
    (∑ i, schoolPotentialOutcome a b i true) = 2 ∧
    (∀ i, schoolPotentialOutcome a b i false = 0) ∧
    (∀ {α : Type*} (hosts : α → School → Bool) z i,
      schoolExampleObserved hosts a b z i = schoolHostBit hosts z i * schoolActiveOutcome a b i) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i d
    cases d
    · simp [schoolPotentialOutcome]
    · by_cases ha : i = a
      · simp [schoolPotentialOutcome,schoolActiveOutcome,ha]
      · by_cases hb : i = b <;> simp [schoolPotentialOutcome,schoolActiveOutcome,ha,hb]
  · simpa [schoolPotentialOutcome] using
      (school_two_HT_reduction schoolBHosts a b hab (fun _ => ∅)).2
  · intro i; rfl
  · intro α hosts z i
    cases h : hosts z i <;> simp [schoolExampleObserved,schoolPotentialOutcome,schoolHostBit,h]

/-- Supplying the actual positive joint p to (7) restores exact unbiasedness,
as Lemma 5.1 guarantees, for the artificial 56-unit population under any
of the actual finite school laws. P013-T25(b), p. 1921; P013-N016. -/
theorem school_correct_joint_unbiased {α : Type*} (S : Finset α)
    (hosts : α → School → Bool) (a b : School) (hab : a ≠ b) (p : ℝ) (hpos : 0 < p)
    (ha : uniformSchoolProbability S (fun z => hosts z a = true) = 1/2)
    (hb : uniformSchoolProbability S (fun z => hosts z b = true) = 1/2)
    (hp : uniformSchoolProbability S (fun z => hosts z a = true ∧ hosts z b = true) = p) :
    uniformSchoolMean S (schoolTwoVarianceInput hosts a b p) =
      uniformSchoolVariance S (schoolTwoHT hosts a b) := by
  have h := school_two_moments S hosts a b hab p p ha hb hp
  rw [h.2.2,h.2.1]
  field_simp [ne_of_gt hpos] <;> ring

/-- Exact wrong-input variance biases on the full 56-school block support:
52/81 for the same-block active pair and −1/27 for the different-block
active pair. P013-T25(c,d), P013-N016. -/
theorem school_wrong_joint_biases :
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (0,1) (27/110)) -
      uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (0,1)) = 52/81 ∧
    uniformSchoolMean schoolBSupport
      (schoolTwoVarianceInput schoolBHosts (0,0) (1,0) (27/110)) -
      uniformSchoolVariance schoolBSupport (schoolTwoHT schoolBHosts (0,0) (1,0)) = -(1/27) := by
  have h := school_wrong_joint_counterexample
  rw [h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1]
  norm_num

end
end AronowAudit.P013

