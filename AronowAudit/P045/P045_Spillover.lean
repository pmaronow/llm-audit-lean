import Mathlib.Tactic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Nat.Dist
import Mathlib.Data.ENat.SuccOrder
import Mathlib.Analysis.SpecificLimits.Basic

/-!
P045: Spillover Effects in Experimental Data (2021), pp. 289–319.
All randomness is the finite experimental design. A ratio with zero denominator
is represented as `none` where its domain matters, not as an observed zero.
-/

namespace AronowAudit.P045
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Finset
noncomputable section

/-- "a treatment assignment vector ... z_i ∈ {1,0}" (p. 292).
`true` denotes treatment and `false` control; indices are zero based. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- "predetermined probability p_z" (p. 292): a genuine finite law,
with nonnegative masses summing to one, including zero-mass assignments. -/
structure Design (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ w, 0 ≤ mass w
  total : ∑ w, mass w = 1

/-- Design-based expectation, p. 292: ∑_z p_z X(z). -/
def expect {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ w, p w * X w

/-- Event probability under the design of p. 292. -/
def prob {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  by classical exact expect p (fun w => if E w then 1 else 0)

/-- Conditional finite expectation (p. 309 and the proviso on p. 310).
Paper assertions use positive-probability events; supporting algebra also
states identities for the totalized quotient. -/
def condMean {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (E : Ω → Prop) (X : Ω → ℝ) : ℝ :=
  by classical exact expect p (fun w => if E w then X w else 0) / prob p E

/-- Randomization variance: E[(X−EX)^2], the variance discussed on pp. 298–299. -/
def variance {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  expect p (fun w => (X w - expect p X)^2)

/-- Uniform expectation over a finite support, as in complete randomization
(pp. 292, 309–310). Assertions require a nonempty support. -/
def average {Ω : Type*} (S : Finset Ω) (X : Ω → ℝ) : ℝ :=
  (∑ w ∈ S, X w) / S.card

/-- "the average potential outcome ... (1/N)∑_i y_i(d_k)" (p. 297);
also the equal-group averages of p. 309 when the index denotes groups. -/
def mean {I : Type*} [Fintype I] (x : I → ℝ) : ℝ :=
  (∑ i, x i) / Fintype.card I

/-- Zero-one indicator of a treatment value, p. 294. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- Bernoulli(p) assignment: independent unit draws (pp. 292, 309–310). -/
def bernoulli {n : ℕ} (p : ℝ) (z : Assignment n) : ℝ :=
  ∏ i, if z i then p else 1-p

/-- "exactly k ... uniformly" (pp. 292, 309–310): all k-subsets. -/
def fixedAssignments (n k : ℕ) : Finset (Assignment n) :=
  univ.filter (fun z => (univ.filter (fun i => z i = true)).card = k)

/-- "D_i=f(Z,θ_i)" with four first-degree exposures (pp. 293–294). -/
inductive Exposure | d11 | d10 | d01 | d00
  deriving DecidableEq
instance : Fintype Exposure := ⟨{.d11, .d10, .d01, .d00}, by
  intro d; cases d <;> simp⟩

/-- Symmetric zero-diagonal 0/1 adjacency, the undirected networks of p. 295. -/
structure Network (n : ℕ) where
  adj : Fin n → Fin n → Bool
  symmetric : ∀ i j, adj i j = adj j i
  loopless : ∀ i, adj i i = false

/-- A unit has indirect exposure iff at least one directly tied peer is treated;
combined with own treatment this is exactly the display on p. 294. -/
def exposure {n : ℕ} (A : Fin n → Fin n → Bool) (z : Assignment n)
    (i : Fin n) : Exposure :=
  if z i then
    if ∃ j, A i j = true ∧ z j = true then .d11 else .d10
  else if ∃ j, A i j = true ∧ z j = true then .d01 else .d00

/-- "π_i(d)=Pr(D_i=d)" (p. 294). -/
def exposureProb {n : ℕ} {Δ : Type*} [DecidableEq Δ] (p : Assignment n → ℝ)
    (D : Assignment n → Fin n → Δ) (i : Fin n) (d : Δ) : ℝ :=
  prob p (fun z => D z i = d)

/-- "Y_i=y_i(Z)" and a correctly specified exposure mapping (pp. 293, 297).
The assignment-level outcome is the exposure-specific potential outcome. -/
def observed {n : ℕ} {Δ : Type*} [DecidableEq Δ] (D : Assignment n → Fin n → Δ)
    (y : Fin n → Δ → ℝ) (z : Assignment n) (i : Fin n) : ℝ := y i (D z i)

/-- Horvitz–Thompson exposure total, the first estimator on p. 297.
Empty realized cells are empty sums; all inclusion probabilities are positive
in the unbiasedness and domain statements. -/
def htTotal {n : ℕ} {Δ : Type*} [DecidableEq Δ] (p : Assignment n → ℝ)
    (D : Assignment n → Fin n → Δ) (y : Fin n → Δ → ℝ)
    (d : Δ) (z : Assignment n) : ℝ :=
  ∑ i, if D z i = d then observed D y z i / exposureProb p D i d else 0

/-- "τ(d_k,d_l)=μ(d_k)−μ(d_l)" (p. 297). -/
def effect {n : ℕ} {Δ : Type*} [DecidableEq Δ] (y : Fin n → Δ → ℝ) (k l : Δ) : ℝ :=
  mean (fun i => y i k) - mean (fun i => y i l)

/-- HT causal contrast, (1/N)[HT total(k)−HT total(l)] (p. 297). -/
def htContrast {n : ℕ} {Δ : Type*} [DecidableEq Δ] (p : Assignment n → ℝ)
    (D : Assignment n → Fin n → Δ) (y : Fin n → Δ → ℝ)
    (k l : Δ) (z : Assignment n) : ℝ :=
  (htTotal p D y k z - htTotal p D y l z) / n

/-- Hajek exposure mean, the ratio on p. 299. `none` is an undefined 0/0;
using an Option keeps that domain distinct from the empty HT total. -/
def hajek {n : ℕ} {Δ : Type*} [DecidableEq Δ] (p : Assignment n → ℝ)
    (D : Assignment n → Fin n → Δ) (y : Fin n → Δ → ℝ)
    (d : Δ) (z : Assignment n) : Option ℝ :=
  let den := ∑ i, if D z i = d then 1 / exposureProb p D i d else 0
  if den = 0 then none else some (htTotal p D y d z / den)

/-- Linearity of finite randomization expectation (supporting pp. 297, 310). -/
theorem expect_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (p : Ω → ℝ) (X : I → Ω → ℝ) :
    expect p (fun w => ∑ i, X i w) = ∑ i, expect p (X i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

/-- Linearity for a causal contrast of randomization estimators. -/
theorem expect_sub {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X Y : Ω → ℝ) :
    expect p (fun w => X w - Y w) = expect p X - expect p Y := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

/-- Addition is linear under the finite experimental law (p. 297). -/
theorem expect_add {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X Y : Ω → ℝ) :
    expect p (fun w => X w+Y w)=expect p X+expect p Y := by
  simp [expect,mul_add,Finset.sum_add_distrib]

/-- Event probabilities under a genuine finite design are nonnegative. -/
theorem prob_nonneg {Ω : Type*} [Fintype Ω] (p : Design Ω) (E : Ω → Prop) :
    0 ≤ prob p.mass E := by
  classical
  unfold prob expect
  apply Finset.sum_nonneg
  intro w hw
  by_cases h : E w <;> simp [h,p.nonneg w]

/-- Inclusion of events preserves probability under the finite design. -/
theorem prob_mono {Ω : Type*} [Fintype Ω] (p : Design Ω) (E F : Ω → Prop)
    (hEF : ∀ w, E w → F w) : prob p.mass E ≤ prob p.mass F := by
  classical
  unfold prob expect
  apply Finset.sum_le_sum
  intro w hw
  by_cases h : E w
  · simp [h,hEF w h]
  · simp [h]; by_cases hF : F w <;> simp [hF,p.nonneg w]

/-- The mean of differences is the difference of means (p. 297). -/
theorem mean_sub {I : Type*} [Fintype I] (x y : I → ℝ) :
    mean (fun i => x i-y i)=mean x-mean y := by
  simp [mean,Finset.sum_sub_distrib,sub_div]

/-- Negating every potential outcome negates its finite mean. -/
theorem mean_neg {I : Type*} [Fintype I] (x : I → ℝ) :
    mean (fun i => -x i)=-mean x := by
  simp [mean,Finset.sum_neg_distrib,neg_div]

/-- A mean of nonnegative finite quantities is nonnegative. -/
theorem mean_nonneg {I : Type*} [Fintype I] (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ mean x := by
  unfold mean
  exact div_nonneg (Finset.sum_nonneg (fun i hi => hx i)) (Nat.cast_nonneg _)

/-- A mean of nonpositive finite quantities is nonpositive. -/
theorem mean_nonpos {I : Type*} [Fintype I] (x : I → ℝ) (hx : ∀ i, x i ≤ 0) :
    mean x ≤ 0 := by
  unfold mean
  exact div_nonpos_of_nonpos_of_nonneg (Finset.sum_nonpos (fun i hi => hx i)) (Nat.cast_nonneg _)

/-- A deterministic denominator can be taken outside the finite expectation. -/
theorem expect_div {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → ℝ) (a : ℝ) :
    expect p (fun w => X w / a) = expect p X / a := by
  simp [expect, mul_div_assoc, Finset.sum_div]

/-- Averaging fixed units commutes with design expectation (pp. 297, 309). -/
theorem expect_mean {Ω I : Type*} [Fintype Ω] [Fintype I]
    (p : Ω → ℝ) (X : I → Ω → ℝ) :
    expect p (fun w => mean (fun i => X i w)) = mean (fun i => expect p (X i)) := by
  unfold mean
  rw [expect_div, expect_sum]

/-- A fixed outcome multiplied by an event indicator has expectation
Pr(E) times that outcome, the finite identity underlying p. 297. -/
theorem expect_event_constant {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (E : Ω → Prop) [DecidablePred E] (c : ℝ) :
    expect p (fun w => if E w then c else 0) = prob p E*c := by
  classical
  unfold prob expect
  have hmul : ∀ w, p w*(if E w then c else 0) = (p w*(if E w then 1 else 0))*c := by
    intro w; split_ifs <;> simp
  simp_rw [hmul]
  rw [← Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  by_cases h : E w <;> simp [h]

/-- An outcome constant on a positive-probability event is recovered by
inverse probability weighting, with outcomes elsewhere unrestricted. -/
theorem event_constant_ht {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (E : Ω → Prop) [DecidablePred E] (Y : Ω → ℝ) (c : ℝ)
    (hY : ∀ w, E w → Y w=c) (hp : 0 < prob p E) :
    expect p (fun w => if E w then Y w/prob p E else 0)=c := by
  have hx : (fun w => if E w then Y w/prob p E else 0) =
      (fun w => if E w then c/prob p E else 0) := by
    funext w
    by_cases h : E w
    · simp [h, hY w h]
    · simp [h]
  rw [hx, expect_event_constant]
  field_simp [ne_of_gt hp]

/-- T6(d): inverse-weighting an event estimates its conditional mean;
this identity permits arbitrary outcomes on mixed neighbourhoods. -/
theorem event_ht_conditional {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (E : Ω → Prop) [DecidablePred E] (Y : Ω → ℝ) :
    expect p (fun w => if E w then Y w / prob p E else 0) = condMean p E Y := by
  classical
  unfold condMean
  rw [← expect_div]
  congr 1
  funext w
  split_ifs <;> simp

/-- Multiplication by a fixed real is linear in finite design expectation,
supporting the exact conditional-mixture correction on p. 303 (T9). -/
theorem expect_mul_const {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → ℝ) (a : ℝ) :
    expect p (fun w => X w*a)=expect p X*a := by
  simp [expect,mul_assoc,Finset.sum_mul]

/-- T9's finite mixture identity: if an outcome takes values a and b
on an event E according to a second event F, its conditional mean is
(1-c)a+cb, where c is the conditional indicator mean of F given E.
The conditioning event must have positive exact probability. -/
theorem event_binary_mixture {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (E F : Ω → Prop) [DecidablePred F] (X : Ω → ℝ) (a b : ℝ)
    (hp : 0 < prob p E) (hX : ∀ w, E w → X w=if F w then b else a) :
    condMean p E X =
      (1-condMean p E (fun w => if F w then 1 else 0))*a +
      condMean p E (fun w => if F w then 1 else 0)*b := by
  classical
  have hx : (fun w => if E w then X w else 0) =
      (fun w => (if E w then a else 0)+(if E w then (if F w then 1 else 0) else 0)*(b-a)) := by
    funext w
    by_cases he : E w
    · by_cases hf : F w <;> simp [he,hf,hX w he] <;> ring
    · simp [he]
  unfold condMean
  rw [hx,expect_add,expect_event_constant,expect_mul_const]
  field_simp [ne_of_gt hp]
  <;> ring

/-- T30, pp. 297–298: the exposure-specific HT total is exactly unbiased
under a correctly specified mapping and positive exact exposure probabilities. -/
theorem ht_total_unbiased {n : ℕ} {Δ : Type*} [Fintype Δ] [DecidableEq Δ] (p : Design (Assignment n))
    (D : Assignment n → Fin n → Δ) (y : Fin n → Δ → ℝ)
    (d : Δ) (hpos : ∀ i, 0 < exposureProb p.mass D i d) :
    expect p.mass (htTotal p.mass D y d) = ∑ i, y i d := by
  classical
  unfold htTotal
  rw [expect_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h : (fun z => if D z i = d then observed D y z i / exposureProb p.mass D i d else 0) =
      (fun z => (if D z i = d then 1 else 0) * (y i d / exposureProb p.mass D i d)) := by
    funext z
    by_cases hz : D z i = d <;> simp [hz, observed]
  rw [h]
  change (∑ z, p.mass z * ((if D z i = d then 1 else 0) *
    (y i d / exposureProb p.mass D i d))) = y i d
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  have hprob : (∑ z, p.mass z * (if D z i = d then (1 : ℝ) else 0)) =
      exposureProb p.mass D i d := by simp [exposureProb, prob, expect]
  rw [hprob]
  field_simp [ne_of_gt (hpos i)]

/-- T30, pp. 297–298: the HT contrast is unbiased for the finite-population
causal effect, with positivity for both exposures. -/
theorem ht_contrast_unbiased {n : ℕ} {Δ : Type*} [Fintype Δ] [DecidableEq Δ] (hn : 0 < n) (p : Design (Assignment n))
    (D : Assignment n → Fin n → Δ) (y : Fin n → Δ → ℝ)
    (k l : Δ) (hk : ∀ i, 0 < exposureProb p.mass D i k)
    (hl : ∀ i, 0 < exposureProb p.mass D i l) :
    expect p.mass (htContrast p.mass D y k l) = effect y k l := by
  unfold htContrast effect mean
  rw [expect_div, expect_sub, ht_total_unbiased p D y k hk,
    ht_total_unbiased p D y l hl]
  simp [sub_div]

/-- T30, the full p. 297–298 headline under its positive population-size
standing assumption, for an arbitrary finite set of K exposure labels:
the exposure total and its causal contrast are both exactly unbiased. -/
theorem ht_unbiased_headline {n : ℕ} (hn : 0 < n) {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    (p : Design (Assignment n)) (D : Assignment n → Fin n → Δ) (y : Fin n → Δ → ℝ)
    (k : Δ) (hk : ∀ i, 0 < exposureProb p.mass D i k) :
    expect p.mass (htTotal p.mass D y k) = ∑ i, y i k ∧
    (∀ l : Δ, (∀ i, 0 < exposureProb p.mass D i l) →
      expect p.mass (htContrast p.mass D y k l)=effect y k l) :=
  ⟨ht_total_unbiased p D y k hk,fun l hl => ht_contrast_unbiased hn p D y k l hk hl⟩

/-- T17(a): an empty exposure cell has zero HT total and a computable contrast;
the paper's positivity conditions ensure all individual divisions are valid. -/
theorem empty_ht_total {n : ℕ} {Δ : Type*} [Fintype Δ] [DecidableEq Δ] (p : Design (Assignment n))
    (D : Assignment n → Fin n → Δ) (y : Fin n → Δ → ℝ)
    (k l : Δ) (hk : ∀ i, 0 < exposureProb p.mass D i k)
    (hl : ∀ i, 0 < exposureProb p.mass D i l) (z : Assignment n)
    (hempty : ∀ i, D z i ≠ k) :
    htTotal p.mass D y k z = 0 ∧
    htContrast p.mass D y k l z = -htTotal p.mass D y l z / n := by
  have h : htTotal p.mass D y k z = 0 := by simp [htTotal, hempty]
  simp [h, htContrast]

/-- T17(d): an empty realized Hajek exposure mean remains undefined (p. 299). -/
theorem empty_hajek {n : ℕ} {Δ : Type*} [Fintype Δ] [DecidableEq Δ] (p : Assignment n → ℝ)
    (D : Assignment n → Fin n → Δ) (y : Fin n → Δ → ℝ)
    (k : Δ) (z : Assignment n) (hempty : ∀ i, D z i ≠ k) :
    hajek p D y k z = none := by simp [hajek, hempty]

/-- A finite tuple sum separates the first coordinate. This is the bijection
used to certify small assignment distributions without a large `decide`. -/
theorem sum_tuple_succ {A : Type*} [Fintype A] (n : ℕ)
    (F : (Fin (n+1) → A) → ℝ) :
    (∑ z, F z) = ∑ a : A, ∑ u : Fin n → A, F (Fin.cons (α := fun _ : Fin (n+1) => A) a u) := by
  let e := Fin.consEquiv (fun _ : Fin (n+1) => A)
  calc
    (∑ z, F z) = ∑ v : A × (Fin n → A), F (e v) := (e.sum_comp F).symm
    _ = ∑ a : A, ∑ u : Fin n → A, F (Fin.cons (α := fun _ : Fin (n+1) => A) a u) := by
      rw [Fintype.sum_prod_type]
      rfl

/-- Evaluation of tuple coordinate 2. -/
theorem cons_at_two {A : Type*} (n : ℕ) (a : A) (u : Fin (n+2) → A) :
    Fin.cons (α := fun _ : Fin (n+3) => A) a u ⟨2, by omega⟩ = u ⟨1, by omega⟩ := rfl
/-- Evaluation of tuple coordinate 3. -/
theorem cons_at_three {A : Type*} (n : ℕ) (a : A) (u : Fin (n+3) → A) :
    Fin.cons (α := fun _ : Fin (n+4) => A) a u ⟨3, by omega⟩ = u ⟨2, by omega⟩ := rfl
attribute [local simp] cons_at_two cons_at_three

/-- Coordinate evaluations with fixed tuple sizes for the four-member law. -/
@[local simp] theorem cons4_two {A : Type*} (a : A) (u : Fin 3 → A) :
    Fin.cons (α := fun _ : Fin 4 => A) a u (2 : Fin 4) = u (1 : Fin 3) := rfl
/-- Last coordinate of a four-member tuple. -/
@[local simp] theorem cons4_three {A : Type*} (a : A) (u : Fin 3 → A) :
    Fin.cons (α := fun _ : Fin 4 => A) a u (3 : Fin 4) = u (2 : Fin 3) := rfl
/-- Last coordinate of a three-member tuple. -/
@[local simp] theorem cons3_two {A : Type*} (a : A) (u : Fin 2 → A) :
    Fin.cons (α := fun _ : Fin 3 => A) a u (2 : Fin 3) = u (1 : Fin 2) := rfl

/-- The independent Bernoulli product weights sum to one (pp. 292, 309). -/
theorem bernoulli_total (n : ℕ) (p : ℝ) :
    (∑ z : Assignment n, bernoulli p z) = 1 := by
  change (∑ z : Assignment n, ∏ i, if z i then p else 1-p) = 1
  have h := Fintype.prod_sum (fun (_i : Fin n) (b : Bool) => if b then p else 1-p)
  simpa using h.symm

/-- Separating an arbitrary own-treatment coordinate in the finite sum,
the probability decomposition defining marginal outcomes on p. 309. -/
theorem sum_tuple_at {A : Type*} [Fintype A] (n : ℕ) (i : Fin (n+1))
    (F : (Fin (n+1) → A) → ℝ) :
    (∑ z, F z) = ∑ b : A, ∑ u : Fin n → A,
      F (i.insertNth (α := fun _ : Fin (n+1) => A) b u) := by
  let e := i.insertNthEquiv (fun _ : Fin (n+1) => A)
  calc
    (∑ z, F z) = ∑ v : A × (Fin n → A), F (e v) := (e.sum_comp F).symm
    _ = ∑ b, ∑ u, F (i.insertNth (α := fun _ : Fin (n+1) => A) b u) := by
      rw [Fintype.sum_prod_type]; rfl

/-- Independence factors the inserted own-treatment value from all
remaining assignments under the Bernoulli regime of pp. 309–310. -/
theorem bernoulli_insert {n : ℕ} (p : ℝ) (i : Fin (n+1)) (b : Bool)
    (u : Assignment n) :
    bernoulli p (i.insertNth (α := fun _ : Fin (n+1) => Bool) b u) =
      (if b then p else 1-p)*bernoulli p u := by
  unfold bernoulli
  rw [Fin.prod_univ_succAbove _ i]
  simp

/-- A function of one Bernoulli coordinate has exactly the two-point
expectation pF(1)+(1−p)F(0), without enumerating the assignment cube. -/
theorem bernoulli_coordinate_expect {n : ℕ} (p : ℝ) (i : Fin (n+1)) (F : Bool → ℝ) :
    expect (bernoulli p) (fun z : Assignment (n+1) => F (z i)) =
      p*F true+(1-p)*F false := by
  unfold expect
  rw [sum_tuple_at n i]
  simp only [bernoulli_insert, Fin.insertNth_apply_same]
  simp_rw [mul_assoc, mul_comm (bernoulli p _), ← mul_assoc]
  simp only [← Finset.mul_sum,bernoulli_total,mul_one]
  simp

/-- The own-arm probability under independent Bernoulli assignment is
p or 1−p, as used by the corrected unconditional HT group estimator. -/
theorem bernoulli_arm_probability {n : ℕ} (p : ℝ) (i : Fin n) (b : Bool) :
    prob (bernoulli p) (fun z : Assignment n => z i=b) = if b then p else 1-p := by
  classical
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    calc
      prob (bernoulli p) (fun z : Assignment (n+1) => z i=b) =
          expect (bernoulli p) (fun z : Assignment (n+1) => if z i=b then 1 else 0) := by
        unfold prob
        apply congrArg (expect (bernoulli p))
        funext z
        by_cases h : z i=b <;> simp [h]
      _ = p*(if true=b then 1 else 0)+(1-p)*(if false=b then 1 else 0) :=
        bernoulli_coordinate_expect p i (fun a => if a=b then 1 else 0)
      _ = if b then p else 1-p := by cases b <;> simp

/-- The Bernoulli cube expectation separates the first coin and the
remaining independent coins. Used for the finite T22 moment identities. -/
theorem bernoulli_expect_cons {n : ℕ} (p : ℝ) (F : Assignment (n+1) → ℝ) :
    expect (bernoulli p) F =
      p*expect (bernoulli p) (fun u : Assignment n => F (Fin.cons (α := fun _ : Fin (n+1) => Bool) true u)) +
      (1-p)*expect (bernoulli p) (fun u : Assignment n => F (Fin.cons (α := fun _ : Fin (n+1) => Bool) false u)) := by
  have hc : ∀ b : Bool, ∀ u : Assignment n,
      bernoulli p (Fin.cons (α := fun _ : Fin (n+1) => Bool) b u) =
        (if b then p else 1-p)*bernoulli p u := by
    intro b u
    simpa using bernoulli_insert p (0 : Fin (n+1)) b u
  unfold expect
  rw [sum_tuple_succ n]
  simp [hc,mul_assoc,Fintype.univ_bool,← Finset.mul_sum]

/-- Bernoulli(p) is a probability design when 0≤p≤1 (pp. 292, 309). -/
def bernoulliDesign (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Design (Assignment n) where
  mass := bernoulli p
  nonneg z := Finset.prod_nonneg (fun i hi => by split <;> linarith)
  total := bernoulli_total n p

/-- Number of treated members K_g=∑_i Z_ig, p. 310 and T1. -/
def treatedCount {n : ℕ} (z : Assignment n) : ℕ :=
  (univ.filter (fun i => z i = true)).card

/-- "y_ig(z;ψ)" averages a fixed potential outcome given own treatment
(p. 309). The Bernoulli law and the CR law use this same definition. -/
def marginal {n : ℕ} (p : Assignment n → ℝ)
    (y : Fin n → Assignment n → ℝ) (i : Fin n) (b : Bool) : ℝ :=
  condMean p (fun z => z i = b) (y i)

/-- Within-arm sample mean (p. 310), only used conditional on a nonempty arm. -/
def armMean {n : ℕ} (y : Fin n → Assignment n → ℝ)
    (b : Bool) (z : Assignment n) : ℝ :=
  (∑ i, if z i = b then y i z else 0) /
    (∑ i, if z i = b then (1 : ℝ) else 0)

/-- Nonzero-denominator proviso of p. 310. A raw quotient outside this
event is an auxiliary totalization and has no observed-estimator meaning. -/
def armExists {n : ℕ} (b : Bool) (z : Assignment n) : Prop :=
  ∃ i, z i = b

/-- All-unit group mean yhat_g(ψ), for the overall effect (p. 310). -/
def groupOverall {n : ℕ} (y : Fin n → Assignment n → ℝ) (z : Assignment n) : ℝ :=
  mean (fun i => y i z)

/-- T1's explicit partial/stratified interference schedule: "number of
treated other members", for four-member groups. -/
def coMembers {n : ℕ} (i : Fin n) (z : Assignment n) : ℝ :=
  ∑ j ∈ univ.erase i, bit (z j)

/-- Sum of treated indicators is the treated count K (T1, T19). -/
theorem sum_bit_count {n : ℕ} (z : Assignment n) :
    (∑ i, bit (z i)) = (treatedCount z : ℝ) := by
  simp [bit,treatedCount,Finset.sum_ite]

/-- Treated peers equal K−Z_i, for every binary assignment (T1(ii),
the correction of the group-member count on p. 310, T19). -/
theorem co_members_count {n : ℕ} (z : Assignment n) (i : Fin n) :
    coMembers i z = (treatedCount z : ℝ)-bit (z i) := by
  have h := Finset.sum_erase_add univ (fun j => bit (z j)) (mem_univ i)
  rw [sum_bit_count] at h
  unfold coMembers
  linarith

/-- T1(ii): on its actual positive-denominator domain the peer-count arm
mean is K−1 for treated units and K for controls, for labelled assignments. -/
theorem co_members_arm_mean {n : ℕ} (z : Assignment n) (b : Bool)
    (h : armExists b z) : armMean coMembers b z = (treatedCount z : ℝ)-bit b := by
  have hne : (univ.filter (fun i => z i=b)).Nonempty := by
    rcases h with ⟨i,hi⟩; exact ⟨i, by simp [hi]⟩
  have hden : (∑ i, if z i=b then (1 : ℝ) else 0) ≠ 0 := by
    simp only [Finset.sum_boole]
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr hne))
  have hf : ∀ i, (if z i=b then coMembers i z else 0) =
      (if z i=b then (1 : ℝ) else 0)*((treatedCount z : ℝ)-bit b) := by
    intro i; by_cases hi : z i=b
    · simp [hi,co_members_count]
    · simp [hi]
  unfold armMean
  simp_rw [hf]
  rw [← Finset.sum_mul]
  exact mul_div_cancel_left₀ _ hden

/-- T1(ii): the direct ratio equals −1 whenever both arms are nonempty,
an assignment-level identity under the witness's partial interference. -/
theorem co_members_direct_wrong {n : ℕ} (z : Assignment n)
    (h1 : armExists true z) (h0 : armExists false z) :
    armMean coMembers true z-armMean coMembers false z = -1 := by
  rw [co_members_arm_mean z true h1, co_members_arm_mean z false h0]
  simp [bit]

/-- T1(v): all-unit group means are 3K/4 in the four-member witness;
this estimator has no empty-arm restriction. -/
theorem co_members_overall_four (z : Assignment 4) :
    groupOverall coMembers z = (3/4)*(treatedCount z : ℝ) := by
  simp only [groupOverall,mean,co_members_count,Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ,Fintype.card_fin,sum_bit_count]
  push_cast
  ring

/-- T1(i): the Bernoulli marginal peer count is 3p, for both own
treatment values and each of the four labelled units (p. 309). -/
theorem co_members_marginal_four (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : Fin 4) (b : Bool) : marginal (bernoulli p) coMembers i b = 3*p := by
  have hpn : p ≠ 0 := ne_of_gt hp
  have hqn : 1-p ≠ 0 := by linarith
  fin_cases i <;> cases b <;>
    simp [marginal,condMean,prob,expect,bernoulli,coMembers,bit,
      sum_tuple_succ,Fin.sum_univ_succ,Fin.prod_univ_succ,Fin.univ_succ,
      Finset.erase_insert,Finset.erase_insert_of_ne,Finset.filter_insert,Finset.filter_singleton]
    <;> ring_nf <;> field_simp [hpn,hqn] <;> ring

/-- Four-member Bernoulli count law, derived by grouping the 16 labelled
assignments; binomial coefficients are (1,4,6,4,1) (T1). -/
def binomial4 (p : ℝ) (k : Fin 5) : ℝ :=
  (Nat.choose 4 k.val : ℝ) * p^k.val * (1-p)^(4-k.val)

/-- T1's arm values at a fixed treated count; these are used only on the
appropriate positive-denominator event. -/
def countArm (b : Bool) (k : Fin 5) : ℝ := (k.val : ℝ) - bit b

/-- The treated count K as an element of {0,1,2,3,4}, the sufficient
statistic of the four-member witness in T1. -/
def countIndex4 (z : Assignment 4) : Fin 5 :=
  ⟨treatedCount z, by
    have h := Finset.card_le_card (Finset.filter_subset (s := (univ : Finset (Fin 4)))
      (p := fun i => z i=true))
    simpa [treatedCount] using Nat.lt_succ_of_le h⟩

/-- T1: the actual arm domains correspond to positive treated count and
non-full treated count, respectively. This certificate enumerates 16
Boolean assignments and contains no arithmetic over real probabilities. -/
theorem four_arm_domains : ∀ z : Assignment 4,
    (armExists true z ↔ 0 < treatedCount z) ∧ (armExists false z ↔ treatedCount z < 4) := by
  unfold armExists
  decide

/-- T1: count sufficient statistic for the actual Bernoulli assignment
law, valid for any function of K and every real p. -/
theorem bernoulli4_count_law (p : ℝ) (F : Fin 5 → ℝ) :
    expect (bernoulli p) (fun z : Assignment 4 => F (countIndex4 z)) =
    expect (binomial4 p) F := by
  simp [expect, bernoulli, treatedCount, countIndex4, sum_tuple_succ,
    Fin.sum_univ_succ, Fin.prod_univ_succ, binomial4, Fin.univ_succ,
    Finset.filter_insert, Finset.filter_singleton, Nat.choose]
  <;> ring


/-- T1: the exact conditional arm-mean and direct-effect failures, computed
on the five-point count law certified by `bernoulli4_count_law`. Own-arm
conditioning and both-arm conditioning are kept separate (p. 310). -/
theorem bernoulli_count_counterexample :
    prob (binomial4 (1/2)) (fun k => 0 < k.val ∧ k.val < 4) = 7/8 ∧
    prob (binomial4 (1/4)) (fun k => 0 < k.val ∧ k.val < 4) = 87/128 ∧
    condMean (binomial4 (1/2)) (fun k => 0 < k.val) (countArm true) = 17/15 ∧
    condMean (binomial4 (1/2)) (fun k => k.val < 4) (countArm false) = 28/15 ∧
    condMean (binomial4 (1/4)) (fun k => 0 < k.val) (countArm true) = 81/175 ∧
    condMean (binomial4 (1/4)) (fun k => k.val < 4) (countArm false) = 84/85 ∧
    condMean (binomial4 (1/2)) (fun k => 0 < k.val ∧ k.val < 4)
      (countArm true) = 1 ∧
    condMean (binomial4 (1/2)) (fun k => 0 < k.val ∧ k.val < 4)
      (countArm false) = 2 ∧
    condMean (binomial4 (1/4)) (fun k => 0 < k.val ∧ k.val < 4)
      (countArm true) = 13/29 ∧
    condMean (binomial4 (1/4)) (fun k => 0 < k.val ∧ k.val < 4)
      (countArm false) = 42/29 ∧
    (∀ k, 0 < k.val → k.val < 4 → countArm true k - countArm false k = -1) := by
  norm_num [prob, condMean, expect, countArm, bit, binomial4, Fin.sum_univ_succ, Nat.choose]

/-- T1: two-stage outcomes: first-stage fair choice of the ψ group, followed
by independent four-unit assignments. There are 2·16·16=512 outcomes. -/
abbrev BernoulliWitnessOutcome := Bool × Assignment 4 × Assignment 4
/-- "the group with S_g=ψ" in T1(ii): select the higher-saturation assignment after the fair first-stage swap; witness, not printed data. -/
def witnessHigh (w : BernoulliWitnessOutcome) : Assignment 4 :=
  if w.1 then w.2.1 else w.2.2
/-- "the group with S_g=φ" in T1(ii): select the lower-saturation assignment after the same swap; witness, not printed data. -/
def witnessLow (w : BernoulliWitnessOutcome) : Assignment 4 :=
  if w.1 then w.2.2 else w.2.1
/-- "Second stage: given the first stage, the eight Z_ig are independent" (T1 setting). The fair first-stage factor and the two Bernoulli product weights define the actual witness law. -/
def bernoulliWitnessMass (w : BernoulliWitnessOutcome) : ℝ :=
  (1/2) * bernoulli (1/2) (witnessHigh w) * bernoulli (1/4) (witnessLow w)
/-- "yhat_g(z;ψ)" (p. 310), evaluated in T1's group assigned the indicated saturation. The accompanying domain records its nonzero denominator. -/
def witnessArm (b : Bool) (high : Bool) (w : BernoulliWitnessOutcome) : ℝ :=
  armMean coMembers b (if high then witnessHigh w else witnessLow w)
/-- "conditional on the denominators of these estimators being nonzero" (p. 310): this is the own-arm existence event in the T1 two-stage witness. -/
def witnessDomain (b : Bool) (high : Bool) (w : BernoulliWitnessOutcome) : Prop :=
  armExists b (if high then witnessHigh w else witnessLow w)
/-- "τhat^D(ψ)=yhat(1;ψ)−yhat(0;ψ)" (p. 310), in the T1 witness with one group per saturation. -/
def witnessDirect (high : Bool) (w : BernoulliWitnessOutcome) : ℝ :=
  witnessArm true high w - witnessArm false high w
/-- "τhat^I(ψ,φ)=yhat(0;ψ)−yhat(0;φ)" (p. 310), in T1's explicit two-stage law. -/
def witnessIndirect (w : BernoulliWitnessOutcome) : ℝ :=
  witnessArm false true w - witnessArm false false w
/-- "τhat^To(ψ,φ)=yhat(1;ψ)−yhat(0;φ)" (p. 310), in T1's explicit two-stage law. -/
def witnessTotal (w : BernoulliWitnessOutcome) : ℝ :=
  witnessArm true true w - witnessArm false false w
/-- "τhat^O(ψ,φ)=yhat(ψ)−yhat(φ)" (p. 310), using all four observed outcomes in each of T1's saturation groups. -/
def witnessOverall (w : BernoulliWitnessOutcome) : ℝ :=
  groupOverall coMembers (witnessHigh w) - groupOverall coMembers (witnessLow w)

/-- T1's 512-outcome law has the independent high/low assignment law
after integrating the fair first-stage swap. This is an exact finite-sum
identity, not an assumption about the count reduction. -/
theorem witness_expect_product (F : Assignment 4 → Assignment 4 → ℝ) :
    expect bernoulliWitnessMass (fun w => F (witnessHigh w) (witnessLow w)) =
      ∑ h, ∑ l, bernoulli (1/2) h*bernoulli (1/4) l*F h l := by
  unfold expect bernoulliWitnessMass witnessHigh witnessLow
  simp only [Fintype.sum_prod_type]
  simp [Fintype.univ_bool]
  have hswap : (∑ l : Assignment 4, ∑ h : Assignment 4,
      (1/2 : ℝ)*bernoulli (1/2) h*bernoulli (1/4) l*F h l) =
      ∑ h : Assignment 4, ∑ l : Assignment 4,
        (1/2 : ℝ)*bernoulli (1/2) h*bernoulli (1/4) l*F h l := Finset.sum_comm
  simp only [one_div] at hswap
  rw [hswap]
  have ht : ∀ h l : Assignment 4,
    (1/2 : ℝ)*bernoulli (1/2) h*bernoulli (1/4) l*F h l =
      (1/2)*(bernoulli (1/2) h*bernoulli (1/4) l*F h l) := by intros; ring
  simp only [one_div] at ht
  simp_rw [ht]
  simp only [← Finset.mul_sum]
  ring

/-- T1's specified two-stage mass is a genuine probability law, with
nonnegative weights and total mass one. -/
theorem witness_mass_is_probability :
    (∀ w, 0 ≤ bernoulliWitnessMass w) ∧ (∑ w, bernoulliWitnessMass w)=1 := by
  constructor
  · intro w
    unfold bernoulliWitnessMass
    apply mul_nonneg
    · apply mul_nonneg (by norm_num)
      exact (bernoulliDesign 4 (1/2) (by norm_num) (by norm_num)).nonneg _
    · exact (bernoulliDesign 4 (1/4) (by norm_num) (by norm_num)).nonneg _
  · have h := witness_expect_product (fun _ _ => 1)
    simp only [expect,mul_one] at h
    rw [h]
    simp only [← Finset.mul_sum, bernoulli_total,mul_one]

/-- T1: integrating the other group and first stage leaves the specified
Bernoulli law for the high-saturation group's labelled assignments. -/
theorem witness_high_expect (X : Assignment 4 → ℝ) :
    expect bernoulliWitnessMass (fun w => X (witnessHigh w)) = expect (bernoulli (1/2)) X := by
  rw [witness_expect_product (fun h _ => X h)]
  have ht : ∀ h l : Assignment 4, bernoulli (1/2) h*bernoulli (1/4) l*X h =
      (bernoulli (1/2) h*X h)*bernoulli (1/4) l := by intros; ring
  simp_rw [ht]
  simp only [← Finset.mul_sum,bernoulli_total,mul_one,expect]

/-- T1: the corresponding exact marginal law of the low-saturation group. -/
theorem witness_low_expect (X : Assignment 4 → ℝ) :
    expect bernoulliWitnessMass (fun w => X (witnessLow w)) = expect (bernoulli (1/4)) X := by
  rw [witness_expect_product (fun _ l => X l)]
  rw [Finset.sum_comm]
  have ht : ∀ h l : Assignment 4, bernoulli (1/2) h*bernoulli (1/4) l*X l =
      (bernoulli (1/4) l*X l)*bernoulli (1/2) h := by intros; ring
  simp_rw [ht]
  simp only [← Finset.mul_sum,bernoulli_total,mul_one,expect]

/-- T1(ii): in the proper 512-outcome law the direct ratios are defined
with probabilities 7/8 and 87/128, respectively, and each has conditional
expectation −1 against its Bernoulli marginal target 0. -/
theorem bernoulli_direct_failure_means (high : Bool) :
    prob bernoulliWitnessMass (fun w => witnessDomain true high w ∧ witnessDomain false high w) =
      (if high then 7/8 else 87/128) ∧
    condMean bernoulliWitnessMass (fun w => witnessDomain true high w ∧ witnessDomain false high w)
      (witnessDirect high) = -1 := by
  classical
  have hprob : prob bernoulliWitnessMass
      (fun w => witnessDomain true high w ∧ witnessDomain false high w) =
        (if high then 7/8 else 87/128) := by
    cases high
    · unfold prob witnessDomain
      simp only [Bool.false_eq_true,ite_false]
      rw [witness_low_expect (fun z => if armExists true z ∧ armExists false z then 1 else 0)]
      have he : (fun z : Assignment 4 => if armExists true z ∧ armExists false z then (1 : ℝ) else 0) =
          (fun z => if 0 < (countIndex4 z).val ∧ (countIndex4 z).val < 4 then 1 else 0) := by
        funext z; simp [four_arm_domains z,countIndex4]
      rw [he,bernoulli4_count_law (1/4) (fun k => if 0 < k.val ∧ k.val < 4 then 1 else 0)]
      norm_num [expect,binomial4,Fin.sum_univ_succ,Nat.choose]
    · unfold prob witnessDomain
      simp only [ite_true]
      rw [witness_high_expect (fun z => if armExists true z ∧ armExists false z then 1 else 0)]
      have he : (fun z : Assignment 4 => if armExists true z ∧ armExists false z then (1 : ℝ) else 0) =
          (fun z => if 0 < (countIndex4 z).val ∧ (countIndex4 z).val < 4 then 1 else 0) := by
        funext z; simp [four_arm_domains z,countIndex4]
      rw [he,bernoulli4_count_law (1/2) (fun k => if 0 < k.val ∧ k.val < 4 then 1 else 0)]
      norm_num [expect,binomial4,Fin.sum_univ_succ,Nat.choose]
  refine ⟨hprob,?_⟩
  rw [← event_ht_conditional]
  apply event_constant_ht
  · intro w hw
    exact co_members_direct_wrong _ hw.1 hw.2
  · rw [hprob]; cases high <;> norm_num

/-- T1: a full-hypothesis counterexample certificate. The proper two-stage
law has 512 outcomes, both Bernoulli marginal direct effects are zero, and
the observed direct estimate is −1 at every point on its domain. The
additional conditional indirect/total arithmetic is stated separately. -/
theorem bernoulli_direct_failure :
    Fintype.card BernoulliWitnessOutcome = 512 ∧
    (∀ w, 0 ≤ bernoulliWitnessMass w) ∧ (∑ w, bernoulliWitnessMass w)=1 ∧
    (∀ p : ℝ, 0 < p → p < 1 →
      mean (fun i : Fin 4 => marginal (bernoulli p) coMembers i true) -
      mean (fun i : Fin 4 => marginal (bernoulli p) coMembers i false) = 0) ∧
    (∀ w high, witnessDomain true high w → witnessDomain false high w →
      witnessDirect high w = -1) := by
  refine ⟨by simp [BernoulliWitnessOutcome,Assignment],
    witness_mass_is_probability.1,witness_mass_is_probability.2,?_,?_⟩
  · intro p hp hp1
    simp [co_members_marginal_four p hp hp1]
  · intro w high h1 h0
    exact co_members_direct_wrong _ h1 h0

/-- Nonempty-arm domains on the four-member count law, T1(iii), p. 310:
treated requires K>0 and control requires K<4. -/
def countDomain (b : Bool) (k : Fin 5) : Prop :=
  if b then 0 < k.val else k.val < 4

/-- T1: each actual witness arm exists exactly on its count-law domain. -/
theorem witness_domain_count (b high : Bool) (w : BernoulliWitnessOutcome) :
    witnessDomain b high w ↔
      countDomain b (countIndex4 (if high then witnessHigh w else witnessLow w)) := by
  cases b <;> simp [witnessDomain, countDomain, four_arm_domains, countIndex4]

/-- T1(iii): transfer the within-arm conditional ratio from the labelled
Bernoulli cube to its proved count pushforward; the ratio is only used on
the nonempty-arm event. -/
theorem bernoulli_arm_count_conditional (p : ℝ) (b : Bool) :
    condMean (bernoulli p) (armExists b) (armMean (coMembers (n := 4)) b) =
      condMean (binomial4 p) (countDomain b) (countArm b) := by
  classical
  have hd : ∀ z : Assignment 4, armExists b z ↔ countDomain b (countIndex4 z) := by
    intro z; cases b <;> simp [countDomain, four_arm_domains, countIndex4]
  have hf : (fun z : Assignment 4 => if armExists b z then armMean coMembers b z else 0) =
      (fun z => if countDomain b (countIndex4 z) then countArm b (countIndex4 z) else 0) := by
    funext z
    by_cases h : armExists b z
    · simp only [← hd z, if_pos h]
      exact co_members_arm_mean z b h
    · simp [h, ← hd z]
  unfold condMean prob
  rw [hf, bernoulli4_count_law p (fun k => if countDomain b k then countArm b k else 0)]
  simp_rw [hd]
  rw [bernoulli4_count_law p (fun k => if countDomain b k then 1 else 0)]

/-- The joint count pushforward of T1's specified two-stage law. This is
derived from its fair first-stage swap and independent Bernoulli cubes. -/
def witnessCountMass (k : Fin 5 × Fin 5) : ℝ :=
  binomial4 (1/2) k.1 * binomial4 (1/4) k.2

/-- T1: integrate the fair swap, then push forward each independent
four-member Bernoulli cube to its treated count. -/
theorem witness_count_expect (F : Fin 5 → Fin 5 → ℝ) :
    expect bernoulliWitnessMass (fun w =>
      F (countIndex4 (witnessHigh w)) (countIndex4 (witnessLow w))) =
    expect witnessCountMass (fun k => F k.1 k.2) := by
  rw [witness_expect_product (fun h l => F (countIndex4 h) (countIndex4 l))]
  have h : (∑ h : Assignment 4, ∑ l : Assignment 4,
      bernoulli (1/2) h * bernoulli (1/4) l * F (countIndex4 h) (countIndex4 l)) =
      expect (bernoulli (1/2)) (fun h =>
        expect (bernoulli (1/4)) (fun l => F (countIndex4 h) (countIndex4 l))) := by
    simp [expect, Finset.mul_sum, mul_assoc]
  rw [h]
  simp_rw [bernoulli4_count_law (1/4)]
  rw [bernoulli4_count_law (1/2) (fun h => expect (binomial4 (1/4)) (F h))]
  simp [expect, witnessCountMass, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- T1(iv): transfer conditional means on joint count events. Agreement
of estimators is required only where every necessary arm is nonempty. -/
theorem witness_count_conditional (E : Fin 5 → Fin 5 → Prop)
    (X : BernoulliWitnessOutcome → ℝ) (F : Fin 5 → Fin 5 → ℝ)
    (hX : ∀ w, E (countIndex4 (witnessHigh w)) (countIndex4 (witnessLow w)) →
      X w = F (countIndex4 (witnessHigh w)) (countIndex4 (witnessLow w))) :
    condMean bernoulliWitnessMass (fun w =>
      E (countIndex4 (witnessHigh w)) (countIndex4 (witnessLow w))) X =
    condMean witnessCountMass (fun k => E k.1 k.2) (fun k => F k.1 k.2) := by
  classical
  have hf : (fun w => if E (countIndex4 (witnessHigh w)) (countIndex4 (witnessLow w))
      then X w else 0) = (fun w =>
        if E (countIndex4 (witnessHigh w)) (countIndex4 (witnessLow w))
        then F (countIndex4 (witnessHigh w)) (countIndex4 (witnessLow w)) else 0) := by
    funext w
    by_cases h : E (countIndex4 (witnessHigh w)) (countIndex4 (witnessLow w))
    · simp [h, hX w h]
    · simp [h]
  unfold condMean prob
  rw [hf, witness_count_expect (fun h l => if E h l then F h l else 0),
    witness_count_expect (fun h l => if E h l then 1 else 0)]

/-- T1, full witness, clauses (i)–(v): all unit marginal targets,
the wrong direct estimate on every defined assignment, all reported
conditional means and event probabilities, and unbiased overall contrast.
The 512 outcomes include the first-stage choice explicitly. -/
theorem bernoulli_ratio_counterexample :
    Fintype.card BernoulliWitnessOutcome = 512 ∧
    (∑ w, bernoulliWitnessMass w) = 1 ∧
    (∀ p : ℝ, 0 < p → p < 1 → ∀ i : Fin 4, ∀ b : Bool,
      marginal (bernoulli p) coMembers i b = 3*p) ∧
    (∀ z : Assignment 4, ∀ i, coMembers i z = (treatedCount z : ℝ) - bit (z i)) ∧
    (∀ w high, witnessDomain true high w → witnessDomain false high w →
      witnessDirect high w = -1) ∧
    (∀ p : ℝ, 0 < p → p < 1 → ∀ b,
      condMean (bernoulli p) (fun z : Assignment 4 => armExists b z) (armMean coMembers b) =
      condMean (binomial4 p) (fun k => if b then 0 < k.val else k.val < 4) (countArm b)) ∧
    prob bernoulliWitnessMass (fun w => witnessDomain true true w ∧ witnessDomain false true w) = 7/8 ∧
    prob bernoulliWitnessMass (fun w => witnessDomain true false w ∧ witnessDomain false false w) = 87/128 ∧
    prob bernoulliWitnessMass (fun w => witnessDomain false true w ∧ witnessDomain false false w) = 3825/4096 ∧
    prob bernoulliWitnessMass (fun w => witnessDomain true true w ∧ witnessDomain false false w) = 3825/4096 ∧
    condMean bernoulliWitnessMass (fun w => witnessDomain false true w ∧ witnessDomain false false w)
      witnessIndirect = 224/255 ∧
    condMean bernoulliWitnessMass (fun w => witnessDomain true true w ∧ witnessDomain false false w)
      witnessTotal = 37/255 ∧
    prob bernoulliWitnessMass (fun w => ∀ b high, witnessDomain b high w) = 609/1024 ∧
    condMean bernoulliWitnessMass (fun w => ∀ b high, witnessDomain b high w) witnessIndirect = 16/29 ∧
    condMean bernoulliWitnessMass (fun w => ∀ b high, witnessDomain b high w) witnessTotal = -13/29 ∧
    (∀ z : Assignment 4, groupOverall coMembers z = (3/4)*(treatedCount z : ℝ)) ∧
    expect bernoulliWitnessMass witnessOverall = 3/4 := by
  classical
  refine ⟨by simp [BernoulliWitnessOutcome, Assignment], witness_mass_is_probability.2,
    co_members_marginal_four, co_members_count, ?_, ?_,
    (bernoulli_direct_failure_means true).1, (bernoulli_direct_failure_means false).1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, co_members_overall_four, ?_⟩
  · intro w high ht hc
    exact co_members_direct_wrong _ ht hc
  · intro p hp hp1 b
    exact bernoulli_arm_count_conditional p b
  · simp_rw [witness_domain_count]
    change prob bernoulliWitnessMass (fun w =>
      countDomain false (countIndex4 (witnessHigh w)) ∧
      countDomain false (countIndex4 (witnessLow w))) = _
    unfold prob
    have h := witness_count_expect (fun h l => if countDomain false h ∧ countDomain false l then 1 else 0)
    have hn : expect witnessCountMass (fun k =>
      if countDomain false k.1 ∧ countDomain false k.2 then 1 else 0) = 3825/4096 := by
      norm_num [expect, witnessCountMass, countDomain, binomial4,
        Fintype.sum_prod_type, Fin.sum_univ_succ, Nat.choose]
    convert h.trans hn using 1
    apply congrArg (expect bernoulliWitnessMass)
    funext w
    split_ifs <;> rfl
  · simp_rw [witness_domain_count]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    unfold prob
    have h := witness_count_expect (fun h l => if countDomain true h ∧ countDomain false l then 1 else 0)
    have hn : expect witnessCountMass (fun k =>
      if countDomain true k.1 ∧ countDomain false k.2 then 1 else 0) = 3825/4096 := by
      norm_num [expect, witnessCountMass, countDomain, binomial4,
        Fintype.sum_prod_type, Fin.sum_univ_succ, Nat.choose]
    convert h.trans hn using 1
    apply congrArg (expect bernoulliWitnessMass)
    funext w
    split_ifs <;> rfl
  · simp_rw [witness_domain_count]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    rw [witness_count_conditional (fun h l => countDomain false h ∧ countDomain false l) witnessIndirect
      (fun h l => countArm false h - countArm false l)]
    · norm_num [condMean, prob, expect, witnessCountMass, countDomain, countArm, bit,
        binomial4, Fintype.sum_prod_type, Fin.sum_univ_succ, Nat.choose]
    · intro w hw
      simp only [countDomain, Bool.false_eq_true, ite_false] at hw
      have hh := (four_arm_domains (witnessHigh w)).2.mpr hw.1
      have hl := (four_arm_domains (witnessLow w)).2.mpr hw.2
      simp [witnessIndirect, witnessArm, co_members_arm_mean _ false hh,
        co_members_arm_mean _ false hl, countArm, countIndex4]
  · simp_rw [witness_domain_count]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    rw [witness_count_conditional (fun h l => countDomain true h ∧ countDomain false l) witnessTotal
      (fun h l => countArm true h - countArm false l)]
    · norm_num [condMean, prob, expect, witnessCountMass, countDomain, countArm, bit,
        binomial4, Fintype.sum_prod_type, Fin.sum_univ_succ, Nat.choose]
    · intro w hw
      simp only [countDomain, ite_true, Bool.false_eq_true, ite_false] at hw
      have hh := (four_arm_domains (witnessHigh w)).1.mpr hw.1
      have hl := (four_arm_domains (witnessLow w)).2.mpr hw.2
      simp [witnessTotal, witnessArm, co_members_arm_mean _ true hh,
        co_members_arm_mean _ false hl, countArm, countIndex4]
  · simp only [Bool.forall_bool, witnessDomain, ite_true, Bool.false_eq_true, ite_false]
    simp_rw [four_arm_domains]
    unfold prob
    have h := witness_count_expect (fun h l => if
      (l.val < 4 ∧ h.val < 4) ∧ (0 < l.val ∧ 0 < h.val) then 1 else 0)
    have hn : expect witnessCountMass (fun k => if
      (k.2.val < 4 ∧ k.1.val < 4) ∧ (0 < k.2.val ∧ 0 < k.1.val) then 1 else 0) = 609/1024 := by
      norm_num [expect, witnessCountMass, binomial4,
        Fintype.sum_prod_type, Fin.sum_univ_succ, Nat.choose]
    convert h.trans hn using 1 <;> simp only [countIndex4]
    apply congrArg (expect bernoulliWitnessMass)
    funext w
    split_ifs <;> rfl
  · simp only [Bool.forall_bool, witnessDomain, ite_true, Bool.false_eq_true, ite_false]
    simp_rw [four_arm_domains]
    trans condMean witnessCountMass (fun k =>
      (k.2.val < 4 ∧ k.1.val < 4) ∧ (0 < k.2.val ∧ 0 < k.1.val))
      (fun k => countArm false k.1 - countArm false k.2)
    · have hx : ∀ w, ((treatedCount (witnessLow w) < 4 ∧ treatedCount (witnessHigh w) < 4) ∧
          (0 < treatedCount (witnessLow w) ∧ 0 < treatedCount (witnessHigh w))) →
          witnessIndirect w = countArm false (countIndex4 (witnessHigh w)) -
            countArm false (countIndex4 (witnessLow w)) := by
        intro w hw
        have hh := (four_arm_domains (witnessHigh w)).2.mpr hw.1.2
        have hl := (four_arm_domains (witnessLow w)).2.mpr hw.1.1
        simp [witnessIndirect, witnessArm, co_members_arm_mean _ false hh,
          co_members_arm_mean _ false hl, countArm, countIndex4]
      simpa only [countIndex4] using witness_count_conditional (fun h l =>
        (l.val < 4 ∧ h.val < 4) ∧ (0 < l.val ∧ 0 < h.val)) witnessIndirect
        (fun h l => countArm false h - countArm false l) hx
    · norm_num [condMean, prob, expect, witnessCountMass, countArm, bit,
        binomial4, Fintype.sum_prod_type, Fin.sum_univ_succ, Nat.choose]
  · simp only [Bool.forall_bool, witnessDomain, ite_true, Bool.false_eq_true, ite_false]
    simp_rw [four_arm_domains]
    trans condMean witnessCountMass (fun k =>
      (k.2.val < 4 ∧ k.1.val < 4) ∧ (0 < k.2.val ∧ 0 < k.1.val))
      (fun k => countArm true k.1 - countArm false k.2)
    · have hx : ∀ w, ((treatedCount (witnessLow w) < 4 ∧ treatedCount (witnessHigh w) < 4) ∧
          (0 < treatedCount (witnessLow w) ∧ 0 < treatedCount (witnessHigh w))) →
          witnessTotal w = countArm true (countIndex4 (witnessHigh w)) -
            countArm false (countIndex4 (witnessLow w)) := by
        intro w hw
        have hh := (four_arm_domains (witnessHigh w)).1.mpr hw.2.2
        have hl := (four_arm_domains (witnessLow w)).2.mpr hw.1.1
        simp [witnessTotal, witnessArm, co_members_arm_mean _ true hh,
          co_members_arm_mean _ false hl, countArm, countIndex4]
      simpa only [countIndex4] using witness_count_conditional (fun h l =>
        (l.val < 4 ∧ h.val < 4) ∧ (0 < l.val ∧ 0 < h.val)) witnessTotal
        (fun h l => countArm true h - countArm false l) hx
    · norm_num [condMean, prob, expect, witnessCountMass, countArm, bit,
        binomial4, Fintype.sum_prod_type, Fin.sum_univ_succ, Nat.choose]
  · unfold witnessOverall
    rw [expect_sub, witness_high_expect, witness_low_expect]
    have hg : groupOverall (coMembers (n := 4)) =
        fun z => (∑ i, bit (z i))*(3/4) := by
      funext z
      rw [co_members_overall_four, sum_bit_count]
      ring
    rw [hg, expect_mul_const, expect_mul_const, expect_sum, expect_sum]
    simp_rw [bernoulli_coordinate_expect]
    norm_num [bit, Fin.sum_univ_succ]

/-- T2(a): unconditional group HT mean, replacing the ratio on p. 310;
π_z(p)=p for treated and 1−p for control. Empty arms contribute zero. -/
def groupHT {n : ℕ} (p : ℝ) (y : Fin n → Assignment n → ℝ)
    (b : Bool) (z : Assignment n) : ℝ :=
  (∑ i, if z i = b then y i z else 0) / ((n : ℝ) * (if b then p else 1-p))

/-- T2(a): the corrected Bernoulli HT group mean is unbiased for exactly
the original marginal target, over all assignments including empty arms. -/
theorem bernoulli_group_ht_unbiased {n : ℕ} (hn : 0 < n) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (y : Fin n → Assignment n → ℝ) (b : Bool) :
    (∀ i, expect (bernoulli p) (fun z => if z i=b then y i z else 0) =
      (if b then p else 1-p)*marginal (bernoulli p) y i b) ∧
    expect (bernoulli p) (groupHT p y b) = mean (fun i => marginal (bernoulli p) y i b) := by
  have hπ : (if b then p else 1-p) ≠ 0 := by cases b <;> simp <;> linarith
  have hm : ∀ i, expect (bernoulli p) (fun z => if z i=b then y i z else 0) =
      (if b then p else 1-p)*marginal (bernoulli p) y i b := by
    intro i
    unfold marginal condMean
    rw [bernoulli_arm_probability]
    field_simp [hπ]
    apply congrArg (expect (bernoulli p))
    funext z
    by_cases h : z i=b <;> simp [h]
  refine ⟨hm,?_⟩
  unfold groupHT mean
  simp only [Fintype.card_fin]
  rw [expect_div,expect_sum]
  simp_rw [hm]
  rw [← Finset.mul_sum]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp [hn',hπ] <;> ring

/-- T2(f): in the four-member peer-count schedule the repaired group
HT means are K(K−1)/(4p) and K(4−K)/(4(1−p)), including empty arms. -/
theorem co_members_group_ht_formula (p : ℝ) (z : Assignment 4) :
    groupHT p coMembers true z =
      (treatedCount z : ℝ)*((treatedCount z : ℝ)-1)/(4*p) ∧
    groupHT p coMembers false z =
      (treatedCount z : ℝ)*(4-(treatedCount z : ℝ))/(4*(1-p)) := by
  have h1 : ∀ i, (if z i=true then coMembers i z else 0) =
      (if z i=true then (1 : ℝ) else 0)*((treatedCount z : ℝ)-1) := by
    intro i; by_cases h : z i=true <;> simp [h,co_members_count,bit]
  have h0 : ∀ i, (if z i=false then coMembers i z else 0) =
      (if z i=false then (1 : ℝ) else 0)*(treatedCount z : ℝ) := by
    intro i; by_cases h : z i=false <;> simp [h,co_members_count,bit]
  have hs0 : (∑ i, if z i=false then (1 : ℝ) else 0)=4-(treatedCount z : ℝ) := by
    have he : ∀ i, (if z i=false then (1 : ℝ) else 0)=1-bit (z i) := by
      intro i; cases z i <;> simp [bit]
    simp_rw [he]
    simp [Finset.sum_sub_distrib,sum_bit_count]
  constructor
  · unfold groupHT
    simp_rw [h1]
    rw [← Finset.sum_mul]
    simp [bit,treatedCount]
  · unfold groupHT
    simp_rw [h0]
    rw [← Finset.sum_mul,hs0]
    simp only [Bool.false_eq_true,ite_false,Nat.cast_ofNat]
    ring

/-- T2(f): both corrected HT arm means in the actual four-unit
Bernoulli law have expectation 3p, so their direct contrast has mean zero. -/
theorem co_members_group_ht_expectation (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    expect (bernoulli p) (groupHT p (coMembers (n := 4)) true)=3*p ∧
    expect (bernoulli p) (groupHT p (coMembers (n := 4)) false)=3*p ∧
    expect (bernoulli p) (fun z : Assignment 4 =>
      groupHT p coMembers true z-groupHT p coMembers false z)=0 := by
  have ht := (bernoulli_group_ht_unbiased (by norm_num : 0<4) p hp hp1 coMembers true).2
  have hc := (bernoulli_group_ht_unbiased (by norm_num : 0<4) p hp hp1 coMembers false).2
  simp [co_members_marginal_four p hp hp1,mean] at ht hc
  exact ⟨ht,hc,by rw [expect_sub,ht,hc]; ring⟩

/-- First-stage uniform selection of C groups among G (p. 310; T2(b)). -/
def firstStageSets (G C : ℕ) : Finset (Finset (Fin G)) := univ.powersetCard C

/-- Assignments inside the disjoint groups of pp. 308–310. Local outcome
functions below depend only on this local assignment, enforcing partial interference. -/
abbrev GroupAssignments {G : ℕ} (n : Fin G → ℕ) := (g : Fin G) → Assignment (n g)

/-- A two-stage law: uniform C-subset of groups, independent within-group
laws q_g. Unselected local assignments are auxiliary draws integrated out. -/
def selectedLaw {G : ℕ} (n : Fin G → ℕ) (C : ℕ)
    (q : (g : Fin G) → Assignment (n g) → ℝ)
    (w : Finset (Fin G) × GroupAssignments n) : ℝ :=
  if w.1 ∈ firstStageSets G C then
    (1 / (firstStageSets G C).card) * ∏ g, q g (w.2 g) else 0

/-- Average of group estimates over the C groups assigned this saturation,
the second displayed estimator on p. 310. -/
def selectedMean {G : ℕ} {n : Fin G → ℕ} (C : ℕ)
    (X : (g : Fin G) → Assignment (n g) → ℝ)
    (w : Finset (Fin G) × GroupAssignments n) : ℝ :=
  (∑ g ∈ w.1, X g (w.2 g)) / C

/-- Complete-randomization mass within a group, pp. 309–310. -/
def crMass (n k : ℕ) (z : Assignment n) : ℝ :=
  if z ∈ fixedAssignments n k then 1 / (fixedAssignments n k).card else 0

/-- Complete-randomization expectation is uniform averaging over the
fixed-count support, the design of pp. 309–310. -/
theorem cr_expect_average (n k : ℕ) (F : Assignment n → ℝ) :
    expect (crMass n k) F=average (fixedAssignments n k) F := by
  calc
    _ = ∑ z : Assignment n, if z ∈ fixedAssignments n k then F z/(fixedAssignments n k).card else 0 := by
      unfold expect
      apply Finset.sum_congr rfl
      intro z hz
      by_cases h : z ∈ fixedAssignments n k <;> simp [crMass,h,div_eq_mul_inv,mul_comm]
    _ = _ := by simp [Finset.sum_ite,average,Finset.sum_div]

/-- Finite product-law expectation factors for a product of local
statistics, the independent second stage of p. 310. -/
theorem independent_expect_product {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] (q : Ω → ℝ) (X : I → Ω → ℝ) :
    expect (fun w : I → Ω => ∏ i, q (w i)) (fun w => ∏ i, X i (w i)) =
      ∏ i, expect q (X i) := by
  unfold expect
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i w => q w * X i w)).symm

/-- Two specified coordinates contribute their two scalar factors to a
finite product; every other coordinate contributes one. -/
theorem product_two_factors {I : Type*} [Fintype I] [DecidableEq I]
    (i j : I) (hij : i ≠ j) (a b : ℝ) :
    (∏ g : I, if g=i then a else if g=j then b else 1) = a*b := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have he : (∏ g ∈ univ.erase i, if g=i then a else if g=j then b else 1) = b := by
    rw [Finset.prod_eq_single j]
    · simp [hij.symm]
    · intro g hg hgj
      simp [(Finset.mem_erase.mp hg).1, hgj]
    · intro hj
      exact False.elim (hj (by simp [hij.symm]))
  rw [he]
  simp [mul_comm]

/-- T3–T4: local statistics in distinct independently randomized groups
have product expectation equal to the product of their expectations. -/
theorem independent_pair_expect {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] (q : Ω → ℝ) (hq : ∑ w, q w=1)
    (i j : I) (hij : i ≠ j) (X Y : Ω → ℝ) :
    expect (fun w : I → Ω => ∏ g, q (w g)) (fun w => X (w i)*Y (w j)) =
      expect q X * expect q Y := by
  classical
  let F : I → Ω → ℝ := fun g w => if g=i then X w else if g=j then Y w else 1
  have hF : ∀ w : I → Ω, (∏ g, F g (w g)) = X (w i)*Y (w j) := by
    intro w
    calc
      _ = ∏ g : I, if g=i then X (w i) else if g=j then Y (w j) else 1 := by
        apply Finset.prod_congr rfl
        intro g hg
        by_cases hi : g=i <;> by_cases hj : g=j <;> simp [F, hi, hj, hij.symm]
      _ = _ := product_two_factors i j hij _ _
  have he : ∀ g : I, expect q (F g) =
      if g=i then expect q X else if g=j then expect q Y else 1 := by
    intro g
    by_cases hi : g=i <;> by_cases hj : g=j <;>
      simp [F, hi, hj, expect, hq]
  have h := independent_expect_product q F
  simp_rw [hF, he] at h
  rw [h, product_two_factors i j hij]

/-- Integrate the independent second stage and then average over uniform
first-stage sets, for any statistic (p. 310, T2–T4). -/
theorem selected_expect_average {G : ℕ} (n : Fin G → ℕ) (C : ℕ)
    (q : (g : Fin G) → Assignment (n g) → ℝ)
    (X : Finset (Fin G) × GroupAssignments n → ℝ) :
    expect (selectedLaw n C q) X = average (firstStageSets G C)
      (fun H => expect (fun w : GroupAssignments n => ∏ g, q g (w g)) (fun w => X (H,w))) := by
  unfold expect selectedLaw average
  simp only [Fintype.sum_prod_type]
  simp [ite_mul, Finset.sum_ite, Finset.mul_sum, Finset.sum_div,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- T3's local complete-randomization supports contain exactly the three
single-treatment and the three single-control assignments, respectively. -/
theorem fixed_three_supports :
    fixedAssignments 3 1 = {![true,false,false],![false,true,false],![false,false,true]} ∧
    fixedAssignments 3 2 = {![false,true,true],![true,false,true],![true,true,false]} := by
  decide

/-- T2(b): double counting the selected groups in a uniform C-subset.
Each group occurs in choose(G−1,C−1) of the first-stage assignments. -/
theorem first_stage_sum {G C : ℕ} (hC : 0 < C) (X : Fin G → ℝ) :
    (∑ H ∈ firstStageSets G C, ∑ g ∈ H, X g) =
      (Nat.choose (G-1) (C-1) : ℝ) * ∑ g, X g := by
  classical
  have hsum (H : Finset (Fin G)) : (∑ g ∈ H, X g) =
      ∑ g, if g ∈ H then X g else 0 := by
    simp [Finset.sum_ite, Finset.filter_mem_eq_inter]
  simp_rw [hsum]
  rw [Finset.sum_comm]
  have hc (g : Fin G) :
      ((firstStageSets G C).filter (fun H => g ∈ H)).card = Nat.choose (G-1) (C-1) := by
    simpa [firstStageSets] using Finset.card_filter_powersetCard_subset
      ({g} : Finset (Fin G)) univ C (by simp) (by simp; omega)
  simp_rw [Finset.sum_ite, Finset.sum_const, hc]
  simp [← Finset.mul_sum]

/-- T2(b): uniform selection of exactly C>0 groups preserves the equal
group population mean. The proof uses membership counts, including C=G. -/
theorem uniform_first_stage_mean {G C : ℕ} (hC : 0 < C) (hCG : C ≤ G)
    (X : Fin G → ℝ) :
    average (firstStageSets G C) (fun H => (∑ g ∈ H, X g)/C) = mean X := by
  classical
  have hG : 0 < G := lt_of_lt_of_le hC hCG
  have hc : 0 < (firstStageSets G C).card := by
    apply Finset.card_pos.mpr
    exact Finset.powersetCard_nonempty.mpr (by simpa using hCG)
  have hcounts : ((firstStageSets G C).card : ℝ) * C =
      (Nat.choose (G-1) (C-1) : ℝ) * G := by
    have h := first_stage_sum hC (fun _ : Fin G => (1 : ℝ))
    have hs : ∀ H ∈ firstStageSets G C, (∑ _g ∈ H, (1 : ℝ)) = C := by
      intro H hH
      have hh := (Finset.mem_powersetCard.mp hH).2
      simp [hh]
    rw [Finset.sum_congr rfl hs] at h
    simpa using h
  unfold average mean
  simp only [← Finset.sum_div]
  rw [first_stage_sum hC X]
  simp only [Fintype.card_fin]
  have hCn : (C : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hC)
  have hGn : (G : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hG)
  have hFn : ((firstStageSets G C).card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hc)
  field_simp [hCn, hGn, hFn]
  nlinarith [congrArg (fun t : ℝ => t * ∑ g, X g) hcounts]

/-- T2(b): independent local randomization integrates out every other
group's assignment when taking the expectation of one group's statistic. -/
theorem independent_coordinate_expect {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (q : ∀ i, Ω i → ℝ)
    (hq : ∀ i, ∑ w, q i w = 1) (i : I) (X : Ω i → ℝ) :
    expect (fun w : ∀ j, Ω j => ∏ j, q j (w j)) (fun w => X (w i)) =
      expect (q i) X := by
  classical
  have hp (w : ∀ j, Ω j) : (∏ j, q j (w j)) * X (w i) =
      ∏ j, if h : j=i then q j (w j) * X (h ▸ w j) else q j (w j) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    simp only [dite_true]
    have he : (∏ j ∈ univ.erase i,
        if h : j=i then q j (w j) * X (h ▸ w j) else q j (w j)) =
        ∏ j ∈ univ.erase i, q j (w j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [(Finset.mem_erase.mp hj).1]
    rw [he]
    ring
  unfold expect
  simp_rw [hp]
  rw [← Fintype.prod_sum (fun j w =>
    if h : j=i then q j w * X (h ▸ w) else q j w)]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [dite_true]
  have he : (∏ j ∈ univ.erase i,
      ∑ w : Ω j, if h : j=i then q j w * X (h ▸ w) else q j w) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simpa [(Finset.mem_erase.mp hj).1] using hq j
  rw [he, one_mul]

/-- T2(b): the actual uniform-first-stage, independent-second-stage law
preserves the population mean of arbitrary local estimates. -/
theorem selected_mean_expect {G C : ℕ} (hC : 0 < C) (hCG : C ≤ G)
    (n : Fin G → ℕ) (q : (g : Fin G) → Assignment (n g) → ℝ)
    (hq : ∀ g, ∑ z, q g z = 1)
    (X : (g : Fin G) → Assignment (n g) → ℝ) :
    expect (selectedLaw n C q) (selectedMean C X) =
      mean (fun g => expect (q g) (X g)) := by
  classical
  have he : expect (selectedLaw n C q) (selectedMean C X) =
      average (firstStageSets G C) (fun H =>
        expect (fun w : GroupAssignments n => ∏ g, q g (w g))
          (fun w => (∑ g ∈ H, X g (w g))/C)) := by
    unfold expect selectedLaw selectedMean average
    simp only [Fintype.sum_prod_type]
    simp [ite_mul, Finset.sum_ite, Finset.mul_sum, Finset.sum_div,
      div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  rw [he]
  have hs : ∀ H : Finset (Fin G),
      expect (fun w : GroupAssignments n => ∏ g, q g (w g))
        (fun w => (∑ g ∈ H, X g (w g))/C) =
      (∑ g ∈ H, expect (q g) (X g))/C := by
    intro H
    rw [expect_div]
    unfold expect
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    exact independent_coordinate_expect q hq g (X g)
  simp_rw [hs]
  exact uniform_first_stage_mean hC hCG _

/-- Treatment subsets and binary assignment vectors are equivalent objects
(p. 292, complete random assignment), preserving the treated membership. -/
def subsetAssignment (n : ℕ) : Finset (Fin n) ≃ Assignment n where
  toFun S i := decide (i ∈ S)
  invFun z := univ.filter (fun i => z i=true)
  left_inv S := by ext i; simp
  right_inv z := by funext i; cases h : z i <;> simp [h]

/-- T2(c): uniform fixed-count assignments are exactly the binary images
of the k-element treatment subsets, with no replacement and no repetitions. -/
theorem fixed_assignments_map (n k : ℕ) :
    fixedAssignments n k = (univ.powersetCard k).map (subsetAssignment n).toEmbedding := by
  classical
  ext z
  simp only [fixedAssignments, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · intro hz
    refine ⟨(subsetAssignment n).symm z, ?_, (subsetAssignment n).apply_symm_apply z⟩
    simpa [subsetAssignment] using hz
  · rintro ⟨S, hS, rfl⟩
    simpa [subsetAssignment] using (Finset.mem_powersetCard.mp hS).2

/-- T2(c): change variables from binary fixed-count assignments to their
uniform k-subset representation in an exact finite expectation. -/
theorem cr_subset_average (n k : ℕ) (F : Assignment n → ℝ) :
    expect (crMass n k) F = average (univ.powersetCard k)
      (fun S => F (subsetAssignment n S)) := by
  rw [cr_expect_average, fixed_assignments_map]
  simp [average]

/-- T2(c): each unit's treated probability in uniform fixed-count
assignment is k/n, by the same uniform-subset calculation as the first stage. -/
theorem cr_treated_probability {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (i : Fin n) :
    prob (crMass n k) (fun z => z i=true) = (k : ℝ)/n := by
  classical
  have hp : prob (crMass n k) (fun z => z i=true) =
      average (univ.powersetCard k) (fun S : Finset (Fin n) => if i ∈ S then 1 else 0) := by
    unfold prob
    rw [cr_subset_average]
    simp [subsetAssignment]
  have h := uniform_first_stage_mean hk hkn (fun j : Fin n => if j=i then (1 : ℝ) else 0)
  have hs : ∀ S : Finset (Fin n),
      (∑ j ∈ S, if j=i then (1 : ℝ) else 0) = if i ∈ S then 1 else 0 := by
    intro S; simp
  simp_rw [hs] at h
  have h' : average (univ.powersetCard k)
      (fun S : Finset (Fin n) => if i ∈ S then (1 : ℝ) else 0)/k = 1/n := by
    simpa [firstStageSets, average, mean, ← Finset.sum_div, div_div, mul_comm] using h
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have hknz : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  have hnnz : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  rw [hp]
  field_simp [hknz, hnnz] at h' ⊢
  nlinarith

/-- T2(c): the fixed-count mass is a normalized nonnegative probability
law whenever the chosen count is feasible. -/
theorem cr_mass_probability {n k : ℕ} (hkn : k ≤ n) :
    (∀ z, 0 ≤ crMass n k z) ∧ (∑ z, crMass n k z)=1 := by
  classical
  have hc : 0 < (fixedAssignments n k).card := by
    rw [fixed_assignments_map, Finset.card_map]
    exact Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr (by simpa using hkn))
  constructor
  · intro z; unfold crMass; split_ifs <;> positivity
  · simp [crMass, Finset.sum_ite, ne_of_gt (Nat.cast_pos.mpr hc)]

/-- T2(c): fixed-count arm probabilities are k/n for treatment and
(n−k)/n for control; both are positive for 0<k<n. -/
theorem cr_arm_probability {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (i : Fin n) (b : Bool) :
    prob (crMass n k) (fun z => z i=b) =
      (if b then (k : ℝ) else (n-k : ℕ))/n := by
  classical
  cases b
  · have ht : expect (crMass n k) (fun _ => 1) = 1 := by
      simpa [expect] using (cr_mass_probability (le_of_lt hkn)).2
    have he : prob (crMass n k) (fun z => z i=false) +
        prob (crMass n k) (fun z => z i=true) = 1 := by
      unfold prob
      rw [← expect_add]
      calc
        _ = expect (crMass n k) (fun _ => 1) := by
          apply congrArg (expect (crMass n k))
          funext z
          cases hz : z i <;> simp [hz]
        _ = 1 := ht
    rw [cr_treated_probability hk (le_of_lt hkn)] at he
    simp only [Bool.false_eq_true, ite_false]
    rw [Nat.cast_sub (le_of_lt hkn)]
    have hn : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (lt_trans hk hkn))
    field_simp [hn] at he ⊢
    linarith
  · simpa using cr_treated_probability hk (le_of_lt hkn) i

/-- T2(c): fixed positive arm counts make the displayed within-arm mean
unbiased for the conditional marginal outcomes of that fixed-count law. -/
theorem cr_group_arm_unbiased {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (y : Fin n → Assignment n → ℝ) (b : Bool) :
    expect (crMass n k) (armMean y b) =
      mean (fun i => marginal (crMass n k) y i b) := by
  classical
  let kb : ℕ := if b then k else n-k
  have hkb : 0 < kb := by cases b <;> simp [kb] <;> omega
  have hden : ∀ z ∈ fixedAssignments n k,
      (∑ i, if z i=b then (1 : ℝ) else 0) = kb := by
    intro z hz
    have hc : (univ.filter (fun i => z i=true)).card=k := (Finset.mem_filter.mp hz).2
    cases b
    · have hn := Finset.card_filter_add_card_filter_not (s := univ) (fun i : Fin n => z i=true)
      have hf : (univ.filter (fun i : Fin n => ¬z i=true)) = univ.filter (fun i => z i=false) := by
        ext i; cases z i <;> simp
      rw [hf, hc] at hn
      have hc0 : (univ.filter (fun i => z i=false)).card=n-k := by
        simp only [Finset.card_univ, Fintype.card_fin] at hn
        omega
      simp [Finset.sum_ite, hc0, kb]
    · simp [Finset.sum_ite, hc, kb]
  have he : expect (crMass n k) (armMean y b) =
      expect (crMass n k) (fun z => (∑ i, if z i=b then y i z else 0)/kb) := by
    unfold expect
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hs : z ∈ fixedAssignments n k
    · simp only [armMean, hden z hs]
    · simp [crMass, hs]
  rw [he, expect_div, expect_sum]
  unfold mean marginal condMean
  simp_rw [cr_arm_probability hk hkn]
  have hkbn : (kb : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hkb)
  have hnn : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (lt_trans hk hkn))
  have hcast : (if b then (k : ℝ) else (n-k : ℕ)) = (kb : ℝ) := by cases b <;> rfl
  rw [hcast]
  simp only [Fintype.card_fin, div_div, ← Finset.sum_div]
  field_simp [hkbn, hnn]
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (expect (crMass n k))
  funext z
  split_ifs <;> rfl

/-- T2(d): the co-member-count schedule has fixed-count conditional
marginals k−1 and k, which differ from the Bernoulli marginals of p. 309. -/
theorem cr_co_members_marginal {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (i : Fin n) (b : Bool) :
    marginal (crMass n k) coMembers i b = (k : ℝ)-bit b := by
  classical
  have he : expect (crMass n k) (fun z => if z i=b then coMembers i z else 0) =
      expect (crMass n k) (fun z => if z i=b then (k : ℝ)-bit b else 0) := by
    unfold expect
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hs : z ∈ fixedAssignments n k
    · have hc : treatedCount z=k := (Finset.mem_filter.mp hs).2
      by_cases hb : z i=b <;> simp [hb, co_members_count, hc]
    · simp [crMass, hs]
  have hpn : prob (crMass n k) (fun z => z i=b) ≠ 0 := by
    rw [cr_arm_probability hk hkn]
    have hn : 0 < n := lt_trans hk hkn
    have hnk : 0 < n-k := Nat.sub_pos_of_lt hkn
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> positivity
  unfold marginal condMean
  trans expect (crMass n k) (fun z => if z i=b then coMembers i z else 0) /
    prob (crMass n k) (fun z => z i=b)
  · apply congrArg (fun num : ℝ => num / prob (crMass n k) (fun z => z i=b))
    apply congrArg (expect (crMass n k))
    funext z
    split_ifs <;> rfl
  · rw [he, expect_event_constant (crMass n k) (fun z => z i=b) ((k : ℝ)-bit b)]
    exact mul_div_cancel_left₀ _ hpn

/-- T2, the entire mathematical repair (a)–(f). Arbitrary local potential
outcomes are allowed; the Bernoulli and CR marginal targets are distinct.
The uniform first-stage identity applies separately to each saturation;
linearity then gives direct, indirect, total and overall contrasts. -/
theorem marginal_estimator_correction :
    (∀ n : ℕ, 0 < n → ∀ p : ℝ, 0 < p → p < 1 →
      ∀ y : Fin n → Assignment n → ℝ, ∀ b : Bool,
      (∀ i, expect (bernoulli p) (fun z => if z i = b then y i z else 0) =
        (if b then p else 1-p) * marginal (bernoulli p) y i b) ∧
      expect (bernoulli p) (groupHT p y b) = mean (fun i => marginal (bernoulli p) y i b)) ∧
    (∀ G C : ℕ, 0 < C → C ≤ G → ∀ n : Fin G → ℕ, (∀ g, 0 < n g) →
      ∀ q : (g : Fin G) → Assignment (n g) → ℝ,
      (∀ g z, 0 ≤ q g z) → (∀ g, ∑ z, q g z = 1) →
      ∀ X : (g : Fin G) → Assignment (n g) → ℝ,
      expect (selectedLaw n C q) (selectedMean C X) = mean (fun g => expect (q g) (X g))) ∧
    (∀ n k : ℕ, 0 < k → k < n → ∀ y : Fin n → Assignment n → ℝ, ∀ b : Bool,
      expect (crMass n k) (armMean y b) = mean (fun i => marginal (crMass n k) y i b)) ∧
    (∀ k : Fin 4, 0 < k.val →
      (∀ i : Fin 4, marginal (crMass 4 k.val) coMembers i true = (k.val : ℝ)-1 ∧
        marginal (crMass 4 k.val) coMembers i false = (k.val : ℝ)) ∧
      mean (fun i : Fin 4 => marginal (crMass 4 k.val) coMembers i true) -
        mean (fun i : Fin 4 => marginal (crMass 4 k.val) coMembers i false) = -1 ∧
      mean (fun i : Fin 4 => marginal (bernoulli ((k.val : ℝ)/4)) coMembers i true) -
        mean (fun i : Fin 4 => marginal (bernoulli ((k.val : ℝ)/4)) coMembers i false) = 0) ∧
    (∀ n : ℕ, 0 < n → ∀ q : Design (Assignment n), ∀ y : Fin n → Assignment n → ℝ,
      expect q.mass (groupOverall y) = mean (fun i => expect q.mass (y i))) ∧
    (∀ p : ℝ, 0 < p → p < 1 →
      expect (bernoulli p) (groupHT p (coMembers (n := 4)) true) = 3*p ∧
      expect (bernoulli p) (groupHT p (coMembers (n := 4)) false) = 3*p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn p hp hp1 y b
    exact bernoulli_group_ht_unbiased hn p hp hp1 y b
  · intro G C hC hCG n hn q hq hqt X
    exact selected_mean_expect hC hCG n q hqt X
  · intro n k hk hkn y b
    exact cr_group_arm_unbiased hk hkn y b
  · intro k hk
    have hm : k.val < 4 := k.isLt
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simpa [bit] using And.intro (cr_co_members_marginal hk hm i true)
        (cr_co_members_marginal hk hm i false)
    · simp_rw [cr_co_members_marginal hk hm]
      norm_num [mean, bit, Fin.sum_univ_succ]
      ring
    · have hp : 0 < (k.val : ℝ)/4 := by positivity
      have hp1 : (k.val : ℝ)/4 < 1 := by
        have hkR : (k.val : ℝ) < 4 := by exact_mod_cast hm
        linarith
      simp [co_members_marginal_four _ hp hp1]
  · intro n hn q y
    unfold groupOverall mean
    rw [expect_div, expect_sum]
  · intro p hp hp1
    exact ⟨(co_members_group_ht_expectation p hp hp1).1,
      (co_members_group_ht_expectation p hp hp1).2.1⟩

/-- T2(e), p. 310: all-unit group means are unconditionally unbiased for
the overall group marginal mean for every finite assignment law. -/
theorem overall_group_unbiased {n : ℕ} (hn : 0 < n) (q : Design (Assignment n))
    (y : Fin n → Assignment n → ℝ) :
    expect q.mass (groupOverall y) = mean (fun i => expect q.mass (y i)) := by
  unfold groupOverall mean
  rw [expect_div, expect_sum]

/-- Within-population variance with divisor |S|−1; meaningful as a sample
variance only for |S|≥2 (p. 310, T3–T4). -/
def rawSampleVar {I : Type*} (S : Finset I) (x : I → ℝ) : ℝ :=
  (∑ i ∈ S, (x i - average S x)^2) / ((S.card : ℝ)-1)

/-- Required arm sample variance, with the mathematical domain enforced.
For zero or one observation this is `none`, matching the corrected NA. -/
def sampleVar {I : Type*} (S : Finset I) (x : I → ℝ) : Option ℝ :=
  if 2 ≤ S.card then some (rawSampleVar S x) else none

/-- Finite-population variance with divisor n_g−1 (T4(a)). -/
def popVar {I : Type*} [Fintype I] (x : I → ℝ) : ℝ := rawSampleVar univ x

/-- Treated set in a group, as in the fixed-count design of p. 310. -/
def treatedSet {n : ℕ} (z : Assignment n) : Finset (Fin n) := univ.filter (fun i => z i = true)

/-- Fixed-count direct effect estimate D_g, p. 310. -/
def directGroup {n : ℕ} (a b : Fin n → ℝ) (z : Assignment n) : ℝ :=
  average (treatedSet z) a - average (univ \ treatedSet z) b

/-- The package's singleton-drop quantity in T3: sample
variance/arm size is retained only for arms with at least two units. -/
def droppedWithin {n : ℕ} (a b : Fin n → ℝ) (z : Assignment n) : ℝ :=
  (if 2 ≤ (treatedSet z).card then rawSampleVar (treatedSet z) a / (treatedSet z).card else 0) +
  (if 2 ≤ (univ \ treatedSet z).card then
    rawSampleVar (univ \ treatedSet z) b / (univ \ treatedSet z).card else 0)

/-- Direct-effect variance formula computed by the package, p. 311,
T3–T4. Its within-arm terms implement the singleton drop;
on the repaired domain they equal both required sample-variance terms. -/
def directVarianceEstimate {G : ℕ} {n : Fin G → ℕ} (C : ℕ)
    (a b : (g : Fin G) → Fin (n g) → ℝ)
    (w : Finset (Fin G) × GroupAssignments n) : ℝ :=
  ((1 - (C : ℝ)/G)/C) * rawSampleVar w.1 (fun g => directGroup (a g) (b g) (w.2 g)) +
    (∑ g ∈ w.1, droppedWithin (a g) (b g) (w.2 g)) / ((C : ℝ)*G)

/-- A uniform average of a statistic constant on its nonempty support
equals that constant (finite design algebra for pp. 292 and 310). -/
theorem average_constant_on {I : Type*} (S : Finset I) (hS : 0 < S.card)
    (X : I → ℝ) (c : ℝ) (hX : ∀ i ∈ S, X i=c) : average S X=c := by
  unfold average
  rw [Finset.sum_congr rfl hX]
  simp [ne_of_gt (Nat.cast_pos.mpr hS)]

/-- T4's repair of the p. 311 variance output: the formula is defined
only with at least two selected groups and at least two observations in
each required arm. `none` is NA, so an undefined arm is propagated. -/
def requiredDirectVariance {G : ℕ} {n : Fin G → ℕ} (C : ℕ)
    (a b : (g : Fin G) → Fin (n g) → ℝ)
    (w : Finset (Fin G) × GroupAssignments n) : Option ℝ :=
  if 2 ≤ C ∧ w.1.card=C ∧ ∀ g ∈ w.1,
    2 ≤ (treatedSet (w.2 g)).card ∧ 2 ≤ (univ \ treatedSet (w.2 g)).card
  then some (directVarianceEstimate C a b w) else none

/-- T4's corrected toy output: every assignment on the six-group,
three-unit fixed-count support has a required singleton arm, so the
repaired direct variance is undefined for either saturation, for all
outcome values. This conclusion needs no original random baseline data. -/
theorem toy_required_direct_variance_undefined (m : ℕ) (hm : m ∈ ({1,2} : Finset ℕ))
    (a b : Fin 6 → Fin 3 → ℝ) (H : Finset (Fin 6)) (hH : H ∈ firstStageSets 6 3)
    (w : Fin 6 → Assignment 3) (hw : ∀ g ∈ H, w g ∈ fixedAssignments 3 m) :
    requiredDirectVariance (n := fun _ => 3) 3 a b (H,w)=none := by
  classical
  have hc : H.card=3 := (Finset.mem_powersetCard.mp hH).2
  obtain ⟨g, hg⟩ := Finset.card_pos.mp (show 0 < H.card by omega)
  have ht : (treatedSet (w g)).card=m := (Finset.mem_filter.mp (hw g hg)).2
  have hz : (univ \ treatedSet (w g)).card=3-m := by
    simp [Finset.card_sdiff_of_subset (Finset.subset_univ _), ht]
  have hbad : ¬(∀ g ∈ H, 2 ≤ (treatedSet (w g)).card ∧ 2 ≤ (univ \ treatedSet (w g)).card) := by
    intro hh
    have h := hh g hg
    rw [ht, hz] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  simp [requiredDirectVariance, hbad]

/-- T4: each finite-population variance (divisor n−1) is nonnegative
on the corrected population-size domain. -/
theorem pop_var_nonnegative {I : Type*} [Fintype I] (hI : 2 ≤ Fintype.card I)
    (x : I → ℝ) : 0 ≤ popVar x := by
  unfold popVar rawSampleVar
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i hi => sq_nonneg _)
  · simp only [Finset.card_univ]
    exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ Fintype.card I by omega))

/-- T4(c): zero finite-population variance is equivalent to the schedule
being constant across all units. This proves the finite zero-variance
criterion used by the correction's equality-under-additivity clause. -/
theorem pop_var_zero_iff_constant {I : Type*} [Fintype I] (hI : 2 ≤ Fintype.card I)
    (x : I → ℝ) : popVar x=0 ↔ ∀ i j, x i=x j := by
  classical
  have hd : ((Fintype.card I : ℕ) : ℝ)-1 ≠ 0 := by
    have h : (2 : ℝ) ≤ Fintype.card I := by exact_mod_cast hI
    linarith
  constructor
  · intro hz
    unfold popVar rawSampleVar at hz
    simp only [Finset.card_univ] at hz
    have hs : (∑ i : I, (x i-average univ x)^2)=0 :=
      (div_eq_zero_iff.mp hz).resolve_right hd
    have hi : ∀ i : I, x i=average univ x := by
      intro i
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => sq_nonneg (x j-average univ x))).mp hs i (mem_univ i)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
    intro i j
    rw [hi i, hi j]
  · intro hx
    have hpos : 0 < (univ : Finset I).card := by simp; omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    have hm := average_constant_on univ hpos x (x i) (fun j hj => hx j i)
    unfold popVar rawSampleVar
    rw [hm]
    have hs : (∑ j : I, (x j-x i)^2)=0 := by
      simp only [show ∀ j, x j=x i from fun j => hx j i, sub_self, zero_pow (by norm_num : 2≠0), Finset.sum_const_zero]
    rw [hs]
    simp

/-- T4(d): scaling a baseline schedule scales its finite-population
variance by the square of the multiplier, including the chapter's
dilated multipliers. The divisor remains n−1. -/
theorem pop_var_scale {I : Type*} [Fintype I] (c : ℝ) (x : I → ℝ) :
    popVar (fun i => c*x i)=c^2*popVar x := by
  have hm : average (univ : Finset I) (fun i => c*x i)=c*average univ x := by
    simp [average, ← Finset.mul_sum, mul_div_assoc]
  have hs : ∀ i : I, (c*x i-c*average univ x)^2=c^2*(x i-average univ x)^2 := by
    intro i; ring
  simp only [popVar, rawSampleVar, hm, hs, ← Finset.mul_sum, mul_div_assoc]

/-- Finite-set summation commutes with finite design expectation,
including the selected subsets of groups in p. 310. -/
theorem expect_finset_sum {Ω I : Type*} [Fintype Ω] (p : Ω → ℝ)
    (S : Finset I) (X : I → Ω → ℝ) :
    expect p (fun w => ∑ i ∈ S, X i w) = ∑ i ∈ S, expect p (X i) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- T3–T4: the centered sum of independent, identically distributed
group statistics has second moment |S| times the individual variance. -/
theorem independent_centered_sum {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] (q : Ω → ℝ) (hq : ∑ w, q w=1) (X : Ω → ℝ) (S : Finset I) :
    expect (fun w : I → Ω => ∏ g, q (w g))
      (fun w => (∑ g ∈ S, (X (w g)-expect q X))^2) = S.card * variance q X := by
  classical
  let Z := fun w => X w-expect q X
  have hz : expect q Z=0 := by
    simp [Z, expect, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq]
  have hp (g h : I) : expect (fun w : I → Ω => ∏ j, q (w j))
      (fun w => Z (w g)*Z (w h)) = if g=h then variance q X else 0 := by
    by_cases he : g=h
    · subst h
      simpa [variance, Z, pow_two] using
        independent_coordinate_expect (fun _ : I => q) (fun _ => hq) g
          (fun w => (X w-expect q X)*(X w-expect q X))
    · rw [independent_pair_expect q hq g h he, hz]
      simp [he]
  have hpoly (w : I → Ω) : (∑ g ∈ S, Z (w g))^2 =
      ∑ g ∈ S, ∑ h ∈ S, Z (w g)*Z (w h) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  change expect (fun w : I → Ω => ∏ g, q (w g)) (fun w => (∑ g ∈ S, Z (w g))^2) = _
  simp_rw [hpoly]
  rw [expect_finset_sum]
  simp_rw [expect_finset_sum, hp]
  have hs : ∀ g ∈ S, (∑ h ∈ S, if g=h then variance q X else 0) = variance q X := by
    intro g hg
    simp [Finset.sum_ite_eq', hg]
  rw [Finset.sum_congr rfl hs]
  simp

/-- The sample sum of squares can be centered at an arbitrary fixed μ.
This exact algebraic identity underlies the finite p. 310 variance proof. -/
theorem raw_sample_variance_centered {I : Type*} (S : Finset I) (hS : 0 < S.card)
    (X : I → ℝ) (μ : ℝ) :
    rawSampleVar S X =
      ((∑ g ∈ S, (X g-μ)^2) - S.card*(average S X-μ)^2)/((S.card : ℝ)-1) := by
  have hn : (S.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hS)
  have hs : (∑ g ∈ S, (X g-μ)) = S.card*(average S X-μ) := by
    simp [average, Finset.sum_sub_distrib] <;> field_simp [hn] <;> ring
  have hp : (∑ g ∈ S, (X g-average S X)^2) =
      (∑ g ∈ S, (X g-μ)^2) - S.card*(average S X-μ)^2 := by
    calc
      _ = ∑ g ∈ S, ((X g-μ)^2 - 2*(average S X-μ)*(X g-μ) + (average S X-μ)^2) := by
        apply Finset.sum_congr rfl
        intro g hg
        ring
      _ = (∑ g ∈ S, (X g-μ)^2) -
          2*(average S X-μ)*(∑ g ∈ S, (X g-μ)) + S.card*(average S X-μ)^2 := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = _ := by rw [hs]; ring
  exact congrArg (fun t : ℝ => t/((S.card : ℝ)-1)) hp

/-- T3: the sample mean of C independently randomized identical groups
has its marginal mean and variance V_g/C, using the actual product law. -/
theorem independent_average_moments {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] (q : Ω → ℝ) (hq : ∑ w, q w=1) (X : Ω → ℝ)
    (S : Finset I) (hS : 0 < S.card) :
    expect (fun w : I → Ω => ∏ g, q (w g)) (fun w => average S (fun g => X (w g))) = expect q X ∧
    variance (fun w : I → Ω => ∏ g, q (w g)) (fun w => average S (fun g => X (w g))) =
      variance q X / S.card := by
  classical
  have hn : (S.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hS)
  have hm : expect (fun w : I → Ω => ∏ g, q (w g))
      (fun w => average S (fun g => X (w g))) = expect q X := by
    unfold average
    rw [expect_div, expect_finset_sum]
    simp_rw [independent_coordinate_expect (fun _ : I => q) (fun _ => hq) _ X]
    simp [hn]
  refine ⟨hm, ?_⟩
  unfold variance
  rw [hm]
  have hf (w : I → Ω) : (average S (fun g => X (w g))-expect q X)^2 =
      (∑ g ∈ S, (X (w g)-expect q X))^2/(S.card : ℝ)^2 := by
    simp [average, Finset.sum_sub_distrib] <;> field_simp [hn] <;> ring
  simp_rw [hf]
  rw [expect_div, independent_centered_sum q hq X S]
  field_simp [hn] <;> rfl

/-- T3: the sample variance across C≥2 independently randomized
identical groups has expectation equal to the true within-group variance. -/
theorem independent_sample_variance {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] (q : Ω → ℝ) (hq : ∑ w, q w=1) (X : Ω → ℝ)
    (S : Finset I) (hS : 2 ≤ S.card) :
    expect (fun w : I → Ω => ∏ g, q (w g))
      (fun w => rawSampleVar S (fun g => X (w g))) = variance q X := by
  have hpos : 0 < S.card := lt_of_lt_of_le (by norm_num : 0<2) hS
  have hn : (S.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hpos)
  have hd : (S.card : ℝ)-1 ≠ 0 := by exact_mod_cast (show (S.card : ℤ)-1 ≠ 0 by omega)
  simp_rw [raw_sample_variance_centered S hpos _ (expect q X)]
  rw [expect_div, expect_sub]
  have hs : expect (fun w : I → Ω => ∏ g, q (w g))
      (fun w => ∑ g ∈ S, (X (w g)-expect q X)^2) = S.card*variance q X := by
    rw [expect_finset_sum]
    simp_rw [independent_coordinate_expect (fun _ : I => q) (fun _ => hq) _
      (fun w => (X w-expect q X)^2)]
    simp [variance]
  have hm := independent_average_moments q hq X S hpos
  have hv : expect (fun w : I → Ω => ∏ g, q (w g))
      (fun w => S.card*(average S (fun g => X (w g))-expect q X)^2) = variance q X := by
    simp_rw [mul_comm (S.card : ℝ)]
    rw [expect_mul_const]
    have hvar : expect (fun w : I → Ω => ∏ g, q (w g))
        (fun w => (average S (fun g => X (w g))-expect q X)^2) = variance q X/S.card := by
      simpa only [variance, hm.1] using hm.2
    rw [hvar]
    exact div_mul_cancel₀ _ hn
  rw [hs, hv]
  field_simp [hn, hd] <;> ring

/-- T3's six-group calculation factors through independent identical
group moments. This finite lemma applies to any G,C with 2≤C≤G and any
normalized local law; it derives the true mean, variance, and expectation
of the actual singleton-drop variance formula from its local statistics. -/
theorem identical_group_selected_moments {G C n : ℕ} (hC : 2 ≤ C) (hCG : C ≤ G)
    (q : Assignment n → ℝ) (hq : ∑ z, q z=1) (a b : Fin n → ℝ) :
    let ns : Fin G → ℕ := fun _ => n
    let law := selectedLaw ns C (fun _ => q)
    let X := directGroup a b
    let point := selectedMean (n := ns) C (fun _ => X)
    expect law point = expect q X ∧
    variance law point = variance q X/C ∧
    expect law (directVarianceEstimate (n := ns) C (fun _ => a) (fun _ => b)) =
      ((1-(C : ℝ)/G)/C)*variance q X + expect q (droppedWithin a b)/G := by
  classical
  dsimp only
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num : 0<2) hC
  have hGp : 0 < G := lt_of_lt_of_le hCp hCG
  have hCn : (C : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hCp)
  have hGn : (G : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hGp)
  have hF : 0 < (firstStageSets G C).card := by
    exact Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr (by simpa using hCG))
  have hcard : ∀ H ∈ firstStageSets G C, H.card=C := by
    intro H hH
    exact (Finset.mem_powersetCard.mp hH).2
  have hm : expect (selectedLaw (fun _ : Fin G => n) C (fun _ => q))
      (selectedMean C (fun _ => directGroup a b)) = expect q (directGroup a b) := by
    rw [selected_mean_expect hCp hCG _ _ (fun _ => hq)]
    simp [mean, ne_of_gt (Nat.cast_pos.mpr hGp)]
  refine ⟨hm, ?_, ?_⟩
  · unfold variance
    rw [hm, selected_expect_average]
    apply average_constant_on _ hF
    intro H hH
    have hc := hcard H hH
    have hpos : 0 < H.card := by omega
    have hi := independent_average_moments (I := Fin G) q hq (directGroup a b) H hpos
    have hv := hi.2
    unfold variance at hv
    rw [hi.1] at hv
    simpa only [selectedMean, average, hc] using hv
  · rw [selected_expect_average]
    apply average_constant_on _ hF
    intro H hH
    have hc := hcard H hH
    change expect (fun w : Fin G → Assignment n => ∏ g, q (w g))
      (fun w => ((1-(C : ℝ)/G)/C)*rawSampleVar H (fun g => directGroup a b (w g)) +
        (∑ g ∈ H, droppedWithin a b (w g))/((C : ℝ)*G)) = _
    rw [expect_add]
    have hs : expect (fun w : Fin G → Assignment n => ∏ g, q (w g))
        (fun w => ((1-(C : ℝ)/G)/C)*rawSampleVar H (fun g => directGroup a b (w g))) =
        ((1-(C : ℝ)/G)/C)*variance q (directGroup a b) := by
      simp_rw [mul_comm ((1-(C : ℝ)/G)/C)]
      rw [expect_mul_const, independent_sample_variance q hq _ H (by omega)] <;> ring
    rw [hs, expect_div, expect_finset_sum]
    simp_rw [independent_coordinate_expect (fun _ : Fin G => q) (fun _ => hq) _ (droppedWithin a b)]
    simp only [Finset.sum_const, nsmul_eq_mul, hc]
    field_simp [hCn, hGn] <;> ring

/-- T3(ii),(iv): actual three-unit CR group moments for the additive
baseline (1,2,3): E(D_g)=1, Var(D_g)=3/2 and E(Bhat_g)=1/2,
for either singleton arm. These are finite lemmas for the six-group target. -/
theorem singleton_group_finite_moments :
    let x : Fin 3 → ℝ := fun i => (i.val : ℝ)+1
    ∀ m ∈ ({1,2} : Finset ℕ),
      expect (crMass 3 m) (directGroup (fun i => x i+1) x)=1 ∧
      variance (crMass 3 m) (directGroup (fun i => x i+1) x)=3/2 ∧
      expect (crMass 3 m) (droppedWithin (fun i => x i+1) x)=1/2 := by
  dsimp only
  intro m hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl | rfl <;>
    simp only [variance,cr_expect_average,fixed_three_supports.1,fixed_three_supports.2] <;>
    norm_num [average,directGroup,droppedWithin,rawSampleVar,treatedSet,
      Fin.univ_succ,Fin.sum_univ_succ,Finset.filter_insert,Finset.filter_singleton,
      Finset.sdiff_singleton_eq_erase,Finset.sdiff_insert,Finset.erase_insert,
      Finset.erase_insert_of_ne]

/-- T3's fixed-count local moments for affine baseline schedules in a
three-unit group, x=(1,2,3). The exact three-assignment supports give the
mean, direct variance and retained within-arm term for counts two and one. -/
theorem three_unit_affine_moments (α β u v : ℝ) :
    let x : Fin 3 → ℝ := fun i => (i.val : ℝ)+1
    let a := fun i => α*x i+u
    let b := fun i => β*x i+v
    expect (crMass 3 2) (directGroup a b)=2*α+u-2*β-v ∧
    variance (crMass 3 2) (directGroup a b)=(2/3)*(α/2+β)^2 ∧
    expect (crMass 3 2) (droppedWithin a b)=α^2/2 ∧
    expect (crMass 3 1) (directGroup a b)=2*α+u-2*β-v ∧
    variance (crMass 3 1) (directGroup a b)=(2/3)*(α+β/2)^2 ∧
    expect (crMass 3 1) (droppedWithin a b)=β^2/2 := by
  dsimp only
  simp only [variance, cr_expect_average, fixed_three_supports.1, fixed_three_supports.2]
  norm_num [average, directGroup, droppedWithin, rawSampleVar, treatedSet,
    Fin.univ_succ, Fin.sum_univ_succ, Finset.filter_insert, Finset.filter_singleton,
    Finset.sdiff_singleton_eq_erase, Finset.sdiff_insert, Finset.erase_insert,
    Finset.erase_insert_of_ne]
  all_goals (repeat' constructor <;> try ring <;> simp)

/-- T3, full explicit six-group singleton-arm counterexample (p. 310 toy
design): additive, dilated and upward-bias schedules are all stated. -/
theorem singleton_variance_counterexample :
    let n : Fin 6 → ℕ := fun _ => 3
    let law (m : ℕ) := selectedLaw n 3 (fun _ => crMass 3 m)
    let x : Fin 3 → ℝ := fun i => (i.val : ℝ)+1
    let point (a b : Fin 3 → ℝ) := selectedMean 3 (fun _ => directGroup a b)
    let vest (a b : Fin 3 → ℝ) := directVarianceEstimate 3 (fun _ => a) (fun _ => b)
    (∀ m ∈ ({1,2} : Finset ℕ),
      expect (law m) (point (fun i => x i+1) x) = 1 ∧
      variance (law m) (point (fun i => x i+1) x) = 1/2 ∧
      expect (law m) (vest (fun i => x i+1) x) = 1/3) ∧
    variance (law 2) (point (fun i => 2*x i) (fun i => (5/4)*x i)) = 9/8 ∧
    expect (law 2) (vest (fun i => 2*x i) (fun i => (5/4)*x i)) = 43/48 ∧
    variance (law 1) (point (fun i => (3/2)*x i) x) = 8/9 ∧
    expect (law 1) (vest (fun i => (3/2)*x i) x) = 19/36 ∧
    variance (law 2) (point x (fun _ => 0)) = 1/18 ∧
    expect (law 2) (vest x (fun _ => 0)) = 1/9 := by
  dsimp only
  let x : Fin 3 → ℝ := fun i => (i.val : ℝ)+1
  have hψ := (identical_group_selected_moments (G := 6) (C := 3)
    (by norm_num) (by norm_num) (crMass 3 2)
    (cr_mass_probability (by norm_num : 2≤3)).2
    (fun i => 2*x i) (fun i => (5/4)*x i)).2
  have hφ := (identical_group_selected_moments (G := 6) (C := 3)
    (by norm_num) (by norm_num) (crMass 3 1)
    (cr_mass_probability (by norm_num : 1≤3)).2
    (fun i => (3/2)*x i) x).2
  have hup := (identical_group_selected_moments (G := 6) (C := 3)
    (by norm_num) (by norm_num) (crMass 3 2)
    (cr_mass_probability (by norm_num : 2≤3)).2 x (fun _ => 0)).2
  have hp := three_unit_affine_moments 2 (5/4) 0 0
  have hf := three_unit_affine_moments (3/2) 1 0 0
  have hu := three_unit_affine_moments 1 0 0 0
  simp only [add_zero, one_mul, zero_mul] at hp hf hu
  rw [hp.2.1, hp.2.2.1] at hψ
  rw [hf.2.2.2.2.1, hf.2.2.2.2.2] at hφ
  rw [hu.2.1, hu.2.2.1] at hup
  norm_num at hψ hφ hup
  refine ⟨?_, hψ.1, hψ.2, hφ.1, hφ.2, hup.1, hup.2⟩
  intro m hm
  have hk : m ≤ 3 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hm; omega
  have hi := identical_group_selected_moments (G := 6) (C := 3)
    (by norm_num) (by norm_num) (crMass 3 m) (cr_mass_probability hk).2
    (fun i => x i+1) x
  have hl := singleton_group_finite_moments m hm
  dsimp only at hl hi
  rw [hl.1, hl.2.1, hl.2.2] at hi
  norm_num at hi
  exact hi

/-- T4(a): under any nonempty treated and control fixed-count arms,
the actual within-group direct estimator is unbiased for the group's
fixed potential-outcome mean difference, for arbitrary real schedules. -/
theorem direct_group_cr_unbiased {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (a b : Fin n → ℝ) :
    expect (crMass n k) (directGroup a b)=mean a-mean b := by
  classical
  have hm : ∀ (x : Fin n → ℝ) (v : Bool),
      expect (crMass n k) (armMean (fun i _ => x i) v)=mean x := by
    intro x v
    rw [cr_group_arm_unbiased hk hkn]
    apply congrArg mean
    funext i
    unfold marginal condMean
    dsimp only
    rw [@expect_event_constant (Assignment n) _ (crMass n k) (fun z => z i=v)
      (fun z => Classical.propDecidable (z i=v)) (x i)]
    have hp : prob (crMass n k) (fun z => z i=v) ≠ 0 := by
      rw [cr_arm_probability hk hkn]
      have hN : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (lt_trans hk hkn))
      have hK : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
      have hC : ((n-k : ℕ) : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (by omega))
      cases v
      · simpa using div_ne_zero hC hN
      · simpa using div_ne_zero hK hN
    field_simp [hp]
  have he : ∀ z : Assignment n, directGroup a b z =
      armMean (fun i _ => a i) true z-armMean (fun i _ => b i) false z := by
    intro z
    have h0 : univ \ treatedSet z=univ.filter (fun i => z i=false) := by
      ext i
      cases hz : z i <;> simp [treatedSet, hz]
    unfold directGroup
    rw [h0]
    unfold average armMean
    simp only [treatedSet, Finset.sum_filter]
    have hcount : ∀ v : Bool, (∑ i : Fin n, if z i=v then (1 : ℝ) else 0) =
        ((univ.filter (fun i => z i=v)).card : ℝ) := by
      intro v
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one,
        mul_zero, add_zero]
    rw [hcount true, hcount false]
  have hf : directGroup a b=(fun z =>
      armMean (fun i _ => a i) true z-armMean (fun i _ => b i) false z) := funext he
  rw [hf, expect_sub, hm, hm]

/-- T4(b): the uniform first-stage sample of groups and independent
within-group complete assignments give an unbiased direct contrast for
arbitrary group sizes and fixed real schedules. This is the exact mean
identity from the general correction; it assumes no variance formula. -/
theorem selected_direct_cr_unbiased {G C : ℕ} (hC : 0 < C) (hCG : C ≤ G)
    (n m : Fin G → ℕ) (hm : ∀ g, 0 < m g ∧ m g < n g)
    (a b : (g : Fin G) → Fin (n g) → ℝ) :
    expect (selectedLaw n C (fun g => crMass (n g) (m g)))
      (selectedMean C (fun g => directGroup (a g) (b g))) =
      mean (fun g => mean (a g)-mean (b g)) := by
  rw [selected_mean_expect hC hCG _ _
    (fun g => (cr_mass_probability (le_of_lt (hm g).2)).2)]
  congr 1
  funext g
  exact direct_group_cr_unbiased (hm g).1 (hm g).2 (a g) (b g)


/-- T4's domain correction: a one-observation arm has undefined sample
variance. This is why the three-unit toy cannot use the repaired formula. -/
theorem singleton_sample_variance_undefined {I : Type*} [DecidableEq I]
    (i : I) (x : I → ℝ) : sampleVar {i} x = none := by
  simp [sampleVar]

/-- Closed first-degree neighbourhood B_i={i}∪{j:A_ij=1}, as documented
for full-neighbourhood exposure (p. 305). -/
def neighborhood {n : ℕ} (A : Fin n → Fin n → Bool) (i : Fin n) : Finset (Fin n) :=
  insert i (univ.filter (fun j => A i j = true))

/-- s_i(z), the number treated in B_i (full-neighbourhood mapping). -/
def neighborhoodCount {n : ℕ} (A : Fin n → Fin n → Bool)
    (z : Assignment n) (i : Fin n) : ℕ :=
  ((neighborhood A i).filter (fun j => z j = true)).card

/-- Full-neighbourhood target events: all treated, all control (p. 305).
The erroneous package control event is s_i<b_i. -/
def allTreated {n : ℕ} (A : Fin n → Fin n → Bool) (z : Assignment n) (i : Fin n) : Prop :=
  neighborhoodCount A z i = (neighborhood A i).card
/-- "a unit and 100% of its first-degree neighbors are in the control condition" (full-neighbourhood package documentation; T6, p. 305 context). The repaired indicator is s_i=0. -/
def allControl {n : ℕ} (A : Fin n → Fin n → Bool) (z : Assignment n) (i : Fin n) : Prop :=
  neighborhoodCount A z i = 0
/-- "exposure<B_size" (mapping in T5 and T27, p. 305 context). This coded complement is deliberately kept distinct from the documented all-control condition. -/
def badAllControl {n : ℕ} (A : Fin n → Fin n → Bool) (z : Assignment n) (i : Fin n) : Prop :=
  neighborhoodCount A z i < (neighborhood A i).card

/-- HT contrast using the full-neighbourhood extreme events with exact
event probabilities (p. 297, p. 305). `correct` selects the repaired
control event; the other event is the package's complement of all treatment. -/
def fullHT {n : ℕ} (p : Assignment n → ℝ) (A : Fin n → Fin n → Bool)
    (Y : Fin n → Assignment n → ℝ) (correct : Bool) (z : Assignment n) : ℝ :=
  by classical exact mean (fun i =>
    (if allTreated A z i then Y i z / prob p (fun v => allTreated A v i) else 0) -
    (if (if correct then allControl A z i else badAllControl A z i) then
      Y i z / prob p (fun v => if correct then allControl A v i else badAllControl A v i) else 0))

/-- τ(1,0), the all-versus-none finite-population estimand (p. 300). -/
def allVsNone {n : ℕ} (Y : Fin n → Assignment n → ℝ) : ℝ :=
  mean (fun i => Y i (fun _ => true) - Y i (fun _ => false))

/-- Two adjacent units in the explicit counterexample (T5). -/
def edge2 (i j : Fin 2) : Bool := decide (i ≠ j)
/-- "y_i(z)=1+z_1+z_2" (T5(iii)): the explicit two-unit schedule. -/
def linear2 (_i : Fin 2) (z : Assignment 2) : ℝ := 1 + bit (z 0) + bit (z 1)
/-- "y_i(z)=1+2 I(z_1=z_2=1)" (T5(iv)): the threshold schedule illustrating that miscoding need not change the expectation. -/
def threshold2 (_i : Fin 2) (z : Assignment 2) : ℝ :=
  1 + 2 * (if z 0 = true ∧ z 1 = true then 1 else 0)

/-- T5(i)–(iv): the actual full-neighbourhood package predicate falsely labels
mixed assignments, with positive exact probabilities. For explicit linear
outcomes its HT expectation is 4/3 instead of 2; threshold outcomes show
why this defect alone does not refute Table 16.3's numerical results. -/
theorem full_neighborhood_counterexample :
    (∀ i : Fin 2, neighborhood edge2 i = univ) ∧
    (∀ i : Fin 2, badAllControl edge2 ![true,false] i ∧ ¬allControl edge2 ![true,false] i) ∧
    (∀ i : Fin 2, prob (bernoulli (1/2)) (fun z => allTreated edge2 z i) = 1/4 ∧
      prob (bernoulli (1/2)) (fun z => badAllControl edge2 z i) = 3/4 ∧
      prob (bernoulli (1/2)) (fun z => allControl edge2 z i) = 1/4) ∧
    allVsNone linear2 = 2 ∧
    fullHT (bernoulli (1/2)) edge2 linear2 false ![false,false] = -4/3 ∧
    fullHT (bernoulli (1/2)) edge2 linear2 false ![false,true] = -8/3 ∧
    fullHT (bernoulli (1/2)) edge2 linear2 false ![true,false] = -8/3 ∧
    fullHT (bernoulli (1/2)) edge2 linear2 false ![true,true] = 12 ∧
    expect (bernoulli (1/2)) (fullHT (bernoulli (1/2)) edge2 linear2 false) = 4/3 ∧
    expect (bernoulli (1/2)) (fullHT (bernoulli (1/2)) edge2 linear2 true) = 2 ∧
    allVsNone threshold2 = 2 ∧
    expect (bernoulli (1/2)) (fullHT (bernoulli (1/2)) edge2 threshold2 false) = 2 ∧
    expect (bernoulli (1/2)) (fullHT (bernoulli (1/2)) edge2 threshold2 true) = 2 := by
  norm_num [neighborhood, neighborhoodCount, edge2, badAllControl, allControl, allTreated,
    fullHT, allVsNone, linear2, threshold2, expect, prob, mean, bit, bernoulli,
    sum_tuple_succ, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.univ_succ, Finset.filter_insert, Finset.filter_singleton]
  decide

/-- T6(b): the repaired indicator s_i=0 says exactly that the unit and all
first-degree neighbours are untreated, for every finite graph and assignment. -/
theorem full_control_correct {n : ℕ} (A : Fin n → Fin n → Bool)
    (z : Assignment n) (i : Fin n) :
    allControl A z i ↔ ∀ j ∈ neighborhood A i, z j = false := by
  unfold allControl neighborhoodCount
  rw [Finset.card_filter_eq_zero_iff]
  simp only [Bool.not_eq_true]

/-- T6(a)–(c): the complete combinatorial repair, with the matrix orientation
explicitly checked using the symmetric closed-neighbourhood adjacency. -/
theorem full_neighborhood_events {n : ℕ} (A : Network n) (z : Assignment n) (i : Fin n) :
    (∑ j, bit (z j) * bit (if j = i then true else A.adj j i)) = neighborhoodCount A.adj z i ∧
    (∑ j, bit (if i = j then true else A.adj i j)) = (neighborhood A.adj i).card ∧
    neighborhoodCount A.adj z i ≤ (neighborhood A.adj i).card ∧
    (allTreated A.adj z i ↔ ∀ j ∈ neighborhood A.adj i, z j = true) ∧
    (allControl A.adj z i ↔ ∀ j ∈ neighborhood A.adj i, z j = false) ∧
    (badAllControl A.adj z i ↔ ∃ j ∈ neighborhood A.adj i, z j = false) ∧
    (allControl A.adj z i → badAllControl A.adj z i) ∧
    (badAllControl A.adj z i ∧ ¬allControl A.adj z i ↔
      0 < neighborhoodCount A.adj z i ∧ neighborhoodCount A.adj z i < (neighborhood A.adj i).card) ∧
    ((∀ v : Assignment n, allControl A.adj v i ↔ badAllControl A.adj v i) ↔
      (neighborhood A.adj i).card = 1) ∧
    ¬(allTreated A.adj z i ∧ allControl A.adj z i) ∧
    (allTreated A.adj z i ↔ ¬badAllControl A.adj z i) := by
  classical
  let B := neighborhood A.adj i
  have hi : i ∈ B := by simp [B,neighborhood]
  have hpos : 0 < B.card := Finset.card_pos.2 ⟨i,hi⟩
  have hmem (j : Fin n) : j ∈ B ↔ j=i ∨ A.adj i j=true := by
    simp [B,neighborhood]
  have hcol (j : Fin n) : bit (if j=i then true else A.adj j i) =
      if j ∈ B then 1 else 0 := by
    rw [A.symmetric j i]
    by_cases h : j=i <;> simp [bit,hmem,h]
  have hrow (j : Fin n) : bit (if i=j then true else A.adj i j) =
      if j ∈ B then 1 else 0 := by
    by_cases h : i=j
    · subst j; simp [bit,hmem]
    · simp [bit,hmem,h,Ne.symm h]
  have hcount : (∑ j, bit (z j)*bit (if j=i then true else A.adj j i)) =
      (neighborhoodCount A.adj z i : ℝ) := by
    simp_rw [hcol]
    have hx : (fun j => bit (z j)*(if j ∈ B then 1 else 0)) =
        (fun j => if j ∈ B then bit (z j) else 0) := by
      funext j; split_ifs <;> simp
    rw [hx]
    simp [neighborhoodCount,B,bit,Finset.sum_ite]
  have hsize : (∑ j, bit (if i=j then true else A.adj i j)) = (B.card : ℝ) := by
    simp_rw [hrow]
    simp
  have hle : neighborhoodCount A.adj z i ≤ B.card :=
    Finset.card_filter_le B _
  have hT : allTreated A.adj z i ↔ ∀ j ∈ B, z j=true :=
    Finset.card_filter_eq_iff
  have hC := full_control_correct A.adj z i
  have hbad (v : Assignment n) : badAllControl A.adj v i ↔ ∃ j ∈ B, v j=false := by
    have hvle := Finset.card_filter_le B (fun j => v j=true)
    change (B.filter (fun j => v j=true)).card < B.card ↔ _
    have hh : (B.filter (fun j => v j=true)).card < B.card ↔
        ¬(B.filter (fun j => v j=true)).card=B.card := by omega
    rw [hh,Finset.card_filter_eq_iff]
    push_neg
    simp only [Bool.not_eq_true]
  refine ⟨hcount,hsize,hle,hT,hC,hbad z,?_,?_,?_,?_,?_⟩
  · intro hc
    change neighborhoodCount A.adj z i=0 at hc
    change neighborhoodCount A.adj z i < B.card
    omega
  · change (neighborhoodCount A.adj z i < B.card ∧ ¬neighborhoodCount A.adj z i=0) ↔
      (0 < neighborhoodCount A.adj z i ∧ neighborhoodCount A.adj z i < B.card)
    omega
  · change (∀ v : Assignment n, allControl A.adj v i ↔ badAllControl A.adj v i) ↔ B.card=1
    constructor
    · intro hv
      let v : Assignment n := fun j => decide (j ≠ i)
      have hb : badAllControl A.adj v i := (hbad v).2 ⟨i,hi,by simp [v]⟩
      have hc := (full_control_correct A.adj v i).1 ((hv v).2 hb)
      have heq : B={i} := by
        apply Finset.ext
        intro j
        constructor
        · intro hj
          have hh := hc j hj
          have hji : j=i := by simpa [v] using hh
          exact Finset.mem_singleton.mpr hji
        · intro hj
          have hji : j=i := Finset.mem_singleton.mp hj
          simpa only [hji] using hi
      simp [heq]
    · intro hb v
      have hvle := Finset.card_filter_le B (fun j => v j=true)
      change (B.filter (fun j => v j=true)).card=0 ↔ (B.filter (fun j => v j=true)).card<B.card
      omega
  · change ¬(neighborhoodCount A.adj z i=B.card ∧ neighborhoodCount A.adj z i=0)
    omega
  · change neighborhoodCount A.adj z i=B.card ↔ ¬neighborhoodCount A.adj z i<B.card
    omega

/-- T6(e)–(f): corrected full-neighbourhood HT unbiasedness requires
constant extreme outcomes and positive exact probabilities, but leaves mixed
outcomes unrestricted. Complement coding estimates a conditional mixture. -/
theorem full_neighborhood_ht_correction {n : ℕ} (hn : 0 < n)
    (p : Design (Assignment n)) (A : Network n) (Y : Fin n → Assignment n → ℝ)
    (hT : ∀ i z, allTreated A.adj z i → Y i z = Y i (fun _ => true))
    (hC : ∀ i z, allControl A.adj z i → Y i z = Y i (fun _ => false))
    (pT : ∀ i, 0 < prob p.mass (fun z => allTreated A.adj z i))
    (pC : ∀ i, 0 < prob p.mass (fun z => allControl A.adj z i)) :
    expect p.mass (fullHT p.mass A.adj Y true) = allVsNone Y ∧
    expect p.mass (fullHT p.mass A.adj Y false) =
      mean (fun i => Y i (fun _ => true) - condMean p.mass (fun z => badAllControl A.adj z i) (Y i)) ∧
    ((∀ i z, badAllControl A.adj z i → Y i z = Y i (fun _ => false)) →
      expect p.mass (fullHT p.mass A.adj Y false) = allVsNone Y) := by
  classical
  have ht : ∀ i, expect p.mass (fun z => if allTreated A.adj z i then
      Y i z/prob p.mass (fun v => allTreated A.adj v i) else 0) = Y i (fun _ => true) :=
    fun i => event_constant_ht p.mass _ (Y i) _ (hT i) (pT i)
  have hc : ∀ i, expect p.mass (fun z => if allControl A.adj z i then
      Y i z/prob p.mass (fun v => allControl A.adj v i) else 0) = Y i (fun _ => false) :=
    fun i => event_constant_ht p.mass _ (Y i) _ (hC i) (pC i)
  have hcomp : expect p.mass (fullHT p.mass A.adj Y false) =
      mean (fun i => Y i (fun _ => true) - condMean p.mass
        (fun z => badAllControl A.adj z i) (Y i)) := by
    unfold fullHT
    rw [expect_mean]
    simp only [Bool.false_eq_true,ite_false,expect_sub, ht, event_ht_conditional]
  refine ⟨?_, hcomp, ?_⟩
  · unfold fullHT
    rw [expect_mean]
    simp only [ite_true,expect_sub, ht, hc, allVsNone]
  · intro hthreshold
    have hb : ∀ i, 0 < prob p.mass (fun z => badAllControl A.adj z i) := by
      intro i
      have hsubset : ∀ z, allControl A.adj z i → badAllControl A.adj z i := by
        intro z hz
        have hne : (neighborhood A.adj i).Nonempty := ⟨i, by simp [neighborhood]⟩
        exact lt_of_eq_of_lt hz (Finset.card_pos.mpr hne)
      have hle : prob p.mass (fun z => allControl A.adj z i) ≤
          prob p.mass (fun z => badAllControl A.adj z i) := by
        unfold prob expect
        apply Finset.sum_le_sum
        intro z hz
        by_cases h : allControl A.adj z i
        · simp [h, hsubset z h]
        · simp [h]; split_ifs <;> simp [p.nonneg z]
      exact lt_of_lt_of_le (pC i) hle
    have he : ∀ i, condMean p.mass (fun z => badAllControl A.adj z i) (Y i) =
        Y i (fun _ => false) := by
      intro i
      rw [← event_ht_conditional]
      exact event_constant_ht p.mass _ (Y i) _ (hthreshold i) (hb i)
    simpa only [he, allVsNone] using hcomp

/-- R's column-major strict triangle order (T7). Coordinates are
zero based; list order is by column then row, exactly as R indexes cells. -/
def upperCells (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap (fun j => (List.range n).filterMap
    (fun i => if i < j then some (i,j) else none))
/-- "R lists the selected cells ... column by column" (T7 operation): strict lower-triangle cells in the actual storage order. -/
def lowerCells (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap (fun j => (List.range n).filterMap
    (fun i => if j < i then some (i,j) else none))

/-- Literal faulty lower-triangle copy: kth lower cell receives kth upper
cell. It keeps the upper triangle and diagonal unchanged (T7). -/
def faultyCopy (n : ℕ) (M : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if j < i then
    let cell := (upperCells n)[(lowerCells n).idxOf (i,j)]?.getD (0,0)
    M cell.1 cell.2
  else M i j

/-- T9(a), corrected transpose copy: each lower cell receives its actual transpose. -/
def correctedCopy (M : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if j < i then M j i else M i j

/-- T7's one-edge four-vertex witness. -/
def singleEdge4 (i j : ℕ) : ℝ :=
  if (i=0 ∧ j=3) ∨ (i=3 ∧ j=0) then 1 else 0

/-- T7(ii): a symmetric zero-diagonal binary adjacency is made asymmetric
even at zero requested modification probability; a true entry is removed
and a spurious entry is added. This is a concrete witness. -/
theorem faulty_copy_counterexample :
    (∀ i j, singleEdge4 i j = singleEdge4 j i) ∧
    (∀ i, singleEdge4 i i = 0) ∧
    faultyCopy 4 singleEdge4 0 3 = 1 ∧
    faultyCopy 4 singleEdge4 3 0 = 0 ∧
    faultyCopy 4 singleEdge4 2 1 = 1 ∧
    faultyCopy 4 singleEdge4 1 2 = 0 := by
  constructor
  · intro i j
    have h : ((i=0 ∧ j=3) ∨ (i=3 ∧ j=0)) ↔ ((j=0 ∧ i=3) ∨ (j=3 ∧ i=0)) := by tauto
    simp only [singleEdge4,h]
  constructor
  · intro i; simp [singleEdge4]; omega
  change (1 : ℝ)=1 ∧ (0 : ℝ)=0 ∧ (1 : ℝ)=1 ∧ (0 : ℝ)=0
  norm_num

/-- T9(a): the transposed copy is symmetric in every dimension, without
any assumption on the original matrix or on outcomes. -/
theorem corrected_copy_symmetric (M : ℕ → ℕ → ℝ) (i j : ℕ) :
    correctedCopy M i j = correctedCopy M j i := by
  unfold correctedCopy
  by_cases h : i=j
  · subst j; rfl
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · simp [hlt, Nat.not_lt_of_ge (le_of_lt hlt)]
    · simp [hgt, Nat.not_lt_of_ge (le_of_lt hgt)]

/-- The package multiplies z' M and therefore reads columns. -/
def matrixExposure {n : ℕ} (M : ℕ → ℕ → ℝ) (z : Assignment n) (i : Fin n) : Exposure :=
  if z i then
    if 0 < ∑ j, bit (z j) * M j.val i.val then .d11 else .d10
  else if 0 < ∑ j, bit (z j) * M j.val i.val then .d01 else .d00

/-- A four-vertex upper triangle with six binary entries, for T7's exact
64-case count. The input is symmetrized correctly before applying the defect. -/
def upperInput4 (u : Fin 6 → Bool) (i j : ℕ) : ℝ :=
  if i < j then bit (u ⟨(upperCells 4).idxOf (i,j) % 6, Nat.mod_lt _ (by decide)⟩)
  else if j < i then bit (u ⟨(upperCells 4).idxOf (j,i) % 6, Nat.mod_lt _ (by decide)⟩)
  else 0

/-- T7(i): in every dimension n≥4 the third strict upper cell is (1,2)
and the third strict lower cell is (3,0), in zero-based R storage order. -/
theorem third_triangle_cells (n : ℕ) (hn : 4 ≤ n) :
    (upperCells n)[2]? = some (1,2) ∧ (lowerCells n)[2]? = some (3,0) := by
  have hr (m : ℕ) (hm : m ≤ n) : List.range n =
      List.range m ++ (List.range (n-m)).map (m+·) := by
    simpa [Nat.add_sub_of_le hm] using (List.range_add (n := m) (m := n-m))
  have hrow (j : ℕ) (hj : j ∈ List.range 3) :
      (List.range n).filterMap (fun i => if i<j then some (i,j) else none) =
        (List.range 3).filterMap (fun i => if i<j then some (i,j) else none) := by
    rw [hr 3 (by omega), List.filterMap_append]
    have ht : ((List.range (n-3)).map (3+·)).filterMap
        (fun i => if i<j then some (i,j) else none) = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro i hi
      rcases List.mem_map.mp hi with ⟨k, hk, rfl⟩
      have hj' := List.mem_range.mp hj
      simp [show ¬3+k<j by omega]
    simp [ht]
  have hupper : ∃ L, upperCells n = [(0,1),(0,2),(1,2)] ++ L := by
    unfold upperCells
    rw [hr 3 (by omega), List.flatMap_append]
    have he := List.flatMap_congr hrow
    rw [hr 3 (by omega)] at he
    rw [he]
    exact ⟨_, rfl⟩
  have hzero : (List.range n).filterMap (fun i => if 0 < i then some (i,0) else none) =
      [(1,0),(2,0),(3,0)] ++
        ((List.range (n-4)).map (4+·)).filterMap (fun i => if 0 < i then some (i,0) else none) := by
    rw [hr 4 hn, List.filterMap_append]
    rfl
  have hlower : ∃ L, lowerCells n = [(1,0),(2,0),(3,0)] ++ L := by
    unfold lowerCells
    rw [hr 4 hn, List.flatMap_append]
    simp only [show List.range 4=[0,1,2,3] from rfl,
      List.flatMap_cons, List.flatMap_nil, List.nil_append]
    have hz := hzero
    rw [hr 4 hn] at hz
    simp only [show List.range 4=[0,1,2,3] from rfl] at hz
    rw [hz]
    simp only [List.append_assoc]
    exact ⟨_, rfl⟩
  rcases hupper with ⟨U, hU⟩
  rcases hlower with ⟨L, hL⟩
  rw [hU,hL]
  constructor <;> rfl

/-- T7(iii): the R copy on four vertices is asymmetric precisely when
the third and fourth upper entries differ. The other entries copy to
their own transpose, so this reduces the 64-input check to two bits. -/
theorem faulty_copy_asymmetric_iff (u : Fin 6 → Bool) :
    (∃ i j : Fin 4, faultyCopy 4 (upperInput4 u) i.val j.val ≠
      faultyCopy 4 (upperInput4 u) j.val i.val) ↔ u 2 ≠ u 3 := by
  have hs (hu : u 2=u 3) : ∀ i j : Fin 4,
      faultyCopy 4 (upperInput4 u) i.val j.val = faultyCopy 4 (upperInput4 u) j.val i.val := by
    have hU : upperCells 4 = [(0,1),(0,2),(1,2),(0,3),(1,3),(2,3)] := by decide
    have hL : lowerCells 4 = [(1,0),(2,0),(3,0),(2,1),(3,1),(3,2)] := by decide
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [faultyCopy, upperInput4, hU, hL, hu, List.idxOf_cons]
  constructor
  · rintro ⟨i,j,hij⟩ hu
    exact hij (hs hu i j)
  · intro hu
    have hb : bit (u 2) ≠ bit (u 3) := by
      intro h
      cases h2 : u 2 <;> cases h3 : u 3 <;> simp_all [bit]
    refine ⟨0,3,?_⟩
    change bit (u 3) ≠ bit (u 2)
    exact hb.symm

set_option maxRecDepth 4096 in
/-- T7(i)–(v), full source-semantics statement: column orders, the 32/64
asymmetry count, changed exposures, and the defect at every q<1. The
zero-probability invocation concerns the helpers. -/
theorem faulty_copy_full_counterexample :
    upperCells 4 = [(0,1),(0,2),(1,2),(0,3),(1,3),(2,3)] ∧
    lowerCells 4 = [(1,0),(2,0),(3,0),(2,1),(3,1),(3,2)] ∧
    (∀ n : ℕ, 4 ≤ n → (upperCells n)[2]? = some (1,2) ∧ (lowerCells n)[2]? = some (3,0)) ∧
    (∀ n : ℕ, n ≤ 3 → ∀ k : ℕ, k < (upperCells n).length →
      (lowerCells n)[k]? = ((upperCells n)[k]?).map (fun x => (x.2,x.1))) ∧
    (univ.filter (fun u : Fin 6 → Bool => ∃ i j : Fin 4,
      faultyCopy 4 (upperInput4 u) i.val j.val ≠ faultyCopy 4 (upperInput4 u) j.val i.val)).card = 32 ∧
    matrixExposure singleEdge4 ![false,false,false,true] 0 = .d01 ∧
    matrixExposure (faultyCopy 4 singleEdge4) ![false,false,false,true] 0 = .d00 ∧
    matrixExposure singleEdge4 ![false,false,true,false] 1 = .d00 ∧
    matrixExposure (faultyCopy 4 singleEdge4) ![false,false,true,false] 1 = .d01 ∧
    (∀ q : ℝ, 0 ≤ q → q < 1 →
      prob (fun b : Bool => if b then q else 1-q)
        (fun b => (fun i j => if b then 0 else faultyCopy 4 singleEdge4 i j) =
          faultyCopy 4 singleEdge4) = 1-q) := by
  have hU : upperCells 4 = [(0,1),(0,2),(1,2),(0,3),(1,3),(2,3)] := by decide
  have hL : lowerCells 4 = [(1,0),(2,0),(3,0),(2,1),(3,1),(3,2)] := by decide
  refine ⟨by decide, by decide, third_triangle_cells, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn k hk
    interval_cases n
    · change k<0 at hk; omega
    · change k<0 at hk; omega
    · change k<1 at hk
      have h : k=0 := by omega
      subst k
      rfl
    · change k<3 at hk
      interval_cases k <;> rfl
  · have he : (univ.filter (fun u : Fin 6 → Bool => ∃ i j : Fin 4,
        faultyCopy 4 (upperInput4 u) i.val j.val ≠ faultyCopy 4 (upperInput4 u) j.val i.val)) =
        univ.filter (fun u => u 2 ≠ u 3) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, faulty_copy_asymmetric_iff]
    rw [he]
    decide
  · norm_num [matrixExposure, singleEdge4, bit, Fin.sum_univ_succ, faultyCopy, hU, hL, List.idxOf_cons]
  · norm_num [matrixExposure, singleEdge4, bit, Fin.sum_univ_succ, faultyCopy, hU, hL, List.idxOf_cons]
  · norm_num [matrixExposure, singleEdge4, bit, Fin.sum_univ_succ, faultyCopy, hU, hL, List.idxOf_cons]
  · norm_num [matrixExposure, singleEdge4, bit, Fin.sum_univ_succ, faultyCopy, hU, hL, List.idxOf_cons]
  · intro q hq hq1
    have hz : (fun _ _ : ℕ => (0 : ℝ)) ≠ faultyCopy 4 singleEdge4 := by
      intro h
      have he := congrFun (congrFun h 0) 3
      change (0 : ℝ)=1 at he
      norm_num at he
    simp [prob, expect, Fintype.univ_bool, hz]

/-- T9(b): symmetrizing edited upper entries preserves deletion/addition
inequalities and restores A exactly if its upper entries were unchanged. -/
theorem corrected_copy_monotone (n : ℕ) (A U : ℕ → ℕ → ℝ)
    (hA : ∀ i j, A i j = A j i) (hdiag : ∀ i, A i i = 0)
    (hbin : ∀ i j, i < n → j < n → A i j = 0 ∨ A i j = 1)
    (hUdiag : ∀ i, U i i = 0)
    (hUbin : ∀ i j, i < j → j < n → U i j = 0 ∨ U i j = 1) :
    ((∀ i j, i < j → j < n → U i j ≤ A i j) →
      ∀ i j, i < n → j < n → 0 ≤ correctedCopy U i j ∧ correctedCopy U i j ≤ A i j) ∧
    ((∀ i j, i < j → j < n → A i j ≤ U i j) →
      ∀ i j, i < n → j < n → i ≠ j → A i j ≤ correctedCopy U i j ∧ correctedCopy U i j ≤ 1) ∧
    ((∀ i j, i < j → j < n → U i j = A i j) →
      ∀ i j, i < n → j < n → correctedCopy U i j = A i j) := by
  have hUb (i j : ℕ) (hij : i < j) (hj : j < n) : 0 ≤ U i j ∧ U i j ≤ 1 := by
    rcases hUbin i j hij hj with h | h <;> simp [h]
  refine ⟨?_,?_,?_⟩
  · intro h i j hi hj
    rcases lt_trichotomy i j with hij | heq | hji
    · simpa [correctedCopy,not_lt_of_ge hij.le] using
        And.intro (hUb i j hij hj).1 (h i j hij hj)
    · subst j
      simp [correctedCopy,hUdiag,hdiag]
    · rw [correctedCopy,if_pos hji,hA i j]
      exact ⟨(hUb j i hji hi).1,h j i hji hi⟩
  · intro h i j hi hj hne
    rcases lt_trichotomy i j with hij | heq | hji
    · simpa [correctedCopy,not_lt_of_ge hij.le] using
        And.intro (h i j hij hj) (hUb i j hij hj).2
    · exact False.elim (hne heq)
    · rw [correctedCopy,if_pos hji,hA i j]
      exact ⟨h j i hji hi,(hUb j i hji hi).2⟩
  · intro h i j hi hj
    rcases lt_trichotomy i j with hij | heq | hji
    · simpa [correctedCopy,not_lt_of_ge hij.le] using h i j hij hj
    · subst j
      simp [correctedCopy,hUdiag,hdiag]
    · rw [correctedCopy,if_pos hji,hA i j]
      exact h j i hji hi

/-- HT total with assignment-level observed outcomes supplied before the
event mask; essential for misspecified maps (p. 303, T9; T6's repair). -/
def htObserved {n : ℕ} (p : Assignment n → ℝ)
    (D : Assignment n → Fin n → Exposure) (Y : Fin n → Assignment n → ℝ)
    (d : Exposure) (z : Assignment n) : ℝ :=
  ∑ i, if D z i = d then Y i z / exposureProb p D i d else 0

/-- T9(c): deleting undirected ties can lose positive exposure but cannot
invent it. The four label inclusions hold on every assignment (p. 303). -/
theorem deletion_exposure_inclusions {n : ℕ} (T S : Network n)
    (hsub : ∀ i j, S.adj i j = true → T.adj i j = true) (z : Assignment n) (i : Fin n) :
    (exposure S.adj z i = .d01 → exposure T.adj z i = .d01) ∧
    (exposure S.adj z i = .d11 → exposure T.adj z i = .d11) ∧
    (exposure S.adj z i = .d00 → exposure T.adj z i = .d00 ∨ exposure T.adj z i = .d01) ∧
    (exposure S.adj z i = .d10 → exposure T.adj z i = .d10 ∨ exposure T.adj z i = .d11) := by
  unfold exposure
  by_cases hz : z i = true
  · have hz' : z i = true := hz
    by_cases hS : ∃ j, S.adj i j = true ∧ z j = true
    · obtain ⟨j,hj,hzj⟩ := hS
      have hT : ∃ j, T.adj i j = true ∧ z j = true := ⟨j,hsub i j hj,hzj⟩
      simp [hz', hT, show ∃ j, S.adj i j = true ∧ z j = true from ⟨j,hj,hzj⟩]
    · by_cases hT : ∃ j, T.adj i j = true ∧ z j = true <;> simp [hz',hS,hT]
  · have hz' : z i = false := Bool.eq_false_of_not_eq_true hz
    by_cases hS : ∃ j, S.adj i j = true ∧ z j = true
    · obtain ⟨j,hj,hzj⟩ := hS
      have hT : ∃ j, T.adj i j = true ∧ z j = true := ⟨j,hsub i j hj,hzj⟩
      simp [hz', hT, show ∃ j, S.adj i j = true ∧ z j = true from ⟨j,hj,hzj⟩]
    · by_cases hT : ∃ j, T.adj i j = true ∧ z j = true <;> simp [hz',hS,hT]

/-- T9(d): measured d00 is a conditional mixture, giving the exact HT
bias −(1/N)∑_i c_i[y_i(d01)−y_i(d00)]. This is an HT assertion;
it does not silently replace the expectation of a Hajek ratio by a ratio
of expectations. -/
theorem missing_ties_ht_bias {n : ℕ} (hn : 0 < n) (p : Design (Assignment n))
    (T S : Network n) (hsub : ∀ i j, S.adj i j = true → T.adj i j = true)
    (y : Fin n → Exposure → ℝ)
    (h0 : ∀ i, 0 < exposureProb p.mass (exposure S.adj) i .d00)
    (h1 : ∀ i, 0 < exposureProb p.mass (exposure S.adj) i .d01) :
    let Y := fun i z => y i (exposure T.adj z i)
    let M := fun d z => htObserved p.mass (exposure S.adj) Y d z / n
    let c := fun i => condMean p.mass (fun z => exposure S.adj z i = .d00)
      (fun z => if exposure T.adj z i = .d01 then 1 else 0)
    expect p.mass (M .d00) = mean (fun i => (1-c i)*y i .d00+c i*y i .d01) ∧
    expect p.mass (M .d01) = mean (fun i => y i .d01) ∧
    expect p.mass (fun z => M .d01 z-M .d00 z)-effect y .d01 .d00 =
      -mean (fun i => c i*(y i .d01-y i .d00)) ∧
    ((∀ i, y i .d00 ≤ y i .d01) →
      expect p.mass (fun z => M .d01 z-M .d00 z) ≤ effect y .d01 .d00) := by
  classical
  let Y := fun i z => y i (exposure T.adj z i)
  let M := fun d z => htObserved p.mass (exposure S.adj) Y d z/n
  let c := fun i => condMean p.mass (fun z => exposure S.adj z i=.d00)
    (fun z => if exposure T.adj z i=.d01 then 1 else 0)
  have hpoint (d : Exposure) : M d = fun z => mean (fun i =>
      if exposure S.adj z i=d then Y i z/exposureProb p.mass (exposure S.adj) i d else 0) := by
    funext z
    simp only [M,htObserved,mean,Fintype.card_fin]
  have hM0 : expect p.mass (M .d00) = mean (fun i => (1-c i)*y i .d00+c i*y i .d01) := by
    rw [hpoint,expect_mean]
    apply congrArg mean
    funext i
    rw [exposureProb,event_ht_conditional]
    apply event_binary_mixture p.mass _ _ (Y i) _ _ (h0 i)
    intro z hz
    rcases (deletion_exposure_inclusions T S hsub z i).2.2.1 hz with h | h
    · simp [Y,h]
    · simp [Y,h]
  have hM1 : expect p.mass (M .d01) = mean (fun i => y i .d01) := by
    rw [hpoint,expect_mean]
    apply congrArg mean
    funext i
    apply event_constant_ht p.mass _ (Y i) _ _ (h1 i)
    intro z hz
    simp only [Y,(deletion_exposure_inclusions T S hsub z i).1 hz]
  have hbias : expect p.mass (fun z => M .d01 z-M .d00 z)-effect y .d01 .d00 =
      -mean (fun i => c i*(y i .d01-y i .d00)) := by
    rw [expect_sub,hM1,hM0]
    unfold effect
    rw [← mean_sub,← mean_sub,← mean_sub,← mean_neg]
    apply congrArg mean
    funext i
    ring
  refine ⟨hM0,hM1,hbias,?_⟩
  intro hy
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    apply div_nonneg _ (le_of_lt (h0 i))
    unfold expect
    apply Finset.sum_nonneg
    intro z hz
    by_cases hs : exposure S.adj z i=.d00
    · by_cases ht : exposure T.adj z i=.d01 <;> simp [hs,ht,p.nonneg z]
    · simp [hs]
  have hm := mean_nonneg (fun i => c i*(y i .d01-y i .d00))
    (fun i => mul_nonneg (hc i) (sub_nonneg.mpr (hy i)))
  linarith

/-- The adjacency matrix printed on p. 295 (PDF p. 7), transcribed from
the page image. Used by T8 and T16; twenty undirected ties. -/
def printedAdj : Fin 10 → Fin 10 → Bool :=
  ![![false,true,true,false,true,false,false,false,false,false],
    ![true,false,true,true,false,false,false,false,false,true],
    ![true,true,false,true,true,true,false,false,true,false],
    ![false,true,true,false,true,true,true,false,false,false],
    ![true,false,true,true,false,true,false,true,false,false],
    ![false,false,true,true,true,false,false,false,false,false],
    ![false,false,false,true,false,false,false,true,true,false],
    ![false,false,false,false,true,false,true,false,true,true],
    ![false,false,true,false,false,false,true,true,false,true],
    ![false,true,false,false,false,false,false,true,true,false]]

/-- True undirected ties, each represented once (T8: uniform d-tie deletion). -/
def printedEdges : Finset (Fin 10 × Fin 10) :=
  univ.filter (fun e => e.1 < e.2 ∧ printedAdj e.1 e.2 = true)

/-- All measured networks obtained by deleting exactly d of the twenty
ties, uniformly and independently of the treated unit (T8). -/
def deletionMasks (d : ℕ) : Finset (Finset (Fin 10 × Fin 10)) := printedEdges.powersetCard d
/-- "randomly missing varying proportions of ties" (p. 303). T8's exact-d mask deletes both orientations of each selected undirected printed-network tie. -/
def deletedAdj (R : Finset (Fin 10 × Fin 10)) (i j : Fin 10) : Bool :=
  printedAdj i j && decide ((i,j) ∉ R ∧ (j,i) ∉ R)
/-- "number of direct ties" (p. 293): the remaining degree after the symmetric deletion mask in T8. -/
def measuredDegree (R : Finset (Fin 10 × Fin 10)) (i : Fin 10) : ℕ :=
  (univ.filter (fun j => deletedAdj R i j = true)).card

/-- T8's positive baseline schedule: b_2=5/2, all others 1. -/
def biasBaseline (i : Fin 10) : ℝ := if i=1 then 5/2 else 1

/-- Exact Hajek d01−d00 contrast with one uniformly treated unit t and
measured inverse-probability weights. The common factor ten cancels,
giving precisely the two ratios fixed in T8 (p. 299). -/
def deletionHajek (R : Finset (Fin 10 × Fin 10)) (t : Fin 10) : ℝ :=
  let S := univ.filter (fun i => deletedAdj R t i = true)
  let C := univ \ insert t S
  ((∑ i ∈ S, ((5/4)*biasBaseline i)/(measuredDegree R i)) /
    (∑ i ∈ S, 1/(measuredDegree R i : ℝ))) -
  ((∑ i ∈ C, biasBaseline i*(1+(if printedAdj t i then (1/4 : ℝ) else 0))/
      (9-(measuredDegree R i : ℝ))) /
    (∑ i ∈ C, 1/(9-(measuredDegree R i : ℝ))))

/-- β_d is the exact mean over 10·choose(20,d) equally likely cases minus
the true exposure contrast 23/80 (T8). -/
def deletionBias (d : ℕ) : ℝ := average (deletionMasks d) (fun R => mean (deletionHajek R)) - 23/80

/-- T8 zero-deletion certificate: the indirect-exposure cells when each
of the ten units is treated. This table is certified against the printed
graph, and is used only to keep rational arithmetic small. -/
def zeroDeletionCells : Fin 10 → Finset (Fin 10) :=
  ![{1,2,4},{0,2,3,9},{0,1,3,4,5,8},{1,2,4,5,6},{0,2,3,5,7},
    {2,3,4},{3,7,8},{4,6,8,9},{2,6,7,9},{1,7,8}]

/-- T8's no-exposure cells at zero deletion, a finite certificate of
the complement of the indirect-exposure cell and the treated unit. -/
def zeroDeletionControlCells : Fin 10 → Finset (Fin 10) :=
  ![{3,5,6,7,8,9},{4,5,6,7,8},{6,7,9},{0,7,8,9},{1,6,8,9},
    {0,1,6,7,8,9},{0,1,2,4,5,9},{0,1,2,3,5},{0,1,3,4,5},{0,2,3,4,5,6}]

/-- T8: the tabulated no-exposure cells are the actual complements. -/
theorem zero_deletion_control_certificate (t : Fin 10) :
    univ \ insert t (zeroDeletionCells t) = zeroDeletionControlCells t := by
  revert t
  decide

/-- T8: degree and exposure-cell certificates with no missing ties,
checked on the printed adjacency, with nonempty indirect and no-exposure
cells for every possible single treated unit. -/
theorem zero_deletion_graph_certificate :
    (∀ i : Fin 10, measuredDegree ∅ i = ![3,4,6,5,5,3,3,4,4,3] i) ∧
    (∀ t : Fin 10, univ.filter (fun i => deletedAdj ∅ t i=true) = zeroDeletionCells t) ∧
    (∀ t : Fin 10, (zeroDeletionCells t).Nonempty ∧
      (univ \ insert t (zeroDeletionCells t)).Nonempty) ∧
    (∀ t : Fin 10, ∀ i ∈ univ \ insert t (zeroDeletionCells t), printedAdj t i=false) := by
  decide

/-- T8(iv): the ten exact Hajek contrasts at zero missing ties, using
the actual true exposures, baseline schedule and unit-treatment design. -/
theorem zero_deletion_hajek_values (t : Fin 10) :
    deletionHajek ∅ t =
      ![(299/296 : ℝ),1/4,413/752,379/616,-7/44,-1/44,5/308,-5/268,-5/124,7/8] t := by
  classical
  have hS := zero_deletion_graph_certificate.2.1 t
  have hC : (∑ i ∈ univ \ insert t (zeroDeletionCells t),
      biasBaseline i*(1+(if printedAdj t i then (1/4 : ℝ) else 0))/(9-(measuredDegree ∅ i : ℝ))) =
      ∑ i ∈ univ \ insert t (zeroDeletionCells t),
        biasBaseline i/(9-(measuredDegree ∅ i : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [zero_deletion_graph_certificate.2.2.2 t i hi]
  unfold deletionHajek
  dsimp only
  rw [hS, hC]
  rw [zero_deletion_control_certificate]
  simp_rw [zero_deletion_graph_certificate.1]
  fin_cases t <;> norm_num [zeroDeletionCells, zeroDeletionControlCells, biasBaseline]

/-- T8(i),(iv): with the correctly measured printed graph, positive
baseline dilated outcomes and exact exposure probabilities, the indirect
Hajek contrast is biased. All ten ratios have nonempty exposure cells;
its exact bias is 890121037/44498644960, between 1/50 and 1/49. This is
the zero-deletion case of the monotonicity counterexample. -/
theorem zero_deletion_hajek_counterexample :
    printedEdges.card=20 ∧ mean biasBaseline/4=23/80 ∧
    (∀ i : Fin 10, 1 ≤ measuredDegree ∅ i ∧ measuredDegree ∅ i ≤ 6) ∧
    (∀ t : Fin 10, (univ.filter (fun i => deletedAdj ∅ t i=true)).Nonempty ∧
      (univ \ insert t (univ.filter (fun i => deletedAdj ∅ t i=true))).Nonempty) ∧
    deletionBias 0=890121037/44498644960 ∧
    1/50 < deletionBias 0 ∧ deletionBias 0 < 1/49 ∧ deletionBias 0 ≠ 0 := by
  have he : deletionBias 0=890121037/44498644960 := by
    unfold deletionBias deletionMasks
    rw [Finset.powersetCard_zero]
    simp only [average, Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, div_one]
    unfold mean
    simp_rw [zero_deletion_hajek_values]
    norm_num [Fin.sum_univ_succ]
  refine ⟨by decide, ?_, by decide, ?_, he, ?_, ?_, ?_⟩
  · norm_num [mean, biasBaseline, Fin.sum_univ_succ]
  · intro t
    rw [zero_deletion_graph_certificate.2.1]
    exact zero_deletion_graph_certificate.2.2.1 t
  all_goals rw [he] <;> norm_num

/-- A rational-arithmetic copy of the actual T8 Hajek contrast;
its equality with the real estimator is proved below. -/
def deletionHajekQ (R : Finset (Fin 10 × Fin 10)) (t : Fin 10) : ℚ :=
  let S := univ.filter (fun i => deletedAdj R t i = true)
  let C := univ \ insert t S
  let b := fun i : Fin 10 => if i=1 then (5/2 : ℚ) else 1
  ((∑ i ∈ S, ((5/4)*b i)/(measuredDegree R i)) /
    (∑ i ∈ S, 1/(measuredDegree R i : ℚ))) -
  ((∑ i ∈ C, b i*(1+(if printedAdj t i then (1/4 : ℚ) else 0))/
      (9-(measuredDegree R i : ℚ))) /
    (∑ i ∈ C, 1/(9-(measuredDegree R i : ℚ))))

/-- The rational copy represents exactly the original real contrast. -/
theorem deletion_hajek_rat (R : Finset (Fin 10 × Fin 10)) (t : Fin 10) :
    (deletionHajekQ R t : ℝ) = deletionHajek R t := by
  classical
  dsimp only [deletionHajekQ, deletionHajek, biasBaseline]
  simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero,
    apply_ite (fun x : ℚ => (x : ℝ))]


/-- Rational representation of T8's exact finite-design bias. -/
def deletionBiasQ (d : ℕ) : ℚ :=
  (∑ R ∈ deletionMasks d, (∑ t : Fin 10, deletionHajekQ R t)/10) /
    (deletionMasks d).card - 23/80

/-- Rational representation preserves the exact averaging law and bias. -/
theorem deletion_bias_rat (d : ℕ) : (deletionBiasQ d : ℝ) = deletionBias d := by
  simp [deletionBiasQ, deletionBias, average, mean, Rat.cast_sum, deletion_hajek_rat]

set_option maxRecDepth 4096 in
/-- T8: exact rational one-tie-deletion bias bounds for all 200 cases. -/
theorem one_deletion_bias_bounds :
    (9/1000 : ℝ) < deletionBias 1 ∧ deletionBias 1 < 1/100 := by
  have h : (9/1000 : ℚ) < deletionBiasQ 1 ∧ deletionBiasQ 1 < 1/100 := by
    decide +kernel
  have h' := And.intro ((Rat.cast_lt (K := ℝ)).2 h.1)
    ((Rat.cast_lt (K := ℝ)).2 h.2)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, deletion_bias_rat] using h'

set_option maxRecDepth 4096 in
/-- T8: exact rational two-tie-deletion bias bounds for all 1,900 cases. -/
theorem two_deletion_bias_bounds :
    -(1/800 : ℝ) < deletionBias 2 ∧ deletionBias 2 < -(1/900) := by
  have h : -(1/800 : ℚ) < deletionBiasQ 2 ∧ deletionBiasQ 2 < -(1/900) := by
    decide +kernel
  have h' := And.intro ((Rat.cast_lt (K := ℝ)).2 h.1)
    ((Rat.cast_lt (K := ℝ)).2 h.2)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_neg,
    deletion_bias_rat] using h'

/-- Deleting R undirected edges can remove at most card R neighbors of
one vertex. This bound applies to every mask, including redundant/non-edge
entries, and supports T8's valid-domain certificate. -/
theorem deleted_degree_loss_bound (R : Finset (Fin 10 × Fin 10)) (i : Fin 10) :
    measuredDegree ∅ i - R.card ≤ measuredDegree R i ∧
      measuredDegree R i ≤ measuredDegree ∅ i := by
  classical
  let A := univ.filter (fun j => printedAdj i j=true)
  let B := univ.filter (fun j => deletedAdj R i j=true)
  have ha : A.card=measuredDegree ∅ i := by
    simp [A, measuredDegree, deletedAdj]
  have hb : B.card=measuredDegree R i := rfl
  have hsub : B ⊆ A := by
    intro j hj
    simp only [B, A, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    unfold deletedAdj at hj
    cases h : printedAdj i j <;> simp [h] at hj ⊢
  have hdiff : A \ B ⊆ R.image (fun e => if e.1=i then e.2 else e.1) := by
    intro j hj
    rcases Finset.mem_sdiff.mp hj with ⟨hjA,hjB⟩
    have htrue : printedAdj i j=true := (Finset.mem_filter.mp hjA).2
    have hdir : (i,j) ∈ R ∨ (j,i) ∈ R := by
      by_contra h
      push Not at h
      apply hjB
      simp [B, deletedAdj, htrue, h.1, h.2]
    rcases hdir with h | h
    · exact Finset.mem_image.mpr ⟨(i,j),h,by simp⟩
    · refine Finset.mem_image.mpr ⟨(j,i),h,?_⟩
      by_cases hji : j=i <;> simp [hji]
  have hl := le_trans (Finset.card_le_card hdiff) (Finset.card_image_le)
  rw [Finset.card_sdiff_of_subset hsub] at hl
  have hu := Finset.card_le_card hsub
  rw [ha,hb] at hl hu
  omega

/-- T8(ii): measured degrees, positive inclusion-probability factors,
and nonempty realized cells under every mask with at most two missing ties. -/
theorem deletion_domain_certificate :
    ∀ d : Fin 3, ∀ R ∈ deletionMasks d.val,
      (∀ i : Fin 10, 1 ≤ measuredDegree R i ∧ measuredDegree R i ≤ 6) ∧
      (∀ t : Fin 10, (univ.filter (fun i => deletedAdj R t i=true)).Nonempty ∧
        (univ \ insert t (univ.filter (fun i => deletedAdj R t i=true))).Nonempty) := by
  have hbase : ∀ i : Fin 10, 3 ≤ measuredDegree ∅ i ∧ measuredDegree ∅ i ≤ 6 := by
    decide
  intro d R hR
  have hc : R.card=d.val := (Finset.mem_powersetCard.mp hR).2
  have hdegree : ∀ i : Fin 10, 1 ≤ measuredDegree R i ∧ measuredDegree R i ≤ 6 := by
    intro i
    have hl := deleted_degree_loss_bound R i
    have hb := hbase i
    have hd := d.isLt
    omega
  refine ⟨hdegree, ?_⟩
  intro t
  have hb := hdegree t
  constructor
  · apply Finset.card_pos.mp
    exact lt_of_lt_of_le (by norm_num : 0<1) hb.1
  · let B := univ.filter (fun i => deletedAdj R t i=true)
    have hi : (insert t B).card ≤ B.card+1 := Finset.card_insert_le _ _
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hu : (univ : Finset (Fin 10)).card=10 := by simp
    rw [hu]
    have hupper : B.card ≤ 6 := hb.2
    change 0 < 10 - (insert t B).card
    omega

/-- T8(i)–(iv): every probability and ratio is on its valid domain, and
absolute Hajek bias strictly decreases at 0, 1/20, 1/10 missing ties.
The source matrix, baseline schedule and exact finite averaging are explicit. -/
theorem nonmonotone_hajek_counterexample :
    printedEdges.card = 20 ∧
    mean biasBaseline / 4 = 23/80 ∧
    (∀ d : ℕ, d ≤ 2 → ∀ R ∈ deletionMasks d, ∀ i,
      1 ≤ measuredDegree R i ∧ measuredDegree R i ≤ 6) ∧
    deletionBias 0 = 890121037/44498644960 ∧
    1/50 < deletionBias 0 ∧ deletionBias 0 < 1/49 ∧
    9/1000 < deletionBias 1 ∧ deletionBias 1 < 1/100 ∧
    -(1/800) < deletionBias 2 ∧ deletionBias 2 < -(1/900) ∧
    |deletionBias 2| < |deletionBias 1| ∧ |deletionBias 1| < |deletionBias 0| ∧
    deletionBias 0 ≠ 0 := by
  have hz := zero_deletion_hajek_counterexample
  have h0 := hz.2.2.2.2
  have h1 := one_deletion_bias_bounds
  have h2 := two_deletion_bias_bounds
  refine ⟨hz.1, hz.2.1, ?_, h0.1, h0.2.1, h0.2.2.1,
    h1.1, h1.2, h2.1, h2.2, ?_, ?_, h0.2.2.2⟩
  · intro d hd R hR i
    exact (deletion_domain_certificate ⟨d, by omega⟩ R hR).1 i
  · rw [abs_of_neg (by linarith : deletionBias 2<0),
      abs_of_pos (by linarith : 0<deletionBias 1)]
    linarith
  · rw [abs_of_pos (by linarith : 0<deletionBias 1),
      abs_of_pos (by linarith : 0<deletionBias 0)]
    linarith

/-- T9(e), the repaired qualitative conclusion: exact Hajek unbiasedness
at zero missing ties and monotone growth of bias are both false in general. -/
theorem hajek_bias_correction :
    deletionBias 0 ≠ 0 ∧ |deletionBias 1| < |deletionBias 0| := by
  have h0 := zero_deletion_hajek_counterexample.2.2.2.2
  have h1 := one_deletion_bias_bounds
  refine ⟨h0.2.2.2, ?_⟩
  rw [abs_of_pos (by linarith : 0<deletionBias 1),
    abs_of_pos (by linarith : 0<deletionBias 0)]
  linarith


/-- Graph hop distances are extended naturals, infinite between components;
the correction to "ε hops apart" is on p. 305 (T21). -/
def separated {V : Type*} (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, s ≠ t → (ε : ℕ∞) ≤ d s t
/-- "every unit outside the set is within ε−1 hops of a unit in the set" (p. 305). Distances are extended naturals, with infinity between components. -/
def covers {V : Type*} (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) : Prop :=
  ∀ v, v ∉ S → ∃ s ∈ S, d s v ≤ ((ε-1 : ℕ) : ℕ∞)
/-- "at least ε hops apart" and "within ε−1 hops" (p. 305, correction T21): pairwise separation together with the unchanged covering clause. -/
def epsilonNet {V : Type*} (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) : Prop :=
  separated d ε S ∧ covers d ε S

instance {V : Type*} [Fintype V] [DecidableEq V] (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) :
    Decidable (separated d ε S) :=
  inferInstanceAs (Decidable (∀ s ∈ S, ∀ t ∈ S, s ≠ t → (ε : ℕ∞) ≤ d s t))
instance {V : Type*} [Fintype V] [DecidableEq V] (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) :
    Decidable (covers d ε S) :=
  inferInstanceAs (Decidable (∀ v, v ∉ S → ∃ s ∈ S, d s v ≤ ((ε-1 : ℕ) : ℕ∞)))
instance {V : Type*} [Fintype V] [DecidableEq V] (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) :
    Decidable (epsilonNet d ε S) :=
  inferInstanceAs (Decidable (separated d ε S ∧ covers d ε S))

/-- Marked vertices are the union of the radius ε−1 balls of the centres,
p. 305 corrected greedy construction (T11, T21). -/
def marked {V : Type*} [Fintype V] (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) : Finset V :=
  univ.filter (fun v => ∃ s ∈ S, d s v ≤ ((ε-1 : ℕ) : ℕ∞))

/-- A sequence of correct choices always picks outside the previously
marked set. This represents every possible corrected draw sequence. -/
def greedyRun {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → V → ℕ∞) (ε : ℕ) (cs : List V) : Prop :=
  ∀ k : Fin cs.length, cs.get k ∉ marked d ε (cs.take k.val).toFinset

/-- Integer hop distances are at most ε−1 exactly when they are less
than ε. This also treats infinite distances between components (T21). -/
theorem hops_radius_iff (ε : ℕ) (hε : 1 ≤ ε) (x : ℕ∞) :
    x ≤ ((ε-1 : ℕ) : ℕ∞) ↔ x < (ε : ℕ∞) := by
  have hc : (ε : ℕ∞)=((ε-1 : ℕ) : ℕ∞)+1 := by
    exact_mod_cast (show ε=(ε-1)+1 by omega)
  rw [hc,ENat.lt_natCast_add_one_iff]

/-- T21(i): a separated set admits an additional vertex precisely when
that vertex is at least ε hops from every existing centre. -/
theorem separated_insert_iff {n ε : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hs : separated G.edist ε S) (v : Fin n) (hv : v ∉ S) :
    separated G.edist ε (insert v S) ↔ ∀ s ∈ S, (ε : ℕ∞) ≤ G.edist s v := by
  constructor
  · intro h s hS
    exact h s (mem_insert_of_mem hS) v (mem_insert_self _ _) (by intro he; subst s; exact hv hS)
  · intro h a ha b hb hab
    rcases Finset.mem_insert.mp ha with he | ha
    · subst a
      rcases Finset.mem_insert.mp hb with he | hb
      · exact (hab he.symm).elim
      · simpa only [G.edist_comm] using h b hb
    · rcases Finset.mem_insert.mp hb with he | hb
      · subst b; exact h a ha
      · exact hs a ha b hb hab

/-- T21(i): covering is exactly maximality of the separated centre set;
the statement uses the same finite undirected graph and integer radius. -/
theorem separated_maximal_iff_covers {n ε : ℕ} (hε : 1 ≤ ε)
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (hs : separated G.edist ε S) :
    covers G.edist ε S ↔ ∀ v ∉ S, ¬separated G.edist ε (insert v S) := by
  constructor
  · intro hc v hv hi
    rcases hc v hv with ⟨s,hS,hnear⟩
    have hfar := (separated_insert_iff G S hs v hv).1 hi s hS
    exact (not_le_of_gt ((hops_radius_iff ε hε _).1 hnear)) hfar
  · intro hm v hv
    by_contra h
    apply hm v hv
    rw [separated_insert_iff G S hs v hv]
    intro s hS
    apply le_of_not_gt
    intro hd
    exact h ⟨s,hS,(hops_radius_iff ε hε _).2 hd⟩

/-- T21(i): every finite undirected graph has an ε-net. A separated set
of maximal cardinality covers, including disconnected graphs. -/
theorem finite_graph_has_epsilon_net {n ε : ℕ} (hε : 1 ≤ ε)
    (G : SimpleGraph (Fin n)) : ∃ S : Finset (Fin n), epsilonNet G.edist ε S := by
  classical
  let admissible : Finset (Finset (Fin n)) := univ.filter (separated G.edist ε)
  have he : separated G.edist ε ∅ := by simp [separated]
  have ha : admissible.Nonempty := ⟨∅,by simp [admissible,he]⟩
  obtain ⟨S,hS,hmax⟩ := Finset.exists_max_image admissible Finset.card ha
  have hs : separated G.edist ε S := (Finset.mem_filter.mp hS).2
  refine ⟨S,hs,(separated_maximal_iff_covers hε G S hs).2 ?_⟩
  intro v hv hi
  have hI : insert v S ∈ admissible := by simp [admissible,hi]
  have hbound := hmax (insert v S) hI
  rw [Finset.card_insert_of_notMem hv] at hbound
  omega

/-- T11(c), T21(ii): adding an unmarked centre strictly decreases the
number of unmarked vertices. No probabilistic hypothesis is needed. -/
theorem unmarked_strictly_decreases {n ε : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (v : Fin n) (hv : v ∉ marked G.edist ε S) :
    (univ \ marked G.edist ε (insert v S)).card < (univ \ marked G.edist ε S).card := by
  have hsub : marked G.edist ε S ⊆ marked G.edist ε (insert v S) := by
    intro w hw
    simp only [marked,Finset.mem_filter,Finset.mem_univ,true_and] at hw ⊢
    rcases hw with ⟨s,hS,hd⟩
    exact ⟨s,mem_insert_of_mem hS,hd⟩
  have hvnew : v ∈ marked G.edist ε (insert v S) := by
    simp only [marked,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨v,mem_insert_self _ _,by simp⟩
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.sdiff_subset_sdiff_right _ hsub,?_⟩
  intro he
  have hvold : v ∈ (univ \ marked G.edist ε S) := by simp [hv]
  rw [← he] at hvold
  exact (Finset.mem_sdiff.mp hvold).2 hvnew

/-- T11(a),(d), T21(ii): ball-union marking at termination is equivalent
to the covering clause; centres cover themselves at distance zero. -/
theorem marked_all_iff_covers {n ε : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    marked G.edist ε S = univ ↔ covers G.edist ε S := by
  constructor
  · intro he v hv
    have hm : v ∈ marked G.edist ε S := by rw [he]; simp
    simpa only [marked,Finset.mem_filter,Finset.mem_univ,true_and] using hm
  · intro hc
    apply Finset.eq_univ_of_forall
    intro v
    simp only [marked,Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases hv : v ∈ S
    · exact ⟨v,hv,by simp⟩
    · exact hc v hv

/-- A greedy run may append exactly an unmarked vertex, directly from
the paper's sequential choice rule (T11, T21). -/
theorem greedy_append_iff {n ε : ℕ} (G : SimpleGraph (Fin n)) (cs : List (Fin n)) (v : Fin n) :
    greedyRun G.edist ε (cs++[v]) ↔ greedyRun G.edist ε cs ∧ v ∉ marked G.edist ε cs.toFinset := by
  constructor
  · intro h
    constructor
    · intro k
      have hk : k.val < (cs++[v]).length := by
        simp only [List.length_append,List.length_singleton]; omega
      have hh := h ⟨k.val,hk⟩
      simpa only [List.get_eq_getElem,List.getElem_append_left k.isLt,
        List.take_append_of_le_length (le_of_lt k.isLt)] using hh
    · have hk : cs.length < (cs++[v]).length := by simp
      have hh := h ⟨cs.length,hk⟩
      simpa [List.get_eq_getElem,List.getElem_append_right (le_refl cs.length),
        List.take_append_of_le_length (le_refl cs.length)] using hh
  · rintro ⟨h,hv⟩ k
    by_cases hk : k.val < cs.length
    · have hh := h ⟨k.val,hk⟩
      simpa only [List.get_eq_getElem,List.getElem_append_left hk,
        List.take_append_of_le_length (le_of_lt hk)] using hh
    · have he : k.val=cs.length := by have := k.isLt; simp only [List.length_append,List.length_singleton] at this; omega
      simpa [List.get_eq_getElem,he,List.getElem_append_right (by omega : cs.length ≤ k.val),
        List.take_append_of_le_length (by omega : k.val ≤ cs.length)] using hv

/-- T11(b)–(d), T21(ii): every allowed run has distinct centres, at most
n of them, and pairwise separation. A terminating run is a covering net. -/
theorem greedy_run_properties {n ε : ℕ} (hε : 1 ≤ ε) (G : SimpleGraph (Fin n))
    (cs : List (Fin n)) (h : greedyRun G.edist ε cs) :
    cs.Nodup ∧ cs.length ≤ n ∧ separated G.edist ε cs.toFinset ∧
      (marked G.edist ε cs.toFinset = univ → epsilonNet G.edist ε cs.toFinset) := by
  have hcore : cs.Nodup ∧ separated G.edist ε cs.toFinset := by
    induction cs using List.reverseRecOn with
    | nil => simp [separated]
    | append_singleton cs v ih =>
      have hp := (greedy_append_iff G cs v).1 h
      obtain ⟨hnd,hsep⟩ := ih hp.1
      have hv : v ∉ cs.toFinset := by
        intro hm
        apply hp.2
        simp only [marked,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨v,hm,by simp⟩
      constructor
      · simp only [List.nodup_append,hnd,List.nodup_singleton,true_and]
        intro a ha b hb he
        have hb' : b=v := List.mem_singleton.mp hb
        apply hv
        rw [← hb',← he]
        exact List.mem_toFinset.mpr ha
      · simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
          Finset.insert_empty,Finset.union_singleton]
        apply (separated_insert_iff G cs.toFinset hsep v hv).2
        intro s hs
        apply le_of_not_gt
        intro hd
        apply hp.2
        simp only [marked,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨s,hs,(hops_radius_iff ε hε _).2 hd⟩
  refine ⟨hcore.1,?_,hcore.2,?_⟩
  · simpa using hcore.1.length_le_card
  · intro he; exact ⟨hcore.2,(marked_all_iff_covers G cs.toFinset).1 he⟩

/-- T11(c), T21(ii): a completed valid greedy run exists. Strong
induction uses the strictly decreasing number of unmarked vertices,
without any enumeration or probabilistic termination assumption. -/
theorem greedy_completed_run_exists {n ε : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ cs : List (Fin n), greedyRun G.edist ε cs ∧ marked G.edist ε cs.toFinset = univ := by
  classical
  have extend : ∀ k : ℕ, ∀ cs : List (Fin n),
      (univ \ marked G.edist ε cs.toFinset).card=k → greedyRun G.edist ε cs →
      ∃ cs' : List (Fin n), greedyRun G.edist ε cs' ∧ marked G.edist ε cs'.toFinset=univ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro cs hk hg
      by_cases he : marked G.edist ε cs.toFinset=univ
      · exact ⟨cs,hg,he⟩
      · have hex : ∃ v, v ∉ marked G.edist ε cs.toFinset := by
          by_contra hnone
          push_neg at hnone
          apply he
          exact Finset.eq_univ_of_forall hnone
        obtain ⟨v,hv⟩ := hex
        have hv' := unmarked_strictly_decreases G cs.toFinset v hv
        have hcard : (univ \ marked G.edist ε (cs++[v]).toFinset).card < k := by
          simpa [List.toFinset_append,hk] using hv'
        exact ih _ hcard (cs++[v]) rfl ((greedy_append_iff G cs v).2 ⟨hg,hv⟩)
  exact extend _ [] rfl (by simp [greedyRun])

/-- Path hop distance |i−j|, the explicit distance fixed in T10 and T20. -/
def pathDistance {n : ℕ} (i j : Fin n) : ℕ∞ := (Nat.dist i.val j.val : ℕ)

/-- The actual R centre draw, including its singleton-number rule; `coded`
selects the defect. For the repaired draw every remaining vertex is equally
likely. Only nonterminal states use this kernel (T10–T11). -/
def centreDraw {n : ℕ} (d : Fin n → Fin n → ℕ∞) (ε : ℕ) (coded : Bool)
    (S : Finset (Fin n)) (v : Fin n) : ℝ :=
  let R := univ \ marked d ε S
  if coded = true ∧ R.card = 1 then
    let u := R.toList.head?.getD v
    if v.val ≤ u.val then 1/(u.val+1 : ℕ) else 0
  else if v ∈ R then 1/R.card else 0

/-- Probability of a finite terminating trace in the sampler, computed
from actual transition probabilities. Proper prefixes must be nonterminal,
and the final centres must mark every vertex. -/
def traceMass {n : ℕ} (d : Fin n → Fin n → ℕ∞) (ε : ℕ) (coded : Bool)
    (cs : List (Fin n)) : ℝ :=
  if (∀ k : Fin cs.length, marked d ε (cs.take k.val).toFinset ≠ univ) ∧
      marked d ε cs.toFinset = univ then
    ∏ k : Fin cs.length, centreDraw d ε coded (cs.take k.val).toFinset (cs.get k)
  else 0

/-- Terminal centre law, summing over all finite trace lengths; unchanged
state retries are included, rather than assuming their 1/3 probabilities. -/
def terminalCentres {n : ℕ} (d : Fin n → Fin n → ℕ∞) (ε : ℕ)
    (coded : Bool) (S : Finset (Fin n)) : ℝ :=
  ∑' t : ℕ, ∑ z : Fin t → Fin n,
    if (List.ofFn z).toFinset = S then traceMass d ε coded (List.ofFn z) else 0

/-- Nearest-centre membership, with ties going to the smallest vertex
index (p. 305, package sampler). Empty S gives `none`. -/
def nearestCentre {n : ℕ} (d : Fin n → Fin n → ℕ∞)
    (S : Finset (Fin n)) (v : Fin n) : Option (Fin n) :=
  (S.toList.mergeSort (fun a b => decide (d a v < d b v ∨ (d a v = d b v ∧ a ≤ b)))).head?

/-- Independent Bernoulli(p) draws for the centres; extra unused unit
coordinates integrate out. Membership is constant within each cluster. -/
def clusterProb {n : ℕ} (d : Fin n → Fin n → ℕ∞) (S : Finset (Fin n))
    (p : ℝ) (z : Assignment n) : ℝ :=
  prob (bernoulli p) (fun c => ∀ v, ∃ s, nearestCentre d S v = some s ∧ z v = c s)
/-- "treatment randomization is performed at the cluster level" (p. 305). Integrate nearest-centre Bernoulli coins over the explicit terminal-centre law (T10–T11, T29). -/
def clusteredTreatment {n : ℕ} (d : Fin n → Fin n → ℕ∞) (coded : Bool)
    (p : ℝ) (z : Assignment n) : ℝ :=
  ∑ S : Finset (Fin n), terminalCentres d 3 coded S * clusterProb d S p z

/-- T10(i): the actual radius-two marking on the four-path. -/
theorem four_path_marking_certificate :
    marked (pathDistance (n := 4)) 3 (∅ : Finset (Fin 4))=∅ ∧
    marked (pathDistance (n := 4)) 3 {0}={0,1,2} ∧
    (∀ j : Fin 4, j ≠ 0 → marked (pathDistance (n := 4)) 3 {0,j}=univ) := by
  decide

/-- T10(ii): every coded draw from the empty state or from the state
with centre `0` alone is uniform on all four path vertices. -/
theorem four_path_coded_draws (v : Fin 4) :
    centreDraw pathDistance 3 true ∅ v=1/4 ∧
    centreDraw pathDistance 3 true {0} v=1/4 := by
  have h0 := four_path_marking_certificate.1
  have hR : (univ : Finset (Fin 4)) \ marked pathDistance 3 {0}={3} := by decide
  have hv : v.val ≤ 3 := by omega
  constructor
  · norm_num [centreDraw, h0]
  · norm_num [centreDraw, hR, hv]

/-- T10(ii): the finite terminating trace with r retries of centre `0`
and eventual second centre j has exactly mass (1/4)^(r+2). The mass is
computed from the coded kernel, including the unchanged-state retries. -/
theorem four_path_repeat_trace_mass (r : ℕ) (j : Fin 4) (hj : j ≠ 0) :
    traceMass pathDistance 3 true (List.replicate (r+1) (0 : Fin 4) ++ [j]) =
      (1/4 : ℝ)^(r+2) := by
  classical
  let cs := List.replicate (r+1) (0 : Fin 4) ++ [j]
  have hlen : cs.length=r+2 := by simp [cs]
  have hp : ∀ k : ℕ, k ≤ r+1 →
      (cs.take k).toFinset = if k=0 then ∅ else {0} := by
    intro k hk
    dsimp only [cs]
    rw [List.take_append_of_le_length (by simpa)]
    rw [List.take_replicate, Nat.min_eq_left hk]
    by_cases hz : k=0
    · simp [hz]
    · simp [hz, List.toFinset_replicate_of_ne_zero hz]
  have hf : cs.toFinset={0,j} := by
    simp [cs, List.toFinset_append, List.toFinset_replicate_of_ne_zero
      (by omega : r+1≠0)]
  have ht : (∀ k : Fin cs.length,
      marked pathDistance 3 (cs.take k.val).toFinset ≠ univ) ∧
      marked pathDistance 3 cs.toFinset=univ := by
    constructor
    · intro k
      have hk : k.val ≤ r+1 := by have hk := k.isLt; omega
      rw [hp k.val hk]
      by_cases hz : k.val=0
      · rw [if_pos hz, four_path_marking_certificate.1]
        decide
      · rw [if_neg hz, four_path_marking_certificate.2.1]
        decide
    · rw [hf]
      exact four_path_marking_certificate.2.2 j hj
  have hd : ∀ k : Fin cs.length,
      centreDraw pathDistance 3 true (cs.take k.val).toFinset (cs.get k)=1/4 := by
    intro k
    have hk : k.val ≤ r+1 := by have hk := k.isLt; omega
    rw [hp k.val hk]
    split_ifs
    · exact (four_path_coded_draws _).1
    · exact (four_path_coded_draws _).2
  change traceMass pathDistance 3 true cs = _
  unfold traceMass
  rw [if_pos ht]
  simp_rw [hd]
  simp [hlen]

/-- T10(ii): summing the actual retry-trace masses for each eventual
second centre gives 1/12, before adding any other initial-centre cases.
This is a geometric-series lemma; it does not assume terminal-law
normalization or classify every possible terminating trace. -/
theorem four_path_repeat_trace_sum (j : Fin 4) (hj : j ≠ 0) :
    (∑' r : ℕ, traceMass pathDistance 3 true
      (List.replicate (r+1) (0 : Fin 4) ++ [j])) = 1/12 := by
  simp_rw [four_path_repeat_trace_mass _ j hj, pow_add]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num


/-- T10's finite positive-probability bad trace: on the four-path, centres
1 then 2 (one based) end the loop but violate separation. Its probability
is 1/16 before the cluster coin flips. -/
theorem singleton_draw_bad_trace :
    traceMass (pathDistance (n := 4)) 3 true [0,1] = 1/16 ∧
    ¬separated (pathDistance (n := 4)) 3 {0,1} := by
  constructor
  · have h0 : marked (pathDistance (n := 4)) 3 ∅=∅ := by ext i; simp [marked]
    have h1 : marked (pathDistance (n := 4)) 3 {0}={0,1,2} := by decide
    have h2 : marked (pathDistance (n := 4)) 3 {0,1}=univ := by decide
    have ht : (∀ k : Fin ([0,1] : List (Fin 4)).length,
        marked (pathDistance (n := 4)) 3 ([0,1].take k.val).toFinset ≠ univ) ∧
        marked (pathDistance (n := 4)) 3 [0,1].toFinset=univ := by decide
    unfold traceMass
    rw [if_pos ht]
    have hr : (univ : Finset (Fin 4)) \ marked pathDistance 3 {0} = {3} := by decide
    have hc0 : centreDraw (pathDistance (n := 4)) 3 true ∅ 0 = 1/4 := by
      norm_num [centreDraw, h0]
    have hc1 : centreDraw (pathDistance (n := 4)) 3 true {0} 1 = 1/4 := by
      norm_num [centreDraw, hr]
    simpa [Fin.prod_univ_succ, hc0, hc1] using (show (1/4 : ℝ)*(1/4)=1/16 by norm_num)
  · decide

/-- T11(a)–(d): corrected greedy centre choices in any finite undirected
graph preserve ball-union marking, separate centres, strictly reduce the
unmarked set, and finish in at most n steps with a 3-net. -/
theorem greedy_three_net_correction {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    (∀ cs : List (Fin n), greedyRun G.edist 3 cs →
      cs.Nodup ∧ cs.length ≤ n ∧ separated G.edist 3 cs.toFinset ∧
      (marked G.edist 3 cs.toFinset = univ → epsilonNet G.edist 3 cs.toFinset)) ∧
    (∀ S : Finset (Fin n), ∀ v ∉ marked G.edist 3 S,
      (univ \ marked G.edist 3 (insert v S)).card < (univ \ marked G.edist 3 S).card) ∧
    (∃ cs : List (Fin n), greedyRun G.edist 3 cs ∧ marked G.edist 3 cs.toFinset = univ) := by
  exact ⟨fun cs h => greedy_run_properties (by norm_num) G cs h,
    unmarked_strictly_decreases G,greedy_completed_run_exists G⟩

/-- T21(i)–(ii): corrected ε-net definition is equivalent to maximal
separation and has the finite greedy construction, including disconnected
graphs with infinite inter-component distance. -/
theorem epsilon_net_correction {n ε : ℕ} (hε : 1 ≤ ε) (G : SimpleGraph (Fin n)) :
    (∀ S : Finset (Fin n), separated G.edist ε S →
      (covers G.edist ε S ↔ ∀ v ∉ S, ¬separated G.edist ε (insert v S))) ∧
    (∀ cs : List (Fin n), greedyRun G.edist ε cs →
      cs.Nodup ∧ cs.length ≤ n ∧ separated G.edist ε cs.toFinset ∧
      (marked G.edist ε cs.toFinset = univ → epsilonNet G.edist ε cs.toFinset)) ∧
    (∃ cs : List (Fin n), greedyRun G.edist ε cs ∧ marked G.edist ε cs.toFinset = univ) ∧
    (∃ S : Finset (Fin n), epsilonNet G.edist ε S) := by
  exact ⟨fun S h => separated_maximal_iff_covers hε G S h,
    fun cs h => greedy_run_properties hε G cs h,
    greedy_completed_run_exists G,finite_graph_has_epsilon_net hε G⟩

/-- T20's literal "within 3 hops of each other" upper bound (p. 305). -/
def withinThree (S : Finset (Fin 9)) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, pathDistance s t ≤ 3

/-- Decidability of the pairwise distance upper bound on the nine-vertex path. -/
instance (S : Finset (Fin 9)) : Decidable (withinThree S) :=
  inferInstanceAs (Decidable (∀ s ∈ S, ∀ t ∈ S, pathDistance s t ≤ 3))

set_option maxRecDepth 4096 in
/-- T20, the literal p. 305 definition on the nine-vertex path: no set
has both pairwise-within-three distance and the required two-hop cover.
The corrected separation definition instead has exactly the thirteen
listed three-nets, certifying the distinction with actual path distances. -/
theorem within_hops_counterexample :
    (∀ S : Finset (Fin 9), ¬(withinThree S ∧ covers pathDistance 3 S)) ∧
    (univ.filter (fun S : Finset (Fin 9) => epsilonNet pathDistance 3 S)).card = 13 ∧
    (∀ S : Finset (Fin 9), epsilonNet pathDistance 3 S ↔
      S ∈ ({ {1,6}, {2,6}, {2,7}, {0,3,6}, {0,3,7}, {0,3,8},
        {0,4,7}, {0,4,8}, {0,5,8}, {1,4,7}, {1,4,8}, {1,5,8}, {2,5,8} } : Finset (Finset (Fin 9)))) := by
  decide

/-- Uniform design treating exactly two of ten units, with the pair
representation avoiding enumeration of 1024 irrelevant assignment vectors
(p. 292 and targets T12, T16). -/
def treatmentPairs : Finset (Fin 10 × Fin 10) := univ.filter (fun e => e.1 < e.2)
/-- "exactly ... two" treated units in the running CR example (p. 292): a sorted pair induces its Boolean ten-unit assignment. -/
def pairAssignment (e : Fin 10 × Fin 10) : Assignment 10 := fun i => decide (i=e.1 ∨ i=e.2)
/-- "π_i(d)=Pr(D_i=d)" (p. 294), computed exactly over the forty-five equally likely pairs (T12, T16). -/
def pairExposureProb (A : Fin 10 → Fin 10 → Bool) (i : Fin 10) (d : Exposure) : ℝ :=
  average treatmentPairs (fun e => if exposure A (pairAssignment e) i = d then 1 else 0)

/-- Ten-cycle, T12's counterexample. -/
def cycle10 (i j : Fin 10) : Bool :=
  decide ((i.val+1)%10 = j.val ∨ (j.val+1)%10 = i.val)
/-- "(2,1,1,0)" (T12 setting): the ten-cycle counterexample's fixed four-exposure outcomes. -/
def cycleOut (_i : Fin 10) (d : Exposure) : ℝ :=
  match d with | .d11 => 2 | .d10 => 1 | .d01 => 1 | .d00 => 0

/-- T12's two printed expressions. Denominators are the exact finite
pair-design probabilities; L uses own-treatment probability 1/5 and R the
exposure-specific probabilities (p. 301, the erroneous equality). -/
def cycleL (e : Fin 10 × Fin 10) : ℝ :=
  mean (fun i => if pairAssignment e i then cycleOut i (exposure cycle10 (pairAssignment e) i)/(1/5) else 0)
/-- The printed sum with denominators "π_i(d11)" and "π_i(d10)" (p. 301), evaluated in T12's actual ten-cycle pair design. -/
def cycleR (e : Fin 10 × Fin 10) : ℝ :=
  mean (fun i =>
    (if exposure cycle10 (pairAssignment e) i = .d11 then 2/pairExposureProb cycle10 i .d11 else 0) +
    (if exposure cycle10 (pairAssignment e) i = .d10 then 1/pairExposureProb cycle10 i .d10 else 0))

/-- T12/T16, p. 294: exact pair-design exposure probabilities are event
counts divided by the number of equally likely treatment pairs. -/
theorem pair_exposure_probability_count (A : Fin 10 → Fin 10 → Bool)
    (i : Fin 10) (d : Exposure) :
    pairExposureProb A i d =
      ((treatmentPairs.filter (fun e => exposure A (pairAssignment e) i=d)).card : ℝ) /
        treatmentPairs.card := by
  simp [pairExposureProb, average, Finset.sum_ite]

/-- T12(i): the four cycle exposure counts, computed on the 45 pairs,
give the exact positive probabilities of the counterexample. -/
theorem cycle_pair_probabilities : ∀ i : Fin 10,
    pairExposureProb cycle10 i .d11 = 2/45 ∧
    pairExposureProb cycle10 i .d10 = 7/45 ∧
    pairExposureProb cycle10 i .d01 = 1/3 ∧
    pairExposureProb cycle10 i .d00 = 7/15 := by
  have hc : treatmentPairs.card = 45 := by decide
  have he : ∀ i : Fin 10,
      (treatmentPairs.filter (fun e => exposure cycle10 (pairAssignment e) i=.d11)).card = 2 ∧
      (treatmentPairs.filter (fun e => exposure cycle10 (pairAssignment e) i=.d10)).card = 7 ∧
      (treatmentPairs.filter (fun e => exposure cycle10 (pairAssignment e) i=.d01)).card = 15 ∧
      (treatmentPairs.filter (fun e => exposure cycle10 (pairAssignment e) i=.d00)).card = 21 := by
    decide
  intro i
  simp only [pair_exposure_probability_count, hc, (he i).1,
    (he i).2.1, (he i).2.2.1, (he i).2.2.2]
  norm_num

set_option maxRecDepth 4096 in
/-- T12(ii): on adjacent pairs both units have d11, and on nonadjacent
pairs both have d10. This small Boolean certificate determines both sums. -/
theorem cycle_pair_exposure_counts : ∀ e ∈ treatmentPairs,
    (univ.filter (fun i => exposure cycle10 (pairAssignment e) i=.d11)).card =
      (if cycle10 e.1 e.2 then 2 else 0) ∧
    (univ.filter (fun i => exposure cycle10 (pairAssignment e) i=.d10)).card =
      (if cycle10 e.1 e.2 then 0 else 2) := by
  decide

/-- T12(ii)–(iii): the two erroneous-equality sides and the correctly
specified d11 HT mean have their asserted values on each actual pair. -/
theorem cycle_pair_estimates (e : Fin 10 × Fin 10) (he : e ∈ treatmentPairs) :
    cycleL e = (if cycle10 e.1 e.2 then 2 else 1) ∧
    cycleR e = (if cycle10 e.1 e.2 then 9 else 9/7) ∧
    mean (fun i => if exposure cycle10 (pairAssignment e) i=.d11 then
      2/pairExposureProb cycle10 i .d11 else 0) =
      (if cycle10 e.1 e.2 then 9 else 0) := by
  classical
  have hf : ∀ i : Fin 10,
      (if pairAssignment e i then cycleOut i (exposure cycle10 (pairAssignment e) i)/(1/5) else 0) =
      (if exposure cycle10 (pairAssignment e) i=.d11 then (10 : ℝ) else 0) +
      (if exposure cycle10 (pairAssignment e) i=.d10 then (5 : ℝ) else 0) := by
    intro i
    unfold exposure
    cases h : pairAssignment e i <;>
      by_cases hpeer : ∃ j, cycle10 i j=true ∧ pairAssignment e j=true <;>
      norm_num [h, hpeer, cycleOut]
  have hc := cycle_pair_exposure_counts e he
  constructor
  · unfold cycleL mean
    simp_rw [hf]
    simp only [Finset.sum_add_distrib]
    simp [Finset.sum_ite, hc.1, hc.2]
    cases cycle10 e.1 e.2 <;> norm_num
  constructor
  · unfold cycleR mean
    simp_rw [(cycle_pair_probabilities _).1, (cycle_pair_probabilities _).2.1]
    simp [Finset.sum_add_distrib, Finset.sum_ite, hc.1, hc.2]
    cases cycle10 e.1 e.2 <;> norm_num
  · unfold mean
    simp_rw [(cycle_pair_probabilities _).1]
    simp [Finset.sum_ite, hc.1]
    cases cycle10 e.1 e.2 <;> norm_num

/-- Finite uniform averaging of a statistic with two values, supporting
the exact-design enumerations of T12 and the p. 312 pooling correction. -/
theorem average_two_values {Ω : Type*} [DecidableEq Ω] (S : Finset Ω)
    (E : Ω → Prop) [DecidablePred E] (X : Ω → ℝ) (a b : ℝ)
    (hX : ∀ w ∈ S, X w=if E w then a else b) :
    average S X = ((S.filter E).card*a+(S.filter (fun w => ¬E w)).card*b)/S.card := by
  unfold average
  congr 1
  calc
    (∑ w ∈ S, X w) = ∑ w ∈ S, if E w then a else b := Finset.sum_congr rfl hX
    _ = (S.filter E).card*a+(S.filter (fun w => ¬E w)).card*b := by
      rw [Finset.sum_ite]
      simp

/-- T12(i)–(iv): exact ten-cycle counterexample to the second equality on
p. 301, with every exposure probability positive and all forty-five pairs.
The correctly specified exposure estimator remains unbiased. -/
theorem naive_denominator_counterexample :
    treatmentPairs.card = 45 ∧
    (∀ i, pairExposureProb cycle10 i .d11 = 2/45 ∧
      pairExposureProb cycle10 i .d10 = 7/45 ∧
      pairExposureProb cycle10 i .d01 = 1/3 ∧
      pairExposureProb cycle10 i .d00 = 7/15) ∧
    (treatmentPairs.filter (fun e => cycle10 e.1 e.2 = true)).card = 10 ∧
    (∀ e ∈ treatmentPairs, (if cycle10 e.1 e.2 then cycleL e = 2 ∧ cycleR e = 9
      else cycleL e = 1 ∧ cycleR e = 9/7)) ∧
    (∀ e ∈ treatmentPairs, cycleL e ≠ cycleR e) ∧
    average treatmentPairs cycleL = 11/9 ∧ average treatmentPairs cycleR = 3 ∧
    average treatmentPairs (fun e => mean (fun i =>
      if exposure cycle10 (pairAssignment e) i = .d11 then 2/pairExposureProb cycle10 i .d11 else 0)) = 2 ∧
    average treatmentPairs cycleL-mean (fun i : Fin 10 => cycleOut i .d11) = -7/9 := by
  have hc : treatmentPairs.card = 45 := by decide
  have ha : (treatmentPairs.filter (fun e => cycle10 e.1 e.2=true)).card = 10 := by decide
  have hb : (treatmentPairs.filter (fun e => ¬cycle10 e.1 e.2=true)).card = 35 := by decide
  have hL : average treatmentPairs cycleL = 11/9 := by
    rw [average_two_values treatmentPairs (fun e => cycle10 e.1 e.2=true)
      cycleL 2 1 (fun e he => (cycle_pair_estimates e he).1), hc, ha, hb]
    norm_num
  have hR : average treatmentPairs cycleR = 3 := by
    rw [average_two_values treatmentPairs (fun e => cycle10 e.1 e.2=true)
      cycleR 9 (9/7) (fun e he => (cycle_pair_estimates e he).2.1), hc, ha, hb]
    norm_num
  refine ⟨hc, cycle_pair_probabilities, ha, ?_, ?_, hL, hR, ?_, ?_⟩
  · intro e he
    have h := cycle_pair_estimates e he
    have hh := And.intro h.1 h.2.1
    cases ht : cycle10 e.1 e.2 <;> simpa [ht] using hh
  · intro e he
    rw [(cycle_pair_estimates e he).1, (cycle_pair_estimates e he).2.1]
    cases cycle10 e.1 e.2 <;> norm_num
  · rw [average_two_values treatmentPairs (fun e => cycle10 e.1 e.2=true)
      _ 9 0 (fun e he => (cycle_pair_estimates e he).2.2), hc, ha, hb]
    norm_num
  · rw [hL]
    norm_num [mean, cycleOut, Fin.sum_univ_succ]

/-- Own-treatment probability π_i=Pr(Z_i=1), pp. 300–301. -/
def ownProb {n : ℕ} (p : Assignment n → ℝ) (i : Fin n) : ℝ := prob p (fun z => z i = true)
/-- "(1/N)∑ I(Z_i=1)Y_i/π_i" (pp. 300–301): the own-treatment HT mean under an interference-ignoring mapping. -/
def naiveTreated {n : ℕ} (p : Assignment n → ℝ) (A : Fin n → Fin n → Bool)
    (y : Fin n → Exposure → ℝ) (z : Assignment n) : ℝ :=
  mean (fun i => if z i then y i (exposure A z i)/ownProb p i else 0)
/-- "the common denominator π_i in both terms" (T13 correction, p. 301): retain the treated-exposure partition and exact own-treatment weights. -/
def repairedExpansion {n : ℕ} (p : Assignment n → ℝ) (A : Fin n → Fin n → Bool)
    (y : Fin n → Exposure → ℝ) (z : Assignment n) : ℝ :=
  mean (fun i =>
    (if exposure A z i = .d11 then y i .d11/ownProb p i else 0) +
    (if exposure A z i = .d10 then y i .d10/ownProb p i else 0))

/-- T13(a)–(b): the two treated exposures partition own treatment, and
the expansion keeps π_i in both denominators (corrected p. 301 display). -/
theorem naive_expansion_correct {n : ℕ} (p : Assignment n → ℝ)
    (A : Fin n → Fin n → Bool) (y : Fin n → Exposure → ℝ) (z : Assignment n) :
    naiveTreated p A y z = repairedExpansion p A y z := by
  unfold naiveTreated repairedExpansion mean
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  unfold exposure
  cases hz : z i <;> by_cases h : ∃ j, A i j = true ∧ z j = true <;> simp [hz,h]

/-- T13(a),(c)–(e): exact mixture expectation and bias, with precise sign
and strictness conditions. Unit differences of opposite signs may cancel.
Only own-treatment positivity is needed for the repaired estimator. -/
theorem naive_bias_correction {n : ℕ} (hn : 0 < n) (p : Design (Assignment n))
    (A : Network n) (y : Fin n → Exposure → ℝ) (hp : ∀ i, 0 < ownProb p.mass i) :
    (∀ i, ownProb p.mass i = exposureProb p.mass (exposure A.adj) i .d11 +
      exposureProb p.mass (exposure A.adj) i .d10) ∧
    expect p.mass (naiveTreated p.mass A.adj y) = mean (fun i =>
      (exposureProb p.mass (exposure A.adj) i .d11/ownProb p.mass i)*y i .d11 +
      (exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i)*y i .d10) ∧
    expect p.mass (naiveTreated p.mass A.adj y)-mean (fun i => y i .d11) =
      -mean (fun i => (exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i)*(y i .d11-y i .d10)) ∧
    ((∀ i, y i .d10 ≤ y i .d11) →
      expect p.mass (naiveTreated p.mass A.adj y) ≤ mean (fun i => y i .d11) ∧
      (expect p.mass (naiveTreated p.mass A.adj y) < mean (fun i => y i .d11) ↔
        ∃ i, 0 < exposureProb p.mass (exposure A.adj) i .d10 ∧ y i .d10 < y i .d11)) ∧
    ((∀ i, y i .d11 ≤ y i .d10) →
      mean (fun i => y i .d11) ≤ expect p.mass (naiveTreated p.mass A.adj y)) ∧
    ((∀ i, 0 < exposureProb p.mass (exposure A.adj) i .d11 ∧
      0 < exposureProb p.mass (exposure A.adj) i .d10) →
      expect p.mass (fun z => (htTotal p.mass (exposure A.adj) y .d11 z +
        htTotal p.mass (exposure A.adj) y .d10 z)/n) =
          mean (fun i => y i .d11)+mean (fun i => y i .d10)) := by
  classical
  have hN : (0 : ℝ)<n := by exact_mod_cast hn
  have hpart : ∀ i, ownProb p.mass i = exposureProb p.mass (exposure A.adj) i .d11 +
      exposureProb p.mass (exposure A.adj) i .d10 := by
    intro i
    unfold ownProb exposureProb prob
    rw [← expect_add]
    apply congrArg (expect p.mass)
    funext z
    unfold exposure
    cases hz : z i <;> by_cases h : ∃ j, A.adj i j=true ∧ z j=true <;> simp [hz,h]
  have hmean : expect p.mass (naiveTreated p.mass A.adj y) = mean (fun i =>
      (exposureProb p.mass (exposure A.adj) i .d11/ownProb p.mass i)*y i .d11 +
      (exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i)*y i .d10) := by
    have hf : naiveTreated p.mass A.adj y = repairedExpansion p.mass A.adj y :=
      funext (naive_expansion_correct p.mass A.adj y)
    rw [hf]
    unfold repairedExpansion
    rw [expect_mean]
    apply congrArg mean
    funext i
    rw [expect_add,expect_event_constant,expect_event_constant]
    simp only [exposureProb]
    ring
  have hweights : ∀ i,
      exposureProb p.mass (exposure A.adj) i .d11/ownProb p.mass i +
      exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i = 1 := by
    intro i
    rw [← add_div,← hpart i]
    exact div_self (ne_of_gt (hp i))
  have hbias : expect p.mass (naiveTreated p.mass A.adj y)-mean (fun i => y i .d11) =
      -mean (fun i => (exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i)*
        (y i .d11-y i .d10)) := by
    rw [hmean,← mean_sub,← mean_neg]
    apply congrArg mean
    funext i
    calc
      _ = (exposureProb p.mass (exposure A.adj) i .d11/ownProb p.mass i +
          exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i-1)*y i .d11 -
          (exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i)*(y i .d11-y i .d10) := by ring
      _ = _ := by rw [hweights]; ring
  have hc : ∀ i, 0 ≤ exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i := by
    intro i
    exact div_nonneg (prob_nonneg p _) (le_of_lt (hp i))
  refine ⟨hpart,hmean,hbias,?_,?_,?_⟩
  · intro hy
    have hterms : ∀ i, 0 ≤ (exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i)*
        (y i .d11-y i .d10) := fun i => mul_nonneg (hc i) (sub_nonneg.mpr (hy i))
    have hm := mean_nonneg _ hterms
    have hpos : 0 < mean (fun i => (exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i)*
        (y i .d11-y i .d10)) ↔
        ∃ i, 0 < exposureProb p.mass (exposure A.adj) i .d10 ∧ y i .d10 < y i .d11 := by
      unfold mean
      simp only [Fintype.card_fin]
      rw [div_pos_iff_of_pos_right hN,Finset.sum_pos_iff_of_nonneg (fun i hi => hterms i)]
      constructor
      · rintro ⟨i,hi,hterm⟩
        have hd : 0 ≤ y i .d11-y i .d10 := sub_nonneg.mpr (hy i)
        have hcp : 0 < exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i := by
          nlinarith [hc i]
        have hdp : 0 < y i .d11-y i .d10 := by nlinarith [hc i]
        exact ⟨i,(div_pos_iff_of_pos_right (hp i)).mp hcp,by linarith⟩
      · rintro ⟨i,hpi,hyi⟩
        exact ⟨i,mem_univ _,mul_pos (div_pos hpi (hp i)) (sub_pos.mpr hyi)⟩
    refine ⟨by linarith,?_⟩
    constructor
    · intro hlt; apply hpos.mp; linarith
    · intro hex; have := hpos.mpr hex; linarith
  · intro hy
    have hm := mean_nonpos (fun i => (exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i)*
      (y i .d11-y i .d10)) (fun i => mul_nonpos_of_nonneg_of_nonpos (hc i) (sub_nonpos.mpr (hy i)))
    linarith
  · intro h
    rw [expect_div,expect_add,ht_total_unbiased p (exposure A.adj) y .d11 (fun i => (h i).1),
      ht_total_unbiased p (exposure A.adj) y .d10 (fun i => (h i).2)]
    simp [mean,add_div]

/-- T13(f): opposite unit-level spillovers in the adjacent two-unit
witness. Untreated outcomes are zero. -/
def cancellingOut2 (i : Fin 2) (d : Exposure) : ℝ :=
  match d with
  | .d11 => if i=0 then 2 else 1
  | .d10 => if i=0 then 1 else 2
  | .d01 | .d00 => 0

/-- T13(f): differences at both units can cancel. The four naive
estimates are 0,2,1,3 and their exact expectation is the target 3/2. -/
theorem spillover_cancellation_instance :
    (∀ i : Fin 2, cancellingOut2 i .d11 ≠ cancellingOut2 i .d10) ∧
    naiveTreated (bernoulli (1/2)) edge2 cancellingOut2 ![false,false] = 0 ∧
    naiveTreated (bernoulli (1/2)) edge2 cancellingOut2 ![false,true] = 2 ∧
    naiveTreated (bernoulli (1/2)) edge2 cancellingOut2 ![true,false] = 1 ∧
    naiveTreated (bernoulli (1/2)) edge2 cancellingOut2 ![true,true] = 3 ∧
    expect (bernoulli (1/2)) (naiveTreated (bernoulli (1/2)) edge2 cancellingOut2) = 3/2 ∧
    mean (fun i : Fin 2 => cancellingOut2 i .d11) = 3/2 := by
  norm_num [naiveTreated, cancellingOut2, edge2, exposure, ownProb, prob,
    expect, bernoulli, mean, sum_tuple_succ, Fin.sum_univ_succ, Fin.prod_univ_succ]

/-- Subgroup pooling notation A,B,a,b in T14–T15 (p. 312). -/
def pooledMean (a b : ℕ) (A B : ℝ) : Option ℝ :=
  if a+b=0 then none else some ((A+B)/(a+b : ℕ))
/-- "A/a+B/b" (T14 notation, p. 312): the sum of separately normalized subclass means is undefined if either required subclass is empty. -/
def printedPool (a b : ℕ) (A B : ℝ) : Option ℝ :=
  if a=0 ∨ b=0 then none else some (A/a+B/b)

/-- T14(i)–(iii),(v): explicit six-group means from the 450-unit witness
give unequal treated/control pooled means and unequal direct contrasts.
Also states the general algebraic error with positive subgroup counts. -/
theorem pooling_counterexample :
    pooledMean 2 1 (9/2) 2 = some (13/6) ∧ printedPool 2 1 (9/2) 2 = some (17/4) ∧
    pooledMean 2 1 (11/4) (5/4) = some (4/3) ∧ printedPool 2 1 (11/4) (5/4) = some (21/8) ∧
    (13/6 : ℝ)-4/3 = 5/6 ∧ (17/4 : ℝ)-21/8 = 13/8 ∧
    (∀ a b : ℕ, 0 < a → 0 < b → ∀ A B : ℝ,
      A/a+B/b-(A+B)/(a+b : ℕ) =
        (b : ℝ)*A/((a : ℝ)*(a+b : ℕ)) + (a : ℝ)*B/((b : ℝ)*(a+b : ℕ))) := by
  norm_num [pooledMean, printedPool]
  intro a b ha hb A B
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  have hab' : ((a+b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.add_pos_left ha b)
  push_cast
  field_simp
  <;> ring

/-- Paired tracts (1,2),(3,4),(5,6), used in T14–T15's twenty first-stage
assignments. partner swaps each adjacent pair. -/
def tractPartner (g : Fin 6) : Fin 6 :=
  ![1,0,3,2,5,4] g
/-- "S_g=ψψ" (p. 312 contextual shorthand): among the own-ψ groups, count those whose tract partner also has ψ (T14–T15). -/
def sameRegimeCount (H : Finset (Fin 6)) : ℕ := (H.filter (fun g => tractPartner g ∈ H)).card

/-- T14's 450-unit witness: 75 units in each of six groups. Groups
1–3 treat their first 50 units and groups 4–6 their first 25, giving
the specified 2/3 and 1/3 saturations (pp. 311–312). -/
def tractWitnessAssignment (g : Fin 6) : Assignment 75 :=
  fun i => decide (i.val < if g.val < 3 then 50 else 25)

/-- The baseline-one tract schedule fixed in T14: for total tract
counts 100, 75, 50 the untreated/treated multipliers are respectively
(11/8,9/4), (5/4,2), (1,3/2). Other tract counts use the last pair.
The function depends only on own treatment and the number treated in
the focal tract, and therefore enforces the stated tract interference. -/
def tractOutcome (w : Fin 6 → Assignment 75) (g : Fin 6) (i : Fin 75) : ℝ :=
  let k := treatedCount (w g)+treatedCount (w (tractPartner g))
  if w g i then (if k=100 then 9/4 else if k=75 then 2 else 3/2)
  else (if k=100 then 11/8 else if k=75 then 5/4 else 1)

/-- Observed within-arm means m_g of p. 310 in the T14 tract witness.
Outcomes are generated from the whole tract assignment before the arm mask. -/
def tractObservedArm (w : Fin 6 → Assignment 75) (g : Fin 6) (b : Bool) : ℝ :=
  armMean (fun i _ => tractOutcome w g i) b (w g)

/-- A nonempty observed arm whose outcomes are all c has sample mean c;
this supporting identity verifies the group means in T14's full population. -/
theorem observed_arm_constant {n : ℕ} (z : Assignment n) (b : Bool) (X : Fin n → ℝ)
    (c : ℝ) (hX : ∀ i, z i=b → X i=c) (hex : armExists b z) :
    armMean (fun i _ => X i) b z=c := by
  obtain ⟨i,hi⟩ := hex
  have hcard : 0 < (univ.filter (fun j => z j=b)).card :=
    Finset.card_pos.2 ⟨i,by simp [hi]⟩
  have hden : (∑ j, if z j=b then (1 : ℝ) else 0) ≠ 0 := by
    simp only [Finset.sum_ite,Finset.sum_const_zero,sub_zero,Finset.sum_const,
      nsmul_eq_mul,mul_one]
    exact_mod_cast Nat.ne_of_gt hcard
  have hnum : (∑ j, if z j=b then X j else 0) =
      (∑ j, if z j=b then (1 : ℝ) else 0)*c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : z j=b <;> simp [h,hX j]
  unfold armMean
  rw [hnum]
  field_simp

/-- Every assignment in the nonempty fixed-count support has strictly
positive complete-randomization mass (pp. 292, 309–310). This generic
certificate avoids evaluating a large Boolean assignment universe. -/
theorem cr_mass_positive {n k : ℕ} (z : Assignment n) (hz : z ∈ fixedAssignments n k) :
    0 < crMass n k z := by
  rw [crMass,if_pos hz]
  apply one_div_pos.mpr
  exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨z,hz⟩)

/-- Membership in the actual complete-randomization support is exactly
the fixed treated-count condition (pp. 292, 309–310). -/
theorem mem_fixed_assignments_iff {n k : ℕ} (z : Assignment n) :
    z ∈ fixedAssignments n k ↔ treatedCount z=k := by
  simp [fixedAssignments,treatedCount]

attribute [local irreducible] fixedAssignments
set_option maxRecDepth 4096 in
/-- T14's full population certificate: 450 actual units, admissible
fixed counts in every group, the specified first stage, and arm means
generated from the baseline-one tract schedule. Together with
`pooling_counterexample`, this verifies the concrete hypotheses behind
the unequal pooled means and direct contrasts. -/
theorem pooling_population_counterexample :
    Fintype.card (Fin 6 × Fin 75)=450 ∧
    ({0,1,2} : Finset (Fin 6)) ∈ firstStageSets 6 3 ∧
    (({0,1,2} : Finset (Fin 6)).filter (fun g => tractPartner g ∈ ({0,1,2} : Finset (Fin 6))))={0,1} ∧
    (({0,1,2} : Finset (Fin 6)).filter (fun g => tractPartner g ∉ ({0,1,2} : Finset (Fin 6))))={2} ∧
    (∀ g : Fin 6, treatedCount (tractWitnessAssignment g)=(if g.val<3 then 50 else 25) ∧
      0 < crMass 75 (if g.val<3 then 50 else 25) (tractWitnessAssignment g)) ∧
    (∀ g : Fin 6, g.val<3 → ∀ b : Bool,
      tractObservedArm tractWitnessAssignment g b =
        if g.val<2 then (if b then 9/4 else 11/8) else (if b then 2 else 5/4)) ∧
    pooledMean 2 1
      (∑ g ∈ ({0,1} : Finset (Fin 6)), tractObservedArm tractWitnessAssignment g true)
      (tractObservedArm tractWitnessAssignment 2 true)=some (13/6) ∧
    printedPool 2 1
      (∑ g ∈ ({0,1} : Finset (Fin 6)), tractObservedArm tractWitnessAssignment g true)
      (tractObservedArm tractWitnessAssignment 2 true)=some (17/4) ∧
    pooledMean 2 1
      (∑ g ∈ ({0,1} : Finset (Fin 6)), tractObservedArm tractWitnessAssignment g false)
      (tractObservedArm tractWitnessAssignment 2 false)=some (4/3) ∧
    printedPool 2 1
      (∑ g ∈ ({0,1} : Finset (Fin 6)), tractObservedArm tractWitnessAssignment g false)
      (tractObservedArm tractWitnessAssignment 2 false)=some (21/8) := by
  have hcount : ∀ g : Fin 6, treatedCount (tractWitnessAssignment g)=
      (if g.val<3 then 50 else 25) := by decide
  have hmeans : ∀ g : Fin 6, g.val<3 → ∀ b : Bool,
      tractObservedArm tractWitnessAssignment g b =
        if g.val<2 then (if b then 9/4 else 11/8) else (if b then 2 else 5/4) := by
    intro g hg b
    fin_cases g
    all_goals norm_num at hg
    all_goals cases b
    all_goals norm_num
    all_goals apply observed_arm_constant
    all_goals try { intro i hi; simp [tractOutcome,hi,hcount,tractPartner] }
    all_goals first | exact ⟨74,by decide⟩ | exact ⟨0,by decide⟩
  refine ⟨by simp,by decide,by decide,by decide,?_,hmeans,?_,?_,?_,?_⟩
  · intro g
    refine ⟨hcount g,?_⟩
    have hm : tractWitnessAssignment g ∈ fixedAssignments 75 (if g.val<3 then 50 else 25) :=
      (mem_fixed_assignments_iff (n := 75) (k := if g.val<3 then 50 else 25)
        (tractWitnessAssignment g)).2 (hcount g)
    exact cr_mass_positive (tractWitnessAssignment g) hm
  all_goals
    have h0 := hmeans 0 (by decide)
    have h1 := hmeans 1 (by decide)
    have h2 := hmeans 2 (by decide)
    norm_num [pooledMean,printedPool,h0,h1,h2]

/-- T14(iv): eight of twenty assignments have a=0,b=3; the printed
separate subgroup ratio is undefined there, while the pooled ratio exists. -/
theorem pooling_empty_subclass :
    (firstStageSets 6 3).card = 20 ∧
    ((firstStageSets 6 3).filter (fun H => sameRegimeCount H=0)).card = 8 ∧
    (∀ H ∈ firstStageSets 6 3, sameRegimeCount H=0 ∨ sameRegimeCount H=2) ∧
    (∀ B : ℝ, printedPool 0 3 0 B = none ∧ pooledMean 0 3 0 B = some (B/3)) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro B
  simp [printedPool, pooledMean]

/-- T14(iv), T15(c): a 64-set certificate for the twenty admissible first
stages: eight have zero same-regime partners and twelve have two. -/
theorem tract_count_certificate :
    ((firstStageSets 6 3).filter (fun H => sameRegimeCount H=0)).card = 8 ∧
    ((firstStageSets 6 3).filter (fun H => sameRegimeCount H≠0)).card = 12 ∧
    (∀ H ∈ firstStageSets 6 3, sameRegimeCount H=0 ∨ sameRegimeCount H=2) := by
  decide

/-- T15(a)–(b): the repair is one pooled ratio on the domain a+b>0.
It equals the group-share weighted mixture when both subgroups exist and
remains defined when the first subgroup is empty (p. 312 correction). -/
theorem pooled_ratio_correction (a b : ℕ) (A B : ℝ) (hab : 0 < a+b) :
    pooledMean a b A B = some ((A+B)/(a+b : ℕ)) ∧
    (0 < a → 0 < b → (A+B)/(a+b : ℕ) =
      (a : ℝ)/(a+b : ℕ)*(A/a)+(b : ℝ)/(a+b : ℕ)*(B/b)) ∧
    (a=0 → A=0 → pooledMean a b A B = some (B/b)) := by
  constructor
  · simp only [pooledMean]
    rw [if_neg (Nat.ne_of_gt hab)]
  constructor
  · intro ha hb
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
    have hab' : ((a+b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hab
    field_simp
    <;> ring
  · rintro rfl rfl
    simp [pooledMean, show b ≠ 0 by omega]

/-- T15(a): the own-ψ groups are exactly the disjoint union of the ψψ
and ψφ subclasses. The pooled count and numerator are their sums. -/
theorem tract_partition (H : Finset (Fin 6)) (m : Fin 6 → ℝ) :
    H.card = (H.filter (fun g => tractPartner g ∈ H)).card +
      (H.filter (fun g => tractPartner g ∉ H)).card ∧
    (∑ g ∈ H, m g) = (∑ g ∈ H.filter (fun g => tractPartner g ∈ H), m g) +
      (∑ g ∈ H.filter (fun g => tractPartner g ∉ H), m g) := by
  constructor
  · exact (Finset.card_filter_add_card_filter_not _).symm
  · exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- T15(c): exact misspecified-partial-interference bias in the twenty
first-stage choices. The subgroup mean contrasts are 7/8 and 3/4, giving
expectation 4/5 against the ψψ target 7/8. -/
theorem tract_mixture_bias :
    average (firstStageSets 6 3) (fun H => (sameRegimeCount H : ℝ)/3) = 2/5 ∧
    average (firstStageSets 6 3) (fun H => (3-(sameRegimeCount H : ℝ))/3) = 3/5 ∧
    average (firstStageSets 6 3) (fun H =>
      ((sameRegimeCount H : ℝ)/3)*(7/8) + ((3-(sameRegimeCount H : ℝ))/3)*(3/4)) = 4/5 ∧
    (4/5 : ℝ)-7/8 = -3/40 := by
  have havg : ∀ F : ℕ → ℝ, average (firstStageSets 6 3) (fun H => F (sameRegimeCount H)) =
      (8*F 0+12*F 2)/20 := by
    intro F
    rw [average_two_values (firstStageSets 6 3) (fun H => sameRegimeCount H=0)
      (fun H => F (sameRegimeCount H)) (F 0) (F 2)]
    · simp [tract_count_certificate.1, tract_count_certificate.2.1, pooling_empty_subclass.1]
    · intro H hH
      rcases tract_count_certificate.2.2 H hH with h | h
      · simp [h]
      · simp [h]
  constructor
  · rw [havg (fun k => (k : ℝ)/3)]; norm_num
  constructor
  · rw [havg (fun k => (3-(k : ℝ))/3)]; norm_num
  constructor
  · rw [havg (fun k => ((k : ℝ)/3)*(7/8)+((3-(k : ℝ))/3)*(3/4))]; norm_num
  · norm_num

/-- Dilated four-exposure outcomes, multipliers (2,3/2,5/4,1) from
p. 298. Reused with T8's and T16's explicit baseline schedules. -/
def dilated (b : ℝ) (d : Exposure) : ℝ :=
  match d with | .d11 => 2*b | .d10 => (3/2)*b | .d01 => (5/4)*b | .d00 => b
/-- "yhat^T_HT(d_k)=∑ I(D_i=d_k)Y_i/π_i(d_k)" (p. 297), evaluated with the exact pair-design probabilities for T16. -/
def pairHT (A : Fin 10 → Fin 10 → Bool) (y : Fin 10 → Exposure → ℝ)
    (d : Exposure) (e : Fin 10 × Fin 10) : ℝ :=
  ∑ i, if exposure A (pairAssignment e) i = d then y i d/pairExposureProb A i d else 0
/-- "(1/N)[yhat^T_HT(d_k)−yhat^T_HT(d_l)]" (p. 297), with N=10, the printed network and baseline-one dilated schedule (T16). -/
def printedContrast (e : Fin 10 × Fin 10) : ℝ :=
  (pairHT printedAdj (fun _ => dilated 1) .d11 e - pairHT printedAdj (fun _ => dilated 1) .d00 e)/10
/-- "no unit received exposure d11" (p. 298): the complementary event that some unit in the pair assignment has the indicated exposure. -/
def pairCellNonempty (d : Exposure) (e : Fin 10 × Fin 10) : Prop :=
  ∃ i, exposure printedAdj (pairAssignment e) i = d
instance (d : Exposure) (e : Fin 10 × Fin 10) : Decidable (pairCellNonempty d e) :=
  inferInstanceAs (Decidable (∃ i, exposure printedAdj (pairAssignment e) i = d))

set_option maxRecDepth 4096 in
/-- T16(i): all exact exposure probabilities on the printed graph,
proved by small natural-number event counts on its 45 treatment pairs. -/
theorem printed_pair_probabilities :
    ∀ i : Fin 10, let g := (univ.filter (fun j => printedAdj i j=true)).card
      pairExposureProb printedAdj i .d11 = (g : ℝ)/45 ∧
      pairExposureProb printedAdj i .d10 = (9-g : ℕ)/45 ∧
      pairExposureProb printedAdj i .d00 = (Nat.choose (9-g) 2 : ℝ)/45 ∧
      pairExposureProb printedAdj i .d01 = (36-(Nat.choose (9-g) 2 : ℝ))/45 ∧
      (∀ d, 0 < pairExposureProb printedAdj i d) := by
  have hc : treatmentPairs.card=45 := by decide
  have he : ∀ i : Fin 10, let g := (univ.filter (fun j => printedAdj i j=true)).card
      (treatmentPairs.filter (fun e => exposure printedAdj (pairAssignment e) i=.d11)).card = g ∧
      (treatmentPairs.filter (fun e => exposure printedAdj (pairAssignment e) i=.d10)).card = 9-g ∧
      (treatmentPairs.filter (fun e => exposure printedAdj (pairAssignment e) i=.d00)).card = Nat.choose (9-g) 2 ∧
      (treatmentPairs.filter (fun e => exposure printedAdj (pairAssignment e) i=.d01)).card = 36-Nat.choose (9-g) 2 ∧
      Nat.choose (9-g) 2 ≤ 36 := by decide
  have hp : ∀ i d,
      0 < (treatmentPairs.filter (fun e => exposure printedAdj (pairAssignment e) i=d)).card := by decide
  intro i
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [pair_exposure_probability_count, hc, (he i).1, Nat.cast_ofNat]
  · simp only [pair_exposure_probability_count, hc, (he i).2.1, Nat.cast_ofNat]
  · simp only [pair_exposure_probability_count, hc, (he i).2.2.1, Nat.cast_ofNat]
  · simp only [pair_exposure_probability_count, hc, (he i).2.2.2.1,
      Nat.cast_sub (he i).2.2.2.2, Nat.cast_ofNat]
  · intro d
    rw [pair_exposure_probability_count, hc]
    exact div_pos (Nat.cast_pos.mpr (hp i d)) (by norm_num)

/-- Integer arithmetic certificate for T16: twice an included unit's HT
weight is 180/degree for d11 and 90/choose(9−degree,2) for d00. All these
integer quotients are exact for the printed degrees (3,4,6,5,5,3,3,4,4,3). -/
def printedHalfWeight (d : Exposure) (i : Fin 10) : ℕ :=
  let g := (univ.filter (fun j => printedAdj i j=true)).card
  if d=.d11 then 180/g else 90/(Nat.choose (9-g) 2)

/-- T16 arithmetic certificate: a natural-number sum encoding twice the
real HT total. Its equality to the paper's estimator is proved below. -/
def printedPairCertificate (d : Exposure) (e : Fin 10 × Fin 10) : ℕ :=
  ∑ i, if exposure printedAdj (pairAssignment e) i=d then printedHalfWeight d i else 0

/-- T16: the printed degrees and the exact integer HT weights. These
Boolean/natural certificates avoid expanding real arithmetic on the graph. -/
theorem printed_weight_certificates :
    (∀ i : Fin 10, (univ.filter (fun j => printedAdj i j=true)).card =
      ![3,4,6,5,5,3,3,4,4,3] i) ∧
    (∀ i : Fin 10, printedHalfWeight .d11 i = ![60,45,30,36,36,60,60,45,45,60] i ∧
      printedHalfWeight .d00 i = ![6,9,30,15,15,6,6,9,9,6] i) := by
  decide

/-- T16: the integer certificate equals twice the actual real HT total,
for both exposure conditions used in the target contrast. -/
theorem printed_pair_total_certificate (e : Fin 10 × Fin 10) :
    pairHT printedAdj (fun _ => dilated 1) .d11 e = (printedPairCertificate .d11 e : ℝ)/2 ∧
    pairHT printedAdj (fun _ => dilated 1) .d00 e = (printedPairCertificate .d00 e : ℝ)/2 := by
  have h1 : ∀ i : Fin 10, (2 : ℝ)/pairExposureProb printedAdj i .d11 =
      (printedHalfWeight .d11 i : ℝ)/2 := by
    intro i
    rw [(printed_pair_probabilities i).1, printed_weight_certificates.1 i,
      (printed_weight_certificates.2 i).1]
    fin_cases i <;> norm_num
  have h0 : ∀ i : Fin 10, (1 : ℝ)/pairExposureProb printedAdj i .d00 =
      (printedHalfWeight .d00 i : ℝ)/2 := by
    intro i
    rw [(printed_pair_probabilities i).2.2.1, printed_weight_certificates.1 i,
      (printed_weight_certificates.2 i).2]
    fin_cases i <;> norm_num [Nat.choose]
  constructor <;> simp only [pairHT, dilated, mul_one]
  · simp_rw [h1]
    simp only [printedPairCertificate, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_div, ite_div, zero_div]
  · simp_rw [h0]
    simp only [printedPairCertificate, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_div, ite_div, zero_div]

/-- T16: a uniform average of actual real HT totals equals the average
of their certified integer numerators divided by two. -/
theorem printed_pair_average_certificate (S : Finset (Fin 10 × Fin 10)) :
    average S (pairHT printedAdj (fun _ => dilated 1) .d11) =
      (∑ e ∈ S, printedPairCertificate .d11 e : ℕ)/2/S.card ∧
    average S (pairHT printedAdj (fun _ => dilated 1) .d00) =
      (∑ e ∈ S, printedPairCertificate .d00 e : ℕ)/2/S.card := by
  constructor <;> unfold average
  · simp_rw [(printed_pair_total_certificate _).1]
    simp only [Nat.cast_sum, Finset.sum_div]
  · simp_rw [(printed_pair_total_certificate _).2]
    simp only [Nat.cast_sum, Finset.sum_div]

/-- T16: averaging the printed contrast commutes with its difference
and its factor 1/10. No realized exposure cell has been discarded here. -/
theorem printed_contrast_average (S : Finset (Fin 10 × Fin 10)) :
    average S printedContrast =
      (average S (pairHT printedAdj (fun _ => dilated 1) .d11) -
        average S (pairHT printedAdj (fun _ => dilated 1) .d00))/10 := by
  simp [average, printedContrast, Finset.sum_sub_distrib, ← Finset.sum_div,
    div_sub_div_same, div_div, mul_comm]

set_option maxRecDepth 4096 in
/-- T16(i)–(iv): the printed nonadjacent treatment of units 6 and 9 gives
HT contrast −3/4, not NA. Discarding empty cells changes the means;
all exact positive exposure probabilities and both conditioning events
are included (p. 298 correction). -/
theorem empty_cell_counterexample :
    (∀ i : Fin 10, let g := (univ.filter (fun j => printedAdj i j=true)).card
      pairExposureProb printedAdj i .d11 = (g : ℝ)/45 ∧
      pairExposureProb printedAdj i .d10 = (9-g : ℕ)/45 ∧
      pairExposureProb printedAdj i .d00 = (Nat.choose (9-g) 2 : ℝ)/45 ∧
      pairExposureProb printedAdj i .d01 = (36-(Nat.choose (9-g) 2 : ℝ))/45 ∧
      (∀ d, 0 < pairExposureProb printedAdj i d)) ∧
    ¬pairCellNonempty .d11 (5,8) ∧
    (∀ i : Fin 10, exposure printedAdj (pairAssignment (5,8)) i = .d00 ↔ i=0 ∨ i=1) ∧
    pairHT printedAdj (fun _ => dilated 1) .d11 (5,8) = 0 ∧
    pairHT printedAdj (fun _ => dilated 1) .d00 (5,8) = 15/2 ∧
    printedContrast (5,8) = -3/4 ∧
    (treatmentPairs.filter (pairCellNonempty .d11)).card = 20 ∧
    (treatmentPairs.filter (fun e => pairCellNonempty .d11 e ∧ pairCellNonempty .d00 e)).card = 19 ∧
    average treatmentPairs (pairHT printedAdj (fun _ => dilated 1) .d11) = 20 ∧
    average (treatmentPairs.filter (pairCellNonempty .d11)) (pairHT printedAdj (fun _ => dilated 1) .d11) = 45 ∧
    average treatmentPairs printedContrast = 1 ∧
    average (treatmentPairs.filter (pairCellNonempty .d11)) printedContrast = 651/200 ∧
    average (treatmentPairs.filter (fun e => pairCellNonempty .d11 e ∧ pairCellNonempty .d00 e)) printedContrast = 1227/380 := by
  have hcard : treatmentPairs.card=45 := by decide
  have h11 : (treatmentPairs.filter (pairCellNonempty .d11)).card=20 := by decide
  have hboth : (treatmentPairs.filter (fun e => pairCellNonempty .d11 e ∧ pairCellNonempty .d00 e)).card=19 := by decide
  have hs :
      (∑ e ∈ treatmentPairs, printedPairCertificate .d11 e)=1800 ∧
      (∑ e ∈ treatmentPairs, printedPairCertificate .d00 e)=900 ∧
      (∑ e ∈ treatmentPairs.filter (pairCellNonempty .d11), printedPairCertificate .d11 e)=1800 ∧
      (∑ e ∈ treatmentPairs.filter (pairCellNonempty .d11), printedPairCertificate .d00 e)=498 ∧
      (∑ e ∈ treatmentPairs.filter (fun e => pairCellNonempty .d11 e ∧ pairCellNonempty .d00 e),
        printedPairCertificate .d11 e)=1725 ∧
      (∑ e ∈ treatmentPairs.filter (fun e => pairCellNonempty .d11 e ∧ pairCellNonempty .d00 e),
        printedPairCertificate .d00 e)=498 := by decide
  refine ⟨printed_pair_probabilities, by decide, by decide, ?_, ?_, ?_,
    h11, hboth, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(printed_pair_total_certificate (5,8)).1]
    have h : printedPairCertificate .d11 (5,8)=0 := by decide
    rw [h]; norm_num
  · rw [(printed_pair_total_certificate (5,8)).2]
    have h : printedPairCertificate .d00 (5,8)=15 := by decide
    rw [h]; norm_num
  · unfold printedContrast
    rw [(printed_pair_total_certificate (5,8)).1, (printed_pair_total_certificate (5,8)).2]
    have h : printedPairCertificate .d11 (5,8)=0 ∧ printedPairCertificate .d00 (5,8)=15 := by decide
    rw [h.1,h.2]; norm_num
  · rw [(printed_pair_average_certificate treatmentPairs).1, hs.1, hcard]; norm_num
  · rw [(printed_pair_average_certificate _).1, hs.2.2.1, h11]; norm_num
  · rw [printed_contrast_average, (printed_pair_average_certificate _).1,
      (printed_pair_average_certificate _).2, hs.1, hs.2.1, hcard]; norm_num
  · rw [printed_contrast_average, (printed_pair_average_certificate _).1,
      (printed_pair_average_certificate _).2, hs.2.2.1, hs.2.2.2.1, h11]; norm_num
  · rw [printed_contrast_average, (printed_pair_average_certificate _).1,
      (printed_pair_average_certificate _).2, hs.2.2.2.2.1, hs.2.2.2.2.2, hboth]; norm_num

/-- T17(c): conditioning an unbiased HT total on a nonempty exposure cell
inflates its mean by 1/Pr(nonempty). Empty cells have not been discarded
from the expectation in T30. -/
theorem nonempty_ht_conditional {n : ℕ} (p : Design (Assignment n))
    (D : Assignment n → Fin n → Exposure) (y : Fin n → Exposure → ℝ)
    (k : Exposure) (hk : ∀ i, 0 < exposureProb p.mass D i k)
    (hcell : 0 < prob p.mass (fun z => ∃ i, D z i=k)) :
    condMean p.mass (fun z => ∃ i, D z i=k) (htTotal p.mass D y k) =
      (∑ i, y i k)/prob p.mass (fun z => ∃ i, D z i=k) := by
  unfold condMean
  apply congrArg (fun v : ℝ => v / prob p.mass (fun z => ∃ i, D z i=k))
  calc
    _ = expect p.mass (htTotal p.mass D y k) := by
      unfold expect
      apply Finset.sum_congr rfl
      intro z hzmem
      by_cases hz : ∃ i, D z i=k
      · simp [hz]
      · have he : ∀ i, D z i ≠ k := by simpa using hz
        simp [hz,htTotal,he]
    _ = _ := ht_total_unbiased p D y k hk


/-- Corrected vector z_{−i}: remove coordinate i and retain the original
order, with empty prefixes/suffixes at endpoints (p. 292, T18). -/
def withoutCoordinate {n : ℕ} (i : Fin (n+1)) (z : Assignment (n+1)) : Assignment n :=
  i.removeNth z
/-- "y_i(z) can equivalently be expressed as y_i(z_i;z_{−i})" (p. 292): the coordinate/remnant bijection preserving original order (T18). -/
def splitAssignment {n : ℕ} (i : Fin (n+1)) : Assignment (n+1) ≃ Bool × Assignment n :=
  (Fin.insertNthEquiv (fun _ : Fin (n+1) => Bool) i).symm

/-- T18(i)–(iii): the corrected ordered vector does not depend on own
treatment and splitting off own treatment is a bijection. -/
theorem coordinate_removal_correct {n : ℕ} (i : Fin (n+1)) :
    (∀ z : Assignment (n+1), ∀ j : Fin n,
      withoutCoordinate i z j = if j.val < i.val then z j.castSucc else z j.succ) ∧
    (∀ z z' : Assignment (n+1), (∀ j, j ≠ i → z j=z' j) →
      withoutCoordinate i z=withoutCoordinate i z') ∧
    Function.Bijective (fun z : Assignment (n+1) => (z i, withoutCoordinate i z)) := by
  constructor
  · intro z j
    unfold withoutCoordinate Fin.removeNth
    by_cases h : j.val < i.val
    · rw [if_pos h, Fin.succAbove_of_castSucc_lt]
      exact h
    · rw [if_neg h, Fin.succAbove_of_le_castSucc]
      exact Nat.le_of_not_gt h
  constructor
  · intro z z' h
    funext j
    exact h _ (Fin.succAbove_ne i j)
  · exact (splitAssignment i).bijective

/-- T18(iii): exactly one reindexed potential-outcome function realizes
y_i(z)=y_i(z_i;z_{−i}), including arbitrary assignment-level outcomes. -/
theorem reindexed_outcome_unique {n : ℕ} (i : Fin (n+1)) (y : Assignment (n+1) → ℝ) :
    ∃! f : Bool × Assignment n → ℝ, ∀ z, f (z i, withoutCoordinate i z)=y z := by
  let e := splitAssignment i
  refine ⟨fun x => y (e.symm x), ?_, ?_⟩
  · intro z
    change y (e.symm (e z))=y z
    simp
  · intro f hf
    funext x
    have h := hf (e.symm x)
    change f (e (e.symm x))=y (e.symm x) at h
    simpa using h

/-- T18(iv): removing coordinate 3 from four coordinates gives (z1,z2,z4). -/
theorem coordinate_removal_instance (z : Assignment 4) :
    withoutCoordinate 2 z = ![z 0,z 1,z 3] := by
  funext j
  fin_cases j <;> rfl

/-- T19: with fixed integer K=ψ n_g, treated units face ψ n_g−1 treated
peers, controls ψ n_g. The misprinted ψ(n_g−1) exceeds the treated count
by 1−ψ>0. All original size and saturation restrictions are retained. -/
theorem fixed_count_peers_correct {n K : ℕ} (hn : 2 ≤ n) (ψ : ℝ)
    (hψ : 0 < ψ) (hψ1 : ψ < 1) (hK : (K : ℝ)=ψ*n)
    (z : Assignment n) (hz : treatedCount z=K) (i : Fin n) :
    coMembers i z = (K : ℝ)-bit (z i) ∧
    (z i=true → coMembers i z=ψ*n-1 ∧ ψ*(n-1)-coMembers i z=1-ψ ∧
      coMembers i z < ψ*(n-1)) ∧
    (z i=false → coMembers i z=ψ*n) := by
  have h := co_members_count z i
  rw [hz] at h
  refine ⟨h, ?_, ?_⟩
  · intro hi
    rw [hK,hi,bit] at h
    simp only [if_true] at h
    refine ⟨h, ?_, ?_⟩ <;> linarith
  · intro hi
    simpa [hK,hi,bit] using h

/-- Convergence in probability for varying finite designs, the asymptotic
scale relevant to p. 299 (T22–T23). The sample spaces may grow with N. -/
def InProbability {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (p : (n : ℕ) → Ω n → ℝ) (X : (n : ℕ) → Ω n → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n => prob (p n) (fun w => ε < |X n w-a n|))
    Filter.atTop (nhds 0)

/-- Independent fair signs and their mean T_N, T22's explicit inference
counterexample. N=n+1 is always positive; the first sign also defines B. -/
def sign (b : Bool) : ℝ := if b then 1 else -1
/-- "T_N=(1/N)∑ X_j" (T22 setting): the actual mean of N independent fair signs in the explicit counterexample. -/
def signMean {n : ℕ} (z : Assignment n) : ℝ := mean (fun i => sign (z i))

/-- Unnormalized sum of the independent fair signs in T22's sample
mean; introduced only to state its exact finite second moment. -/
def signSum {n : ℕ} (z : Assignment n) : ℝ := ∑ i, sign (z i)

/-- The sign sum separates the first coin (T22 finite moment proof). -/
theorem sign_sum_cons {n : ℕ} (b : Bool) (u : Assignment n) :
    signSum (Fin.cons (α := fun _ : Fin (n+1) => Bool) b u)=sign b+signSum u := by
  simp [signSum,Fin.sum_univ_succ]

/-- T22(ii): the squared sum of n independent fair signs has expectation
n, with induction over independent coins rather than cube enumeration. -/
theorem sign_sum_second_moment (n : ℕ) :
    expect (bernoulli (1/2)) (fun z : Assignment n => (signSum z)^2)=(n : ℝ) := by
  induction n with
  | zero => simp [signSum,expect]
  | succ n ih =>
    rw [bernoulli_expect_cons]
    simp only [sign_sum_cons,sign,ite_true,Bool.false_eq_true,ite_false]
    calc
      _ = expect (bernoulli (1/2)) (fun z : Assignment n => 1+(signSum z)^2) := by
        unfold expect
        simp only [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _ = 1+(n : ℝ) := by
        unfold expect
        simp only [mul_add,mul_one,Finset.sum_add_distrib,bernoulli_total]
        rw [← expect,ih]
      _ = ((n+1 : ℕ) : ℝ) := by push_cast; ring

/-- T22(ii): the specified sample mean has exact mean zero and variance
1/N at every positive population size N=n+1. -/
theorem sign_mean_finite_moments (n : ℕ) :
    expect (bernoulli (1/2)) (signMean (n := n+1))=0 ∧
    variance (bernoulli (1/2)) (signMean (n := n+1))=1/(n+1 : ℕ) := by
  have hm : expect (bernoulli (1/2)) (signMean (n := n+1))=0 := by
    unfold signMean
    rw [expect_mean]
    have hi : ∀ i : Fin (n+1), expect (bernoulli (1/2)) (fun z : Assignment (n+1) => sign (z i))=0 := by
      intro i
      rw [bernoulli_coordinate_expect (1/2) i sign]
      norm_num [sign]
    simp only [hi]
    simp [mean]
  refine ⟨hm,?_⟩
  unfold variance
  rw [hm]
  simp only [sub_zero,signMean,mean,Fintype.card_fin,div_pow]
  rw [expect_div]
  change expect (bernoulli (1/2)) (fun z : Assignment (n+1) => (signSum z)^2)/(n+1 : ℕ)^2 = _
  rw [sign_sum_second_moment]
  have hN : ((n+1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  field_simp [hN]

/-- T22(iii): finite Chebyshev inequality under the actual design. This
proof is a weighted-sum inequality and assumes the estimator's mean zero. -/
theorem finite_chebyshev_zero_mean {Ω : Type*} [Fintype Ω] (p : Design Ω)
    (X : Ω → ℝ) (hm : expect p.mass X=0) (ε : ℝ) (hε : 0 < ε) :
    prob p.mass (fun w => ε < |X w|) ≤ variance p.mass X/ε^2 := by
  classical
  have hpoint : ∀ w, (if ε < |X w| then ε^2 else 0) ≤ (X w)^2 := by
    intro w
    by_cases h : ε < |X w|
    · simp only [if_pos h]
      have hsq : |X w|^2=(X w)^2 := sq_abs _
      nlinarith [abs_nonneg (X w)]
    · simp only [if_neg h]; exact sq_nonneg _
  have hi : expect p.mass (fun w => if ε < |X w| then ε^2 else 0) ≤
      expect p.mass (fun w => (X w)^2) := by
    unfold expect
    apply Finset.sum_le_sum
    intro w hw
    exact mul_le_mul_of_nonneg_left (hpoint w) (p.nonneg w)
  rw [expect_event_constant] at hi
  have hv : variance p.mass X=expect p.mass (fun w => (X w)^2) := by
    unfold variance; rw [hm]; simp
  rw [← hv] at hi
  exact (le_div_iff₀ (sq_pos_of_pos hε)).2 hi

/-- T23(b2)'s finite Markov inequality: a nonnegative estimator exceeds
a positive threshold with probability at most its mean/threshold. -/
theorem finite_markov_nonneg {Ω : Type*} [Fintype Ω] (p : Design Ω)
    (X : Ω → ℝ) (hX : ∀ w, 0 ≤ X w) (t : ℝ) (ht : 0 < t) :
    prob p.mass (fun w => t < X w) ≤ expect p.mass X/t := by
  classical
  have hpoint : ∀ w, (if t < X w then t else 0) ≤ X w := by
    intro w
    by_cases h : t < X w
    · simp [h,h.le]
    · simp [h,hX w]
  have hi : expect p.mass (fun w => if t < X w then t else 0) ≤ expect p.mass X := by
    unfold expect
    apply Finset.sum_le_sum
    intro w hw
    exact mul_le_mul_of_nonneg_left (hpoint w) (p.nonneg w)
  rw [expect_event_constant] at hi
  exact (le_div_iff₀ ht).2 hi

/-- T22(iii): explicit 1/(Nε²) deviation bound for the fair-sign sample
mean, using the proved moments at the same population size. -/
theorem sign_mean_chebyshev (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    prob (bernoulli (1/2)) (fun z : Assignment (n+1) => ε < |signMean z|) ≤
      1/((n+1 : ℕ)*ε^2) := by
  have h := finite_chebyshev_zero_mean
    (bernoulliDesign (n+1) (1/2) (by norm_num) (by norm_num)) signMean
    (sign_mean_finite_moments n).1 ε hε
  dsimp only [bernoulliDesign] at h
  rw [(sign_mean_finite_moments n).2] at h
  simpa [div_div,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using h
/-- "B=3/2 when X_1=1 and B=1/2 when X_1=−1" (T22). Its dependence on the first actual sign is retained. -/
def varianceFactor {n : ℕ} (z : Assignment (n+1)) : ℝ := if z 0 then 3/2 else 1/2
/-- "Vhat_N=B²/N" (T22): the explicit nonnegative variance estimator, with N=n+1, on the varying Bernoulli spaces. -/
def varianceWitness (n : ℕ) (z : Assignment (n+1)) : ℝ := (varianceFactor z)^2/(n+1 : ℕ)
/-- "SE_N=sqrt(Vhat_N)" (T22): the reported standard-error estimator of the witness. -/
def seWitness (n : ℕ) (z : Assignment (n+1)) : ℝ := Real.sqrt (varianceWitness n z)

/-- T22's finite obstruction, for every actual population size N=n+1.
The specified Bernoulli law has E(B)=1 and E(B²)=5/4. The expected
standard error is 1/√N, while the variance estimate has positive bias
1/(4N) relative to 1/N and relative error >1/2 with probability one.
The sample-mean variance is established separately in `sign_mean_finite_moments`. -/
theorem mean_se_finite_obstruction (n : ℕ) :
    expect (bernoulli (1/2)) (varianceFactor (n := n))=1 ∧
    expect (bernoulli (1/2)) (fun z : Assignment (n+1) => (varianceFactor z)^2)=5/4 ∧
    (∀ z : Assignment (n+1), seWitness n z=varianceFactor z/Real.sqrt (n+1 : ℕ)) ∧
    expect (bernoulli (1/2)) (seWitness n)=1/Real.sqrt (n+1 : ℕ) ∧
    expect (bernoulli (1/2)) (varianceWitness n)-1/(n+1 : ℕ)=1/(4*(n+1 : ℕ)) ∧
    prob (bernoulli (1/2)) (fun z : Assignment (n+1) =>
      1/2 < |varianceWitness n z/(1/(n+1 : ℕ))-1|)=1 := by
  have hN : (0 : ℝ)<(n+1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hmean : expect (bernoulli (1/2)) (varianceFactor (n := n))=1 := by
    unfold varianceFactor
    rw [bernoulli_coordinate_expect (1/2) (0 : Fin (n+1)) (fun b => if b then 3/2 else 1/2)]
    norm_num
  have hsq : expect (bernoulli (1/2))
      (fun z : Assignment (n+1) => (varianceFactor z)^2)=5/4 := by
    unfold varianceFactor
    rw [bernoulli_coordinate_expect (1/2) (0 : Fin (n+1)) (fun b => (if b then 3/2 else 1/2)^2)]
    norm_num
  have hse : ∀ z : Assignment (n+1), seWitness n z=varianceFactor z/Real.sqrt (n+1 : ℕ) := by
    intro z
    unfold seWitness varianceWitness
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq_eq_abs]
    have hB : 0 ≤ varianceFactor z := by unfold varianceFactor; split <;> norm_num
    rw [abs_of_nonneg hB]
  have hrelative : ∀ z : Assignment (n+1),
      1/2 < |varianceWitness n z/(1/(n+1 : ℕ))-1| := by
    intro z
    have hr : varianceWitness n z/(1/(n+1 : ℕ))=(varianceFactor z)^2 := by
      unfold varianceWitness
      field_simp [ne_of_gt hN]
    rw [hr]
    unfold varianceFactor
    split <;> norm_num
  refine ⟨hmean,hsq,hse,?_,?_,?_⟩
  · have hf : seWitness n=(fun z => varianceFactor z/Real.sqrt (n+1 : ℕ)) := funext hse
    rw [hf,expect_div,hmean]
  · unfold varianceWitness
    rw [expect_div,hsq]
    field_simp [ne_of_gt hN] <;> ring
  · unfold prob expect
    simp only [hrelative,ite_true,mul_one]
    exact bernoulli_total (n+1) (1/2)

/-- T22(iv): relative inconsistency follows directly from the proved
probability-one finite error events, on the varying Bernoulli spaces. -/
theorem variance_witness_not_relative_consistent :
    ¬InProbability (fun n => bernoulli (n := n+1) (1/2))
      (fun n z => varianceWitness n z/(1/(n+1 : ℕ))) (fun _ => 1) := by
  intro h
  have ht := h (1/2) (by norm_num)
  have hp : (fun n => prob (bernoulli (1/2)) (fun z : Assignment (n+1) =>
      1/2 < |varianceWitness n z/(1/(n+1 : ℕ))-1|)) = fun _ => (1 : ℝ) := by
    funext n
    exact (mean_se_finite_obstruction n).2.2.2.2.2
  rw [hp] at ht
  have he : (1 : ℝ)=0 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at he

/-- T22(iv): the absolute error is deterministically at most 5/(4N),
with N=n+1. This explicitly preserves its shrinking absolute scale. -/
theorem variance_witness_absolute_bound (n : ℕ) (z : Assignment (n+1)) :
    |varianceWitness n z-1/(n+1 : ℕ)| ≤ 5/(4*(n+1 : ℕ)) := by
  have hN : (0 : ℝ)<(n+1 : ℕ) := by exact_mod_cast (Nat.succ_pos n)
  have he : varianceWitness n z-1/(n+1 : ℕ)=((varianceFactor z)^2-1)/(n+1 : ℕ) := by
    unfold varianceWitness
    ring
  rw [he,abs_div,abs_of_pos hN]
  have hb : |(varianceFactor z)^2-1| ≤ 5/4 := by
    unfold varianceFactor
    split <;> norm_num
  calc
    _ ≤ (5/4 : ℝ)/(n+1 : ℕ) := (div_le_div_iff_of_pos_right hN).2 hb
    _ = _ := by ring

/-- T22(iii): the fair-sign sample mean is consistent in probability,
using the proved finite Chebyshev bound and the genuine varying designs. -/
theorem sign_mean_consistent :
    InProbability (fun n => bernoulli (n := n+1) (1/2)) (fun _ z => signMean z) (fun _ => 0) := by
  intro ε hε
  have hlim : Filter.Tendsto (fun n : ℕ => 1/((n+1 : ℕ)*ε^2)) Filter.atTop (nhds (0 : ℝ)) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const (ε^2)
    simpa [Nat.cast_add,Nat.cast_one,div_div,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using h
  apply squeeze_zero
  · intro n
    exact prob_nonneg (bernoulliDesign (n+1) (1/2) (by norm_num) (by norm_num)) _
  · intro n
    simpa only [sub_zero] using sign_mean_chebyshev n ε hε
  · exact hlim

/-- T22(iv): despite its relative inconsistency, the variance witness is
absolutely consistent, as follows from its deterministic 5/(4N) bound. -/
theorem variance_witness_absolute_consistent :
    InProbability (fun n => bernoulli (n := n+1) (1/2)) varianceWitness (fun n => 1/(n+1 : ℕ)) := by
  intro ε hε
  have hlim : Filter.Tendsto (fun n : ℕ => (5 : ℝ)/(4*(n+1 : ℕ))) Filter.atTop (nhds (0 : ℝ)) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (5/4)
    simpa [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using h
  have hb : ∀ᶠ n in Filter.atTop, 5/(4*(n+1 : ℕ)) < ε := hlim.eventually (gt_mem_nhds hε)
  have he : (fun n : ℕ => prob (bernoulli (1/2)) (fun z : Assignment (n+1) =>
      ε < |varianceWitness n z-1/(n+1 : ℕ)|)) =ᶠ[Filter.atTop] (fun _ => (0 : ℝ)) := by
    filter_upwards [hb] with n hn
    have hfalse : ∀ z : Assignment (n+1), ¬ε < |varianceWitness n z-1/(n+1 : ℕ)| := by
      intro z
      exact not_lt_of_ge (le_of_lt (lt_of_le_of_lt (variance_witness_absolute_bound n z) hn))
    simp only [prob,expect,hfalse,if_false,mul_zero,Finset.sum_const_zero]
  exact Filter.Tendsto.congr' he.symm tendsto_const_nhds

/-- T22(i)–(v), full explicit sample-mean/variance sequence. Exact mean
SE agreement and conservative expectation coexist with relative
inconsistency; absolute consistency is explicitly retained. This is the
counterexample estimator, not a claim about either estimator in Table 16.1. -/
theorem mean_se_counterexample :
    (∀ n : ℕ,
      expect (bernoulli (1/2)) (signMean (n := n+1)) = 0 ∧
      variance (bernoulli (1/2)) (signMean (n := n+1)) = 1/(n+1 : ℕ) ∧
      (∀ ε : ℝ, 0 < ε → prob (bernoulli (1/2))
        (fun z : Assignment (n+1) => ε < |signMean z|) ≤ 1/((n+1 : ℕ)*ε^2)) ∧
      expect (bernoulli (1/2)) (varianceFactor (n := n)) = 1 ∧
      expect (bernoulli (1/2)) (fun z : Assignment (n+1) => (varianceFactor z)^2) = 5/4 ∧
      (∀ z : Assignment (n+1), seWitness n z=varianceFactor z/Real.sqrt (n+1 : ℕ)) ∧
      expect (bernoulli (1/2)) (seWitness n) = 1/Real.sqrt (n+1 : ℕ) ∧
      expect (bernoulli (1/2)) (varianceWitness n)-1/(n+1 : ℕ) = 1/(4*(n+1 : ℕ)) ∧
      prob (bernoulli (1/2)) (fun z : Assignment (n+1) =>
        1/2 < |varianceWitness n z/(1/(n+1 : ℕ))-1|) = 1 ∧
      (∀ z : Assignment (n+1), |varianceWitness n z-1/(n+1 : ℕ)| ≤ 5/(4*(n+1 : ℕ)))) ∧
    InProbability (fun n => bernoulli (n := n+1) (1/2)) (fun _ z => signMean z) (fun _ => 0) ∧
    ¬InProbability (fun n => bernoulli (n := n+1) (1/2))
      (fun n z => varianceWitness n z/(1/(n+1 : ℕ))) (fun _ => 1) ∧
    InProbability (fun n => bernoulli (n := n+1) (1/2)) varianceWitness (fun n => 1/(n+1 : ℕ)) := by
  refine ⟨?_,sign_mean_consistent,variance_witness_not_relative_consistent,
    variance_witness_absolute_consistent⟩
  intro n
  have hf := mean_se_finite_obstruction n
  exact ⟨(sign_mean_finite_moments n).1,(sign_mean_finite_moments n).2,
    fun ε hε => sign_mean_chebyshev n ε hε,
    hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,hf.2.2.2.2.2,
    variance_witness_absolute_bound n⟩

/-- T23(a): exact finite-sample Mean SE/SD ratios read from Table 16.1,
p. 300, with the corrected 7.1%, 24.4–24.5%, and 16.4–16.5% comparisons. -/
theorem table_standard_error_comparison :
    (3311/2660 : ℝ)=473/380 ∧
    (∀ r ∈ ({4594/4532,1033/1045,3407/3666,841/838} : Finset ℝ),
      1-71/1000 ≤ r ∧ r ≤ 1+71/1000) ∧
    (244/1000 : ℝ) < 473/380-1 ∧ (473/380 : ℝ)-1 < 245/1000 ∧
    (164/1000 : ℝ) < 2509/2155-1 ∧ (2509/2155 : ℝ)-1 < 165/1000 := by
  norm_num

/-- T23(b2): the faithful asymptotic repair. If the true variances tend
to zero and E(sqrt(Vhat))−sqrt(V) tends to zero, absolute variance
consistency follows. This does not assert relative consistency. -/
theorem absolute_variance_consistency {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (p : (n : ℕ) → Design (Ω n)) (T Vhat : (n : ℕ) → Ω n → ℝ)
    (hV : ∀ n, 0 < variance (p n).mass (T n)) (hhat : ∀ n w, 0 ≤ Vhat n w)
    (hvanish : Filter.Tendsto (fun n => variance (p n).mass (T n)) Filter.atTop (nhds 0))
    (hse : Filter.Tendsto (fun n => expect (p n).mass (fun w => Real.sqrt (Vhat n w)) -
      Real.sqrt (variance (p n).mass (T n))) Filter.atTop (nhds 0)) :
    InProbability (fun n => (p n).mass) Vhat (fun n => variance (p n).mass (T n)) := by
  classical
  have hroot : Filter.Tendsto (fun n => Real.sqrt (variance (p n).mass (T n)))
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hvanish
  have hmean : Filter.Tendsto (fun n => expect (p n).mass (fun w => Real.sqrt (Vhat n w)))
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [sub_add_cancel,zero_add] using hse.add hroot
  intro ε hε
  have hhalf : (0 : ℝ)<ε/2 := by linarith
  let t := Real.sqrt (ε/2)
  have ht : 0 < t := Real.sqrt_pos.2 hhalf
  have hlim : Filter.Tendsto (fun n => expect (p n).mass (fun w => Real.sqrt (Vhat n w))/t)
      Filter.atTop (nhds (0 : ℝ)) := by simpa using hmean.div_const t
  have hsmall : ∀ᶠ n in Filter.atTop, variance (p n).mass (T n)<ε/2 :=
    hvanish.eventually (gt_mem_nhds hhalf)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => prob_nonneg (p n) _)) _ hlim
  filter_upwards [hsmall] with n hn
  calc
    _ ≤ prob (p n).mass (fun w => t < Real.sqrt (Vhat n w)) := by
      apply prob_mono
      intro w hw
      have hv : 0 ≤ variance (p n).mass (T n) := le_of_lt (hV n)
      have hhatbig : ε/2 < Vhat n w := by
        rcases lt_abs.mp hw with h | h <;> linarith [hhat n w]
      exact Real.sqrt_lt_sqrt (le_of_lt hhalf) hhatbig
    _ ≤ _ := finite_markov_nonneg (p n) _ (fun w => Real.sqrt_nonneg _) t ht

/-- T23(b3): without a vanishing true variance even absolute consistency
need not follow from mean-SE agreement. T=X1, V=1 and Vhat=B² on one fair
sign give error >1/2 with probability one at every N. -/
theorem nonvanishing_variance_counterexample :
    variance (fun _ : Bool => (1/2 : ℝ)) sign=1 ∧
    expect (fun _ : Bool => (1/2 : ℝ)) (fun b => Real.sqrt ((if b then (3/2 : ℝ) else 1/2)^2))=1 ∧
    prob (fun _ : Bool => (1/2 : ℝ)) (fun b => 1/2 < |(if b then (3/2 : ℝ) else 1/2)^2-1|)=1 ∧
    ¬InProbability (fun (_n : ℕ) (_b : Bool) => (1/2 : ℝ))
      (fun _ b => (if b then (3/2 : ℝ) else 1/2)^2) (fun _ => 1) := by
  have hprob : prob (fun _ : Bool => (1/2 : ℝ))
      (fun b => 1/2 < |(if b then (3/2 : ℝ) else 1/2)^2-1|)=1 := by
    norm_num [prob, expect]
  refine ⟨?_, ?_, hprob, ?_⟩
  · norm_num [variance, expect, sign]
  · simp only [Real.sqrt_sq_eq_abs]
    norm_num [expect]
  · intro h
    have ht := h (1/2) (by norm_num)
    simp only [hprob] at ht
    have he : (1 : ℝ)=0 := tendsto_nhds_unique tendsto_const_nhds ht
    norm_num at he

/-- T23(b4): the square of a mean SE is no larger than the mean of
the variance estimates. Nonnegative s_r are the reported SEs (p. 300). -/
theorem mean_square_bound {M : ℕ} (hM : 0 < M) (s : Fin M → ℝ) (hs : ∀ i, 0 ≤ s i) :
    (mean s)^2 ≤ mean (fun i => (s i)^2) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum : (∑ i, s i) = mean s * M := by
    simp [mean, ne_of_gt hM']
  have hnonneg : 0 ≤ ∑ i, (s i-mean s)^2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hexpand : (∑ i, (s i-mean s)^2) =
      (∑ i, (s i)^2) - 2*mean s*(∑ i, s i) + (M : ℝ)*(mean s)^2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc, mul_comm]
  have hsq : (mean s)^2 ≤ (∑ i, (s i)^2)/(M : ℝ) := by
    apply (le_div_iff₀ hM').2
    rw [hexpand,hsum] at hnonneg
    nlinarith
  simpa [mean] using hsq

/-- Linearity of a finite population mean, used for the p. 310 dilated
effects and the mediation decomposition on p. 315. -/
theorem mean_smul {I : Type*} [Fintype I] (c : ℝ) (x : I → ℝ) :
    mean (fun i => c*x i)=c*mean x := by
  simp only [mean, ← Finset.mul_sum]
  ring

/-- Mean marginal outcome across groups, then units, as on p. 309;
groups are weighted equally, even when their sizes differ (T24). -/
def regimeMean {G : ℕ} {n : Fin G → ℕ}
    (y : (g : Fin G) → Fin (n g) → Bool → Bool → ℝ) (b s : Bool) : ℝ :=
  mean (fun g => mean (fun i => y g i b s))

/-- T24(iii), p. 309: for every potential-outcome schedule, total equals
direct at psi plus indirect between psi and phi. This identity does not
require the dilated model used for the other Figure 16.6 formulas. -/
theorem total_direct_indirect_identity {G : ℕ} (hG : 0 < G) (n : Fin G → ℕ)
    (hn : ∀ g, 0 < n g) (y : (g : Fin G) → Fin (n g) → Bool → Bool → ℝ) :
    regimeMean y true true-regimeMean y false false =
      (regimeMean y true true-regimeMean y false true) +
      (regimeMean y false true-regimeMean y false false) := by ring
/-- "bbar=(1/G)∑_g (1/n_g)∑_i b_ig" (T24 setting, p. 310 model and p. 309 estimand definitions): equal group weighting. -/
def baselineMean {G : ℕ} {n : Fin G → ℕ} (b : (g : Fin G) → Fin (n g) → ℝ) : ℝ :=
  mean (fun g => mean (b g))
/-- "y_ig(1,ψ)=2 b_ig", "y_ig(1,φ)=1.5 b_ig", "y_ig(0,ψ)=1.25 b_ig" (p. 310). These are the fixed marginal schedules for T24. -/
def dilatedMarginal {G : ℕ} {n : Fin G → ℕ} (b : (g : Fin G) → Fin (n g) → ℝ)
    (g : Fin G) (i : Fin (n g)) (own high : Bool) : ℝ :=
  if high then (if own then 2 else 5/4)*b g i else (if own then 3/2 else 1)*b g i

/-- The p. 310 marginal schedule has a common regime multiplier for
each group's and the population's baseline mean (supporting T24). -/
theorem dilated_regime_mean {G : ℕ} {n : Fin G → ℕ}
    (b : (g : Fin G) → Fin (n g) → ℝ) (own high : Bool) :
    regimeMean (dilatedMarginal b) own high =
      (if high then (if own then 2 else 5/4) else (if own then 3/2 else 1))*baselineMean b := by
  cases own <;> cases high <;>
    simp [regimeMean,dilatedMarginal,baselineMean,mean_smul]

/-- T24(i)–(iii): the p. 310 model fixes the direct effects' ordering,
the five effect formulas, the φ/ψ ratio 2/3 and the total=direct+indirect
identity. These determine the swapped Figure 16.6 labels. -/
theorem dilated_effect_labels {G : ℕ} (hG : 0 < G) (n : Fin G → ℕ)
    (hn : ∀ g, 0 < n g) (b : (g : Fin G) → Fin (n g) → ℝ) :
    let μ := regimeMean (dilatedMarginal b)
    let B := baselineMean b
    let Dψ := μ true true-μ false true
    let Dφ := μ true false-μ false false
    let I := μ false true-μ false false
    let To := μ true true-μ false false
    let O := (2/3)*μ true true+(1/3)*μ false true - ((1/3)*μ true false+(2/3)*μ false false)
    Dψ=(3/4)*B ∧ Dφ=(1/2)*B ∧ I=(1/4)*B ∧ To=B ∧ O=(7/12)*B ∧
    (0 < B → Dφ/Dψ=2/3 ∧ Dφ < Dψ) ∧ To=Dψ+I ∧
    (B ≠ 0 → To-I ≠ Dφ) := by
  simp only [dilated_regime_mean]
  dsimp
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · intro hB
    constructor
    · field_simp
      <;> ring
    · linarith
  constructor
  · ring
  · intro hB
    intro heq
    apply hB
    linarith

/-- T31, "y*_{i1}(z_i)∈{0,1}" and unreachable-voter potential outcome
"y_{i2}(z_i,y*_{i1}(z_i))", p. 315. Outcome functions are arbitrary reals. -/
def indirectHousehold {Nc : ℕ} (m : Fin Nc → Bool → Bool) (y : Fin Nc → Bool → Bool → ℝ) : ℝ :=
  mean (fun i => y i true (m i true)-y i false (m i false))
/-- "average contagion effect" γ(z) (p. 315): hold the reachable voter's treatment at z and vary the mediator between its treated and control values. -/
def contagion {Nc : ℕ} (m : Fin Nc → Bool → Bool) (y : Fin Nc → Bool → Bool → ℝ) (z : Bool) : ℝ :=
  mean (fun i => y i z (m i true)-y i z (m i false))
/-- "Other non-contagion mechanisms are captured by" η(z) (p. 315): hold the mediator at its z value and vary treatment. -/
def otherMechanisms {Nc : ℕ} (m : Fin Nc → Bool → Bool) (y : Fin Nc → Bool → Bool → ℝ) (z : Bool) : ℝ :=
  mean (fun i => y i true (m i z)-y i false (m i z))

/-- T31: θ=γ(1)+η(0)=γ(0)+η(1), the finite-population mediation identity
printed on p. 315. An unchanged intention gives zero contagion summand. -/
theorem contagion_decomposition {Nc : ℕ} (hN : 0 < Nc)
    (m : Fin Nc → Bool → Bool) (y : Fin Nc → Bool → Bool → ℝ) :
    indirectHousehold m y=contagion m y true+otherMechanisms m y false ∧
    indirectHousehold m y=contagion m y false+otherMechanisms m y true ∧
    (∀ i, m i true=m i false → ∀ z, y i z (m i true)-y i z (m i false)=0) := by
  constructor
  · unfold indirectHousehold contagion otherMechanisms mean
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  constructor
  · unfold indirectHousehold contagion otherMechanisms mean
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro i hi z
    simp [hi]

/-- Two-stage experiment under an arbitrary first-stage design on regime
labels: true=ψ, false=φ. Each group's units are then independent Bernoulli
at its assigned saturation, as on pp. 308–310. -/
def hierarchyLaw {G : ℕ} (n : Fin G → ℕ) (S : Design (Assignment G)) (ψ φ : ℝ)
    (w : Assignment G × GroupAssignments n) : ℝ :=
  S.mass w.1 * ∏ g, bernoulli (if w.1 g then ψ else φ) (w.2 g)
/-- "I(S_g=ψ)" (p. 310): the groups assigned the designated saturation in the first-stage assignment. -/
def regimeGroups {G : ℕ} (s : Assignment G) (high : Bool) : Finset (Fin G) :=
  univ.filter (fun g => s g=high)
/-- "yhat(z;ψ)" (p. 310): average the observed within-arm group ratios over the groups in the specified saturation. -/
def hierarchyArm {G : ℕ} {n : Fin G → ℕ}
    (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ)
    (high b : Bool) (w : Assignment G × GroupAssignments n) : ℝ :=
  average (regimeGroups w.1 high) (fun g => armMean (y g) b (w.2 g))
/-- "conditional on the denominators ... being nonzero" (p. 310): there is a saturation group and every included group's required individual arm is nonempty. -/
def hierarchyDomain {G : ℕ} {n : Fin G → ℕ}
    (high b : Bool) (w : Assignment G × GroupAssignments n) : Prop :=
  (regimeGroups w.1 high).Nonempty ∧ ∀ g ∈ regimeGroups w.1 high, armExists b (w.2 g)
/-- "the population average ... is the average ... across groups" (p. 309): equal-group mean of the Bernoulli marginal unit means. -/
def hierarchyTarget {G : ℕ} {n : Fin G → ℕ}
    (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ) (p : ℝ) (b : Bool) : ℝ :=
  mean (fun g => mean (fun i => marginal (bernoulli p) (y g) i b))
/-- "average across groups ... of the average observed outcomes" (p. 310): use all-unit group means without an individual-arm restriction. -/
def hierarchyOverall {G : ℕ} {n : Fin G → ℕ}
    (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ)
    (high : Bool) (w : Assignment G × GroupAssignments n) : ℝ :=
  average (regimeGroups w.1 high) (fun g => groupOverall (y g) (w.2 g))


end
end AronowAudit.P045
