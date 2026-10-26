import Mathlib

/-!
P024: Field Experimental Designs for the Study of Media Effects, pp. 170–177.
The article contains prose statistical claims, not displayed formulas. The definitions
below express these claims using potential outcomes, finite probability laws, estimators,
and population sequences. All randomness is assignment.
-/
namespace AronowAudit.P024
open scoped BigOperators
open Filter
noncomputable section

/-- “random assignments” (p. 170) and “all possible random assignments” (p. 172):
a finite known randomization law. This notation is not printed in the paper. -/
structure Design (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

/-- “unbiased estimation” (p. 170): expectation over assignment alone. -/
def expectation {Ω : Type*} [Fintype Ω] (d : Design Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, d.mass ω * X ω

/-- The design probability of an event; p. 172's randomization distribution. -/
def probability {Ω : Type*} [Fintype Ω] (d : Design Ω) (P : Ω → Prop) : ℝ :=
  by classical exact expectation d (fun ω => if P ω then 1 else 0)

/-- Variance under the randomization distribution, not a sampling model (p. 171). -/
def variance {Ω : Type*} [Fintype Ω] (d : Design Ω) (X : Ω → ℝ) : ℝ :=
  expectation d (fun ω => (X ω - expectation d X)^2)

/-- Uniform finite randomization for onset and complete designs. -/
def uniformDesign (Ω : Type*) [Fintype Ω] [Nonempty Ω] : Design Ω where
  mass := fun _ => 1 / (Fintype.card Ω : ℝ)
  nonneg := fun _ => by positivity
  total := by simp [Fintype.card_ne_zero]

/-- Auxiliary linearity of finite randomization expectation. This lemma is used for corrected T2(a), p. 174. -/
theorem expectation_add {Ω : Type*} [Fintype Ω] (d : Design Ω) (X Y : Ω → ℝ) :
    expectation d (fun ω => X ω + Y ω) = expectation d X + expectation d Y := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

/-- Auxiliary linearity of finite randomization expectation. This lemma is used for corrected T2(a), p. 174. -/
theorem expectation_sub {Ω : Type*} [Fintype Ω] (d : Design Ω) (X Y : Ω → ℝ) :
    expectation d (fun ω => X ω - Y ω) = expectation d X - expectation d Y := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

/-- Auxiliary extraction of a constant from expectation. This lemma is used for corrected T2(a), p. 174. -/
theorem expectation_mul {Ω : Type*} [Fintype Ω] (d : Design Ω) (X : Ω → ℝ) (a : ℝ) :
    expectation d (fun ω => X ω * a) = expectation d X * a := by
  simp [expectation, mul_assoc, Finset.sum_mul]

/-- Auxiliary expectation of a nonrandom constant. This lemma is used for corrected T2(a), p. 174. -/
theorem expectation_const {Ω : Type*} [Fintype Ω] (d : Design Ω) (a : ℝ) :
    expectation d (fun _ => a) = a := by
  simp [expectation, ← Finset.sum_mul, d.total]

/-- Auxiliary interchange of finite summation and assignment expectation. This lemma is used for corrected T2(a), p. 174. -/
theorem expectation_sum {I Ω : Type*} [Fintype Ω] (d : Design Ω)
    (E : Finset I) (X : I → Ω → ℝ) :
    expectation d (fun ω => ∑ i ∈ E, X i ω) = ∑ i ∈ E, expectation d (X i) := by
  simp only [expectation, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Auxiliary extraction of a fixed divisor from expectation. This lemma is used for corrected T2(a), p. 174. -/
theorem expectation_div {Ω : Type*} [Fintype Ω] (d : Design Ω) (X : Ω → ℝ) (a : ℝ) :
    expectation d (fun ω => X ω / a) = expectation d X / a := by
  simpa only [div_eq_mul_inv] using expectation_mul d X a⁻¹

/-- “subjects respond solely to the treatment that they receive” (p. 170):
a binary current-exposure indicator, with fixed potential outcomes. -/
def indicator (z : Bool) : ℝ := if z then 1 else 0

/-- All outcomes observed as planned, and no interference: conditions (a)–(c), p. 170.
For timing, this current-exposure model also rules out anticipation and duration effects. -/
def observed {I Ω : Type*} (z : Ω → I → Bool) (y0 y1 : I → ℝ) (ω : Ω) (i : I) : ℝ :=
  if z ω i then y1 i else y0 i

/-- “average causal effect ... in the subject pool” (p. 170); over the finite set E.
Potential-outcome notation is used, and periods are restricted to those with overlap. -/
def averageEffect {I : Type*} (E : Finset I) (y0 y1 : I → ℝ) : ℝ :=
  (∑ i ∈ E, (y1 i - y0 i)) / E.card

/-- Inverse-probability contrast, Note 4 (p. 177); current-exposure timing version.
The if expression equals Z Y/p - (1-Z) Y/(1-p), with Y the observed outcome. -/
def htEstimate {I Ω : Type*} (E : Finset I) (z : Ω → I → Bool)
    (y0 y1 π : I → ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ E, if z ω i then y1 i / π i else -(y0 i / (1 - π i))) / E.card

/-- Exposure probability: no independence across periods. -/
def exposureProbability {I Ω : Type*} [Fintype Ω] (d : Design Ω)
    (z : Ω → I → Bool) (i : I) : ℝ := expectation d (fun ω => indicator (z ω i))

/-- Auxiliary expectation of one inverse-probability contrast. This lemma is used for corrected T2(a), p. 174. -/
theorem ht_coordinate_unbiased {Ω : Type*} [Fintype Ω] (d : Design Ω)
    (z : Ω → Bool) (y0 y1 p : ℝ)
    (hp : expectation d (fun ω => indicator (z ω)) = p) (h0 : p ≠ 0) (h1 : 1-p ≠ 0) :
    expectation d (fun ω => if z ω then y1/p else -(y0/(1-p))) = y1-y0 := by
  have hb : ∀ ω, (if z ω then y1/p else -(y0/(1-p))) =
      indicator (z ω) * (y1/p) - (1-indicator (z ω)) * (y0/(1-p)) := by
    intro ω; cases z ω <;> simp [indicator]
  simp_rw [hb]
  rw [expectation_sub, expectation_mul, expectation_mul, hp]
  have hc : expectation d (fun ω => 1-indicator (z ω)) = 1-p := by
    rw [expectation_sub, expectation_const, hp]
  rw [hc]
  field_simp

/-- Corrected timing statement T2(a), p. 174: over any nonempty set of
periods with overlap, the HT contrast is design-unbiased for the average within-period
causal effect. Arbitrary fixed calendar trends and dependent exposures are allowed. -/
theorem timing_ht_unbiased {I Ω : Type*} [Fintype Ω] (d : Design Ω)
    (E : Finset I) (hE : E.Nonempty) (z : Ω → I → Bool) (y0 y1 : I → ℝ)
    (hov : ∀ i ∈ E, 0 < exposureProbability d z i ∧ exposureProbability d z i < 1) :
    expectation d (htEstimate E z y0 y1 (exposureProbability d z)) =
      averageEffect E y0 y1 := by
  unfold htEstimate averageEffect
  rw [expectation_div, expectation_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact ht_coordinate_unbiased d (fun ω => z ω i) (y0 i) (y1 i)
    (exposureProbability d z i) rfl (ne_of_gt (hov i hi).1)
      (by linarith [(hov i hi).2])

/-- The eligible periods E={t:0<p_t<1}, T2(a). -/
def overlap {I Ω : Type*} [Fintype I] [Fintype Ω] (d : Design Ω)
    (z : Ω → I → Bool) : Finset I :=
  Finset.univ.filter (fun i => 0 < exposureProbability d z i ∧ exposureProbability d z i < 1)

/-- T2(a) with exactly the set E specified by the corrected statement. -/
theorem timing_overlap_unbiased {I Ω : Type*} [Fintype I] [Fintype Ω]
    (d : Design Ω) (z : Ω → I → Bool) (y0 y1 : I → ℝ) (hE : (overlap d z).Nonempty) :
    expectation d (htEstimate (overlap d z) z y0 y1 (exposureProbability d z)) =
      averageEffect (overlap d z) y0 y1 := by
  apply timing_ht_unbiased d _ hE
  simp [overlap]

/-- Upper-tail randomization p-value, ties included; p. 172 and corrected T2(b).
The sharp null fixes the outcome path, so D is fixed. -/
def randomizationP {Ω : Type*} [Fintype Ω] (D : Ω → ℝ) (ω : Ω) : ℝ :=
  ((Finset.univ.filter (fun υ => D ω ≤ D υ)).card : ℝ) / Fintype.card Ω

/-- T2(b): under a uniform finite schedule and sharp null, any fixed statistic has
Pr(p(W)≤α)≤α. Ties count against rejection. No calendar-trend restriction is made. -/
theorem randomization_test_valid {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (D : Ω → ℝ) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    probability (uniformDesign Ω) (fun ω => randomizationP D ω ≤ α) ≤ α := by
  classical
  let R := Finset.univ.filter (fun ω => randomizationP D ω ≤ α)
  have hm : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hprob : probability (uniformDesign Ω) (fun ω => randomizationP D ω ≤ α) =
      (R.card : ℝ) / Fintype.card Ω := by
    simp [probability, expectation, uniformDesign, R, div_eq_mul_inv,
      Finset.sum_ite, mul_comm]
  rw [hprob]
  by_cases hr : R.Nonempty
  · obtain ⟨w, hw, hmin⟩ := R.exists_min_image D hr
    have hsub : R ⊆ Finset.univ.filter (fun υ => D w ≤ D υ) := by
      intro υ hυ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmin υ hυ
    have hcard : (R.card : ℝ) ≤ (Finset.univ.filter (fun υ => D w ≤ D υ)).card := by
      exact_mod_cast Finset.card_le_card hsub
    have hwα : randomizationP D w ≤ α := (Finset.mem_filter.mp hw).2
    exact (div_le_div_of_nonneg_right hcard hm.le).trans hwα
  · have hempty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hr
    simpa [hempty] using hα

/-- T1: four calendar periods t=1,2,3,4, encoded by Fin 4, and onsets
s=2,3,4 encoded by Fin 3; “randomizes the timing” (p. 174). -/
def onsetExposure (s : Fin 3) (t : Fin 4) : Bool := decide (s.val+2 ≤ t.val+1)

/-- T1's untreated calendar trajectory t²; p. 174 necessity claim witness.
The trend is fixed before randomization. -/
def calendarBaseline (t : Fin 4) : ℝ := (t.val+1 : ℝ)^2

/-- T1's treated potential outcomes t²+2, same location. -/
def calendarTreated (t : Fin 4) : ℝ := calendarBaseline t + 2

/-- T1's overlap set is calendar periods 2 and 3. -/
def calendarEligible : Finset (Fin 4) := {1,2}

/-- T1's HT timing estimator, using observed outcomes under current exposure. -/
def calendarHT (s : Fin 3) : ℝ :=
  htEstimate calendarEligible onsetExposure calendarBaseline calendarTreated
    (exposureProbability (uniformDesign (Fin 3)) onsetExposure) s

/-- T1's raw before-after statistic on the fixed sharp-null trajectory.
Means use all four periods. -/
def calendarBeforeAfter (s : Fin 3) : ℝ :=
  (∑ t : Fin 4, if onsetExposure s t then calendarBaseline t else 0) / (3-s.val : ℝ) -
  (∑ t : Fin 4, if onsetExposure s t then 0 else calendarBaseline t) / (s.val+1 : ℝ)

/-- T1(ii): exact exposure probabilities, estimates, estimand, expectation, and variance.
This is the numerical witness, not a formula printed in the article. -/
theorem calendar_ht_counterexample :
    (∀ t : Fin 4, exposureProbability (uniformDesign (Fin 3)) onsetExposure t =
      (![0,1/3,2/3,1] : Fin 4 → ℝ) t) ∧
    calendarBaseline 0 = 1 ∧ calendarBaseline 1 = 4 ∧
    calendarBaseline 2 = 9 ∧ calendarBaseline 3 = 16 ∧
    calendarBaseline 0 ≠ calendarBaseline 1 ∧
    calendarHT 0 = 69/4 ∧ calendarHT 1 = 21/4 ∧ calendarHT 2 = -33/2 ∧
    averageEffect calendarEligible calendarBaseline calendarTreated = 2 ∧
    expectation (uniformDesign (Fin 3)) calendarHT = 2 ∧
    variance (uniformDesign (Fin 3)) calendarHT = 1561/8 := by
  constructor
  · intro t
    fin_cases t <;> norm_num [exposureProbability, expectation, uniformDesign, indicator,
      onsetExposure, Fin.sum_univ_succ]
  · norm_num [exposureProbability, expectation, uniformDesign, indicator, onsetExposure,
      calendarBaseline, calendarTreated, calendarEligible, calendarHT, htEstimate,
      averageEffect, variance, Fin.sum_univ_succ]

/-- T1(iii): exact raw null statistics and upper-tail p-values, with a valid test for
all levels despite the nonconstant calendar trend. -/
theorem calendar_null_counterexample :
    calendarBeforeAfter 0 = 26/3 ∧ calendarBeforeAfter 1 = 10 ∧
    calendarBeforeAfter 2 = 34/3 ∧
    randomizationP calendarBeforeAfter 0 = 1 ∧
    randomizationP calendarBeforeAfter 1 = 2/3 ∧
    randomizationP calendarBeforeAfter 2 = 1/3 ∧
    (∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      probability (uniformDesign (Fin 3))
        (fun s => randomizationP calendarBeforeAfter s ≤ α) ≤ α) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun α h0 h1 => randomization_test_valid _ α h0 h1⟩
  all_goals
    try simp only [randomizationP, ← Finset.sum_boole]
    norm_num [calendarBeforeAfter, calendarBaseline, onsetExposure, Fin.sum_univ_succ,
      -Finset.sum_boole]

/-- T2(c): randomizing timing does not remove bias in a raw before-after contrast.
Its null expectation is 10; with the constant effect 2 it is 12, rather than 2. -/
theorem raw_before_after_bias :
    expectation (uniformDesign (Fin 3)) calendarBeforeAfter = 10 ∧
    expectation (uniformDesign (Fin 3)) calendarBeforeAfter ≠ 0 ∧
    expectation (uniformDesign (Fin 3)) (fun s => calendarBeforeAfter s + 2) = 12 ∧
    expectation (uniformDesign (Fin 3)) (fun s => calendarBeforeAfter s + 2) ≠ 2 := by
  norm_num [expectation, uniformDesign, calendarBeforeAfter, calendarBaseline,
    onsetExposure, Fin.sum_univ_succ]

/-- “comparing treatment and control group averages” (p. 171): individuals in cluster
j have common assignment z_j. n_j times the cluster potential-outcome mean gives
its total. Nonempty-arm estimator; Lean division is total, but empty allocations
will be explicitly extended when needed. -/
def clusterDIM {J : Type*} [Fintype J] (n y0 y1 : J → ℝ) (z : J → Bool) : ℝ :=
  (∑ j, if z j then n j * y1 j else 0) / (∑ j, if z j then n j else 0) -
  (∑ j, if z j then 0 else n j * y0 j) / (∑ j, if z j then 0 else n j)

/-- “individual-level average treatment effect” (p. 172): size-weighted cluster effect. -/
def clusterEffect {J : Type*} [Fintype J] (n y0 y1 : J → ℝ) : ℝ :=
  (∑ j, n j * (y1 j-y0 j)) / (∑ j, n j)

/-- Number of treated units/clusters in an allocation; notation for p. 170–171. -/
def treatedCount {J : Type*} [Fintype J] (z : J → Bool) : ℕ :=
  (Finset.univ.filter (fun j => z j = true)).card


/-- Fixed-arm difference in means, p. 170: m treated and N-m control units.
This representation is used only with the hypothesis that exactly m are treated. -/
def fixedDIM {J : Type*} [Fintype J] (m : ℕ) (y0 y1 : J → ℝ) (z : J → Bool) : ℝ :=
  (∑ j, if z j then y1 j else 0) / (m : ℝ) -
  (∑ j, if z j then 0 else y0 j) / ((Fintype.card J : ℝ)-m)

/-- Auxiliary algebra relating a fixed-count difference in means to the HT contrast. This lemma is used for T6, p. 170. -/
theorem fixed_dim_ht {J : Type*} [Fintype J] (m : ℕ) (hm : 0 < m)
    (hmN : m < Fintype.card J) (y0 y1 : J → ℝ) (z : J → Bool) :
    fixedDIM m y0 y1 z =
      htEstimate Finset.univ (fun (_ : Unit) => z) y0 y1
        (fun _ => (m : ℝ)/Fintype.card J) () := by
  classical
  let N : ℝ := Fintype.card J
  have hN : N ≠ 0 := by dsimp [N]; exact_mod_cast (ne_of_gt (lt_trans hm hmN))
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hd : N-(m : ℝ) ≠ 0 := by
    have h : (m : ℝ) < Fintype.card J := by exact_mod_cast hmN
    dsimp [N]; linarith
  have hsum : (∑ j, if z j then y1 j / ((m : ℝ)/N) else -(y0 j/(1-(m : ℝ)/N))) =
      (∑ j, if z j then y1 j else 0) / ((m : ℝ)/N) -
      (∑ j, if z j then 0 else y0 j) / (1-(m : ℝ)/N) := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _; cases z j <;> simp
  simp only [fixedDIM, htEstimate, Finset.card_univ]
  change _ = (∑ j, if z j then y1 j / ((m : ℝ)/N) else -(y0 j/(1-(m : ℝ)/N))) / N
  rw [hsum]
  change _ / (m : ℝ) - _ / (N-(m : ℝ)) = _
  field_simp [hN, hm0, hd]
  <;> ring

/-- T6, p. 170: equal inclusion probabilities and exactly m treated subjects give
an unbiased difference in means for the subject-pool effect. Uniform complete
randomization is an instance; independence is unnecessary. -/
theorem individual_dim_unbiased {J Ω : Type*} [Fintype J] [Fintype Ω]
    (d : Design Ω) (m : ℕ) (hm : 0 < m) (hmN : m < Fintype.card J)
    (z : Ω → J → Bool) (y0 y1 : J → ℝ)
    (hcount : ∀ ω, treatedCount (z ω) = m)
    (hp : ∀ j, exposureProbability d z j = (m : ℝ)/Fintype.card J) :
    expectation d (fun ω => fixedDIM m y0 y1 (z ω)) = averageEffect Finset.univ y0 y1 := by
  classical
  have hE : (Finset.univ : Finset J).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fintype.card_pos_iff.mp (lt_trans hm hmN)
  have hov : ∀ j ∈ (Finset.univ : Finset J),
      0 < exposureProbability d z j ∧ exposureProbability d z j < 1 := by
    intro j _; rw [hp j]
    have hn : (0 : ℝ) < Fintype.card J := by exact_mod_cast lt_trans hm hmN
    constructor
    · exact div_pos (by exact_mod_cast hm) hn
    · exact (div_lt_one hn).mpr (by exact_mod_cast hmN)
  have heq : (fun ω => fixedDIM m y0 y1 (z ω)) =
      htEstimate Finset.univ z y0 y1 (exposureProbability d z) := by
    funext ω
    have hπ : exposureProbability d z = fun _ => (m : ℝ)/Fintype.card J := funext hp
    rw [hπ]; exact fixed_dim_ht m hm hmN y0 y1 (z ω)
  rw [heq]
  exact timing_ht_unbiased d _ hE z y0 y1 hov

/-- Auxiliary cancellation of equal cluster sizes: with fixed m treated clusters,
individual group means equal the corresponding cluster group means. This lemma is used for T7, p. 171. -/
theorem equal_size_dim {J : Type*} [Fintype J] (n : ℝ) (hn : 0 < n)
    (m : ℕ) (hm : 0 < m) (hmN : m < Fintype.card J) (z : J → Bool)
    (hcount : treatedCount z = m) (y0 y1 : J → ℝ) :
    clusterDIM (fun _ => n) y0 y1 z = fixedDIM m y0 y1 z := by
  classical
  have ht : (∑ j, if z j then (1 : ℝ) else 0) = m := by
    simpa [treatedCount, ← hcount] using
      (Finset.sum_boole (R := ℝ) (fun j => z j = true) Finset.univ)
  have hc : (∑ j, if z j then (0 : ℝ) else 1) = (Fintype.card J : ℝ)-m := by
    have hh : ∀ j, (if z j then (0 : ℝ) else 1) = 1-(if z j then 1 else 0) := by
      intro j; cases z j <;> simp
    simp_rw [hh]; rw [Finset.sum_sub_distrib, ht]; simp
  have htN : (∑ j, if z j then n else 0) = n*(m : ℝ) := by
    rw [← ht, Finset.mul_sum]; apply Finset.sum_congr rfl
    intro j _; cases z j <;> simp
  have hcN : (∑ j, if z j then 0 else n) = n*((Fintype.card J : ℝ)-m) := by
    rw [← hc, Finset.mul_sum]; apply Finset.sum_congr rfl
    intro j _; cases z j <;> simp
  have htY : (∑ j, if z j then n*y1 j else 0) = n*(∑ j, if z j then y1 j else 0) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl
    intro j _; cases z j <;> simp
  have hcY : (∑ j, if z j then 0 else n*y0 j) = n*(∑ j, if z j then 0 else y0 j) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl
    intro j _; cases z j <;> simp
  unfold clusterDIM fixedDIM
  rw [htN, hcN, htY, hcY, mul_div_mul_left _ _ (ne_of_gt hn),
    mul_div_mul_left _ _ (ne_of_gt hn)]


/-- Total number N of randomized units across the blocks.
Each block has its own finite unit type; excluded markets are absent. -/
def blockPopulation {B : Type*} [Fintype B] (I : B → Type*) [∀ b, Fintype (I b)] : ℝ :=
  ∑ b, (Fintype.card (I b) : ℝ)

/-- Note 4 (p. 177)'s HT estimator under blocked randomization, in nested finite sums. -/
def blockedHT {B Ω : Type*} [Fintype B] (I : B → Type*) [∀ b, Fintype (I b)]
    (m : B → ℕ) (z : Ω → (b : B) → I b → Bool)
    (y0 y1 : (b : B) → I b → ℝ) (ω : Ω) : ℝ :=
  (∑ b, ∑ i, if z ω b i then y1 b i / ((m b : ℝ)/Fintype.card (I b))
    else -(y0 b i/(1-(m b : ℝ)/Fintype.card (I b)))) / blockPopulation I

/-- “weighted average of the estimate for each block” (p. 173), with N_b/N weights;
within each block the estimator is its treatment mean minus its control mean. -/
def blockedEstimate {B Ω : Type*} [Fintype B] (I : B → Type*) [∀ b, Fintype (I b)]
    (m : B → ℕ) (z : Ω → (b : B) → I b → Bool)
    (y0 y1 : (b : B) → I b → ℝ) (ω : Ω) : ℝ :=
  ∑ b, (Fintype.card (I b) : ℝ)/blockPopulation I * fixedDIM (m b) (y0 b) (y1 b) (z ω b)

/-- T8(i), p. 173 and Note 4: on every allocation with the stipulated fixed block
counts, the HT estimator equals the population-share weighted block mean differences.
Assignments across blocks need not be independent. -/
theorem blocked_weighted_identity {B Ω : Type*} [Fintype B] [Nonempty B]
    (I : B → Type*) [∀ b, Fintype (I b)] (m : B → ℕ)
    (hm : ∀ b, 0 < m b) (hmN : ∀ b, m b < Fintype.card (I b))
    (z : Ω → (b : B) → I b → Bool) (y0 y1 : (b : B) → I b → ℝ)
    (hcount : ∀ ω b, treatedCount (z ω b) = m b) (ω : Ω) :
    blockedHT I m z y0 y1 ω = blockedEstimate I m z y0 y1 ω := by
  unfold blockedHT blockedEstimate
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  rw [fixed_dim_ht (m b) (hm b) (hmN b) (y0 b) (y1 b) (z ω b)]
  unfold htEstimate
  simp only [Finset.card_univ]
  have hnb : (Fintype.card (I b) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (lt_trans (hm b) (hmN b))
  field_simp
  simp only [mul_comm]

/-- T8(ii): the common HT/block-weighted estimator is unbiased for the average
causal effect among randomized units. Equal inclusion probabilities within each
block suffice; no independence between blocks is assumed. -/
theorem blocked_estimator_unbiased {B Ω : Type*} [Fintype B] [Nonempty B] [Fintype Ω]
    (I : B → Type*) [∀ b, Fintype (I b)] (d : Design Ω) (m : B → ℕ)
    (hm : ∀ b, 0 < m b) (hmN : ∀ b, m b < Fintype.card (I b))
    (z : Ω → (b : B) → I b → Bool) (y0 y1 : (b : B) → I b → ℝ)
    (hcount : ∀ ω b, treatedCount (z ω b) = m b)
    (hp : ∀ b i, expectation d (fun ω => indicator (z ω b i)) =
      (m b : ℝ)/Fintype.card (I b)) :
    expectation d (blockedHT I m z y0 y1) =
      (∑ b, ∑ i, (y1 b i-y0 b i)) / blockPopulation I ∧
    expectation d (blockedEstimate I m z y0 y1) =
      (∑ b, ∑ i, (y1 b i-y0 b i)) / blockPopulation I := by
  have hht : expectation d (blockedHT I m z y0 y1) =
      (∑ b, ∑ i, (y1 b i-y0 b i)) / blockPopulation I := by
    unfold blockedHT
    rw [expectation_div, expectation_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    rw [expectation_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply ht_coordinate_unbiased d _ _ _ _ (hp b i)
    · have hn : (0 : ℝ) < Fintype.card (I b) := by exact_mod_cast lt_trans (hm b) (hmN b)
      exact ne_of_gt (div_pos (by exact_mod_cast hm b) hn)
    · have hn : (0 : ℝ) < Fintype.card (I b) := by exact_mod_cast lt_trans (hm b) (hmN b)
      have hp1 : (m b : ℝ)/Fintype.card (I b) < 1 :=
        (div_lt_one hn).mpr (by exact_mod_cast hmN b)
      linarith
  refine ⟨hht, ?_⟩
  have heq : blockedEstimate I m z y0 y1 = blockedHT I m z y0 y1 := by
    funext ω; exact (blocked_weighted_identity I m hm hmN z y0 y1 hcount ω).symm
  rw [heq]; exact hht

/-- Cluster assignments as treated subsets: “all individuals ... within the same
geographic cluster are assigned together” (p. 171). -/
def subsetExposure {K : ℕ} (s : Finset (Fin K)) (j : Fin K) : Bool := decide (j ∈ s)

/-- Independent Bernoulli(p) cluster law, p. 171; common probability is part of
corrected T5. This product mass specifies full independence, not only covariances. -/
def independentClusterLaw {K : ℕ} (d : Design (Finset (Fin K))) (p : ℝ) : Prop :=
  ∀ s, d.mass s = (∏ j ∈ s, p) * (∏ j ∈ Finset.univ \ s, (1-p))

/-- Complete randomization of m clusters: each treated subset of size m is uniform,
T4(iii) and T5's additional design; not attributed to the paper's word “independently”. -/
def completeClusterLaw {K : ℕ} (d : Design (Finset (Fin K))) (m : ℕ) : Prop :=
  ∀ s, d.mass s = if s.card = m then 1/(Nat.choose K m : ℝ) else 0

/-- Realization of the independent Bernoulli(p) design. -/
def bernoulliDesign (K : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Design (Finset (Fin K)) where
  mass := fun s => (∏ j ∈ s, p) * (∏ j ∈ Finset.univ \ s, (1-p))
  nonneg := fun s => mul_nonneg
    (Finset.prod_nonneg (fun _ _ => hp0)) (Finset.prod_nonneg (fun _ _ => by linarith))
  total := by
    have h := Finset.prod_add (fun (_ : Fin K) => p) (fun _ => 1-p) Finset.univ
    simpa using h.symm

/-- Finite populations underlying “average treatment effect among all subjects”
(p. 171–172), with “outcomes ... observed for all subjects” and no interference
(p. 170). The paper prints no notation. Individual potential outcomes are fixed. -/
structure ClusterPopulation (K : ℕ) where
  size : Fin K → ℕ
  positive : ∀ j, 0 < size j
  y0 : (j : Fin K) → Fin (size j) → ℝ
  y1 : (j : Fin K) → Fin (size j) → ℝ

/-- Cluster control means, “group averages” (p. 171), explicit notation. -/
def clusterMean0 {K : ℕ} (P : ClusterPopulation K) (j : Fin K) : ℝ :=
  (∑ i, P.y0 j i) / P.size j

/-- Cluster treatment means, same printed location as clusterMean0. -/
def clusterMean1 {K : ℕ} (P : ClusterPopulation K) (j : Fin K) : ℝ :=
  (∑ i, P.y1 j i) / P.size j

/-- Population shares w_j=n_j/N, corrected T5. -/
def clusterWeight {K : ℕ} (P : ClusterPopulation K) (j : Fin K) : ℝ :=
  (P.size j : ℝ) / ∑ l, (P.size l : ℝ)

/-- Individual finite-population effect, p. 172's “individual-level” estimand. -/
def populationEffect {K : ℕ} (P : ClusterPopulation K) : ℝ :=
  clusterEffect (fun j => P.size j) (clusterMean0 P) (clusterMean1 P)

/-- Difference in individual means on nonempty arms; arbitrary real extension on
empty-arm allocations. Corrected T5 allows this extension. -/
def populationEstimator {K : ℕ} (P : ClusterPopulation K)
    (empty : Finset (Fin K) → ℝ) (s : Finset (Fin K)) : ℝ :=
  if s = ∅ ∨ s = Finset.univ then empty s
  else clusterDIM (fun j => P.size j) (clusterMean0 P) (clusterMean1 P) (subsetExposure s)

/-- Largest population share, max_j w_j, corrected T5's no-dominance condition.
Use k+2 clusters, so the finite maximum always exists. -/
def maxClusterWeight {k : ℕ} (P : ClusterPopulation (k+2)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (clusterWeight P)

/-- L1, corrected T5: the sum of squared nonnegative normalized weights
lies between (max w)² and max w. This is the finite inequality behind no dominance. -/
theorem weight_square_bounds {J : Type*} [Fintype J] [Nonempty J]
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1) :
    let M := Finset.univ.sup' Finset.univ_nonempty w
    M^2 ≤ ∑ j, (w j)^2 ∧ (∑ j, (w j)^2) ≤ M := by
  classical
  dsimp only
  let M := Finset.univ.sup' Finset.univ_nonempty w
  have hle : ∀ j, w j ≤ M := fun j => Finset.le_sup' w (Finset.mem_univ j)
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty w
  constructor
  · rw [hmax]
    exact Finset.single_le_sum (fun l _ => sq_nonneg (w l)) hj
  · calc
      (∑ j, (w j)^2) ≤ ∑ j, M*w j := by
        apply Finset.sum_le_sum
        intro j _
        nlinarith [mul_nonneg (hw j) (sub_nonneg.mpr (hle j))]
      _ = M := by rw [← Finset.mul_sum, hs, mul_one]

/-- L4, corrected T5: finite-design Chebyshev inequality with ≥,
so it also bounds > events. No distributional limit theorem is assumed. -/
theorem finite_chebyshev {Ω : Type*} [Fintype Ω] (d : Design Ω)
    (X : Ω → ℝ) (t : ℝ) (ht : 0 < t) :
    probability d (fun ω => t ≤ |X ω-expectation d X|) ≤ variance d X / t^2 := by
  classical
  have hi : t^2 * probability d (fun ω => t ≤ |X ω-expectation d X|) ≤ variance d X := by
    unfold probability variance expectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω _
    by_cases h : t ≤ |X ω-∑ υ, d.mass υ*X υ|
    · simp only [if_pos h, mul_one]
      have hx : t^2 ≤ (X ω-∑ υ, d.mass υ*X υ)^2 := by
        nlinarith [sq_abs (X ω-∑ υ, d.mass υ*X υ)]
      nlinarith [mul_nonneg (d.nonneg ω) (sub_nonneg.mpr hx)]
    · simp only [if_neg h, mul_zero]
      exact mul_nonneg (d.nonneg ω) (sq_nonneg _)
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  nlinarith

/-- L5, corrected T5: the deterministic ratio error bound for one
arm, allowing arbitrary A and a fixed calendar/population mean μ. -/
theorem ratio_error_bound (A D p μ B η : ℝ) (hη : 0 < η)
    (hp : η ≤ p) (hμ : |μ| ≤ B) (hD : |D-p| < η/2) :
    η/2 ≤ D ∧ |A/D-μ| ≤ (2/η)*(|A-p*μ| +B*|D-p|) := by
  have hDlow : η/2 ≤ D := by linarith [(abs_lt.mp hD).1]
  have hDpos : 0 < D := by linarith
  have hηhalf : 0 < η/2 := by linarith
  have hid : A/D-μ = (A-p*μ+μ*(p-D))/D := by field_simp <;> ring
  have hn : 0 ≤ |A-p*μ| +B*|D-p| := by
    have hB : 0 ≤ B := (abs_nonneg μ).trans hμ
    positivity
  refine ⟨hDlow, ?_⟩
  calc
    |A/D-μ| = |A-p*μ+μ*(p-D)|/D := by rw [hid, abs_div, abs_of_pos hDpos]
    _ ≤ (|A-p*μ| +B*|D-p|)/D := by
      apply div_le_div_of_nonneg_right _ hDpos.le
      calc
        |A-p*μ+μ*(p-D)| ≤ |A-p*μ| +|μ*(p-D)| := abs_add_le _ _
        _ = |A-p*μ| +|μ| *|D-p| := by rw [abs_mul, abs_sub_comm p D]
        _ ≤ |A-p*μ| +B*|D-p| := by
          gcongr
    _ ≤ (|A-p*μ| +B*|D-p|)/(η/2) := div_le_div_of_nonneg_left hn hηhalf hDlow
    _ = (2/η)*(|A-p*μ| +B*|D-p|) := by field_simp <;> ring

/-- L5, both arms: the treatment and control ratios share the same denominator
concentration requirement. Corrected T5. -/
theorem two_arm_ratio_bound (A C D p μ1 μ0 B η : ℝ) (hη : 0 < η)
    (hp : η ≤ p ∧ p ≤ 1-η) (hμ : |μ1| ≤ B ∧ |μ0| ≤ B) (hD : |D-p| < η/2) :
    η/2 ≤ D ∧ η/2 ≤ 1-D ∧
    |A/D-μ1| ≤ (2/η)*(|A-p*μ1| +B*|D-p|) ∧
    |C/(1-D)-μ0| ≤ (2/η)*(|C-(1-p)*μ0| +B*|D-p|) := by
  have h0 := ratio_error_bound A D p μ1 B η hη hp.1 hμ.1 hD
  have hc : |(1-D)-(1-p)| = |D-p| := by
    have : (1-D)-(1-p) = -(D-p) := by ring
    rw [this, abs_neg]
  have h1 := ratio_error_bound C (1-D) (1-p) μ0 B η hη (by linarith [hp.2]) hμ.2
    (by rw [hc]; exact hD)
  exact ⟨h0.1,h1.1,h0.2,by simpa only [hc] using h1.2⟩

/-- Auxiliary monotonicity of weighted finite expectation. This lemma is used for corrected T5, p. 171. -/
theorem expectation_mono {Ω : Type*} [Fintype Ω] (d : Design Ω) (X Y : Ω → ℝ)
    (h : ∀ ω, X ω ≤ Y ω) : expectation d X ≤ expectation d Y := by
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (h ω) (d.nonneg ω)

/-- Auxiliary monotonicity of design event probabilities. This lemma is used for corrected T5, p. 171. -/
theorem probability_mono {Ω : Type*} [Fintype Ω] (d : Design Ω) (P Q : Ω → Prop)
    (h : ∀ ω, P ω → Q ω) : probability d P ≤ probability d Q := by
  classical
  apply expectation_mono
  intro ω
  by_cases hp : P ω
  · simp [hp, h ω hp]
  · by_cases hq : Q ω <;> simp [hp, hq]

/-- Auxiliary bounds on a finite design event probability. This lemma is used for corrected T5, p. 171. -/
theorem probability_bounds {Ω : Type*} [Fintype Ω] (d : Design Ω) (P : Ω → Prop) :
    0 ≤ probability d P ∧ probability d P ≤ 1 := by
  classical
  constructor
  · have h := expectation_mono d (fun _ => 0) (fun ω => if P ω then 1 else 0)
      (by intro ω; split_ifs <;> norm_num)
    simpa only [expectation_const, probability] using h
  · have h := expectation_mono d (fun ω => if P ω then 1 else 0) (fun _ => 1)
      (by intro ω; split_ifs <;> norm_num)
    simpa only [expectation_const, probability] using h

/-- Auxiliary counting formula for uniform finite design probabilities. This lemma is used for corrected T5, p. 171. -/
theorem uniform_probability_card {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] :
    probability (uniformDesign Ω) P =
      ((Finset.univ.filter P).card : ℝ)/Fintype.card Ω := by
  classical
  simp [probability, expectation, uniformDesign, div_eq_mul_inv, Finset.sum_ite, mul_comm]

/-- T4's concrete population: K=k+2 clusters, one of size K², all others size 1;
large-cluster potential outcomes 1/2,3/4, singleton outcomes 1/4,1/2.
All individual effects are 1/4 and outcomes lie in (0,1). -/
def dominantPopulation (k : ℕ) : ClusterPopulation (k+2) where
  size := fun j => if j.val = 0 then (k+2)^2 else 1
  positive := fun j => by split_ifs <;> positivity
  y0 := fun j _ => if j.val = 0 then 1/2 else 1/4
  y1 := fun j _ => if j.val = 0 then 3/4 else 1/2

/-- T4(i)'s exact estimate as a function of total cluster count K, treated count m,
and the treatment status of cluster 1. Derived by substitution into individual means. -/
def dominantValue (K m : ℝ) (largeTreated : Bool) : ℝ :=
  if largeTreated then 1/4+(1/4)*K^2/(K^2+m-1)
  else 1/4-(1/4)*K^2/(K^2+K-m-1)

/-- Auxiliary sum of two types of clusters, one distinguished and the rest equal. This lemma is used for counterexample T4, p. 171. -/
theorem sum_two_values {J : Type*} [DecidableEq J] (s : Finset J)
    (j0 : J) (a b : ℝ) :
    (∑ j ∈ s, if j=j0 then a else b) = (s.card : ℝ)*b + if j0 ∈ s then a-b else 0 := by
  have h : ∀ j, (if j=j0 then a else b) = b+(if j=j0 then a-b else 0) := by
    intro j; split_ifs <;> ring
  simp_rw [h]
  simp [Finset.sum_add_distrib]

/-- Auxiliary rewriting of cluster group means as sums over a treated subset. This lemma is used for counterexample T4, p. 171. -/
theorem cluster_dim_subset {K : ℕ} (s : Finset (Fin K)) (n y0 y1 : Fin K → ℝ) :
    clusterDIM n y0 y1 (subsetExposure s) =
      (∑ j ∈ s, n j*y1 j)/(∑ j ∈ s, n j) -
      (∑ j ∈ Finset.univ \ s, n j*y0 j)/(∑ j ∈ Finset.univ \ s, n j) := by
  classical
  simp [clusterDIM, subsetExposure, Finset.sum_ite, Finset.filter_not,
    Finset.filter_mem_eq_inter]

/-- T4's cluster means equal the specified constant individual outcomes. -/
theorem dominant_means (k : ℕ) :
    (∀ j, clusterMean0 (dominantPopulation k) j = if j.val=0 then 1/2 else 1/4) ∧
    (∀ j, clusterMean1 (dominantPopulation k) j = if j.val=0 then 3/4 else 1/2) := by
  constructor
  · intro j
    unfold clusterMean0
    have hy : ∀ i : Fin ((dominantPopulation k).size j),
        (dominantPopulation k).y0 j i = if j.val=0 then (1/2 : ℝ) else 1/4 := fun _ => rfl
    simp_rw [hy]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast ne_of_gt ((dominantPopulation k).positive j))
  · intro j
    unfold clusterMean1
    have hy : ∀ i : Fin ((dominantPopulation k).size j),
        (dominantPopulation k).y1 j i = if j.val=0 then (3/4 : ℝ) else 1/2 := fun _ => rfl
    simp_rw [hy]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast ne_of_gt ((dominantPopulation k).positive j))

/-- T4: every potential outcome is strictly interior and every individual effect is 1/4. -/
theorem dominant_individual_outcomes (k : ℕ) :
    ∀ j i, 0 < (dominantPopulation k).y0 j i ∧ (dominantPopulation k).y0 j i < 1 ∧
      0 < (dominantPopulation k).y1 j i ∧ (dominantPopulation k).y1 j i < 1 ∧
      (dominantPopulation k).y1 j i-(dominantPopulation k).y0 j i = 1/4 := by
  intro j i
  dsimp [dominantPopulation]
  split_ifs <;> norm_num

/-- T4: the size-weighted individual average effect is 1/4 in every population. -/
theorem dominant_effect (k : ℕ) : populationEffect (dominantPopulation k) = 1/4 := by
  unfold populationEffect clusterEffect
  simp_rw [(dominant_means k).1, (dominant_means k).2]
  have he : ∀ j : Fin (k+2),
      (if j.val=0 then (3/4 : ℝ) else 1/2)-(if j.val=0 then 1/2 else 1/4) = 1/4 := by
    intro j; split_ifs <;> norm_num
  simp_rw [he]
  rw [← Finset.sum_mul]
  have hn : (0 : ℝ) < ∑ j, ((dominantPopulation k).size j : ℝ) := by
    apply Finset.sum_pos
    · intro j _; exact_mod_cast (dominantPopulation k).positive j
    · exact Finset.univ_nonempty
  exact mul_div_cancel_left₀ _ (ne_of_gt hn)

/-- T4(i): substitution of the concrete sizes and outcomes gives the two exact
formulas on every allocation with both arms nonempty, not merely in expectation. -/
theorem dominant_exact_value (k : ℕ) (s : Finset (Fin (k+2)))
    (hs0 : s ≠ ∅) (hs1 : s ≠ Finset.univ) :
    clusterDIM (fun j => (dominantPopulation k).size j)
      (clusterMean0 (dominantPopulation k)) (clusterMean1 (dominantPopulation k))
      (subsetExposure s) = dominantValue (k+2 : ℝ) s.card (decide ((0 : Fin (k+2)) ∈ s)) := by
  classical
  rw [cluster_dim_subset]
  simp_rw [(dominant_means k).1, (dominant_means k).2]
  have hv : ∀ j : Fin (k+2), j.val=0 ↔ j=0 := by
    intro j; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [dominantPopulation, hv, Nat.cast_ite, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  have ht1 : ∀ j : Fin (k+2),
      (if j=0 then (k+2 : ℝ)^2 else 1)*(if j=0 then 3/4 else 1/2) =
      if j=0 then (k+2 : ℝ)^2*(3/4) else 1/2 := by
    intro j; split_ifs <;> ring
  have ht0 : ∀ j : Fin (k+2),
      (if j=0 then (k+2 : ℝ)^2 else 1)*(if j=0 then 1/2 else 1/4) =
      if j=0 then (k+2 : ℝ)^2*(1/2) else 1/4 := by
    intro j; split_ifs <;> ring
  simp_rw [ht1, ht0, sum_two_values]
  have hcard : (Finset.univ \ s).card = k+2-s.card := by
    simp [Finset.card_sdiff_of_subset (Finset.subset_univ s)]
  have hmpos : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs0)
  have hmless : (s.card : ℝ) < k+2 := by
    have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ s, hs1⟩)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    exact_mod_cast hc
  have hmc : ((Finset.univ \ s).card : ℝ) = (k+2 : ℝ)-s.card := by
    rw [hcard, Nat.cast_sub (by exact_mod_cast hmless.le)]; norm_num
  rw [hmc]
  by_cases hlarge : (0 : Fin (k+2)) ∈ s
  · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hlarge, not_true_eq_false,
      if_true, if_false, decide_true, dominantValue, Bool.true_eq_false]
    have hden : (k+2 : ℝ)^2+(s.card : ℝ)-1 ≠ 0 := by nlinarith [sq_nonneg (k : ℝ)]
    have hcden : (k+2 : ℝ)-(s.card : ℝ) ≠ 0 := by linarith
    ring_nf at hden hcden ⊢
    field_simp [hden, hcden] <;> ring
  · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hlarge, not_false_eq_true,
      if_true, if_false, decide_false, dominantValue, Bool.false_eq_true]
    have hden : (k+2 : ℝ)^2+(k+2)-(s.card : ℝ)-1 ≠ 0 := by nlinarith [sq_nonneg (k : ℝ)]
    ring_nf at hden ⊢
    field_simp [ne_of_gt hmpos, hden] <;> ring
    all_goals nlinarith [mul_inv_cancel₀ hden]

/-- T4(ii)'s finite deterministic separation: every nonempty allocation has
absolute error at least (1/4)K²/(K²+K-2), which is strictly greater than 1/8. -/
theorem dominant_error_bound (K m : ℝ) (hK : 2 ≤ K) (hm : 1 ≤ m) (hmK : m ≤ K-1)
    (b : Bool) :
    (1/4)*K^2/(K^2+K-2) ≤ |dominantValue K m b-1/4| ∧
    (1/8 : ℝ) < (1/4)*K^2/(K^2+K-2) := by
  have hsq : 4 ≤ K^2 := by nlinarith
  have hd : 0 < K^2+K-2 := by linarith
  have ht : 0 < K^2+m-1 := by linarith
  have hc : 0 < K^2+K-m-1 := by linarith
  have hn : 0 ≤ (1/4)*K^2 := by positivity
  constructor
  · cases b
    · simp only [dominantValue, Bool.false_eq_true, if_false]
      have hval : 1/4-(1/4)*K^2/(K^2+K-m-1)-1/4 = -((1/4)*K^2/(K^2+K-m-1)) := by ring
      rw [hval, abs_neg, abs_of_nonneg (div_nonneg hn hc.le)]
      apply div_le_div_of_nonneg_left hn hc
      linarith
    · simp only [dominantValue, if_true, add_sub_cancel_left]
      rw [abs_of_nonneg (div_nonneg hn ht.le)]
      apply div_le_div_of_nonneg_left hn ht
      linarith
  · apply (lt_div_iff₀ hd).mpr
    nlinarith [sq_nonneg (K-1)]

/-- T4: uniform subsets are exactly independent Bernoulli(1/2) cluster assignment. -/
theorem uniform_subsets_independent (K : ℕ) :
    independentClusterLaw (uniformDesign (Finset (Fin K))) (1/2) := by
  classical
  intro s
  simp only [uniformDesign, Fintype.card_finset, Fintype.card_fin, Finset.prod_const,
    Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ]
  norm_num only [show (1 : ℝ)-1/2 = 1/2 by norm_num]
  have hc : s.card ≤ K := by simpa using Finset.card_le_univ s
  rw [← pow_add, Nat.add_sub_of_le hc]
  simp [div_pow]

/-- T4(ii): exactly two of the 2^K independent half-probability allocations have
an empty arm, so the nonempty-arm probability is 1-2/2^K. -/
theorem nonempty_arm_probability (k : ℕ) :
    probability (uniformDesign (Finset (Fin (k+2))))
      (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) = 1-2/(2 : ℝ)^(k+2) := by
  classical
  rw [uniform_probability_card]
  have he : (∅ : Finset (Fin (k+2))) ≠ Finset.univ := by
    intro h; have hc := congrArg Finset.card h; simp at hc
  have hfilter : (Finset.univ.filter (fun s : Finset (Fin (k+2)) => s ≠ ∅ ∧ s ≠ Finset.univ)) =
      Finset.univ \ {∅, Finset.univ} := by ext s; simp [and_comm]
  rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have hh : ({∅,Finset.univ} : Finset (Finset (Fin (k+2)))).card = 2 := by simp [he]
  rw [hh]
  have htwo : 2 ≤ Fintype.card (Finset (Fin (k+2))) := by
    simpa only [hh] using
      Finset.card_le_univ ({∅,Finset.univ} : Finset (Finset (Fin (k+2))))
  rw [Finset.card_univ, Nat.cast_sub htwo]
  simp only [Fintype.card_finset, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- T4(ii): a positive lower bound on the error probability, independent of every
choice of estimator values on the two empty-arm allocations. -/
theorem dominant_probability_lower_bound (k : ℕ) (empty : Finset (Fin (k+2)) → ℝ) :
    1-2/(2 : ℝ)^(k+2) ≤ probability (uniformDesign (Finset (Fin (k+2))))
      (fun s => (1/8 : ℝ) < |populationEstimator (dominantPopulation k) empty s-
        populationEffect (dominantPopulation k)|) := by
  rw [← nonempty_arm_probability]
  apply probability_mono
  intro s hs
  simp only [populationEstimator, hs.1, hs.2, or_self, if_false, dominant_effect]
  rw [dominant_exact_value k s hs.1 hs.2]
  have hm : (1 : ℝ) ≤ s.card := by
    exact_mod_cast Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hs.1)
  have hmK : (s.card : ℝ) ≤ (k+2 : ℝ)-1 := by
    have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ s, hs.2⟩)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    have hcR : (s.card : ℝ) < (k+2 : ℝ) := by exact_mod_cast hc
    have hcN : s.card ≤ k+1 := by omega
    have hcR2 : (s.card : ℝ) ≤ (k : ℝ)+1 := by exact_mod_cast hcN
    linarith
  have hK : (2 : ℝ) ≤ k+2 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have h := dominant_error_bound (k+2) s.card hK hm hmK (decide ((0 : Fin (k+2)) ∈ s))
  exact lt_of_lt_of_le h.2 h.1

/-- T4's counterexample to consistency, p. 171: along K=k+2 the error probability
at ε=1/8 tends to one (and therefore cannot tend to zero), even though all effects
are 1/4, outcomes are bounded, assignment is independent at probability 1/2,
all outcomes are observed, and there is no interference. -/
theorem dominant_cluster_inconsistent
    (empty : (k : ℕ) → Finset (Fin (k+2)) → ℝ) :
    Tendsto (fun k => probability (uniformDesign (Finset (Fin (k+2))))
      (fun s => (1/8 : ℝ) < |populationEstimator (dominantPopulation k) (empty k) s-
        populationEffect (dominantPopulation k)|)) atTop (nhds 1) ∧
    ¬ Tendsto (fun k => probability (uniformDesign (Finset (Fin (k+2))))
      (fun s => (1/8 : ℝ) < |populationEstimator (dominantPopulation k) (empty k) s-
        populationEffect (dominantPopulation k)|)) atTop (nhds 0) := by
  have hgeo : Tendsto (fun k : ℕ => 2/(2 : ℝ)^(k+2)) atTop (nhds 0) := by
    have hg := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)
    have he : ∀ k : ℕ, 2/(2 : ℝ)^(k+2) = (1/2)*(1/2 : ℝ)^k := by
      intro k; rw [pow_add, div_pow]; field_simp <;> ring
    simp_rw [he]
    simpa using hg.const_mul (1/2 : ℝ)
  have hlow : Tendsto (fun k : ℕ => 1-2/(2 : ℝ)^(k+2)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hgeo
  have hlim := tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun k => dominant_probability_lower_bound k (empty k))
    (fun k => (probability_bounds _ _).2)
  refine ⟨hlim, ?_⟩
  intro hz
  have heq := tendsto_nhds_unique hlim hz
  norm_num at heq

/-- Auxiliary union bound over a finite assignment law. This lemma is used for corrected T5, p. 171. -/
theorem probability_union_le {Ω : Type*} [Fintype Ω] (d : Design Ω) (P Q : Ω → Prop) :
    probability d (fun ω => P ω ∨ Q ω) ≤ probability d P+probability d Q := by
  classical
  rw [probability, probability, probability, ← expectation_add]
  apply expectation_mono
  intro ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp,hq]

/-- L6's good-event bound, corrected T5: the stated deviation bounds imply nonempty arms and error at most 3ε/4. -/
theorem finite_ratio_good_event (A C D p μ1 μ0 B η ε : ℝ)
    (hB : 0 ≤ B) (hη : 0 < η) (hε : 0 < ε)
    (hp : η ≤ p ∧ p ≤ 1-η) (hμ : |μ1| ≤ B ∧ |μ0| ≤ B)
    (hA : |A-p*μ1| ≤ ε*η/8) (hC : |C-(1-p)*μ0| ≤ ε*η/8)
    (hD : |D-p| < min (η/2) (ε*η/(16*max B 1))) :
    0 < D ∧ D < 1 ∧ |(A/D-C/(1-D))-(μ1-μ0)| ≤ 3*ε/4 := by
  have hDη : |D-p| < η/2 := lt_of_lt_of_le hD (min_le_left _ _)
  have hDL : |D-p| ≤ ε*η/(16*max B 1) :=
    le_trans hD.le (min_le_right _ _)
  have hL : 0 < max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdev : |D-p| *(16*max B 1) ≤ ε*η :=
    (le_div_iff₀ (by positivity : 0 < 16*max B 1)).mp hDL
  have hBdev : B*|D-p| ≤ ε*η/16 := by
    have hb := mul_le_mul_of_nonneg_right (le_max_left B 1) (abs_nonneg (D-p))
    nlinarith
  have hr := two_arm_ratio_bound A C D p μ1 μ0 B η hη hp hμ hDη
  have hdpos : 0 < D := by linarith [hr.1]
  have hdlt : D < 1 := by linarith [hr.2.1]
  refine ⟨hdpos,hdlt,?_⟩
  have hid : (A/D-C/(1-D))-(μ1-μ0) = (A/D-μ1)-(C/(1-D)-μ0) := by ring
  rw [hid]
  calc
    |(A/D-μ1)-(C/(1-D)-μ0)| ≤ |A/D-μ1| +|C/(1-D)-μ0| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (A/D-μ1) 0 (C/(1-D)-μ0))
    _ ≤ (2/η)*(|A-p*μ1| +B*|D-p|)+(2/η)*(|C-(1-p)*μ0| +B*|D-p|) :=
      add_le_add hr.2.2.1 hr.2.2.2
    _ ≤ (2/η)*(ε*η/8+ε*η/16)+(2/η)*(ε*η/8+ε*η/16) := by
      gcongr
    _ = 3*ε/4 := by field_simp <;> ring

/-- L6 finite-sample probability bound, corrected T5: from the
stated means and variance bounds for A,C,D, Chebyshev and the union bound yield
the stated probability bound. X can have arbitrary empty-arm values.
This lemma explicitly assumes the moment bounds; it does not prove them for either design. -/
theorem finite_sample_probability_bound {Ω : Type*} [Fintype Ω]
    (d : Design Ω) (A C D X : Ω → ℝ) (p μ1 μ0 B η ε c W : ℝ)
    (hB : 0 ≤ B) (hη : 0 < η) (hε : 0 < ε) (hc : 0 ≤ c) (hW : 0 ≤ W)
    (hp : η ≤ p ∧ p ≤ 1-η) (hμ : |μ1| ≤ B ∧ |μ0| ≤ B)
    (hmeans : expectation d A = p*μ1 ∧ expectation d C = (1-p)*μ0 ∧ expectation d D = p)
    (hvars : variance d A ≤ (c/4)*B^2*W ∧ variance d C ≤ (c/4)*B^2*W ∧
      variance d D ≤ (c/4)*W)
    (hX : ∀ ω, 0 < D ω → D ω < 1 → X ω = A ω/D ω-C ω/(1-D ω)) :
    let δ := min (η/2) (ε*η/(16*max B 1))
    probability d (fun ω => ε ≤ |X ω-(μ1-μ0)|) ≤
      (c/4)*W*(128*B^2/(ε^2*η^2)+1/δ^2) := by
  classical
  dsimp only
  let δ := min (η/2) (ε*η/(16*max B 1))
  let t := ε*η/8
  have ht : 0 < t := by dsimp [t]; positivity
  have hδ : 0 < δ := by dsimp [δ]; apply lt_min <;> positivity
  let PA := fun ω => t ≤ |A ω-p*μ1|
  let PC := fun ω => t ≤ |C ω-(1-p)*μ0|
  let PD := fun ω => δ ≤ |D ω-p|
  have hbad : ∀ ω, ε ≤ |X ω-(μ1-μ0)| → PA ω ∨ PC ω ∨ PD ω := by
    intro ω hω
    by_contra hn
    have ha : |A ω-p*μ1| ≤ t := le_of_lt (lt_of_not_ge (by tauto))
    have hc' : |C ω-(1-p)*μ0| ≤ t := le_of_lt (lt_of_not_ge (by tauto))
    have hd : |D ω-p| < δ := lt_of_not_ge (by tauto)
    have hg := finite_ratio_good_event (A ω) (C ω) (D ω) p μ1 μ0 B η ε
      hB hη hε hp hμ ha hc' hd
    rw [hX ω hg.1 hg.2.1] at hω
    linarith [hg.2.2]
  have ha := finite_chebyshev d A t ht
  have hc' := finite_chebyshev d C t ht
  have hd := finite_chebyshev d D δ hδ
  rw [hmeans.1] at ha
  rw [hmeans.2.1] at hc'
  rw [hmeans.2.2] at hd
  calc
    probability d (fun ω => ε ≤ |X ω-(μ1-μ0)|) ≤ probability d (fun ω => PA ω ∨ PC ω ∨ PD ω) :=
      probability_mono d _ _ hbad
    _ ≤ probability d PA+(probability d PC+probability d PD) := by
      exact (probability_union_le d PA (fun ω => PC ω ∨ PD ω)).trans
        (add_le_add le_rfl (probability_union_le d PC PD))
    _ ≤ variance d A/t^2+(variance d C/t^2+variance d D/δ^2) :=
      add_le_add ha (add_le_add hc' hd)
    _ ≤ ((c/4)*B^2*W)/t^2+(((c/4)*B^2*W)/t^2+((c/4)*W)/δ^2) := by
      gcongr
      · exact hvars.1
      · exact hvars.2.1
      · exact hvars.2.2
    _ = (c/4)*W*(128*B^2/(ε^2*η^2)+1/δ^2) := by
      dsimp [t]
      field_simp <;> ring

/-- Equivalence in corrected T5: for nonnegative normalized weights, maximum
weight tends to zero iff the sum of squared weights does. -/
theorem no_dominance_iff_squared_weights
    (w : (k : ℕ) → Fin (k+2) → ℝ) (hw : ∀ k j, 0 ≤ w k j)
    (hs : ∀ k, ∑ j, w k j = 1) :
    Tendsto (fun k => Finset.univ.sup' Finset.univ_nonempty (w k)) atTop (nhds 0) ↔
    Tendsto (fun k => ∑ j, (w k j)^2) atTop (nhds 0) := by
  let M := fun k => Finset.univ.sup' Finset.univ_nonempty (w k)
  have hb := fun k => weight_square_bounds (w k) (hw k) (hs k)
  have hM : ∀ k, 0 ≤ M k := by
    intro k
    exact (hw k 0).trans (Finset.le_sup' (w k) (Finset.mem_univ 0))
  constructor
  · intro hm
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm
      (fun k => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (fun k => (hb k).2)
  · intro hw2
    have hm2 : Tendsto (fun k => (M k)^2) atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hw2
        (fun k => sq_nonneg _) (fun k => (hb k).1)
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hm2
    have he : (fun k => Real.sqrt ((M k)^2)) = M := by
      funext k; exact Real.sqrt_sq (hM k)
    change Tendsto (fun k => Real.sqrt ((M k)^2)) atTop (nhds (Real.sqrt 0)) at hsqrt
    rw [he] at hsqrt
    simpa using hsqrt

/-- Observed raw before-after contrast with T1's constant effect restored.
Unlike calendarHT it compares different calendar dates. -/
def calendarObservedBeforeAfter (s : Fin 3) : ℝ :=
  (∑ t : Fin 4, if onsetExposure s t then observed onsetExposure calendarBaseline calendarTreated s t else 0) /
    (3-s.val : ℝ) -
  (∑ t : Fin 4, if onsetExposure s t then 0 else observed onsetExposure calendarBaseline calendarTreated s t) /
    (s.val+1 : ℝ)

/-- T2(c): the actual observed raw contrast equals D(s)+2 on each onset. -/
theorem raw_observed_effect_bias :
    (∀ s, calendarObservedBeforeAfter s = calendarBeforeAfter s+2) ∧
    expectation (uniformDesign (Fin 3)) calendarObservedBeforeAfter = 12 ∧
    expectation (uniformDesign (Fin 3)) calendarObservedBeforeAfter ≠ 2 := by
  have he : ∀ s, calendarObservedBeforeAfter s = calendarBeforeAfter s+2 := by
    intro s; fin_cases s <;> norm_num [calendarObservedBeforeAfter, calendarBeforeAfter,
      observed, calendarBaseline, calendarTreated, onsetExposure, Fin.sum_univ_succ]
  have heq : calendarObservedBeforeAfter = fun s => calendarBeforeAfter s+2 := funext he
  refine ⟨he, ?_, ?_⟩ <;> rw [heq]
  · exact raw_before_after_bias.2.2.1
  · exact raw_before_after_bias.2.2.2

/-- T1(iii): exact calibration at the four attainable grid levels k/3, k=0,1,2,3. -/
theorem calendar_p_grid : ∀ k : Fin 4,
    probability (uniformDesign (Fin 3)) (fun s => randomizationP calendarBeforeAfter s ≤ (k.val : ℝ)/3) =
      (k.val : ℝ)/3 := by
  have heq : randomizationP calendarBeforeAfter = (![1,2/3,1/3] : Fin 3 → ℝ) := by
    rcases calendar_null_counterexample with ⟨_,_,_,hp0,hp1,hp2,_⟩
    funext s; fin_cases s
    · exact hp0
    · exact hp1
    · exact hp2
  intro k
  rw [heq]
  fin_cases k <;> norm_num [probability, expectation, uniformDesign, Fin.sum_univ_succ]

/-- T1(iv): a concrete randomized-timing design has a nonconstant untreated path,
an unbiased average-effect estimator, and a valid sharp-null test. This refutes the
broad design-level necessity reading of the p. 174 sentence; it cannot decide intent. -/
theorem randomized_timing_no_trend_counterexample :
    calendarBaseline 0 ≠ calendarBaseline 1 ∧
    averageEffect calendarEligible calendarBaseline calendarTreated = 2 ∧
    expectation (uniformDesign (Fin 3)) calendarHT =
      averageEffect calendarEligible calendarBaseline calendarTreated ∧
    (∀ α : ℝ, 0 ≤ α → α ≤ 1 → probability (uniformDesign (Fin 3))
      (fun s => randomizationP calendarBeforeAfter s ≤ α) ≤ α) := by
  rcases calendar_ht_counterexample with ⟨_,_,_,_,_,hne,_,_,_,hτ,hE,_⟩
  exact ⟨hne,hτ,by rw [hτ,hE],fun α h0 h1 => randomization_test_valid _ α h0 h1⟩

/-- T6 in terms of the actual observed group denominators, p. 170. Complete
randomization is covered by fixed m and common marginal m/N. -/
theorem individual_observed_dim_unbiased {J Ω : Type*} [Fintype J] [Fintype Ω]
    (d : Design Ω) (m : ℕ) (hm : 0 < m) (hmN : m < Fintype.card J)
    (z : Ω → J → Bool) (y0 y1 : J → ℝ)
    (hcount : ∀ ω, treatedCount (z ω) = m)
    (hp : ∀ j, exposureProbability d z j = (m : ℝ)/Fintype.card J) :
    expectation d (fun ω => clusterDIM (fun _ => 1) y0 y1 (z ω)) =
      averageEffect Finset.univ y0 y1 := by
  have he : (fun ω => clusterDIM (fun _ => 1) y0 y1 (z ω)) =
      fun ω => fixedDIM m y0 y1 (z ω) := by
    funext ω
    exact equal_size_dim 1 (by norm_num) m hm hmN (z ω) (hcount ω) y0 y1
  rw [he]
  exact individual_dim_unbiased d m hm hmN z y0 y1 hcount hp

/-- T8(i) with actual observed block group means instead of fixed denominators.
The equality uses the fixed-count assignment hypothesis within every block. -/
theorem blocked_actual_means_identity {B Ω : Type*} [Fintype B] [Nonempty B]
    (I : B → Type*) [∀ b, Fintype (I b)] (m : B → ℕ)
    (hm : ∀ b, 0 < m b) (hmN : ∀ b, m b < Fintype.card (I b))
    (z : Ω → (b : B) → I b → Bool) (y0 y1 : (b : B) → I b → ℝ)
    (hcount : ∀ ω b, treatedCount (z ω b) = m b) (ω : Ω) :
    blockedHT I m z y0 y1 ω =
      ∑ b, (Fintype.card (I b) : ℝ)/blockPopulation I *
        clusterDIM (fun _ => 1) (y0 b) (y1 b) (z ω b) := by
  rw [blocked_weighted_identity I m hm hmN z y0 y1 hcount ω]
  unfold blockedEstimate
  apply Finset.sum_congr rfl
  intro b _
  rw [equal_size_dim 1 (by norm_num) (m b) (hm b) (hmN b) (z ω b) (hcount ω b)]

/-- T4's main counterexample: the explicit independent half-probability sequence
satisfies bounded interior outcomes and constant positive individual effects, but
its error probability tends to one at ε=1/8, for every empty-arm extension. -/
theorem clustered_consistency_counterexample
    (empty : (k : ℕ) → Finset (Fin (k+2)) → ℝ) :
    (∀ k, independentClusterLaw (uniformDesign (Finset (Fin (k+2)))) (1/2)) ∧
    (∀ k j i, 0 < (dominantPopulation k).y0 j i ∧ (dominantPopulation k).y0 j i < 1 ∧
      0 < (dominantPopulation k).y1 j i ∧ (dominantPopulation k).y1 j i < 1 ∧
      (dominantPopulation k).y1 j i-(dominantPopulation k).y0 j i = 1/4) ∧
    (∀ k, populationEffect (dominantPopulation k) = 1/4) ∧
    Tendsto (fun k => probability (uniformDesign (Finset (Fin (k+2))))
      (fun s => (1/8 : ℝ) < |populationEstimator (dominantPopulation k) (empty k) s-
        populationEffect (dominantPopulation k)|)) atTop (nhds 1) ∧
    ¬ Tendsto (fun k => probability (uniformDesign (Finset (Fin (k+2))))
      (fun s => (1/8 : ℝ) < |populationEstimator (dominantPopulation k) (empty k) s-
        populationEffect (dominantPopulation k)|)) atTop (nhds 0) := by
  exact ⟨fun k => uniform_subsets_independent (k+2), dominant_individual_outcomes,
    dominant_effect, (dominant_cluster_inconsistent empty).1, (dominant_cluster_inconsistent empty).2⟩

/-- Weighted cluster assignment total, corrected T5 (L2). -/
def assignmentTotal {K : ℕ} (x : Fin K → ℝ) (s : Finset (Fin K)) : ℝ :=
  ∑ j ∈ s, x j

/-- Auxiliary complement-event probability identity under a finite design. This lemma is used for corrected T5, p. 171. -/
theorem probability_not {Ω : Type*} [Fintype Ω] (d : Design Ω) (P : Ω → Prop) :
    probability d (fun ω => ¬ P ω) = 1-probability d P := by
  classical
  unfold probability expectation
  apply eq_sub_iff_add_eq.mpr
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ ω, d.mass ω := by
      apply Finset.sum_congr rfl
      intro ω _; by_cases h : P ω <;> simp [h]
    _ = 1 := d.total

/-- Independent cluster-law calculation: the chance that none of the clusters
in H is treated equals (1-p)^|H|. Auxiliary to corrected T5's finite moments. -/
theorem independent_exclusion_probability {K : ℕ} (d : Design (Finset (Fin K)))
    (p : ℝ) (hd : independentClusterLaw d p) (H : Finset (Fin K)) :
    probability d (fun s => Disjoint H s) = (1-p)^H.card := by
  classical
  have he := Finset.prod_add (fun j : Fin K => if j ∈ H then (0 : ℝ) else p)
    (fun _ => 1-p) Finset.univ
  have hL : (∏ j : Fin K, ((if j ∈ H then (0 : ℝ) else p)+(1-p))) = (1-p)^H.card := by
    have hi : ∀ j : Fin K, ((if j ∈ H then (0 : ℝ) else p)+(1-p)) =
        if j ∈ H then 1-p else 1 := by intro j; split_ifs <;> ring
    simp_rw [hi]
    simp [Finset.prod_ite]
  have hR : ∀ s : Finset (Fin K),
      (∏ j ∈ s, if j ∈ H then (0 : ℝ) else p)*(∏ j ∈ Finset.univ \ s, (1-p)) =
        d.mass s*(if Disjoint H s then 1 else 0) := by
    intro s
    by_cases h : Disjoint H s
    · have hn : ∀ j ∈ s, j ∉ H := by
        intro j hjs hjH; exact Finset.disjoint_left.mp h hjH hjs
      simp only [if_pos h, mul_one, hd s]
      congr 1
      apply Finset.prod_congr rfl
      intro j hjs; simp [hn j hjs]
    · obtain ⟨j,hjH,hjs⟩ := Finset.not_disjoint_iff.mp h
      have hz : (∏ j ∈ s, if j ∈ H then (0 : ℝ) else p) = 0 := by
        apply Finset.prod_eq_zero hjs
        simp [hjH]
      simp [h,hz]
  rw [hL] at he
  simp only [Finset.powerset_univ] at he
  simp_rw [hR] at he
  calc
    probability d (fun s => Disjoint H s) = ∑ s, d.mass s*(if Disjoint H s then 1 else 0) := by
      unfold probability expectation
      apply Finset.sum_congr rfl
      intro s _; by_cases h : Disjoint H s <;> simp [h]
    _ = (1-p)^H.card := he.symm

/-- Corrected T5: a cluster in the independent product law has inclusion probability p. -/
theorem independent_marginal {K : ℕ} (d : Design (Finset (Fin K))) (p : ℝ)
    (hd : independentClusterLaw d p) (j : Fin K) :
    expectation d (fun s => indicator (subsetExposure s j)) = p := by
  classical
  have hn := independent_exclusion_probability d p hd {j}
  simp only [Finset.disjoint_singleton_left, Finset.card_singleton, pow_one] at hn
  have hnot := probability_not d (fun s => j ∈ s)
  rw [hn] at hnot
  have hi : expectation d (fun s => indicator (subsetExposure s j)) = probability d (fun s => j ∈ s) := by
    unfold probability expectation
    apply Finset.sum_congr rfl
    intro s _; by_cases h : j ∈ s <;> simp [indicator,subsetExposure,h]
  rw [hi]
  linarith

/-- Corrected T5: the independent product law has off-diagonal joint inclusion p²,
and diagonal joint inclusion p, before any weighted-sum calculation. -/
theorem independent_pair_moment {K : ℕ} (d : Design (Finset (Fin K))) (p : ℝ)
    (hd : independentClusterLaw d p) (j l : Fin K) :
    expectation d (fun s => indicator (subsetExposure s j)*indicator (subsetExposure s l)) =
      if j=l then p else p^2 := by
  classical
  by_cases hjl : j=l
  · subst l
    have he : ∀ s, indicator (subsetExposure s j)*indicator (subsetExposure s j) =
        indicator (subsetExposure s j) := by intro s; cases subsetExposure s j <;> simp [indicator]
    simp_rw [he]
    simp [independent_marginal d p hd j]
  · have hn := independent_exclusion_probability d p hd {j,l}
    have he : (fun s => indicator (subsetExposure s j)*indicator (subsetExposure s l)) =
        fun s => (indicator (subsetExposure s j)+indicator (subsetExposure s l)-1)+
          (if Disjoint ({j,l} : Finset (Fin K)) s then 1 else 0) := by
      funext s
      by_cases hjs : j ∈ s <;> by_cases hls : l ∈ s <;>
        simp [indicator, subsetExposure, hjs,hls, Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    rw [he, expectation_add, expectation_sub, expectation_add, expectation_const,
      independent_marginal d p hd j, independent_marginal d p hd l]
    have hprob : expectation d (fun s => if Disjoint ({j,l} : Finset (Fin K)) s then 1 else 0) =
        (1-p)^2 := by
      calc
        _ = probability d (fun s => Disjoint ({j,l} : Finset (Fin K)) s) := by
          unfold probability expectation
          apply Finset.sum_congr rfl
          intro s _; by_cases h : Disjoint ({j,l} : Finset (Fin K)) s <;> simp [h]
        _ = (1-p)^({j,l} : Finset (Fin K)).card := hn
        _ = (1-p)^2 := by simp [hjl]
    rw [hprob]
    simp only [if_neg hjl]
    ring

/-- Auxiliary finite variance identity E[X²]-(E[X])². This lemma is used for corrected T5, p. 171. -/
theorem finite_variance_identity {Ω : Type*} [Fintype Ω] (d : Design Ω) (X : Ω → ℝ) :
    variance d X = expectation d (fun ω => (X ω)^2)-(expectation d X)^2 := by
  have hi : (fun ω => (X ω-expectation d X)^2) =
      fun ω => (X ω)^2-(X ω*(2*expectation d X))+(expectation d X)^2 := by
    funext ω; ring
  unfold variance
  rw [hi, expectation_add, expectation_sub, expectation_mul, expectation_const]
  ring

/-- Auxiliary variance invariance under subtraction from a fixed total. This lemma is used for corrected T5, p. 171. -/
theorem variance_const_sub {Ω : Type*} [Fintype Ω] (d : Design Ω) (X : Ω → ℝ) (a : ℝ) :
    variance d (fun ω => a-X ω) = variance d X := by
  unfold variance
  rw [expectation_sub, expectation_const]
  have he : (fun ω => (a-X ω-(a-expectation d X))^2) =
      fun ω => (X ω-expectation d X)^2 := by funext ω; ring
  rw [he]

/-- Auxiliary rewriting of a treated-subset total using assignment indicators. This lemma is used for corrected T5, p. 171. -/
theorem assignment_total_indicator {K : ℕ} (x : Fin K → ℝ) (s : Finset (Fin K)) :
    assignmentTotal x s = ∑ j, indicator (subsetExposure s j)*x j := by
  simp [assignmentTotal, indicator, subsetExposure, Finset.sum_ite]

/-- Auxiliary identity: the control total is the fixed total minus the treatment total. This lemma is used for corrected T5, p. 171. -/
theorem assignment_total_complement {K : ℕ} (x : Fin K → ℝ) (s : Finset (Fin K)) :
    assignmentTotal x (Finset.univ \ s) = (∑ j, x j)-assignmentTotal x s := by
  unfold assignmentTotal
  have h := Finset.sum_sdiff (f := x) (Finset.subset_univ s)
  linarith
/-- Finite second-moment algebra for exchangeable binary indicators: given mean p
and pair moment q off the diagonal, calculate mean and variance of every weighted
sum. This is a reduction lemma, not an additional hypothesis on corrected T5. -/
theorem exchangeable_weighted_moments {J Ω : Type*} [Fintype J] [DecidableEq J] [Fintype Ω]
    (d : Design Ω) (z : Ω → J → ℝ) (p q : ℝ) (x : J → ℝ)
    (hm : ∀ j, expectation d (fun ω => z ω j) = p)
    (hpair : ∀ j l, expectation d (fun ω => z ω j*z ω l) = if j=l then p else q) :
    expectation d (fun ω => ∑ j, z ω j*x j) = p*(∑ j, x j) ∧
    variance d (fun ω => ∑ j, z ω j*x j) =
      (p-q)*(∑ j, (x j)^2)+(q-p^2)*(∑ j, x j)^2 := by
  have hmean : expectation d (fun ω => ∑ j, z ω j*x j) = p*(∑ j, x j) := by
    rw [expectation_sum]
    simp_rw [expectation_mul,hm]
    rw [← Finset.mul_sum]
  have hsq : ∀ ω, (∑ j, z ω j*x j)^2 =
      ∑ j, ∑ l, (z ω j*z ω l)*(x j*x l) := by
    intro ω
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hinner : ∀ j, (∑ l, (if j=l then p else q)*(x j*x l)) =
      q*x j*(∑ l, x l)+(p-q)*(x j)^2 := by
    intro j
    have hv : ∀ l, (if j=l then p else q)*(x j*x l) =
        q*x j*x l+(if l=j then (p-q)*(x j)^2 else 0) := by
      intro l
      by_cases hl : l=j
      · subst l; simp; ring
      · simp [hl,Ne.symm hl,mul_assoc]
    simp_rw [hv]
    simp [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsecond : expectation d (fun ω => (∑ j, z ω j*x j)^2) =
      q*(∑ j, x j)^2+(p-q)*(∑ j, (x j)^2) := by
    simp_rw [hsq]
    rw [expectation_sum]
    simp_rw [expectation_sum, expectation_mul, hpair, hinner]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  refine ⟨hmean,?_⟩
  rw [finite_variance_identity,hsecond,hmean]
  ring

/-- L2 for independent assignment, corrected T5: exact weighted
sum expectation and variance, also for control indicators 1-Z. No limit or
moment hypothesis is added to the design itself. -/
theorem independent_weighted_moments {K : ℕ} (d : Design (Finset (Fin K)))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hd : independentClusterLaw d p)
    (x : Fin K → ℝ) :
    expectation d (assignmentTotal x) = p*(∑ j, x j) ∧
    variance d (assignmentTotal x) = p*(1-p)*(∑ j, (x j)^2) ∧
    expectation d (fun s => assignmentTotal x (Finset.univ \ s)) = (1-p)*(∑ j, x j) ∧
    variance d (fun s => assignmentTotal x (Finset.univ \ s)) = p*(1-p)*(∑ j, (x j)^2) := by
  classical
  have h := exchangeable_weighted_moments d (fun s j => indicator (subsetExposure s j))
    p (p^2) x (independent_marginal d p hd) (independent_pair_moment d p hd)
  have hi : assignmentTotal x = fun s => ∑ j, indicator (subsetExposure s j)*x j :=
    funext (assignment_total_indicator x)
  have hm : expectation d (assignmentTotal x) = p*(∑ j, x j) := by rw [hi]; exact h.1
  have hv : variance d (assignmentTotal x) = p*(1-p)*(∑ j, (x j)^2) := by
    rw [hi,h.2]; ring
  have hcomp : (fun s => assignmentTotal x (Finset.univ \ s)) =
      fun s => (∑ j, x j)-assignmentTotal x s := funext (assignment_total_complement x)
  refine ⟨hm,hv,?_,?_⟩
  · rw [hcomp,expectation_sub,expectation_const,hm]; ring
  · rw [hcomp,variance_const_sub,hv]

/-- Auxiliary exact event counting for uniform fixed-count cluster randomization. This lemma is used for corrected T5, p. 171. -/
theorem complete_probability_count {K : ℕ} (d : Design (Finset (Fin K)))
    (m : ℕ) (hd : completeClusterLaw d m) (P : Finset (Fin K) → Prop) [DecidablePred P] :
    probability d P =
      ((((Finset.univ : Finset (Fin K)).powersetCard m).filter P).card : ℝ)/(Nat.choose K m : ℝ) := by
  classical
  unfold probability expectation
  have hmass : ∀ s, d.mass s = if s.card=m then 1/(Nat.choose K m : ℝ) else 0 := hd
  simp_rw [hmass]
  simp only [ite_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.univ_filter_card_eq]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv, one_mul]
  have he : (Finset.univ.filter P).filter (fun s : Finset (Fin K) => s.card=m) =
      ((Finset.univ : Finset (Fin K)).powersetCard m).filter P := by
    ext s; simp [Finset.mem_powersetCard,and_comm]
  rw [he] <;> ring

/-- Auxiliary inclusion probability for any specified H under complete assignment. This lemma is used for corrected T5, p. 171. -/
theorem complete_joint_probability {K : ℕ} (d : Design (Finset (Fin K)))
    (m : ℕ) (hd : completeClusterLaw d m) (H : Finset (Fin K)) (hH : H.card ≤ m) :
    probability d (fun s => H ⊆ s) =
      (Nat.choose (K-H.card) (m-H.card) : ℝ)/(Nat.choose K m : ℝ) := by
  classical
  rw [complete_probability_count d m hd]
  rw [Finset.card_filter_powersetCard_subset H Finset.univ m (Finset.subset_univ H) hH]
  simp

/-- Exact complete-randomization marginal, auxiliary to T5 L2 and the
unbiasedness statements: each cluster has probability m/K of treatment. -/
theorem complete_marginal {K : ℕ} (hK : 2 ≤ K) (m : ℕ) (hm : 0 < m) (hmK : m < K)
    (d : Design (Finset (Fin K))) (hd : completeClusterLaw d m) (j : Fin K) :
    expectation d (fun s => indicator (subsetExposure s j)) = (m : ℝ)/K := by
  classical
  have hprob := complete_joint_probability d m hd {j} (by simp only [Finset.card_singleton]; omega)
  simp only [Finset.singleton_subset_iff, Finset.card_singleton] at hprob
  have hi : expectation d (fun s => indicator (subsetExposure s j)) = probability d (fun s => j ∈ s) := by
    unfold probability expectation
    apply Finset.sum_congr rfl
    intro s _; by_cases h : j ∈ s <;> simp [indicator,subsetExposure,h]
  rw [hi,hprob]
  have hk1 : 1 ≤ K := by omega
  have hm1 : 1 ≤ m := hm
  have hn := Nat.add_one_mul_choose_eq (K-1) (m-1)
  rw [Nat.sub_add_cancel hk1, Nat.sub_add_cancel hm1] at hn
  have hnr : (K : ℝ)*(Nat.choose (K-1) (m-1) : ℝ) =
      (Nat.choose K m : ℝ)*(m : ℝ) := by exact_mod_cast hn
  have hk0 : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hch : (Nat.choose K m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.choose_pos hmK.le)
  field_simp [hk0,hch]
  nlinarith [hnr]

/-- Exact off-diagonal joint inclusion probability m(m-1)/(K(K-1));
auxiliary to corrected T5's complete-assignment covariance. -/
theorem complete_pair_inclusion {K : ℕ} (hK : 2 ≤ K) (m : ℕ) (hm : 0 < m) (hmK : m < K)
    (d : Design (Finset (Fin K))) (hd : completeClusterLaw d m) (j l : Fin K) (hjl : j ≠ l) :
    expectation d (fun s => indicator (subsetExposure s j)*indicator (subsetExposure s l)) =
      (m : ℝ)*(m-1)/((K : ℝ)*(K-1)) := by
  classical
  have hi : expectation d (fun s => indicator (subsetExposure s j)*indicator (subsetExposure s l)) =
      probability d (fun s => ({j,l} : Finset (Fin K)) ⊆ s) := by
    unfold probability expectation
    apply Finset.sum_congr rfl
    intro s _
    by_cases hj : j ∈ s <;> by_cases hl : l ∈ s <;>
      simp [indicator,subsetExposure,hj,hl,Finset.insert_subset_iff,Finset.singleton_subset_iff]
  rw [hi]
  by_cases hm2 : 2 ≤ m
  · have hjoint := complete_joint_probability d m hd {j,l} (by simp [hjl]; exact hm2)
    simp only [Finset.card_pair hjl] at hjoint
    rw [hjoint]
    have hk1 : 1 ≤ K := by omega
    have hk2 : 2 ≤ K := hK
    have hm1 : 1 ≤ m := hm
    have hn1 := Nat.add_one_mul_choose_eq (K-1) (m-1)
    rw [Nat.sub_add_cancel hk1, Nat.sub_add_cancel hm1] at hn1
    have hn2 := Nat.add_one_mul_choose_eq (K-2) (m-2)
    have hka : K-2+1=K-1 := by omega
    have hma : m-2+1=m-1 := by omega
    rw [hka,hma] at hn2
    have hn : K*(K-1)*Nat.choose (K-2) (m-2) = Nat.choose K m*m*(m-1) := by
      calc
        K*(K-1)*Nat.choose (K-2) (m-2) = K*((K-1)*Nat.choose (K-2) (m-2)) := by ring
        _ = K*(Nat.choose (K-1) (m-1)*(m-1)) := by rw [hn2]
        _ = (K*Nat.choose (K-1) (m-1))*(m-1) := by ring
        _ = Nat.choose K m*m*(m-1) := by rw [hn1]
    have hnr : (K : ℝ)*(K-1)*(Nat.choose (K-2) (m-2) : ℝ) =
        (Nat.choose K m : ℝ)*m*(m-1) := by
      have hc := congrArg (fun n : ℕ => (n : ℝ)) hn
      push_cast [Nat.cast_sub hk1, Nat.cast_sub hm1] at hc
      exact hc
    have hk0 : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
    have hk10 : (K : ℝ)-1 ≠ 0 := by
      have hkR : (2 : ℝ) ≤ K := by exact_mod_cast hK
      linarith
    have hch : (Nat.choose K m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.choose_pos hmK.le)
    field_simp [hk0,hk10,hch]
    nlinarith [hnr]
  · have hmone : m=1 := by omega
    subst m
    rw [complete_probability_count d 1 hd]
    have he : (((Finset.univ : Finset (Fin K)).powersetCard 1).filter
        (fun s => ({j,l} : Finset (Fin K)) ⊆ s)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro s hs
      rcases Finset.mem_filter.mp hs with ⟨hsm, hsub⟩
      have hcard := Finset.card_le_card hsub
      have hsc : s.card=1 := (Finset.mem_powersetCard.mp hsm).2
      simp [Finset.card_pair hjl, hsc] at hcard
    simp [he]

/-- L2 for complete assignment, corrected T5: exact inclusion
probabilities, off-diagonal covariances, weighted-sum variance and its upper bound,
for both treatment and control indicators. -/
theorem complete_weighted_moments {K : ℕ} (hK : 2 ≤ K) (m : ℕ) (hm : 0 < m)
    (hmK : m < K) (d : Design (Finset (Fin K))) (hd : completeClusterLaw d m)
    (x : Fin K → ℝ) :
    let p := (m : ℝ)/K
    (∀ j, expectation d (fun s => indicator (subsetExposure s j)) = p) ∧
    (∀ j l, j ≠ l →
      expectation d (fun s => indicator (subsetExposure s j)*indicator (subsetExposure s l)) - p^2 =
        -(p*(1-p)/(K-1 : ℝ))) ∧
    expectation d (assignmentTotal x) = p*(∑ j, x j) ∧
    expectation d (fun s => assignmentTotal x (Finset.univ \ s)) = (1-p)*(∑ j, x j) ∧
    variance d (assignmentTotal x) = p*(1-p)*(K : ℝ)/(K-1)*
      ((∑ j, (x j)^2)-(∑ j, x j)^2/K) ∧
    variance d (assignmentTotal x) ≤ p*(1-p)*(K : ℝ)/(K-1)*(∑ j, (x j)^2) ∧
    variance d (fun s => assignmentTotal x (Finset.univ \ s)) = p*(1-p)*(K : ℝ)/(K-1)*
      ((∑ j, (x j)^2)-(∑ j, x j)^2/K) ∧
    variance d (fun s => assignmentTotal x (Finset.univ \ s)) ≤ p*(1-p)*(K : ℝ)/(K-1)*(∑ j, (x j)^2) := by
  classical
  dsimp only
  let p : ℝ := (m : ℝ)/K
  let q : ℝ := p^2-p*(1-p)/(K-1)
  have hkR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hk0 : (K : ℝ) ≠ 0 := by linarith
  have hk10 : (K : ℝ)-1 ≠ 0 := by linarith
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (by linarith : (0 : ℝ) < K)).mpr
    exact_mod_cast hmK.le
  have hpair : ∀ j l, expectation d (fun s => indicator (subsetExposure s j)*indicator (subsetExposure s l)) =
      if j=l then p else q := by
    intro j l
    by_cases hjl : j=l
    · subst l
      have he : ∀ s, indicator (subsetExposure s j)*indicator (subsetExposure s j) =
          indicator (subsetExposure s j) := by intro s; cases subsetExposure s j <;> simp [indicator]
      simp_rw [he]
      simp only [if_true]
      exact complete_marginal hK m hm hmK d hd j
    · rw [complete_pair_inclusion hK m hm hmK d hd j l hjl, if_neg hjl]
      dsimp [p,q]
      field_simp [hk0,hk10] <;> ring
  have h := exchangeable_weighted_moments d (fun s j => indicator (subsetExposure s j)) p q x
    (complete_marginal hK m hm hmK d hd) hpair
  have hi : assignmentTotal x = fun s => ∑ j, indicator (subsetExposure s j)*x j :=
    funext (assignment_total_indicator x)
  have hmean : expectation d (assignmentTotal x) = p*(∑ j, x j) := by rw [hi]; exact h.1
  have hv : variance d (assignmentTotal x) = p*(1-p)*(K : ℝ)/(K-1)*
      ((∑ j, (x j)^2)-(∑ j, x j)^2/K) := by
    rw [hi,h.2]
    dsimp [q]
    field_simp [hk0,hk10] <;> ring
  have hcoef : 0 ≤ p*(1-p)*(K : ℝ)/(K-1) := by
    exact div_nonneg (mul_nonneg (mul_nonneg hp0 (by linarith)) (by linarith)) (by linarith)
  have hbound : variance d (assignmentTotal x) ≤ p*(1-p)*(K : ℝ)/(K-1)*(∑ j, (x j)^2) := by
    rw [hv]
    have ht : 0 ≤ (∑ j, x j)^2/(K : ℝ) := div_nonneg (sq_nonneg _) (by linarith)
    nlinarith [mul_nonneg hcoef ht]
  have hcomp : (fun s => assignmentTotal x (Finset.univ \ s)) =
      fun s => (∑ j, x j)-assignmentTotal x s := funext (assignment_total_complement x)
  refine ⟨complete_marginal hK m hm hmK d hd,?_,hmean,?_,hv,hbound,?_,?_⟩
  · intro j l hjl
    rw [hpair j l,if_neg hjl]
    dsimp [q]
    ring
  · rw [hcomp,expectation_sub,expectation_const,hmean]; ring
  · rw [hcomp,variance_const_sub,hv]
  · rw [hcomp,variance_const_sub]; exact hbound

/-- Normalized treatment total A, corrected T5. -/
def normalizedTreatmentTotal {K : ℕ} (w y1 : Fin K → ℝ) (s : Finset (Fin K)) : ℝ :=
  assignmentTotal (fun j => w j*y1 j) s

/-- Normalized control total C, corrected T5. -/
def normalizedControlTotal {K : ℕ} (w y0 : Fin K → ℝ) (s : Finset (Fin K)) : ℝ :=
  assignmentTotal (fun j => w j*y0 j) (Finset.univ \ s)

/-- L3, corrected T5: normalized totals A,C,D have the specified
means and variance upper bounds under either specified design. The weights may
be any nonnegative normalized real weights, including the population shares. -/
theorem normalized_total_moments {K : ℕ} (hK : 2 ≤ K) (d : Design (Finset (Fin K)))
    (w y0 y1 : Fin K → ℝ) (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1)
    (B p c : ℝ) (hB : 0 ≤ B) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hy : ∀ j, |y0 j| ≤ B ∧ |y1 j| ≤ B)
    (hd : (independentClusterLaw d p ∧ c=1) ∨
      ∃ m : ℕ, 0 < m ∧ m < K ∧ p=(m : ℝ)/K ∧ completeClusterLaw d m ∧ c=(K : ℝ)/(K-1)) :
    expectation d (normalizedTreatmentTotal w y1) = p*(∑ j, w j*y1 j) ∧
    expectation d (normalizedControlTotal w y0) = (1-p)*(∑ j, w j*y0 j) ∧
    expectation d (assignmentTotal w) = p ∧
    variance d (normalizedTreatmentTotal w y1) ≤ (c/4)*B^2*(∑ j, (w j)^2) ∧
    variance d (normalizedControlTotal w y0) ≤ (c/4)*B^2*(∑ j, (w j)^2) ∧
    variance d (assignmentTotal w) ≤ (c/4)*(∑ j, (w j)^2) := by
  classical
  have hkR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hquarter : p*(1-p) ≤ 1/4 := by nlinarith [sq_nonneg (p-1/2)]
  have hc0 : 0 ≤ c := by
    rcases hd with ⟨_,rfl⟩ | ⟨m,hm,hmK,hp,hdesign,hc⟩
    · norm_num
    · rw [hc]; apply div_nonneg <;> linarith
  have hmom : ∀ x : Fin K → ℝ,
      expectation d (assignmentTotal x) = p*(∑ j, x j) ∧
      expectation d (fun s => assignmentTotal x (Finset.univ \ s)) = (1-p)*(∑ j, x j) ∧
      variance d (assignmentTotal x) ≤ (c/4)*(∑ j, (x j)^2) ∧
      variance d (fun s => assignmentTotal x (Finset.univ \ s)) ≤ (c/4)*(∑ j, (x j)^2) := by
    intro x
    have hs2 : 0 ≤ ∑ j, (x j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    rcases hd with ⟨hdesign,hc⟩ | ⟨m,hm,hmK,hp,hdesign,hc⟩
    · rcases independent_weighted_moments d p hp0 hp1 hdesign x with ⟨hmean,hvar,hmeanC,hvarC⟩
      refine ⟨hmean,hmeanC,?_,?_⟩ <;> rw [hc]
      · rw [hvar]; exact mul_le_mul_of_nonneg_right hquarter hs2
      · rw [hvarC]; exact mul_le_mul_of_nonneg_right hquarter hs2
    · rcases complete_weighted_moments hK m hm hmK d hdesign x with
        ⟨hmar,hcov,hmean,hmeanC,hvar,hvarB,hvarC,hvarCB⟩
      have hcoef : p*(1-p)*c ≤ c/4 := by
        have h := mul_le_mul_of_nonneg_right hquarter hc0
        nlinarith
      have ht : variance d (assignmentTotal x) ≤ p*(1-p)*c*(∑ j, (x j)^2) := by
        simpa only [hp,hc,mul_div_assoc] using hvarB
      have htC : variance d (fun s => assignmentTotal x (Finset.univ \ s)) ≤ p*(1-p)*c*(∑ j, (x j)^2) := by
        simpa only [hp,hc,mul_div_assoc] using hvarCB
      refine ⟨by simpa only [hp] using hmean,by simpa only [hp] using hmeanC,
        ht.trans (mul_le_mul_of_nonneg_right hcoef hs2),htC.trans (mul_le_mul_of_nonneg_right hcoef hs2)⟩
  have hweight : ∀ y : Fin K → ℝ, (∀ j, |y j| ≤ B) →
      (∑ j, (w j*y j)^2) ≤ B^2*(∑ j, (w j)^2) := by
    intro y hy
    calc
      _ ≤ ∑ j, B^2*(w j)^2 := by
        apply Finset.sum_le_sum
        intro j _
        have hy2 := (sq_le_sq₀ (abs_nonneg (y j)) hB).mpr (hy j)
        rw [sq_abs] at hy2
        have h := mul_le_mul_of_nonneg_left hy2 (sq_nonneg (w j))
        convert h using 1 <;> ring
      _ = _ := by rw [← Finset.mul_sum]
  have hA := hmom (fun j => w j*y1 j)
  have hC := hmom (fun j => w j*y0 j)
  have hD := hmom w
  refine ⟨hA.1,hC.2.1,?_,?_,?_,hD.2.2.1⟩
  · rw [hD.1,hs,mul_one]
  · exact hA.2.2.1.trans (by
      have h := mul_le_mul_of_nonneg_left (hweight y1 (fun j => (hy j).2)) (by positivity : 0 ≤ c/4)
      simpa only [mul_assoc] using h)
  · exact hC.2.2.2.trans (by
      have h := mul_le_mul_of_nonneg_left (hweight y0 (fun j => (hy j).1)) (by positivity : 0 ≤ c/4)
      simpa only [mul_assoc] using h)

/-- Independent half-probability design conditional on both arms being nonempty,
T4(ii). Every remaining subset is equally likely. -/
def conditionalNonemptyDesign (k : ℕ) :
    Design {s : Finset (Fin (k+2)) // s ≠ ∅ ∧ s ≠ Finset.univ} := by
  letI : Nonempty {s : Finset (Fin (k+2)) // s ≠ ∅ ∧ s ≠ Finset.univ} :=
    ⟨⟨{0}, by
      constructor
      · simp
      · intro h
        have hc := congrArg Finset.card h
        simp at hc⟩⟩
  exact uniformDesign _

/-- Complementary nonempty allocations exchange the treatment and control arms;
auxiliary to T4's conditional unbiasedness calculation. -/
def nonemptyComplementEquiv (k : ℕ) :
    {s : Finset (Fin (k+2)) // s ≠ ∅ ∧ s ≠ Finset.univ} ≃
      {s : Finset (Fin (k+2)) // s ≠ ∅ ∧ s ≠ Finset.univ} := by
  let f : {s : Finset (Fin (k+2)) // s ≠ ∅ ∧ s ≠ Finset.univ} →
      {s : Finset (Fin (k+2)) // s ≠ ∅ ∧ s ≠ Finset.univ} :=
    fun s => ⟨s.valᶜ, by constructor <;> simp [s.property.1,s.property.2]⟩
  exact ⟨f,f,by intro s; apply Subtype.ext; exact compl_compl s.val,
    by intro s; apply Subtype.ext; exact compl_compl s.val⟩

/-- T4(ii)'s ancillary conditional unbiasedness: the inconsistency witness has
mean 1/4 even conditional on both arms nonempty. -/
theorem dominant_conditional_unbiased (k : ℕ) :
    expectation (conditionalNonemptyDesign k)
      (fun s => populationEstimator (dominantPopulation k) (fun _ => 0) s.val) = 1/4 := by
  classical
  let Ω := {s : Finset (Fin (k+2)) // s ≠ ∅ ∧ s ≠ Finset.univ}
  let X : Ω → ℝ := fun s => populationEstimator (dominantPopulation k) (fun _ => 0) s.val
  let e := nonemptyComplementEquiv k
  have hpair : ∀ s : Ω, X (e s)+X s = 1/2 := by
    intro s
    have hes : (e s).val = s.valᶜ := rfl
    dsimp [X]
    simp only [populationEstimator,(e s).property.1,(e s).property.2,s.property.1,s.property.2,
      or_self,if_false]
    rw [dominant_exact_value k _ (e s).property.1 (e s).property.2,
      dominant_exact_value k _ s.property.1 s.property.2,hes]
    have hcard : ((s.valᶜ).card : ℝ) = (k+2 : ℝ)-s.val.card := by
      rw [Finset.card_compl,Nat.cast_sub (Finset.card_le_univ s.val)]
      simp
    rw [hcard]
    by_cases h : (0 : Fin (k+2)) ∈ s.val <;>
      simp only [Finset.mem_compl,h,not_true_eq_false,not_false_eq_true,decide_true,decide_false,
        dominantValue,Bool.false_eq_true,if_true,if_false] <;> ring_nf
  have hperm : expectation (conditionalNonemptyDesign k) (fun s => X (e s)) =
      expectation (conditionalNonemptyDesign k) X := by
    unfold expectation conditionalNonemptyDesign uniformDesign
    exact e.sum_comp (fun s => (1/(Fintype.card Ω : ℝ))*X s)
  have hsum : expectation (conditionalNonemptyDesign k) (fun s => X (e s)+X s) = 1/2 := by
    have he : (fun s => X (e s)+X s) = fun _ => (1/2 : ℝ) := funext hpair
    rw [he,expectation_const]
  rw [expectation_add,hperm] at hsum
  linarith

/-- Complete randomization of half of K=2n+2 clusters, T4(iii). -/
def halfClusterDesign (n : ℕ) :
    Design {s : Finset (Fin (2*n+2)) // s.card=n+1} := by
  have hc : 0 < Fintype.card {s : Finset (Fin (2*n+2)) // s.card=n+1} := by
    simpa using (Nat.choose_pos (by omega : n+1 ≤ 2*n+2))
  letI : Nonempty {s : Finset (Fin (2*n+2)) // s.card=n+1} := Fintype.card_pos_iff.mp hc
  exact uniformDesign _

/-- T4(iii)'s ratio r_K, with K=2n+2 and m=n+1. -/
def halfDominantRatio (n : ℕ) : ℝ :=
  (2*n+2 : ℝ)^2 / ((2*n+2 : ℝ)^2+(n+1)-1)

/-- Auxiliary identification of a binary event expectation with its design probability. This lemma is used for counterexample T4, p. 171. -/
theorem probability_indicator_expected {Ω : Type*} [Fintype Ω] (d : Design Ω)
    (P : Ω → Prop) [DecidablePred P] :
    expectation d (fun ω => if P ω then 1 else 0) = probability d P := by
  classical
  unfold probability expectation
  apply Finset.sum_congr rfl
  intro ω _; by_cases h : P ω <;> simp [h]

/-- Auxiliary expectation of a two-valued statistic under any finite law. This lemma is used for counterexample T4, p. 171. -/
theorem expectation_if_constant {Ω : Type*} [Fintype Ω] (d : Design Ω)
    (P : Ω → Prop) [DecidablePred P] (a b : ℝ) :
    expectation d (fun ω => if P ω then a else b) = probability d P*a+(1-probability d P)*b := by
  classical
  have he : (fun ω => if P ω then a else b) =
      fun ω => (if P ω then (1 : ℝ) else 0)*(a-b)+b := by
    funext ω; by_cases h : P ω <;> simp [h]
  rw [he,expectation_add,expectation_mul,expectation_const,probability_indicator_expected]
  ring

/-- Auxiliary fact that an event true on every schedule has design probability one. This lemma is used for counterexample T4, p. 171. -/
theorem probability_all {Ω : Type*} [Fintype Ω] (d : Design Ω)
    (P : Ω → Prop) (h : ∀ ω, P ω) : probability d P = 1 := by
  simp [probability,expectation,h,d.total]

/-- Marginal inclusion under a uniform fixed-size subset, with the design's support
represented as a subtype. Auxiliary to T4's half-cluster ancillary distribution. -/
theorem uniform_fixed_subset_marginal {K : ℕ} (hK : 2 ≤ K) (m : ℕ)
    (hm : 0 < m) (hmK : m < K)
    [Nonempty {s : Finset (Fin K) // s.card=m}] (j : Fin K) :
    expectation (uniformDesign {s : Finset (Fin K) // s.card=m})
      (fun s => indicator (subsetExposure s.val j)) = (m : ℝ)/K := by
  classical
  have hsum : (∑ s : {s : Finset (Fin K) // s.card=m}, indicator (subsetExposure s.val j)) =
      ∑ s ∈ (Finset.univ : Finset (Fin K)).powersetCard m, if j ∈ s then (1 : ℝ) else 0 := by
    rw [Finset.sum_subtype _ (fun s => Finset.mem_powersetCard_univ)]
    apply Finset.sum_congr rfl
    intro s _; by_cases h : j ∈ s.val <;> simp [indicator,subsetExposure,h]
  unfold expectation uniformDesign
  rw [← Finset.mul_sum,hsum]
  rw [Finset.sum_boole]
  have hcount := Finset.card_filter_powersetCard_subset ({j} : Finset (Fin K)) Finset.univ m
    (Finset.subset_univ _) (by simp only [Finset.card_singleton]; omega)
  simp only [Finset.singleton_subset_iff,Finset.card_singleton,Finset.card_univ,Fintype.card_fin] at hcount
  rw [hcount]
  simp only [Fintype.card_finset_len,Fintype.card_fin]
  have hn := Nat.add_one_mul_choose_eq (K-1) (m-1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ K),Nat.sub_add_cancel (by omega : 1 ≤ m)] at hn
  have hnr : (K : ℝ)*(Nat.choose (K-1) (m-1) : ℝ) = (Nat.choose K m : ℝ)*(m : ℝ) := by exact_mod_cast hn
  have hk0 : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hch : (Nat.choose K m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.choose_pos hmK.le)
  field_simp [hk0,hch]
  nlinarith [hnr]

/-- T6's complete-randomization reading, p. 170: drawing a uniform treated subset
of size m gives an unbiased observed difference in individual means. Its equal
marginal probabilities and fixed counts are derived, rather than assumed here.
The subtype is nonempty automatically because 0<m<K. -/
theorem complete_individual_dim_unbiased {K : ℕ} (m : ℕ) (hm : 0 < m) (hmK : m < K)
    [Nonempty {s : Finset (Fin K) // s.card=m}] (y0 y1 : Fin K → ℝ) :
    expectation (uniformDesign {s : Finset (Fin K) // s.card=m})
      (fun s => clusterDIM (fun _ => 1) y0 y1 (subsetExposure s.val)) =
      averageEffect Finset.univ y0 y1 := by
  classical
  let z : {s : Finset (Fin K) // s.card=m} → Fin K → Bool := fun s => subsetExposure s.val
  have hcount : ∀ s, treatedCount (z s) = m := by
    intro s
    have he : Finset.univ.filter (fun j => subsetExposure s.val j = true) = s.val := by
      ext j; simp [subsetExposure]
    change (Finset.univ.filter (fun j => subsetExposure s.val j = true)).card=m
    rw [he]
    exact s.property
  have hp : ∀ j, exposureProbability (uniformDesign {s : Finset (Fin K) // s.card=m}) z j = (m : ℝ)/K := by
    intro j
    simpa only [exposureProbability,z] using uniform_fixed_subset_marginal (by omega : 2 ≤ K) m hm hmK j
  exact individual_observed_dim_unbiased (uniformDesign {s : Finset (Fin K) // s.card=m})
    m hm (by simpa only [Fintype.card_fin] using hmK) z y0 y1 hcount
    (fun j => by simpa only [Fintype.card_fin] using hp j)

/-- T4(iii)'s additional complete-design claims: exactly unbiased but inconsistent,
with the two specified values each of probability 1/2 and variance r_K²/16. -/
theorem dominant_complete_distribution (n : ℕ) :
    let d := halfClusterDesign n
    let X := fun s : {s : Finset (Fin (2*n+2)) // s.card=n+1} => populationEstimator (dominantPopulation (2*n)) (fun _ => 0) s.val
    probability d (fun s => (0 : Fin (2*n+2)) ∈ s.val) = 1/2 ∧
    (∀ s, X s = if (0 : Fin (2*n+2)) ∈ s.val then 1/4+(1/4)*halfDominantRatio n
      else 1/4-(1/4)*halfDominantRatio n) ∧
    expectation d X = 1/4 ∧ variance d X = (halfDominantRatio n)^2/16 ∧
    (1/2 : ℝ) < halfDominantRatio n ∧
    probability d (fun s => (1/8 : ℝ) < |X s-1/4|) = 1 := by
  classical
  dsimp only
  let Ω := {s : Finset (Fin (2*n+2)) // s.card=n+1}
  have hc : 0 < Fintype.card Ω := by
    dsimp [Ω]; simpa using (Nat.choose_pos (by omega : n+1 ≤ 2*n+2))
  letI : Nonempty Ω := Fintype.card_pos_iff.mp hc
  have hp : probability (halfClusterDesign n) (fun s => (0 : Fin (2*n+2)) ∈ s.val) = 1/2 := by
    have hm := uniform_fixed_subset_marginal (by omega : 2 ≤ 2*n+2) (n+1)
      (by omega) (by omega) (0 : Fin (2*n+2))
    have he : expectation (halfClusterDesign n) (fun s => indicator (subsetExposure s.val 0)) =
        probability (halfClusterDesign n) (fun s => (0 : Fin (2*n+2)) ∈ s.val) := by
      unfold probability expectation
      apply Finset.sum_congr rfl
      intro s _; by_cases h : (0 : Fin (2*n+2)) ∈ s.val <;> simp [indicator,subsetExposure,h]
    have hd : halfClusterDesign n = uniformDesign Ω := rfl
    rw [← he,hd,hm]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    field_simp <;> nlinarith
  have hpoint : ∀ s : Ω,
      populationEstimator (dominantPopulation (2*n)) (fun _ => 0) s.val =
        if (0 : Fin (2*n+2)) ∈ s.val then 1/4+(1/4)*halfDominantRatio n else 1/4-(1/4)*halfDominantRatio n := by
    intro s
    have hs0 : s.val ≠ ∅ := by intro h; have hc := s.property; rw [h] at hc; simp at hc
    have hs1 : s.val ≠ Finset.univ := by
      intro h; have hc := s.property; rw [h] at hc; simp at hc; omega
    simp only [populationEstimator,hs0,hs1,or_self,if_false]
    rw [dominant_exact_value (2*n) s.val hs0 hs1,s.property]
    by_cases h : (0 : Fin (2*n+2)) ∈ s.val <;>
      simp [dominantValue,halfDominantRatio,h,mul_div_assoc] <;> ring_nf
  have heq : (fun s : Ω => populationEstimator (dominantPopulation (2*n)) (fun _ => 0) s.val) =
      fun s => if (0 : Fin (2*n+2)) ∈ s.val then 1/4+(1/4)*halfDominantRatio n else 1/4-(1/4)*halfDominantRatio n :=
    funext hpoint
  have hmean : expectation (halfClusterDesign n)
      (fun s => populationEstimator (dominantPopulation (2*n)) (fun _ => 0) s.val) = 1/4 := by
    rw [heq,expectation_if_constant,hp]; ring
  have hvar : variance (halfClusterDesign n)
      (fun s => populationEstimator (dominantPopulation (2*n)) (fun _ => 0) s.val) = (halfDominantRatio n)^2/16 := by
    unfold variance
    rw [hmean]
    have he : (fun s : Ω => (populationEstimator (dominantPopulation (2*n)) (fun _ => 0) s.val-1/4)^2) =
        fun _ => (halfDominantRatio n)^2/16 := by
      funext s
      rw [hpoint s]
      split_ifs <;> ring
    rw [he,expectation_const]
  have hr : (1/2 : ℝ) < halfDominantRatio n := by
    unfold halfDominantRatio
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    apply (lt_div_iff₀ (by nlinarith [sq_nonneg (n : ℝ)] : 0 < (2*n+2 : ℝ)^2+(n+1)-1)).mpr
    nlinarith [sq_nonneg (n : ℝ)]
  refine ⟨hp,hpoint,hmean,hvar,hr,?_⟩
  apply probability_all
  intro s
  rw [hpoint s]
  have hr0 : 0 ≤ halfDominantRatio n := by linarith
  by_cases h : (0 : Fin (2*n+2)) ∈ s.val
  · rw [if_pos h,add_sub_cancel_left,abs_of_nonneg (by positivity)]
    linarith
  · rw [if_neg h]
    have he : 1/4-(1/4)*halfDominantRatio n-1/4 = -((1/4)*halfDominantRatio n) := by ring
    rw [he,abs_neg,abs_of_nonneg (by positivity)]
    linarith

/-- T4(iii): r_K tends to one along every even K=2n+2. -/
theorem half_dominant_ratio_limit : Tendsto halfDominantRatio atTop (nhds 1) := by
  have hi : Tendsto (fun n : ℕ => 1/(2*n+2 : ℝ)) atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1/2 : ℝ)
    have he : (fun n : ℕ => (1/2 : ℝ)*(1/(n+1 : ℝ))) = fun n : ℕ => 1/(2*n+2 : ℝ) := by
      funext n
      have hn : (0 : ℝ) < n+1 := by positivity
      have hk : (0 : ℝ) < 2*n+2 := by positivity
      field_simp [ne_of_gt hn,ne_of_gt hk] <;> ring
    rw [he] at h
    simpa using h
  have hb : ∀ n : ℕ, 1-1/(2*n+2 : ℝ) ≤ halfDominantRatio n ∧ halfDominantRatio n ≤ 1 := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hk : 0 < (2*n+2 : ℝ) := by positivity
    have hd : 0 < (2*n+2 : ℝ)^2+n := by positivity
    have he : halfDominantRatio n = (2*n+2 : ℝ)^2/((2*n+2 : ℝ)^2+n) := by
      unfold halfDominantRatio
      congr 1; ring
    rw [he]
    constructor
    · have hdev : (n : ℝ)/((2*n+2 : ℝ)^2+n) ≤ 1/(2*n+2 : ℝ) := by
        apply (div_le_div_iff₀ hd hk).mpr
        nlinarith [sq_nonneg (n : ℝ)]
      have hid : 1-(2*n+2 : ℝ)^2/((2*n+2 : ℝ)^2+n) =
          (n : ℝ)/((2*n+2 : ℝ)^2+n) := by field_simp [ne_of_gt hd] <;> ring
      linarith
    · apply (div_le_one hd).mpr
      linarith
  have hlo : Tendsto (fun n : ℕ => 1-1/(2*n+2 : ℝ)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hi
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun n => (hb n).1) (fun n => (hb n).2)

/-- T4(iii)'s two asymptotic ancillary claims along every even cluster count. -/
theorem dominant_complete_limits :
    Tendsto halfDominantRatio atTop (nhds 1) ∧
    Tendsto (fun n => variance (halfClusterDesign n)
      (fun s => populationEstimator (dominantPopulation (2*n)) (fun _ => 0) s.val))
      atTop (nhds (1/16)) := by
  refine ⟨half_dominant_ratio_limit,?_⟩
  have heq : (fun n => variance (halfClusterDesign n)
      (fun s => populationEstimator (dominantPopulation (2*n)) (fun _ => 0) s.val)) =
      fun n => (halfDominantRatio n)^2/16 := by
    funext n; exact (dominant_complete_distribution n).2.2.2.1
  rw [heq]
  convert (half_dominant_ratio_limit.pow 2).div_const 16 using 1 <;> simp
/-- T4(iv): total population size is K²+K-1, K=k+2, for the concrete sequence. -/
theorem dominant_total_size (k : ℕ) :
    (∑ j, ((dominantPopulation k).size j : ℝ)) = (k+2 : ℝ)^2+(k+2)-1 := by
  have hv : ∀ j : Fin (k+2), j.val=0 ↔ j=0 := by
    intro j; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [dominantPopulation, hv, Nat.cast_ite, Nat.cast_pow, Nat.cast_one,
    Nat.cast_add, Nat.cast_ofNat]
  rw [sum_two_values Finset.univ (0 : Fin (k+2))]
  simp only [Finset.mem_univ, if_true, Finset.card_univ, Fintype.card_fin,
    Nat.cast_add, Nat.cast_ofNat]
  ring

/-- T4(iv): the largest population share is K²/(K²+K-1), rather than tending to zero. -/
theorem dominant_max_weight (k : ℕ) :
    maxClusterWeight (dominantPopulation k) =
      (k+2 : ℝ)^2/((k+2 : ℝ)^2+(k+2)-1) := by
  have htot : (0 : ℝ) < (k+2 : ℝ)^2+(k+2)-1 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [sq_nonneg (k : ℝ)]
  unfold maxClusterWeight
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    unfold clusterWeight
    rw [dominant_total_size]
    apply div_le_div_of_nonneg_right _ htot.le
    dsimp [dominantPopulation]
    split_ifs
    · simp
    · norm_num only [Nat.cast_one]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [sq_nonneg (k : ℝ)]
  · have h0 := Finset.le_sup' (clusterWeight (dominantPopulation k))
      (Finset.mem_univ (0 : Fin (k+2)))
    have hw0 : clusterWeight (dominantPopulation k) (0 : Fin (k+2)) =
        (k+2 : ℝ)^2/((k+2 : ℝ)^2+(k+2)-1) := by
      unfold clusterWeight
      rw [dominant_total_size]
      simp [dominantPopulation, Nat.cast_pow]
    rw [hw0] at h0
    exact h0

/-- T4(iv)'s limit: the dominant cluster's share tends to one, explicitly showing
the violated regularity condition. -/
theorem dominant_share_limit :
    Tendsto (fun k => maxClusterWeight (dominantPopulation k)) atTop (nhds 1) := by
  have hi : Tendsto (fun k : ℕ => 1/(k+2 : ℝ)) atTop (nhds 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h
  have hd : Tendsto (fun k : ℕ => 1+1/(k+2 : ℝ)-(1/(k+2 : ℝ))^2) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add hi).sub (hi.pow 2)
  have h : Tendsto (fun k : ℕ => 1/(1+1/(k+2 : ℝ)-(1/(k+2 : ℝ))^2)) atTop (nhds 1) := by
    have hc : Tendsto (fun (_ : ℕ) => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    convert hc.div hd (by norm_num : (1 : ℝ) ≠ 0) using 1
    · ext k; simp
  have he : (fun k : ℕ => 1/(1+1/(k+2 : ℝ)-(1/(k+2 : ℝ))^2)) =
      fun k => maxClusterWeight (dominantPopulation k) := by
    funext k
    rw [dominant_max_weight]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hn : (k+2 : ℝ) ≠ 0 := by positivity
    have hden : (k+2 : ℝ)^2+(k+2)-1 ≠ 0 := by nlinarith [sq_nonneg (k : ℝ)]
    field_simp [hn,hden] <;> ring
  rw [he] at h
  exact h

/-- T4(v): at K=6, the two half-assignment formulas give 37/76 and 1/76;
there are 20 half allocations, 10 containing cluster 1. Of 64 independent
allocations, 62 have nonempty arms. The finite separation bound is 9/40. -/
theorem dominant_six_checks :
    dominantValue 6 3 true = 37/76 ∧ dominantValue 6 3 false = 1/76 ∧
    Fintype.card {s : Finset (Fin 6) // s.card=3} = 20 ∧
    (((Finset.univ : Finset (Fin 6)).powersetCard 3).filter (fun s => (0 : Fin 6) ∈ s)).card = 10 ∧
    Fintype.card (Finset (Fin 6)) = 64 ∧
    probability (uniformDesign (Finset (Fin 6))) (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) = 62/64 ∧
    (1/4 : ℝ)*6^2/(6^2+6-2) = 9/40 ∧
    ((18/19 : ℝ)^2/16) = 81/1444 := by
  have hcard : (((Finset.univ : Finset (Fin 6)).powersetCard 3).filter
      (fun s => (0 : Fin 6) ∈ s)).card = 10 := by
    have h := Finset.card_filter_powersetCard_subset ({0} : Finset (Fin 6)) Finset.univ 3
      (Finset.subset_univ _) (by simp)
    norm_num [Nat.choose] at h
    exact h
  refine ⟨by norm_num [dominantValue],by norm_num [dominantValue],
    by norm_num [Nat.choose],hcard,by norm_num,?_,by norm_num,by norm_num⟩
  have h := nonempty_arm_probability 4
  norm_num at h
  convert h using 1 <;> norm_num

/-- T4(v)'s actual K=6 population: sizes (36,1,1,1,1,1), half-design
variance 81/1444, and the minimum nonempty-allocation absolute error is 9/40.
The allocation treating every cluster except cluster 6 attains that minimum. -/
theorem dominant_six_actual_checks :
    (∀ j : Fin 6, (dominantPopulation 4).size j = if j=0 then 36 else 1) ∧
    variance (halfClusterDesign 2)
      (fun s => populationEstimator (dominantPopulation 4) (fun _ => 0) s.val) = 81/1444 ∧
    (∀ s : Finset (Fin 6), s ≠ ∅ → s ≠ Finset.univ →
      (9/40 : ℝ) ≤ |populationEstimator (dominantPopulation 4) (fun _ => 0) s-1/4|) ∧
    (∃ s : Finset (Fin 6), s ≠ ∅ ∧ s ≠ Finset.univ ∧
      |populationEstimator (dominantPopulation 4) (fun _ => 0) s-1/4| = 9/40) := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · intro j; fin_cases j <;> norm_num [dominantPopulation]
  · have h := (dominant_complete_distribution 2).2.2.2.1
    norm_num [halfDominantRatio] at h
    exact h
  · intro s hs0 hs1
    simp only [populationEstimator,hs0,hs1,or_self,if_false]
    rw [dominant_exact_value 4 s hs0 hs1]
    have hm : (1 : ℝ) ≤ s.card := by
      exact_mod_cast Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hs0)
    have hc : s.card < 6 := by
      simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ s,hs1⟩)
    have hm5 : (s.card : ℝ) ≤ (5 : ℝ) := by exact_mod_cast (by omega : s.card ≤ 5)
    have hmK : (s.card : ℝ) ≤ 6-1 := by linarith
    have h := dominant_error_bound 6 s.card (by norm_num) hm hmK (decide ((0 : Fin 6) ∈ s))
    have hb := h.1
    norm_num at hb
    convert hb using 1 <;> norm_num
  · let s : Finset (Fin 6) := Finset.univ.erase 5
    have hs0 : s ≠ ∅ := by
      apply Finset.nonempty_iff_ne_empty.mp
      exact ⟨0,by simp [s]⟩
    have hs1 : s ≠ Finset.univ := by
      intro h
      have hc := congrArg Finset.card h
      norm_num [s] at hc
    refine ⟨s,hs0,hs1,?_⟩
    simp only [populationEstimator,hs0,hs1,or_self,if_false]
    rw [dominant_exact_value 4 s hs0 hs1]
    norm_num [s,dominantValue]

/-- Auxiliary positivity of the individual population size in corrected T5. -/
theorem population_total_positive {k : ℕ} (P : ClusterPopulation (k+2)) :
    (0 : ℝ) < ∑ j, (P.size j : ℝ) := by
  apply Finset.sum_pos
  · intro j _; exact_mod_cast P.positive j
  · exact Finset.univ_nonempty

/-- Corrected T5's actual population shares are positive and sum to one. -/
theorem population_weights {k : ℕ} (P : ClusterPopulation (k+2)) :
    (∀ j, 0 < clusterWeight P j) ∧ (∑ j, clusterWeight P j) = 1 := by
  have hn := population_total_positive P
  constructor
  · intro j; exact div_pos (by exact_mod_cast P.positive j) hn
  · unfold clusterWeight
    rw [← Finset.sum_div,div_self (ne_of_gt hn)]

/-- An individual outcome bound also bounds its cluster's mean, corrected T5. -/
theorem finite_mean_abs_bound (n : ℕ) (hn : 0 < n) (y : Fin n → ℝ) (B : ℝ)
    (hy : ∀ i, |y i| ≤ B) : |(∑ i, y i)/(n : ℝ)| ≤ B := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_div,abs_of_pos hnR]
  calc
    |∑ i, y i|/(n : ℝ) ≤ (∑ i, |y i|)/(n : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hnR.le
    _ ≤ ((n : ℝ)*B)/(n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      calc
        (∑ i, |y i|) ≤ ∑ _i : Fin n, B := Finset.sum_le_sum (fun i _ => hy i)
        _ = (n : ℝ)*B := by simp
    _ = B := mul_div_cancel_left₀ _ (ne_of_gt hnR)

/-- Bounded cluster outcomes also bound the population-share weighted arm mean. This lemma is used for corrected T5, p. 171. -/
theorem weighted_mean_abs_bound {J : Type*} [Fintype J] (w y : J → ℝ) (B : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1) (hy : ∀ j, |y j| ≤ B) :
    |∑ j, w j*y j| ≤ B := by
  calc
    _ ≤ ∑ j, |w j*y j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, w j*|y j| := by
      apply Finset.sum_congr rfl
      intro j _; rw [abs_mul,abs_of_nonneg (hw j)]
    _ ≤ ∑ j, w j*B := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hy j) (hw j))
    _ = B := by rw [← Finset.sum_mul,hs,one_mul]

/-- Corrected T5: size-weighted effect equals the difference of normalized arm means. -/
theorem population_effect_normalized {k : ℕ} (P : ClusterPopulation (k+2)) :
    populationEffect P = (∑ j, clusterWeight P j*clusterMean1 P j)-
      (∑ j, clusterWeight P j*clusterMean0 P j) := by
  unfold populationEffect clusterEffect clusterWeight
  simp_rw [mul_sub,div_mul_eq_mul_div]
  rw [Finset.sum_sub_distrib,← Finset.sum_div,← Finset.sum_div,sub_div]

/-- Corrected T5's actual individual mean difference equals A/D-C/(1-D) whenever
0<D<1. Empty-arm values are arbitrary and the overlap condition handles them. -/
theorem population_estimator_normalized {k : ℕ} (P : ClusterPopulation (k+2))
    (empty : Finset (Fin (k+2)) → ℝ) (s : Finset (Fin (k+2)))
    (hD0 : 0 < assignmentTotal (clusterWeight P) s)
    (hD1 : assignmentTotal (clusterWeight P) s < 1) :
    populationEstimator P empty s =
      normalizedTreatmentTotal (clusterWeight P) (clusterMean1 P) s/assignmentTotal (clusterWeight P) s -
      normalizedControlTotal (clusterWeight P) (clusterMean0 P) s/(1-assignmentTotal (clusterWeight P) s) := by
  have hw := population_weights P
  have hs0 : s ≠ ∅ := by intro h; subst s; simpa [assignmentTotal] using hD0
  have hs1 : s ≠ Finset.univ := by
    intro h; subst s
    have he : assignmentTotal (clusterWeight P) Finset.univ=1 := hw.2
    linarith
  simp only [populationEstimator,hs0,hs1,or_self,if_false]
  rw [cluster_dim_subset]
  have hc : 1-assignmentTotal (clusterWeight P) s = assignmentTotal (clusterWeight P) (Finset.univ \ s) := by
    rw [assignment_total_complement,hw.2]
  rw [hc]
  unfold normalizedTreatmentTotal normalizedControlTotal assignmentTotal clusterWeight
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div,← Finset.sum_div,← Finset.sum_div,← Finset.sum_div]
  rw [div_div_div_cancel_right₀ (ne_of_gt (population_total_positive P)),
      div_div_div_cancel_right₀ (ne_of_gt (population_total_positive P))]

/-- L6 for the actual individual population and either stipulated cluster design,
corrected T5. The moment assumptions in the abstract bound are derived here,
rather than imposed as extra population hypotheses. -/
theorem cluster_population_probability_bound {k : ℕ} (P : ClusterPopulation (k+2))
    (d : Design (Finset (Fin (k+2)))) (empty : Finset (Fin (k+2)) → ℝ)
    (B η ε p c : ℝ) (hB : 0 ≤ B) (hη : 0 < η) (hε : 0 < ε)
    (hbound : ∀ j i, |P.y0 j i| ≤ B ∧ |P.y1 j i| ≤ B)
    (hp : η ≤ p ∧ p ≤ 1-η)
    (hd : (independentClusterLaw d p ∧ c=1) ∨
      ∃ m : ℕ, 0 < m ∧ m < k+2 ∧ p=(m : ℝ)/(k+2) ∧ completeClusterLaw d m ∧ c=(k+2 : ℝ)/(k+1)) :
    let δ := min (η/2) (ε*η/(16*max B 1))
    probability d (fun s => ε ≤ |populationEstimator P empty s-populationEffect P|) ≤
      (c/4)*(∑ j, (clusterWeight P j)^2)*(128*B^2/(ε^2*η^2)+1/δ^2) := by
  classical
  dsimp only
  have hw := population_weights P
  have hy0 : ∀ j, |clusterMean0 P j| ≤ B :=
    fun j => finite_mean_abs_bound (P.size j) (P.positive j) (P.y0 j) B (fun i => (hbound j i).1)
  have hy1 : ∀ j, |clusterMean1 P j| ≤ B :=
    fun j => finite_mean_abs_bound (P.size j) (P.positive j) (P.y1 j) B (fun i => (hbound j i).2)
  have hp0 : 0 ≤ p := by linarith [hp.1]
  have hp1 : p ≤ 1 := by linarith [hp.2]
  have hd' : (independentClusterLaw d p ∧ c=1) ∨
      ∃ m : ℕ, 0 < m ∧ m < k+2 ∧ p=(m : ℝ)/((k+2 : ℕ) : ℝ) ∧ completeClusterLaw d m ∧
        c=((k+2 : ℕ) : ℝ)/(((k+2 : ℕ) : ℝ)-1) := by
    have hden : (k+2 : ℝ)-1 = k+1 := by ring
    simpa only [Nat.cast_add,Nat.cast_ofNat,hden] using hd
  have hm := normalized_total_moments (by omega : 2 ≤ k+2) d (clusterWeight P) (clusterMean0 P) (clusterMean1 P)
    (fun j => (hw.1 j).le) hw.2 B p c hB hp0 hp1 (fun j => ⟨hy0 j,hy1 j⟩) hd'
  have hc : 0 ≤ c := by
    rcases hd with ⟨_,rfl⟩ | ⟨m,hm,hmK,hp,hdesign,hc⟩
    · norm_num
    · rw [hc]; positivity
  have h := finite_sample_probability_bound d
    (normalizedTreatmentTotal (clusterWeight P) (clusterMean1 P))
    (normalizedControlTotal (clusterWeight P) (clusterMean0 P))
    (assignmentTotal (clusterWeight P)) (populationEstimator P empty)
    p (∑ j, clusterWeight P j*clusterMean1 P j) (∑ j, clusterWeight P j*clusterMean0 P j)
    B η ε c (∑ j, (clusterWeight P j)^2) hB hη hε hc
    (Finset.sum_nonneg (fun j _ => sq_nonneg _)) hp
    ⟨weighted_mean_abs_bound _ _ B (fun j => (hw.1 j).le) hw.2 hy1,
      weighted_mean_abs_bound _ _ B (fun j => (hw.1 j).le) hw.2 hy0⟩
    ⟨hm.1,hm.2.1,hm.2.2.1⟩ ⟨hm.2.2.2.1,hm.2.2.2.2.1,hm.2.2.2.2.2⟩
    (fun s h0 h1 => population_estimator_normalized P empty s h0 h1)
  simpa only [population_effect_normalized] using h

/-- T5, p. 171, corrected: bounded individual outcomes, a common interior
probability, independent Bernoulli or uniform fixed-count cluster assignment, and
no dominant cluster imply consistency for the changing individual-level effect.
No convergence of p_k or τ_k, and no restriction on the empty-arm extension, is imposed.
The index k denotes a population with k+2 clusters. -/
theorem corrected_cluster_consistency
    (P : (k : ℕ) → ClusterPopulation (k+2))
    (d : (k : ℕ) → Design (Finset (Fin (k+2)))) (p : ℕ → ℝ)
    (empty : (k : ℕ) → Finset (Fin (k+2)) → ℝ)
    (B η : ℝ) (hB : 0 ≤ B) (hη : 0 < η)
    (hbound : ∀ k j i, |(P k).y0 j i| ≤ B ∧ |(P k).y1 j i| ≤ B)
    (hdesign : ∀ k, independentClusterLaw (d k) (p k) ∨
      ∃ m : ℕ, 0 < m ∧ m < k+2 ∧ p k = (m : ℝ)/(k+2) ∧ completeClusterLaw (d k) m)
    (hinterior : ∀ k, η ≤ p k ∧ p k ≤ 1-η)
    (hdominance : Tendsto (fun k => maxClusterWeight (P k)) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun k => probability (d k)
        (fun s => ε < |populationEstimator (P k) (empty k) s - populationEffect (P k)|))
        atTop (nhds 0) := by
  classical
  intro ε hε
  let δ := min (η/2) (ε*η/(16*max B 1))
  let Q := 128*B^2/(ε^2*η^2)+1/δ^2
  have hδ : 0 < δ := by dsimp [δ]; apply lt_min <;> positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hW : Tendsto (fun k => ∑ j, (clusterWeight (P k) j)^2) atTop (nhds 0) := by
    have h := no_dominance_iff_squared_weights (fun k => clusterWeight (P k))
      (fun k j => ((population_weights (P k)).1 j).le) (fun k => (population_weights (P k)).2)
    exact h.mp hdominance
  have hupper : ∀ k, probability (d k)
      (fun s => ε < |populationEstimator (P k) (empty k) s-populationEffect (P k)|) ≤
        (1/2)*Q*(∑ j, (clusterWeight (P k) j)^2) := by
    intro k
    have hex : ∃ c : ℝ, 0 ≤ c ∧ c ≤ 2 ∧
        ((independentClusterLaw (d k) (p k) ∧ c=1) ∨
          ∃ m : ℕ, 0 < m ∧ m < k+2 ∧ p k=(m : ℝ)/(k+2) ∧
            completeClusterLaw (d k) m ∧ c=(k+2 : ℝ)/(k+1)) := by
      rcases hdesign k with hi | ⟨m,hm,hmK,hp,hc⟩
      · exact ⟨1,by norm_num,by norm_num,Or.inl ⟨hi,rfl⟩⟩
      · refine ⟨(k+2 : ℝ)/(k+1),by positivity,?_,Or.inr ⟨m,hm,hmK,hp,hc,rfl⟩⟩
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
    obtain ⟨c,hc0,hc2,hd⟩ := hex
    have hb := cluster_population_probability_bound (P k) (d k) (empty k)
      B η ε (p k) c hB hη hε (hbound k) (hinterior k) hd
    have hws : 0 ≤ ∑ j, (clusterWeight (P k) j)^2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    calc
      _ ≤ probability (d k)
          (fun s => ε ≤ |populationEstimator (P k) (empty k) s-populationEffect (P k)|) :=
        probability_mono (d k) _ _ (fun s hs => hs.le)
      _ ≤ (c/4)*(∑ j, (clusterWeight (P k) j)^2)*Q := hb
      _ ≤ (1/2)*Q*(∑ j, (clusterWeight (P k) j)^2) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hc2) (mul_nonneg hws hQ)]
  have hu : Tendsto (fun k => (1/2)*Q*(∑ j, (clusterWeight (P k) j)^2)) atTop (nhds 0) := by
    simpa using hW.const_mul ((1/2)*Q)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun k => (probability_bounds (d k) _).1) hupper


end
end AronowAudit.P024
