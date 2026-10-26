import Mathlib

/-!
P014: The Regression Discontinuity Design Under Interference (2017).
Printed pp. 129--131, PDF pp. 2--4. Finite sums use actual distinct support
points. No assumption of independence or no interference is built into the model.
Fin N uses indices 0,...,N-1 in place of the paper's 1,...,N.
-/

namespace AronowAudit.P014

open scoped BigOperators

set_option maxHeartbeats 800000
noncomputable section

/-- "Supp (Z)": the distinct points of positive probability (p. 131).
A finite probability law, with strictly positive masses on its support and total
mass one. The mass function away from the support is immaterial. -/
structure FiniteLaw (α : Type*) where
  support : Finset α
  mass : α → ℝ
  positive : ∀ a ∈ support, 0 < mass a
  total : ∑ a ∈ support, mass a = 1

/-- "E" over the randomization distribution: the weighted finite sum (p. 131). -/
def FiniteLaw.expect {α : Type*} (L : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ a ∈ L.support, L.mass a * f a

/-- "Pr" over the joint law of X (p. 130); probability of an event. -/
def FiniteLaw.prob {α : Type*} (L : FiniteLaw α) (P : α → Prop) : ℝ := by
  classical
  exact ∑ a ∈ L.support, if P a then L.mass a else 0

/-- A pushforward law: "the joint distribution of X ... fully determines the
joint distribution of Z" (p. 130). Image is a set, so repeated images count once. -/
def FiniteLaw.map {α β : Type*} (L : FiniteLaw α) (f : α → β) : FiniteLaw β := by
  classical
  refine ⟨L.support.image f, fun b => L.prob (fun a => f a = b), ?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    unfold FiniteLaw.prob
    have hle : L.mass a ≤ ∑ x ∈ L.support, if f x = f a then L.mass x else 0 := by
      have hnonneg : ∀ x ∈ L.support,
          0 ≤ (if f x = f a then L.mass x else 0) := by
        intro x hx
        split_ifs
        · exact (L.positive x hx).le
        · exact le_rfl
      simpa using Finset.single_le_sum hnonneg ha
    exact lt_of_lt_of_le (L.positive a ha) hle
  · unfold FiniteLaw.prob
    rw [Finset.sum_comm]
    calc
      _ = ∑ a ∈ L.support, L.mass a := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [Finset.mem_image_of_mem f ha]
      _ = 1 := L.total

/-- Linearity and the threshold pushforward used on pp. 130--131. -/
theorem expect_map {α β : Type*} (L : FiniteLaw α) (f : α → β) (g : β → ℝ) :
    (L.map f).expect g = L.expect (g ∘ f) := by
  classical
  unfold FiniteLaw.expect FiniteLaw.map FiniteLaw.prob
  simp only
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp [Finset.mem_image_of_mem f ha, Function.comp_def]

/-- "z_i ∈ {0,1}" and "z=(z_1,...,z_N)'" (p. 130). -/
abbrev Assignment (N : ℕ) := Fin N → Bool

/-- "2^N fixed potential outcomes, y_i(z)" (p. 130), for every binary vector;
real valued, with arbitrary interference, and no additional dependence on X. -/
abbrev Outcomes (N : ℕ) := Fin N → Assignment N → ℝ

/-- The real value of binary treatment, 0 control and 1 treatment (p. 130). -/
def bit (a : Bool) : ℝ := if a then 1 else 0

/-- "Z_i=1 ... if X_i ≥ 0 ... else ... 0" (p. 130). -/
def threshold {N : ℕ} (x : Fin N → ℝ) : Assignment N := fun i => decide (0 ≤ x i)

/-- "W_0=[-b,b]" (p. 130). -/
def inWindow (b x : ℝ) : Prop := -b ≤ x ∧ x ≤ b

/-- "N_0=Σ I(X_i∈W_0)" (p. 130), as a cardinality. -/
def windowSet {N : ℕ} (b : ℝ) (x : Fin N → ℝ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i => inWindow b (x i))

/-- "F_{x,W_0} ... the empirical distribution function of X_i for all subjects
such that X_i∈W_0" (p. 130); S is the fixed window set. -/
def empiricalCDF {N : ℕ} (S : Finset (Fin N)) (x : Fin N → ℝ) (t : ℝ) : ℝ := by
  classical
  exact (∑ i ∈ S, if x i ≤ t then (1 : ℝ) else 0) / S.card

/-- Arm subsets K_{i,a} of distinct supported treatment vectors, the index set
of the printed individual average on p. 131 (T3 notation). -/
def armSupport {N : ℕ} (L : FiniteLaw (Assignment N)) (i : Fin N) (a : Bool) :=
  L.support.filter (fun z => z i = a)

/-- Pr(Z_i=a), the corrected denominator in P014-T2 (correction to p. 131). -/
def armMass {N : ℕ} (L : FiniteLaw (Assignment N)) (i : Fin N) (a : Bool) : ℝ :=
  ∑ z ∈ armSupport L i a, L.mass z

/-- The probability-weighted numerator of corrected Ybar_i(a), P014-T2. -/
def weightedNumerator {N : ℕ} (L : FiniteLaw (Assignment N)) (y : Outcomes N)
    (i : Fin N) (a : Bool) : ℝ := ∑ z ∈ armSupport L i a, L.mass z * y i z

/-- "Ybar_i(z)=Σ y_i(z) I(z_i=z) / Σ I(z_i=z)" (p. 131),
the printed unweighted average over distinct supported vectors. -/
def printedMean {N : ℕ} (L : FiniteLaw (Assignment N)) (y : Outcomes N)
    (i : Fin N) (a : Bool) : ℝ :=
  (∑ z ∈ armSupport L i a, y i z) / (armSupport L i a).card

/-- The corrected "Ybar_i(a)=Σ p(z)y_i(z)I(z_i=a)/Σ p(z)I(z_i=a)"
(P014-T2, correction to p. 131). This is conditional expectation on a positive arm. -/
def weightedMean {N : ℕ} (L : FiniteLaw (Assignment N)) (y : Outcomes N)
    (i : Fin N) (a : Bool) : ℝ := weightedNumerator L y i a / armMass L i a

/-- "τ=N_0⁻¹ Σ [Ybar_i(1)-Ybar_i(0)]" (p. 131), with the summand
bracketed as corrected in P014-T8. Applies to either definition of Ybar. -/
def windowContrast {N : ℕ} (S : Finset (Fin N)) (μ : Fin N → Bool → ℝ) : ℝ :=
  (∑ i ∈ S, (μ i true - μ i false)) / S.card

/-- Arm count Σ Z_i, or Σ (1-Z_i), in the estimator display (p. 131). -/
def armCount {N : ℕ} (S : Finset (Fin N)) (z : Assignment N) (a : Bool) : ℝ :=
  ∑ i ∈ S, if z i = a then (1 : ℝ) else 0

/-- The observed outcome is "Y_i=y_i(Z)" (p. 130); these are the observed
outcome totals within each arm in the estimator display (p. 131). -/
def armTotal {N : ℕ} (S : Finset (Fin N)) (y : Outcomes N)
    (z : Assignment N) (a : Bool) : ℝ := ∑ i ∈ S, if z i = a then y i z else 0

/-- "τhat=Σ Y_i Z_i/Σ Z_i - Σ Y_i(1-Z_i)/Σ(1-Z_i)" (p. 131). -/
def differenceInMeans {N : ℕ} (S : Finset (Fin N)) (y : Outcomes N)
    (z : Assignment N) : ℝ :=
  armTotal S y z true / armCount S z true - armTotal S y z false / armCount S z false

/-- T8, the missing brackets on p. 131: the mean of differences is the
difference of the two sums divided by the window size. -/
theorem bracketed_contrast {N : ℕ} (S : Finset (Fin N)) (μ : Fin N → Bool → ℝ)
    (_hS : S.Nonempty) :
    windowContrast S μ = ((∑ i ∈ S, μ i true) - ∑ i ∈ S, μ i false) / S.card := by
  simp [windowContrast, Finset.sum_sub_distrib]

/-- Finite identity behind T2 step (1): binary arm counts sum to N_0 (p. 131). -/
theorem armCounts_add {N : ℕ} (S : Finset (Fin N)) (z : Assignment N) :
    armCount S z true + armCount S z false = S.card := by
  unfold armCount
  rw [← Finset.sum_add_distrib]
  have : ∀ i, (if z i = true then (1 : ℝ) else 0) +
      (if z i = false then (1 : ℝ) else 0) = 1 := by intro i; cases z i <;> simp
  simp_rw [this]
  simp

/-- Finite identity behind T2 step (3): the two arm probabilities sum to one. -/
theorem armMasses_add {N : ℕ} (L : FiniteLaw (Assignment N)) (i : Fin N) :
    armMass L i true + armMass L i false = 1 := by
  classical
  simp only [armMass, armSupport, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  have : ∀ z : Assignment N, (if z i = true then L.mass z else 0) +
      (if z i = false then L.mass z else 0) = L.mass z := by intro z; cases z i <;> simp
  simp_rw [this]
  exact L.total

/-- T2 step (1) and linearity in step (4): if the window count is fixed at m,
the expectation is the difference of the two summed arm moments / fixed counts. -/
theorem expectation_fixed_counts {N : ℕ} (L : FiniteLaw (Assignment N))
    (S : Finset (Fin N)) (y : Outcomes N) (m : ℝ)
    (hc : ∀ z ∈ L.support, armCount S z true = m) :
    L.expect (differenceInMeans S y) =
      (∑ i ∈ S, weightedNumerator L y i true) / m -
      (∑ i ∈ S, weightedNumerator L y i false) / (S.card - m) := by
  classical
  have hf : ∀ z ∈ L.support, armCount S z false = S.card - m := by
    intro z hz; have := armCounts_add S z; rw [hc z hz] at this; linarith
  have exchange (a : Bool) (d : ℝ) :
      (∑ z ∈ L.support, L.mass z * (armTotal S y z a / d)) =
      (∑ i ∈ S, weightedNumerator L y i a) / d := by
    simp only [armTotal, weightedNumerator, armSupport, Finset.sum_filter,
      mul_div_assoc, Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro z hz
    split_ifs <;> ring
  unfold FiniteLaw.expect differenceInMeans
  calc
    _ = ∑ z ∈ L.support, L.mass z *
        (armTotal S y z true / m - armTotal S y z false / (S.card - m)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hc z hz, hf z hz]
    _ = _ := by simp_rw [mul_sub]; rw [Finset.sum_sub_distrib, exchange, exchange]

/-- T2 steps (2)--(3): the unnormalized arm moment equals arm probability
times the corrected conditional mean (p. 131, corrected). -/
theorem moment_identity {N : ℕ} (L : FiniteLaw (Assignment N)) (y : Outcomes N)
    (i : Fin N) (a : Bool) (h : armMass L i a ≠ 0) :
    weightedNumerator L y i a = armMass L i a * weightedMean L y i a := by
  unfold weightedMean
  field_simp

/-- T2, the probability-weighted correction to the unbiasedness display on
p. 131: arbitrary interference, fixed 0<m<n local treated count, common m/n
propensities, and no restriction on outside assignments. -/
theorem weighted_unbiasedness {N : ℕ} (L : FiniteLaw (Assignment N))
    (S : Finset (Fin N)) (y : Outcomes N) (m : ℕ)
    (hm : 0 < m) (hmn : m < S.card)
    (hc : ∀ z ∈ L.support, armCount S z true = m)
    (hp : ∀ i ∈ S, armMass L i true = (m : ℝ) / S.card) :
    L.expect (differenceInMeans S y) = windowContrast S (weightedMean L y) ∧
    windowContrast S (weightedMean L y) =
      ((∑ i ∈ S, weightedMean L y i true) - ∑ i ∈ S, weightedMean L y i false) /
        S.card := by
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans hm hmn))
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hnm : (S.card : ℝ) - m ≠ 0 := by
    have : (m : ℝ) < S.card := by exact_mod_cast hmn
    linarith
  have hp0 : ∀ i ∈ S, armMass L i false = ((S.card : ℝ) - m) / S.card := by
    intro i hi
    have h := armMasses_add L i
    rw [hp i hi] at h
    field_simp at *
    nlinarith
  constructor
  · rw [expectation_fixed_counts L S y m hc]
    unfold windowContrast
    rw [Finset.sum_sub_distrib, sub_div]
    congr 1
    · rw [Finset.sum_div, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      unfold weightedMean
      rw [hp i hi]
      field_simp
    · rw [Finset.sum_div, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      unfold weightedMean
      rw [hp0 i hi]
      field_simp
  · simp [windowContrast, Finset.sum_sub_distrib]

/-- T3's added (U): the conditional full assignment law is uniform over its
own-arm support, an additional condition absent from pp. 130--131. -/
def ConditionalUniform {N : ℕ} (L : FiniteLaw (Assignment N))
    (S : Finset (Fin N)) : Prop :=
  ∀ i ∈ S, ∀ a, ∀ z ∈ armSupport L i a,
    L.mass z / armMass L i a = 1 / ((armSupport L i a).card : ℝ)

/-- T3(a): conditional uniformity identifies the printed average with the
probability-weighted conditional mean, for every potential-outcome schedule. -/
theorem means_equal_of_conditional_uniform {N : ℕ} (L : FiniteLaw (Assignment N))
    (S : Finset (Fin N)) (hU : ConditionalUniform L S) (y : Outcomes N)
    (i : Fin N) (hi : i ∈ S) (a : Bool) :
    printedMean L y i a = weightedMean L y i a := by
  unfold printedMean weightedMean weightedNumerator
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z hz
  have := hU i hi a z hz
  calc
    y i z / ((armSupport L i a).card : ℝ) =
      (1 / ((armSupport L i a).card : ℝ)) * y i z := by ring
    _ = (L.mass z / armMass L i a) * y i z := by rw [this]
    _ = _ := by ring

/-- T3(a), the alternative corrected unbiasedness result (p. 131) retaining
the printed target under added conditional uniformity. -/
theorem printed_unbiasedness_under_U {N : ℕ} (L : FiniteLaw (Assignment N))
    (S : Finset (Fin N)) (y : Outcomes N) (m : ℕ)
    (hm : 0 < m) (hmn : m < S.card)
    (hc : ∀ z ∈ L.support, armCount S z true = m)
    (hp : ∀ i ∈ S, armMass L i true = (m : ℝ) / S.card)
    (hU : ConditionalUniform L S) :
    L.expect (differenceInMeans S y) = windowContrast S (printedMean L y) := by
  rw [(weighted_unbiasedness L S y m hm hmn hc hp).1]
  unfold windowContrast
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [means_equal_of_conditional_uniform L S hU y i hi true,
    means_equal_of_conditional_uniform L S hU y i hi false]

/-- "Pr(X_i=X_j)=0" for distinct window subjects, corrected P014-T7 (p. 130). -/
def DistinctNoTies {Ω : Type*} {N : ℕ} (L : FiniteLaw Ω)
    (X : Ω → Fin N → ℝ) (S : Finset (Fin N)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → L.prob (fun ω => X ω i = X ω j) = 0

/-- The literal printed quantifier includes the diagonal (p. 130); it is kept
separate from the distinct-subject reading used for the substantive results. -/
def PrintedNoTies {Ω : Type*} {N : ℕ} (L : FiniteLaw Ω)
    (X : Ω → Fin N → ℝ) (S : Finset (Fin N)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, L.prob (fun ω => X ω i = X ω j) = 0

/-- T7(a)--(b): the literal no-ties condition holds exactly when the window
set is empty, because every diagonal event has probability one (p. 130). -/
theorem printed_no_ties_iff_empty {Ω : Type*} {N : ℕ} (L : FiniteLaw Ω)
    (X : Ω → Fin N → ℝ) (S : Finset (Fin N)) : PrintedNoTies L X S ↔ S = ∅ := by
  classical
  constructor
  · intro h
    by_contra hs
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hz := h i hi i hi
    simp only [FiniteLaw.prob, if_true] at hz
    rw [L.total] at hz
    norm_num at hz
  · rintro rfl
    simp [PrintedNoTies]

/-- The formal local-randomization clauses on p. 130, with no ties read for
distinct subjects. Fixed membership is expressed at every positive support
point (equivalently its probability is 0 or 1). The mass clause is for the
FULL X vector, as printed, and the empirical CDF is constant for all t. -/
def PrintedLocal {Ω : Type*} {N : ℕ} (L : FiniteLaw Ω) (X : Ω → Fin N → ℝ)
    (b : ℝ) (S : Finset (Fin N)) : Prop :=
  (∀ ω ∈ L.support, windowSet b (X ω) = S) ∧
  (∃ F₀ : ℝ → ℝ, ∀ ω ∈ L.support, ∀ t, empiricalCDF S (X ω) t = F₀ t) ∧
  (∀ ω ∈ L.support, L.prob (fun η => X η = X ω) = 1 / (S.card.factorial : ℝ)) ∧
  DistinctNoTies L X S ∧
  (∀ ω ∈ L.support, 0 < armCount S (threshold (X ω)) true ∧
    armCount S (threshold (X ω)) true < S.card)




/-- Uniform six-atom randomization for the counterexamples to T1,
T5, T9: every running-vector row has probability 1/6. -/
def sixLaw : FiniteLaw (Fin 6) :=
  ⟨Finset.univ, fun _ => 1/6, by intro a ha; norm_num,
    by norm_num [Fin.sum_univ_succ]⟩

/-- The fixed window S={1,2,3} (zero-based {0,1,2}) in the counterexamples. -/
def threeWindow : Finset (Fin 4) := {0, 1, 2}

/-- Finite expansion for S={1,2,3}, shared by the exact
counterexamples to the displays on pp. 130--131. -/
theorem sum_three_window (f : Fin 4 → ℝ) :
    (∑ i ∈ threeWindow, f i) = f 0 + f 1 + f 2 := by
  norm_num [threeWindow]
  ring

/-- T1's complete six-row running-variable schedule (P014-E001), N=4, b=2. -/
def witnessX : Fin 6 → Fin 4 → ℝ :=
  ![![-2,-1,1,3], ![-2,1,-1,-3], ![-1,-2,1,-3],
    ![-1,1,-2,-3], ![1,-2,-1,-3], ![1,-1,-2,-3]]

/-- The thresholded treatment vectors of T1, and of T9's rescaled scores. -/
def witnessZ : Fin 6 → Assignment 4 :=
  ![![false,false,true,true], ![false,true,false,false], ![false,false,true,false],
    ![false,true,false,false], ![true,false,false,false], ![true,false,false,false]]

/-- T1 outcomes on ALL 16 treatment vectors: y_1=y_2=y_3=z_4, y_4=0
(P014-E001), independent of scores conditional on full assignment. -/
def spilloverAll : Outcomes 4 := fun i z => if i = 3 then 0 else bit (z 3)

/-- T9's outcomes on all assignments: y_1=z_4, y_2=y_3=y_4=0
(P014-N002). -/
def spilloverOne : Outcomes 4 := fun i z => if i = 0 then bit (z 3) else 0

/-- T5's complete running-variable schedule (P014-E002), N=4,b=2;
four different outside scores lie above one repeated in-window arrangement. -/
def defectiveX : Fin 6 → Fin 4 → ℝ :=
  ![![1,-1,-2,3], ![-1,1,-2,3], ![-1,-2,1,3],
    ![-1,-2,1,4], ![-1,-2,1,5], ![-1,-2,1,6]]

/-- T5 outcomes on all assignments: y_1=z_1 and all other outcomes zero
(P014-E002); no interference. -/
def noInterferenceOne : Outcomes 4 := fun i z => if i = 0 then bit (z 0) else 0

/-- T9 running scores, N=4,b=1, the six vectors of P014-N002. -/
def comparisonX : Fin 6 → Fin 4 → ℝ :=
  ![![-1,-(1/2),1/2,2], ![-1,1/2,-(1/2),-2], ![-(1/2),-1,1/2,-2],
    ![-(1/2),1/2,-1,-2], ![1/2,-1,-(1/2),-2], ![1/2,-(1/2),-1,-2]]

/-- The full assignment distribution shared by T1 and T9: pushforward of
the six equally probable score rows; its four support points have unequal masses. -/
def witnessLaw : FiniteLaw (Assignment 4) := sixLaw.map witnessZ

/-- T1 and T9's displayed binary vectors agree with the threshold rule (p.130). -/
theorem witness_threshold : (fun ω => threshold (witnessX ω)) = witnessZ ∧
    (fun ω => threshold (comparisonX ω)) = witnessZ := by
  constructor <;> funext ω i <;> fin_cases ω <;> fin_cases i <;>
    norm_num [threshold, witnessX, comparisonX, witnessZ]

/-- T1 and T9: all six local score arrangements occur exactly once, each
with probability 1/6, not merely the full-vector mass condition (p. 130 prose). -/
theorem witness_local_arrangements :
    Function.Injective (fun ω : Fin 6 => fun i : Fin 3 => witnessX ω (Fin.castSucc i)) ∧
    (∀ ω : Fin 6, sixLaw.prob (fun η =>
      (fun i : Fin 3 => witnessX η (Fin.castSucc i)) =
      (fun i : Fin 3 => witnessX ω (Fin.castSucc i))) = 1/6) := by
  constructor
  · intro a b h
    fin_cases a <;> fin_cases b <;>
      norm_num [witnessX, funext_iff, Fin.forall_fin_succ] at h <;> rfl
  · intro ω
    fin_cases ω <;> norm_num [FiniteLaw.prob, sixLaw, Fin.sum_univ_succ,
      witnessX, funext_iff, Fin.forall_fin_succ]

/-- T1: every printed local-randomization clause holds, with the no-ties
quantifier interpreted for distinct subjects (p. 130; P014-E001). -/
theorem witness_printed_local : PrintedLocal sixLaw witnessX 2 threeWindow := by
  classical
  refine ⟨?_, ⟨fun t => ((if (-2 : ℝ) ≤ t then 1 else 0) +
    (if (-1 : ℝ) ≤ t then 1 else 0) + (if (1 : ℝ) ≤ t then 1 else 0)) / 3, ?_⟩,
    ?_, ?_, ?_⟩
  · intro ω hω
    ext i
    fin_cases ω <;> fin_cases i <;> norm_num [windowSet, inWindow, witnessX, threeWindow]
  · intro ω hω t
    simp only [empiricalCDF, sum_three_window]
    fin_cases ω <;> norm_num [witnessX, threeWindow] <;> ring
  · intro ω hω
    fin_cases ω <;> norm_num [FiniteLaw.prob, sixLaw, Fin.sum_univ_succ,
      witnessX, funext_iff, Fin.forall_fin_succ, threeWindow]
  · intro i hi j hj hij
    simp only [threeWindow, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      first | exact (hij rfl).elim
            | norm_num [FiniteLaw.prob, sixLaw, Fin.sum_univ_succ, witnessX]
  · intro ω hω
    fin_cases ω <;> norm_num [armCount, threshold, witnessX, threeWindow, Finset.filter_insert, Finset.filter_singleton]

/-- T9: the rescaled six-row running law also satisfies every printed clause
(p. 130; P014-N002). -/
theorem comparison_printed_local : PrintedLocal sixLaw comparisonX 1 threeWindow := by
  classical
  refine ⟨?_, ⟨fun t => ((if (-1 : ℝ) ≤ t then 1 else 0) +
    (if (-(1/2) : ℝ) ≤ t then 1 else 0) + (if (1/2 : ℝ) ≤ t then 1 else 0)) / 3, ?_⟩,
    ?_, ?_, ?_⟩
  · intro ω hω
    ext i
    fin_cases ω <;> fin_cases i <;> norm_num [windowSet, inWindow, comparisonX, threeWindow]
  · intro ω hω t
    simp only [empiricalCDF, sum_three_window]
    fin_cases ω <;> norm_num [comparisonX, threeWindow] <;> ring
  · intro ω hω
    fin_cases ω <;> norm_num [FiniteLaw.prob, sixLaw, Fin.sum_univ_succ,
      comparisonX, funext_iff, Fin.forall_fin_succ, threeWindow]
  · intro i hi j hj hij
    simp only [threeWindow, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      first | exact (hij rfl).elim
            | norm_num [FiniteLaw.prob, sixLaw, Fin.sum_univ_succ, comparisonX]
  · intro ω hω
    fin_cases ω <;> norm_num [armCount, threshold, comparisonX, threeWindow, Finset.filter_insert, Finset.filter_singleton]

/-- T1/T9: the treatment support has FOUR distinct vectors, not six copies;
this is the set interpretation of Supp(Z) in the first display of p. 131. -/
theorem witness_support : witnessLaw.support =
    {![false,false,true,true], ![false,true,false,false],
      ![false,false,true,false], ![true,false,false,false]} := by
  classical
  ext z
  simp [witnessLaw, FiniteLaw.map, sixLaw, witnessZ, Fin.exists_fin_succ]
  tauto

/-- T1/T9: the actual four treatment masses are 1/6,1/3,1/6,1/3
(P014-E001 and P014-N002). -/
theorem witness_masses :
    witnessLaw.mass ![false,false,true,true] = 1/6 ∧
    witnessLaw.mass ![false,true,false,false] = 1/3 ∧
    witnessLaw.mass ![false,false,true,false] = 1/6 ∧
    witnessLaw.mass ![true,false,false,false] = 1/3 := by
  norm_num [witnessLaw, FiniteLaw.map, FiniteLaw.prob, sixLaw, witnessZ,
    Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]

/-- T1: common 1/3 propensities and fixed one treated window subject,
including arbitrary dependence of the outside treatment on local ranks. -/
theorem witness_counts_propensities :
    (∀ z ∈ witnessLaw.support, armCount threeWindow z true = 1) ∧
    (∀ i ∈ threeWindow, armMass witnessLaw i true = 1/3) := by
  classical
  constructor
  · intro z hz
    rw [witness_support] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;>
      simp only [armCount, sum_three_window] <;> norm_num
  · intro i hi
    simp only [threeWindow, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;>
      norm_num [armMass, armSupport, witness_support, witness_masses,
        Finset.filter_insert, Finset.filter_singleton, funext_iff, Fin.forall_fin_succ]

/-- T1: the printed conditional means, weighted means, estimator expectation
and targets, computed from the actual support and probabilities (P014-E001). -/
theorem t1_arithmetic :
    printedMean witnessLaw spilloverAll 0 true = 0 ∧
    printedMean witnessLaw spilloverAll 0 false = 1/3 ∧
    printedMean witnessLaw spilloverAll 1 true = 0 ∧
    printedMean witnessLaw spilloverAll 1 false = 1/3 ∧
    printedMean witnessLaw spilloverAll 2 true = 1/2 ∧
    printedMean witnessLaw spilloverAll 2 false = 0 ∧
    weightedMean witnessLaw spilloverAll 0 false = 1/4 ∧
    weightedMean witnessLaw spilloverAll 1 false = 1/4 ∧
    weightedMean witnessLaw spilloverAll 2 true = 1/2 ∧
    (∀ ω : Fin 6, differenceInMeans threeWindow spilloverAll (witnessZ ω) = 0) ∧
    witnessLaw.expect (differenceInMeans threeWindow spilloverAll) = 0 ∧
    windowContrast threeWindow (printedMean witnessLaw spilloverAll) = -1/18 ∧
    windowContrast threeWindow (weightedMean witnessLaw spilloverAll) = 0 := by
  classical
  have he : witnessLaw.expect (differenceInMeans threeWindow spilloverAll) = 0 := by
    rw [witnessLaw, expect_map]
    simp only [FiniteLaw.expect, Function.comp_def, differenceInMeans, armCount, armTotal,
      sum_three_window]
    norm_num [FiniteLaw.expect, sixLaw, Fin.sum_univ_succ, Function.comp_def,
      differenceInMeans, armCount, armTotal, threeWindow, witnessZ, spilloverAll, bit]
  have hz : ∀ ω : Fin 6, differenceInMeans threeWindow spilloverAll (witnessZ ω) = 0 := by
    intro ω
    simp only [differenceInMeans, armCount, armTotal, sum_three_window]
    fin_cases ω <;> norm_num [witnessZ, spilloverAll, bit]
  simp only [he, hz, forall_const, true_and, and_true]
  norm_num [printedMean, weightedMean, weightedNumerator, armMass, armSupport,
    witness_support, windowContrast, threeWindow, spilloverAll, bit,
    witness_masses, Finset.filter_insert, Finset.filter_singleton,
    Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]

/-- T1, complete counterexample to the printed unbiasedness display (p. 131).
Every formal local clause holds, all SIX local arrangements are equiprobable,
E[τhat]=0, the printed τ=-1/18, and their nonzero gap is 1/18. -/
theorem t1_counterexample :
    PrintedLocal sixLaw witnessX 2 threeWindow ∧
    Function.Injective (fun ω : Fin 6 => fun i : Fin 3 => witnessX ω (Fin.castSucc i)) ∧
    (∀ ω : Fin 6, sixLaw.prob (fun η =>
      (fun i : Fin 3 => witnessX η (Fin.castSucc i)) =
      (fun i : Fin 3 => witnessX ω (Fin.castSucc i))) = 1/6) ∧
    (sixLaw.map (fun ω => threshold (witnessX ω))).expect
      (differenceInMeans threeWindow spilloverAll) = 0 ∧
    windowContrast threeWindow
      (printedMean (sixLaw.map (fun ω => threshold (witnessX ω))) spilloverAll) = -1/18 ∧
    (sixLaw.map (fun ω => threshold (witnessX ω))).expect
      (differenceInMeans threeWindow spilloverAll) ≠
      windowContrast threeWindow
        (printedMean (sixLaw.map (fun ω => threshold (witnessX ω))) spilloverAll) := by
  rw [witness_threshold.1]
  change PrintedLocal sixLaw witnessX 2 threeWindow ∧ _ ∧ _ ∧
    witnessLaw.expect _ = 0 ∧ windowContrast threeWindow (printedMean witnessLaw _) = -1/18 ∧ _
  obtain ⟨_, _, _, _, _, _, _, _, _, _, he, ht, _⟩ := t1_arithmetic
  exact ⟨witness_printed_local, witness_local_arrangements.1, witness_local_arrangements.2,
    he, ht, by
      change witnessLaw.expect _ ≠ windowContrast threeWindow (printedMean witnessLaw _)
      rw [he, ht]; norm_num⟩

/-- T5: the defective local law satisfies every FORMAL printed clause
(p. 130; P014-E002), despite nonuniform local arrangement probabilities. -/
theorem defective_printed_local : PrintedLocal sixLaw defectiveX 2 threeWindow := by
  classical
  refine ⟨?_, ⟨fun t => ((if (-2 : ℝ) ≤ t then 1 else 0) +
    (if (-1 : ℝ) ≤ t then 1 else 0) + (if (1 : ℝ) ≤ t then 1 else 0)) / 3, ?_⟩,
    ?_, ?_, ?_⟩
  · intro ω hω
    ext i
    fin_cases ω <;> fin_cases i <;> norm_num [windowSet, inWindow, defectiveX, threeWindow]
  · intro ω hω t
    simp only [empiricalCDF, sum_three_window]
    fin_cases ω <;> norm_num [defectiveX, threeWindow] <;> ring
  · intro ω hω
    fin_cases ω <;> norm_num [FiniteLaw.prob, sixLaw, Fin.sum_univ_succ,
      defectiveX, funext_iff, Fin.forall_fin_succ, threeWindow]
  · intro i hi j hj hij
    simp only [threeWindow, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      first | exact (hij rfl).elim
            | norm_num [FiniteLaw.prob, sixLaw, Fin.sum_univ_succ, defectiveX]
  · intro ω hω
    fin_cases ω <;> norm_num [armCount, threshold, defectiveX, threeWindow, Finset.filter_insert, Finset.filter_singleton]

/-- T5: a concrete arrangement has probability 2/3 instead of 1/6, subject
propensities are 1/6,1/6,2/3, and E[τhat]=1/6 while printed τ=1/3.
This refutes the implication to equiprobable local arrangements (p. 130). -/
theorem t5_counterexample :
    PrintedLocal sixLaw defectiveX 2 threeWindow ∧
    sixLaw.prob (fun ω => (fun i : Fin 3 => defectiveX ω (Fin.castSucc i)) = ![-1,-2,1]) = 2/3 ∧
    sixLaw.prob (fun ω => (fun i : Fin 3 => defectiveX ω (Fin.castSucc i)) = ![-1,-2,1]) ≠ 1/6 ∧
    sixLaw.prob (fun ω => threshold (defectiveX ω) 0 = true) = 1/6 ∧
    sixLaw.prob (fun ω => threshold (defectiveX ω) 1 = true) = 1/6 ∧
    sixLaw.prob (fun ω => threshold (defectiveX ω) 2 = true) = 2/3 ∧
    (sixLaw.map (fun ω => threshold (defectiveX ω))).expect
      (differenceInMeans threeWindow noInterferenceOne) = 1/6 ∧
    windowContrast threeWindow
      (printedMean (sixLaw.map (fun ω => threshold (defectiveX ω))) noInterferenceOne) = 1/3 := by
  classical
  have hs : (sixLaw.map (fun ω => threshold (defectiveX ω))).support =
      {![true,false,false,true], ![false,true,false,true], ![false,false,true,true]} := by
    ext z
    norm_num [FiniteLaw.map, sixLaw, defectiveX, threshold, Fin.exists_fin_succ,
      funext_iff, Fin.forall_fin_succ]
  have ht : windowContrast threeWindow
      (printedMean (sixLaw.map (fun ω => threshold (defectiveX ω))) noInterferenceOne) = 1/3 := by
    simp only [windowContrast, printedMean, armSupport, hs]
    norm_num [threeWindow, noInterferenceOne, bit, Finset.filter_insert,
      Finset.filter_singleton, funext_iff, Fin.forall_fin_succ]
  refine ⟨defective_printed_local, ?_⟩
  rw [ht, expect_map]
  simp only [FiniteLaw.expect, Function.comp_def, differenceInMeans, armCount, armTotal,
    sum_three_window]
  norm_num [FiniteLaw.prob, sixLaw, Fin.sum_univ_succ, defectiveX, threshold,
    funext_iff, Fin.forall_fin_succ, FiniteLaw.expect, Function.comp_def,
    differenceInMeans, armCount, armTotal, threeWindow, noInterferenceOne, bit,
    Finset.filter_insert, Finset.filter_singleton]

/-- T9, concrete counterexample to equivalence with the cited direct effect
(p. 129 and p. 131; P014-N002). All printed clauses hold. The printed contrast
is -1/9, the weighted contrast -1/12, and the control-minus-treatment direct
effect is 1/12; the printed contrast equals neither sign of that effect. -/
theorem t9_counterexample :
    PrintedLocal sixLaw comparisonX 1 threeWindow ∧
    printedMean witnessLaw spilloverOne 0 false = 1/3 ∧
    weightedMean witnessLaw spilloverOne 0 false = 1/4 ∧
    windowContrast threeWindow (printedMean witnessLaw spilloverOne) = -1/9 ∧
    windowContrast threeWindow (weightedMean witnessLaw spilloverOne) = -1/12 ∧
    windowContrast threeWindow (printedMean witnessLaw spilloverOne) ≠
      -windowContrast threeWindow (weightedMean witnessLaw spilloverOne) ∧
    windowContrast threeWindow (printedMean witnessLaw spilloverOne) ≠
      windowContrast threeWindow (weightedMean witnessLaw spilloverOne) ∧
    (sixLaw.map (fun ω => threshold (comparisonX ω))).expect
      (differenceInMeans threeWindow spilloverOne) = -1/12 := by
  classical
  refine ⟨comparison_printed_local, ?_⟩
  rw [witness_threshold.2, expect_map]
  simp only [FiniteLaw.expect, Function.comp_def, differenceInMeans, armCount, armTotal,
    sum_three_window]
  norm_num [printedMean, weightedMean, weightedNumerator, armMass, armSupport,
    witness_support, windowContrast, threeWindow, spilloverOne, bit,
    witness_masses, Finset.filter_insert, Finset.filter_singleton,
    Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ, FiniteLaw.expect, sixLaw, witnessZ,
    Function.comp_def, differenceInMeans, armCount, armTotal, Finset.filter_insert, Finset.filter_singleton]

/-- T3(b): uniformity of the FULL assignment distribution implies conditional
uniformity on every nonempty own-arm support (alternative repair, p. 131). -/
theorem conditional_uniform_of_full_uniform {N : ℕ} (L : FiniteLaw (Assignment N))
    (S : Finset (Fin N))
    (hfull : ∀ z ∈ L.support, L.mass z = 1 / (L.support.card : ℝ)) :
    ConditionalUniform L S := by
  classical
  intro i hi a z hz
  have hzL := (Finset.mem_filter.mp hz).1
  have hk : ((armSupport L i a).card : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Finset.card_pos.mpr ⟨z, hz⟩)
  have hn : (L.support.card : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Finset.card_pos.mpr ⟨z, hzL⟩)
  have hm : armMass L i a = (armSupport L i a).card / (L.support.card : ℝ) := by
    unfold armMass
    calc
      _ = ∑ x ∈ armSupport L i a, (1 / (L.support.card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hfull x (Finset.mem_filter.mp hx).1
      _ = _ := by simp <;> ring
  rw [hfull z hzL, hm]
  field_simp

/-- Positive own-arm probability ensures a nonempty own-arm support, so the
printed average also has a nonzero denominator (T2/T3 corrections, p. 131). -/
theorem arm_nonempty_of_mass_ne_zero {N : ℕ} (L : FiniteLaw (Assignment N))
    (i : Fin N) (a : Bool) (hm : armMass L i a ≠ 0) : (armSupport L i a).Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  simp [armMass, he] at hm

/-- T3(d), finite identity: on an arm with constant potential outcome, weighted
and unweighted averages both equal that value, regardless of assignment weights. -/
theorem constant_arm_means {N : ℕ} (L : FiniteLaw (Assignment N)) (y : Outcomes N)
    (i : Fin N) (a : Bool) (c : ℝ) (hm : armMass L i a ≠ 0)
    (hy : ∀ z ∈ armSupport L i a, y i z = c) :
    printedMean L y i a = c ∧ weightedMean L y i a = c := by
  have hk : ((armSupport L i a).card : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Finset.card_pos.mpr (arm_nonempty_of_mass_ne_zero L i a hm))
  have hu : (∑ z ∈ armSupport L i a, y i z) = (armSupport L i a).card * c := by
    calc
      _ = ∑ z ∈ armSupport L i a, c := Finset.sum_congr rfl hy
      _ = _ := by simp
  have hw : weightedNumerator L y i a = armMass L i a * c := by
    unfold weightedNumerator armMass
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hy z hz]
  constructor
  · unfold printedMean
    rw [hu]
    field_simp
  · unfold weightedMean
    rw [hw]
    field_simp

/-- "absence of interference" (p. 130): for window subject i, y_i depends
only on that subject's treatment, with values defined on all assignment vectors. -/
def NoInterference {N : ℕ} (S : Finset (Fin N)) (y : Outcomes N) : Prop :=
  ∀ i ∈ S, ∀ z z', z i = z' i → y i z = y i z'

/-- T3(d): without interference, on any positive arm the printed support
mean and probability-weighted conditional mean agree without (U). -/
theorem means_equal_without_interference {N : ℕ} (L : FiniteLaw (Assignment N))
    (S : Finset (Fin N)) (y : Outcomes N) (hno : NoInterference S y)
    (i : Fin N) (hi : i ∈ S) (a : Bool) (hm : armMass L i a ≠ 0) :
    printedMean L y i a = weightedMean L y i a := by
  obtain ⟨z₀, hz₀⟩ := arm_nonempty_of_mass_ne_zero L i a hm
  have hconst : ∀ z ∈ armSupport L i a, y i z = y i z₀ := by
    intro z hz
    apply hno i hi z z₀
    exact (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz₀).2.symm
  obtain ⟨hu, hw⟩ := constant_arm_means L y i a (y i z₀) hm hconst
  exact hu.trans hw.symm

/-- T3(d): the printed unbiasedness identity does hold without interference
under fixed counts and common propensities alone (alternative repair, p. 131). -/
theorem printed_unbiasedness_no_interference {N : ℕ} (L : FiniteLaw (Assignment N))
    (S : Finset (Fin N)) (y : Outcomes N) (m : ℕ)
    (hm : 0 < m) (hmn : m < S.card)
    (hc : ∀ z ∈ L.support, armCount S z true = m)
    (hp : ∀ i ∈ S, armMass L i true = (m : ℝ) / S.card)
    (hno : NoInterference S y) :
    L.expect (differenceInMeans S y) = windowContrast S (printedMean L y) := by
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_trans hm hmn)
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hp1 : ∀ i ∈ S, armMass L i true ≠ 0 := by
    intro i hi; rw [hp i hi]; exact div_ne_zero hm' hn
  have hp0 : ∀ i ∈ S, armMass L i false ≠ 0 := by
    intro i hi
    have he := armMasses_add L i
    rw [hp i hi] at he
    have hl : (m : ℝ) < S.card := by exact_mod_cast hmn
    intro hz
    rw [hz] at he
    have : (m : ℝ) = S.card := (div_eq_one_iff_eq hn).mp (by linarith)
    linarith
  rw [(weighted_unbiasedness L S y m hm hmn hc hp).1]
  unfold windowContrast
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [means_equal_without_interference L S y hno i hi true (hp1 i hi),
    means_equal_without_interference L S y hno i hi false (hp0 i hi)]

/-- T3(e): agreement of printed and weighted means for EVERY outcome function
forces uniformity of the conditional assignment law, proved by a point indicator. -/
theorem conditional_uniform_necessary {N : ℕ} (L : FiniteLaw (Assignment N))
    (i : Fin N) (a : Bool)
    (hall : ∀ y : Outcomes N, printedMean L y i a = weightedMean L y i a) :
    ∀ z ∈ armSupport L i a,
      L.mass z / armMass L i a = 1 / ((armSupport L i a).card : ℝ) := by
  classical
  intro z hz
  have h := hall (fun _ z' => if z' = z then 1 else 0)
  simpa [printedMean, weightedMean, weightedNumerator, hz, mul_ite] using h.symm

/-- Hudgens--Halloran's Z_{-i} in single-population notation:
assignments of other subjects (P014-N002). -/
abbrev OtherAssignment {N : ℕ} (i : Fin N) := {j : Fin N // j ≠ i} → Bool

/-- Remove subject i's assignment, the vector Z_{-i} in T9/T10. -/
def others {N : ℕ} (i : Fin N) (z : Assignment N) : OtherAssignment i := fun j => z j

/-- y_i(s,u): insert own assignment s among assignments u of the other N-1
subjects (T10, P014-N002). -/
def withOwn {N : ℕ} (i : Fin N) (a : Bool) (u : OtherAssignment i) : Assignment N :=
  (Equiv.funSplitAt i Bool).symm (a, u)

/-- T10's finite reconstruction identity: reinserting the observed own arm
and the assignments of others gives the entire original assignment vector. -/
theorem withOwn_others {N : ℕ} (i : Fin N) (a : Bool) (z : Assignment N)
    (h : z i = a) : withOwn i a (others i z) = z := by
  unfold withOwn others
  have hs : (a, fun j : {j : Fin N // j ≠ i} => z j) = (Equiv.funSplitAt i Bool) z := by
    simp [Equiv.funSplitAt, Equiv.piSplitAt, h]
  rw [hs]
  exact (Equiv.funSplitAt i Bool).symm_apply_apply z

/-- Pr(Z_{-i}=u | Z_i=a), the conditional weights in Hudgens--Halloran's
individual average potential outcome (T10; P014-N002). -/
def conditionalOtherMass {N : ℕ} (L : FiniteLaw (Assignment N)) (i : Fin N)
    (a : Bool) (u : OtherAssignment i) : ℝ :=
  L.prob (fun z => z i = a ∧ others i z = u) / armMass L i a

/-- m_i(s;p)=Σ_u y_i(s,u) Pr(Z_{-i}=u | Z_i=s), the cited individual
average potential outcome in T10 (P014-N002). -/
def hhMean {N : ℕ} (L : FiniteLaw (Assignment N)) (y : Outcomes N)
    (i : Fin N) (a : Bool) : ℝ :=
  ∑ u : OtherAssignment i, y i (withOwn i a u) * conditionalOtherMass L i a u

/-- d_i(p)=m_i(0;p)-m_i(1;p), Hudgens--Halloran's CONTROL MINUS TREATMENT
convention in T9/T10 (their equation (3)). -/
def hhDirect {N : ℕ} (L : FiniteLaw (Assignment N)) (y : Outcomes N) (i : Fin N) : ℝ :=
  hhMean L y i false - hhMean L y i true

/-- T10(a): the other-subjects conditional sum equals the corrected full-vector
probability-weighted average. Positive probability makes conditioning meaningful. -/
theorem hhMean_eq_weighted {N : ℕ} (L : FiniteLaw (Assignment N)) (y : Outcomes N)
    (i : Fin N) (a : Bool) (_hp : 0 < armMass L i a) :
    hhMean L y i a = weightedMean L y i a := by
  classical
  unfold hhMean conditionalOtherMass FiniteLaw.prob weightedMean weightedNumerator armSupport
  simp_rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div, mul_ite, mul_zero, ite_div, zero_div]
  rw [Finset.sum_comm]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : z i = a
  · simp [h, withOwn_others i a z h, mul_comm]
  · simp [h]

/-- T10(b): the probability-weighted treated-minus-control target is the
NEGATIVE of the window average of the cited individual direct effects (pp.129,131). -/
theorem corrected_target_hh_sign {N : ℕ} (L : FiniteLaw (Assignment N))
    (S : Finset (Fin N)) (y : Outcomes N) (_hS : S.Nonempty)
    (hp : ∀ i ∈ S, 0 < armMass L i true ∧ armMass L i true < 1) :
    windowContrast S (weightedMean L y) = -(∑ i ∈ S, hhDirect L y i) / S.card := by
  have hp0 : ∀ i ∈ S, 0 < armMass L i false := by
    intro i hi; have he := armMasses_add L i; linarith [(hp i hi).2]
  unfold windowContrast hhDirect
  rw [← Finset.sum_neg_distrib, Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hhMean_eq_weighted L y i true (hp i hi).1, hhMean_eq_weighted L y i false (hp0 i hi)]
  ring

/-- T10(c): under T2's hypotheses the unchanged estimator has expectation
minus the cited direct-effect average, using Hudgens--Halloran's sign convention. -/
theorem estimator_hh_sign {N : ℕ} (L : FiniteLaw (Assignment N))
    (S : Finset (Fin N)) (y : Outcomes N) (m : ℕ)
    (hm : 0 < m) (hmn : m < S.card)
    (hc : ∀ z ∈ L.support, armCount S z true = m)
    (hp : ∀ i ∈ S, armMass L i true = (m : ℝ) / S.card) :
    L.expect (differenceInMeans S y) = -(∑ i ∈ S, hhDirect L y i) / S.card := by
  have hnr : (0 : ℝ) < S.card := by exact_mod_cast lt_trans hm hmn
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnr : (m : ℝ) < S.card := by exact_mod_cast hmn
  rw [(weighted_unbiasedness L S y m hm hmn hc hp).1]
  apply corrected_target_hh_sign L S y (Finset.card_pos.mp (lt_trans hm hmn))
  intro i hi
  rw [hp i hi]
  exact ⟨div_pos hmr hnr, (div_lt_one hnr).mpr hmnr⟩

/-- T9's explicit comparison with the cited definition, using the
other-subject conditional sum: D=1/12, neither sign equals
the printed target, and the estimator's bias for the printed target is 1/36
(P014-N002). -/
theorem t9_hudgens_halloran_comparison :
    (∑ i ∈ threeWindow, hhDirect witnessLaw spilloverOne i) / threeWindow.card = 1/12 ∧
    windowContrast threeWindow (printedMean witnessLaw spilloverOne) ≠
      (∑ i ∈ threeWindow, hhDirect witnessLaw spilloverOne i) / threeWindow.card ∧
    windowContrast threeWindow (printedMean witnessLaw spilloverOne) ≠
      -(∑ i ∈ threeWindow, hhDirect witnessLaw spilloverOne i) / threeWindow.card ∧
    (sixLaw.map (fun ω => threshold (comparisonX ω))).expect
      (differenceInMeans threeWindow spilloverOne) -
      windowContrast threeWindow (printedMean witnessLaw spilloverOne) = 1/36 := by
  obtain ⟨hf, hu, hw, hTA, hTM, hn1, hn2, hE⟩ := t9_counterexample
  have hp : ∀ i ∈ threeWindow,
      0 < armMass witnessLaw i true ∧ armMass witnessLaw i true < 1 := by
    intro i hi
    rw [witness_counts_propensities.2 i hi]
    norm_num
  have hs := corrected_target_hh_sign witnessLaw threeWindow spilloverOne
    (by simp [threeWindow]) hp
  rw [hTM] at hs
  have hD : (∑ i ∈ threeWindow, hhDirect witnessLaw spilloverOne i) /
      threeWindow.card = 1/12 := by
    apply neg_injective
    calc
      _ = -(∑ i ∈ threeWindow, hhDirect witnessLaw spilloverOne i) / threeWindow.card := by ring
      _ = -1/12 := hs.symm
      _ = -(1/12 : ℝ) := by ring
  refine ⟨hD, ?_, ?_, ?_⟩
  · rw [hTA, hD]
    norm_num
  · rw [hTA, ← hs]
    norm_num
  · rw [hE, hTA]
    norm_num

/-- Probability for general real running-variable laws (T6), including
continuous outside scores: ordinary probability μ(event), as a real number. -/
def eventProb {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (P : Ω → Prop) : ℝ := (μ {ω | P ω}).toReal

/-- Probability clauses for corrected local randomization (P014-T6, p. 130):
measurability of the running scores, fixed window-membership probabilities, and
mass 1/|S|! for each permutation event generated by the fixed score map `v`.
In `corrected_local_randomization`, the probability-measure condition, injectivity
of `v`, and membership of its values in the window are supplied separately.
Outside scores have no additional joint-law restriction. -/
def CorrectedLocal {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : MeasureTheory.Measure Ω) (X : Ω → Fin N → ℝ) (b : ℝ)
    (S : Finset (Fin N)) (v : S → ℝ) : Prop :=
  (∀ i, Measurable (fun ω => X ω i)) ∧
  (∀ i, eventProb μ (fun ω => inWindow b (X ω i)) = if i ∈ S then 1 else 0) ∧
  (∀ σ : Equiv.Perm S, eventProb μ (fun ω => ∀ i : S, X ω i = v (σ i)) =
    1 / (S.card.factorial : ℝ))

/-- The uniform law on all n! permutations of a finite local population, the
intended local law (p. 130 prose) and corrected marginal law P014-T6. -/
def permutationLaw (ι : Type*) [Fintype ι] [DecidableEq ι] : FiniteLaw (Equiv.Perm ι) := by
  classical
  refine ⟨Finset.univ, fun _ => 1 / (Fintype.card (Equiv.Perm ι) : ℝ), ?_, ?_⟩
  · intro σ hσ
    have hp : (0 : ℝ) < Fintype.card (Equiv.Perm ι) := by exact_mod_cast Fintype.card_pos
    exact one_div_pos.mpr hp
  · simp

/-- T6 finite counting lemma: permutation of local values preserves the
number of nonnegative scores, hence the local treated count (p. 130, corrected). -/
theorem permutation_count {ι : Type*} [Fintype ι] (v : ι → ℝ) (σ : Equiv.Perm ι) :
    (∑ i : ι, if 0 ≤ v (σ i) then (1 : ℝ) else 0) =
      (Finset.univ.filter (fun i => 0 ≤ v i)).card := by
  classical
  calc
    _ = ∑ i : ι, if 0 ≤ v i then (1 : ℝ) else 0 :=
      Equiv.sum_comp σ (fun i => if 0 ≤ v i then (1 : ℝ) else 0)
    _ = _ := by simp

/-- T6 finite counting lemma: a uniformly random permutation puts each local
score at a fixed subject with probability 1/n. The proof averages over all
positions and uses permutation symmetry, without assuming independence. -/
theorem uniform_permutation_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (i : ι) :
    (permutationLaw ι).expect (fun σ => f (σ i)) =
      (∑ j : ι, f j) / Fintype.card ι := by
  classical
  let A : ι → ℝ := fun j => ∑ σ : Equiv.Perm ι, f (σ j)
  have he : ∀ j, A j = A i := by
    intro j
    have h := Equiv.sum_comp (Equiv.mulRight (Equiv.swap i j))
      (fun σ : Equiv.Perm ι => f (σ j))
    simpa [A, Equiv.Perm.mul_apply] using h.symm
  have hsum : (Fintype.card ι : ℝ) * A i =
      (Fintype.card (Equiv.Perm ι) : ℝ) * ∑ j : ι, f j := by
    calc
      _ = ∑ j : ι, A j := by simp [he]
      _ = ∑ σ : Equiv.Perm ι, ∑ j : ι, f (σ j) := by
        unfold A; rw [Finset.sum_comm]
      _ = ∑ σ : Equiv.Perm ι, ∑ j : ι, f j := by simp_rw [Equiv.sum_comp]
      _ = _ := by simp
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    have : Nonempty ι := ⟨i⟩
    exact_mod_cast ne_of_gt Fintype.card_pos
  have hk : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt Fintype.card_pos
  unfold permutationLaw FiniteLaw.expect
  simp only
  rw [← Finset.mul_sum]
  change (1 / (Fintype.card (Equiv.Perm ι) : ℝ)) * A i = _
  field_simp
  nlinarith [hsum]

/-- T6(b)'s finite lemma: the common local treatment propensity is m/n,
where m is the number of nonnegative fixed scores. -/
theorem uniform_permutation_propensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (i : ι) :
    (permutationLaw ι).prob (fun σ => 0 ≤ v (σ i)) =
      ((Finset.univ.filter (fun j => 0 ≤ v j)).card : ℝ) / Fintype.card ι := by
  classical
  have h := uniform_permutation_average (fun j => if 0 ≤ v j then (1 : ℝ) else 0) i
  simpa [FiniteLaw.expect, FiniteLaw.prob, mul_ite, permutationLaw] using h

/-- T6(c)'s finite lemma: distinct local values remain distinct at different
subjects under any arrangement, so no distinct-subject tie is possible. -/
theorem permutation_no_ties {ι : Type*} (v : ι → ℝ) (hv : Function.Injective v)
    (σ : Equiv.Perm ι) (i j : ι) (hij : i ≠ j) : v (σ i) ≠ v (σ j) := by
  intro h
  exact hij (σ.injective (hv h))

/-- A finite local-subvector uniform law, the discrete specialization of
P014-T6's corrected clause, with fixed membership and no outside-law restriction. -/
def FiniteCorrectedLocal {Ω : Type*} {N : ℕ} (L : FiniteLaw Ω)
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (v : S → ℝ) : Prop :=
  (∀ ω ∈ L.support, windowSet b (X ω) = S) ∧
  (∀ σ : Equiv.Perm S, L.prob (fun ω => ∀ i : S, X ω i = v (σ i)) =
    1 / (S.card.factorial : ℝ))

/-- The assignment induced by a local score arrangement with fixed outside
TREATMENTS (not fixed outside scores), used in T3(c)'s counting assertion. -/
def assignmentFromPermutation {N : ℕ} (S : Finset (Fin N)) (v : S → ℝ)
    (c : Assignment N) (σ : Equiv.Perm S) : Assignment N := fun i =>
  if h : i ∈ S then decide (0 ≤ v (σ ⟨i, h⟩)) else c i

/-- T6(d), finite fiber identity: under a uniform local marginal with k points,
uniform full-vector masses 1/k are equivalent to each local value having
exactly one full supported vector above it (P014-E002). -/
theorem uniform_joint_iff_injective_local {α β : Type*} (L : FiniteLaw α)
    (f : α → β) (k : ℕ) (hk : 0 < k)
    (hlocal : ∀ b, (∃ a ∈ L.support, f a = b) → L.prob (fun a => f a = b) = 1 / (k : ℝ)) :
    (∀ a ∈ L.support, L.mass a = 1 / (k : ℝ)) ↔
      Set.InjOn f (L.support : Set α) := by
  classical
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  constructor
  · intro hfull a ha b hb hab
    change a ∈ L.support at ha
    change b ∈ L.support at hb
    let K := L.support.filter (fun x => f x = f a)
    have hsum : L.prob (fun x => f x = f a) = (K.card : ℝ) / k := by
      unfold FiniteLaw.prob
      change (∑ x ∈ L.support, if f x = f a then L.mass x else 0) = _
      rw [← Finset.sum_filter]
      calc
        _ = ∑ x ∈ K, (1 / (k : ℝ)) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hfull x (Finset.mem_filter.mp hx).1
        _ = _ := by simp <;> ring
    have he := hlocal (f a) ⟨a, ha, rfl⟩
    rw [hsum] at he
    have hc : K.card = 1 := by
      have : (K.card : ℝ) = 1 := by apply (div_left_inj' hk').mp; exact he
      exact_mod_cast this
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
    have haK : a ∈ K := by simp [K, ha]
    have hbK : b ∈ K := by simp [K, hb, hab]
    rw [hx, Finset.mem_singleton] at haK hbK
    exact haK.trans hbK.symm
  · intro hinj a ha
    have he := hlocal (f a) ⟨a, ha, rfl⟩
    have hfilter : L.support.filter (fun x => f x = f a) = {a} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, hfa⟩; exact hinj hx ha hfa
      · rintro rfl; exact ⟨ha, rfl⟩
    simpa [FiniteLaw.prob, ← Finset.sum_filter, hfilter] using he

/-- T6(e): six uniformly random local arrangements, independently of a binary
outside score with probabilities 1/3 and 2/3. The 12 atoms have masses 1/18,1/9. -/
def extendedLaw : FiniteLaw (Fin 6 × Bool) :=
  ⟨Finset.univ, fun ω => if ω.2 then 1/9 else 1/18,
    by intro ω hω; cases ω.2 <;> norm_num,
    by norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ]⟩

/-- T6(e)'s full running scores: the six local arrangements of (-2,-1,1),
and the independently randomized outside score -3 or 3 (P014-E002). -/
def extendedX (ω : Fin 6 × Bool) : Fin 4 → ℝ := fun i =>
  if i = 3 then (if ω.2 then 3 else -3) else witnessX ω.1 i

/-- T6(e), the corrected law admits independent outside randomization and
excludes the printed full-vector mass clause: each local arrangement has
probability 1/6, while each of the 12 full rows has probability 1/18 or 1/9. -/
theorem corrected_law_allows_outside_randomness :
    (∀ ω : Fin 6 × Bool, windowSet 2 (extendedX ω) = threeWindow) ∧
    (∀ a : Fin 6, extendedLaw.prob (fun ω =>
      (fun i : Fin 3 => extendedX ω (Fin.castSucc i)) =
      (fun i : Fin 3 => witnessX a (Fin.castSucc i))) = 1/6) ∧
    (∀ ω : Fin 6 × Bool, extendedLaw.prob (fun η => extendedX η = extendedX ω) =
      if ω.2 then 1/9 else 1/18) ∧
    (∀ ω : Fin 6 × Bool, extendedLaw.prob (fun η => extendedX η = extendedX ω) ≠ 1/6) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨ω, a⟩
    ext i
    fin_cases ω <;> cases a <;> fin_cases i <;>
      norm_num [windowSet, inWindow, extendedX, witnessX, threeWindow]
  · intro a
    fin_cases a <;> norm_num [FiniteLaw.prob, extendedLaw, extendedX, witnessX,
      Fintype.sum_prod_type, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]
  · rintro ⟨ω, a⟩
    fin_cases ω <;> cases a <;> norm_num [FiniteLaw.prob, extendedLaw, extendedX, witnessX,
      Fintype.sum_prod_type, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]
  · rintro ⟨ω, a⟩
    fin_cases ω <;> cases a <;> norm_num [FiniteLaw.prob, extendedLaw, extendedX, witnessX,
      Fintype.sum_prod_type, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]

/-- T7(a)--(b) for ANY probability law, including continuous running variables:
the literal printed no-ties condition (with the diagonal) is equivalent to an
empty window set. Distinct-subject no-ties has exactly the off-diagonal clauses. -/
theorem no_ties_diagonal_general {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Fin N → ℝ) (S : Finset (Fin N)) :
    (∀ i ∈ S, ∀ j ∈ S, eventProb μ (fun ω => X ω i = X ω j) = 0) ↔ S = ∅ := by
  classical
  constructor
  · intro h
    by_contra hs
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have he := h i hi i hi
    norm_num [eventProb] at he
  · rintro rfl
    simp

/-- The six actual permutations of three scores, corresponding to the six
rows of the T1/T9 counterexamples. -/
def rowPermutation (ω : Fin 6) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective
    (![![0,1,2], ![0,2,1], ![1,0,2], ![1,2,0], ![2,0,1], ![2,1,0]] ω)
    (by fin_cases ω <;> decide)

/-- T1/T9: the six rows exhaust ALL 3! permutations, not just a six-element
subset of possible arrangements. This verifies the prose assumption of p.130. -/
theorem rows_exhaust_permutations : Function.Bijective rowPermutation := by
  apply (Fintype.bijective_iff_injective_and_card rowPermutation).mpr
  constructor
  · intro a b h
    have hp := congrArg (fun σ : Equiv.Perm (Fin 3) => (σ 0, σ 1)) h
    fin_cases a <;> fin_cases b <;> norm_num [rowPermutation, Equiv.ofBijective] at hp <;> rfl
  · norm_num [Fintype.card_perm]

/-- T1 and T9 score rows are exactly the corresponding permutations of
(-2,-1,1) and (-1,-1/2,1/2), respectively (P014-E001 and P014-N002). -/
theorem score_rows_are_permutations :
    (∀ ω : Fin 6, ∀ i : Fin 3,
      witnessX ω (Fin.castSucc i) = (![-2,-1,1] : Fin 3 → ℝ) (rowPermutation ω i)) ∧
    (∀ ω : Fin 6, ∀ i : Fin 3,
      comparisonX ω (Fin.castSucc i) = (![-1,-(1/2),1/2] : Fin 3 → ℝ) (rowPermutation ω i)) := by
  constructor <;> intro ω i <;> fin_cases ω <;> fin_cases i <;>
    norm_num [witnessX, comparisonX, rowPermutation, Equiv.ofBijective]

/-- T1/T9: probability of EACH of the 3! in-window permutations is 1/6,
with explicit threshold-valid running scores. -/
theorem all_local_permutations_equiprobable :
    (∀ σ : Equiv.Perm (Fin 3), sixLaw.prob (fun ω => ∀ i : Fin 3,
      witnessX ω (Fin.castSucc i) = (![-2,-1,1] : Fin 3 → ℝ) (σ i)) = 1/6) ∧
    (∀ σ : Equiv.Perm (Fin 3), sixLaw.prob (fun ω => ∀ i : Fin 3,
      comparisonX ω (Fin.castSucc i) = (![-1,-(1/2),1/2] : Fin 3 → ℝ) (σ i)) = 1/6) := by
  constructor <;> intro σ <;> obtain ⟨ω, rfl⟩ := rows_exhaust_permutations.2 σ <;>
    fin_cases ω <;> norm_num [FiniteLaw.prob, sixLaw, Fin.sum_univ_succ,
      witnessX, comparisonX, rowPermutation, Equiv.ofBijective, Fin.forall_fin_succ]

/-- T7(c): the corrected distinct-subject no-ties condition is satisfiable
in a nonempty window, in the exact counterexample designs of T1, T5, and T9. -/
theorem corrected_no_ties_witnesses :
    threeWindow.card = 3 ∧ DistinctNoTies sixLaw witnessX threeWindow ∧
      DistinctNoTies sixLaw defectiveX threeWindow ∧ DistinctNoTies sixLaw comparisonX threeWindow := by
  refine ⟨by norm_num [threeWindow], witness_printed_local.2.2.2.1,
    defective_printed_local.2.2.2.1, comparison_printed_local.2.2.2.1⟩

/-- A probability-one event holds almost surely; used to translate fixed
window membership and the corrected local mass clauses on p. 130 (T6). -/
theorem ae_event_of_probability_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (P : Ω → Prop) (hMeas : MeasurableSet {ω | P ω}) (hp : eventProb μ P = 1) :
    ∀ᵐ ω ∂μ, P ω := by
  apply (MeasureTheory.mem_ae_iff_prob_eq_one hMeas).mpr
  have h := congrArg ENNReal.ofReal hp
  simpa [eventProb, ENNReal.ofReal_toReal (MeasureTheory.measure_ne_top μ _)] using h

/-- A probability-zero event fails almost surely (T6, fixed outside membership). -/
theorem ae_not_of_probability_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (P : Ω → Prop) (hp : eventProb μ P = 0) : ∀ᵐ ω ∂μ, ¬ P ω := by
  apply MeasureTheory.ae_iff.mpr
  have hzero : μ {ω | P ω} = 0 :=
    (MeasureTheory.measureReal_eq_zero_iff (μ := μ)).mp hp
  simpa using hzero

/-- T6 probability lemma: a finite family of disjoint measurable events,
each of mass 1/k, with k events, covers the probability space almost surely. -/
theorem uniform_partition_covers {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (A : ι → Set Ω)
    (hMeas : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hp : ∀ i, μ.real (A i) = 1 / (Fintype.card ι : ℝ)) :
    ∀ᵐ ω ∂μ, ∃ i, ω ∈ A i := by
  have hmass : μ.real (⋃ i, A i) = 1 := by
    rw [MeasureTheory.measureReal_iUnion_fintype hdisj hMeas]
    simp [hp, Fintype.card_ne_zero]
  have hAE := ae_event_of_probability_one μ (fun ω => ω ∈ ⋃ i, A i)
    (MeasurableSet.iUnion hMeas) hmass
  simpa using hAE

/-- T6 probability lemma: for a finite uniform event partition, an event
constant on each part has probability equal to its fraction of selected parts. -/
theorem probability_from_uniform_partition {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hMeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hp : ∀ i, μ.real (A i) = 1 / (Fintype.card ι : ℝ))
    (hcover : ∀ᵐ ω ∂μ, ∃ i, ω ∈ A i) (P : Ω → Prop) (R : ι → Prop) [DecidablePred R]
    (hon : ∀ i, ∀ ω ∈ A i, P ω ↔ R i) :
    eventProb μ P = ((Finset.univ.filter R).card : ℝ) / Fintype.card ι := by
  classical
  have he : {ω | P ω} =ᵐ[μ] ⋃ i : {i : ι // R i}, A i := by
    filter_upwards [hcover] with ω hω
    change P ω = (ω ∈ ⋃ i : {i : ι // R i}, A i)
    apply propext
    simp only [Set.mem_iUnion]
    constructor
    · intro hP
      obtain ⟨i, hi⟩ := hω
      exact ⟨⟨i, (hon i ω hi).mp hP⟩, hi⟩
    · rintro ⟨i, hi⟩
      exact (hon i ω hi).mpr i.property
  change μ.real {ω | P ω} = _
  rw [MeasureTheory.measureReal_congr he]
  have hd : Pairwise (fun (i j : {i : ι // R i}) => Disjoint (A i) (A j)) := by
    intro i j hij
    apply hdisj
    exact fun h => hij (Subtype.ext h)
  rw [MeasureTheory.measureReal_iUnion_fintype hd (fun i => hMeas i)]
  simp [hp, Fintype.card_subtype]
  rw [div_eq_mul_inv]

/-- T6(b)'s factorial expression is exactly m/n for n≥1, without asymptotics. -/
theorem factorial_propensity_ratio (n m : ℕ) (hn : 0 < n) :
    (m : ℝ) * (n - 1).factorial / n.factorial = (m : ℝ) / n := by
  have he : n.factorial = n * (n - 1).factorial := by
    have hns : n = n - 1 + 1 := by omega
    nth_rw 1 [hns]
    rw [Nat.factorial_succ]
    congr 1
    omega
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hf : ((n - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - 1)
  rw [he, Nat.cast_mul]
  field_simp

/-- T6(a)--(c), the corrected running-variable assumption and its conclusions
on a GENERAL probability space. Fixed local counts, common propensities, fixed
membership, common empirical CDF, and no distinct-subject ties. This includes
continuous outside allocations. The proof uses a measurable uniform event partition. -/
theorem corrected_local_randomization {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    {N : ℕ} (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N))
    (v : S → ℝ) (m : ℕ) (_hb : 0 < b) (_hn : 2 ≤ S.card)
    (_hv : Function.Injective v) (_hwin : ∀ i, inWindow b (v i))
    (_hm : 0 < m) (_hmn : m < S.card)
    (_hmdef : (Finset.univ.filter (fun i : S => 0 ≤ v i)).card = m)
    (_hl : CorrectedLocal μ X b S v) :
    (∀ᵐ ω ∂μ, armCount S (threshold (X ω)) true = m ∧
      windowSet b (X ω) = S ∧
      ∀ t, empiricalCDF S (X ω) t =
        (∑ i : S, if v i ≤ t then (1 : ℝ) else 0) / S.card) ∧
    (∀ i : S, eventProb μ (fun ω => threshold (X ω) i = true) =
      (m : ℝ) * (S.card - 1).factorial / S.card.factorial ∧
      eventProb μ (fun ω => threshold (X ω) i = true) = (m : ℝ) / S.card ∧
      eventProb μ (fun ω => threshold (X ω) i = false) = ((S.card : ℝ) - m) / S.card) ∧
    (∀ i j : S, i ≠ j → eventProb μ (fun ω => X ω i = X ω j) = 0) := by
  classical
  let A : Equiv.Perm S → Set Ω := fun σ => {ω | ∀ i : S, X ω i = v (σ i)}
  have hMeas : ∀ σ, MeasurableSet (A σ) := by
    intro σ
    have h := MeasurableSet.iInter (fun i : S =>
      measurableSet_eq_fun (_hl.1 i) (measurable_const (a := v (σ i))))
    convert h using 1
    ext ω
    simp [A]
  have hdisj : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro σ τ hστ
    apply Set.disjoint_left.mpr
    intro ω hσ hτ
    apply hστ
    apply Equiv.ext
    intro i
    exact _hv ((hσ i).symm.trans (hτ i))
  have hprob : ∀ σ, μ.real (A σ) = 1 / (Fintype.card (Equiv.Perm S) : ℝ) := by
    intro σ
    simpa [A, eventProb, MeasureTheory.measureReal_def, Fintype.card_perm] using _hl.2.2 σ
  have hcover := uniform_partition_covers μ A hMeas hdisj hprob
  have hfixed : ∀ᵐ ω ∂μ, ∀ i : Fin N, inWindow b (X ω i) ↔ i ∈ S := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    have hm : MeasurableSet {ω | inWindow b (X ω i)} := by
      change MeasurableSet ((fun ω => X ω i) ⁻¹' Set.Icc (-b) b)
      exact measurableSet_Icc.preimage (_hl.1 i)
    by_cases hi : i ∈ S
    · have hp : eventProb μ (fun ω => inWindow b (X ω i)) = 1 := by
        simpa [hi] using _hl.2.1 i
      filter_upwards [ae_event_of_probability_one μ _ hm hp] with ω hω
      simp [hω, hi]
    · have hp : eventProb μ (fun ω => inWindow b (X ω i)) = 0 := by
        simpa [hi] using _hl.2.1 i
      filter_upwards [ae_not_of_probability_zero μ _ hp] with ω hω
      simp [hω, hi]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hcover, hfixed] with ω hω hwω
    obtain ⟨σ, hσ⟩ := hω
    change ∀ i : S, X ω i = v (σ i) at hσ
    refine ⟨?_, ?_, ?_⟩
    · unfold armCount threshold
      rw [← Finset.sum_coe_sort]
      simp_rw [hσ]
      simp only [decide_eq_true_eq]
      rw [permutation_count, _hmdef]
    · ext i
      simp [windowSet, hwω i]
    · intro t
      unfold empiricalCDF
      rw [← Finset.sum_coe_sort]
      simp_rw [hσ]
      congr 1
      exact Equiv.sum_comp σ (fun i => if v i ≤ t then (1 : ℝ) else 0)
  · intro i
    have hpt : eventProb μ (fun ω => threshold (X ω) i = true) = (m : ℝ) / S.card := by
      rw [probability_from_uniform_partition μ A hMeas hdisj hprob hcover _
        (fun σ => 0 ≤ v (σ i)) (by
          intro σ ω hω
          simp [threshold, hω i])]
      have hperm := uniform_permutation_propensity v i
      have hex : (permutationLaw S).prob (fun σ => 0 ≤ v (σ i)) =
          ((Finset.univ.filter (fun σ : Equiv.Perm S => 0 ≤ v (σ i))).card : ℝ) /
            Fintype.card (Equiv.Perm S) := by
        unfold FiniteLaw.prob permutationLaw
        simp only
        rw [← Finset.sum_filter]
        simp <;> ring
      rw [hex, _hmdef] at hperm
      simpa only [Fintype.card_coe] using hperm
    have hpf : eventProb μ (fun ω => threshold (X ω) i = false) =
        ((S.card : ℝ) - m) / S.card := by
      have hm : MeasurableSet {ω | threshold (X ω) i = true} := by
        have h := (measurableSet_Ici : MeasurableSet (Set.Ici (0 : ℝ))).preimage (_hl.1 i)
        convert h using 1
        ext ω
        simp [threshold]
      have hcomp := MeasureTheory.probReal_compl_eq_one_sub (μ := μ) hm
      have hset : {ω | threshold (X ω) i = false} = {ω | threshold (X ω) i = true}ᶜ := by
        ext ω; cases threshold (X ω) i <;> simp
      change μ.real {ω | threshold (X ω) i = false} = _
      rw [hset, hcomp]
      change 1 - eventProb μ (fun ω => threshold (X ω) i = true) = _
      rw [hpt]
      have hn' : (S.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (by omega : 0 < S.card)
      field_simp <;> ring
    exact ⟨hpt.trans (factorial_propensity_ratio S.card m (by omega)).symm, hpt, hpf⟩
  · intro i j hij
    have hnot : ∀ᵐ ω ∂μ, X ω i ≠ X ω j := by
      filter_upwards [hcover] with ω hω
      obtain ⟨σ, hσ⟩ := hω
      rw [hσ i, hσ j]
      exact permutation_no_ties v _hv σ i j hij
    have hz : μ {ω | X ω i = X ω j} = 0 := by
      simpa using MeasureTheory.ae_iff.mp hnot
    simp [eventProb, hz]


/-- T6(d), the meaning of one full-vector support point above each local
arrangement: the full vector can be reconstructed from its local subvector.
Thus the outside scores are a function of the local arrangement, almost surely. -/
theorem injective_local_iff_reconstructible {α β : Type*} (L : FiniteLaw α) (f : α → β) :
    Set.InjOn f (L.support : Set α) ↔ ∃ g : β → α, ∀ a ∈ L.support, g (f a) = a := by
  classical
  constructor
  · intro hinj
    have hne : L.support.Nonempty := by
      by_contra he
      have hempty := Finset.not_nonempty_iff_eq_empty.mp he
      have ht := L.total
      simp [hempty] at ht
    obtain ⟨a₀, ha₀⟩ := hne
    let g : β → α := fun b => if hb : ∃ a, a ∈ L.support ∧ f a = b then
      Classical.choose hb else a₀
    refine ⟨g, ?_⟩
    intro a ha
    have he : ∃ x, x ∈ L.support ∧ f x = f a := ⟨a, ha, rfl⟩
    dsimp [g]
    rw [dite_eq_left he]
    exact hinj (Classical.choose_spec he).1 ha (Classical.choose_spec he).2
  · rintro ⟨g, hg⟩ a ha b hb hab
    exact (hg a ha).symm.trans ((congrArg g hab).trans (hg b hb))

/-- T10(a)'s full-assignment conditional sum equals the probability-weighted
ratio: Σ_{z:z_i=a} y_i(z) Pr(Z=z | Z_i=a). -/
theorem conditional_full_average_eq_weighted {N : ℕ} (L : FiniteLaw (Assignment N))
    (y : Outcomes N) (i : Fin N) (a : Bool) (_hp : 0 < armMass L i a) :
    (∑ z ∈ armSupport L i a, y i z * (L.mass z / armMass L i a)) =
      weightedMean L y i a := by
  unfold weightedMean weightedNumerator
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- T7(b): the printed and corrected no-ties requirements differ exactly by
one impossible probability-zero diagonal requirement for each window subject. -/
theorem no_ties_quantifier_decomposition {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : MeasureTheory.Measure Ω) (X : Ω → Fin N → ℝ) (S : Finset (Fin N)) :
    (∀ i ∈ S, ∀ j ∈ S, eventProb μ (fun ω => X ω i = X ω j) = 0) ↔
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → eventProb μ (fun ω => X ω i = X ω j) = 0) ∧
      (∀ i ∈ S, eventProb μ (fun ω => X ω i = X ω i) = 0) := by
  constructor
  · intro h
    exact ⟨fun i hi j hj _ => h i hi j hj, fun i hi => h i hi i hi⟩
  · rintro ⟨h, hd⟩ i hi j hj
    by_cases hij : i = j
    · subst j; exact hd i hi
    · exact h i hi j hj hij




/-- T3(c)'s finite combinatorial reduction: a permutation matching two binary
partitions is exactly a pair of bijections on their treated and control parts. -/
def matchingPermutationEquiv {ι : Type*} (p q : ι → Prop) [DecidablePred p] [DecidablePred q] :
    {σ : Equiv.Perm ι // ∀ i, p i ↔ q (σ i)} ≃
      ({i // p i} ≃ {i // q i}) × ({i // ¬p i} ≃ {i // ¬q i}) := by
  let f : {σ : Equiv.Perm ι // ∀ i, p i ↔ q (σ i)} →
      ({i // p i} ≃ {i // q i}) × ({i // ¬p i} ≃ {i // ¬q i}) := fun σ =>
    (σ.val.subtypeEquiv σ.property, σ.val.subtypeEquiv (fun i => not_congr (σ.property i)))
  apply Equiv.ofBijective f
  constructor
  · intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_cases hi : p i
    · have he := congrArg (fun r : ({i // p i} ≃ {i // q i}) ×
          ({i // ¬p i} ≃ {i // ¬q i}) => (r.1 ⟨i, hi⟩).val) h
      exact he
    · have he := congrArg (fun r : ({i // p i} ≃ {i // q i}) ×
          ({i // ¬p i} ≃ {i // ¬q i}) => (r.2 ⟨i, hi⟩).val) h
      exact he
  · rintro ⟨ep, en⟩
    let σ : Equiv.Perm ι :=
      (Equiv.sumCompl p).symm.trans ((Equiv.sumCongr ep en).trans (Equiv.sumCompl q))
    have hpq : ∀ i, p i ↔ q (σ i) := by
      intro i
      by_cases hi : p i
      · have he : σ i = (ep ⟨i, hi⟩).val := by simp [σ, hi]
        rw [he]
        exact ⟨fun _ => (ep ⟨i, hi⟩).property, fun _ => hi⟩
      · have he : σ i = (en ⟨i, hi⟩).val := by simp [σ, hi]
        rw [he]
        simp [hi, (en ⟨i, hi⟩).property]
    refine ⟨⟨σ, hpq⟩, ?_⟩
    apply Prod.ext <;> apply Equiv.ext <;> intro i <;> apply Subtype.ext
    · simp [f, σ, Equiv.subtypeEquiv, i.property]
    · simp [f, σ, Equiv.subtypeEquiv, i.property]

/-- T3(c)'s finite counting lemma: if a score permutation matches the
requested treatment partition, the number that do so is m!(n-m)!. -/
theorem matching_permutation_count {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ι → Prop)
    [DecidablePred p] [DecidablePred q] (σ₀ : Equiv.Perm ι)
    (hσ₀ : ∀ i, p i ↔ q (σ₀ i)) :
    Fintype.card {σ : Equiv.Perm ι // ∀ i, p i ↔ q (σ i)} =
      (Fintype.card {i // q i}).factorial *
        (Fintype.card ι - Fintype.card {i // q i}).factorial := by
  classical
  rw [Fintype.card_congr (matchingPermutationEquiv p q), Fintype.card_prod,
    Fintype.card_equiv (σ₀.subtypeEquiv hσ₀),
    Fintype.card_equiv (σ₀.subtypeEquiv (fun i => not_congr (hσ₀ i))),
    Fintype.card_subtype_compl]
  rw [Fintype.card_congr (σ₀.subtypeEquiv hσ₀)]

/-- T3(c)'s exact finite pushforward identity, before using any counting
formula: an assignment's probability equals its number of score preimages / n!. -/
theorem assignment_permutation_mass {N : ℕ} (S : Finset (Fin N)) (v : S → ℝ)
    (c : Assignment N) (z : Assignment N) :
    ((permutationLaw S).map (assignmentFromPermutation S v c)).mass z =
      ((Finset.univ.filter (fun σ : Equiv.Perm S =>
        assignmentFromPermutation S v c σ = z)).card : ℝ) / S.card.factorial := by
  classical
  unfold FiniteLaw.map FiniteLaw.prob permutationLaw
  simp only
  change (∑ σ : Equiv.Perm S, if assignmentFromPermutation S v c σ = z then
    (1 / (Fintype.card (Equiv.Perm S) : ℝ)) else 0) = _
  rw [← Finset.sum_filter]
  simp [Fintype.card_perm] <;> ring

/-- T3(c)'s score-fiber characterization: with the outside treatments fixed,
a permutation yields z exactly when its score signs match z at every local subject. -/
theorem assignment_matching_iff {N : ℕ} (S : Finset (Fin N)) (v : S → ℝ)
    (c z : Assignment N) (σ : Equiv.Perm S)
    (hout : ∀ i ∉ S, z i = c i) :
    assignmentFromPermutation S v c σ = z ↔
      ∀ i : S, z i = true ↔ 0 ≤ v (σ i) := by
  constructor
  · intro h i
    rw [← h]
    simp [assignmentFromPermutation, i.property]
  · intro h
    funext i
    by_cases hi : i ∈ S
    · have he : z i = true ↔ decide (0 ≤ v (σ ⟨i, hi⟩)) = true := by
        simpa using h ⟨i, hi⟩
      have hb : decide (0 ≤ v (σ ⟨i, hi⟩)) = z i := by
        cases hzi : z i <;> cases hvi : decide (0 ≤ v (σ ⟨i, hi⟩)) <;> simp_all
      simpa [assignmentFromPermutation, hi] using hb
    · simpa [assignmentFromPermutation, hi] using (hout i hi).symm

/-- T3(c)'s finite preimage count, for every assignment actually obtainable
from a local score permutation with fixed outside treatments. -/
theorem assignment_permutation_fiber_count {N : ℕ} (S : Finset (Fin N)) (v : S → ℝ)
    (c z : Assignment N) (m : ℕ)
    (hmdef : (Finset.univ.filter (fun i : S => 0 ≤ v i)).card = m)
    (σ₀ : Equiv.Perm S) (hσ₀ : assignmentFromPermutation S v c σ₀ = z) :
    (Finset.univ.filter (fun σ : Equiv.Perm S =>
      assignmentFromPermutation S v c σ = z)).card = m.factorial * (S.card - m).factorial := by
  classical
  have hout : ∀ i ∉ S, z i = c i := by
    intro i hi
    rw [← hσ₀]
    simp [assignmentFromPermutation, hi]
  have he : (Finset.univ.filter (fun σ : Equiv.Perm S =>
      assignmentFromPermutation S v c σ = z)) =
      (Finset.univ.filter (fun σ : Equiv.Perm S =>
        ∀ i : S, z i = true ↔ 0 ≤ v (σ i))) := by
    ext σ
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      assignment_matching_iff S v c z σ hout
  rw [he, ← Fintype.card_subtype]
  rw [matching_permutation_count (fun i : S => z i = true) (fun i : S => 0 ≤ v i)
    σ₀ ((assignment_matching_iff S v c z σ₀ hout).mp hσ₀)]
  simp only [Fintype.card_coe]
  simp only [Fintype.card_subtype, hmdef]

/-- T3(c): EVERY full binary vector with the fixed outside treatments and
exactly m treated local subjects is realized by some score permutation. Thus
the preimage-count conclusion is not restricted to already-supported vectors. -/
theorem assignment_with_count_obtainable {N : ℕ} (S : Finset (Fin N)) (v : S → ℝ)
    (c z : Assignment N) (m : ℕ)
    (hmdef : (Finset.univ.filter (fun i : S => 0 ≤ v i)).card = m)
    (hout : ∀ i ∉ S, z i = c i) (hzcount : armCount S z true = m) :
    ∃ σ : Equiv.Perm S, assignmentFromPermutation S v c σ = z := by
  classical
  have hpc : Fintype.card {i : S // z i = true} = m := by
    have hs : armCount S z true = (Fintype.card {i : S // z i = true} : ℝ) := by
      unfold armCount
      rw [← Finset.sum_coe_sort]
      simp [Fintype.card_subtype]
    exact_mod_cast hs.symm.trans hzcount
  have hqc : Fintype.card {i : S // 0 ≤ v i} = m := by
    simpa only [Fintype.card_subtype] using hmdef
  let ep : {i : S // z i = true} ≃ {i : S // 0 ≤ v i} :=
    Fintype.equivOfCardEq (hpc.trans hqc.symm)
  have hneg : Fintype.card {i : S // ¬z i = true} =
      Fintype.card {i : S // ¬0 ≤ v i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hpc, hqc]
  let en : {i : S // ¬z i = true} ≃ {i : S // ¬0 ≤ v i} := Fintype.equivOfCardEq hneg
  let σ := (matchingPermutationEquiv (fun i : S => z i = true)
    (fun i : S => 0 ≤ v i)).symm (ep, en)
  exact ⟨σ.val, (assignment_matching_iff S v c z σ.val hout).mpr σ.property⟩

/-- T2/T3 finite pushforward identity for event probabilities, from the
threshold relationship between running variables and assignments (p. 130). -/
theorem prob_map {α β : Type*} (L : FiniteLaw α) (f : α → β) (P : β → Prop) :
    (L.map f).prob P = L.prob (fun a => P (f a)) := by
  classical
  have h := expect_map L f (fun b => if P b then (1 : ℝ) else 0)
  simpa [FiniteLaw.expect, FiniteLaw.prob, Function.comp_def, mul_ite] using h

/-- The arm denominator in the corrected first display of p. 131 is exactly
Pr(Z_i=a), represented by the finite law's event probability. -/
theorem armMass_as_prob {N : ℕ} (L : FiniteLaw (Assignment N)) (i : Fin N) (a : Bool) :
    armMass L i a = L.prob (fun z => z i = a) := by
  classical
  unfold armMass armSupport FiniteLaw.prob
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : z i = a <;> simp [h]

/-- T3(c)'s finite fixed-count identity: every score permutation assigns
exactly m window subjects to treatment, independent of the outside treatments. -/
theorem assignment_permutation_count {N : ℕ} (S : Finset (Fin N)) (v : S → ℝ)
    (c : Assignment N) (m : ℕ)
    (hmdef : (Finset.univ.filter (fun i : S => 0 ≤ v i)).card = m)
    (σ : Equiv.Perm S) : armCount S (assignmentFromPermutation S v c σ) true = m := by
  classical
  unfold armCount
  rw [← Finset.sum_coe_sort]
  simp only [assignmentFromPermutation, Subtype.property, dite_true, decide_eq_true_eq]
  rw [permutation_count, hmdef]

/-- T3(c)'s finite common-propensity identity: pushing uniform local score
permutations to binary assignments gives each local subject propensity m/n. -/
theorem assignment_permutation_propensity {N : ℕ} (S : Finset (Fin N)) (v : S → ℝ)
    (c : Assignment N) (m : ℕ)
    (hmdef : (Finset.univ.filter (fun i : S => 0 ≤ v i)).card = m)
    (i : Fin N) (hi : i ∈ S) :
    armMass ((permutationLaw S).map (assignmentFromPermutation S v c)) i true =
      (m : ℝ) / S.card := by
  classical
  rw [armMass_as_prob, prob_map]
  have h := uniform_permutation_propensity v ⟨i, hi⟩
  rw [hmdef] at h
  simpa [assignmentFromPermutation, hi, Fintype.card_coe] using h

/-- Off the distinct image support, a finite pushforward gives mass zero;
this prevents hidden or duplicated support points in T3(c)'s counting argument. -/
theorem map_mass_zero_off_support {α β : Type*} (L : FiniteLaw α) (f : α → β) (b : β)
    (hb : b ∉ (L.map f).support) : (L.map f).mass b = 0 := by
  classical
  unfold FiniteLaw.map FiniteLaw.prob
  simp only
  apply Finset.sum_eq_zero
  intro a ha
  have hne : f a ≠ b := by
    intro h
    apply hb
    exact Finset.mem_image.mpr ⟨a, ha, h⟩
  simp [hne]
/-- Distinct support of the pushforward is exactly the image of the source
support (pp. 130--131). The generic statement keeps the same decidable-equality
instance as the definition even for vectors indexed by a finite population. -/
theorem mem_map_support_iff {α β : Type*} (L : FiniteLaw α) (f : α → β) (b : β) :
    b ∈ (L.map f).support ↔ ∃ a ∈ L.support, f a = b := by
  classical
  exact Finset.mem_image

/-- T3(c), fixed outside treatments and corrected uniform local scores:
every supported full assignment has m!(n-m)! score-arrangement preimages;
the binary support has choose(n,m) points and is uniform; fixed counts,
common propensities, conditional uniformity, and printed unbiasedness follow.
A is the induced finite law of the binary vector, even when outside scores are
continuous. The proof counts the treated/control permutation fibers and uses the actual threshold pushforward law. -/
theorem fixed_outside_uniform_assignments {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (v : S → ℝ)
    (A : FiniteLaw (Assignment N)) (c : Assignment N) (y : Outcomes N) (m : ℕ)
    (_hb : 0 < b) (_hv : Function.Injective v) (_hw : ∀ i, inWindow b (v i))
    (_hm : 0 < m) (_hmn : m < S.card)
    (_hmdef : (Finset.univ.filter (fun i : S => 0 ≤ v i)).card = m)
    (_hl : CorrectedLocal μ X b S v)
    (_hA : ∀ z : Assignment N, eventProb μ (fun ω => threshold (X ω) = z) =
      if z ∈ A.support then A.mass z else 0)
    (_hout : ∀ᵐ ω ∂μ, ∀ i ∉ S, threshold (X ω) i = c i) :
    A.support.card = S.card.choose m ∧
    (∀ z ∈ A.support,
      (Finset.univ.filter (fun σ : Equiv.Perm S =>
        assignmentFromPermutation S v c σ = z)).card = m.factorial * (S.card - m).factorial ∧
      A.mass z = (m.factorial : ℝ) * (S.card - m).factorial / S.card.factorial ∧
      A.mass z = 1 / (S.card.choose m : ℝ)) ∧
    (∀ z ∈ A.support, armCount S z true = m) ∧
    (∀ i ∈ S, armMass A i true = (m : ℝ) / S.card) ∧
    ConditionalUniform A S ∧
    A.expect (differenceInMeans S y) = windowContrast S (printedMean A y) ∧
    (∀ z : Assignment N, (∀ i ∉ S, z i = c i) → armCount S z true = m →
      z ∈ A.support ∧
      (Finset.univ.filter (fun σ : Equiv.Perm S =>
        assignmentFromPermutation S v c σ = z)).card = m.factorial * (S.card - m).factorial ∧
      A.mass z = 1 / (S.card.choose m : ℝ)) := by
  classical
  let φ : Equiv.Perm S → Assignment N := assignmentFromPermutation S v c
  let B : FiniteLaw (Assignment N) := (permutationLaw S).map φ
  let E : Equiv.Perm S → Set Ω := fun σ => {ω | ∀ i : S, X ω i = v (σ i)}
  let localZ : Ω → Assignment N := fun ω i => if i ∈ S then threshold (X ω) i else c i
  have hMeas : ∀ σ, MeasurableSet (E σ) := by
    intro σ
    have h := MeasurableSet.iInter (fun i : S =>
      measurableSet_eq_fun (_hl.1 i) (measurable_const (a := v (σ i))))
    convert h using 1
    ext ω
    simp [E]
  have hdisj : Pairwise (fun σ τ => Disjoint (E σ) (E τ)) := by
    intro σ τ hστ
    apply Set.disjoint_left.mpr
    intro ω hσ hτ
    apply hστ
    apply Equiv.ext
    intro i
    exact _hv ((hσ i).symm.trans (hτ i))
  have hprob : ∀ σ, μ.real (E σ) = 1 / (Fintype.card (Equiv.Perm S) : ℝ) := by
    intro σ
    simpa [E, eventProb, MeasureTheory.measureReal_def, Fintype.card_perm] using _hl.2.2 σ
  have hcover := uniform_partition_covers μ E hMeas hdisj hprob
  have hlocalEq : ∀ᵐ ω ∂μ, threshold (X ω) = localZ ω := by
    filter_upwards [_hout] with ω hω
    funext i
    by_cases hi : i ∈ S
    · simp [localZ, hi]
    · simp [localZ, hi, hω i hi]
  have hpmass : ∀ z : Assignment N,
      (if z ∈ A.support then A.mass z else 0) = B.mass z := by
    intro z
    calc
      _ = eventProb μ (fun ω => threshold (X ω) = z) := (_hA z).symm
      _ = eventProb μ (fun ω => localZ ω = z) := by
        apply MeasureTheory.measureReal_congr
        filter_upwards [hlocalEq] with ω hω
        simp only [hω]
      _ = ((Finset.univ.filter (fun σ : Equiv.Perm S => φ σ = z)).card : ℝ) /
          Fintype.card (Equiv.Perm S) := by
        apply probability_from_uniform_partition μ E hMeas hdisj hprob hcover
        intro σ ω hω
        change ∀ i : S, X ω i = v (σ i) at hω
        have he : localZ ω = φ σ := by
          funext i
          by_cases hi : i ∈ S
          · simp [localZ, φ, assignmentFromPermutation, hi, threshold, hω ⟨i, hi⟩]
          · simp [localZ, φ, assignmentFromPermutation, hi]
        rw [he]
      _ = B.mass z := by
        simpa [B, φ, Fintype.card_perm] using (assignment_permutation_mass S v c z).symm
  have hsupport : A.support = B.support := by
    ext z
    constructor
    · intro hz
      by_contra hzb
      have hm := hpmass z
      rw [ite_eq_left hz, map_mass_zero_off_support (permutationLaw S) φ z hzb] at hm
      have hp := A.positive z hz
      linarith
    · intro hz
      by_contra hza
      have hm := hpmass z
      rw [ite_eq_right hza] at hm
      have hp := B.positive z hz
      linarith
  have hmass : ∀ z ∈ A.support, A.mass z = B.mass z := by
    intro z hz
    simpa only [ite_eq_left hz] using hpmass z
  have hfiber : ∀ z ∈ A.support,
      (Finset.univ.filter (fun σ : Equiv.Perm S => φ σ = z)).card =
        m.factorial * (S.card - m).factorial := by
    intro z hz
    rw [hsupport] at hz
    obtain ⟨σ, hσ, rfl⟩ := (mem_map_support_iff (permutationLaw S) φ z).mp hz
    exact assignment_permutation_fiber_count S v c (φ σ) m _hmdef σ rfl
  let F : ℕ := m.factorial * (S.card - m).factorial
  have hmF : ∀ z ∈ A.support, A.mass z = (F : ℝ) / S.card.factorial := by
    intro z hz
    rw [hmass z hz]
    change ((permutationLaw S).map (assignmentFromPermutation S v c)).mass z = _
    rw [assignment_permutation_mass, hfiber z hz]
  have htotal : (A.support.card : ℝ) * (F : ℝ) / S.card.factorial = 1 := by
    calc
      _ = ∑ z ∈ A.support, (F : ℝ) / S.card.factorial := by simp <;> ring
      _ = ∑ z ∈ A.support, A.mass z := Finset.sum_congr rfl (fun z hz => (hmF z hz).symm)
      _ = 1 := A.total
  have hF : (F : ℝ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (Nat.factorial_ne_zero m) (Nat.factorial_ne_zero (S.card - m))
  have hfact : (S.card.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero S.card
  have hbin : (S.card.choose m : ℝ) * (F : ℝ) = S.card.factorial := by
    have hnat : S.card.choose m * F = S.card.factorial := by
      simpa [F, Nat.mul_assoc] using Nat.choose_mul_factorial_mul_factorial _hmn.le
    exact_mod_cast hnat
  have hcard : A.support.card = S.card.choose m := by
    have he : (A.support.card : ℝ) * (F : ℝ) = S.card.factorial :=
      (div_eq_one_iff_eq hfact).mp htotal
    have hc : (A.support.card : ℝ) = S.card.choose m :=
      (mul_right_cancel₀ hF) (he.trans hbin.symm)
    exact_mod_cast hc
  have hchoose : (S.card.choose m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Nat.choose_pos _hmn.le)
  have hfull : ∀ z ∈ A.support, A.mass z = 1 / (A.support.card : ℝ) := by
    intro z hz
    rw [hmF z hz, hcard, ← hbin]
    field_simp
  have hc : ∀ z ∈ A.support, armCount S z true = m := by
    intro z hz
    rw [hsupport] at hz
    obtain ⟨σ, hσ, rfl⟩ := (mem_map_support_iff (permutationLaw S) φ z).mp hz
    exact assignment_permutation_count S v c m _hmdef σ
  have hprobEq : ∀ P : Assignment N → Prop, A.prob P = B.prob P := by
    intro P
    unfold FiniteLaw.prob
    rw [hsupport]
    apply Finset.sum_congr rfl
    intro z hz
    have he : A.mass z = B.mass z := hmass z (hsupport.symm ▸ hz)
    split_ifs <;> first | exact he | rfl
  have hp : ∀ i ∈ S, armMass A i true = (m : ℝ) / S.card := by
    intro i hi
    rw [armMass_as_prob, hprobEq, ← armMass_as_prob]
    exact assignment_permutation_propensity S v c m _hmdef i hi
  have hU := conditional_uniform_of_full_uniform A S hfull
  refine ⟨hcard, ?_, hc, hp, hU,
    printed_unbiasedness_under_U A S y m _hm _hmn hc hp hU, ?_⟩
  · intro z hz
    refine ⟨hfiber z hz, ?_, ?_⟩
    · simpa [F, Nat.cast_mul] using hmF z hz
    · simpa [hcard] using hfull z hz
  · intro z hout hzcount
    obtain ⟨σ, hσ⟩ := assignment_with_count_obtainable S v c z m _hmdef hout hzcount
    have hz : z ∈ A.support := by
      rw [hsupport]
      exact (mem_map_support_iff (permutationLaw S) φ z).mpr ⟨σ, Finset.mem_univ _, hσ⟩
    exact ⟨hz, hfiber z hz, by simpa [hcard] using hfull z hz⟩


/-- A distinct injective image retains the probability of each support point;
this is the finite pushforward fact used in T6(d)'s full-score law. -/
theorem map_mass_of_injective {α β : Type*} (L : FiniteLaw α) (f : α → β)
    (hf : Function.Injective f) (a : α) (ha : a ∈ L.support) :
    (L.map f).mass (f a) = L.mass a := by
  classical
  unfold FiniteLaw.map FiniteLaw.prob
  simp only
  have he : ∀ x, f x = f a ↔ x = a := fun x => hf.eq_iff
  simp_rw [he]
  simp [ha]

/-- A normalized finite law giving every support point mass 1/k has exactly
k support points; T6(d), with k=n!. -/
theorem uniform_finite_support_card {α : Type*} (L : FiniteLaw α) (k : ℕ)
    (hk : 0 < k) (hfull : ∀ a ∈ L.support, L.mass a = 1 / (k : ℝ)) :
    L.support.card = k := by
  have ht : (L.support.card : ℝ) / k = 1 := by
    calc
      _ = ∑ a ∈ L.support, 1 / (k : ℝ) := by simp <;> ring
      _ = ∑ a ∈ L.support, L.mass a :=
        Finset.sum_congr rfl (fun a ha => (hfull a ha).symm)
      _ = 1 := L.total
  have hn : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  exact_mod_cast (div_eq_one_iff_eq hn).mp ht

/-- T6(d)'s explicit cardinal conclusion: an injective local projection under
a uniform k-point local marginal forces exactly k full-vector support points. -/
theorem uniform_joint_support_card {α β : Type*} (L : FiniteLaw α) (f : α → β)
    (k : ℕ) (hk : 0 < k)
    (hlocal : ∀ b, (∃ a ∈ L.support, f a = b) → L.prob (fun x => f x = b) = 1 / (k : ℝ))
    (hinj : Set.InjOn f (L.support : Set α)) : L.support.card = k := by
  apply uniform_finite_support_card L k hk
  exact (uniform_joint_iff_injective_local L f k hk hlocal).mpr hinj

/-- T6(d): combine a local score arrangement with outside scores that are a
function g of that arrangement, without any independence or discreteness
assumption on the original probability space. -/
def scoreFromPermutation {N : ℕ} (S : Finset (Fin N)) (v : S → ℝ)
    (g : (S → ℝ) → Fin N → ℝ) (σ : Equiv.Perm S) : Fin N → ℝ := by
  classical
  exact fun i => if hi : i ∈ S then v (σ ⟨i, hi⟩) else g (fun j => v (σ j)) i

/-- T6(d)'s converse on a GENERAL probability space: when outside scores
are an almost surely deterministic function of the uniform local arrangement,
the full score vector has exactly n! distinct support points, each mass 1/n!.
The finite law is constructed, rather than assumed as an extra hypothesis. -/
theorem outside_function_gives_discrete_full_law {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (v : S → ℝ)
    (g : (S → ℝ) → Fin N → ℝ) (_hv : Function.Injective v)
    (_hl : CorrectedLocal μ X b S v)
    (_hout : ∀ᵐ ω ∂μ, ∀ j ∉ S, X ω j = g (fun i : S => X ω i) j) :
    ∃ A : FiniteLaw (Fin N → ℝ), A.support.card = S.card.factorial ∧
      (∀ x ∈ A.support, A.mass x = 1 / (S.card.factorial : ℝ)) ∧
      (∀ x, eventProb μ (fun ω => X ω = x) = if x ∈ A.support then A.mass x else 0) := by
  classical
  let f : Equiv.Perm S → Fin N → ℝ := scoreFromPermutation S v g
  let B : FiniteLaw (Fin N → ℝ) := (permutationLaw S).map f
  let E : Equiv.Perm S → Set Ω := fun σ => {ω | ∀ i : S, X ω i = v (σ i)}
  let fullX : Ω → Fin N → ℝ := fun ω i =>
    if hi : i ∈ S then X ω i else g (fun j : S => X ω j) i
  have hinj : Function.Injective f := by
    intro σ τ he
    apply Equiv.ext
    intro i
    have h := congrFun he i
    exact _hv (by simpa [f, scoreFromPermutation, i.property] using h)
  have hMeas : ∀ σ, MeasurableSet (E σ) := by
    intro σ
    have h := MeasurableSet.iInter (fun i : S =>
      measurableSet_eq_fun (_hl.1 i) (measurable_const (a := v (σ i))))
    convert h using 1
    ext ω
    simp [E]
  have hdisj : Pairwise (fun σ τ => Disjoint (E σ) (E τ)) := by
    intro σ τ hστ
    apply Set.disjoint_left.mpr
    intro ω hσ hτ
    apply hστ
    apply Equiv.ext
    intro i
    exact _hv ((hσ i).symm.trans (hτ i))
  have hprob : ∀ σ, μ.real (E σ) = 1 / (Fintype.card (Equiv.Perm S) : ℝ) := by
    intro σ
    simpa [E, eventProb, MeasureTheory.measureReal_def, Fintype.card_perm] using _hl.2.2 σ
  have hcover := uniform_partition_covers μ E hMeas hdisj hprob
  have hAE : ∀ᵐ ω ∂μ, X ω = fullX ω := by
    filter_upwards [_hout] with ω hω
    funext i
    by_cases hi : i ∈ S
    · simp [fullX, hi]
    · simp [fullX, hi, hω i hi]
  have hmass : ∀ x ∈ B.support, B.mass x = 1 / (S.card.factorial : ℝ) := by
    intro x hx
    obtain ⟨σ, hσ, rfl⟩ := (mem_map_support_iff (permutationLaw S) f x).mp hx
    change ((permutationLaw S).map f).mass (f σ) = _
    rw [map_mass_of_injective (permutationLaw S) f hinj σ hσ]
    simp [permutationLaw, Fintype.card_perm]
  refine ⟨B, ?_, hmass, ?_⟩
  · apply uniform_finite_support_card B S.card.factorial (Nat.factorial_pos _) hmass
  · intro x
    have hb : B.mass x =
        ((Finset.univ.filter (fun σ : Equiv.Perm S => f σ = x)).card : ℝ) /
          Fintype.card (Equiv.Perm S) := by
      unfold B FiniteLaw.map FiniteLaw.prob permutationLaw
      simp only
      change (∑ σ : Equiv.Perm S, if f σ = x then
        1 / (Fintype.card (Equiv.Perm S) : ℝ) else 0) = _
      rw [← Finset.sum_filter]
      simp <;> ring
    have he : eventProb μ (fun ω => X ω = x) = B.mass x := by
      calc
        _ = eventProb μ (fun ω => fullX ω = x) := by
          apply MeasureTheory.measureReal_congr
          filter_upwards [hAE] with ω hω
          simp only [hω]
        _ = ((Finset.univ.filter (fun σ : Equiv.Perm S => f σ = x)).card : ℝ) /
            Fintype.card (Equiv.Perm S) := by
          apply probability_from_uniform_partition μ E hMeas hdisj hprob hcover
          intro σ ω hω
          change ∀ i : S, X ω i = v (σ i) at hω
          have hl : (fun i : S => X ω i) = fun i : S => v (σ i) := funext hω
          have hr : fullX ω = f σ := by
            funext i
            by_cases hi : i ∈ S
            · simp [fullX, f, scoreFromPermutation, hi, hω ⟨i, hi⟩]
            · simp [fullX, f, scoreFromPermutation, hi, hl]
          rw [hr]
        _ = B.mass x := hb.symm
    rw [he]
    split_ifs with hx
    · rfl
    · exact map_mass_zero_off_support (permutationLaw S) f x hx


/-- An injective pushforward preserves support cardinality (T6(d)--(e),
finite identity for distinct running-variable support vectors). -/
theorem map_support_card_of_injective {α β : Type*} (L : FiniteLaw α) (f : α → β)
    (hf : Function.Injective f) : (L.map f).support.card = L.support.card := by
  classical
  change (L.support.image f).card = L.support.card
  exact Finset.card_image_of_injective _ hf

/-- T6(e): the 12 displayed score rows are pairwise distinct, so they are
12 full-score support points rather than repeated representations of fewer points. -/
theorem extended_scores_injective : Function.Injective extendedX := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  have hp := congrArg (fun u : Fin 4 → ℝ => (u 0, u 1, u 3)) h
  fin_cases a <;> fin_cases b <;> cases x <;> cases y <;>
    norm_num [extendedX, witnessX] at hp <;> rfl

/-- T6(e)'s support cardinality and outside law: there are exactly 12 full
support points; X_4=-3 has probability 1/3 and X_4=3 probability 2/3, and each
local arrangement/outside-value joint probability factors into its marginals.
Together with corrected_law_allows_outside_randomness this gives the
independent-outside counterexample (P014-E002). -/
theorem extended_law_support_and_outside :
    (extendedLaw.map extendedX).support.card = 12 ∧
    extendedLaw.prob (fun ω => extendedX ω 3 = -3) = 1/3 ∧
    extendedLaw.prob (fun ω => extendedX ω 3 = 3) = 2/3 ∧
    (∀ a : Fin 6, ∀ t : Bool,
      extendedLaw.prob (fun ω =>
        (fun i : Fin 3 => extendedX ω (Fin.castSucc i)) =
          (fun i : Fin 3 => witnessX a (Fin.castSucc i)) ∧
        extendedX ω 3 = (if t then 3 else -3)) =
      extendedLaw.prob (fun ω =>
        (fun i : Fin 3 => extendedX ω (Fin.castSucc i)) =
          (fun i : Fin 3 => witnessX a (Fin.castSucc i))) *
      extendedLaw.prob (fun ω => extendedX ω 3 = (if t then 3 else -3))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_support_card_of_injective extendedLaw extendedX extended_scores_injective]
    norm_num [extendedLaw]
  · norm_num [FiniteLaw.prob, extendedLaw, extendedX, Fintype.sum_prod_type, Fin.sum_univ_succ]
  · norm_num [FiniteLaw.prob, extendedLaw, extendedX, Fintype.sum_prod_type, Fin.sum_univ_succ]
  · intro a t
    fin_cases a <;> cases t <;> norm_num [FiniteLaw.prob, extendedLaw, extendedX,
      witnessX, Fintype.sum_prod_type, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]


end
end AronowAudit.P014

