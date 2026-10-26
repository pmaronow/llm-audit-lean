import Mathlib

/-!
Formalizations of claims in Aronow, Coppock, Crawford, and Green, P019.
Locations use printed article pages (PDF page = printed page - 42).
The supplement has its own page numbers. All finite distributions are exact
weighted sums; no Monte Carlo probability is promoted to an exact theorem.
-/

namespace AronowAudit.P019

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical

/-- Section 2, pp. 46-47: "a random sample ... independently drawn from a
large population". The law of one subject is represented by a finite support
and nonnegative real masses summing to one. Fixed finite list counts make
this an exact representation of the observable population law. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

variable {Ω : Type*} [Fintype Ω]

/-- Population expectation, used throughout Sections 2-4: E[f] = Σ p(ω)f(ω). -/
def FiniteLaw.mean (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, P.mass ω * f ω

/-- Population event probability, Section 2, pp. 46-47. -/
def FiniteLaw.prob (P : FiniteLaw Ω) (D : Ω → Prop) [DecidablePred D] : ℝ :=
  P.mean fun ω => if D ω then 1 else 0

/-- E[f | D], Section 2 and Lemma 1, pp. 46-48. A theorem using this as conditioning requires
P(D)>0. The value at a null event is Lean's totalized division, zero. -/
def FiniteLaw.ce (P : FiniteLaw Ω) (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] : ℝ :=
  (P.mean fun ω => if D ω then f ω else 0) / P.prob D

/-- Population variance, Assumption 4, p. 47: E[f²] - E[f]². -/
def FiniteLaw.variance (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  P.mean (fun ω => f ω ^ 2) - (P.mean f) ^ 2

/-- Population conditional variance, Assumption 4, p. 47. -/
def FiniteLaw.cv (P : FiniteLaw Ω) (f : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] : ℝ :=
  P.ce (fun ω => f ω ^ 2) D - (P.ce f D) ^ 2

/-- Covariance appearing in Lemma 2 and the corrected proof of (9), pp. 48,63. -/
def FiniteLaw.cov (P : FiniteLaw Ω) (f g : Ω → ℝ) : ℝ :=
  P.mean (fun ω => f ω * g ω) - P.mean f * P.mean g

/-- Conditional covariance on D in the correction to Lemma 2. -/
def FiniteLaw.ccov (P : FiniteLaw Ω) (f g : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] : ℝ :=
  P.ce (fun ω => f ω * g ω) D - P.ce f D * P.ce g D

/-- A binary variable is represented by Bool, with numeric values 0 and 1;
Section 2, pp. 46-47: "X_i = 1 ... and X_i = 0 otherwise". -/
def bitVal (b : Bool) : ℝ := if b then 1 else 0

/-- Section 2, pp. 46-47: W is "the baseline outcome (under control)",
X indicates engagement, Y is "the report ... to the direct question", Z is
the binary treatment, and V is "the number of items ... applicable".
Both list responses are natural-valued counts. -/
structure Study (Ω : Type*) [Fintype Ω] where
  law : FiniteLaw Ω
  W : Ω → ℕ
  X : Ω → Bool
  Y : Ω → Bool
  Z : Ω → Bool
  V : Ω → ℕ

/-- Assumption 1 (Monotonicity), p. 46: no false positive direct answers,
Y ≤ X. It is imposed only on atoms of positive probability. -/
def Study.monotone (S : Study Ω) : Prop :=
  ∀ ω, 0 < S.law.mass ω → S.Y ω = true → S.X ω = true

/-- Assumption 2 (No Liars and No Design Effects), p. 47:
"we observe V_i = W_i + X_i Z_i". -/
def Study.noLiarsDesign (S : Study Ω) : Prop :=
  ∀ ω, 0 < S.law.mass ω →
    (S.V ω : ℝ) = (S.W ω : ℝ) + bitVal (S.X ω) * bitVal (S.Z ω)

/-- Assumption 3, p. 47: "(W_i,X_i,Y_i) ⟂ Z_i". On finite support this
is expressed by factorization of the expectation of EVERY real function of
(W,X,Y) against each treatment indicator. No equality of conditional means
is assumed in place of independence. -/
def Study.treatmentIndependent (S : Study Ω) : Prop :=
  ∀ (f : ℕ → Bool → Bool → ℝ) (z : Bool),
    S.law.mean (fun ω => if S.Z ω = z then f (S.W ω) (S.X ω) (S.Y ω) else 0) =
    S.law.prob (fun ω => S.Z ω = z) *
      S.law.mean (fun ω => f (S.W ω) (S.X ω) (S.Y ω))

/-- Population (Z,Y) cell used in Sections 3-4, pp. 48-51. -/
def Study.cell (S : Study Ω) (z y : Bool) (ω : Ω) : Prop := S.Z ω = z ∧ S.Y ω = y

/-- Assumption 4, p. 47: all four conditional V variances and the
variances of Z and Y are positive. Positive conditioning probabilities
make explicit the existence of the paper's conditional distributions. -/
def Study.nondegenerate (S : Study Ω) : Prop :=
  (∀ z y, 0 < S.law.prob (S.cell z y) ∧
    0 < S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z y)) ∧
  0 < S.law.variance (fun ω => bitVal (S.Z ω)) ∧
  0 < S.law.variance (fun ω => bitVal (S.Y ω))

/-- The four standing assumptions, Section 2, pp. 46-47. -/
def Study.standing (S : Study Ω) : Prop :=
  S.monotone ∧ S.noLiarsDesign ∧ S.treatmentIndependent ∧ S.nondegenerate

/-- "μ = Pr[X_i = 1]", p. 46. -/
def Study.mu (S : Study Ω) : ℝ := S.law.prob fun ω => S.X ω = true

/-- "p = Pr[Y_i = 1 | X_i = 1]", p. 46. -/
def Study.truthRate (S : Study Ω) : ℝ :=
  S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.X ω = true)

/-- "γ = Pr(Z_i = 1)", p. 48. -/
def Study.gamma (S : Study Ω) : ℝ := S.law.prob fun ω => S.Z ω = true

/-- "E[V_i | Z_i=z,Y_i=y]", the conditional list means in
Sections 2-4, pp. 47-51; m_{z,y} is auxiliary notation for this object. -/
def Study.listMean (S : Study Ω) (z y : Bool) : ℝ :=
  S.law.ce (fun ω => (S.V ω : ℝ)) (S.cell z y)

/-- Equation (1), p. 47: "E[Y_i] + E[1-Y_i]
(E[V_i | Z_i=1,Y_i=0] - E[V_i | Z_i=0,Y_i=0])",
the combined population functional. -/
def Study.combined (S : Study Ω) : ℝ :=
  S.law.mean (fun ω => bitVal (S.Y ω)) +
  S.law.mean (fun ω => 1 - bitVal (S.Y ω)) *
    (S.listMean true false - S.listMean false false)

/-- Placebo Test I, p. 50: "β = E[V_i | Z_i=1,Y_i=1] -
E[V_i | Z_i=0,Y_i=1]". -/
def Study.beta (S : Study Ω) : ℝ := S.listMean true true - S.listMean false true

/-- Placebo Test II, p. 51: "δ = E[Y_i | Z_i=1] - E[Y_i | Z_i=0]". -/
def Study.delta (S : Study Ω) : ℝ :=
  S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = true) -
  S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = false)

/- Elementary finite expectation lemmas; these are not assumptions. -/

/-- Linearity of the finite population expectation used in Lemma 1. -/
theorem mean_add (P : FiniteLaw Ω) (f g : Ω → ℝ) :
    P.mean (fun ω => f ω + g ω) = P.mean f + P.mean g := by
  simp [FiniteLaw.mean, mul_add, Finset.sum_add_distrib]

/-- Expectation of a constant under a normalized finite law. -/
theorem mean_const (P : FiniteLaw Ω) (c : ℝ) : P.mean (fun _ => c) = c := by
  rw [FiniteLaw.mean, ← Finset.sum_mul, P.total, one_mul]

/-- Scalar linearity of the finite expectation. -/
theorem mean_mul_const (P : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    P.mean (fun ω => f ω * c) = P.mean f * c := by
  simp [FiniteLaw.mean, ← mul_assoc, Finset.sum_mul]

/-- Scalar linearity with the constant on the left. -/
theorem mean_const_mul (P : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    P.mean (fun ω => c*f ω) = c*P.mean f := by
  simpa only [mul_comm c] using mean_mul_const P f c

/-- Division by a constant commutes with finite expectation. -/
theorem mean_div_const (P : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    P.mean (fun ω => f ω/c) = P.mean f/c := by
  simp only [div_eq_mul_inv, mean_mul_const]

/-- Subtractive linearity of finite expectation. -/
theorem mean_sub (P : FiniteLaw Ω) (f g : Ω → ℝ) :
    P.mean (fun ω => f ω - g ω) = P.mean f - P.mean g := by
  simp [FiniteLaw.mean, mul_sub, Finset.sum_sub_distrib]

/-- Changing a variable only at zero-mass atoms does not change its mean. -/
theorem mean_congr_support (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (h : ∀ ω, 0 < P.mass ω → f ω = g ω) : P.mean f = P.mean g := by
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hp : P.mass ω = 0
  · simp [hp]
  · have hp' : 0 < P.mass ω := lt_of_le_of_ne (P.nonneg ω) (Ne.symm hp)
    rw [h ω hp']

/-- Conditional expectation respects almost sure equality within its event. -/
theorem ce_congr_support (P : FiniteLaw Ω) (f g : Ω → ℝ) (D : Ω → Prop)
    [DecidablePred D]
    (h : ∀ ω, 0 < P.mass ω → D ω → f ω = g ω) : P.ce f D = P.ce g D := by
  unfold FiniteLaw.ce
  congr 1
  apply mean_congr_support
  intro ω hp
  by_cases hD : D ω
  · simp [hD, h ω hp hD]
  · simp [hD]

/-- Conditional linearity on any event, for the corrected population steps. -/
theorem ce_add (P : FiniteLaw Ω) (f g : Ω → ℝ) (D : Ω → Prop) [DecidablePred D] :
    P.ce (fun ω => f ω + g ω) D = P.ce f D + P.ce g D := by
  unfold FiniteLaw.ce
  have h : (fun ω => if D ω then f ω + g ω else 0) =
      (fun ω => (if D ω then f ω else 0) + (if D ω then g ω else 0)) := by
    funext ω; split_ifs <;> simp
  rw [h, mean_add, add_div]

/-- Scalar conditional linearity. -/
theorem ce_mul_const (P : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) (D : Ω → Prop) [DecidablePred D] :
    P.ce (fun ω => f ω * c) D = P.ce f D * c := by
  unfold FiniteLaw.ce
  have h : (fun ω => if D ω then f ω * c else 0) =
      (fun ω => (if D ω then f ω else 0) * c) := by
    funext ω; split_ifs <;> simp
  rw [h, mean_mul_const]; ring

/-- Expectation of a constant conditional on a positive-probability event. -/
theorem ce_const (P : FiniteLaw Ω) (c : ℝ) (D : Ω → Prop) [DecidablePred D] (hD : P.prob D ≠ 0) :
    P.ce (fun _ => c) D = c := by
  have h : (fun ω => if D ω then c else 0) =
      (fun ω => (if D ω then (1 : ℝ) else 0) * c) := by
    funext ω; split_ifs <;> simp
  rw [FiniteLaw.ce, h, mean_mul_const]
  change (P.prob D * c) / P.prob D = c
  field_simp

/-- Exact central moments inside a cell: its centered residual has
unconditional mean zero, and its squared residual has mean P(D)Var(f|D).
These are the finite lemmas behind the influence-function calculation. -/
theorem masked_central_moments (P : FiniteLaw Ω) (f : Ω → ℝ) (D : Ω → Prop)
    [DecidablePred D] (hD : P.prob D ≠ 0) :
    P.mean (fun ω => if D ω then f ω-P.ce f D else 0) = 0 ∧
    P.mean (fun ω => if D ω then (f ω-P.ce f D)^2 else 0) = P.prob D * P.cv f D := by
  have he1 : (fun ω => if D ω then f ω-P.ce f D else 0) =
      (fun ω => (if D ω then f ω else 0) - (if D ω then (1 : ℝ) else 0)*P.ce f D) := by
    funext ω; by_cases h : D ω <;> simp [h]
  have he2 : (fun ω => if D ω then (f ω-P.ce f D)^2 else 0) =
      (fun ω => (if D ω then f ω^2 else 0) -
        (if D ω then f ω else 0)*(2*P.ce f D) +
        (if D ω then (1 : ℝ) else 0)*(P.ce f D)^2) := by
    funext ω; by_cases h : D ω <;> simp [h] <;> ring
  constructor
  · rw [he1, mean_sub, mean_mul_const]
    change P.mean (fun ω => if D ω then f ω else 0) - P.prob D * P.ce f D = 0
    unfold FiniteLaw.ce
    field_simp <;> ring
  · rw [he2, mean_add, mean_sub, mean_mul_const, mean_mul_const]
    change P.mean (fun ω => if D ω then f ω^2 else 0) -
      P.mean (fun ω => if D ω then f ω else 0)*(2*P.ce f D) +
      P.prob D*(P.ce f D)^2 = P.prob D * P.cv f D
    unfold FiniteLaw.cv FiniteLaw.ce
    field_simp <;> ring

/-- Exact second central moment of a binary answer Y, Section 2 and
the finite variance calculations underlying equation (3). -/
theorem binary_centered_moment (P : FiniteLaw Ω) (Y : Ω → Bool) :
    let r := P.prob (fun ω => Y ω = true)
    P.mean (fun ω => (bitVal (Y ω)-r)^2) = r*(1-r) := by
  dsimp only
  let r := P.prob (fun ω => Y ω = true)
  have he : (fun ω => (bitVal (Y ω)-r)^2) =
      (fun ω => bitVal (Y ω)*(1-2*r)+r^2) := by
    funext ω; cases h : Y ω <;> simp [h, bitVal] <;> ring
  change P.mean (fun ω => (bitVal (Y ω)-r)^2) = r*(1-r)
  rw [he, mean_add, mean_mul_const, mean_const]
  change r*(1-2*r)+r^2 = r*(1-r)
  ring

/-- For a Boolean indicator, the mean equals its affirmative probability. -/
theorem mean_bit (P : FiniteLaw Ω) (Y : Ω → Bool) :
    P.mean (fun ω => bitVal (Y ω)) = P.prob (fun ω => Y ω = true) := by
  unfold FiniteLaw.prob
  congr 1

/-- Finite probabilities are monotone under inclusion, allowing changes
on zero-mass atoms. Used to extract regularity from Assumption 4. -/
theorem probability_mono (P : FiniteLaw Ω) (A B : Ω → Prop)
    [DecidablePred A] [DecidablePred B]
    (h : ∀ ω, 0 < P.mass ω → A ω → B ω) : P.prob A ≤ P.prob B := by
  unfold FiniteLaw.prob FiniteLaw.mean
  apply Finset.sum_le_sum
  intro ω _
  by_cases ha : A ω
  · by_cases hb : B ω
    · simp [ha, hb]
    · have hp : P.mass ω = 0 := by
        have hn : ¬ 0 < P.mass ω := by intro hp; exact hb (h ω hp ha)
        exact le_antisymm (le_of_not_gt hn) (P.nonneg ω)
      simp [hp]
  · by_cases hb : B ω
    · simpa [ha, hb] using P.nonneg ω
    · simp [ha, hb]

/-- Assumption 4 makes both treatment arms and both direct-answer
strata positive, in addition to the explicitly defined conditioning cells. -/
theorem regularity_probabilities (S : Study Ω) (h4 : S.nondegenerate) :
    (∀ z : Bool, 0 < S.law.prob (fun ω => S.Z ω = z)) ∧
    (∀ y : Bool, 0 < S.law.prob (fun ω => S.Y ω = y)) := by
  constructor
  · intro z
    exact lt_of_lt_of_le (h4.1 z false).1
      (probability_mono S.law (S.cell z false) (fun ω => S.Z ω = z)
        (fun _ _ h => h.1))
  · intro y
    exact lt_of_lt_of_le (h4.1 false y).1
      (probability_mono S.law (S.cell false y) (fun ω => S.Y ω = y)
        (fun _ _ h => h.2))

/-- Binary negative probability is one minus affirmative probability. -/
theorem prob_false (P : FiniteLaw Ω) (Y : Ω → Bool) :
    P.prob (fun ω => Y ω = false) = 1 - P.prob (fun ω => Y ω = true) := by
  have h : (fun ω => if Y ω = false then (1 : ℝ) else 0) =
      (fun ω => 1 - bitVal (Y ω)) := by
    funext ω; cases hY : Y ω <;> simp [bitVal, hY]
  rw [FiniteLaw.prob, h, mean_sub, mean_const, mean_bit]

/-- The direct affirmative response probability is μp under monotonicity,
the response law in Section 2, p. 46. -/
theorem direct_response_probability (S : Study Ω) (h1 : S.monotone)
    (h4 : S.nondegenerate) :
    S.law.prob (fun ω => S.Y ω = true) = S.mu*S.truthRate := by
  have hx : 0 < S.mu := lt_of_lt_of_le ((regularity_probabilities S h4).2 true)
    (probability_mono S.law (fun ω => S.Y ω = true) (fun ω => S.X ω = true) h1)
  have he : S.law.mean (fun ω => if S.X ω = true then bitVal (S.Y ω) else 0) =
      S.law.mean (fun ω => bitVal (S.Y ω)) := by
    apply mean_congr_support
    intro ω hp
    by_cases hy : S.Y ω = true
    · simp [h1 ω hp hy]
    · have hyf : S.Y ω = false := Bool.eq_false_iff.mpr hy
      simp [hyf, bitVal]
  unfold Study.truthRate FiniteLaw.ce
  rw [he, mean_bit]
  change S.law.prob (fun ω => S.Y ω = true) =
    S.mu * (S.law.prob (fun ω => S.Y ω = true)/S.mu)
  field_simp [ne_of_gt hx]

/-- Treatment independence factors the probability of a (Z,Y) cell. -/
theorem cell_probability (S : Study Ω) (hi : S.treatmentIndependent) (z y : Bool) :
    S.law.prob (S.cell z y) =
    S.law.prob (fun ω => S.Z ω = z) * S.law.prob (fun ω => S.Y ω = y) := by
  have h := hi (fun _ _ y' => if y' = y then 1 else 0) z
  have he : (fun ω => if S.Z ω = z then
      (if S.Y ω = y then (1 : ℝ) else 0) else 0) =
      (fun ω => if S.cell z y ω then 1 else 0) := by
    funext ω; simp only [Study.cell]; split_ifs <;> simp_all
  simpa only [he, FiniteLaw.prob] using h

/-- Treatment independence removes Z from conditioning on the joint
(Z,Y) cell for every function of (W,X,Y). -/
theorem ce_cell_independent (S : Study Ω) (hi : S.treatmentIndependent)
    (f : ℕ → Bool → Bool → ℝ) (z y : Bool)
    (hcell : S.law.prob (S.cell z y) ≠ 0) :
    S.law.ce (fun ω => f (S.W ω) (S.X ω) (S.Y ω)) (S.cell z y) =
    S.law.ce (fun ω => f (S.W ω) (S.X ω) (S.Y ω)) (fun ω => S.Y ω = y) := by
  have hnum := hi (fun w x y' => if y' = y then f w x y' else 0) z
  have he : (fun ω => if S.Z ω = z then
      (if S.Y ω = y then f (S.W ω) (S.X ω) (S.Y ω) else 0) else 0) =
      (fun ω => if S.cell z y ω then f (S.W ω) (S.X ω) (S.Y ω) else 0) := by
    funext ω; simp only [Study.cell]; split_ifs <;> simp_all
  rw [he] at hnum
  have hprob := cell_probability S hi z y
  have hn : S.law.prob (fun ω => S.Z ω = z) *
      S.law.prob (fun ω => S.Y ω = y) ≠ 0 := by rw [← hprob]; exact hcell
  have hz := (mul_ne_zero_iff.mp hn).1
  have hy := (mul_ne_zero_iff.mp hn).2
  unfold FiniteLaw.ce
  rw [hnum, hprob]
  field_simp

/-- Treatment independence removes arm conditioning for every function of
(W,X,Y), the repaired expansion in equation (2). -/
theorem ce_arm_independent (S : Study Ω) (hi : S.treatmentIndependent)
    (f : ℕ → Bool → Bool → ℝ) (z : Bool)
    (hz : S.law.prob (fun ω => S.Z ω = z) ≠ 0) :
    S.law.ce (fun ω => f (S.W ω) (S.X ω) (S.Y ω)) (fun ω => S.Z ω = z) =
    S.law.mean (fun ω => f (S.W ω) (S.X ω) (S.Y ω)) := by
  rw [FiniteLaw.ce, hi f z]
  field_simp

/-- The list equation gives the conditional list mean as a baseline mean
plus the sensitive indicator in the treated arm. -/
theorem list_mean_response (S : Study Ω) (h2 : S.noLiarsDesign) (z y : Bool) :
    S.listMean z y = S.law.ce (fun ω => (S.W ω : ℝ)) (S.cell z y) +
      S.law.ce (fun ω => bitVal (S.X ω)) (S.cell z y) * bitVal z := by
  unfold Study.listMean
  rw [ce_congr_support S.law _
    (fun ω => (S.W ω : ℝ) + bitVal (S.X ω) * bitVal z) (S.cell z y) ?_]
  · rw [ce_add, ce_mul_const]
  · intro ω hp hD; rw [h2 ω hp, hD.1]

/-- Assumptions 2-3 identify each (Z,Y) list mean from the corresponding
Y-stratum baseline and sensitive-indicator means. -/
theorem list_mean_identified (S : Study Ω) (h2 : S.noLiarsDesign)
    (h3 : S.treatmentIndependent) (z y : Bool)
    (hD : S.law.prob (S.cell z y) ≠ 0) :
    S.listMean z y = S.law.ce (fun ω => (S.W ω : ℝ)) (fun ω => S.Y ω = y) +
      S.law.ce (fun ω => bitVal (S.X ω)) (fun ω => S.Y ω = y) * bitVal z := by
  rw [list_mean_response S h2]
  rw [ce_cell_independent S h3 (fun w _ _ => (w : ℝ)) z y hD]
  rw [ce_cell_independent S h3 (fun _ x _ => bitVal x) z y hD]

/-- T11(b): monotonicity and positive probability of Y=1 give E[X | Y=1]=1;
corrected last sentence of the Lemma 1 proof, p. 48. -/
theorem monotone_yes_mean (S : Study Ω) (h1 : S.monotone)
    (hy : S.law.prob (fun ω => S.Y ω = true) ≠ 0) :
    S.law.ce (fun ω => bitVal (S.X ω)) (fun ω => S.Y ω = true) = 1 := by
  rw [ce_congr_support S.law _ (fun _ => 1) _ ?_, ce_const S.law 1 _ hy]
  intro ω hp hyω; simp [h1 ω hp hyω, bitVal]

/-- T8(i): under Assumptions 1-2, β includes the difference in baseline
composition among confessors. No treatment independence is assumed. -/
theorem beta_baseline_decomposition (S : Study Ω) (h1 : S.monotone)
    (h2 : S.noLiarsDesign)
    (h0 : S.law.prob (S.cell false true) ≠ 0)
    (ht : S.law.prob (S.cell true true) ≠ 0) :
    S.beta = 1 + S.law.ce (fun ω => (S.W ω : ℝ)) (S.cell true true) -
      S.law.ce (fun ω => (S.W ω : ℝ)) (S.cell false true) := by
  have hx : S.law.ce (fun ω => bitVal (S.X ω)) (S.cell true true) = 1 := by
    rw [ce_congr_support S.law _ (fun _ => 1) _ ?_, ce_const S.law 1 _ ht]
    intro ω hp hD; simp [h1 ω hp hD.2, bitVal]
  rw [Study.beta, list_mean_response S h2, list_mean_response S h2, hx]
  simp [bitVal]; ring

/-- T12 and T11(e), corrected first sentence of Proposition 3, p. 50:
Assumptions 1-3 and defined confessing cells imply β=1. -/
theorem placebo_one_identity (S : Study Ω) (h1 : S.monotone)
    (h2 : S.noLiarsDesign) (h3 : S.treatmentIndependent)
    (h0 : S.law.prob (S.cell false true) ≠ 0)
    (ht : S.law.prob (S.cell true true) ≠ 0) : S.beta = 1 := by
  rw [beta_baseline_decomposition S h1 h2 h0 ht]
  rw [ce_cell_independent S h3 (fun w _ _ => (w : ℝ)) true true ht]
  rw [ce_cell_independent S h3 (fun w _ _ => (w : ℝ)) false true h0]
  ring

/-- T8(iii): a population β different from one entails failure of at
least one of Assumptions 1-3 (the repaired exhaustive diagnosis). -/
theorem beta_departure_diagnosis (S : Study Ω)
    (h0 : S.law.prob (S.cell false true) ≠ 0)
    (ht : S.law.prob (S.cell true true) ≠ 0) (hβ : S.beta ≠ 1) :
    ¬ S.monotone ∨ ¬ S.noLiarsDesign ∨ ¬ S.treatmentIndependent := by
  by_contra h
  push_neg at h
  exact hβ (placebo_one_identity S h.1 h.2.1 h.2.2 h0 ht)

/-- T6: control V and treated V-1 have the same conditional distribution
among confessors, both equal to W | Y=1. This is the repaired comparison
sentence in Section 4.1, p. 50, for every real t. -/
theorem placebo_distribution_corrected (S : Study Ω) (h1 : S.monotone)
    (h2 : S.noLiarsDesign) (h3 : S.treatmentIndependent)
    (h0 : S.law.prob (S.cell false true) ≠ 0)
    (ht : S.law.prob (S.cell true true) ≠ 0) (t : ℝ) :
    S.law.ce (fun ω => if (S.V ω : ℝ) = t then 1 else 0) (S.cell false true) =
      S.law.ce (fun ω => if (S.W ω : ℝ) = t then 1 else 0) (fun ω => S.Y ω = true) ∧
    S.law.ce (fun ω => if (S.V ω : ℝ) - 1 = t then 1 else 0) (S.cell true true) =
      S.law.ce (fun ω => if (S.W ω : ℝ) = t then 1 else 0) (fun ω => S.Y ω = true) := by
  constructor
  · rw [ce_congr_support S.law _ (fun ω => if (S.W ω : ℝ) = t then 1 else 0) _ ?_]
    · exact ce_cell_independent S h3 (fun w _ _ => if (w : ℝ) = t then 1 else 0) false true h0
    · intro ω hp hD; simp [h2 ω hp, hD.1, bitVal]
  · rw [ce_congr_support S.law _ (fun ω => if (S.W ω : ℝ) = t then 1 else 0) _ ?_]
    · exact ce_cell_independent S h3 (fun w _ _ => if (w : ℝ) = t then 1 else 0) true true ht
    · intro ω hp hD; simp [h2 ω hp, hD.1, h1 ω hp hD.2, bitVal]

/-- T11(a): repaired equation (2), p. 48. Under Assumptions 2-3, the
treated population mean is E[W]+μ and the control mean is E[W]. -/
theorem list_arm_expansion (S : Study Ω) (h2 : S.noLiarsDesign)
    (h3 : S.treatmentIndependent)
    (h0 : S.law.prob (fun ω => S.Z ω = false) ≠ 0)
    (ht : S.law.prob (fun ω => S.Z ω = true) ≠ 0) :
    S.law.ce (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = true) =
      S.law.mean (fun ω => (S.W ω : ℝ)) + S.mu ∧
    S.law.ce (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = false) =
      S.law.mean (fun ω => (S.W ω : ℝ)) := by
  have hv (z : Bool) (hz : S.law.prob (fun ω => S.Z ω = z) ≠ 0) :
      S.law.ce (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = z) =
      S.law.mean (fun ω => (S.W ω : ℝ)) + S.mu * bitVal z := by
    rw [ce_congr_support S.law _
      (fun ω => (S.W ω : ℝ) + bitVal (S.X ω) * bitVal z) _ ?_]
    · rw [ce_add, ce_mul_const,
        ce_arm_independent S h3 (fun w _ _ => (w : ℝ)) z hz,
        ce_arm_independent S h3 (fun _ x _ => bitVal x) z hz,
        mean_bit]
      rfl
    · intro ω hp hzω; rw [h2 ω hp, hzω]
  constructor <;> simp [hv, ht, h0, bitVal]

/-- T17, underlying exact identity including false confessions: the
combined functional equals μ + Pr[X=0,Y=1], under Assumptions 2-3.
It yields Lemma 1 and its strict remark, pp. 47-48. -/
theorem combined_excess (S : Study Ω) (h2 : S.noLiarsDesign)
    (h3 : S.treatmentIndependent)
    (h0 : S.law.prob (S.cell false false) ≠ 0)
    (ht : S.law.prob (S.cell true false) ≠ 0) :
    S.combined = S.mu + S.law.prob (fun ω => S.X ω = false ∧ S.Y ω = true) := by
  have hy : S.law.prob (fun ω => S.Y ω = false) ≠ 0 := by
    have h := cell_probability S h3 false false
    exact (mul_ne_zero_iff.mp (h ▸ h0)).2
  have hdiff : S.listMean true false - S.listMean false false =
      S.law.ce (fun ω => bitVal (S.X ω)) (fun ω => S.Y ω = false) := by
    rw [list_mean_identified S h2 h3 true false ht,
      list_mean_identified S h2 h3 false false h0]
    simp [bitVal]
  have hm : S.law.mean (fun ω => 1 - bitVal (S.Y ω)) =
      S.law.prob (fun ω => S.Y ω = false) := by
    rw [mean_sub, mean_const, mean_bit, prob_false]
  have hpoint : (fun ω => bitVal (S.Y ω) +
      (if S.Y ω = false then bitVal (S.X ω) else 0)) =
      (fun ω => bitVal (S.X ω) +
        (if S.X ω = false ∧ S.Y ω = true then 1 else 0)) := by
    funext ω; cases hx : S.X ω <;> cases hy : S.Y ω <;> simp [bitVal, hx, hy]
  have he := congrArg S.law.mean hpoint
  rw [mean_add, mean_add, mean_bit] at he
  rw [Study.combined, hdiff, hm, FiniteLaw.ce]
  have hcancel : S.law.prob (fun ω => S.Y ω = false) *
      (S.law.mean (fun ω => if S.Y ω = false then bitVal (S.X ω) else 0) /
        S.law.prob (fun ω => S.Y ω = false)) =
      S.law.mean (fun ω => if S.Y ω = false then bitVal (S.X ω) else 0) := by
    field_simp
  rw [hcancel]
  simpa only [Study.mu, FiniteLaw.prob, mean_bit] using he

/-- T17: Lemma 1, equation (1), with all four printed standing
assumptions: the combined functional identifies sensitive prevalence. -/
theorem prevalence_identity (S : Study Ω) (h : S.standing) : S.mu = S.combined := by
  have hzero : S.law.prob (fun ω => S.X ω = false ∧ S.Y ω = true) = 0 := by
    unfold FiniteLaw.prob
    rw [mean_congr_support S.law _ (fun _ => 0) ?_, mean_const]
    intro ω hp
    have h1 := h.1 ω hp
    split_ifs with he
    · have := h1 he.2; simp_all
    · rfl
  rw [combined_excess S h.2.1 h.2.2.1
    (ne_of_gt (h.2.2.2.1 false false).1)
    (ne_of_gt (h.2.2.2.1 true false).1), hzero, add_zero]

/-- T17: the remark after Lemma 1 is strict when false confessions have
positive probability, under Assumptions 2-4. The excess is their mass. -/
theorem false_confessions_strict (S : Study Ω) (h2 : S.noLiarsDesign)
    (h3 : S.treatmentIndependent) (h4 : S.nondegenerate)
    (hf : 0 < S.law.prob (fun ω => S.X ω = false ∧ S.Y ω = true)) :
    S.mu < S.combined := by
  rw [combined_excess S h2 h3 (ne_of_gt (h4.1 false false).1)
    (ne_of_gt (h4.1 true false).1)]
  linarith

/-- T22, exact first sentence of Proposition 4: Treatment Independence
and positive arm probabilities imply the placebo-II population δ=0. -/
theorem placebo_two_identity (S : Study Ω) (h3 : S.treatmentIndependent)
    (h0 : S.law.prob (fun ω => S.Z ω = false) ≠ 0)
    (ht : S.law.prob (fun ω => S.Z ω = true) ≠ 0) : S.delta = 0 := by
  rw [Study.delta, ce_arm_independent S h3 (fun _ _ y => bitVal y) true ht,
    ce_arm_independent S h3 (fun _ _ y => bitVal y) false h0, sub_self]

/-- Uniform finite latent bits in explicit counterexamples. -/
def uniformFin (n : ℕ) (hn : 0 < n) : FiniteLaw (Fin n) where
  mass := fun _ => 1 / (n : ℝ)
  nonneg := by intro; positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp

/-- Binomial(4,2/5) baseline of Appendix C, supplement p. 2; the exact
probabilities are choose(4,w)(2/5)^w(3/5)^(4-w). -/
def ceilingBaseline : FiniteLaw (Fin 5) where
  mass := ![81/625, 216/625, 216/625, 96/625, 16/625]
  nonneg := by intro w; fin_cases w <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- T1-T2: the five exact baseline masses really are Binomial(4,2/5),
with mean 8/5 and variance 24/25, supplement Appendix C, p. 2. -/
theorem binomial_baseline_exact :
    (∀ w : Fin 5, ceilingBaseline.mass w =
      (Nat.choose 4 w.val : ℝ)*(2/5)^w.val*(3/5)^(4-w.val)) ∧
    ceilingBaseline.mean (fun w => (w.val : ℝ)) = 8/5 ∧
    ceilingBaseline.variance (fun w => (w.val : ℝ)) = 24/25 := by
  constructor
  · intro w; fin_cases w <;> norm_num [ceilingBaseline, Nat.choose]
  · norm_num [ceilingBaseline, FiniteLaw.mean, FiniteLaw.variance, Fin.sum_univ_succ]

/-- Printed affected response: "the control list plus one ... those units'
treatment list response remained equal to 4", Appendix C, supplement p. 2. -/
def printedAffected (w : Fin 5) : ℝ := (min (w.val + 1) 4 : ℕ)

/-- Corrected response: the coded capped NONSENSITIVE increment, followed
by the sensitive item. Appendix C correction, target T2. -/
def codedAffected (w : Fin 5) : ℝ := printedAffected w + 1

/-- Unaffected truthful admitter response W+1, Appendix C, supplement p. 2. -/
def unaffected (w : Fin 5) : ℝ := (w.val : ℝ) + 1

/-- Population β under independent affected status with probability ρ,
independent treatment, no false confessors and no liars, Appendix C. The
mixture is the exact marginal treatment mean minus the control mean. -/
def ceilingBeta (affectedResponse : Fin 5 → ℝ) (ρ : ℝ) : ℝ :=
  ceilingBaseline.mean (fun w => (1 - ρ) * unaffected w + ρ * affectedResponse w) -
    ceilingBaseline.mean (fun w => (w.val : ℝ))

/-- T1: the printed and coded responses differ at W=0 and W=4, and their
contrasts at ρ=1/5 are 3109/3125 and 3734/3125. This refutes agreement of
the printed mechanism with the implementation, not an exact power claim. -/
theorem ceiling_counterexample :
    printedAffected 0 = 1 ∧ codedAffected 0 = 2 ∧
    printedAffected 4 = 4 ∧ codedAffected 4 = 5 ∧
    ceilingBeta printedAffected (1/5) = 3109/3125 ∧
    ceilingBeta codedAffected (1/5) = 3734/3125 ∧
    ceilingBeta codedAffected (1/5) - ceilingBeta printedAffected (1/5) = 1/5 := by
  norm_num [ceilingBeta, FiniteLaw.mean, ceilingBaseline, printedAffected,
    codedAffected, unaffected, Fin.sum_univ_succ]

/-- T2: the corrected coded effect increases the total by two below the
ceiling and by one at the ceiling; β=1+(609/625)ρ, strictly above 1 if ρ>0.
The comparison to the printed rule has gap exactly ρ. -/
theorem ceiling_corrected (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∀ w : Fin 5, codedAffected w = if w.val < 4 then (w.val : ℝ) + 2 else 5) ∧
    ceilingBeta codedAffected ρ = 1 + (609/625) * ρ ∧
    ceilingBeta printedAffected ρ = 1 - (16/625) * ρ ∧
    ceilingBeta codedAffected ρ - ceilingBeta printedAffected ρ = ρ ∧
    (0 < ρ → 1 < ceilingBeta codedAffected ρ) := by
  have hp : ceilingBeta printedAffected ρ = 1 - (16/625) * ρ := by
    norm_num [ceilingBeta, FiniteLaw.mean, ceilingBaseline, printedAffected,
      unaffected, Fin.sum_univ_succ]
    <;> ring
  have hc : ceilingBeta codedAffected ρ = 1 + (609/625) * ρ := by
    norm_num [ceilingBeta, FiniteLaw.mean, ceilingBaseline, printedAffected,
      codedAffected, unaffected, Fin.sum_univ_succ]
    <;> ring
  refine ⟨?_, hc, hp, ?_, ?_⟩
  · intro w; fin_cases w <;> norm_num [codedAffected, printedAffected]
  · rw [hc, hp]; ring
  · intro h; rw [hc]; linarith

/-- T2 and T16: the subject-level response increments including affected
status. Corrected V(1)-W is 1+1{affected}1{W<4}; the printed rule gives
1-1{affected}1{W=4}. Appendix C correction and comparison. -/
theorem ceiling_response_increments (w : Fin 5) (affected : Bool) :
    (if affected then codedAffected w else unaffected w)-(w.val : ℝ) =
      1 + (if affected = true ∧ w.val < 4 then 1 else 0) ∧
    (if affected then printedAffected w else unaffected w)-(w.val : ℝ) =
      1 - (if affected = true ∧ w.val = 4 then 1 else 0) := by
  cases affected <;> fin_cases w <;> norm_num [codedAffected, printedAffected, unaffected]

/-- T16, exact mathematical content of the PRINTED mechanism:
β=1-(16/625)ρ. The reported "80% power" is empirical Monte Carlo output
and has no exact counterpart in this theorem. -/
theorem ceiling_as_printed (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ceilingBeta printedAffected ρ = 1 - (16/625) * ρ :=
  (ceiling_corrected ρ hρ0 hρ1).2.2.1

/-- Bit k of a uniform finite index. In Fin(2^r), these r bits are
independent fair Bernoulli variables, used only in concrete witnesses. -/
def fairBit {n : ℕ} (ω : Fin n) (k : ℕ) : Bool := decide ((ω.val / 2^k) % 2 = 1)

/-- T3 counterexample population: X,C,W,Z are four independent fair bits,
Y=XC and V=W+XZ. Finding P019-E003; article pp. 46-47. -/
def finiteSampleWitness : Study (Fin 16) where
  law := uniformFin 16 (by norm_num)
  W := fun ω => if fairBit ω 2 then 1 else 0
  X := fun ω => fairBit ω 0
  Y := fun ω => fairBit ω 0 && fairBit ω 1
  Z := fun ω => fairBit ω 3
  V := fun ω => (if fairBit ω 2 then 1 else 0) +
    (if fairBit ω 0 && fairBit ω 3 then 1 else 0)

/-- Every printed standing assumption holds for the T3 population, including
all four positive conditional variances and treatment independence. -/
theorem finite_sample_witness_valid : finiteSampleWitness.standing := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω _; fin_cases ω <;> norm_num [finiteSampleWitness, fairBit]
  · intro ω _; fin_cases ω <;> norm_num [finiteSampleWitness, fairBit, bitVal]
  · intro f z
    cases z <;> norm_num [finiteSampleWitness, fairBit, uniformFin,
      FiniteLaw.mean, FiniteLaw.prob, Fin.sum_univ_succ] <;> ring
  · refine ⟨?_, ?_, ?_⟩
    · intro z y; cases z <;> cases y <;>
        norm_num [finiteSampleWitness, fairBit, uniformFin, Study.cell,
          FiniteLaw.cv, FiniteLaw.ce, FiniteLaw.mean, FiniteLaw.prob,
          Fin.sum_univ_succ]
    · norm_num [FiniteLaw.variance, FiniteLaw.mean, finiteSampleWitness,
        uniformFin, fairBit, bitVal, Fin.sum_univ_succ]
    · norm_num [FiniteLaw.variance, FiniteLaw.mean, finiteSampleWitness,
        uniformFin, fairBit, bitVal, Fin.sum_univ_succ]

/-- The n=1 cell mean with value zero on the empty cell, the explicit
bounded completion in T3 (finding P019-E003). -/
def singletonMean (S : Study Ω) (z y : Bool) (ω : Ω) : ℝ :=
  if S.cell z y ω then (S.V ω : ℝ) else 0

/-- T3(i): all four assumptions hold, but each empty-cell event has
probability 5/8 at n=1. Under the zero completion the covariances are
5/64 and 3/64, both nonzero, contradicting unconditional Lemma 2. -/
theorem lemma_two_counterexample :
    finiteSampleWitness.standing ∧
    finiteSampleWitness.law.prob (fun ω => ¬ finiteSampleWitness.cell true false ω) = 5/8 ∧
    finiteSampleWitness.law.prob (fun ω => ¬ finiteSampleWitness.cell false false ω) = 5/8 ∧
    finiteSampleWitness.law.cov (fun ω => 1 - bitVal (finiteSampleWitness.Y ω))
      (singletonMean finiteSampleWitness true false) = 5/64 ∧
    finiteSampleWitness.law.cov (fun ω => 1 - bitVal (finiteSampleWitness.Y ω))
      (singletonMean finiteSampleWitness false false) = 3/64 := by
  refine ⟨finite_sample_witness_valid, ?_⟩
  norm_num [FiniteLaw.cov, FiniteLaw.mean, FiniteLaw.prob, singletonMean,
    Study.cell, finiteSampleWitness, uniformFin, fairBit, bitVal, Fin.sum_univ_succ]

/-- T3(ii): the sums in (6)-(7) omit the probability of an empty treated
cell. At γ=1/2, k=0,1,2,4 their correct values are 0,1/2,3/4,15/16. -/
theorem omitted_binomial_mass :
    1 - (1 - (1/2 : ℝ))^0 = 0 ∧
    1 - (1 - (1/2 : ℝ))^1 = 1/2 ∧
    1 - (1 - (1/2 : ℝ))^2 = 3/4 ∧
    1 - (1 - (1/2 : ℝ))^4 = 15/16 := by norm_num

/-- T3(ii), actual n=1 conditional probabilities: given one negative
direct answer, the treated count is positive with probability 1/2, not
one. The conditional zero-completed mean is 5/12, not the population
treated-negative mean 5/6 in the last equality of display (6), p. 62. -/
theorem conditional_count_counterexample :
    finiteSampleWitness.standing ∧
    finiteSampleWitness.law.ce (fun ω => if finiteSampleWitness.Z ω = true then 1 else 0)
      (fun ω => finiteSampleWitness.Y ω = false) = 1/2 ∧
    finiteSampleWitness.law.ce (singletonMean finiteSampleWitness true false)
      (fun ω => finiteSampleWitness.Y ω = false) = 5/12 ∧
    finiteSampleWitness.listMean true false = 5/6 := by
  refine ⟨finite_sample_witness_valid, ?_⟩
  norm_num [finiteSampleWitness, uniformFin, fairBit, singletonMean, Study.listMean,
    Study.cell, FiniteLaw.ce, FiniteLaw.prob, FiniteLaw.mean, Fin.sum_univ_succ]

/-- T5 counterexample population: X=Y, W, and Z are independent fair
bits. The eight atoms have mass 1/8. Article Section 4.1, p. 50. -/
def distributionWitness : Study (Fin 8) where
  law := uniformFin 8 (by norm_num)
  W := fun ω => if fairBit ω 1 then 1 else 0
  X := fun ω => fairBit ω 0
  Y := fun ω => fairBit ω 0
  Z := fun ω => fairBit ω 2
  V := fun ω => (if fairBit ω 1 then 1 else 0) +
    (if fairBit ω 0 && fairBit ω 2 then 1 else 0)

/-- The T5 population satisfies every assumption of the sentence whose
distributional comparison has the wrong sign. -/
theorem distribution_witness_valid : distributionWitness.standing := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω _; exact fun h => h
  · intro ω _; fin_cases ω <;> norm_num [distributionWitness, fairBit, bitVal]
  · intro f z
    cases z <;> norm_num [distributionWitness, fairBit, uniformFin,
      FiniteLaw.mean, FiniteLaw.prob, Fin.sum_univ_succ] <;> ring
  · refine ⟨?_, ?_, ?_⟩
    · intro z y; cases z <;> cases y <;>
        norm_num [distributionWitness, fairBit, uniformFin, Study.cell,
          FiniteLaw.cv, FiniteLaw.ce, FiniteLaw.mean, FiniteLaw.prob, Fin.sum_univ_succ]
    · norm_num [FiniteLaw.variance, FiniteLaw.mean, distributionWitness,
        uniformFin, fairBit, bitVal, Fin.sum_univ_succ]
    · norm_num [FiniteLaw.variance, FiniteLaw.mean, distributionWitness,
        uniformFin, fairBit, bitVal, Fin.sum_univ_succ]

/-- T5: under all four assumptions control V has probability 1/2 at zero,
whereas treated V+1 has probability zero there. Treated V-1 has probability
1/2. This is a counterexample only to the printed comparison sentence. -/
theorem distribution_sign_counterexample :
    distributionWitness.standing ∧
    distributionWitness.law.ce (fun ω => if (distributionWitness.V ω : ℝ) = 0 then 1 else 0)
      (distributionWitness.cell false true) = 1/2 ∧
    distributionWitness.law.ce (fun ω => if (distributionWitness.V ω : ℝ) + 1 = 0 then 1 else 0)
      (distributionWitness.cell true true) = 0 ∧
    distributionWitness.law.ce (fun ω => if (distributionWitness.V ω : ℝ) - 1 = 0 then 1 else 0)
      (distributionWitness.cell true true) = 1/2 := by
  refine ⟨distribution_witness_valid, ?_⟩
  norm_num [distributionWitness, fairBit, uniformFin, Study.cell,
    FiniteLaw.ce, FiniteLaw.mean, FiniteLaw.prob, Fin.sum_univ_succ]

/-- T7's interior-prevalence population: B,C,X,Z are independent fair bits;
W=B+C, Y=X·1{C=Z}, V=W+XZ. Finding P019-N006; supplement Appendix C. -/
def diagnosisWitness : Study (Fin 16) where
  law := uniformFin 16 (by norm_num)
  W := fun ω => (if fairBit ω 0 then 1 else 0) + (if fairBit ω 1 then 1 else 0)
  X := fun ω => fairBit ω 2
  Y := fun ω => fairBit ω 2 && decide (fairBit ω 1 = fairBit ω 3)
  Z := fun ω => fairBit ω 3
  V := fun ω => (if fairBit ω 0 then 1 else 0) + (if fairBit ω 1 then 1 else 0) +
    (if fairBit ω 2 && fairBit ω 3 then 1 else 0)

/-- T7: no false confession and no list lying/design effect, positive
variances, δ=0, but β=2 and joint Treatment Independence fails. This
refutes the supplement's assertion that only the first two failures can
explain a population departure from one. -/
theorem diagnosis_counterexample :
    diagnosisWitness.monotone ∧ diagnosisWitness.noLiarsDesign ∧
    diagnosisWitness.nondegenerate ∧ diagnosisWitness.delta = 0 ∧
    diagnosisWitness.beta = 2 ∧ ¬ diagnosisWitness.treatmentIndependent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω _; fin_cases ω <;> norm_num [diagnosisWitness, fairBit]
  · intro ω _; fin_cases ω <;> norm_num [diagnosisWitness, fairBit, bitVal]
  · refine ⟨?_, ?_, ?_⟩
    · intro z y; cases z <;> cases y <;>
        norm_num [diagnosisWitness, fairBit, uniformFin, Study.cell,
          FiniteLaw.cv, FiniteLaw.ce, FiniteLaw.mean, FiniteLaw.prob, Fin.sum_univ_succ]
    · norm_num [FiniteLaw.variance, FiniteLaw.mean, diagnosisWitness,
        uniformFin, fairBit, bitVal, Fin.sum_univ_succ]
    · norm_num [FiniteLaw.variance, FiniteLaw.mean, diagnosisWitness,
        uniformFin, fairBit, bitVal, Fin.sum_univ_succ]
  · norm_num [Study.delta, diagnosisWitness, fairBit, uniformFin, bitVal,
      FiniteLaw.ce, FiniteLaw.mean, FiniteLaw.prob, Fin.sum_univ_succ]
  · norm_num [Study.beta, Study.listMean, diagnosisWitness, fairBit, uniformFin,
      Study.cell, FiniteLaw.ce, FiniteLaw.mean, FiniteLaw.prob, Fin.sum_univ_succ]
  · intro hi
    have h := hi (fun w x y => if w = 0 ∧ x = true ∧ y = false then 1 else 0) false
    norm_num [diagnosisWitness, fairBit, uniformFin, FiniteLaw.mean,
      FiniteLaw.prob, Fin.sum_univ_succ] at h

/-- The CNN non-identification pair uses type masses 1/4,1/4,1/2,
independent W∈{1,2} and fair Z. Finding P019-E007; Table A1,
p. 61. There are twelve complete atoms. -/
def cnnLaw : FiniteLaw (Fin 12) where
  mass := fun ω => if ω.val / 4 < 2 then 1/16 else 1/8
  nonneg := by intro ω; split_ifs <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- Observed variables are identical in the two CNN worlds of T13.
Type 0 admits, type 1 has X=1,Y=0, and type 2 has X=Y=0. -/
def cnnWitness : Study (Fin 12) where
  law := cnnLaw
  W := fun ω => 1 + (if fairBit ω 0 then 1 else 0)
  X := fun ω => decide (ω.val / 4 < 2)
  Y := fun ω => decide (ω.val / 4 = 0)
  Z := fun ω => fairBit ω 1
  V := fun ω => 1 + (if fairBit ω 0 then 1 else 0) +
    (if decide (ω.val / 4 < 2) && fairBit ω 1 then 1 else 0)

/-- World A, T13: watching Q equals the truthful direct answer;
World B replaces the reads-only type by a watcher withholding. -/
def cnnWatching (worldB : Bool) (ω : Fin 12) : Bool :=
  decide (ω.val / 4 = 0) || (worldB && decide (ω.val / 4 = 1))

/-- Reading R is present only in World A's reads-only type, T13. -/
def cnnReading (worldB : Bool) (ω : Fin 12) : Bool :=
  !worldB && decide (ω.val / 4 = 1)

/-- The observable CNN population meets Assumptions 1-4 with X meaning
reading OR watching. This does not identify watching. -/
theorem cnn_witness_valid : cnnWitness.standing := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω _; fin_cases ω <;> norm_num [cnnWitness]
  · intro ω _; fin_cases ω <;> norm_num [cnnWitness, fairBit, bitVal]
  · intro f z
    cases z <;> norm_num [cnnWitness, cnnLaw, fairBit, FiniteLaw.mean,
      FiniteLaw.prob, Fin.sum_univ_succ] <;> ring
  · refine ⟨?_, ?_, ?_⟩
    · intro z y; cases z <;> cases y <;>
        norm_num [cnnWitness, cnnLaw, fairBit, Study.cell,
          FiniteLaw.cv, FiniteLaw.ce, FiniteLaw.mean, FiniteLaw.prob, Fin.sum_univ_succ]
    · norm_num [FiniteLaw.variance, FiniteLaw.mean, cnnWitness,
        cnnLaw, fairBit, bitVal, Fin.sum_univ_succ]
    · norm_num [FiniteLaw.variance, FiniteLaw.mean, cnnWitness,
        cnnLaw, fairBit, bitVal, Fin.sum_univ_succ]

/-- T13: the same observable law satisfies all standing assumptions and
has combined estimand 1/2, β=1, δ=0, yet watching prevalence is 1/4 in
World A and 1/2 in World B. World A's answers are all truthful; World B
has mass 1/4 of false negatives. The two worlds use the SAME observable
functions and masses, so their entire joint law of (Z,Y,V) is identical. -/
theorem cnn_nonidentification_counterexample :
    cnnWitness.standing ∧
    (∀ (b : Bool) (ω : Fin 12), cnnWitness.X ω = (cnnReading b ω || cnnWatching b ω)) ∧
    cnnWitness.law.prob (fun ω => cnnWatching false ω = true) = 1/4 ∧
    cnnWitness.law.prob (fun ω => cnnWatching true ω = true) = 1/2 ∧
    cnnWitness.law.prob (fun ω => cnnWitness.Y ω ≠ cnnWatching false ω) = 0 ∧
    cnnWitness.law.prob (fun ω => cnnWitness.Y ω ≠ cnnWatching true ω) = 1/4 ∧
    cnnWitness.combined = 1/2 ∧ cnnWitness.mu = 1/2 ∧
    cnnWitness.beta = 1 ∧ cnnWitness.delta = 0 := by
  refine ⟨cnn_witness_valid, ?_, ?_⟩
  · intro b ω; cases b <;> fin_cases ω <;> norm_num [cnnWitness, cnnReading, cnnWatching]
  · norm_num [cnnWitness, cnnLaw, fairBit, cnnWatching, bitVal,
      Study.combined, Study.mu, Study.beta, Study.delta, Study.listMean, Study.cell,
      FiniteLaw.mean, FiniteLaw.prob, FiniteLaw.ce, Fin.sum_univ_succ]

/-- The original CNN correction requires joint independence of (W,R,Q)
and Z, not just balanced direct answers. The same all-functions
factorization expresses this finite distributional hypothesis. -/
def tripleIndependent (P : FiniteLaw Ω) (W : Ω → ℕ) (R Q Z : Ω → Bool) : Prop :=
  ∀ (f : ℕ → Bool → Bool → ℝ) (z : Bool),
    P.mean (fun ω => if Z ω = z then f (W ω) (R ω) (Q ω) else 0) =
      P.prob (fun ω => Z ω = z) * P.mean (fun ω => f (W ω) (R ω) (Q ω))

/-- T14, full corrected CNN reading: with truthful questions as worded,
the list/combined functional is b+a = Pr(read OR watch); its excess over
watching is exactly reader-only mass a, and both placebo restrictions
still hold. Table A1, p. 61, and the P019-E007 correction. -/
theorem cnn_interpretation (S : Study Ω) (R Q : Ω → Bool)
    (hY : ∀ ω, S.Y ω = Q ω) (hX : ∀ ω, S.X ω = (R ω || Q ω))
    (h2 : S.noLiarsDesign) (hi : tripleIndependent S.law S.W R Q S.Z)
    (hz0 : S.law.prob (fun ω => S.Z ω = false) ≠ 0)
    (hz1 : S.law.prob (fun ω => S.Z ω = true) ≠ 0)
    (hq0 : S.law.prob (fun ω => Q ω = false) ≠ 0)
    (hq1 : S.law.prob (fun ω => Q ω = true) ≠ 0) :
    let b := S.law.prob (fun ω => Q ω = true)
    let a := S.law.prob (fun ω => R ω = true ∧ Q ω = false)
    S.monotone ∧ S.treatmentIndependent ∧
    S.listMean true false - S.listMean false false = a / (1 - b) ∧
    S.combined = b + a ∧ S.mu = b + a ∧
    S.law.ce (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = true) -
      S.law.ce (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = false) = b + a ∧
    S.combined - b = a ∧ (S.combined = b ↔ a = 0) ∧
    S.beta = 1 ∧ S.delta = 0 := by
  dsimp only
  have h1 : S.monotone := by
    intro ω _ hy
    rw [hY] at hy
    simp [hX, hy]
  have h3 : S.treatmentIndependent := by
    intro f z
    simpa only [hX, hY] using hi (fun w r q => f w (r || q) q) z
  have hy0 : S.law.prob (fun ω => S.Y ω = false) ≠ 0 := by simpa only [hY] using hq0
  have hy1 : S.law.prob (fun ω => S.Y ω = true) ≠ 0 := by simpa only [hY] using hq1
  have hc (z y : Bool) : S.law.prob (S.cell z y) ≠ 0 := by
    rw [cell_probability S h3]
    cases z <;> cases y <;> exact mul_ne_zero (by assumption) (by assumption)
  have hmu : S.mu = S.law.prob (fun ω => Q ω = true) +
      S.law.prob (fun ω => R ω = true ∧ Q ω = false) := by
    rw [Study.mu, ← mean_bit]
    have he : (fun ω => bitVal (S.X ω)) = (fun ω =>
        (if Q ω = true then (1 : ℝ) else 0) +
        (if R ω = true ∧ Q ω = false then (1 : ℝ) else 0)) := by
      funext ω; rw [hX]
      cases hr : R ω <;> cases hq : Q ω <;> simp [bitVal, hr, hq]
    rw [he, mean_add]; rfl
  have hz : S.law.prob (fun ω => S.X ω = false ∧ S.Y ω = true) = 0 := by
    unfold FiniteLaw.prob
    rw [mean_congr_support S.law _ (fun _ => 0) ?_, mean_const]
    intro ω hp
    split_ifs with h
    · have := h1 ω hp h.2; simp_all
    · rfl
  have hcomb : S.combined = S.law.prob (fun ω => Q ω = true) +
      S.law.prob (fun ω => R ω = true ∧ Q ω = false) := by
    rw [combined_excess S h2 h3 (hc false false) (hc true false), hz, add_zero, hmu]
  have hd : S.listMean true false - S.listMean false false =
      S.law.ce (fun ω => bitVal (S.X ω)) (fun ω => S.Y ω = false) := by
    rw [list_mean_identified S h2 h3 true false (hc true false),
      list_mean_identified S h2 h3 false false (hc false false)]
    simp [bitVal]
  have hmask : (fun ω => if S.Y ω = false then bitVal (S.X ω) else 0) =
      (fun ω => if R ω = true ∧ Q ω = false then (1 : ℝ) else 0) := by
    funext ω; rw [hX, hY]
    cases hr : R ω <;> cases hq : Q ω <;> simp [bitVal, hr, hq]
  refine ⟨h1, h3, ?_, hcomb, hmu, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd, FiniteLaw.ce, hmask, prob_false]
    simp only [hY]; rfl
  · have ha := list_arm_expansion S h2 h3 hz0 hz1
    rw [ha.1, ha.2, hmu]; ring
  · rw [hcomb]; ring
  · rw [hcomb]; constructor <;> intro h <;> linarith
  · exact placebo_one_identity S h1 h2 h3 (hc false true) (hc true true)
  · exact placebo_two_identity S h3 hz0 hz1

/-- Independent identically distributed samples of n subjects, Section 2,
p. 46. Each ordered sample s has mass ∏_i p(s_i), with no conditioning
away empty groups. -/
def FiniteLaw.iid (P : FiniteLaw Ω) (n : ℕ) : FiniteLaw (Fin n → Ω) where
  mass := fun s => ∏ i, P.mass (s i)
  nonneg := by intro s; exact Finset.prod_nonneg (fun i _ => P.nonneg (s i))
  total := by
    rw [← Fintype.prod_sum]
    simp [P.total]

/-- Exact expectation factorization under independent sampling, the
finite foundation of the sample-moment calculations in Appendix B. -/
theorem iid_mean_prod (P : FiniteLaw Ω) (n : ℕ) (f : Fin n → Ω → ℝ) :
    (P.iid n).mean (fun s => ∏ i, f i (s i)) = ∏ i, P.mean (f i) := by
  unfold FiniteLaw.mean FiniteLaw.iid
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i ω => P.mass ω * f i ω)).symm

/-- Each sampled coordinate has exactly the original population mean. -/
theorem iid_mean_coordinate (P : FiniteLaw Ω) (n : ℕ) (i : Fin n) (f : Ω → ℝ) :
    (P.iid n).mean (fun s => f (s i)) = P.mean f := by
  have he : (fun s : Fin n → Ω => f (s i)) =
      (fun s => ∏ j, if j = i then f (s j) else 1) := by
    funext s; exact (Fintype.prod_ite_eq' i (fun j => f (s j))).symm
  rw [he, iid_mean_prod P n (fun j ω => if j = i then f ω else 1)]
  have hm (j : Fin n) : P.mean (fun ω => if j = i then f ω else 1) =
      if j = i then P.mean f else 1 := by
    by_cases h : j = i <;> simp [h, mean_const]
  simp_rw [hm]
  exact Fintype.prod_ite_eq' i (fun _ => P.mean f)

/-- Finite sums commute with expectation, used for expected counts. -/
theorem mean_sum {ι : Type*} [Fintype ι] (P : FiniteLaw Ω) (f : ι → Ω → ℝ) :
    P.mean (fun ω => ∑ i, f i ω) = ∑ i, P.mean (f i) := by
  simp only [FiniteLaw.mean, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Complementary events have probabilities summing to one. -/
theorem probability_complement (P : FiniteLaw Ω) (D : Ω → Prop) [DecidablePred D] :
    P.prob (fun ω => ¬ D ω) = 1-P.prob D := by
  have he : (fun ω => if ¬ D ω then (1 : ℝ) else 0) =
      (fun ω => 1 - (if D ω then (1 : ℝ) else 0)) := by
    funext ω; by_cases h : D ω <;> simp [h]
  rw [FiniteLaw.prob, he, mean_sub, mean_const]
  rfl

/-- Exact IID probability that no sampled subject lies in a given event.
This is the probability foundation of empty cells and empty treatment arms. -/
theorem iid_absence_probability (P : FiniteLaw Ω) (D : Ω → Prop) [DecidablePred D] (n : ℕ) :
    (P.iid n).prob (fun s => ∀ i, ¬ D (s i)) = (1-P.prob D)^n := by
  have he : (fun s : Fin n → Ω => if ∀ i, ¬ D (s i) then (1 : ℝ) else 0) =
      (fun s => ∏ i, if ¬ D (s i) then (1 : ℝ) else 0) := by
    funext s
    by_cases h : ∀ i, ¬ D (s i)
    · simp [h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      rw [if_neg h]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  rw [FiniteLaw.prob, he, iid_mean_prod P n (fun _ ω => if ¬ D ω then (1 : ℝ) else 0)]
  change (∏ _ : Fin n, P.prob (fun ω => ¬ D ω)) = _
  rw [probability_complement]
  simp

/-- The sample mean Ybar = (1/n)ΣY_i, p. 48. At n=0 the totalized
definition is zero; every asymptotic theorem uses n→∞. -/
def Study.ybar (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : ℝ :=
  (∑ i, bitVal (S.Y (s i))) / (n : ℝ)

/-- N_{zy}, the number of sampled subjects in (Z,Y) cell (z,y), used in
the printed ratios, p. 48, and corrected Lemma 2, T4. -/
def Study.cellCount (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z y : Bool) : ℕ :=
  ∑ i, if S.cell z y (s i) then 1 else 0

/-- T4(a): an empty (Z,Y) cell has exactly the nth power of its
population complement probability. This is unconditional IID sampling
and includes n=0; no approximation or random-denominator substitution. -/
theorem empty_cell_probability (S : Study Ω) (n : ℕ) (z y : Bool) :
    (S.law.iid n).prob (fun s => S.cellCount s z y = 0) =
      (1-S.law.prob (S.cell z y))^n := by
  have he : (fun s : Fin n → Ω => if S.cellCount s z y = 0 then (1 : ℝ) else 0) =
      (fun s => ∏ i, if ¬ S.cell z y (s i) then (1 : ℝ) else 0) := by
    funext s
    have hzero : S.cellCount s z y = 0 ↔ ∀ i, ¬ S.cell z y (s i) := by
      simp [Study.cellCount, Finset.sum_eq_zero_iff]
    by_cases h : ∀ i, ¬ S.cell z y (s i)
    · simp [hzero.mpr h, h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hiz : ¬ ¬ S.cell z y (s i) := hi
      have hz : S.cell z y (s i) := not_not.mp hiz
      have hc : S.cellCount s z y ≠ 0 := by intro hcount; exact h (hzero.mp hcount)
      rw [if_neg hc]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hz]
  rw [FiniteLaw.prob, he, iid_mean_prod S.law n
    (fun _ ω => if ¬ S.cell z y ω then (1 : ℝ) else 0)]
  change (∏ _ : Fin n, S.law.prob (fun ω => ¬ S.cell z y ω)) = _
  rw [probability_complement]
  simp

/-- A subgroup sample mean, the printed ratio on occupied cells.
The fixed value c on an empty cell is an explicit bounded completion
required by T4 and the asymptotic results; it is absent from the paper. -/
def Study.cellMean (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z y : Bool) (c : ℝ) : ℝ :=
  if S.cellCount s z y = 0 then c else
    (∑ i, if S.cell z y (s i) then (S.V (s i) : ℝ) else 0) / (S.cellCount s z y : ℝ)

/-- D={N10>0,N00>0}, the conditioning event in corrected Lemma 2, T4. -/
def Study.occupied (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : Prop :=
  0 < S.cellCount s true false ∧ 0 < S.cellCount s false false

/-- "μhat=Ybar+(1-Ybar)(Vbar10-Vbar00)", the combined estimator, p. 48.
The completion constants are quantified, not assumed to equal unknown
population means. -/
def Study.muHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.ybar s + (1 - S.ybar s) * (S.cellMean s true false c1 - S.cellMean s false false c0)

/-- Arm sample count Σ1{Z_i=z}, p. 49. -/
def Study.armCount (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z : Bool) : ℕ :=
  ∑ i, if S.Z (s i) = z then 1 else 0

/-- Vbar_z for the standard list estimator, p. 49, with fixed empty-arm
completion c. -/
def Study.armMean (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z : Bool) (c : ℝ) : ℝ :=
  if S.armCount s z = 0 then c else
    (∑ i, if S.Z (s i) = z then (S.V (s i) : ℝ) else 0) / (S.armCount s z : ℝ)

/-- μhat_S=Vbar_1-Vbar_0, the standard difference-in-means estimator,
p. 49, with both empty-arm completions explicit. -/
def Study.standardHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.armMean s true c1 - S.armMean s false c0

/-- Sample γhat=ΣZ_i/n, p. 49. -/
def Study.gammaHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : ℝ :=
  (S.armCount s true : ℝ) / (n : ℝ)

/-- "σhat²(·) denotes the sample variance", p. 49. The definition uses
the usual divisor N_{zy}-1. Zero is an explicit convention if fewer than two
subjects occupy the cell. -/
def Study.cellVariance (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z y : Bool) : ℝ :=
  if S.cellCount s z y < 2 then 0 else
    (∑ i, if S.cell z y (s i) then
      ((S.V (s i) : ℝ) - S.cellMean s z y 0)^2 else 0) / ((S.cellCount s z y : ℝ) - 1)

/-- The printed plug-in Varhat[μhat], p. 49, divided by n.
Where the printed formula lacks a defined sample variance or denominator,
the WHOLE variance estimate is the fixed value cV, per correction T4.
This convention is not an additional population assumption. -/
def Study.muVarianceHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 cV : ℝ) : ℝ :=
  if 2 ≤ S.cellCount s true false ∧ 2 ≤ S.cellCount s false false ∧
      S.ybar s < 1 ∧ 0 < S.gammaHat s ∧ S.gammaHat s < 1 then
    (((1 - S.muHat s c1 c0)^2 / (1 - S.ybar s)) * S.ybar s +
      (1 - S.ybar s) * (S.cellVariance s true false / S.gammaHat s +
        S.cellVariance s false false / (1 - S.gammaHat s))) / (n : ℝ)
  else cV

/-- Equation (3), p. 49: the proposed asymptotic variance σ² of μhat.
The standing model, including monotonicity, is maintained explicitly. -/
def Study.sigmaSq (S : Study Ω) : ℝ :=
  ((1 - S.mu)^2 / (1 - S.mu * S.truthRate)) * (S.mu * S.truthRate) +
    (1 - S.mu * S.truthRate) *
      (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false) / S.gamma +
       S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false) / (1 - S.gamma))

/-- T19(d): the actual equation (3) variance is strictly positive under
the four standing assumptions, as required for normal Wald inference. -/
theorem asymptotic_variance_positive (S : Study Ω) (hs : S.standing) : 0 < S.sigmaSq := by
  have hp := regularity_probabilities S hs.2.2.2
  have hg : 0 < S.gamma := hp.1 true
  have hg0 : 0 < 1-S.gamma := by
    have h := hp.1 false
    rw [prob_false] at h
    exact h
  have hq : 0 < 1-S.mu*S.truthRate := by
    rw [← direct_response_probability S hs.1 hs.2.2.2]
    have h := hp.2 false
    rw [prob_false] at h
    exact h
  have hr : 0 < S.mu*S.truthRate := by
    rw [← direct_response_probability S hs.1 hs.2.2.2]
    exact hp.2 true
  have ht := div_pos (hs.2.2.2.1 true false).2 hg
  have hc := div_pos (hs.2.2.2.1 false false).2 hg0
  have hfirst : 0 ≤ ((1-S.mu)^2/(1-S.mu*S.truthRate))*(S.mu*S.truthRate) :=
    mul_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hq)) (le_of_lt hr)
  unfold Study.sigmaSq
  have hb := mul_pos hq (add_pos ht hc)
  linarith

/-- The influence function ψ of T18 (finding P019-E003):
(1-δ*)(Y-r)+(1-Y)[Z(V-m1)/γ-(1-Z)(V-m0)/(1-γ)]. The two residual
terms use the corresponding Boolean cell masks; this is the identical
function, not a finite-sample substitute for the limit theorem. -/
def Study.combinedPsi (S : Study Ω) (ω : Ω) : ℝ :=
  (1-(S.listMean true false-S.listMean false false)) *
    (bitVal (S.Y ω)-S.law.prob (fun t => S.Y t = true)) +
  (if S.cell true false ω then (S.V ω : ℝ)-S.listMean true false else 0)/S.gamma -
  (if S.cell false false ω then (S.V ω : ℝ)-S.listMean false false else 0)/(1-S.gamma)

/-- T18 finite influence-function calculation: ψ has mean zero and
variance (1-δ*)²r(1-r)+(1-r)(s1/γ+s0/(1-γ)), with actual cell
means/variances. Treatment independence and nondegeneracy suffice for
this calculation; the identification substitution is separate. -/
theorem combined_influence_moments (S : Study Ω) (h3 : S.treatmentIndependent)
    (h4 : S.nondegenerate) :
    S.law.mean S.combinedPsi = 0 ∧
    S.law.variance S.combinedPsi =
      (1-(S.listMean true false-S.listMean false false))^2 *
        S.law.prob (fun ω => S.Y ω = true) * (1-S.law.prob (fun ω => S.Y ω = true)) +
      (1-S.law.prob (fun ω => S.Y ω = true)) *
        (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false)/S.gamma +
         S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)/(1-S.gamma)) := by
  let r := S.law.prob (fun ω => S.Y ω = true)
  let c := 1-(S.listMean true false-S.listMean false false)
  let u := fun ω => if S.cell true false ω then (S.V ω : ℝ)-S.listMean true false else 0
  let v := fun ω => if S.cell false false ω then (S.V ω : ℝ)-S.listMean false false else 0
  have hp := regularity_probabilities S h4
  have hg : S.gamma ≠ 0 := ne_of_gt (hp.1 true)
  have hg0 : 1-S.gamma ≠ 0 := by
    have h := ne_of_gt (hp.1 false)
    rw [prob_false] at h; exact h
  have hu := masked_central_moments S.law (fun ω => (S.V ω : ℝ))
    (S.cell true false) (ne_of_gt (h4.1 true false).1)
  have hv := masked_central_moments S.law (fun ω => (S.V ω : ℝ))
    (S.cell false false) (ne_of_gt (h4.1 false false).1)
  have hu0 : S.law.mean u = 0 := hu.1
  have hv0 : S.law.mean v = 0 := hv.1
  have hu2 : S.law.mean (fun ω => (u ω)^2) =
      S.law.prob (S.cell true false)*S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false) := by
    have he : (fun ω => (u ω)^2) = (fun ω =>
        if S.cell true false ω then ((S.V ω : ℝ)-S.listMean true false)^2 else 0) := by
      funext ω; dsimp only [u]; split_ifs <;> simp
    rw [he]; exact hu.2
  have hv2 : S.law.mean (fun ω => (v ω)^2) =
      S.law.prob (S.cell false false)*S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false) := by
    have he : (fun ω => (v ω)^2) = (fun ω =>
        if S.cell false false ω then ((S.V ω : ℝ)-S.listMean false false)^2 else 0) := by
      funext ω; dsimp only [v]; split_ifs <;> simp
    rw [he]; exact hv.2
  have hfun : S.combinedPsi = (fun ω => c*(bitVal (S.Y ω)-r)+u ω/S.gamma-v ω/(1-S.gamma)) := rfl
  have hmean : S.law.mean S.combinedPsi = 0 := by
    rw [hfun, mean_sub, mean_add, mean_const_mul, mean_div_const, mean_div_const,
      mean_sub, mean_const, mean_bit, hu0, hv0]
    change c*(r-r)+0/S.gamma-0/(1-S.gamma) = 0
    ring
  have hpoint : (fun ω => (S.combinedPsi ω)^2) = (fun ω =>
      c^2*(bitVal (S.Y ω)-r)^2 + (u ω)^2/S.gamma^2 + (v ω)^2/(1-S.gamma)^2 +
        u ω*(-2*c*r/S.gamma) + v ω*(2*c*r/(1-S.gamma))) := by
    funext ω
    rw [hfun]
    dsimp only [u, v]
    cases hy : S.Y ω <;> cases hz : S.Z ω <;>
      simp [Study.cell, bitVal, hy, hz] <;> field_simp <;> ring
  have hp1 : S.law.prob (S.cell true false) = S.gamma*(1-r) := by
    rw [cell_probability S h3, prob_false]; rfl
  have hp0 : S.law.prob (S.cell false false) = (1-S.gamma)*(1-r) := by
    rw [cell_probability S h3, prob_false, prob_false]; rfl
  refine ⟨hmean, ?_⟩
  rw [FiniteLaw.variance, hmean]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
  rw [hpoint]
  simp only [mean_add, mean_const_mul, mean_mul_const, mean_div_const, hu0, hv0,
    zero_mul, add_zero, hu2, hv2]
  rw [binary_centered_moment S.law S.Y]
  rw [hp1, hp0]
  change c^2*(r*(1-r)) + (S.gamma*(1-r)*S.law.cv (fun ω => (S.V ω : ℝ))
      (S.cell true false))/S.gamma^2 +
    ((1-S.gamma)*(1-r)*S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false))/(1-S.gamma)^2 =
    c^2*r*(1-r)+(1-r)*(S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false)/S.gamma+
      S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)/(1-S.gamma))
  field_simp <;> ring

/-- T18: the exact variance of the influence ψ is the printed equation
(3) right-hand side under ALL maintained assumptions. This finite
population statement does not assert the still-separate variance limit. -/
theorem combined_influence_variance (S : Study Ω) (hs : S.standing) :
    S.law.variance S.combinedPsi = S.sigmaSq := by
  have hp := regularity_probabilities S hs.2.2.2
  have hq : 1-S.law.prob (fun ω => S.Y ω = true) ≠ 0 := by
    have h := ne_of_gt (hp.2 false); rw [prob_false] at h; exact h
  have hid : S.mu = S.law.prob (fun ω => S.Y ω = true) +
      (1-S.law.prob (fun ω => S.Y ω = true))*(S.listMean true false-S.listMean false false) := by
    rw [prevalence_identity S hs]
    unfold Study.combined
    rw [mean_sub, mean_const, mean_bit]
  have hc : 1-(S.listMean true false-S.listMean false false) =
      (1-S.mu)/(1-S.law.prob (fun ω => S.Y ω = true)) := by
    apply (eq_div_iff hq).2
    nlinarith [hid]
  rw [(combined_influence_moments S hs.2.2.1 hs.2.2.2).2, hc]
  unfold Study.sigmaSq
  rw [← direct_response_probability S hs.1 hs.2.2.2]
  have hg : S.gamma ≠ 0 := ne_of_gt (hp.1 true)
  have hg0 : 1-S.gamma ≠ 0 := by
    have h := ne_of_gt (hp.1 false); rw [prob_false] at h; exact h
  field_simp <;> ring

/-- Standard estimator's limiting variance, first display of the
Proposition 2 proof, p. 64. -/
def Study.standardSigmaSq (S : Study Ω) : ℝ :=
  S.law.cv (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = true) / S.gamma +
    S.law.cv (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω = false) / (1 - S.gamma)

/-- T18(a), display (8), p. 63: exact finite-sample estimator identity,
valid under every bounded completion. -/
theorem estimator_product_identity (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) :
    S.muHat s c1 c0 = 1 + (1 - S.ybar s) *
      (S.cellMean s true false c1 - S.cellMean s false false c0 - 1) := by
  unfold Study.muHat; ring

/-- T18(c), finding P019-E003: the exact decomposition of the
combined estimator's error before taking a limit. Its only algebraic
hypothesis is the identified population relation μ=r+(1-r)(m1-m0). -/
theorem estimator_error_decomposition (yb v1 v0 μ r m1 m0 : ℝ)
    (hid : μ = r + (1-r)*(m1-m0)) :
    yb + (1-yb)*(v1-v0) - μ =
      (1-(m1-m0))*(yb-r) + (1-r)*((v1-m1)-(v0-m0)) -
        (yb-r)*((v1-m1)-(v0-m0)) := by rw [hid]; ring

/-- T10(d) and T21(c): exact residual identity for a subgroup ratio mean.
With I_i the cell indicator, mhat-m = Σ I_i(V_i-m)/Σ I_i.
This identity is on occupied cells; it assumes no asymptotic expansion. -/
theorem ratio_residual_identity {n : ℕ} (I V : Fin n → ℝ) (m : ℝ)
    (hI : (∑ i, I i) ≠ 0) :
    (∑ i, I i*V i)/(∑ i, I i)-m = (∑ i, I i*(V i-m))/(∑ i, I i) := by
  have he : (∑ i, I i*(V i-m)) = (∑ i, I i*V i) - (∑ i, I i)*m := by
    simp [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [he]
  field_simp <;> ring

/-- T19(a): the printed first plug-in term equals its nonsingular
sample analogue y(1-y)(1-(v1-v0))² when y≠1. -/
theorem plugin_identity (y v1 v0 : ℝ) (hy : 1-y ≠ 0) :
    ((1 - (y+(1-y)*(v1-v0)))^2 / (1-y)) * y =
      y*(1-y)*(1-(v1-v0))^2 := by field_simp <;> ring

/-- T19(b): exact equivalence of the population variance terms, with
r=μp and nonempty negative direct-response stratum. -/
theorem population_variance_term (μ r : ℝ) (hr : 1-r ≠ 0) :
    ((1-μ)^2/(1-r))*r = r*(1-r)*((1-μ)/(1-r))^2 := by field_simp <;> ring

/-- T20(d): completing the square in the minimization on p. 64. This
proves the exact population algebra used before display (10). -/
theorem weighted_square_identity (γ κ x : ℝ) (hg : γ ≠ 0) (hg0 : 1-γ ≠ 0) :
    (κ+x)^2/γ + x^2/(1-γ) - κ^2 = (x+(1-γ)*κ)^2/(γ*(1-γ)) := by
  field_simp; ring

/-- T20(d): the weighted quadratic is bounded below by κ², with equality
exactly at x=(γ-1)κ, for 0<γ<1. -/
theorem weighted_square_minimum (γ κ x : ℝ) (hg : 0 < γ) (hg1 : γ < 1) :
    κ^2 ≤ (κ+x)^2/γ + x^2/(1-γ) ∧
    ((κ+x)^2/γ + x^2/(1-γ) = κ^2 ↔ x = (γ-1)*κ) := by
  have hd : 0 < γ*(1-γ) := mul_pos hg (by linarith)
  have hi := weighted_square_identity γ κ x (ne_of_gt hg) (by linarith)
  have hn := div_nonneg (sq_nonneg (x+(1-γ)*κ)) (le_of_lt hd)
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    have hdiv : (x+(1-γ)*κ)^2/(γ*(1-γ)) = 0 := by linarith
    have hs : (x+(1-γ)*κ)^2 = 0 := (div_eq_zero_iff.mp hdiv).resolve_right (ne_of_gt hd)
    have hz : x+(1-γ)*κ = 0 := sq_eq_zero_iff.mp hs
    nlinarith
  · intro h
    subst x
    have hz : (γ-1)*κ+(1-γ)*κ = 0 := by ring
    rw [hz] at hi
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div] at hi
    linarith

/-- T20(f): the exact strict variance gap after total-variance expansion,
with r=μp, q=1-r, τ=Var[W|Y=1], c=(1-μ)/q and u=a0-m0. -/
theorem variance_gap_strict (r q γ s1 s0 τ u c : ℝ)
    (hr : 0 < r) (hq : 0 ≤ q) (hg : 0 < γ) (hg1 : γ < 1) (ht : 0 < τ) :
    (q*s1+r*τ+r*q*(u+c)^2)/γ + (q*s0+r*τ+r*q*u^2)/(1-γ) -
      (q*(s1/γ+s0/(1-γ))+r*q*c^2) =
        r*τ/(γ*(1-γ)) + r*q*(u+(1-γ)*c)^2/(γ*(1-γ)) ∧
    q*(s1/γ+s0/(1-γ))+r*q*c^2 <
      (q*s1+r*τ+r*q*(u+c)^2)/γ + (q*s0+r*τ+r*q*u^2)/(1-γ) := by
  have hd : 0 < γ*(1-γ) := mul_pos hg (by linarith)
  have he : (q*s1+r*τ+r*q*(u+c)^2)/γ + (q*s0+r*τ+r*q*u^2)/(1-γ) -
      (q*(s1/γ+s0/(1-γ))+r*q*c^2) =
        r*τ/(γ*(1-γ)) + r*q*(u+(1-γ)*c)^2/(γ*(1-γ)) := by
    have hγ := ne_of_gt hg
    have hγ0 : 1-γ ≠ 0 := by linarith
    field_simp; ring
  have hp : 0 < r*τ/(γ*(1-γ)) := div_pos (mul_pos hr ht) hd
  have hn : 0 ≤ r*q*(u+(1-γ)*c)^2/(γ*(1-γ)) :=
    div_nonneg (mul_nonneg (mul_nonneg (le_of_lt hr) hq) (sq_nonneg _)) (le_of_lt hd)
  exact ⟨he, by linarith⟩

/-- The (Y,Z) pattern is the finite sigma-field F of corrected Lemma 2:
conditioning on its fibre is conditioning on all sampled direct answers
and assignments. T4, finding P019-E003. -/
def Study.patternFibre (S : Study Ω) {n : ℕ} (s t : Fin n → Ω) : Prop :=
  ∀ i, S.Y (t i) = S.Y (s i) ∧ S.Z (t i) = S.Z (s i)

/-- A=1-Ybar in the proof of Proposition 1, displays (8)-(9), p. 63. -/
def Study.sampleA (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : ℝ := 1 - S.ybar s

/-- B=Vbar10-Vbar00-1 on D, corrected proof of display (9). -/
def Study.sampleB (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.cellMean s true false c1 - S.cellMean s false false c0 - 1

/-- h=s1/N10+s0/N00 on D, corrected proof of display (9), T4. -/
def Study.sampleH (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : ℝ :=
  S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false) / (S.cellCount s true false : ℝ) +
    S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false) / (S.cellCount s false false : ℝ)

/-- K=N10+N00, the number of negative direct responses, corrected
Lemma 2 and displays (4)-(7), pp. 62-63. -/
def Study.negativeCount (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : ℕ :=
  S.cellCount s true false + S.cellCount s false false


/-- T4(d), exact Taylor coefficient algebra: the multinomial covariance
matrix and gradients of (P1+P0)² and s1/P1+s0/P0 give the claimed
coefficient -2r(s1/γ+s0/(1-γ)), with r=1-q. This proves only the
coefficient, not the probabilistic remainder or covariance-order theorem. -/
theorem covariance_taylor_coefficient (q γ s1 s0 : ℝ)
    (hq : q ≠ 0) (hg : γ ≠ 0) (hg0 : 1-γ ≠ 0) :
    let α := q*γ
    let β := q*(1-γ)
    2*q*(α*(1-α)*(-s1/α^2) + (-α*β)*(-s0/β^2)) +
      2*q*((-α*β)*(-s1/α^2) + β*(1-β)*(-s0/β^2)) =
        -2*(1-q)*(s1/γ+s0/(1-γ)) := by
  dsimp only
  field_simp <;> ring

/-- T4(e): expected treatment count equals nγ under IID Bernoulli
sampling, while the realized count equals nγhat for n>0.
This is the repaired sentence after display (9), p. 63. -/
theorem treatment_count_correction (S : Study Ω) (n : ℕ) (hn : 0 < n) :
    (S.law.iid n).mean (fun s => (S.armCount s true : ℝ)) = (n : ℝ)*S.gamma ∧
    ∀ s : Fin n → Ω, (S.armCount s true : ℝ) = (n : ℝ)*S.gammaHat s := by
  constructor
  · have he : (fun s : Fin n → Ω => (S.armCount s true : ℝ)) =
        (fun s => ∑ i, if S.Z (s i) = true then (1 : ℝ) else 0) := by
      funext s; simp [Study.armCount]
    rw [he, mean_sum]
    simp_rw [iid_mean_coordinate S.law n _ (fun ω => if S.Z ω = true then (1 : ℝ) else 0)]
    change (∑ _ : Fin n, S.gamma) = (n : ℝ)*S.gamma
    simp [Finset.sum_const, nsmul_eq_mul]
  · intro s
    unfold Study.gammaHat
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp

/-- T3(iv): in the same valid population, at n=4 the expected
allocation nγ is 2, but a realized count of zero has probability 1/16.
Thus the equality after (9) cannot be an almost-sure equality. -/
theorem realized_count_counterexample :
    finiteSampleWitness.standing ∧ (4 : ℝ)*finiteSampleWitness.gamma = 2 ∧
    (finiteSampleWitness.law.iid 4).prob
      (fun s => finiteSampleWitness.armCount s true = 0) = 1/16 := by
  refine ⟨finite_sample_witness_valid, ?_, ?_⟩
  · norm_num [Study.gamma, finiteSampleWitness, uniformFin, fairBit,
      FiniteLaw.prob, FiniteLaw.mean, Fin.sum_univ_succ]
  · have he : (fun s : Fin 4 → Fin 16 =>
        if finiteSampleWitness.armCount s true = 0 then (1 : ℝ) else 0) =
        (fun s => if ∀ i, ¬ finiteSampleWitness.Z (s i) = true then (1 : ℝ) else 0) := by
      funext s
      have h : finiteSampleWitness.armCount s true = 0 ↔
          ∀ i, ¬ finiteSampleWitness.Z (s i) = true := by simp [Study.armCount]
      simp only [h]
    rw [FiniteLaw.prob, he]
    change (finiteSampleWitness.law.iid 4).prob (fun s => ∀ i,
      ¬ finiteSampleWitness.Z (s i) = true) = _
    rw [iid_absence_probability finiteSampleWitness.law
      (fun ω => finiteSampleWitness.Z ω = true) 4]
    norm_num [finiteSampleWitness, uniformFin, fairBit,
      FiniteLaw.prob, FiniteLaw.mean, Fin.sum_univ_succ]


/-- Standard normal CDF Φ, Propositions 3-4, pp. 50-51. -/
def normalCDF (t : ℝ) : ℝ := ((gaussianReal 0 1) (Set.Iic t)).toReal

/-- z_u, the standard-normal quantile used without a definition in
Corollary 1, p. 49, and the power correction T15. -/
def normalQuantile (u : ℝ) : ℝ := sInf {x : ℝ | u ≤ normalCDF x}

/-- Weak convergence of the IID sample statistic to a specified
probability law: convergence of expectations of every bounded continuous
test function. This is the usual convergence-in-distribution meaning of
the paper's asymptotic-normality statements, p. 49. -/
def WeakLimit {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (P : FiniteLaw Ω) (T : (n : ℕ) → (Fin n → Ω) → E) (Q : Measure E) : Prop :=
  ∀ f : E → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun n => (P.iid n).mean (fun s => f (T n s))) atTop (nhds (∫ x, f x ∂Q))

/-- Convergence in probability across the paper's IID sample sizes.
For every ε>0 the probability of an ε-error tends to zero. -/
def ProbabilityLimit (P : FiniteLaw Ω) (T : (n : ℕ) → (Fin n → Ω) → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => (P.iid n).prob (fun s => ε < |T n s-a|)) atTop (nhds 0)

/-- Root-n consistency, p. 49, interpreted as stochastic boundedness
of sqrt(n)(μhat-μ). -/
def RootNTight (S : Study Ω) (c1 c0 : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (S.law.iid n).prob (fun s => M < |Real.sqrt n * (S.muHat s c1 c0-S.mu)|) < ε


/-- βhat=Vbar11-Vbar01, Placebo Test I, p. 50, with explicit bounded
values on empty cells. -/
def Study.betaHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.cellMean s true true c1 - S.cellMean s false true c0

/-- Varhat[βhat], Placebo Test I, p. 50, with a fixed value cV wherever
either sample variance is undefined. -/
def Study.betaVarianceHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (cV : ℝ) : ℝ :=
  if 2 ≤ S.cellCount s true true ∧ 2 ≤ S.cellCount s false true then
    S.cellVariance s true true / (S.cellCount s true true : ℝ) +
      S.cellVariance s false true / (S.cellCount s false true : ℝ)
  else cV

/-- Printed two-sided normal p-value, Propositions 3-4, pp. 50-51.
At a zero sample standard error Lean's totalized division assigns zero
to the studentized statistic. This is an explicit bounded completion of
an undefined printed expression; the null limit statements are unchanged. -/
def normalPValue (estimate null varianceEstimate : ℝ) : ℝ :=
  2 * normalCDF (-|estimate-null| / Real.sqrt varianceEstimate)


/-- Direct-answer sample mean within an arm, δhat numerator/denominator
in Section 4.2, p. 51; c completes an empty arm. -/
def Study.directArmMean (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z : Bool) (c : ℝ) : ℝ :=
  if S.armCount s z = 0 then c else
    (∑ i, if S.Z (s i) = z then bitVal (S.Y (s i)) else 0) / (S.armCount s z : ℝ)

/-- δhat is the treated-minus-control direct-answer mean, p. 51. -/
def Study.deltaHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (c1 c0 : ℝ) : ℝ :=
  S.directArmMean s true c1 - S.directArmMean s false c0

/-- Direct-answer sample variance with divisor N_z-1, Section 4.2,
p. 51, and zero if N_z<2. -/
def Study.directArmVariance (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z : Bool) : ℝ :=
  if S.armCount s z < 2 then 0 else
    (∑ i, if S.Z (s i) = z then
      (bitVal (S.Y (s i))-S.directArmMean s z 0)^2 else 0) / ((S.armCount s z : ℝ)-1)

/-- Varhat[δhat], Section 4.2, p. 51, with fixed whole-estimate
completion cV if an arm has fewer than two observations. -/
def Study.deltaVarianceHat (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (cV : ℝ) : ℝ :=
  if 2 ≤ S.armCount s true ∧ 2 ≤ S.armCount s false then
    S.directArmVariance s true / (S.armCount s true : ℝ) +
      S.directArmVariance s false / (S.armCount s false : ℝ)
  else cV


/-- S=p1(1-p1)+p2(1-p2), the unpooled variance in the R planning
approximation for Figure A2, supplement Appendix D and T15. -/
def planningS (p1 p2 : ℝ) : ℝ := p1*(1-p1)+p2*(1-p2)

/-- V=(p1+p2)(1-(p1+p2)/2), the pooled critical-value variance of
power.prop.test, T15 and finding P019-E006. -/
def planningV (p1 p2 : ℝ) : ℝ := (p1+p2)*(1-(p1+p2)/2)

/-- Favored rejection tail A from the first Figure A2 panel's original
strict=FALSE call. This is normal-approximation planning power, not the
exact finite-sample power of Proposition 4. -/
def favoredTail (n p1 p2 c : ℝ) : ℝ :=
  normalCDF ((Real.sqrt n * |p1-p2| - c*Real.sqrt (planningV p1 p2)) /
    Real.sqrt (planningS p1 p2))

/-- Opposite rejection tail B, included by strict=TRUE in the T15
correction. -/
def oppositeTail (n p1 p2 c : ℝ) : ℝ :=
  normalCDF ((-Real.sqrt n * |p1-p2| - c*Real.sqrt (planningV p1 p2)) /
    Real.sqrt (planningS p1 p2))

/-- Two-sided normal planning power as a probability under a standard
normal draw G: |d+sqrt(S/n)G|>c sqrt(V/n), finding P019-E006. -/
def twoSidedPlanningPower (n p1 p2 c : ℝ) : ℝ :=
  ((gaussianReal 0 1) {g : ℝ | c * Real.sqrt (planningV p1 p2 / n) <
    abs (abs (p1-p2) + Real.sqrt (planningS p1 p2/n)*g)}).toReal

/-- T15(i): the pooled-minus-unpooled variance is exactly half the
squared difference in proportions, hence nonnegative. -/
theorem pooled_variance_difference (p1 p2 : ℝ) :
    planningV p1 p2 - planningS p1 p2 = (p1-p2)^2/2 ∧
    planningS p1 p2 ≤ planningV p1 p2 := by
  have he : planningV p1 p2 - planningS p1 p2 = (p1-p2)^2/2 := by
    unfold planningV planningS; ring
  exact ⟨he, by nlinarith [sq_nonneg (p1-p2)]⟩

/-- T15(ii), the exact square-root inequality underlying the omitted
tail bound; no normal-CDF hypothesis is assumed. -/
theorem planning_tail_argument (n p1 p2 c : ℝ) (hn : 0 < n)
    (hs : 0 < planningS p1 p2) (hc : 0 < c) :
    c ≤ (Real.sqrt n * |p1-p2| + c*Real.sqrt (planningV p1 p2)) /
      Real.sqrt (planningS p1 p2) ∧
    ((Real.sqrt n * |p1-p2| + c*Real.sqrt (planningV p1 p2)) /
      Real.sqrt (planningS p1 p2) = c ↔ p1=p2) := by
  have hS : 0 < Real.sqrt (planningS p1 p2) := Real.sqrt_pos.2 hs
  have hN : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hVS := Real.sqrt_le_sqrt (pooled_variance_difference p1 p2).2
  have hC : c*Real.sqrt (planningS p1 p2) ≤ c*Real.sqrt (planningV p1 p2) :=
    mul_le_mul_of_nonneg_left hVS (le_of_lt hc)
  have hD : 0 ≤ Real.sqrt n * |p1-p2| := mul_nonneg (le_of_lt hN) (abs_nonneg _)
  refine ⟨(le_div_iff₀ hS).2 (by linarith), ?_⟩
  constructor
  · intro h
    have he := (div_eq_iff (ne_of_gt hS)).mp h
    have ha : |p1-p2| = 0 := by nlinarith [abs_nonneg (p1-p2)]
    exact sub_eq_zero.mp (abs_eq_zero.mp ha)
  · intro h
    subst p1
    have he : planningV p2 p2 = planningS p2 p2 := by unfold planningV planningS; ring
    simp only [sub_self, abs_zero, mul_zero, zero_add, he]
    field_simp


/-- The per-list placebo influence function (finding P019-N003),
for the joint Fisher calibration on p. 56. q=Pr(Y=1), m=E(W|Y=1).
Its covariance, not shared respondents alone, governs joint inference. -/
def Study.betaPsi (S : Study Ω) (ω : Ω) : ℝ :=
  bitVal (S.Y ω) / S.law.prob (fun t => S.Y t = true) *
    ((bitVal (S.Z ω)-S.gamma) / (S.gamma*(1-S.gamma))) *
    ((S.W ω : ℝ) - S.law.ce (fun t => (S.W t : ℝ)) (fun t => S.Y t = true))

/-- Full assignment independence and independence of the assignment
vector from all W,X,Y coordinates, the sufficient joint premise
in corrected T10. This permits arbitrary cross-list outcome dependence.
Finite factorization is required for every function of the latent vector. -/
def jointAssignmentStable (P : FiniteLaw Ω) (S : Fin 5 → Study Ω) : Prop :=
  ∀ (f : (Fin 5 → ℕ) → (Fin 5 → Bool) → (Fin 5 → Bool) → ℝ) (a : Fin 5 → Bool),
    P.mean (fun ω => if ∀ j, (S j).Z ω = a j then
      f (fun j => (S j).W ω) (fun j => (S j).X ω) (fun j => (S j).Y ω) else 0) =
      (∏ j, P.prob (fun ω => (S j).Z ω = a j)) *
        P.mean (fun ω => f (fun j => (S j).W ω) (fun j => (S j).X ω) (fun j => (S j).Y ω))

/-- Conditioning on all cross-list W,X,Y coordinates, L in corrected
T10 (finding P019-N003). -/
def latentVectorFibre (S : Fin 5 → Study Ω) (ω t : Ω) : Prop :=
  ∀ j, (S j).W t = (S j).W ω ∧ (S j).X t = (S j).X ω ∧ (S j).Y t = (S j).Y ω

/-- Fisher T=-2Σ log p_j, Section 5.3, p. 56 (the paper names the
method without writing out the statistic). -/
def fisherStatistic (p : Fin 5 → ℝ) : ℝ := -2 * ∑ j, Real.log (p j)

/-- χ²_10 is defined as the law of the sum of squares of ten independent
standard normals, the reference used in the p. 56 joint test. -/
def chiSquareTen : Measure ℝ :=
  (Measure.pi (fun _ : Fin 10 => gaussianReal 0 1)).map (fun x => ∑ j, (x j)^2)


/-- A fair sign U or A_j=2Z_j-1 in T9's 128-atom counterexample,
finding P019-N003. -/
def bitSign (b : Bool) : ℝ := if b then 1 else -1

/-- P_k=∏_{j≤k} A_j, with P_0=1, in the sequential-spillover
counterexample, T9. First two bits are D and U. -/
def prefixSign (ω : Fin 128) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, bitSign (fairBit ω (i+2))

/-- F_j=∏_{k>j} A_k, in the sequential-spillover counterexample, T9;
the argument j here is zero-based. -/
def suffixSign (ω : Fin 128) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.Ico (j+1) 5, bitSign (fairBit ω (i+2))

/-- T9's time-ordered model on 128 equiprobable atoms. W_j uses only
earlier assignments, Y_j is reported after the lists and depends on later
assignments, X_j=D, V_j=W_j+DZ_j. Baseline counts are 1 or 2. -/
def sequentialStudy (j : Fin 5) : Study (Fin 128) where
  law := uniformFin 128 (by norm_num)
  W := fun ω => if bitSign (fairBit ω 1) * prefixSign ω j.val = 1 then 2 else 1
  X := fun ω => fairBit ω 0
  Y := fun ω => fairBit ω 0 && decide (suffixSign ω j.val = 1)
  Z := fun ω => fairBit ω (j.val+2)
  V := fun ω => (if bitSign (fairBit ω 1) * prefixSign ω j.val = 1 then 2 else 1) +
    (if fairBit ω 0 && fairBit ω (j.val+2) then 1 else 0)


/-- The exact simplified influences in T9: 2DU(P_j+P_5) for j<5,
2DUP_5 for j=5 (finding P019-N003). -/
def sequentialPsi (j : Fin 5) (ω : Fin 128) : ℝ :=
  2*bitVal (fairBit ω 0)*bitSign (fairBit ω 1)*
    (if j.val < 4 then prefixSign ω (j.val+1)+prefixSign ω 5 else prefixSign ω 5)

/-- Integer copy of the fair signs for finite enumeration.
It does not introduce a different probability model. -/
def integerSign (b : Bool) : ℤ := if b then 1 else -1

/-- Integer copy of P_k in the T9 exact enumeration. -/
def integerPrefix (ω : Fin 128) (k : ℕ) : ℤ :=
  ∏ i ∈ Finset.range k, integerSign (fairBit ω (i+2))

/-- Integer copy of the T9 influence function; its cast equals the real copy. -/
def integerSequentialPsi (j : Fin 5) (ω : Fin 128) : ℤ :=
  2*(if fairBit ω 0 then 1 else 0)*integerSign (fairBit ω 1)*
    (if j.val < 4 then integerPrefix ω (j.val+1)+integerPrefix ω 5 else integerPrefix ω 5)

/-- Integer and real product signs agree by the integer-to-real ring map. -/
theorem prefix_integer_cast (ω : Fin 128) (k : ℕ) :
    (integerPrefix ω k : ℝ) = prefixSign ω k := by
  unfold integerPrefix prefixSign
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  cases h : fairBit ω (i+2) <;> simp [integerSign, bitSign, h]

/-- The simplified real influence is exactly the cast of its integer
copy, so discrete computation verifies real expectation numerators. -/
theorem sequential_psi_integer_cast (j : Fin 5) (ω : Fin 128) :
    (integerSequentialPsi j ω : ℝ) = sequentialPsi j ω := by
  cases hd : fairBit ω 0 <;> cases hu : fairBit ω 1 <;>
    by_cases hj : j.val < 4 <;>
      simp [integerSequentialPsi, sequentialPsi, integerSign, bitVal, bitSign,
        hd, hu, hj, prefix_integer_cast]

/-- Exact integer covariance sums over 128 atoms. -/
theorem sequential_integer_matrix :
    ∀ j k : Fin 5, (∑ ω : Fin 128, integerSequentialPsi j ω * integerSequentialPsi k ω) =
      if j = k then (if j.val < 4 then (512 : ℤ) else 256) else 256 := by decide

/-- Exact integer mean sums over all 128 atoms. -/
theorem sequential_integer_centered :
    ∀ j : Fin 5, (∑ ω : Fin 128, integerSequentialPsi j ω) = 0 := by decide

/-- T9's exact covariance calculation over all 128 latent atoms. This
finite lemma does not by itself prove the Fisher reference is false:
the transformed continuous-law and limit steps remain separate. -/
theorem sequential_influence_matrix (j k : Fin 5) :
    (uniformFin 128 (by norm_num)).mean
      (fun ω => sequentialPsi j ω * sequentialPsi k ω) =
        if j = k then (if j.val < 4 then 4 else 2) else 2 := by
  have he : (uniformFin 128 (by norm_num)).mean
      (fun ω => sequentialPsi j ω * sequentialPsi k ω) =
      (1/128 : ℝ) * ((∑ ω : Fin 128, integerSequentialPsi j ω * integerSequentialPsi k ω : ℤ) : ℝ) := by
    unfold FiniteLaw.mean uniformFin
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    rw [sequential_psi_integer_cast, sequential_psi_integer_cast]
  rw [he, sequential_integer_matrix]
  by_cases hjk : j = k <;> by_cases hj : j.val < 4 <;> simp [hjk, hj] <;> norm_num

/-- T9: each simplified influence has mean zero under the actual
uniform 128-atom law, with the integer computation justified by casting. -/
theorem sequential_influence_centered (j : Fin 5) :
    (uniformFin 128 (by norm_num)).mean (sequentialPsi j) = 0 := by
  have he : (uniformFin 128 (by norm_num)).mean (sequentialPsi j) =
      (1/128 : ℝ) * ((∑ ω : Fin 128, integerSequentialPsi j ω : ℤ) : ℝ) := by
    unfold FiniteLaw.mean uniformFin
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    rw [sequential_psi_integer_cast]
  rw [he, sequential_integer_centered]
  norm_num

/-- The five limiting standardized normals in T9 (finding P019-N003):
G_j=(E_j+E_5)/sqrt(2) for j<5 and G_5=E_5. -/
def correlatedNormals (e : Fin 5 → ℝ) (j : Fin 5) : ℝ :=
  if j.val < 4 then (e j + e 4)/Real.sqrt 2 else e 4

/-- The transformed Fisher limit for the sequential T9 model. -/
def sequentialFisherLimit : Measure ℝ :=
  (Measure.pi (fun _ : Fin 5 => gaussianReal 0 1)).map (fun e =>
    fisherStatistic (fun j => normalPValue (correlatedNormals e j) 0 1))

/-- Variance of a real variable under a continuous law, used to compare
T9's Fisher limit with χ²_10. -/
def continuousVariance (P : Measure ℝ) : ℝ :=
  (∫ x, x^2 ∂P) - (∫ x, x ∂P)^2


/-- T4 (finding P019-E003): conditional on the
full sampled (Y,Z) pattern, the V_i are independent and each has its
own population-cell law. Every test function of each V_i is allowed.
Only a positive-probability pattern is used as a conditioning event. -/
theorem conditional_sample_factorization (S : Study Ω) (n : ℕ)
    (s : Fin n → Ω) (f : Fin n → ℕ → ℝ)
    (hF : (S.law.iid n).prob (S.patternFibre s) ≠ 0) :
    (S.law.iid n).ce (fun t => ∏ i, f i (S.V (t i))) (S.patternFibre s) =
      ∏ i, S.law.ce (fun ω => f i (S.V ω))
        (S.cell (S.Z (s i)) (S.Y (s i))) := by
  let D : Fin n → Ω → Prop := fun i => S.cell (S.Z (s i)) (S.Y (s i))
  have hp (t : Fin n → Ω) : S.patternFibre s t ↔ ∀ i, D i (t i) := by
    simp only [Study.patternFibre, D, Study.cell, and_comm]
  have hproduct (g : Fin n → Ω → ℝ) :
      (fun t : Fin n → Ω => if S.patternFibre s t then ∏ i, g i (t i) else 0) =
        (fun t => ∏ i, if D i (t i) then g i (t i) else 0) := by
    funext t
    by_cases h : ∀ i, D i (t i)
    · simp [hp, h]
    · rw [if_neg (by simpa only [hp] using h)]
      obtain ⟨i, hi⟩ := not_forall.mp h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hprob : (S.law.iid n).prob (S.patternFibre s) = ∏ i, S.law.prob (D i) := by
    unfold FiniteLaw.prob
    have he := hproduct (fun _ _ => 1)
    simp only [Finset.prod_const_one] at he
    rw [he, iid_mean_prod S.law n (fun i ω => if D i ω then 1 else 0)]
  unfold FiniteLaw.ce
  rw [hproduct (fun i ω => f i (S.V ω)), iid_mean_prod S.law n
    (fun i ω => if D i ω then f i (S.V ω) else 0), hprob]
  simp only [FiniteLaw.ce, Finset.prod_div_distrib]
  rfl

/-- Exact product moment of two different IID sampled coordinates.
This is the finite independence calculation needed for the variance of
Ybar in Proposition 1, p. 63. -/
theorem iid_mean_two_coordinates (P : FiniteLaw Ω) (n : ℕ) (i j : Fin n)
    (f g : Ω → ℝ) (hij : i ≠ j) :
    (P.iid n).mean (fun s => f (s i)*g (s j)) = P.mean f * P.mean g := by
  have he : (fun s : Fin n → Ω => f (s i)*g (s j)) =
      (fun s => ∏ k, (if k=i then f (s k) else 1)*(if k=j then g (s k) else 1)) := by
    funext s
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
  rw [he, iid_mean_prod P n
    (fun k ω => (if k=i then f ω else 1)*(if k=j then g ω else 1))]
  have hm (k : Fin n) :
      P.mean (fun ω => (if k=i then f ω else 1)*(if k=j then g ω else 1)) =
        (if k=i then P.mean f else 1)*(if k=j then P.mean g else 1) := by
    by_cases hki : k=i
    · subst k; simp [hij]
    · by_cases hkj : k=j
      · subst k; simp [hki]
      · simp [hki, hkj, mean_const]
  simp_rw [hm]
  rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']

/-- Exact finite IID mean and variance of an average: E[fbar]=E[f]
and Var(fbar)=Var(f)/n for n>0. This proves the random-sample moment
step in Proposition 1 rather than replacing counts by their expectations. -/
theorem iid_average_moments (P : FiniteLaw Ω) (n : ℕ) (hn : 0 < n) (f : Ω → ℝ) :
    (P.iid n).mean (fun s => (∑ i, f (s i))/(n : ℝ)) = P.mean f ∧
    (P.iid n).variance (fun s => (∑ i, f (s i))/(n : ℝ)) = P.variance f/(n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hmean : (P.iid n).mean (fun s => (∑ i, f (s i))/(n : ℝ)) = P.mean f := by
    rw [mean_div_const, mean_sum]
    simp_rw [iid_mean_coordinate P n _ f]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hsecond : (P.iid n).mean (fun s => (∑ i, f (s i))^2) =
      (n : ℝ)*P.mean (fun ω => f ω^2) + (n : ℝ)*((n : ℝ)-1)*(P.mean f)^2 := by
    have he : (fun s : Fin n → Ω => (∑ i, f (s i))^2) =
        (fun s => ∑ i, ∑ j, f (s i)*f (s j)) := by
      funext s
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [he, mean_sum]
    simp_rw [mean_sum]
    have hpair (i j : Fin n) :
        (P.iid n).mean (fun s => f (s i)*f (s j)) =
          if j=i then P.mean (fun ω => f ω^2) else (P.mean f)^2 := by
      by_cases hji : j=i
      · subst j
        rw [if_pos rfl]
        have he : (fun s : Fin n → Ω => f (s i)*f (s i)) =
            (fun s => f (s i)^2) := by
          funext s; exact (pow_two (f (s i))).symm
        rw [he]
        exact iid_mean_coordinate P n i (fun ω => f ω^2)
      · rw [if_neg hji, iid_mean_two_coordinates P n i j f f (Ne.symm hji), pow_two]
    simp_rw [hpair]
    have hsum (i : Fin n) :
        (∑ j : Fin n, if j=i then P.mean (fun ω => f ω^2) else (P.mean f)^2) =
          (n : ℝ)*(P.mean f)^2 + (P.mean (fun ω => f ω^2)-(P.mean f)^2) := by
      have he (j : Fin n) :
          (if j=i then P.mean (fun ω => f ω^2) else (P.mean f)^2) =
            (P.mean f)^2 + if j=i then P.mean (fun ω => f ω^2)-(P.mean f)^2 else 0 := by
        by_cases h : j=i <;> simp [h] <;> ring
      simp_rw [he]
      simp [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    simp_rw [hsum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  refine ⟨hmean, ?_⟩
  have hscale : (P.iid n).mean (fun s => ((∑ i, f (s i))/(n : ℝ))^2) =
      (P.iid n).mean (fun s => (∑ i, f (s i))^2)/(n : ℝ)^2 := by
    simp only [div_pow]
    exact mean_div_const (P.iid n) (fun s => (∑ i, f (s i))^2) ((n : ℝ)^2)
  unfold FiniteLaw.variance
  rw [hmean, hscale, hsecond]
  field_simp <;> ring

/-- T18(d), exact fixed-n moments in the printed proof of (9), p. 63:
E[1-Ybar]=1-μp and Var(1-Ybar)=μp(1-μp)/n under the maintained model. -/
theorem direct_sample_moments (S : Study Ω) (hs : S.standing) (n : ℕ) (hn : 0 < n) :
    (S.law.iid n).mean S.sampleA = 1-S.mu*S.truthRate ∧
    (S.law.iid n).variance S.sampleA = (S.mu*S.truthRate)*(1-S.mu*S.truthRate)/(n : ℝ) := by
  let r := S.law.prob (fun ω => S.Y ω = true)
  let g := fun ω => 1-bitVal (S.Y ω)
  have hg : S.law.mean g = 1-r := by
    dsimp [g, r]; rw [mean_sub, mean_const, mean_bit]
  have hg2 : (fun ω => (g ω)^2) = g := by
    funext ω; cases h : S.Y ω <;> simp [g, bitVal, h]
  have hgv : S.law.variance g = r*(1-r) := by
    unfold FiniteLaw.variance; rw [hg2, hg]; ring
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have he : @Study.sampleA Ω _ S n = (fun s => (∑ i, g (s i))/(n : ℝ)) := by
    funext s
    simp [Study.sampleA, Study.ybar, g, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp <;> ring
  rw [he]
  have hm := iid_average_moments S.law n hn g
  rw [hg, hgv] at hm
  simpa only [r, direct_response_probability S hs.1 hs.2.2.2] using hm

/-- T18(e), T19(b) and T20(c), exact identified population contrast:
the negative-answer list difference is μ(1-p)/(1-μp), and its complement
is (1-μ)/(1-μp). This is the finite relation used in (3), pp. 49,63-64. -/
theorem nonconfessor_population_contrast (S : Study Ω) (hs : S.standing) :
    S.listMean true false-S.listMean false false =
      ((1-S.truthRate)*S.mu)/(1-S.mu*S.truthRate) ∧
    1-(S.listMean true false-S.listMean false false) =
      (1-S.mu)/(1-S.mu*S.truthRate) := by
  have hp := regularity_probabilities S hs.2.2.2
  have hq : 1-S.mu*S.truthRate ≠ 0 := by
    rw [← direct_response_probability S hs.1 hs.2.2.2]
    have h := ne_of_gt (hp.2 false); rw [prob_false] at h; exact h
  have hid : S.mu = S.mu*S.truthRate + (1-S.mu*S.truthRate)*
      (S.listMean true false-S.listMean false false) := by
    conv_lhs => rw [prevalence_identity S hs]; unfold Study.combined
    rw [mean_sub, mean_const, mean_bit, direct_response_probability S hs.1 hs.2.2.2]
  constructor
  · apply (eq_div_iff hq).2; nlinarith [hid]
  · apply (eq_div_iff hq).2; nlinarith [hid]

/-- T10(b) and T21(c), exact pointwise identity reducing the response
residuals to the stated placebo influence. It uses the list equation
and no false confessions on each atom of positive probability. -/
theorem placebo_influence_residual (S : Study Ω) (hs : S.standing) (ω : Ω)
    (hω : 0 < S.law.mass ω) :
    let q := S.law.prob (fun t => S.Y t = true)
    let m := S.law.ce (fun t => (S.W t : ℝ)) (fun t => S.Y t = true)
    bitVal (S.Y ω)*bitVal (S.Z ω)/(q*S.gamma)*((S.V ω : ℝ)-m-1) -
      bitVal (S.Y ω)*(1-bitVal (S.Z ω))/(q*(1-S.gamma))*((S.V ω : ℝ)-m) =
        S.betaPsi ω := by
  dsimp only
  have hp := regularity_probabilities S hs.2.2.2
  have hq := ne_of_gt (hp.2 true)
  have hg : S.gamma ≠ 0 := ne_of_gt (hp.1 true)
  have hg0 : 1-S.gamma ≠ 0 := by
    have h := ne_of_gt (hp.1 false); rw [prob_false] at h; exact h
  cases hy : S.Y ω
  · simp [Study.betaPsi, bitVal, hy]
  · have hx := hs.1 ω hω hy
    rw [hs.2.1 ω hω]
    cases hz : S.Z ω <;> simp [Study.betaPsi, bitVal, hy, hx, hz] <;> field_simp <;> ring


/-- Conditional variance is unchanged by an additive constant. This is
the exact list-versus-baseline variance step for confessors in the proof
of Proposition 2, printed p. 64. -/
theorem conditional_variance_shift (P : FiniteLaw Ω) (f : Ω → ℝ)
    (D : Ω → Prop) [DecidablePred D] (hD : P.prob D ≠ 0) (c : ℝ) :
    P.cv (fun ω => f ω+c) D = P.cv f D := by
  have he : (fun ω => (f ω+c)^2) = (fun ω => f ω^2+f ω*(2*c)+c^2) := by
    funext ω; ring
  unfold FiniteLaw.cv
  rw [he, ce_add, ce_add, ce_mul_const, ce_const P (c^2) D hD,
    ce_add, ce_const P c D hD]
  ring

/-- Conditional variance respects equality on positive-mass atoms
inside the conditioning event, used for the printed list equation. -/
theorem conditional_variance_congr_support (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (D : Ω → Prop) [DecidablePred D]
    (h : ∀ ω, 0 < P.mass ω → D ω → f ω=g ω) : P.cv f D = P.cv g D := by
  have hmean := ce_congr_support P f g D h
  have hsecond := ce_congr_support P (fun ω => f ω^2) (fun ω => g ω^2) D
    (by intro ω hω hD; rw [h ω hω hD])
  unfold FiniteLaw.cv
  rw [hmean, hsecond]

/-- T20(c,f): confessors' conditional list variance in either arm
is Var(W|Y=1), since V=W+z and treatment is independent of the whole
baseline-response triple. This is an actual population identity. -/
theorem confessor_cell_variance (S : Study Ω) (hs : S.standing) (z : Bool) :
    S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z true) =
      S.law.cv (fun ω => (S.W ω : ℝ)) (fun ω => S.Y ω = true) := by
  have hD := ne_of_gt (hs.2.2.2.1 z true).1
  have he : S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z true) =
      S.law.cv (fun ω => (S.W ω : ℝ)+bitVal z) (S.cell z true) := by
    apply conditional_variance_congr_support
    intro ω hω hz
    have hx := hs.1 ω hω hz.2
    rw [hs.2.1 ω hω, hx, hz.1]
    simp [bitVal]
  rw [he, conditional_variance_shift S.law (fun ω => (S.W ω : ℝ))
    (S.cell z true) hD (bitVal z)]
  unfold FiniteLaw.cv
  rw [ce_cell_independent S hs.2.2.1 (fun w _ _ => (w : ℝ)^2) z true hD,
    ce_cell_independent S hs.2.2.1 (fun w _ _ => (w : ℝ)) z true hD]

/-- Exact conditional mean decomposition over Y within either arm,
Proposition 2 proof, printed p. 64. Treatment independence makes the
within-arm mixing weight r=Pr(Y=1), including for V and V². -/
theorem conditional_arm_split (S : Study Ω) (hs : S.standing) (z : Bool) (f : Ω → ℝ) :
    let r := S.law.prob (fun ω => S.Y ω = true)
    S.law.ce f (fun ω => S.Z ω = z) =
      r*S.law.ce f (S.cell z true)+(1-r)*S.law.ce f (S.cell z false) := by
  dsimp only
  let α := S.law.prob (fun ω => S.Z ω = z)
  let r := S.law.prob (fun ω => S.Y ω = true)
  have hp := regularity_probabilities S hs.2.2.2
  have hα : α ≠ 0 := ne_of_gt (hp.1 z)
  have hr : r ≠ 0 := ne_of_gt (hp.2 true)
  have hr0 : 1-r ≠ 0 := by
    have h := ne_of_gt (hp.2 false); rw [prob_false] at h; exact h
  have hc1 : S.law.prob (S.cell z true) = α*r := cell_probability S hs.2.2.1 z true
  have hc0 : S.law.prob (S.cell z false) = α*(1-r) := by
    rw [cell_probability S hs.2.2.1 z false, prob_false]
  have he : S.law.mean (fun ω => if S.Z ω=z then f ω else 0) =
      S.law.mean (fun ω => if S.cell z true ω then f ω else 0) +
      S.law.mean (fun ω => if S.cell z false ω then f ω else 0) := by
    rw [← mean_add]
    apply mean_congr_support
    intro ω _
    cases hy : S.Y ω <;> by_cases hz : S.Z ω=z <;> simp [Study.cell, hy, hz]
  unfold FiniteLaw.ce
  rw [hc1, hc0, he]
  change (_+_)/α = r*(_/(α*r))+(1-r)*(_/(α*(1-r)))
  field_simp <;> ring

/-- T20(a,b), exact law of total variance over the binary direct answer
within an arm, printed p. 64. Its between-stratum contribution is the
actual squared difference of conditional list means. -/
theorem conditional_arm_variance (S : Study Ω) (hs : S.standing) (z : Bool) (f : Ω → ℝ) :
    let r := S.law.prob (fun ω => S.Y ω = true)
    S.law.cv f (fun ω => S.Z ω = z) =
      r*S.law.cv f (S.cell z true)+(1-r)*S.law.cv f (S.cell z false) +
      r*(1-r)*(S.law.ce f (S.cell z true)-S.law.ce f (S.cell z false))^2 := by
  dsimp only
  unfold FiniteLaw.cv
  rw [conditional_arm_split S hs z (fun ω => f ω^2), conditional_arm_split S hs z f]
  ring

/-- T20(a,e,f), the full finite population comparison underlying
Proposition 2, pp. 64-65 and finding P019-E003. This states the
actual population variance gap, beyond the already proved algebra for
abstract component moments. -/
theorem population_efficiency_gap (S : Study Ω) (hs : S.standing) :
    let r := S.mu*S.truthRate
    let q := 1-r
    let τ := S.law.cv (fun ω => (S.W ω : ℝ)) (fun ω => S.Y ω = true)
    let u := S.listMean false true-S.listMean false false
    let c := (1-S.mu)/q
    S.standardSigmaSq-S.sigmaSq =
      r*τ/(S.gamma*(1-S.gamma)) + r*q*(u+(1-S.gamma)*c)^2/(S.gamma*(1-S.gamma)) ∧
    S.sigmaSq < S.standardSigmaSq := by
  dsimp only
  let r := S.mu*S.truthRate
  let q := 1-r
  let τ := S.law.cv (fun ω => (S.W ω : ℝ)) (fun ω => S.Y ω = true)
  let u := S.listMean false true-S.listMean false false
  let c := (1-S.mu)/q
  let s1 := S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false)
  let s0 := S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false)
  change S.standardSigmaSq-S.sigmaSq =
    r*τ/(S.gamma*(1-S.gamma))+r*q*(u+(1-S.gamma)*c)^2/(S.gamma*(1-S.gamma)) ∧
    S.sigmaSq < S.standardSigmaSq
  have hp := regularity_probabilities S hs.2.2.2
  have hr : 0 < r := by
    change 0 < S.mu*S.truthRate
    rw [← direct_response_probability S hs.1 hs.2.2.2]
    exact hp.2 true
  have hq : 0 < q := by
    have h := hp.2 false
    rw [prob_false, direct_response_probability S hs.1 hs.2.2.2] at h
    exact h
  have hg : 0 < S.gamma := hp.1 true
  have hg1 : S.gamma < 1 := by
    have h := hp.1 false; rw [prob_false] at h; exact sub_pos.mp h
  have ht : 0 < τ := by
    have h := (hs.2.2.2.1 false true).2
    rw [confessor_cell_variance S hs false] at h
    exact h
  have hc := (nonconfessor_population_contrast S hs).2
  change 1-(S.listMean true false-S.listMean false false)=c at hc
  have hb := placebo_one_identity S hs.1 hs.2.1 hs.2.2.1
    (ne_of_gt (hs.2.2.2.1 false true).1) (ne_of_gt (hs.2.2.2.1 true true).1)
  change S.listMean true true-S.listMean false true=1 at hb
  have hd : S.listMean true true-S.listMean true false=u+c := by
    change S.listMean true true-S.listMean true false =
      S.listMean false true-S.listMean false false+c
    nlinarith [hc,hb]
  have hm1 : S.law.cv (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω=true) =
      q*s1+r*τ+r*q*(u+c)^2 := by
    have h := conditional_arm_variance S hs true (fun ω => (S.V ω : ℝ))
    rw [direct_response_probability S hs.1 hs.2.2.2, confessor_cell_variance S hs true] at h
    change _ = r*τ+q*s1+r*q*(S.listMean true true-S.listMean true false)^2 at h
    rw [hd] at h
    linarith
  have hm0 : S.law.cv (fun ω => (S.V ω : ℝ)) (fun ω => S.Z ω=false) =
      q*s0+r*τ+r*q*u^2 := by
    have h := conditional_arm_variance S hs false (fun ω => (S.V ω : ℝ))
    rw [direct_response_probability S hs.1 hs.2.2.2, confessor_cell_variance S hs false] at h
    change _ = r*τ+q*s0+r*q*u^2 at h
    linarith
  have hstd : S.standardSigmaSq =
      (q*s1+r*τ+r*q*(u+c)^2)/S.gamma+(q*s0+r*τ+r*q*u^2)/(1-S.gamma) := by
    unfold Study.standardSigmaSq
    rw [hm1,hm0]
  have hsig : S.sigmaSq = q*(s1/S.gamma+s0/(1-S.gamma))+r*q*c^2 := by
    unfold Study.sigmaSq
    change ((1-S.mu)^2/q)*r+q*(s1/S.gamma+s0/(1-S.gamma)) =
      q*(s1/S.gamma+s0/(1-S.gamma))+r*q*c^2
    have hqn : q ≠ 0 := ne_of_gt hq
    have hfirst : ((1-S.mu)^2/q)*r = r*q*c^2 := by
      dsimp only [c]
      field_simp <;> ring
    rw [hfirst]
    ring
  rw [hstd,hsig]
  exact variance_gap_strict r q S.gamma s1 s0 τ u c hr (le_of_lt hq) hg hg1 ht

/-- Independence of the two Boolean indicators Y and Z, Section 4.2,
p. 51: every (z,y) joint probability factors into its marginal product.
This is marginal Y-Z independence, distinct from Assumption 3. -/
def Study.binaryIndependent (S : Study Ω) : Prop :=
  ∀ z y : Bool, S.law.prob (S.cell z y) =
    S.law.prob (fun ω => S.Z ω = z)*S.law.prob (fun ω => S.Y ω = y)

/-- Exact two-arm decomposition of a population mean, used in the
binary characterization of Placebo Test II, target T22. -/
theorem arm_mean_decomposition (S : Study Ω) (f : Ω → ℝ)
    (h0 : S.law.prob (fun ω => S.Z ω = false) ≠ 0)
    (h1 : S.law.prob (fun ω => S.Z ω = true) ≠ 0) :
    S.law.mean f =
      S.law.prob (fun ω => S.Z ω = true)*S.law.ce f (fun ω => S.Z ω = true) +
      S.law.prob (fun ω => S.Z ω = false)*S.law.ce f (fun ω => S.Z ω = false) := by
  have he : f = (fun ω => (if S.Z ω = true then f ω else 0) +
      (if S.Z ω = false then f ω else 0)) := by
    funext ω; cases h : S.Z ω <;> simp [h]
  conv_lhs => rw [he, mean_add]
  unfold FiniteLaw.ce
  field_simp <;> ring

/-- T22(b), exact binary null characterization: with both arms defined,
δ=0 iff Y is independent of Z. It does not imply full (W,X,Y)-Z
independence; the separate T7 counterexample disproves that implication. -/
theorem binary_null_characterization (S : Study Ω)
    (h0 : S.law.prob (fun ω => S.Z ω = false) ≠ 0)
    (h1 : S.law.prob (fun ω => S.Z ω = true) ≠ 0) :
    S.delta = 0 ↔ S.binaryIndependent := by
  let r := S.law.prob (fun ω => S.Y ω = true)
  have hcell (z : Bool) :
      S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = z) =
        S.law.prob (S.cell z true)/S.law.prob (fun ω => S.Z ω = z) := by
    unfold FiniteLaw.ce FiniteLaw.prob
    congr 1
    apply mean_congr_support
    intro ω _
    cases hz : S.Z ω <;> cases hy : S.Y ω <;> cases z <;>
      simp [Study.cell, bitVal, hz, hy]
  have hfalse (z : Bool) : S.law.prob (S.cell z false) =
      S.law.prob (fun ω => S.Z ω = z)-S.law.prob (S.cell z true) := by
    unfold FiniteLaw.prob
    rw [← mean_sub]
    apply mean_congr_support
    intro ω _
    cases hz : S.Z ω <;> cases hy : S.Y ω <;> cases z <;>
      simp [Study.cell, hz, hy]
  constructor
  · intro hd
    have heq : S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = true) =
        S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = false) := sub_eq_zero.mp hd
    have hm := arm_mean_decomposition S (fun ω => bitVal (S.Y ω)) h0 h1
    rw [mean_bit, heq, prob_false] at hm
    have hmean0 : S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = false) = r := by
      dsimp [r]; nlinarith [hm]
    have hmean1 : S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = true) = r := by
      rw [heq]; exact hmean0
    intro z y
    have hmean : S.law.ce (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = z) = r := by
      cases z <;> assumption
    have hz : S.law.prob (fun ω => S.Z ω = z) ≠ 0 := by cases z <;> assumption
    rw [hcell] at hmean
    have ht := (div_eq_iff hz).mp hmean
    cases y
    · rw [hfalse, prob_false]
      dsimp [r] at ht
      nlinarith
    · dsimp [r] at ht
      nlinarith
  · intro hi
    unfold Study.delta
    rw [hcell, hcell, hi true true, hi false true]
    field_simp <;> ring

/-- Ratio-difference influence used for Placebo Tests I and II,
pp. 50-51: each cell's centered residual is divided by its probability,
and the control-cell term is subtracted. The cells are required to be
disjoint and defined in the moment theorem below. -/
def FiniteLaw.contrastInfluence (P : FiniteLaw Ω) (f : Ω → ℝ)
    (D1 D0 : Ω → Prop) [DecidablePred D1] [DecidablePred D0] (ω : Ω) : ℝ :=
  (if D1 ω then f ω-P.ce f D1 else 0)/P.prob D1 -
    (if D0 ω then f ω-P.ce f D0 else 0)/P.prob D0

/-- Exact moments of the residual influence for a difference of two
ratio means. Disjoint cells give no cross term, so the variance is
Var(f|D1)/Pr(D1)+Var(f|D0)/Pr(D0). This is the finite calculation behind
the first-order variances of Propositions 3-4, pp. 50-51. -/
theorem contrast_influence_moments (P : FiniteLaw Ω) (f : Ω → ℝ)
    (D1 D0 : Ω → Prop) [DecidablePred D1] [DecidablePred D0]
    (h1 : P.prob D1 ≠ 0) (h0 : P.prob D0 ≠ 0)
    (hd : ∀ ω, D1 ω → ¬ D0 ω) :
    P.mean (P.contrastInfluence f D1 D0) = 0 ∧
    P.variance (P.contrastInfluence f D1 D0) = P.cv f D1/P.prob D1 + P.cv f D0/P.prob D0 := by
  have hm1 := masked_central_moments P f D1 h1
  have hm0 := masked_central_moments P f D0 h0
  have hm : P.mean (P.contrastInfluence f D1 D0) = 0 := by
    unfold FiniteLaw.contrastInfluence
    rw [mean_sub, mean_div_const, mean_div_const, hm1.1, hm0.1]
    simp
  have he : (fun ω => (P.contrastInfluence f D1 D0 ω)^2) =
      (fun ω => (if D1 ω then (f ω-P.ce f D1)^2 else 0)/(P.prob D1)^2 +
        (if D0 ω then (f ω-P.ce f D0)^2 else 0)/(P.prob D0)^2) := by
    funext ω
    by_cases hD1 : D1 ω
    · have hD0 := hd ω hD1
      simp [FiniteLaw.contrastInfluence, hD1, hD0, div_pow]
    · by_cases hD0 : D0 ω <;>
        simp [FiniteLaw.contrastInfluence, hD1, hD0, div_pow]
  refine ⟨hm, ?_⟩
  unfold FiniteLaw.variance
  rw [hm, he, mean_add, mean_div_const, mean_div_const, hm1.2, hm0.2]
  field_simp <;> ring

/-- T21(c): the actual placebo-I influence ψ has mean zero and variance
Var(V|Z=1,Y=1)/(qγ)+Var(V|Z=0,Y=1)/(q(1-γ)), q=Pr(Y=1), under the
printed maintained model. This is a finite moment identity; studentized limits
and variance-estimator consistency are separate assertions. -/
theorem placebo_influence_moments (S : Study Ω) (hs : S.standing) :
    S.law.mean S.betaPsi = 0 ∧
    S.law.variance S.betaPsi =
      S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true true)/
        (S.law.prob (fun ω => S.Y ω = true)*S.gamma) +
      S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false true)/
        (S.law.prob (fun ω => S.Y ω = true)*(1-S.gamma)) := by
  let q := S.law.prob (fun ω => S.Y ω = true)
  let m := S.law.ce (fun ω => (S.W ω : ℝ)) (fun ω => S.Y ω = true)
  let ψ := S.law.contrastInfluence (fun ω => (S.V ω : ℝ)) (S.cell true true) (S.cell false true)
  have hp := regularity_probabilities S hs.2.2.2
  have hq : q ≠ 0 := ne_of_gt (hp.2 true)
  have hg : S.gamma ≠ 0 := ne_of_gt (hp.1 true)
  have hg0 : 1-S.gamma ≠ 0 := by
    have h := ne_of_gt (hp.1 false); rw [prob_false] at h; exact h
  have hmz (z : Bool) : S.listMean z true = m+bitVal z := by
    rw [list_mean_identified S hs.2.1 hs.2.2.1 z true
      (ne_of_gt (hs.2.2.2.1 z true).1),
      monotone_yes_mean S hs.1 (by exact hq)]
    simp [m]
  have hpc1 : S.law.prob (S.cell true true) = q*S.gamma := by
    rw [cell_probability S hs.2.2.1 true true]; dsimp [q, Study.gamma]; ring
  have hpc0 : S.law.prob (S.cell false true) = q*(1-S.gamma) := by
    rw [cell_probability S hs.2.2.1 false true, prob_false]
    dsimp [q, Study.gamma]; ring
  have hψ : ∀ ω, 0 < S.law.mass ω → S.betaPsi ω = ψ ω := by
    intro ω hω
    change bitVal (S.Y ω)/q*((bitVal (S.Z ω)-S.gamma)/(S.gamma*(1-S.gamma)))*
      ((S.W ω : ℝ)-m) =
      (if S.cell true true ω then (S.V ω : ℝ)-S.listMean true true else 0)/
        S.law.prob (S.cell true true) -
      (if S.cell false true ω then (S.V ω : ℝ)-S.listMean false true else 0)/
        S.law.prob (S.cell false true)
    rw [hpc1, hpc0, hmz true, hmz false]
    cases hy : S.Y ω
    · simp [bitVal, Study.cell, hy]
    · have hx := hs.1 ω hω hy
      rw [hs.2.1 ω hω]
      cases hz : S.Z ω <;> simp [bitVal, Study.cell, hy, hx, hz] <;> field_simp <;> ring
  have hmean := mean_congr_support S.law S.betaPsi ψ hψ
  have hsecond : S.law.mean (fun ω => (S.betaPsi ω)^2) = S.law.mean (fun ω => (ψ ω)^2) := by
    apply mean_congr_support
    intro ω hω; rw [hψ ω hω]
  have hvar : S.law.variance S.betaPsi = S.law.variance ψ := by
    unfold FiniteLaw.variance; rw [hmean, hsecond]
  have hmom := contrast_influence_moments S.law (fun ω => (S.V ω : ℝ))
    (S.cell true true) (S.cell false true)
    (ne_of_gt (hs.2.2.2.1 true true).1) (ne_of_gt (hs.2.2.2.1 false true).1)
    (by intro ω ht hf; exact Bool.false_ne_true (hf.1.symm.trans ht.1))
  rw [hmean, hvar]
  simpa only [hpc1, hpc0, q] using hmom

/-- The influence for δhat, Proposition 4, p. 51: the centered
answer in each arm divided by its arm probability, with control
subtracted. This is the exact ratio-difference influence representation. -/
def Study.deltaPsi (S : Study Ω) : Ω → ℝ :=
  S.law.contrastInfluence (fun ω => bitVal (S.Y ω))
    (fun ω => S.Z ω = true) (fun ω => S.Z ω = false)

/-- T22(c): the direct-question difference influence has zero mean and
variance Var(Y|Z=1)/γ+Var(Y|Z=0)/(1-γ). Thus its IID average has the
specified first-order variance divided by n, by iid_average_moments.
This statement requires only defined arms, not Assumptions 1 or 2. -/
theorem direct_influence_moments (S : Study Ω)
    (h0 : S.law.prob (fun ω => S.Z ω = false) ≠ 0)
    (h1 : S.law.prob (fun ω => S.Z ω = true) ≠ 0) :
    S.law.mean S.deltaPsi = 0 ∧
    S.law.variance S.deltaPsi =
      S.law.cv (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = true)/S.gamma +
      S.law.cv (fun ω => bitVal (S.Y ω)) (fun ω => S.Z ω = false)/(1-S.gamma) := by
  have h := contrast_influence_moments S.law (fun ω => bitVal (S.Y ω))
    (fun ω => S.Z ω = true) (fun ω => S.Z ω = false) h1 h0
    (by intro ω ht hf; exact Bool.false_ne_true (hf.symm.trans ht))
  simpa only [Study.deltaPsi, Study.gamma, prob_false] using h


/-- Appendix C, supplement p. 2: "The treatment list responses for
Liars and False Confessors were set equal to their control list responses."
This is the response rule in the printed Monte Carlo mechanism, T16. -/
def unchangedTreatment (w : Fin 5) : ℝ := (w.val : ℝ)

/-- T16: under either the printed liar or false-confessor response rule,
the individual treatment-minus-control list increment is exactly zero.
This is a response-rule identity, not a claim about Monte Carlo power. -/
theorem unchanged_response_increment (w : Fin 5) :
    unchangedTreatment w-(w.val : ℝ)=0 := by simp [unchangedTreatment]

end
end AronowAudit.P019

