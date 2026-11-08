import Mathlib
import SAP.P002a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P002a
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
attribute [local instance] Classical.propDecidable

universe u

/-- The covariate second-moment matrix, without an intercept. -/
def covariateGram {n k : ℕ} (x : Fin n → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun s t => mean (fun i => x i s * x i t)

/-- The least unit-vector Rayleigh value of the augmented Gram. All uses below have
positive sample size and positive covariate dimension, so the defining set is nonempty
and bounded below by zero. -/
def augmentedLeastRayleigh {n k : ℕ} (x : Fin n → Fin k → ℝ) : ℝ :=
  sInf {t | ∃ b : Option (Fin k) → ℝ, normSq b = 1 ∧
    mean (fun i => (dotProduct (augmented x i) b)^2) = t}

/-- Balanced all-complier exact-fit family: the response and sole covariate are the
same vector, with `m` entries -1 followed by `m` entries +1. -/
def T7ExactFitModel (m : ℕ) : CovPopulation (2*m) 1 :=
  ⟨signModel m, fun i _ => (signModel m).y i false⟩

/-- Intercept zero and sole slope one. -/
def T7ExactFitCoefficient : Option (Fin 1) → ℝ
  | none => 0
  | some _ => 1

/-- Conditional E.58 probability. The event uses the printed non-strict inequality;
this definition contains no variance quotient. -/
def E58Probability {n k : ℕ} (P : CovPopulation n k) (S : Finset (Fin n)) (κ : ℝ) : ℝ :=
  let q := observedW P.pop (late P.pop) S
  probability P.pop (fun T => |adjustedTau P q T - oracleStar P q T| ≥
    κ * Real.sqrt (designVariance P.pop (oracleStar P q)))

/-- Finite certificate for the balanced exact-fit counterexample. -/
def T7FiniteCounterexample : Prop :=
  ∀ m : ℕ, 0 < m →
    let P := T7ExactFitModel m
    Xi P 0 1 1 1 (1/2) ∧ late P.pop = 0 ∧
    (∀ a : Bool,
      popVar (w P.pop a (late P.pop)) = ((2*m : ℕ) : ℝ) / (((2*m : ℕ) : ℝ)-1) ∧
      0 < popVar (w P.pop a (late P.pop))) ∧
    (∀ a : Bool, psi P a (late P.pop) = T7ExactFitCoefficient ∧
      residual P a (late P.pop) = 0) ∧
    (∀ S : Finset (Fin (2*m)),
      let q := observedW P.pop (late P.pop) S
      q = (fun i => P.x i 0) ∧
      ols P.x Finset.univ q = T7ExactFitCoefficient ∧
      (∀ T : Finset (Fin (2*m)), oracleStar P q T = 0) ∧
      designVariance P.pop (oracleStar P q) = 0 ∧
      ∀ κ : ℝ, 0 < κ → E58Probability P S κ = 1)

/-- The printed claim is false: P002-T7; Supplement p. 42 (Supplement PDF p. 22),
Lemma 20, (E.58)-(E.61), with the corrected infeasible-statistic denominator in (E.61).
For every positive m, the balanced 2m-unit all-complier model with identical sign
responses and covariate belongs to Xi(0,1,1,1,1/2), has positive unprojected arm
variances and zero population OLS residuals. Every observed response has pooled
coefficients (0,1), zero oracle reassignment statistic and zero oracle variance.
Consequently the E.58 probability is one for every positive threshold. Along the
strictly increasing sizes 2(j+1), for every path of original assignments this probability
tends to one and does not tend to zero. Thus the canonical four-limit assertion fails,
independently of any convention for a zero variance quotient. -/
def T7WholeStatement : Prop :=
  T7FiniteCounterexample ∧
  StrictMono (fun j : ℕ => 2*(j+1)) ∧
  (∀ (S : ∀ j : ℕ, Finset (Fin (2*(j+1)))) (κ : ℝ), 0 < κ →
    Tendsto (fun j => E58Probability (T7ExactFitModel (j+1)) (S j) κ) atTop (nhds 1) ∧
    ¬Tendsto (fun j => E58Probability (T7ExactFitModel (j+1)) (S j) κ) atTop (nhds 0))

/-- The paper labels units starting at one: the value at Lean index i is
`2*(-1)^(i+1)`, so consecutive pairs are (-2,+2). -/
def T8AlternatingX (m : ℕ) (i : Fin (2*m)) (_ : Fin 1) : ℝ :=
  2 * (-1 : ℝ)^(i.val+1)

/-- P002-T8; Supplement p. 42 (Supplement PDF p. 22), first display;
Assumption 5(v), main p. 11.
For every positive even size 2m, the covariate x_i=2(-1)^i is centered, has fourth
moment 16, and has covariate Gram [4] with smallest eigenvalue 4, at least 2.
Its augmented Gram is diag(1,4) with smallest eigenvalue 1. The unit intercept
vector has quadratic form 1<2, refuting the covariate-to-augmented-Gram implication.
This is a counterexample to that implication, as asserted by the canonical target. -/
def T8WholeStatement : Prop :=
  ∀ m : ℕ, 0 < m →
    let x := T8AlternatingX m
    (∀ s, ∑ i, x i s = 0) ∧
    (∀ s, mean (fun i => x i s^4) = 16 ∧ mean (fun i => x i s^4) ≤ 16) ∧
    covariateGram x = (fun _ _ => 4) ∧ leastRayleigh x = 4 ∧
    (2 : ℝ) ≤ leastRayleigh x ∧
    (∀ b : Fin 1 → ℝ, 2*normSq b ≤ mean (fun i => (dotProduct (x i) b)^2)) ∧
    gram x Finset.univ = Matrix.diagonal (fun j : Option (Fin 1) =>
      match j with | none => 1 | some _ => 4) ∧
    augmentedLeastRayleigh x = 1 ∧
    let b : Option (Fin 1) → ℝ := fun j => if j = none then 1 else 0
    normSq b = 1 ∧ dotProduct b (gram x Finset.univ *ᵥ b) = 1 ∧
    dotProduct b (gram x Finset.univ *ᵥ b) < 2*normSq b

/-- The full finite Gram and spectral conclusions. The positive dimension ensures the
covariate unit sphere is nonempty; positive size makes every population mean genuine. -/
def T9WholeFinite : Prop :=
  ∀ {n k : ℕ} (x : Fin n → Fin k → ℝ) (hn : 0 < n) (hk : 0 < k)
    (e : ℝ) (he : 0 < e) (hx : ∀ s, ∑ i, x i s = 0)
    (hRay : e ≤ leastRayleigh x),
  (gram x Finset.univ) none none = 1 ∧
    (∀ s, (gram x Finset.univ) none (some s) = 0 ∧
      (gram x Finset.univ) (some s) none = 0) ∧
    (∀ s t, (gram x Finset.univ) (some s) (some t) = covariateGram x s t) ∧
    augmentedLeastRayleigh x = min 1 (leastRayleigh x) ∧
    min 1 e ≤ augmentedLeastRayleigh x ∧
    (∀ b : Option (Fin k) → ℝ,
      min 1 e * normSq b ≤ dotProduct b (gram x Finset.univ *ᵥ b))

/-- Marginal-only sequence version of the corrected coefficient-error inequality.
One common error works for both arms, along each fixed strict subsequence. -/
def T9WholeSequence : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ n, CovPopulation (sizes n) k)
    (Z : ∀ n, Ω → Finset (Fin (sizes n))) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hP : ∀ n, Xi (P n) δ e A B r)
    (hZ : RandomizationSequence (fun n => (P n).pop) μ Z)
    (sub : ℕ → ℕ) (hsub : StrictMono sub),
  ∀ᵐ ω ∂μ, ∃ err : ℕ → ℝ, Tendsto err atTop (nhds 0) ∧
    ∀ᶠ j in atTop, ∀ a : Bool,
      let N := sub j
      let S := Z N ω
      let q := observedW (P N).pop (late (P N).pop) S
      let b := fitted (P N) q S a - ols (P N).x Finset.univ q
      (min 1 e + err j) * normSq b ≤
        dotProduct b (gram (P N).x (if a then S else Sᶜ) *ᵥ b)

/-- P002-T9; Supplement p. 42 (Supplement PDF p. 22), first display, corrected.
Centered covariates give population augmented Gram diag(1,C), smallest eigenvalue
min(1,lambda_min(C)) at least min(1,e), and the corresponding quadratic bound for
every vector. For Xi sequences with fixed positive dimension and constants, every
measurable coupling of the exact complete-randomization marginals satisfies, almost
surely along each fixed strictly increasing subsequence, the corrected coefficient-error
bound with one vanishing error for both arms. In particular this covers the paper's
independent coupling. -/
def T9WholeStatement : Prop := T9WholeFinite ∧ T9WholeSequence.{u}

/-- The two additional exact cancellations in corrected (C.17). Positivity is needed
only where the claim divides by S_1 squared. -/
def T11WholeCancellation : Prop :=
  ∀ {n : ℕ} (P : Population n) (hP : ValidDesign P) (β : ℝ)
    (hS : 0 < S2 P β true),
  (∑ i, v P true β i^2) / S2 P β true =
      ((n : ℝ)-1) / ((fraction P)^2*(1-fraction P)^2) ∧
    expectation P (fun T => (groupMean T (w P true β) -
      mean (fun i => P.y i (P.d i true)) +
      β*mean (fun i => binary (P.d i true)))^2 / S2 P β true) =
      controlSize P / ((P.n1 : ℝ)*(n : ℝ)*(fraction P)^2*(1-fraction P)^2)

/-- P002-T11; Supplement p. 26 (Supplement PDF p. 6), identity before (C.17)
and corrected (C.17).
For every valid design and every beta, the treated sample-centering identity has
+beta times the population receipt mean, and its squared bracket has exact expectation
n0*sum(v_i^2)/(n1*n*(n-1)). When S_1 squared is positive, division gives the printed
normalized equality, sum(v_i^2)/S_1 squared=(n-1)/(pi^2*(1-pi)^2), and the simplified
expectation n0/(n1*n*pi^2*(1-pi)^2). Along increasing Theta sequences under fixed
balance and the stated denominator guard this expectation is O(n0/(n1*n)) and tends
to zero. The unnormalized finite identities need no variance positivity. -/
def T11WholeStatement : Prop :=
  T11Finite ∧ T11Normalized ∧ T11WholeCancellation ∧ T11Rate

/-- P002-T15; Supplement p. 30 (Supplement PDF p. 10), corrected Lemma 12.
For Theta sequences under the supplied Supplement p. 23 standing assumption that both
adjusted potential-outcome variances are positive, the corrected variance/variance
error probabilities tend to zero almost surely along every fixed strictly increasing
subsequence, simultaneously for all positive tolerances. Assignments may have any
measurable coupling of their exact complete-randomization marginals. No positivity
of every finite-size conditional variance is assumed; the proof obtains eventual
positivity almost surely, so any totalization at earlier zero denominators is immaterial. -/
def T15WholeStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ n, Population (sizes n))
    (Z : ∀ n, Ω → Finset (Fin (sizes n))) (δ r A : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A)
    (hP : ∀ n, Theta (P n) δ r A)
    (hpositive : ∀ n a, 0 < popVar (w (P n) a (late (P n))))
    (hZ : RandomizationSequence P μ Z)
    (sub : ℕ → ℕ) (hsub : StrictMono sub),
  ∀ᵐ ω ∂μ, ∀ κ : ℝ, 0 < κ → Tendsto (fun j =>
    let N := sub j
    let q := observedW (P N) (late (P N)) (Z N ω)
    probability (P N) (fun S => |rawSigma2 (P N) q S /
      designVariance (P N) (rawTau (P N) q) - 1| ≥ κ)) atTop (nhds 0)

end
end SAP.P002a
