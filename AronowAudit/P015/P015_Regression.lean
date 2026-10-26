import AronowAudit.P015.P015_LogisticTaylorCompletion
import AronowAudit.P015.P015_TaylorUniformCompletion
import Mathlib.Probability.Independence.Basic
import AronowAudit.P015.P015_FiniteConditioning
import AronowAudit.P015.P015_RandomizationKernelCompletion
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Fin.Basic
import AronowAudit.P015.P015_SchurCompletion
import AronowAudit.P015.P015_PopulationMomentCompletion
import AronowAudit.P015.P015_OLSCompletion
import Mathlib.Analysis.Calculus.Implicit
import AronowAudit.P015.P015_ConditionalKernelCompletion
import AronowAudit.P015.P015_TaylorCompletion
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.ConditionalProbability
import AronowAudit.P015.P015_MatrixCompletion
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Probability.CondVar
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace AronowAudit.P015

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

open scoped BigOperators Topology
open Finset Matrix MeasureTheory ProbabilityTheory Filter

/-! Regression weights, causal estimands, and counterexamples for
Aronow and Samii (2016), pp. 250–267.
All tables are exact real-valued finite probability laws, never a zero measure.
-/

/-- E[.] averages over the units in the population (p. 253, after (3)).
For a finite population law this is the weighted sum with atom probabilities p. -/
def fExpectation {A : Type*} [Fintype A] (p Z : A → ℝ) : ℝ := ∑ a, p a * Z a

/-- A finite probability law has nonnegative atom masses summing to one
(the finite super-population representation allowed on p. 252). -/
def IsLaw {A : Type*} [Fintype A] (p : A → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- Pr[A], the mass of an event, used by the positivity display (p. 261). -/
noncomputable def fMass {A : Type*} [Fintype A] (p : A → ℝ) (E : A → Prop) : ℝ :=
  ∑ a, if E a then p a else 0

/-- E[Z | X=x], the cell expectation at a represented covariate profile
(Expressions (3), (8), pp. 253, 255). -/
noncomputable def fCondMean {A B : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (Z : A → ℝ) (x : B) : ℝ :=
  fExpectation p (fun a => if X a = x then Z a else 0) / fMass p (fun a => X a = x)

/-- Pr[D=d | X=x], the pair-specific positivity display (p. 261). -/
noncomputable def fCondProb {A B : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (D : A → ℝ) (x : B) (d : ℝ) : ℝ :=
  fMass p (fun a => X a = x ∧ D a = d) / fMass p (fun a => X a = x)

/-- “w_i = (D_i - E[D_i|X_i])²”, Expression (7), p. 254. -/
noncomputable def fWeight {A B : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (D : A → ℝ) : A → ℝ :=
  fun a => (D a - fCondMean p X D (X a)) ^ 2

/-- The effective sample reweights by w_i (p. 255): Q(a)=p(a)w(a)/E[w]. -/
noncomputable def fEffective {A B : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (D : A → ℝ) : A → ℝ :=
  fun a => p a * fWeight p X D a / fExpectation p (fWeight p X D)

/-- Conditional independence in (2)/(11), pp. 253/260, on a finite law:
within each cell the joint conditional masses factor. -/
noncomputable def fCondIndep {A B C : Type*} [Fintype A]
    (p : A → ℝ) (X : A → B) (U : A → C) (D : A → ℝ) : Prop :=
  ∀ x u d, fMass p (fun a => X a = x ∧ U a = u ∧ D a = d) *
      fMass p (fun a => X a = x) =
    fMass p (fun a => X a = x ∧ U a = u) *
      fMass p (fun a => X a = x ∧ D a = d)

/-- Potential outcomes deterministic given X are unconfounded, as in the
counterexamples to p. 261 (P015-T1, T2). -/
theorem finite_unconfounded_algebra {A B C : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (g : B → C) (D : A → ℝ) :
    fCondIndep p X (fun a => g (X a)) D := by
  classical
  intro x u d
  by_cases h : g x = u
  · have h₁ : fMass p (fun a => X a = x ∧ g (X a) = u ∧ D a = d) =
        fMass p (fun a => X a = x ∧ D a = d) := by
      unfold fMass
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp_all
    have h₂ : fMass p (fun a => X a = x ∧ g (X a) = u) =
        fMass p (fun a => X a = x) := by
      unfold fMass
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp_all
    rw [h₁, h₂, mul_comm]
  · have h₁ : fMass p (fun a => X a = x ∧ g (X a) = u ∧ D a = d) = 0 := by
      unfold fMass
      apply Finset.sum_eq_zero
      intro a _
      split_ifs with ha
      · rcases ha with ⟨hx,hg,_⟩
        exact (h (by simpa [hx] using hg)).elim
      · rfl
    have h₂ : fMass p (fun a => X a = x ∧ g (X a) = u) = 0 := by
      unfold fMass
      apply Finset.sum_eq_zero
      intro a _
      split_ifs with ha
      · rcases ha with ⟨hx,hg⟩
        exact (h (by simpa [hx] using hg)).elim
      · rfl
    rw [h₁, h₂]; ring

/-- “tau_i(d,d') = (Y_i(d') - Y_i(d))/(d'-d)”, p. 260. -/
def contrast {A : Type*} (Y : A → ℝ → ℝ) (d d' : ℝ) : A → ℝ :=
  fun a => (Y a d' - Y a d) / (d' - d)

/-- The inverse-probability variable from P015-T1 uses only Y=Y(D) and
propensity e(X), as in the positivity discussion on pp. 260–261. -/
def ipw {A : Type*} (D Y e : A → ℝ) : A → ℝ :=
  fun a => D a * Y a / e a - (1 - D a) * Y a / (1 - e a)

/-- Variance is the expectation of the squared centered variable. -/
def fVariance {A : Type*} [Fintype A] (p Z : A → ℝ) : ℝ :=
  fExpectation p (fun a => (Z a - fExpectation p Z) ^ 2)

/-- The population least-squares coefficients, E[W'W]⁻¹E[W'Y], used for
T1(e)'s identity for Expression (7). -/
def populationOLS {A Q : Type*} [Fintype A] [Fintype Q] [DecidableEq Q]
    (p : A → ℝ) (W : Matrix A Q ℝ) (Y : A → ℝ) : Q → ℝ :=
  Matrix.mulVec (((fun j k => fExpectation p (fun i => W i j*W i k)) : Matrix Q Q ℝ)⁻¹)
    (fun j => fExpectation p (fun i => W i j*Y i))


/-- P015-T1's four atoms, in order (0,0),(0,1),(1,0),(1,1). -/
def binaryX : Fin 4 → ℝ := ![0,0,1,1]
/-- The binary treatment D_i in (1)–(4), pp. 253–254, at T1/T3's four explicit atoms. -/
def binaryD : Fin 4 → ℝ := ![0,1,0,1]
/-- T1's law: P(X=0)=P(X=1)=1/2 and P(D=1|X=0)=ε, P(D=1|X=1)=1/2; p. 261 counterexample. -/
def rareLaw (ε : ℝ) : Fin 4 → ℝ := ![(1-ε)/2, ε/2, 1/4, 1/4]
/-- T1's affine potential outcomes Y_i(d)=2X_i+(1+X_i)d, the form Y_i(d)=Y_i(0)+τ_i d of (1), p. 253. -/
def rareY (a : Fin 4) (d : ℝ) : ℝ := 2 * binaryX a + (1 + binaryX a) * d
/-- T1's observed-data IPW variable for the p. 261 positivity claim, formed from Y_i(D_i) and the stated propensity. -/
noncomputable def rareZ (ε : ℝ) : Fin 4 → ℝ :=
  ipw binaryD (fun a => rareY a (binaryD a))
    (fun a => ε + (1/2 - ε) * binaryX a)

/-- P015-T1 (a)–(e), p. 261 counterexample: strict positivity, tiny effective
mass, and exact observed-data IPW moments at ε=10⁻⁶. The n-draw bound is stated separately. -/
theorem rare_weight_counterexample :
    IsLaw (rareLaw (1/1000000)) ∧
    (∀ a d, rareY a d = rareY a 0 + (1 + binaryX a) * d) ∧
    fCondIndep (rareLaw (1/1000000)) binaryX
      (fun a => (rareY a 0, 1 + binaryX a)) binaryD ∧
    (∀ x ∈ ({0,1} : Finset ℝ),
      fCondMean (rareLaw (1/1000000)) binaryX binaryD x =
        1/1000000 + (1/2 - 1/1000000) * x ∧
      0 < fCondProb (rareLaw (1/1000000)) binaryX binaryD x 0 ∧
      0 < fCondProb (rareLaw (1/1000000)) binaryX binaryD x 1) ∧
    fCondMean (rareLaw (1/1000000)) binaryX
      (fWeight (rareLaw (1/1000000)) binaryX binaryD) 0 = 999999/1000000000000 ∧
    fCondMean (rareLaw (1/1000000)) binaryX
      (fWeight (rareLaw (1/1000000)) binaryX binaryD) 1 = 1/4 ∧
    fMass (rareLaw (1/1000000)) (fun a => binaryX a = 0) = 1/2 ∧
    fMass (fEffective (rareLaw (1/1000000)) binaryX binaryD)
      (fun a => binaryX a = 0) = 999999/250000999999 ∧
    (999999/250000999999 : ℝ) < 1/250000 ∧
    rareZ (1/1000000) = ![0,1000000,-4,8] ∧
    fExpectation (rareLaw (1/1000000)) (fun a => 1+binaryX a) = 3/2 ∧
    fExpectation (rareLaw (1/1000000)) (rareZ (1/1000000)) = 3/2 ∧
    fExpectation (rareLaw (1/1000000)) (fun a => rareZ (1/1000000) a ^ 2) = 500020 ∧
    fVariance (rareLaw (1/1000000)) (rareZ (1/1000000)) = 2000071/4 ∧
    fExpectation (fEffective (rareLaw (1/1000000)) binaryX binaryD)
      (fun a => 1+binaryX a) = 500000999999/250000999999 ∧
    (500000999999/250000999999 : ℝ) ≠ 3/2 := by
  have hi : fCondIndep (rareLaw (1/1000000)) binaryX
      (fun a => (rareY a 0, 1+binaryX a)) binaryD := by
    simpa [rareY] using finite_unconfounded_algebra (rareLaw (1/1000000)) binaryX
      (fun x => (2*x,1+x)) binaryD
  refine ⟨?_, ?_, hi, ?_, ?_⟩
  · constructor
    · intro a; fin_cases a <;> norm_num [rareLaw]
    · norm_num [rareLaw, Fin.sum_univ_succ]
  · intro a d; simp [rareY]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;>
      norm_num [fCondMean, fCondProb, fExpectation, fMass, rareLaw, binaryX,
        binaryD, Fin.sum_univ_succ]
  · norm_num [fCondMean, fCondProb, fExpectation, fMass, fWeight, fEffective,
      fVariance, rareLaw, rareZ, ipw, rareY, binaryX, binaryD, Fin.sum_univ_succ,
      funext_iff, Fin.forall_fin_succ]

/-- P015-T1's algebraic profile bound: for every 0<ε<1/2 the expression
ε(1-ε)/(ε(1-ε)+1/4) is positive and below 4ε. -/
theorem rare_profile_ratio_bound (ε : ℝ) (hε : 0 < ε) (hu : ε < 1/2) :
    0 < ε*(1-ε)/(ε*(1-ε)+1/4) ∧ ε*(1-ε)/(ε*(1-ε)+1/4) < 4*ε := by
  have hv : 0 < ε*(1-ε) := mul_pos hε (by linarith)
  have hd : 0 < ε*(1-ε)+1/4 := by linarith
  constructor
  · exact div_pos hv hd
  · apply (div_lt_iff₀ hd).2
    nlinarith [mul_pos hε hv]

/-- P015-T2's law: uniform on (0,0),(0,1),(1,0),(1,2). -/
def multiLaw : Fin 4 → ℝ := ![1/4,1/4,1/4,1/4]
/-- T2's multivalued treatment: supports {0,1} at X=0 and {0,2} at X=1; p. 261 counterexample. -/
def multiD : Fin 4 → ℝ := ![0,1,0,2]
/-- T2's first potential-outcome world Y_i(d)=d, under the unrestricted potential outcomes on p. 260. -/
def worldA (_ : Fin 4) (d : ℝ) : ℝ := d
/-- T2's second potential-outcome world changes only the unobserved Y_i(1) at X=1 to 3; p. 260–261. -/
def worldB (a : Fin 4) (d : ℝ) : ℝ := if binaryX a = 1 ∧ d = 1 then 3 else d

/-- P015-T2, p. 261: all weights are positive, both profiles remain represented
under Q, but D=1 is unsupported at X=1. Two unconfounded outcome worlds have
identical observed data and different nominal and effective contrasts. -/
theorem multivalued_support_counterexample :
    IsLaw multiLaw ∧
    (∀ a, fCondMean multiLaw binaryX multiD (binaryX a) = 1/2 + binaryX a/2) ∧
    fWeight multiLaw binaryX multiD = ![1/4,1/4,1,1] ∧
    (∀ a, 0 < fWeight multiLaw binaryX multiD a) ∧
    fExpectation multiLaw (fWeight multiLaw binaryX multiD) = 5/8 ∧
    fEffective multiLaw binaryX multiD = ![1/10,1/10,2/5,2/5] ∧
    fMass (fEffective multiLaw binaryX multiD) (fun a => binaryX a = 0) = 1/5 ∧
    fMass (fEffective multiLaw binaryX multiD) (fun a => binaryX a = 1) = 4/5 ∧
    fCondProb multiLaw binaryX multiD 1 1 = 0 ∧
    fCondProb (fEffective multiLaw binaryX multiD) binaryX multiD 1 1 = 0 ∧
    fCondIndep multiLaw binaryX (fun a => (worldA a 0, worldA a 1, worldA a 2)) multiD ∧
    fCondIndep multiLaw binaryX (fun a => (worldB a 0, worldB a 1, worldB a 2)) multiD ∧
    (∀ a, worldA a (multiD a) = multiD a ∧ worldB a (multiD a) = multiD a) ∧
    fExpectation multiLaw (contrast worldA 0 1) = 1 ∧
    fExpectation multiLaw (contrast worldB 0 1) = 2 ∧
    fExpectation (fEffective multiLaw binaryX multiD) (contrast worldA 0 1) = 1 ∧
    fExpectation (fEffective multiLaw binaryX multiD) (contrast worldB 0 1) = 13/5 := by
  have ha := finite_unconfounded_algebra multiLaw binaryX (fun _ => ((0 : ℝ),(1 : ℝ),(2 : ℝ))) multiD
  have hb := finite_unconfounded_algebra multiLaw binaryX
    (fun x => ((0 : ℝ), (if x = 1 then (3 : ℝ) else 1), (2 : ℝ))) multiD
  have hiA : fCondIndep multiLaw binaryX
      (fun a => (worldA a 0, worldA a 1, worldA a 2)) multiD := by
    simpa [worldA] using ha
  have hiB : fCondIndep multiLaw binaryX
      (fun a => (worldB a 0, worldB a 1, worldB a 2)) multiD := by
    simpa [worldB] using hb
  norm_num [IsLaw, fCondMean, fCondProb, fExpectation, fMass, fWeight,
    fEffective, multiLaw, multiD, binaryX, worldA, worldB, contrast,
    Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ, hiA, hiB]
  simpa [worldA,worldB,multiLaw,binaryX,multiD] using And.intro hiA hiB

/-- “hat w_i = tilde D_i²”, p. 255: square the actual treatment regression residual. -/
def sampleResidual {N Q : Type*} [Fintype Q] (V : Matrix N Q ℝ)
    (D : N → ℝ) (ω : Q → ℝ) : N → ℝ := fun i => D i - V.mulVec ω i



/-- P015-T3's size-four ordered sample (0,0),(0,0),(1,0),(1,1). -/
def zeroSampleV : Matrix (Fin 4) (Fin 2) ℝ := !![1,0; 1,0; 1,1; 1,1]
/-- T3's ordered sample design W_i=(1,D_i,X_i), Appendix A, p. 262. -/
def zeroSampleW : Matrix (Fin 4) (Fin 3) ℝ := !![1,0,0; 1,0,0; 1,0,1; 1,1,1]
/-- T3's realized treatment vector (0,0,0,1), the p. 261 fitted-zero counterexample. -/
def zeroSampleD : Fin 4 → ℝ := ![0,0,0,1]

/-- P015-T3, p. 261: a positive-probability sample has zero fitted weights
at X=0 even though the population has positivity and conditional variance 1/4.
The full regression Gram determinant is 2, so this is a defined regression. -/
theorem fitted_zero_counterexample :
    IsLaw multiLaw ∧
    (∀ x ∈ ({0,1} : Finset ℝ), ∀ d ∈ ({0,1} : Finset ℝ),
      fCondProb multiLaw binaryX binaryD x d = 1/2) ∧
    (∀ x ∈ ({0,1} : Finset ℝ),
      fCondMean multiLaw binaryX (fWeight multiLaw binaryX binaryD) x = 1/4) ∧
    (1/4 : ℝ)^4 = 1/256 ∧ (0 : ℝ) < 1/256 ∧
    zeroSampleV.transpose * zeroSampleV = !![4,2;2,2] ∧
    zeroSampleV.transpose.mulVec zeroSampleD = ![1,1] ∧
    (!![4,2;2,2] : Matrix (Fin 2) (Fin 2) ℝ).mulVec ![0,1/2] = ![1,1] ∧
    (zeroSampleV.transpose * zeroSampleV).det ≠ 0 ∧
    sampleResidual zeroSampleV zeroSampleD ![0,1/2] = ![0,0,-1/2,1/2] ∧
    (fun a => sampleResidual zeroSampleV zeroSampleD ![0,1/2] a ^ 2) = ![0,0,1/4,1/4] ∧
    zeroSampleW.transpose * zeroSampleW = !![4,1,2;1,1,1;2,1,2] ∧
    (zeroSampleW.transpose * zeroSampleW).det = 2 := by
  norm_num [IsLaw, fCondProb, fCondMean, fMass, fExpectation, fWeight, multiLaw,
    binaryX, binaryD, zeroSampleV, zeroSampleW, zeroSampleD, sampleResidual,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.det_fin_two, Matrix.det_fin_three, ← Matrix.ext_iff, Fin.sum_univ_succ,
    funext_iff, Fin.forall_fin_succ]


/-- “logit⁻¹(a)=[1+exp(-a)]⁻¹”, Appendix C, p. 265. -/
def logistic : ℝ → ℝ := Real.sigmoid
/-- “logit(P_Y)=log[P_Y/(1-P_Y)]”, Appendix C, p. 265. -/
def logit (p : ℝ) : ℝ := Real.log (p / (1-p))
/-- A first-order Taylor polynomial; the approximation in Appendix C, p. 265. -/
def firstTaylor (f : ℝ → ℝ) (c a : ℝ) : ℝ := f c + deriv f c * (a-c)

/-- The printed reciprocal inverse link equals exp(a)/(1+exp(a)). -/
theorem logistic_exp (a : ℝ) : logistic a = Real.exp a / (1+Real.exp a) := by
  unfold logistic
  rw [Real.sigmoid_def, Real.exp_neg]
  have h : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
  have h' : 1+Real.exp a ≠ 0 := by positivity
  field_simp <;> ring

/-- The inverse link is the inverse of logit on (0,1), Appendix C. -/
theorem logistic_logit (p : ℝ) (hp : 0 < p) (hu : p < 1) : logistic (logit p) = p := by
  have h : 0 < p/(1-p) := div_pos hp (by linarith)
  rw [logistic_exp, logit, Real.exp_log h]
  field_simp [ne_of_gt (show 0 < 1-p by linarith)]
  <;> ring

/-- P015-T13: the corrected Taylor display, its derivative and affine form,
and the exact P=1/2 witness against the misprinted denominator (p. 265). -/
theorem corrected_logistic_taylor (p : ℝ) (hp : 0 < p) (hu : p < 1) :
    (∀ a, HasDerivAt logistic (Real.exp a/(1+Real.exp a)^2) a) ∧
    logistic (logit p) = p ∧
    deriv logistic (logit p) = Real.exp (logit p)/(1+Real.exp (logit p))^2 ∧
    deriv logistic (logit p) = p*(1-p) ∧
    (∀ a, firstTaylor logistic (logit p) a = p+p*(1-p)*(a-logit p) ∧
      firstTaylor logistic (logit p) a = (p-p*(1-p)*logit p)+p*(1-p)*a) ∧
    logit (1/2) = 0 ∧
    Real.exp (logit (1/2))/(1+logit (1/2))^2 = 1 ∧
    deriv logistic (logit (1/2)) = 1/4 := by
  have hd : ∀ a, HasDerivAt logistic (Real.exp a/(1+Real.exp a)^2) a := by
    intro a
    have h := Real.hasDerivAt_sigmoid a
    change HasDerivAt logistic (logistic a*(1-logistic a)) a at h
    convert h using 1
    rw [logistic_exp]
    field_simp
    <;> ring
  have hi := logistic_logit p hp hu
  have hs : deriv logistic (logit p) = p*(1-p) := by
    have hraw := (Real.hasDerivAt_sigmoid (logit p)).deriv
    change deriv logistic (logit p) = logistic (logit p)*(1-logistic (logit p)) at hraw
    rwa [hi] at hraw
  refine ⟨hd, hi, (hd _).deriv, hs, ?_, ?_⟩
  · intro a
    simp only [firstTaylor, hi, hs]
    constructor
    · trivial
    · ring
  · norm_num [logit, logistic, Real.deriv_sigmoid]

/-- P015-T12(i), the local correction of p. 257: the approximation
is local, with a quadratic remainder at logit(P). No coefficient stability is asserted. -/
theorem local_logistic_remainder (p : ℝ) (hp : 0 < p) (hu : p < 1) :
    (fun a => logistic a - (p+p*(1-p)*(a-logit p))) =O[𝓝 (logit p)]
      (fun a => (a-logit p)^2) := by
  have hc : ContDiff ℝ 2 logistic := contDiff_sigmoid.of_le (by norm_num)
  have ht := (taylor_isLittleO_univ (x₀ := logit p) hc).isBigO
  let C : ℝ := iteratedDerivWithin 2 logistic Set.univ (logit p)/2
  have hC := (Asymptotics.isBigO_refl (fun a : ℝ => (a-logit p)^2) (𝓝 (logit p))).const_mul_left C
  have hd : deriv logistic (logit p) = p*(1-p) := (corrected_logistic_taylor p hp hu).2.2.2.1
  have h₁ : ∀ a, taylorWithinEval logistic 1 Set.univ (logit p) a = p+p*(1-p)*(a-logit p) := by
    intro a
    rw [taylorWithinEval_succ logistic 0 Set.univ (logit p) a]
    simp only [taylor_within_zero_eval, Nat.zero_add, Nat.cast_zero, zero_add, Nat.factorial_zero,
      Nat.cast_one, one_mul, inv_one, pow_one, smul_eq_mul, iteratedDerivWithin_one, derivWithin_univ]
    rw [logistic_logit p hp hu, hd]
    norm_num
    <;> ring
  convert ht.add hC using 1
  ext a
  rw [taylorWithinEval_succ logistic 1 Set.univ (logit p) a, h₁]
  simp [C, smul_eq_mul]
  <;> ring

/-- The Bernoulli likelihood, the standard likelihood underlying Appendix C,
p. 265. Group counts n,k encode n binary observations with k successes. -/
def binomialLogLikelihood (m : ℝ → ℝ) (n k η : ℝ) : ℝ :=
  k*Real.log (m η) + (n-k)*Real.log (1-m η)

/-- P015-T8(i): differentiating the Bernoulli log likelihood keeps the
multiplier m'(η)/[m(η)(1-m(η))], omitted by the broad substitution claim. -/
theorem bernoulli_score_derivative_calculus (m : ℝ → ℝ) (n k η m' : ℝ)
    (hm : HasDerivAt m m' η) (hp : 0 < m η) (hu : m η < 1) :
    HasDerivAt (binomialLogLikelihood m n k)
      (m'/(m η*(1-m η))*(k-n*m η)) η := by
  have h := ((hm.log hp.ne').const_mul k).add
    ((((hasDerivAt_const η 1).sub hm).log (by linarith : 1-m η ≠ 0)).const_mul (n-k))
  convert h using 1
  · rfl
  · simp only [Pi.sub_apply, zero_sub]
    field_simp [hp.ne', ne_of_gt (show 0 < 1-m η by linarith)]
    <;> ring

/-- The exact Bernoulli score multiplier from the correction to Appendix C. -/
def scoreMultiplier (m : ℝ → ℝ) (η : ℝ) : ℝ := deriv m η/(m η*(1-m η))

/-- P015-T8(ii): logistic regression has the constant score multiplier one. -/
theorem logistic_multiplier (η : ℝ) : scoreMultiplier logistic η = 1 := by
  have hp := Real.sigmoid_pos η
  have hu := Real.sigmoid_lt_one η
  simp only [scoreMultiplier, logistic, Real.deriv_sigmoid]
  have h : Real.sigmoid η * (1-Real.sigmoid η) ≠ 0 := by positivity
  exact div_self h

/-- Canonical-link log likelihood contribution {yη-κ(η)}/s+r(y), in the
P015-T8(ii) repair. This includes Poisson with κ=exp and logit with κ=log(1+exp). -/
def canonicalLogLikelihood (κ : ℝ → ℝ) (s y r η : ℝ) : ℝ :=
  (y*η-κ η)/s+r

/-- P015-T8(ii): a common dispersion makes the canonical score a common
multiple of y-κ'(η), exactly the residual equation. -/
theorem canonical_score_derivative_calculus (κ : ℝ → ℝ) (s y r η κ' : ℝ)
    (hs : 0 < s) (hk : HasDerivAt κ κ' η) :
    HasDerivAt (canonicalLogLikelihood κ s y r) ((y-κ')/s) η := by
  unfold canonicalLogLikelihood
  convert ((((hasDerivAt_id η).const_mul y).sub hk).div_const s).add_const r using 1
  <;> simp [Pi.sub_apply]

/-- P015-T8(iv): the full scalar score's first Taylor polynomial, keeping
h'(η₀)(y-p₀), the extra first-order term of the correction. -/
theorem scalar_full_score_firstTaylor (m h : ℝ → ℝ) (η₀ p₀ f₀ h₀ h₁ y : ℝ)
    (hm : HasDerivAt m f₀ η₀) (hh : HasDerivAt h h₁ η₀)
    (hp : m η₀ = p₀) (hval : h η₀ = h₀) :
    ∀ η, firstTaylor (fun t => h t*(y-m t)) η₀ η =
      h₀*(y-p₀) + (h₁*(y-p₀)-h₀*f₀)*(η-η₀) := by
  have hd := hh.mul ((hasDerivAt_const η₀ y).sub hm)
  have hv : deriv (fun t => h t*(y-m t)) η₀ = h₁*(y-p₀)-h₀*f₀ := by
    convert hd.deriv using 1
    simp only [Pi.sub_apply, hp, hval, zero_sub]
    ring
  intro η
  simp only [firstTaylor, hv, hp, hval]

/-- Finite grouped residual equation, Σ W_i'(Y_i-m(W_iθ)), Appendix C,
p. 265; grouping preserves all binary observations and their success counts. -/
def groupedResidual {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (n k : N → ℝ) (m : ℝ → ℝ) (θ : Q → ℝ) : Q → ℝ :=
  fun j => ∑ i, W i j*(k i-n i*m (W.mulVec θ i))
/-- The full likelihood score, with its multiplier, in P015-T8(i). -/
def groupedScore {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (n k : N → ℝ) (m : ℝ → ℝ) (θ : Q → ℝ) : Q → ℝ :=
  fun j => ∑ i, W i j*scoreMultiplier m (W.mulVec θ i)*(k i-n i*m (W.mulVec θ i))
/-- The grouped binary log likelihood; a compact encoding of the individual
binary observations in P015-T5 and T6. -/
def groupedLikelihood {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (n k : N → ℝ) (m : ℝ → ℝ) (θ : Q → ℝ) : ℝ :=
  ∑ i, binomialLogLikelihood m (n i) (k i) (W.mulVec θ i)

/-- P015-T5's six cells: D=0,1 and X=0,1,2, 12 observations per cell. -/
def oddsW : Matrix (Fin 2 × Fin 3) (Fin 3) ℝ :=
  fun i => ![1,(i.1 : ℝ),(i.2 : ℝ)]
/-- T5's six binomial cells each have n=12, with k=(7,6,10) at each D; Appendix C inverse-link substitution counterexample, p. 264. -/
def oddsSuccess (i : Fin 2 × Fin 3) : ℝ := ![7,6,10] i.2
/-- P015-T5's noncanonical inverse link η/(1+η), η>0. -/
def oddsMean (η : ℝ) : ℝ := η/(1+η)

/-- The score multiplier of the counterexample's odds link is 1/η. -/
theorem odds_multiplier (η : ℝ) (hη : 0 < η) : scoreMultiplier oddsMean η = 1/η := by
  have hd : HasDerivAt oddsMean (1/(1+η)^2) η := by
    convert (hasDerivAt_id η).div ((hasDerivAt_const η 1).add (hasDerivAt_id η))
      (by positivity : 1+η ≠ 0) using 1
    · rfl
    · dsimp
      field_simp
      <;> ring
  rw [scoreMultiplier, hd.deriv, oddsMean]
  field_simp
  <;> ring

/-- P015-T5(a),(b): the explicit 72-observation binary sample has a zero
substituted residual equation and nonzero genuine likelihood score. -/
theorem odds_score_counterexample :
    (∀ i, 0 < oddsW.mulVec ![1,0,1] i) ∧
    (∀ i, 0 < oddsSuccess i ∧ oddsSuccess i < 12) ∧
    groupedResidual oddsW (fun _ => 12) oddsSuccess oddsMean ![1,0,1] = 0 ∧
    groupedScore oddsW (fun _ => 12) oddsSuccess oddsMean ![1,0,1] = ![2/3,1/3,-2/3] ∧
    groupedScore oddsW (fun _ => 12) oddsSuccess oddsMean ![1,0,1] ≠ 0 := by
  have hm : ∀ i, scoreMultiplier oddsMean (oddsW.mulVec ![1,0,1] i) =
      1/(oddsW.mulVec ![1,0,1] i) := by
    intro i
    apply odds_multiplier
    rcases i with ⟨d,x⟩
    fin_cases d <;> fin_cases x <;> norm_num [oddsW, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have h₁ := odds_multiplier 1 (by norm_num)
  have h₂ := odds_multiplier 2 (by norm_num)
  have h₃ := odds_multiplier 3 (by norm_num)
  norm_num [groupedResidual, groupedScore, h₁, h₂, h₃, oddsW, oddsSuccess, oddsMean,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
    funext_iff, Fin.forall_fin_succ, Prod.forall, Pi.zero_apply]


/-- Φ and φ are the standard-normal CDF and density in the probit
extension named in Appendix C, pp. 264–265. -/
def normalCDF (a : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) a
/-- The standard normal density φ for the probit model named in Appendix C, p. 264; Mathlib gaussianPDFReal 0 1. -/
def normalPDF (a : ℝ) : ℝ := ProbabilityTheory.gaussianPDFReal 0 1 a
/-- The exact 3/4 standard-normal quantile in P015-T6. -/
def probitA : ℝ := sInf {a : ℝ | 3/4 ≤ normalCDF a}
/-- T6's probit regressor rows W_i=(1,D_i,X_i), D=0,1 and X=-1,0,1, Appendix C, pp. 264–265. -/
def probitW : Matrix (Fin 2 × Fin 3) (Fin 3) ℝ :=
  fun i => ![1,(i.1 : ℝ),(i.2 : ℝ)-1]
/-- T6's six binomial cells each have n=8 and k=(3,2,7) at each D; p. 264 probit counterexample. -/
def probitSuccess (i : Fin 2 × Fin 3) : ℝ := ![3,2,7] i.2
/-- Probit score multiplier h(η)=φ(η)/[Φ(η)(1-Φ(η))], the corrected Bernoulli likelihood score, T8, Appendix C p. 264. -/
def probitH (η : ℝ) : ℝ := normalPDF η/(normalCDF η*(1-normalCDF η))




/-- P015-T6 finite residual calculation, assuming the three exact normal CDF
values. The nonzero score is not assumed. -/
theorem probit_residual_conditional (a : ℝ)
    (hn : normalCDF (-a) = 1/4) (hz : normalCDF 0 = 1/2) (hp : normalCDF a = 3/4) :
    groupedResidual probitW (fun _ => 8) probitSuccess normalCDF ![0,0,a] = 0 := by
  norm_num [groupedResidual, probitW, probitSuccess, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ,
    hn, hz, hp, Pi.zero_apply]

/-- P015-T7's six-atom (X,D) law, e(X)=1/2+X/4 and residualized regressors z=(1,v,X). -/
def rootX : Fin 6 → ℝ := ![-1,-1,0,0,1,1]
/-- T7's binary D, alternating 0 and 1 at the three X profiles; the p. 257 general-GLM first-order counterexample. -/
def rootD : Fin 6 → ℝ := ![0,1,0,1,0,1]
/-- T7's six exact joint atom masses for the first-order GLM counterexample, p. 257 and Appendix C. -/
def rootLaw : Fin 6 → ℝ := ![1/4,1/12,1/6,1/6,1/12,1/4]
/-- T7's E[D|X]=1/2+X/4, an exact instance of (3), p. 253. -/
def rootE (x : ℝ) : ℝ := 1/2+x/4
/-- T7's baseline q₀(X)=1/4+a(3X²-2), the conditional success probability at ε=0. -/
def rootBaseline (a x : ℝ) : ℝ := 1/4+a*(3*x^2-2)
/-- T7's z=(1,D-E[D|X],X), a residualized version of W_i=(1,D_i,X_i), Appendix C, p. 265. -/
def rootZ : Matrix (Fin 6) (Fin 3) ℝ := fun i => ![1,rootD i-rootE (rootX i),rootX i]
/-- Potential outcomes, P015-T7: U uniform on [0,1],
independent of D given X, and Y(d)=1{U≤q₀(X)+ε(d-e(X))}. -/
def rootPotential (a ε x u d : ℝ) : ℝ := if u ≤ rootBaseline a x+ε*(d-rootE x) then 1 else 0
/-- Conditional success probability of that potential-outcome construction. -/
def rootProbability (a ε : ℝ) (i : Fin 6) : ℝ :=
  rootBaseline a (rootX i)+ε*(rootD i-rootE (rootX i))
/-- T7's admissible noncanonical inverse link m(η)=η² on 0<η<1, for the p. 257 first-order claim. -/
def rootMean (η : ℝ) : ℝ := η^2
/-- The expected Bernoulli log likelihood under T7's six-atom law; Appendix C ML, pp. 264–265. -/
def rootLikelihood (a ε : ℝ) (θ : Fin 3 → ℝ) : ℝ :=
  ∑ i, rootLaw i*binomialLogLikelihood rootMean 1 (rootProbability a ε i) (rootZ.mulVec θ i)
/-- T7's parameter domain 0<z_i θ<1 at every atom, so m(z_i θ) lies strictly between 0 and 1. -/
def rootAdmissible (θ : Fin 3 → ℝ) : Prop := ∀ i, 0 < rootZ.mulVec θ i ∧ rootZ.mulVec θ i < 1
/-- The derivative of the treatment coordinate of the local unique ML
branch, in P015-T7. -/
def RootMLDerivative (a b : ℝ) : Prop :=
  ∃ θ : ℝ → Fin 3 → ℝ, θ 0 = ![1/2,0,0] ∧
    (∃ r : ℝ, 0 < r ∧ r ≤ 1/16 ∧ ∀ ε, |ε| < r → rootAdmissible (θ ε) ∧
      (∀ t, rootAdmissible t → rootLikelihood a ε t ≤ rootLikelihood a ε (θ ε)) ∧
      (∀ t, rootAdmissible t → rootLikelihood a ε t = rootLikelihood a ε (θ ε) → t = θ ε)) ∧
    HasDerivAt (fun ε => θ ε 1) b 0

/-- P015-T7 finite rational core: the exact moment matrices, the score
Jacobian arithmetic, and its unique derivative vector (0,120/119,0). -/
theorem root_link_matrix_arithmetic :
    IsLaw rootLaw ∧
    (fun j k => fExpectation rootLaw (fun i => rootZ i j*rootZ i k)) =
      (!![1,0,0;0,5/24,0;0,0,2/3] : Matrix (Fin 3) (Fin 3) ℝ) ∧
    (fun j k => fExpectation rootLaw
      (fun i => rootZ i j*rootZ i k*(rootBaseline (1/16) (rootX i)-1/4))) =
      (!![0,0,0;0,-1/384,0;0,0,1/24] : Matrix (Fin 3) (Fin 3) ℝ) ∧
    ((-32/9 : ℝ) • (!![0,0,0;0,-1/384,0;0,0,1/24] : Matrix (Fin 3) (Fin 3) ℝ) -
      (16/3 : ℝ) • !![1,0,0;0,5/24,0;0,0,2/3]) = !![-16/3,0,0;0,-119/108,0;0,0,-100/27] ∧
    (∀ t : Fin 3 → ℝ,
      (!![-16/3,0,0;0,-119/108,0;0,0,-100/27] : Matrix (Fin 3) (Fin 3) ℝ).mulVec t+
        ![0,10/9,0] = 0 ↔ t = ![0,120/119,0]) ∧
    (120/119 : ℝ) ≠ 1  := by
  have hA : (fun j k => fExpectation rootLaw (fun i => rootZ i j*rootZ i k)) =
      (!![1,0,0;0,5/24,0;0,0,2/3] : Matrix (Fin 3) (Fin 3) ℝ) := by
    funext j k
    fin_cases j <;> fin_cases k <;>
      norm_num [fExpectation,rootLaw,rootZ,rootX,rootD,rootE,Fin.sum_univ_succ]
  have hR : (fun j k => fExpectation rootLaw
      (fun i => rootZ i j*rootZ i k*(rootBaseline (1/16) (rootX i)-1/4))) =
      (!![0,0,0;0,-1/384,0;0,0,1/24] : Matrix (Fin 3) (Fin 3) ℝ) := by
    funext j k
    fin_cases j <;> fin_cases k <;>
      norm_num [fExpectation,rootLaw,rootZ,rootX,rootD,rootE,rootBaseline,Fin.sum_univ_succ]
  refine ⟨?_,hA,hR,?_,?_,by norm_num⟩
  · norm_num [IsLaw,rootLaw,Fin.forall_fin_succ,Fin.sum_univ_succ]
  · ext j k
    fin_cases j <;> fin_cases k <;> norm_num
  · intro t
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1 h2
      funext j
      fin_cases j <;> simp <;> linarith
    · rintro rfl
      norm_num [Matrix.mulVec,Matrix.vecMul,vecHead,vecTail,dotProduct,
        Fin.sum_univ_succ,funext_iff,Fin.forall_fin_succ]




/-- P015-T16(i): the paper's 0.077 natural-log coefficient gives about 8%,
with an exact decimal enclosure, rather than 20% (p. 259). -/
theorem log_points_numeric_correction :
    10800420763/10000000000 < Real.exp (77/1000) ∧
    Real.exp (77/1000) < 10800420765/10000000000 ∧
    (10800420765/10000000000 : ℝ) < 6/5 ∧
    800420763/100000000 < 100*(Real.exp (77/1000)-1) ∧
    100*(Real.exp (77/1000)-1) < 800420765/100000000 := by
  have h := Real.exp_bound (x := 77/1000) (n := 8) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · norm_num
  constructor <;> linarith

/-- P015-T16(ii): one treatment point multiplies the exponentiated fitted
linear predictor by exp(β), with controls held fixed (p. 259 correction). -/
theorem exponentiated_fitted_contrast (α β d controls : ℝ) :
    Real.exp (α+β*(d+1)+controls)/Real.exp (α+β*d+controls) = Real.exp β := by
  rw [← Real.exp_sub]
  congr 1
  ring

/-- P015-T16(iii): zero log-growth OLS coefficient coexists with a 50%
arithmetic-mean spending difference in four observations. -/
theorem spending_mean_arithmetic :
    (Real.log (1/2)+Real.log 2)/2 = 0 ∧
    Real.exp ((Real.log (1/2)+Real.log 2)/2) = 1 ∧
    (1+1 : ℝ)/2 = 1 ∧ (0+3 : ℝ)/2 = 3/2 ∧ ((3/2 : ℝ)/1-1)*100 = 50 := by
  have hl : Real.log (1/2) = -Real.log 2 := by
    simpa using Real.log_inv (2 : ℝ)
  rw [hl]
  norm_num

/-- A general probability distribution's cell law given a discrete X=x,
for the positivity display (p. 261), normalized on its positive-mass cell. -/
def cellLaw {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B) (x : B) : Measure Ω :=
  (P {s | X s = x})⁻¹ • P.restrict {s | X s = x}
/-- E[D_i|X_i=x], (3) and (8), pp. 253 and 255, as an integral under the normalized positive-mass discrete cell. -/
def cellMean {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) (x : B) : ℝ := ∫ s, D s ∂cellLaw P X x
/-- Var[D_i|X_i=x], Expression (8), p. 255, as the cell mean of the squared centered treatment. -/
def cellVar {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) (x : B) : ℝ := ∫ s, (D s-cellMean P X D x)^2 ∂cellLaw P X x
/-- The p. 261 conditional endpoint probability under a general discrete-X law. -/
def cellProb {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) (x : B) (d : ℝ) : ℝ := (cellLaw P X x {s | D s = d}).toReal
/-- The population weight (7), using the discrete conditional mean. -/
def discreteWeight {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) (s : Ω) : ℝ := (D s-cellMean P X D (X s))^2
/-- The effective probability law Q(A)=E[w 1_A]/E[w], p. 255 and P015-T4. -/
def discreteEffective {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) : Measure Ω :=
  (ENNReal.ofReal (∫ s, discreteWeight P X D s ∂P))⁻¹ •
    P.withDensity (fun s => ENNReal.ofReal (discreteWeight P X D s))




/-- The finite binary variance and the conditional effective-law reversal
in the repaired p. 261 argument (T4(ii),(iii)) and Expression (8), T19. -/
theorem binary_variance_reversal_arithmetic (p : ℝ) (hp : 0 < p) (hu : p < 1) :
    (1-p)*(0-p)^2+p*(1-p)^2 = p*(1-p) ∧
    p*(1-p)^2/(p*(1-p)) = 1-p ∧
    (1-p)*p^2/(p*(1-p)) = p ∧ 0 < p*(1-p) := by
  have h : p ≠ 0 := hp.ne'
  have h' : 1-p ≠ 0 := by linarith
  constructor
  · ring
  constructor
  · field_simp <;> ring
  constructor
  · field_simp <;> ring
  · exact mul_pos hp (by linarith)

/-- Finite Chebyshev, used in the all-n finite consistency calculation for T1. -/
theorem finite_chebyshev_algebra {A : Type*} [Fintype A] (p Z : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (δ : ℝ) (hδ : 0 < δ) :
    fMass p (fun a => δ ≤ |Z a-fExpectation p Z|) ≤ fVariance p Z/δ^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).2
  unfold fMass fVariance fExpectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  split_ifs with h
  · have hs : δ^2 ≤ (Z a-∑ b, p b*Z b)^2 := by
      have hh := (sq_le_sq₀ hδ.le (abs_nonneg (Z a-∑ b, p b*Z b))).2 h
      simpa only [sq_abs] using hh
    exact mul_le_mul_of_nonneg_left hs (hp a)
  · simp only [zero_mul]
    exact mul_nonneg (hp a) (sq_nonneg _)

/-- Independent n-draw design, represented by the product of the atom probabilities. -/
def iidLaw {A : Type*} [Fintype A] (p : A → ℝ) (n : ℕ) : (Fin n → A) → ℝ :=
  fun a => ∏ i, p (a i)
/-- T1's iid estimator is n^-1 times the sum of its observed-data IPW variables; p. 261 counterexample. -/
def sampleAverage {A : Type*} (Z : A → ℝ) (n : ℕ) (a : Fin n → A) : ℝ :=
  (∑ i, Z (a i))/(n : ℝ)


/-- Exact factorization of a finite iid product law's product moments,
the elementary independence calculation used in T1(d). -/
theorem iid_tensor_expectation_algebra {A : Type*} [Fintype A] (p : A → ℝ) (n : ℕ)
    (G : Fin n → A → ℝ) :
    fExpectation (iidLaw p n) (fun a => ∏ i, G i (a i)) =
      ∏ i, fExpectation p (G i) := by
  unfold fExpectation iidLaw
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => p a*G i a)).symm

/-- A product of normalized nonnegative atom laws is again a genuine
probability law, for every sample size. -/
theorem iid_isLaw {A : Type*} [Fintype A] (p : A → ℝ) (h : IsLaw p) (n : ℕ) :
    IsLaw (iidLaw p n) := by
  constructor
  · intro a
    exact Finset.prod_nonneg (fun i _ => h.1 (a i))
  · have ht := iid_tensor_expectation_algebra p n (fun _ _ => 1)
    simpa [fExpectation,h.2] using ht

/-- Every coordinate of an iid finite sample has the original expectation. -/
theorem iid_coordinate_mean {A : Type*} [Fintype A] (p Z : A → ℝ)
    (h : IsLaw p) (n : ℕ) (j : Fin n) :
    fExpectation (iidLaw p n) (fun a => Z (a j)) = fExpectation p Z := by
  have ht := iid_tensor_expectation_algebra p n (fun i x => if i=j then Z x else 1)
  have hs : ∀ i, fExpectation p (fun x => if i=j then Z x else 1) =
      if i=j then fExpectation p Z else 1 := by
    intro i
    by_cases hi : i=j <;> simp [hi,fExpectation,h.2]
  simpa [Finset.prod_ite_eq, hs] using ht

/-- Different iid coordinates have factorized cross moments, the exact
covariance-zero fact needed for T1's finite variance bound. -/
theorem iid_coordinate_cross {A : Type*} [Fintype A] (p Z T : A → ℝ)
    (h : IsLaw p) (n : ℕ) (j k : Fin n) (hjk : j ≠ k) :
    fExpectation (iidLaw p n) (fun a => Z (a j)*T (a k)) = fExpectation p Z*fExpectation p T := by
  have ht := iid_tensor_expectation_algebra p n
    (fun i x => (if i=j then Z x else 1)*(if i=k then T x else 1))
  have hs : ∀ i, fExpectation p
      (fun x => (if i=j then Z x else 1)*(if i=k then T x else 1)) =
      (if i=j then fExpectation p Z else 1)*(if i=k then fExpectation p T else 1) := by
    intro i
    by_cases hi : i=j <;> by_cases hk : i=k <;> simp_all [fExpectation,h.2]
  calc
    fExpectation (iidLaw p n) (fun a => Z (a j)*T (a k)) =
        fExpectation (iidLaw p n) (fun a =>
          ∏ i, (if i=j then Z (a i) else 1)*(if i=k then T (a i) else 1)) := by
      congr 1
      funext a
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_ite_eq',Finset.mem_univ,ite_true]
    _ = ∏ i, fExpectation p
        (fun x => (if i=j then Z x else 1)*(if i=k then T x else 1)) := ht
    _ = fExpectation p Z*fExpectation p T := by
      simp_rw [hs]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_ite_eq',Finset.mem_univ,ite_true]

/-- Exact expectation of an iid sample mean, for positive sample sizes. -/
theorem iid_average_mean {A : Type*} [Fintype A] (p Z : A → ℝ)
    (h : IsLaw p) (n : ℕ) (hn : 1 ≤ n) :
    fExpectation (iidLaw p n) (sampleAverage Z n) = fExpectation p Z := by
  have hpos : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0<n))
  unfold fExpectation sampleAverage
  simp only [← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  have hs : ∀ i : Fin n, (∑ a, iidLaw p n a*Z (a i)) = fExpectation p Z :=
    fun i => iid_coordinate_mean p Z h n i
  simp_rw [hs]
  simp [hpos,fExpectation]

/-- Exact variance of an iid sample mean, the finite lemma behind consistency,
with no law of large numbers or normal approximation assumed. -/
theorem iid_average_variance {A : Type*} [Fintype A] (p Z : A → ℝ)
    (h : IsLaw p) (n : ℕ) (hn : 1 ≤ n) :
    fVariance (iidLaw p n) (sampleAverage Z n) = fVariance p Z/(n : ℝ) := by
  let m := fExpectation p Z
  let C : A → ℝ := fun a => Z a-m
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0<n))
  have hc : fExpectation p C=0 := by
    simp [C,m,fExpectation,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,h.2]
  have hcenter : ∀ a : Fin n → A, sampleAverage Z n a-m = (∑ i, C (a i))/(n : ℝ) := by
    intro a
    simp only [sampleAverage,C,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
    field_simp [hn0]
    <;> ring
  have hij : ∀ i j : Fin n,
      fExpectation (iidLaw p n) (fun a => C (a i)*C (a j)) =
        if i=j then fVariance p Z else 0 := by
    intro i j
    by_cases he : i=j
    · subst j
      have hi := iid_coordinate_mean p (fun a => C a^2) h n i
      simpa [sq,C,m,fVariance] using hi
    · simpa [he,hc] using iid_coordinate_cross p C C h n i j he
  rw [fVariance, iid_average_mean p Z h n hn]
  change (∑ a, iidLaw p n a*(sampleAverage Z n a-m)^2) = _
  simp only [hcenter,div_pow, ← mul_div_assoc]
  rw [← Finset.sum_div]
  have hs : (∑ a, iidLaw p n a*(∑ i, C (a i))^2) = (n : ℝ)*fVariance p Z := by
    calc
      (∑ a, iidLaw p n a*(∑ i, C (a i))^2) =
          ∑ i : Fin n, ∑ j : Fin n,
            fExpectation (iidLaw p n) (fun a => C (a i)*C (a j)) := by
        simp only [pow_two,Finset.sum_mul,Finset.mul_sum,fExpectation]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = (n : ℝ)*fVariance p Z := by simp [hij]
  rw [hs]
  field_simp [hn0]
  <;> ring

/-- P015-T1(d): the explicit four-atom IPW estimator is unbiased, has variance
2000071/(4n), and satisfies the Chebyshev probability bound for every n≥1. -/
theorem rare_ipw_all_n (n : ℕ) (hn : 1 ≤ n) :
    IsLaw (iidLaw (rareLaw (1/1000000)) n) ∧
    fExpectation (iidLaw (rareLaw (1/1000000)) n)
      (sampleAverage (rareZ (1/1000000)) n) = 3/2 ∧
    fVariance (iidLaw (rareLaw (1/1000000)) n)
      (sampleAverage (rareZ (1/1000000)) n) = 2000071/(4*n) ∧
    (∀ δ : ℝ, 0 < δ → fMass (iidLaw (rareLaw (1/1000000)) n)
      (fun a => δ ≤ |sampleAverage (rareZ (1/1000000)) n a-3/2|) ≤
        2000071/(4*n*δ^2))  := by
  have hsingle := rare_weight_counterexample
  have hlaw : IsLaw (rareLaw (1/1000000)) := hsingle.1
  have hm : fExpectation (rareLaw (1/1000000)) (rareZ (1/1000000)) = 3/2 := by
    norm_num [fExpectation,rareLaw,rareZ,rareY,binaryX,binaryD,ipw,Fin.sum_univ_succ]
  have hv : fVariance (rareLaw (1/1000000)) (rareZ (1/1000000)) = 2000071/4 := by
    norm_num [fVariance,fExpectation,rareLaw,rareZ,rareY,binaryX,binaryD,ipw,Fin.sum_univ_succ]
  have hprod := iid_isLaw (rareLaw (1/1000000)) hlaw n
  have havg := iid_average_mean (rareLaw (1/1000000)) (rareZ (1/1000000)) hlaw n hn
  have hvar := iid_average_variance (rareLaw (1/1000000)) (rareZ (1/1000000)) hlaw n hn
  rw [hm] at havg
  rw [hv] at hvar
  have hvar' : fVariance (iidLaw (rareLaw (1/1000000)) n)
      (sampleAverage (rareZ (1/1000000)) n) = 2000071/(4*n) := by
    rw [hvar]
    ring
  refine ⟨hprod,havg,hvar',?_⟩
  intro δ hδ
  have hc := finite_chebyshev_algebra (iidLaw (rareLaw (1/1000000)) n)
    (sampleAverage (rareZ (1/1000000)) n) hprod.1 δ hδ
  rw [havg,hvar'] at hc
  convert hc using 1
  ring

/-- P015-T9's group designs and outcome vectors, p. 257 counterexample. -/
def groupZ₁ : Matrix (Fin 3) (Fin 2) ℝ := !![1,0;1,1;1,1]
/-- T9's second within-group design Z_g=(1,D_g), Section Random Coefficient Models, p. 257. -/
def groupZ₂ : Matrix (Fin 3) (Fin 2) ℝ := !![1,0;1,0;1,1]
/-- T9's first full-vector precision P_g=(S+σ_g²Q_g^-1)^-1 with S=I and σ_g²=1, correction T10, p. 257. -/
def groupP₁ : Matrix (Fin 2) (Fin 2) ℝ := !![5/8,1/4;1/4,1/2]
/-- T9's second full-vector precision P_g=(S+σ_g²Q_g^-1)^-1, correction T10, p. 257. -/
def groupP₂ : Matrix (Fin 2) (Fin 2) ℝ := !![5/7,1/7;1/7,3/7]
/-- T9's (sum_g P_g)^-1, the overall full-vector GLS normalization, correction T10, p. 257. -/
def groupHinv : Matrix (Fin 2) (Fin 2) ℝ := !![52/61,-22/61;-22/61,75/61]

/-- P015-T9: both group OLS slopes vanish, but GLS pools to -10/61,
which no scalar combination of the slopes can equal. The inverse matrices are exact. -/
theorem group_pooling_counterexample :
    (groupZ₁.transpose*groupZ₁).det = 2 ∧
    (groupZ₂.transpose*groupZ₂).det = 2 ∧
    ols groupZ₁ ![0,0,0] = ![0,0] ∧ ols groupZ₂ ![2,2,2] = ![2,0] ∧
    groupP₁*(1+(groupZ₁.transpose*groupZ₁)⁻¹) = 1 ∧
    groupP₂*(1+(groupZ₂.transpose*groupZ₂)⁻¹) = 1 ∧
    groupHinv*(groupP₁+groupP₂) = 1 ∧
    groupHinv.mulVec (groupP₁.mulVec ![0,0]+groupP₂.mulVec ![2,0]) = ![68/61,-10/61] ∧
    (∀ a₁ a₂ : ℝ, a₁*0+a₂*0 ≠ -10/61) ∧
    (∀ t₁ t₂ : Fin 2 → ℝ,
      (groupHinv.mulVec (groupP₁.mulVec t₁+groupP₂.mulVec t₂)) 1 =
        (5/61)*t₁ 0-(5/61)*t₂ 0+(32/61)*t₁ 1+(29/61)*t₂ 1) := by
  have h₁ : (groupZ₁.transpose*groupZ₁)⁻¹ =
      (!![1,-1;-1,3/2] : Matrix (Fin 2) (Fin 2) ℝ) := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [groupZ₁, Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_succ, Matrix.one_apply]
  have h₂ : (groupZ₂.transpose*groupZ₂)⁻¹ =
      (!![1/2,-1/2;-1/2,3/2] : Matrix (Fin 2) (Fin 2) ℝ) := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [groupZ₂, Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_succ, Matrix.one_apply]
  simp only [ols, h₁, h₂]
  norm_num [groupZ₁, groupZ₂, groupP₁, groupP₂, groupHinv,
    ← Matrix.ext_iff, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
    dotProduct, Matrix.vecMul, vecHead, vecTail, Matrix.det_fin_two, Fin.sum_univ_succ, Fin.forall_fin_succ,
    funext_iff, Matrix.one_apply, Matrix.add_apply, Pi.add_apply]
  intro t₁ t₂
  ring







/-- P015-T10(i),(ii),(iv), the complete matrix GLS repair with known covariance,
full-rank designs and positive error variances. The row criterion is proved separately. -/
theorem corrected_matrix_pooling (G q : ℕ) (hG : 1 ≤ G) (hq : 1 ≤ q)
    (n : Fin G → ℕ) (Z : ∀ g, Matrix (Fin (n g)) (Fin q) ℝ)
    (y : ∀ g, Fin (n g) → ℝ) (S : Matrix (Fin q) (Fin q) ℝ)
    (σ₂ : Fin G → ℝ) (hS : S.PosSemidef)
    (hσ : ∀ g, 0 < σ₂ g) (hQ : ∀ g, ((Z g).transpose * Z g).det ≠ 0) :
    let P := fun g => groupPrecision S ((Z g).transpose*Z g) (σ₂ g)
    let H := ∑ g, P g
    let A := fun g => H⁻¹*P g
    let t := fun g => ols (Z g) (y g)
    let V : ∀ g, Matrix (Fin (n g)) (Fin (n g)) ℝ := fun g => Z g*S*(Z g).transpose+σ₂ g • 1
    (∀ m, poolingLoss P t (pooledGLS P t) ≤ poolingLoss P t m) ∧
    (∀ m, poolingLoss P t m = poolingLoss P t (pooledGLS P t) → m = pooledGLS P t) ∧
    pooledGLS P t = ∑ g, (A g).mulVec (t g) ∧ (∑ g, A g) = 1 ∧
    (∀ g, (Z g).transpose*(V g)⁻¹*Z g = P g ∧
      ((Z g).transpose*(V g)⁻¹).mulVec (y g) = (P g).mulVec (t g)) ∧
    pooledGLS P t = (∑ g, (Z g).transpose*(V g)⁻¹*Z g)⁻¹.mulVec
      (∑ g, ((Z g).transpose*(V g)⁻¹).mulVec (y g)) ∧
    (∀ b : Fin q, (∀ g j, j ≠ b → (P g) b j = 0 ∧ (P g) j b = 0) →
      (∀ g, 0 < (P g) b b) →
      ∀ g j, A g b j = if j=b then P g b b/(∑ h, P h b b) else 0) := by
  exact MatrixCompletion.corrected_matrix_pooling_completed G q hG hq n Z y S σ₂ hS hσ hQ

/-- P015-T10(iii): a treatment coordinate pools by scalar weights for all
coefficient vectors iff each group's treatment row has that group's scalar in
the treatment entry and zero in every other entry. -/
theorem scalar_pooling_iff_algebra {G Q : Type*} [Fintype G] [Fintype Q]
    [DecidableEq G] [DecidableEq Q] (A : G → Matrix Q Q ℝ) (a : G → ℝ) (b : Q) :
    (∀ t : G → Q → ℝ, (∑ g, ∑ j, A g b j*t g j) = ∑ g, a g*t g b) ↔
      ∀ g j, A g b j = if j=b then a g else 0 := by
  constructor
  · intro h g j
    have hh := h (fun h k => if h=g then (if k=j then 1 else 0) else 0)
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at hh
    simpa [eq_comm] using hh
  · intro h t
    simp [h, ite_mul, Finset.sum_ite_eq]

/-- P015-T20's exact Appendix B law in order (D,X)=(0,0),(1,0),(0,1),(1,1). -/
def leverageLaw : Fin 4 → ℝ := ![1/20,1/5,11/20,1/5]
/-- W_i=(1,D_i,X_i), Appendix B, pp. 263–264, with the exact binary population proportions in T20. -/
def leverageW : Matrix (Fin 4) (Fin 3) ℝ := fun i => ![1,binaryD i,binaryX i]
/-- E[W_i′W_i] for Appendix B's exact four-atom population example, pp. 263–264. -/
def leverageQ : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j k => fExpectation leverageLaw (fun i => leverageW i j*leverageW i k)
/-- The exact rational inverse of Appendix B's E[W_i′W_i], pp. 263–264 (T20). -/
def leverageQinv : Matrix (Fin 3) (Fin 3) ℝ :=
  !![52/7,-30/7,-44/7;-30/7,75/14,20/7;-44/7,20/7,48/7]
/-- Population scaled leverage W E[W'W]⁻¹ W', Appendix B, pp. 263–264.
It also equals n*h_ii for fixed designs with exactly these cell proportions. -/
def populationLeverage (i : Fin 4) : ℝ := dotProduct (leverageW i) (leverageQ⁻¹.mulVec (leverageW i))
/-- A number rounds to the displayed decimal when its error is strictly less
than half a unit in the last printed place; none of T20's numbers are tie cases. -/
def RoundsTo (x display resolution : ℝ) : Prop := |x-display| < resolution/2

/-- P015-T20: exact conditional variances and population leverages, including
rounding to all printed values and the opposite direction of their profile comparisons. -/
theorem leverage_weight_comparison :
    IsLaw leverageLaw ∧
    fCondMean leverageLaw binaryX (fWeight leverageLaw binaryX binaryD) 0 = 4/25 ∧
    fCondMean leverageLaw binaryX (fWeight leverageLaw binaryX binaryD) 1 = 44/225 ∧
    leverageQ = !![1,2/5,3/4;2/5,2/5,1/5;3/4,1/5,3/4] ∧
    leverageQ⁻¹ = leverageQinv ∧
    populationLeverage = ![52/7,59/14,12/7,59/14] ∧
    fCondMean leverageLaw binaryX populationLeverage 0 = 34/7 ∧
    fCondMean leverageLaw binaryX populationLeverage 1 = 50/21 ∧
    (44/225 : ℝ)/(4/25) = 11/9 ∧ (1 : ℝ)-(50/21)/(34/7) = 26/51 ∧
    RoundsTo (4/25) (160/1000) (1/1000) ∧ RoundsTo (44/225) (196/1000) (1/1000) ∧
    RoundsTo (52/7) (743/100) (1/100) ∧ RoundsTo (59/14) (421/100) (1/100) ∧
    RoundsTo (12/7) (171/100) (1/100) ∧ RoundsTo (34/7) (486/100) (1/100) ∧
    RoundsTo (50/21) (238/100) (1/100) ∧
    RoundsTo (100*(11/9-1)) 22 1 ∧ RoundsTo (100*26/51) 51 1 := by
  have hi : leverageQ⁻¹ = leverageQinv := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [leverageQ, leverageQinv, leverageW, leverageLaw, fExpectation,
        binaryX, binaryD, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.one_apply,
        Fin.sum_univ_succ]
  norm_num [hi, IsLaw, fCondMean, fWeight, fMass, fExpectation, leverageLaw,
    leverageQ, leverageQinv, populationLeverage, leverageW, binaryX, binaryD,
    Matrix.mulVec, dotProduct, ← Matrix.ext_iff, funext_iff, Fin.sum_univ_succ,
    Fin.forall_fin_succ, RoundsTo]


/-- P015-T14: the unconditional single-unit left side in the misprint cannot
hold at two different treatment values at fixed controls when β≠0. -/
theorem unconditional_logistic_misprint (α β x d d' p : ℝ)
    (hβ : β ≠ 0) (hd : d ≠ d') :
    ¬ (p=logistic (α+β*d+x) ∧ p=logistic (α+β*d'+x)) := by
  rintro ⟨h,h'⟩
  have hi : α+β*d+x = α+β*d'+x := Real.sigmoid_injective (h.symm.trans h')
  have hh : β*(d-d') = 0 := by linarith
  rcases mul_eq_zero.mp hh with hb | hdd
  · exact hβ hb
  · exact hd (sub_eq_zero.mp hdd)

/-- Exact gradient in directional-derivative form for a finite binary likelihood,
P015-T8(i): the derivative in every direction is the score dotted with that direction. -/
theorem likelihood_directional_derivative_calculus {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (n k : N → ℝ) (m : ℝ → ℝ) (θ v : Q → ℝ)
    (hm : ∀ i, DifferentiableAt ℝ m (W.mulVec θ i))
    (hp : ∀ i, 0 < m (W.mulVec θ i)) (hu : ∀ i, m (W.mulVec θ i) < 1) :
    HasDerivAt (fun t => groupedLikelihood W n k m (fun j => θ j+t*v j))
      (∑ i, scoreMultiplier m (W.mulVec θ i)*(k i-n i*m (W.mulVec θ i))*W.mulVec v i) 0 := by
  have hl : ∀ i, HasDerivAt (fun t => W.mulVec (fun j => θ j+t*v j) i) (W.mulVec v i) 0 := by
    intro i
    unfold Matrix.mulVec dotProduct
    convert HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (((hasDerivAt_const 0 (θ j)).add ((hasDerivAt_id 0).mul_const (v j))).const_mul (W i j))) using 1
    <;> simp
  have hi : ∀ i, HasDerivAt
      (fun t => binomialLogLikelihood m (n i) (k i) (W.mulVec (fun j => θ j+t*v j) i))
      (scoreMultiplier m (W.mulVec θ i)*(k i-n i*m (W.mulVec θ i))*W.mulVec v i) 0 := by
    intro i
    have hg : HasDerivAt (binomialLogLikelihood m (n i) (k i))
        (scoreMultiplier m (W.mulVec θ i)*(k i-n i*m (W.mulVec θ i)))
        (W.mulVec (fun j => θ j+0*v j) i) := by
      simpa [scoreMultiplier] using bernoulli_score_derivative_calculus m (n i) (k i) (W.mulVec θ i) _
        (hm i).hasDerivAt (hp i) (hu i)
    exact hg.comp 0 (hl i)
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)

/-- P015-T5: the counterexample point is not an ML maximizer on the open
odds-link parameter domain; the nonzero derivative rules out even a local maximum. -/
theorem odds_not_mle_calculus : ¬ ∀ θ : Fin 3 → ℝ, (∀ i, 0 < oddsW.mulVec θ i) →
    groupedLikelihood oddsW (fun _ => 12) oddsSuccess oddsMean θ ≤
      groupedLikelihood oddsW (fun _ => 12) oddsSuccess oddsMean ![1,0,1] := by
  intro hmax
  let F : ℝ → ℝ := fun t => groupedLikelihood oddsW (fun _ => 12) oddsSuccess oddsMean
    (fun j => (![1,0,1] : Fin 3 → ℝ) j+t*(![0,1,0] : Fin 3 → ℝ) j)
  have hm : ∀ i, DifferentiableAt ℝ oddsMean (oddsW.mulVec ![1,0,1] i) := by
    intro i
    have hη := odds_score_counterexample.1 i
    exact ((hasDerivAt_id _).div ((hasDerivAt_const _ 1).add (hasDerivAt_id _))
      (by positivity : 1+oddsW.mulVec ![1,0,1] i ≠ 0)).differentiableAt
  have hp : ∀ i, 0 < oddsMean (oddsW.mulVec ![1,0,1] i) := by
    intro i
    have hη := odds_score_counterexample.1 i
    unfold oddsMean
    exact div_pos (odds_score_counterexample.1 i) (by positivity)
  have hu : ∀ i, oddsMean (oddsW.mulVec ![1,0,1] i) < 1 := by
    intro i
    have hη := odds_score_counterexample.1 i
    unfold oddsMean
    apply (div_lt_one (by positivity)).2
    linarith
  have h₁ := odds_multiplier 1 (by norm_num)
  have h₂ := odds_multiplier 2 (by norm_num)
  have h₃ := odds_multiplier 3 (by norm_num)
  have hd : HasDerivAt F (1/3) 0 := by
    convert likelihood_directional_derivative_calculus oddsW (fun _ => 12) oddsSuccess oddsMean
      ![1,0,1] ![0,1,0] hm hp hu using 1
    norm_num [oddsW,oddsSuccess,oddsMean,Matrix.mulVec,dotProduct,
      Fintype.sum_prod_type,Fin.sum_univ_succ,h₁,h₂,h₃]
  have hadm : ∀ᶠ t : ℝ in nhds 0, ∀ i,
      0 < oddsW.mulVec (fun j => (![1,0,1] : Fin 3 → ℝ) j+t*(![0,1,0] : Fin 3 → ℝ) j) i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun t : ℝ => oddsW.mulVec
      (fun j => (![1,0,1] : Fin 3 → ℝ) j+t*(![0,1,0] : Fin 3 → ℝ) j) i) 0 := by
      unfold Matrix.mulVec dotProduct
      fun_prop
    have h₀ : 0 < oddsW.mulVec
      (fun j => (![1,0,1] : Fin 3 → ℝ) j+(0:ℝ)*(![0,1,0] : Fin 3 → ℝ) j) i := by
      simpa using odds_score_counterexample.1 i
    exact hc.eventually (Ioi_mem_nhds h₀)
  have hl : IsLocalMax F 0 := by
    change ∀ᶠ t in nhds (0:ℝ), F t ≤ F 0
    filter_upwards [hadm] with t ht
    simpa [F] using hmax
      (fun j => (![1,0,1] : Fin 3 → ℝ) j+t*(![0,1,0] : Fin 3 → ℝ) j) ht
  have hz := hl.hasDerivAt_eq_zero hd
  norm_num at hz

/-- Full column rank of the rational counterexample's grouped design, T5.
Repeating each of these six rows twelve times preserves this rank. -/
theorem odds_gram_determinant : (oddsW.transpose*oddsW).det = 36 := by
  norm_num [oddsW,Matrix.det_fin_three,Matrix.mul_apply,Matrix.transpose_apply,
    Fintype.sum_prod_type,Fin.sum_univ_succ]

/-- OLS is the unique root of the normal equations whenever W'W is
nonsingular, the matrix algebra used in Appendix C, p. 265 (T21). -/
theorem ols_normal_equation {N Q : Type*} [Fintype N] [Fintype Q] [DecidableEq Q]
    (W : Matrix N Q ℝ) (Y : N → ℝ) (hQ : (W.transpose*W).det ≠ 0) (θ : Q → ℝ) :
    groupedResidual W (fun _ => 1) Y id θ = 0 ↔ θ = ols W Y := by
  let Qm := W.transpose*W
  have hr : groupedResidual W (fun _ => 1) Y id θ =
      W.transpose.mulVec Y-Qm.mulVec θ := by
    change groupedResidual W (fun _ => 1) Y id θ =
      W.transpose.mulVec Y-(W.transpose*W).mulVec θ
    rw [← Matrix.mulVec_mulVec]
    ext j
    simp only [groupedResidual,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
      Pi.sub_apply,id_eq,one_mul,mul_sub,Finset.sum_sub_distrib]
  have hinv : Qm⁻¹*Qm=1 := Matrix.nonsing_inv_mul Qm (isUnit_iff_ne_zero.mpr hQ)
  have hinv' : Qm*Qm⁻¹=1 := Matrix.mul_nonsing_inv Qm (isUnit_iff_ne_zero.mpr hQ)
  rw [hr,sub_eq_zero]
  constructor
  · intro h
    calc θ = Qm⁻¹.mulVec (Qm.mulVec θ) := by
           rw [Matrix.mulVec_mulVec,hinv,Matrix.one_mulVec]
         _ = Qm⁻¹.mulVec (W.transpose.mulVec Y) := by rw [← h]
         _ = ols W Y := rfl
  · intro h
    rw [h]
    change W.transpose.mulVec Y=Qm.mulVec (Qm⁻¹.mulVec (W.transpose.mulVec Y))
    rw [Matrix.mulVec_mulVec,hinv',Matrix.one_mulVec]

/-- T16's four spending observations use the corrected outcome
Y=log((1+S_post)/(1+S_pre)), with S_pre=1; the actual OLS coefficient is zero. -/
theorem spending_ols_counterexample :
    let W : Matrix (Fin 4) (Fin 2) ℝ := !![1,0;1,0;1,1;1,1]
    let S : Fin 4 → ℝ := ![1,1,0,3]
    let Y := fun i => Real.log ((1+S i)/2)
    ols W Y 1=0 ∧ Real.exp (ols W Y 1)=1 ∧
      (S 0+S 1)/2=1 ∧ (S 2+S 3)/2=3/2 := by
  dsimp only
  let W : Matrix (Fin 4) (Fin 2) ℝ := !![1,0;1,0;1,1;1,1]
  let Y : Fin 4 → ℝ := fun i => Real.log ((1+(![1,1,0,3] : Fin 4 → ℝ) i)/2)
  have hdet : (W.transpose*W).det ≠ 0 := by
    norm_num [W,Matrix.det_fin_two,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ]
  have hl : Real.log (1/2) = -Real.log 2 := by simpa using Real.log_inv (2:ℝ)
  have hr : groupedResidual W (fun _ => 1) Y id 0=0 := by
    ext j
    fin_cases j <;>
      norm_num [groupedResidual,W,Y,id,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hl]
  have heq : ols W Y=0 := ((ols_normal_equation W Y hdet 0).1 hr).symm
  change ols W Y 1=0 ∧ Real.exp (ols W Y 1)=1 ∧ _
  rw [heq]
  norm_num

/-- Appendix C's alternative coefficients (b+cα,cβ,cγ), p. 265. -/
def affineTheta {Q : Type*} [DecidableEq Q] (intercept : Q) (b c : ℝ) (θ : Q → ℝ) : Q → ℝ :=
  fun j => (if j=intercept then b else 0)+c*θ j

/-- P015-T21(ii): with a unit intercept, the affine coefficients give predictor
b+c W_i θ, observation by observation. -/
theorem affine_predictor {N Q : Type*} [Fintype Q] [DecidableEq Q]
    (W : Matrix N Q ℝ) (j₀ : Q) (hW : ∀ i, W i j₀ = 1)
    (b c : ℝ) (θ : Q → ℝ) :
    ∀ i, W.mulVec (affineTheta j₀ b c θ) i = b+c*W.mulVec θ i := by
  intro i
  simp only [Matrix.mulVec, dotProduct, affineTheta, mul_add, Finset.sum_add_distrib]
  have hs : (∑ j, W i j*(c*θ j)) = c*∑ j, W i j*θ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  simp [mul_ite, Finset.sum_ite_eq, hW]

/-- P015-T21(i),(iii): the exact logistic score and the unique linearized
root when W'W is invertible. The scale c applies to that root, not the exact MLE. -/
theorem logistic_linearization (N K : ℕ) (W : Matrix (Fin N) (Fin (K+2)) ℝ)
    (Y : Fin N → ℝ) (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (hQ : (W.transpose*W).det ≠ 0) (b c : ℝ) (hc : c ≠ 0) :
    (∀ θ v : Fin (K+2) → ℝ,
      HasDerivAt (fun t => groupedLikelihood W (fun _ => 1) Y logistic (fun j => θ j+t*v j))
        (∑ i, (Y i-logistic (W.mulVec θ i))*W.mulVec v i) 0) ∧
    (∃! θ : Fin (K+2) → ℝ, groupedResidual W (fun _ => 1) Y (fun a => b+c*a) θ = 0) ∧
    (∀ θ, groupedResidual W (fun _ => 1) Y (fun a => b+c*a) θ = 0 →
      affineTheta 0 b c θ = ols W Y ∧ ols W Y 1 = c*θ 1) := by
  have hlin : ∀ θ : Fin (K+2) → ℝ,
      groupedResidual W (fun _ => 1) Y (fun a => b+c*a) θ=0 ↔
        affineTheta 0 b c θ=ols W Y := by
    intro θ
    have hres : groupedResidual W (fun _ => 1) Y (fun a => b+c*a) θ =
        groupedResidual W (fun _ => 1) Y id (affineTheta 0 b c θ) := by
      ext j
      unfold groupedResidual
      apply Finset.sum_congr rfl
      intro i _
      rw [affine_predictor W 0 hW b c θ i]
      rfl
    rw [hres]
    exact ols_normal_equation W Y hQ _
  let θ₀ : Fin (K+2) → ℝ := fun j => (ols W Y j-(if j=0 then b else 0))/c
  have haff : affineTheta 0 b c θ₀=ols W Y := by
    ext j
    dsimp [affineTheta,θ₀]
    field_simp [hc]
    <;> ring
  refine ⟨?_,?_,?_⟩
  · intro θ v
    simpa only [logistic_multiplier,one_mul] using
      likelihood_directional_derivative_calculus W (fun _ => 1) Y logistic θ v
        (fun i => differentiableAt_sigmoid)
        (fun i => Real.sigmoid_pos _) (fun i => Real.sigmoid_lt_one _)
  · refine ⟨θ₀,(hlin θ₀).2 haff,?_⟩
    intro θ hθ
    have hh := (hlin θ).1 hθ
    ext j
    apply mul_left_cancel₀ hc
    have h₁ := congrFun hh j
    have h₂ := congrFun haff j
    dsimp [affineTheta] at h₁ h₂
    linarith
  · intro θ hθ
    have hh := (hlin θ).1 hθ
    refine ⟨hh,?_⟩
    have hn : (1 : Fin (K+2)) ≠ 0 := by
      norm_num [Fin.ext_iff,Nat.mod_eq_of_lt (by omega : 1<K+2)]
    simpa [affineTheta,hn] using (congrFun hh 1).symm

/-- Exact remainder identity for the exact ML root (T21 finite lemma):
discarding R gives the paper's affine scaling, but the exact coefficient retains R. -/
theorem logistic_exact_remainder {N Q : Type*} [Fintype N] [Fintype Q] [DecidableEq Q]
    (W : Matrix N Q ℝ) (j₀ : Q) (hW : ∀ i, W i j₀=1) (Y : N → ℝ)
    (hQ : (W.transpose*W).det ≠ 0) (b c : ℝ) (θ : Q → ℝ)
    (hScore : groupedResidual W (fun _ => 1) Y logistic θ = 0) :
    let R := fun i => logistic (W.mulVec θ i)-(b+c*W.mulVec θ i)
    ols W Y = affineTheta j₀ b c θ+(W.transpose*W)⁻¹.mulVec (W.transpose.mulVec R) := by
  dsimp only
  let R : N → ℝ := fun i => logistic (W.mulVec θ i)-(b+c*W.mulVec θ i)
  have hs : W.transpose.mulVec (Y-(fun i => logistic (W.mulVec θ i)))=0 := by
    ext j
    have hj := congrFun hScore j
    simpa only [groupedResidual,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
      Pi.sub_apply,Pi.zero_apply,one_mul] using hj
  rw [Matrix.mulVec_sub,sub_eq_zero] at hs
  have hf : (fun i => logistic (W.mulVec θ i))=W.mulVec (affineTheta j₀ b c θ)+R := by
    ext i
    rw [Pi.add_apply,affine_predictor W j₀ hW b c θ i]
    dsimp [R]
    ring
  have hh : W.transpose.mulVec Y=(W.transpose*W).mulVec (affineTheta j₀ b c θ)+
      W.transpose.mulVec R := by
    rw [hs,hf,Matrix.mulVec_add,Matrix.mulVec_mulVec]
  change (W.transpose*W)⁻¹.mulVec (W.transpose.mulVec Y)=
    affineTheta j₀ b c θ+(W.transpose*W)⁻¹.mulVec (W.transpose.mulVec R)
  rw [hh,Matrix.mulVec_add,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hQ),Matrix.one_mulVec]

/-- Taylor polynomials of the printed inverse link about a real center,
P015-T11 and T12, using Mathlib's iterated derivatives (all degrees, not sampled orders). -/
def logisticTaylor (N : ℕ) (c a : ℝ) : ℝ := taylorWithinEval logistic N Set.univ c a
/-- The explicit 200-observation likelihood of P015-T11, p. 257 counterexample. -/
def extremeLikelihood (θ : Fin 2 → ℝ) : ℝ :=
  binomialLogLikelihood logistic 100 1 (θ 0)+binomialLogLikelihood logistic 100 99 (θ 0+θ 1)




/-- P015-T11 finite evaluations and the degree-zero error. -/
theorem extreme_sigmoid_arithmetic :
    logistic (Real.log 99) = 99/100 ∧ logistic (-Real.log 99) = 1/100 ∧
    logit ((1+99)/200) = 0 ∧ Real.pi < 9/2 ∧
    |logisticTaylor 0 0 (Real.log 99)-logistic (Real.log 99)| = 49/100 := by
  have h : logistic (Real.log 99) = 99/100 := by
    rw [logistic_exp, Real.exp_log (by norm_num)]
    norm_num
  have hn : logistic (-Real.log 99) = 1/100 := by
    rw [logistic, Real.sigmoid_neg]
    change 1-logistic (Real.log 99) = 1/100
    rw [h]; norm_num
  refine ⟨h,hn,?_,?_,?_⟩
  · norm_num [logit]
  · linarith [Real.pi_lt_four]
  · rw [logisticTaylor, taylor_within_zero_eval, h]
    norm_num [logistic, Real.sigmoid_zero]

/-- General V_i=(1,X_i), p. 253, and W_i=(1,D_i,X_i), p. 262,
with exactly K control entries. -/
def controlRow {K : ℕ} (x : Fin K → ℝ) : Fin (K+1) → ℝ := Fin.cases 1 x
/-- W_i=(1 D_i X_i), Appendix A, p. 262, with exactly K controls. -/
def regressorRow {K : ℕ} (d : ℝ) (x : Fin K → ℝ) : Fin (K+2) → ℝ :=
  Fin.cases 1 (Fin.cases d x)
/-- The affine potential-outcome form (1), p. 253. -/
def affineOutcome (y₀ τ d : ℝ) : ℝ := y₀+τ*d
/-- n×(K+1) and n×(K+2) sample design matrices of Appendix A. -/
def designV {Ω : Type*} {K : ℕ} (X : ℕ → Ω → Fin K → ℝ) (n : ℕ) (s : Ω) :
    Matrix (Fin n) (Fin (K+1)) ℝ := fun i => controlRow (X i s)
/-- The n×(K+2) matrix whose ith row is W_i=(1 D_i X_i), Appendix A, p. 262. -/
def designW {Ω : Type*} {K : ℕ} (D : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (n : ℕ) (s : Ω) : Matrix (Fin n) (Fin (K+2)) ℝ := fun i => regressorRow (D i s) (X i s)
/-- ωhat=(V′V)^-1 V′D, Appendix A, p. 262, the fitted treatment-on-controls coefficients. -/
def omegaHat {Ω : Type*} {K : ℕ} (D : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (n : ℕ) (s : Ω) : Fin (K+1) → ℝ := ols (designV X n s) (fun i => D i s)
/-- Dtilde_i=D_i-V_i ωhat, Appendix A, p. 262; the estimated weight is Dtilde_i², Expression (9), p. 255. -/
def residualHat {Ω : Type*} {K : ℕ} (D : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (n : ℕ) (s : Ω) : Fin n → ℝ :=
  sampleResidual (designV X n s) (fun i => D i s) (omegaHat D X n s)
/-- The treatment entry βhat of (W′W)^-1 W′Y, Appendix A, p. 262, with Y_i=Y_0i+τ_iD_i from (1), p. 253. -/
def betaHat {Ω : Type*} {K : ℕ} (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (n : ℕ) (s : Ω) : ℝ :=
  ols (designW D X n s) (fun i => affineOutcome (Y₀ i s) (τ i s) (D i s)) 1

/-- (7)'s population residual weight with general, possibly continuous X:
conditional expectation is on the σ-algebra generated by X. -/
def populationWeight {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (P : Measure Ω) (D : Ω → ℝ) (X : Ω → B) (s : Ω) : ℝ :=
  (D s-P[D | MeasurableSpace.comap X inferInstance] s)^2
/-- Conditional variance by its squared-centered conditional expectation,
Expression (8), p. 255. -/
def conditionalVariance {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (P : Measure Ω) (D : Ω → ℝ) (X : Ω → B) : Ω → ℝ :=
  P[populationWeight P D X | MeasurableSpace.comap X inferInstance]

/-- P015-T19, Expression (8), for any covariates and finite-variance treatment:
the conditional mean of w is the conditional variance, by its definition. -/
theorem conditional_weight_variance {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → ℝ) (X : Ω → B)
    (hD : MemLp D 2 P) (hX : Measurable X) :
    P[populationWeight P D X | MeasurableSpace.comap X inferInstance] = conditionalVariance P D X := rfl

/-- P015-T19 binary version of (8): conditional variance is π(X)(1-π(X)),
with general covariates and conditional expectation, not just finite tables. -/
theorem binary_conditional_variance {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → ℝ) (X : Ω → B)
    (hD : Measurable D) (hX : Measurable X) (hbin : ∀ᵐ s ∂P, D s=0 ∨ D s=1) :
    conditionalVariance P D X =ᵐ[P] fun s =>
      P[D | MeasurableSpace.comap X inferInstance] s*(1-P[D | MeasurableSpace.comap X inferInstance] s) := by
  have h₂ : MemLp D 2 P := MemLp.of_bound hD.aestronglyMeasurable 1 (by
    filter_upwards [hbin] with s hs
    rcases hs with hs | hs <;> simp [hs])
  have hsq : (D ^ 2) =ᵐ[P] D := by
    filter_upwards [hbin] with s hs
    rcases hs with hs | hs <;> simp [Pi.pow_apply, hs]
  have hc := condExp_congr_ae (m := MeasurableSpace.comap X inferInstance) hsq
  have hv := condVar_ae_eq_condExp_sq_sub_sq_condExp (Measurable.comap_le hX) h₂
  filter_upwards [hc, hv] with s hs hv
  change conditionalVariance P D X s = _
  change condVar (MeasurableSpace.comap X inferInstance) D P s = _
  rw [hv]
  simp only [Pi.sub_apply, Pi.pow_apply, hs]
  ring

/-- “well behaved”, A.1 condition 4, pp. 262–263: a moment is integrable,
and its sample average converges in probability to its population expectation.
Convergence in measure on a probability space is convergence in probability. -/
def MomentLLN {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : ℕ → Ω → ℝ) : Prop :=
  (∀ i, Integrable (Z i) P) ∧ TendstoInMeasure P
    (fun n s => (∑ i : Fin n, Z i s)/(n : ℝ)) atTop (fun _ => ∫ s, Z 0 s ∂P)

/-- The exact eight moment families and nonsingularity required in a
sufficient reading of condition 4; no OLS limit is assumed here. -/
def OLSRegularity {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (P : Measure Ω)
    (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ) : Prop :=
  (∀ j k, MomentLLN P (fun i s => controlRow (X i s) j*controlRow (X i s) k)) ∧
  (∀ j, MomentLLN P (fun i s => controlRow (X i s) j*D i s)) ∧
  MomentLLN P (fun i s => D i s^2) ∧ MomentLLN P (fun i s => D i s*Y₀ i s) ∧
  (∀ j, MomentLLN P (fun i s => controlRow (X i s) j*Y₀ i s)) ∧
  MomentLLN P (fun i s => D i s^2*τ i s) ∧
  (∀ j, MomentLLN P (fun i s => controlRow (X i s) j*D i s*τ i s)) ∧
  (∀ j k, MomentLLN P (fun i s => controlRow (X i s) j*controlRow (X i s) k*τ i s)) ∧
  Matrix.det (fun j k => ∫ s, controlRow (X 0 s) j*controlRow (X 0 s) k ∂P) ≠ 0 ∧
  Integrable (populationWeight P (D 0) (X 0)) P ∧
  0 < ∫ s, populationWeight P (D 0) (X 0) s ∂P




/-- Assemble delta=(alpha,beta,gamma)' from the (alpha,gamma) control
coefficients and the treatment coefficient beta, Appendix A, p. 262. -/
def combineCoefficients {K : ℕ} (a : Fin (K+1) → ℝ) (β : ℝ) : Fin (K+2) → ℝ :=
  Fin.cases (a 0) (Fin.cases β (fun j => a j.succ))

/-- The coefficient column in Model (6) has the same fitted values whether
written W*delta or beta*D+V*(alpha,gamma), pp. 254/262. -/
theorem combined_predictor (n K : ℕ) (D : Fin n → ℝ) (X : Fin n → Fin K → ℝ)
    (a : Fin (K+1) → ℝ) (β : ℝ) (i : Fin n) :
    Matrix.mulVec (fun i => regressorRow (D i) (X i)) (combineCoefficients a β) i =
      β*D i+Matrix.mulVec (fun i => controlRow (X i)) a i := by
  simp [Matrix.mulVec,dotProduct,regressorRow,controlRow,combineCoefficients,Fin.sum_univ_succ]
  ring

/-- Residual orthogonality to every control column implies orthogonality to
its every fitted linear combination, the finite step in partial regression (12). -/
theorem residual_orthogonal_predictor {N Q : Type*} [Fintype N] [Fintype Q]
    (V : Matrix N Q ℝ) (r : N → ℝ) (hr : ∀ j, ∑ i, r i*V i j=0) (a : Q → ℝ) :
    (∑ i, r i*V.mulVec a i)=0 := by
  simp only [Matrix.mulVec,dotProduct]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (j : Q) : (∑ i, r i*(V i j*a j))=(∑ i, r i*V i j)*a j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [he,hr,zero_mul,Finset.sum_const_zero]

/-- T22 finite lemma (12), p. 262: FWL with the actual OLS control residual;
invertibility of the full design Gram matrix implies positive residual sum of squares. -/
theorem partial_regression (n K : ℕ) (D Y : Fin n → ℝ) (X : Fin n → Fin K → ℝ)
    (hQ : Matrix.det ((fun j k : Fin (K+2) =>
      ∑ i : Fin n, regressorRow (D i) (X i) j*regressorRow (D i) (X i) k) :
      Matrix (Fin (K+2)) (Fin (K+2)) ℝ) ≠ 0) :
    let V : Matrix (Fin n) (Fin (K+1)) ℝ := fun i => controlRow (X i)
    let W : Matrix (Fin n) (Fin (K+2)) ℝ := fun i => regressorRow (D i) (X i)
    let r := sampleResidual V D (ols V D)
    0 < (∑ i, r i^2) ∧ (∀ j, ∑ i, r i*V i j = 0) ∧
      ols W Y 1 = (∑ i, r i*Y i)/(∑ i, r i^2) := by
  dsimp only
  let V : Matrix (Fin n) (Fin (K+1)) ℝ := fun i => controlRow (X i)
  let W : Matrix (Fin n) (Fin (K+2)) ℝ := fun i => regressorRow (D i) (X i)
  let ω := ols V D
  let r := sampleResidual V D ω
  change (W.transpose*W).det≠0 at hQ
  have hinjQ := Matrix.mulVec_injective_of_det_ne_zero hQ
  have hinjW : Function.Injective W.mulVec := by
    intro a b hab
    apply hinjQ
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,hab]
  have hinjV : Function.Injective V.mulVec := by
    intro a b hab
    have hc : combineCoefficients a 0=combineCoefficients b 0 := by
      apply hinjW
      ext i
      rw [combined_predictor,combined_predictor]
      simp only [zero_mul,zero_add]
      exact congrFun hab i
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact congrFun hc 0
    · exact congrFun hc j.succ.succ
  have hposV : (V.transpose*V).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.PosDef.conjTranspose_mul_self V hinjV
  have hdetV : (V.transpose*V).det≠0 := hposV.det_pos.ne'
  have hscore := (ols_normal_equation V D hdetV ω).2 rfl
  have hort : ∀ j, ∑ i, r i*V i j=0 := by
    intro j
    have hj := congrFun hscore j
    simpa only [r,sampleResidual,groupedResidual,id_eq,one_mul,mul_comm,Pi.zero_apply] using hj
  have hrspan : W.mulVec (combineCoefficients (-ω) 1)=r := by
    ext i
    rw [combined_predictor]
    simp only [one_mul]
    change D i+V.mulVec (-ω) i=D i-V.mulVec ω i
    rw [Matrix.mulVec_neg]
    rfl
  have hN : 0<(∑ i, r i^2) := by
    have hn : 0≤∑ i, r i^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    by_contra h
    have hz : (∑ i, r i^2)=0 := le_antisymm (le_of_not_gt h) hn
    have hrzero : r=0 := by
      ext i
      have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (r i))).mp hz i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp hs
    have hc : combineCoefficients (-ω) 1=0 := hinjW (by rw [hrspan,hrzero,Matrix.mulVec_zero])
    have hf := congrFun hc (0 : Fin (K+1)).succ
    change (1 : ℝ)=0 at hf
    norm_num at hf
  let t := ols W Y
  let a : Fin (K+1) → ℝ := Fin.cases (t 0) (fun j => t j.succ.succ)
  have ht : combineCoefficients a (t 1)=t := by
    ext j
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;> rfl
  have hnorm : W.transpose.mulVec (Y-W.mulVec t)=0 := by
    have hh := (ols_normal_equation W Y hQ t).2 rfl
    ext j
    simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Pi.sub_apply,
      groupedResidual,id_eq,one_mul] using congrFun hh j
  have hnr : (∑ i, r i*(Y i-W.mulVec t i))=0 := by
    change dotProduct r (Y-W.mulVec t)=0
    rw [← hrspan,← Matrix.vecMul_transpose W,← Matrix.dotProduct_mulVec,hnorm]
    simp
  have hrD : (∑ i, r i*D i)=(∑ i, r i^2) := by
    have he : D=r+V.mulVec ω := by
      ext i
      simp [r,sampleResidual]
    rw [he]
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,
      residual_orthogonal_predictor V r hort ω,add_zero]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrfit : (∑ i, r i*W.mulVec t i)=t 1*(∑ i, r i^2) := by
    have hfit (i : Fin n) : W.mulVec t i=t 1*D i+V.mulVec a i := by
      calc W.mulVec t i = W.mulVec (combineCoefficients a (t 1)) i := by rw [ht]
           _ = t 1*D i+V.mulVec a i := combined_predictor n K D X a (t 1) i
    simp only [hfit,mul_add,Finset.sum_add_distrib]
    rw [residual_orthogonal_predictor V r hort a]
    simp only [add_zero]
    calc (∑ i, r i*(t 1*D i)) = t 1*(∑ i, r i*D i) := by
           rw [Finset.mul_sum]
           apply Finset.sum_congr rfl
           intro i _
           ring
         _ = t 1*(∑ i, r i^2) := by rw [hrD]
  simp_rw [mul_sub,Finset.sum_sub_distrib] at hnr
  rw [hrfit] at hnr
  refine ⟨hN,hort,?_⟩
  change t 1=(∑ i, r i*Y i)/(∑ i, r i^2)
  apply (eq_div_iff hN.ne').2
  linarith

/-- T22 finite lemma (13), p. 263: the exact three-term numerator decomposition,
for every fixed sample; FWL separately identifies this ratio with the OLS coefficient. -/
theorem regression_decomposition_algebra {N : Type*} [Fintype N] (r m Y₀ τ : N → ℝ) :
    (∑ i, r i*(Y₀ i+τ i*(r i+m i)))/(∑ i, r i^2) =
      (∑ i, r i*Y₀ i)/(∑ i, r i^2)+
      (∑ i, r i*m i*τ i)/(∑ i, r i^2)+
      (∑ i, r i^2*τ i)/(∑ i, r i^2) := by
  rw [← add_div, ← add_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- T23's exact finite identity: replacing ω by ωhat changes a squared
residual weighted by Z by the linear cross term and the quadratic coefficient error. -/
theorem residual_weight_expansion {N : Type*} [Fintype N] (r e Z : N → ℝ) :
    (∑ i, (r i-e i)^2*Z i) = (∑ i, r i^2*Z i)-2*(∑ i, r i*Z i*e i)+
      (∑ i, Z i*e i^2) := by
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- T23's regularity: all seven required moment families, including
covariate interactions needed when replacing ω by its fitted value. -/
def CovariateRegularity {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (P : Measure Ω)
    (D Z : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ) (ω : Fin (K+1) → ℝ) : Prop :=
  let r := fun i s => D i s-dotProduct (controlRow (X i s)) ω
  (∀ j k, MomentLLN P (fun i s => controlRow (X i s) j*controlRow (X i s) k)) ∧
  (∀ j, MomentLLN P (fun i s => controlRow (X i s) j*D i s)) ∧
  MomentLLN P (fun i s => r i s^2*Z i s) ∧ MomentLLN P (fun i s => r i s^2) ∧
  (∀ j, MomentLLN P (fun i s => r i s*Z i s*controlRow (X i s) j)) ∧
  (∀ j, MomentLLN P (fun i s => r i s*controlRow (X i s) j)) ∧
  (∀ j k, MomentLLN P (fun i s => Z i s*controlRow (X i s) j*controlRow (X i s) k)) ∧
  Matrix.det (fun j k => ∫ s, controlRow (X 0 s) j*controlRow (X 0 s) k ∂P) ≠ 0 ∧
  0 < ∫ s, r 0 s^2 ∂P




/-- T24 population finite-moment lemma: under common random assignment,
a centered squared treatment weight is independent of τ and cancels exactly. -/
theorem randomization_weight_cancels {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D τ : Ω → ℝ)
    (hD : Measurable D) (hτ : Measurable τ) (hi : IndepFun D τ P) (m : ℝ)
    (hW : Integrable (fun s => (D s-m)^2) P) (hT : Integrable τ P)
    (hpos : 0 < ∫ s, (D s-m)^2 ∂P) :
    (∫ s, (D s-m)^2*τ s ∂P) = (∫ s, (D s-m)^2 ∂P)*(∫ s, τ s ∂P) ∧
    (∫ s, (D s-m)^2*τ s ∂P)/(∫ s, (D s-m)^2 ∂P) = ∫ s, τ s ∂P := by
  have hi' : IndepFun (fun s => (D s-m)^2) τ P := by
    exact hi.comp (by fun_prop : Measurable (fun d : ℝ => (d-m)^2)) measurable_id
  have h := hi'.integral_mul_eq_mul_integral hW.aestronglyMeasurable hT.aestronglyMeasurable
  change (∫ s, (D s-m)^2*τ s ∂P) = (∫ s, (D s-m)^2 ∂P)*(∫ s, τ s ∂P) at h
  refine ⟨h,?_⟩
  rw [h]
  field_simp [hpos.ne']
















/-- T1(e): the actual population OLS coefficient equals the effective-weight
causal average and differs from 3/2; nonsingularity follows from the Gram determinant. -/
theorem rare_ols_arithmetic :
    let p := rareLaw (1/1000000)
    let W : Matrix (Fin 4) (Fin 3) ℝ := fun i => ![1,binaryD i,binaryX i]
    Matrix.det (fun j k => fExpectation p (fun i => W i j*W i k)) ≠ 0 ∧
    populationOLS p W (fun i => rareY i (binaryD i)) 1 = 500000999999/250000999999 := by
  dsimp only
  let p := rareLaw (1/1000000)
  let W : Matrix (Fin 4) (Fin 3) ℝ := fun i => ![1,binaryD i,binaryX i]
  let Q : Matrix (Fin 3) (Fin 3) ℝ := fun j k => fExpectation p (fun i => W i j*W i k)
  let t : Fin 3 → ℝ := ![-250000/250000999999,500000999999/250000999999,1000005499995/500001999998]
  have hdet : Q.det ≠ 0 := by
    rw [Matrix.det_fin_three]
    norm_num [Q,p,W,fExpectation,rareLaw,binaryX,binaryD,Matrix.det_fin_three,Fin.sum_univ_succ]
  have heq : Q.mulVec t = (fun j => fExpectation p (fun i => W i j*rareY i (binaryD i))) := by
    norm_num [Q,p,W,t,fExpectation,rareLaw,rareY,binaryX,binaryD,Matrix.mulVec,
      dotProduct,funext_iff,Fin.forall_fin_succ,Fin.sum_univ_succ]
  refine ⟨hdet,?_⟩
  change (Q⁻¹.mulVec (fun j => fExpectation p (fun i => W i j*rareY i (binaryD i)))) 1 = _
  rw [← heq, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hdet)]
  simp [t]

/-- T2: the two profile-specific supports meet only at zero, so no distinct
pair has positivity at both profiles, under either nominal or effective law. -/
theorem common_support_arithmetic :
    (∀ d : ℝ, (0 < fCondProb multiLaw binaryX multiD 0 d ∧
      0 < fCondProb multiLaw binaryX multiD 1 d) ↔ d=0) ∧
    (∀ d : ℝ, (0 < fCondProb (fEffective multiLaw binaryX multiD) binaryX multiD 0 d ∧
      0 < fCondProb (fEffective multiLaw binaryX multiD) binaryX multiD 1 d) ↔ d=0) := by
  constructor <;> intro d <;> by_cases h₀ : d=0 <;> by_cases h₁ : d=1 <;> by_cases h₂ : d=2 <;>
    norm_num [fCondProb,fEffective,fWeight,fCondMean,fExpectation,fMass,multiLaw,binaryX,multiD,
      Fin.sum_univ_succ,h₀,h₁,h₂,eq_comm] <;> simp_all


namespace ConditionalCompletion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem unconfounded_zero_terms_completed {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : Ω → ℝ) (X : Ω → Fin K → ℝ) (hX : Measurable X)
    (hD : Measurable D) (hY : Measurable Y₀) (hτ : Measurable τ)
    (hunconf : CondIndepFun (MeasurableSpace.comap X inferInstance)
      (Measurable.comap_le hX) (fun s => (Y₀ s,τ s)) D P)
    (ω : Fin (K+1) → ℝ)
    (hlinear : P[D | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => dotProduct (controlRow (X s)) ω)
    (hiD : Integrable D P) (hiY : Integrable Y₀ P) (hiτ : Integrable τ P)
    (hiDY : Integrable (fun s => D s*Y₀ s) P)
    (himY : Integrable (fun s => dotProduct (controlRow (X s)) ω*Y₀ s) P)
    (hirτ : Integrable (fun s => (D s-dotProduct (controlRow (X s)) ω)*τ s) P)
    (hirmτ : Integrable (fun s => (D s-dotProduct (controlRow (X s)) ω)*
      dotProduct (controlRow (X s)) ω*τ s) P) :
    (P[(fun s => D s*Y₀ s) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => P[D | MeasurableSpace.comap X inferInstance] s*
        P[Y₀ | MeasurableSpace.comap X inferInstance] s) ∧
    (P[(fun s => (D s-dotProduct (controlRow (X s)) ω)*τ s) |
      MeasurableSpace.comap X inferInstance] =ᵐ[P] fun _ => 0) ∧
    ((∫ s, D s*Y₀ s ∂P)-(∫ s, dotProduct (controlRow (X s)) ω*Y₀ s ∂P)=0) ∧
    (∫ s, (D s-dotProduct (controlRow (X s)) ω)*dotProduct (controlRow (X s)) ω*τ s ∂P)=0 := by
  let M : Ω → ℝ:=fun s=>dotProduct (controlRow (X s)) ω
  have hmle:=Measurable.comap_le hX
  have hXm : Measurable[MeasurableSpace.comap X inferInstance] X:=
    measurable_iff_comap_le.mpr le_rfl
  have hv (j : Fin (K+1)) :
      Measurable[MeasurableSpace.comap X inferInstance] (fun s=>controlRow (X s) j):=by
    refine Fin.cases ?_ (fun k=>?_) j
    · simpa [controlRow] using (measurable_const : Measurable[MeasurableSpace.comap X inferInstance] (fun _ : Ω=>(1:ℝ)))
    · simpa [controlRow,Function.comp_def] using (measurable_pi_apply k).comp hXm
  have hM : Measurable[MeasurableSpace.comap X inferInstance] M:=by
    unfold M dotProduct
    exact Finset.measurable_sum Finset.univ (fun j _=>(hv j).mul_const (ω j))
  have hDYind : CondIndepFun (MeasurableSpace.comap X inferInstance) hmle D Y₀ P:=by
    convert (hunconf.comp measurable_fst measurable_id).symm using 1 <;> rfl
  have hDTind : CondIndepFun (MeasurableSpace.comap X inferInstance) hmle D τ P:=by
    convert (hunconf.comp measurable_snd measurable_id).symm using 1 <;> rfl
  have hDY:=condExp_product P hmle D Y₀ hD hY hDYind hiD hiY hiDY
  have hR : P[(fun s=>(D s-M s)*τ s)|MeasurableSpace.comap X inferInstance]=ᵐ[P] fun _=>0 := by
    filter_upwards [ae_indep_condExpKernel P hmle D τ hD hτ hDTind,
      ae_kernel_constant P hmle M hM,
      condExp_ae_eq_integral_condExpKernel hmle hiD,hlinear,
      condExp_ae_eq_integral_condExpKernel hmle hirτ,
      hiD.condExpKernel_ae (m:=MeasurableSpace.comap X inferInstance)]
      with s hs hm hmean hlin hprod hiDk
    rw [hprod]
    have hmean' : (∫t,D t∂condExpKernel P (MeasurableSpace.comap X inferInstance) s)=M s:=hmean.symm.trans hlin
    calc
      _ = ∫t,(D t-M s)*τ t∂condExpKernel P (MeasurableSpace.comap X inferInstance) s := by
        apply integral_congr_ae
        filter_upwards [hm] with t ht
        change (D t-M t)*τ t=(D t-M s)*τ t
        rw [ht]
      _ = (∫t,D t-M s∂condExpKernel P (MeasurableSpace.comap X inferInstance) s)*
          (∫t,τ t∂condExpKernel P (MeasurableSpace.comap X inferInstance) s) :=
        (hs.comp (measurable_id.sub_const (M s)) measurable_id).integral_fun_mul_eq_mul_integral
          (hD.sub_const (M s)).aestronglyMeasurable hτ.aestronglyMeasurable
      _ = 0:=by rw [integral_sub hiDk (integrable_const _),integral_const,hmean'];simp
  have hMY:=condExp_mul_of_stronglyMeasurable_left hM.stronglyMeasurable himY hiY
  have hCEeq : P[(fun s=>D s*Y₀ s)|MeasurableSpace.comap X inferInstance]=ᵐ[P]
      P[(fun s=>M s*Y₀ s)|MeasurableSpace.comap X inferInstance] := by
    filter_upwards [hDY,hMY,hlinear] with s hd hm hlin
    change P[(fun u=>M u*Y₀ u)|MeasurableSpace.comap X inferInstance] s= M s*P[Y₀|MeasurableSpace.comap X inferInstance] s at hm
    rw [hd,hm,hlin]
  have hE : (∫s,D s*Y₀ s∂P)=(∫s,M s*Y₀ s∂P):=by
    calc
      _ = ∫s,P[(fun s=>D s*Y₀ s)|MeasurableSpace.comap X inferInstance] s∂P :=
        (integral_condExp hmle).symm
      _ = ∫s,P[(fun s=>M s*Y₀ s)|MeasurableSpace.comap X inferInstance] s∂P :=
        integral_congr_ae hCEeq
      _ = _:=integral_condExp hmle
  have hiMR : Integrable (fun s=>M s*((D s-M s)*τ s)) P:=by
    refine hirmτ.congr (Eventually.of_forall (fun s=>?_))
    dsimp [M];ring
  have hMR:=condExp_mul_of_stronglyMeasurable_left hM.stronglyMeasurable hiMR hirτ
  have hCEzero : P[(fun s=>M s*((D s-M s)*τ s))|MeasurableSpace.comap X inferInstance]=ᵐ[P] fun _=>0:=by
    filter_upwards [hMR,hR] with s hm hr
    change P[(fun u=>M u*((D u-M u)*τ u))|MeasurableSpace.comap X inferInstance] s= M s*P[(fun u=>(D u-M u)*τ u)|MeasurableSpace.comap X inferInstance] s at hm
    rw [hm,hr,mul_zero]
  have hI : (∫s,M s*((D s-M s)*τ s)∂P)=0:=by
    have hh:=integral_congr_ae hCEzero
    rw [integral_condExp hmle,integral_zero] at hh
    exact hh
  refine ⟨hDY,hR,sub_eq_zero.mpr hE,?_⟩
  convert hI using 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun s=>by dsimp [M];ring)

end
end ConditionalCompletion

theorem unconfounded_zero_terms {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : Ω → ℝ) (X : Ω → Fin K → ℝ) (hX : Measurable X)
    (hD : Measurable D) (hY : Measurable Y₀) (hτ : Measurable τ)
    (hunconf : CondIndepFun (MeasurableSpace.comap X inferInstance)
      (Measurable.comap_le hX) (fun s => (Y₀ s,τ s)) D P)
    (ω : Fin (K+1) → ℝ)
    (hlinear : P[D | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => dotProduct (controlRow (X s)) ω)
    (hiD : Integrable D P) (hiY : Integrable Y₀ P) (hiτ : Integrable τ P)
    (hiDY : Integrable (fun s => D s*Y₀ s) P)
    (himY : Integrable (fun s => dotProduct (controlRow (X s)) ω*Y₀ s) P)
    (hirτ : Integrable (fun s => (D s-dotProduct (controlRow (X s)) ω)*τ s) P)
    (hirmτ : Integrable (fun s => (D s-dotProduct (controlRow (X s)) ω)*
      dotProduct (controlRow (X s)) ω*τ s) P) :
    (P[(fun s => D s*Y₀ s) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun s => P[D | MeasurableSpace.comap X inferInstance] s*
        P[Y₀ | MeasurableSpace.comap X inferInstance] s) ∧
    (P[(fun s => (D s-dotProduct (controlRow (X s)) ω)*τ s) |
      MeasurableSpace.comap X inferInstance] =ᵐ[P] fun _ => 0) ∧
    ((∫ s, D s*Y₀ s ∂P)-(∫ s, dotProduct (controlRow (X s)) ω*Y₀ s ∂P)=0) ∧
    (∫ s, (D s-dotProduct (controlRow (X s)) ω)*dotProduct (controlRow (X s)) ω*τ s ∂P)=0 := by
  exact ConditionalCompletion.unconfounded_zero_terms_completed (Ω := Ω) (P := P) (K := K) (D := D) (Y₀ := Y₀) (τ := τ) (X := X) (hX := hX) (hD := hD) (hY := hY) (hτ := hτ) (hunconf := hunconf) (ω := ω) (hlinear := hlinear) (hiD := hiD) (hiY := hiY) (hiτ := hiτ) (hiDY := hiDY) (himY := himY) (hirτ := hirτ) (hirmτ := hirmτ)


/-- A finite probability law's zero variance forces every positive-mass
atom to equal the mean, the finite proof of corrected positivity T4(i). -/
theorem finite_variance_zero_iff {A : Type*} [Fintype A] (p D : A → ℝ) (hlaw : IsLaw p) :
    fVariance p D = 0 ↔ ∀ a, 0 < p a → D a=fExpectation p D := by
  constructor
  · intro h a hpa
    have hn : ∀ i ∈ (Finset.univ : Finset A), 0 ≤ p i*(D i-fExpectation p D)^2 := by
      intro i _
      exact mul_nonneg (hlaw.1 i) (sq_nonneg _)
    have hs := (Finset.sum_eq_zero_iff_of_nonneg hn).mp h a (Finset.mem_univ a)
    have hz : (D a-fExpectation p D)^2 = 0 := (mul_eq_zero.mp hs).resolve_left hpa.ne'
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro h
    unfold fVariance fExpectation
    apply Finset.sum_eq_zero
    intro a _
    by_cases hp : p a=0
    · simp [hp]
    · have hpa : 0 < p a := lt_of_le_of_ne (hlaw.1 a) (Ne.symm hp)
      have hd := h a hpa
      simp only [fExpectation] at hd
      simp [hd]

/-- T4(i)'s finite proof: two distinct positive-mass treatments force
strictly positive conditional variance. Applied to each normalized profile law. -/
theorem finite_variance_pos_of_atoms {A : Type*} [Fintype A] (p D : A → ℝ)
    (hlaw : IsLaw p) (a b : A) (ha : 0 < p a) (hb : 0 < p b) (hd : D a ≠ D b) :
    0 < fVariance p D := by
  have hn : 0 ≤ fVariance p D := by
    unfold fVariance fExpectation
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hlaw.1 i) (sq_nonneg _)
  by_contra h
  have hz : fVariance p D=0 := le_antisymm (le_of_not_gt h) hn
  have he := (finite_variance_zero_iff p D hlaw).mp hz
  exact hd ((he a ha).trans (he b hb).symm)

/-- P015-T11: the actual predictor log 99 is beyond 9/2, proved with
Mathlib's bound exp(1)<2.7182818286. -/
theorem log99_lower_bound : 9/2 < Real.log 99 := by
  have he : Real.exp 1 < 11/4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hp : (Real.exp 1)^9 < (99 : ℝ)^2 := by
    calc
      (Real.exp 1)^9 < (11/4 : ℝ)^9 := by gcongr
      _ < 99^2 := by norm_num
  have hl : Real.exp 9 = (Real.exp 1)^9 := by
    simpa using Real.exp_nat_mul (1 : ℝ) 9
  have hr : Real.exp (2*Real.log 99) = (99 : ℝ)^2 := by
    simpa [Real.exp_log (by norm_num : (0 : ℝ) < 99)] using Real.exp_nat_mul (Real.log 99) 2
  rw [← hl, ← hr, Real.exp_lt_exp] at hp
  linarith

/-- P015-T12(ii): increasing-degree Taylor approximation with a
convergence-domain restriction and Cauchy bound. -/
theorem restricted_taylor_convergence (p r ρ : ℝ) (hp : 0 < p) (hu : p < 1)
    (hr : 0 ≤ r) (hrρ : r < ρ) (hρ : ρ < Real.sqrt ((logit p)^2+Real.pi^2)) :
    let fc := fun z : ℂ => (1+Complex.exp (-z))⁻¹
    let M := sSup ((fun z : ℂ => ‖fc z‖) '' Metric.sphere ((logit p : ℝ) : ℂ) ρ)
    (∃ s : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt fc s ((logit p : ℝ) : ℂ) ∧
      s.radius = ENNReal.ofReal (Real.sqrt ((logit p)^2+Real.pi^2))) ∧
    (∀ N : ℕ, ∀ a : ℝ, |a-logit p| ≤ r →
      |logistic a-logisticTaylor N (logit p) a| ≤ M*(r/ρ)^(N+1)/(1-r/ρ)) ∧
    Tendsto (fun N : ℕ => M*(r/ρ)^(N+1)/(1-r/ρ)) atTop (𝓝 0) := by
  dsimp only
  have hh := UniformTaylorCompletion.uniform_sigmoid_taylor (logit p) r ρ hr hrρ hρ
  refine ⟨?_,?_,?_⟩
  · convert UniformTaylorCompletion.real_center_radius (logit p) using 1 <;> rfl
  · simpa only [UniformTaylorCompletion.fc, TaylorCompletion.fc, logisticTaylor, logistic] using hh.1
  · simpa only [UniformTaylorCompletion.fc, TaylorCompletion.fc] using hh.2


/-- The observed data (X,D,Y(D)) in the two potential-outcome worlds of T2,
p. 261 counterexample. An estimator receives these data, not unobserved endpoints. -/
def multivaluedObserved (Y : Fin 4 → ℝ → ℝ) (a : Fin 4) : ℝ × ℝ × ℝ :=
  (binaryX a,multiD a,Y a (multiD a))

/-- T2's nonidentification consequence in full estimator form: any sequence
of functions of observed samples cannot be consistent under both worlds for two
different targets. The argument applies to iid samples and any other common sampling law. -/
theorem observational_equality_no_two_limits {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (draw : ℕ → Ω → Fin 4)
    (T : ∀ n : ℕ, (Fin n → ℝ × ℝ × ℝ) → ℝ) (c c' : ℝ) (hc : c ≠ c') :
    ¬ (TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldA (draw i s))) atTop (fun _ => c) ∧
      TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldB (draw i s))) atTop (fun _ => c')) := by
  have hobs : multivaluedObserved worldA = multivaluedObserved worldB := by
    funext a
    fin_cases a <;> norm_num [multivaluedObserved,worldA,worldB,binaryX,multiD]
  rintro ⟨ha,hb⟩
  rw [← hobs] at hb
  have he := tendstoInMeasure_ae_unique ha hb
  have hcc : c=c' := by simpa using he
  exact hc hcc

/-- T7 finite population facts for the specified probability law: the outcome
mean is 1/4 for every perturbation with |ε|≤1/16, while the actual population OLS treatment
coefficient is ε. -/
theorem root_ols_arithmetic (ε : ℝ) (hε : |ε| ≤ 1/16) :
    fExpectation rootLaw (rootProbability (1/16) ε)=1/4 ∧
    populationOLS rootLaw rootZ (rootProbability (1/16) ε) 1=ε := by
  have hQ : ((fun j k => fExpectation rootLaw (fun i => rootZ i j*rootZ i k)) :
      Matrix (Fin 3) (Fin 3) ℝ) = !![1,0,0;0,5/24,0;0,0,2/3] :=
    root_link_matrix_arithmetic.2.1
  have hi : ((!![1,0,0;0,5/24,0;0,0,2/3] : Matrix (Fin 3) (Fin 3) ℝ))⁻¹ =
      !![1,0,0;0,24/5,0;0,0,3/2] := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ]
  constructor
  · norm_num [fExpectation,rootLaw,rootProbability,rootBaseline,rootX,rootD,rootE,
      Fin.sum_univ_succ]
    <;> ring
  · unfold populationOLS
    rw [hQ,hi]
    norm_num [fExpectation,rootLaw,rootZ,rootProbability,rootBaseline,rootX,rootD,rootE,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    <;> ring

/-- T3's fitted residuals are the residuals of the actual OLS control fit;
the displayed ordered sample has positive probability 1/256 under the genuine
independent fair binary population. -/
theorem zero_sample_ols_arithmetic :
    ols zeroSampleV zeroSampleD=![0,1/2] ∧
    sampleResidual zeroSampleV zeroSampleD (ols zeroSampleV zeroSampleD)=![0,0,-1/2,1/2] ∧
    iidLaw multiLaw 4 (![0,0,2,3] : Fin 4 → Fin 4)=1/256 := by
  have hdet : (zeroSampleV.transpose*zeroSampleV).det ≠ 0 := by
    norm_num [zeroSampleV,Matrix.det_fin_two,Matrix.mul_apply,Matrix.transpose_apply,
      Fin.sum_univ_succ]
  have hr : groupedResidual zeroSampleV (fun _ => 1) zeroSampleD id ![0,1/2]=0 := by
    norm_num [groupedResidual,zeroSampleV,zeroSampleD,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,funext_iff,Fin.forall_fin_succ,Pi.zero_apply]
  have heq := ((ols_normal_equation zeroSampleV zeroSampleD hdet ![0,1/2]).1 hr).symm
  refine ⟨heq,?_,?_⟩
  · rw [heq]
    norm_num [sampleResidual,zeroSampleV,zeroSampleD,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,funext_iff,Fin.forall_fin_succ]
  · norm_num [iidLaw,multiLaw,Fin.prod_univ_succ]


/-- T1's fixed four-atom observed-data IPW estimator is consistent: for every
positive error threshold the true iid sampling probability tends to zero,
despite this example's small positive regression profile weight. -/
theorem rare_ipw_tail_convergence (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => fMass (iidLaw (rareLaw (1/1000000)) n)
      (fun a => δ ≤ |sampleAverage (rareZ (1/1000000)) n a-3/2|)) atTop (𝓝 0) := by
  let err : ℕ → ℝ := fun n => fMass (iidLaw (rareLaw (1/1000000)) n)
    (fun a => δ ≤ |sampleAverage (rareZ (1/1000000)) n a-3/2|)
  have hnonneg : ∀ n, 0 ≤ err n := by
    intro n
    dsimp [err,fMass]
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact (iid_isLaw (rareLaw (1/1000000)) rare_weight_counterexample.1 n).1 a
    · norm_num
  have hbound : ∀ᶠ n : ℕ in atTop, err n ≤ 2000071/(4*(n:ℝ)*δ^2) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (rare_ipw_all_n n hn).2.2.2 δ hδ
  have hlimit : Tendsto (fun n : ℕ => 2000071/(4*(n:ℝ)*δ^2)) atTop (𝓝 0) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (2000071/(4*δ^2) : ℝ) using 1
    ext n
    rw [div_div]
    congr 1
    ring
  exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hbound hlimit

/-- Scalar canonical likelihood with one common dispersion s,
Σ_i[{y_iη_i-κ(η_i)}/s+r(y_i)], correction T8(ii), Appendix C, p. 264.
The data-dependent carrier term is represented by its fixed observed values. -/
def canonicalLikelihood {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (κ : ℝ → ℝ) (s : ℝ) (Y carrier : N → ℝ) (θ : Q → ℝ) : ℝ :=
  ∑ i, canonicalLogLikelihood κ s (Y i) (carrier i) (W.mulVec θ i)

/-- T8(ii)'s complete common-dispersion canonical score: its directional
gradient is s^-1 Σ_i (y_i-κ′(η_i))W_i v, and its zero equation is precisely
the residual equation because the shared positive dispersion is nonzero. -/
theorem canonical_common_score_calculus {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (κ : ℝ → ℝ) (s : ℝ) (hs : 0 < s)
    (Y carrier : N → ℝ) (θ : Q → ℝ)
    (hκ : ∀ i, DifferentiableAt ℝ κ (W.mulVec θ i)) :
    (∀ v : Q → ℝ, HasDerivAt
      (fun t => canonicalLikelihood W κ s Y carrier (fun j => θ j+t*v j))
      (s⁻¹*(∑ i, (Y i-deriv κ (W.mulVec θ i))*W.mulVec v i)) 0) ∧
    ((∀ j, s⁻¹*(∑ i, W i j*(Y i-deriv κ (W.mulVec θ i)))=0) ↔
      ∀ j, (∑ i, W i j*(Y i-deriv κ (W.mulVec θ i)))=0) := by
  constructor
  · intro v
    have hl : ∀ i, HasDerivAt
        (fun t => W.mulVec (fun j => θ j+t*v j) i) (W.mulVec v i) 0 := by
      intro i
      unfold Matrix.mulVec dotProduct
      convert HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
        (((hasDerivAt_const 0 (θ j)).add ((hasDerivAt_id 0).mul_const (v j))).const_mul (W i j))) using 1
      <;> simp
    have hi : ∀ i, HasDerivAt
        (fun t => canonicalLogLikelihood κ s (Y i) (carrier i)
          (W.mulVec (fun j => θ j+t*v j) i))
        (((Y i-deriv κ (W.mulVec θ i))/s)*W.mulVec v i) 0 := by
      intro i
      have hg : HasDerivAt (canonicalLogLikelihood κ s (Y i) (carrier i))
          ((Y i-deriv κ (W.mulVec θ i))/s)
          (W.mulVec (fun j => θ j+0*v j) i) := by
        simpa using canonical_score_derivative_calculus κ s (Y i) (carrier i) (W.mulVec θ i) _
          hs (hκ i).hasDerivAt
      exact hg.comp 0 (hl i)
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
    convert hsum using 1
    · rfl
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [div_eq_mul_inv]
      ring
  · constructor
    · intro h j
      exact (mul_eq_zero.mp (h j)).resolve_left (inv_ne_zero hs.ne')
    · intro h j
      rw [h j,mul_zero]

/-- The two named canonical examples in T8(ii): κ=log(1+exp η) has
mean κ′=logit^-1 η, and κ=exp η has mean κ′=exp η (Poisson log link). -/
theorem canonical_named_means :
    (∀ η : ℝ, deriv (fun a : ℝ => Real.log (1+Real.exp a)) η=logistic η) ∧
    (∀ η : ℝ, deriv Real.exp η=Real.exp η) := by
  constructor
  · intro η
    have hd := ((Real.hasDerivAt_exp η).const_add 1).log
      (by positivity : 1+Real.exp η ≠ 0)
    rw [logistic_exp]
    simpa only [add_comm] using hd.deriv
  · intro η
    exact (Real.hasDerivAt_exp η).deriv







/-- U is uniform on [0,1] in T7's explicit potential-outcome construction,
the counterexample to p. 257 and Appendix C: its law is restricted Lebesgue
measure on the unit interval, whose length is exactly one. -/
def rootUniformLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- The actual uniform law in T7 has total mass one. -/
theorem root_uniform_is_probability : IsProbabilityMeasure rootUniformLaw := by
  constructor
  simp [rootUniformLaw,Real.volume_Icc]

instance rootUniformLaw_probability : IsProbabilityMeasure rootUniformLaw :=
  root_uniform_is_probability

/-- T7's complete (X,D,U) law: the specified six (X,D) masses times an
independent uniform [0,1] U. This is a fixed genuine distribution, not a
postulated conditional-independence assumption. Coordinates are ((X,D),U). -/
def rootUnitLaw : Measure ((ℝ×ℝ)×ℝ) :=
  ∑ i : Fin 6, (rootLaw i).toNNReal •
    (Measure.dirac (rootX i,rootD i)).prod rootUniformLaw

/-- The six-atom/uniform product mixture in T7 has total mass one. -/
theorem root_unit_is_probability : IsProbabilityMeasure rootUnitLaw := by
  have hcast : ∀ i : Fin 6, ((rootLaw i).toNNReal : ℝ)=rootLaw i :=
    fun i => Real.coe_toNNReal _ (root_link_matrix_arithmetic.1.1 i)
  have hsum : (∑ i : Fin 6, (rootLaw i).toNNReal)=1 := by
    apply NNReal.eq
    simp only [NNReal.coe_sum,NNReal.coe_one]
    simp_rw [hcast]
    exact root_link_matrix_arithmetic.1.2
  have hco : (∑ i : Fin 6, ((rootLaw i).toNNReal : ENNReal))=1 := by
    simpa only [ENNReal.ofNNReal_finsetSum,ENNReal.coe_one] using
      congrArg (fun a : NNReal => (a : ENNReal)) hsum
  constructor
  simpa [rootUnitLaw,rootLaw,Fin.sum_univ_succ,Measure.add_apply,Measure.smul_apply] using hco

instance rootUnitLaw_probability : IsProbabilityMeasure rootUnitLaw := root_unit_is_probability

/-- The X coordinate of T7's ((X,D),U) unit draw; p. 257 counterexample. -/
def rootUnitX (s : (ℝ×ℝ)×ℝ) : ℝ := s.1.1
/-- The D coordinate of T7's ((X,D),U) unit draw; p. 257 counterexample. -/
def rootUnitD (s : (ℝ×ℝ)×ℝ) : ℝ := s.1.2
/-- The uniform auxiliary U coordinate in T7's potential outcomes. -/
def rootUnitU (s : (ℝ×ℝ)×ℝ) : ℝ := s.2
/-- Y(d)=1{U≤q₀(X)+ε[d-e(X)]}, the exact potential outcomes in T7.
Location: p. 257/Appendix C first-order counterexample. -/
def rootUnitY (a ε d : ℝ) (s : (ℝ×ℝ)×ℝ) : ℝ :=
  rootPotential a ε (rootUnitX s) (rootUnitU s) d
/-- τ=Y(1)-Y(0), the binary version of (1), p. 253, in T7's model. -/
def rootUnitTau (a ε : ℝ) (s : (ℝ×ℝ)×ℝ) : ℝ :=
  rootUnitY a ε 1 s-rootUnitY a ε 0 s




/-- T7's actual expected likelihood score under its six (X,D) profiles;
the Bernoulli conditional expectation replaces Y by rootProbability, Appendix C. -/
def rootScore (a ε : ℝ) (θ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j => fExpectation rootLaw (fun i => rootZ i j*
    scoreMultiplier rootMean (rootZ.mulVec θ i)*
      (rootProbability a ε i-rootMean (rootZ.mulVec θ i)))


namespace RootCompletion
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
attribute [local instance] Classical.propDecidable

lemma rootMean_hasDerivAt (η : ℝ) : HasDerivAt rootMean (2*η) η := by
  convert hasDerivAt_pow 2 η using 1 <;> first | rfl | norm_num

lemma rootMultiplier_eq (η : ℝ) : scoreMultiplier rootMean η=(2*η)/(η^2*(1-η^2)) := by
  rw [scoreMultiplier,(rootMean_hasDerivAt η).deriv,rootMean]

lemma rootMultiplier_admissible (η : ℝ) (hp : 0 < η) (hu : η < 1) :
    scoreMultiplier rootMean η=2/(η*(1-η^2)) := by
  rw [rootMultiplier_eq]
  have hsq : 1-η^2≠0 := by nlinarith
  field_simp [hp.ne',hsq]

lemma rootMultiplier_half : scoreMultiplier rootMean (1/2)=16/3 := by
  rw [rootMultiplier_eq]
  norm_num

lemma rootMultiplier_hasDerivAt_half : HasDerivAt (scoreMultiplier rootMean) (-32/9) (1/2) := by
  have hh:=((hasDerivAt_id (1/2:ℝ)).const_mul 2).div
    ((hasDerivAt_pow 2 (1/2:ℝ)).mul ((hasDerivAt_const (1/2:ℝ) (1:ℝ)).sub (hasDerivAt_pow 2 (1/2:ℝ))))
    (by norm_num : ((1/2:ℝ)^2*(1-(1/2)^2))≠0)
  convert hh using 1
  · exact funext rootMultiplier_eq
  · norm_num

lemma matrix_affine_hasDerivAt {N Q : Type*} [Fintype Q]
    (W : Matrix N Q ℝ) (θ v : Q→ℝ) (i : N) :
    HasDerivAt (fun t : ℝ=>W.mulVec (fun j=>θ j+t*v j) i) (W.mulVec v i) 0 := by
  unfold Matrix.mulVec dotProduct
  convert HasDerivAt.fun_sum (u:=Finset.univ) (fun j _=>
    (((hasDerivAt_const 0 (θ j)).add ((hasDerivAt_id 0).mul_const (v j))).const_mul (W i j))) using 1 <;>simp

lemma root_half_predictor (i : Fin 6) : rootZ.mulVec ![1/2,0,0] i=1/2 := by
  fin_cases i <;>norm_num [rootZ,rootX,rootD,rootE,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

lemma rootLikelihood_hasDerivAt (a ε : ℝ) (θ v : Fin 3→ℝ) (hθ : rootAdmissible θ) :
    HasDerivAt (fun t=>rootLikelihood a ε (fun j=>θ j+t*v j)) (dotProduct (rootScore a ε θ) v) 0 := by
  have hi (i : Fin 6) : HasDerivAt
      (fun t=>rootLaw i*binomialLogLikelihood rootMean 1 (rootProbability a ε i)
        (rootZ.mulVec (fun j=>θ j+t*v j) i))
      (rootLaw i*(scoreMultiplier rootMean (rootZ.mulVec θ i)*
        (rootProbability a ε i-rootMean (rootZ.mulVec θ i))*rootZ.mulVec v i)) 0 := by
    have hm : DifferentiableAt ℝ rootMean (rootZ.mulVec θ i):=(rootMean_hasDerivAt _).differentiableAt
    have hp : 0 < rootMean (rootZ.mulVec θ i) := by unfold rootMean;exact sq_pos_of_pos (hθ i).1
    have hu : rootMean (rootZ.mulVec θ i) < 1 := by unfold rootMean;have hh:=hθ i;nlinarith
    have hg:=bernoulli_score_derivative_calculus rootMean 1 (rootProbability a ε i)
      (rootZ.mulVec θ i) _ hm.hasDerivAt hp hu
    rw [←scoreMultiplier] at hg
    have hg' := (by simpa using hg : HasDerivAt (binomialLogLikelihood rootMean 1 (rootProbability a ε i))
      (scoreMultiplier rootMean (rootZ.mulVec θ i) * (rootProbability a ε i-rootMean (rootZ.mulVec θ i)))
      (rootZ.mulVec (fun j=>θ j+(0:ℝ)*v j) i)).comp 0 (matrix_affine_hasDerivAt rootZ θ v i)
    simpa using hg'.const_mul (rootLaw i)
  have hd:=HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=>hi i)
  convert hd using 1
  · rfl
  · unfold rootScore fExpectation dotProduct
    simp only [Matrix.mulVec, dotProduct,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma rootScore_directional (v : Fin 3→ℝ) : HasDerivAt
    (fun t=>rootScore (1/16) 0 (fun j=>(![1/2,0,0] : Fin 3→ℝ) j+t*v j))
    ((!![-16/3,0,0;0,-119/108,0;0,0,-100/27] : Matrix (Fin 3) (Fin 3) ℝ).mulVec v) 0 := by
  have hi (i : Fin 6) : HasDerivAt
      (fun t=>scoreMultiplier rootMean (rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3→ℝ) j+t*v j) i)*
        (rootProbability (1/16) 0 i-rootMean (rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3→ℝ) j+t*v j) i)))
      (((-32/9)*(rootProbability (1/16) 0 i-1/4)-16/3)*rootZ.mulVec v i) 0 := by
    have hη:=matrix_affine_hasDerivAt rootZ (![1/2,0,0] : Fin 3→ℝ) v i
    have hη0 : rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3→ℝ) j+(0:ℝ)*v j) i=1/2 := by simpa using root_half_predictor i
    have hH : HasDerivAt (fun t=>scoreMultiplier rootMean
        (rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3→ℝ) j+t*v j) i))
        ((-32/9)*rootZ.mulVec v i) 0 := by
      have hh : HasDerivAt (scoreMultiplier rootMean) (-32/9)
          (rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3→ℝ) j+(0:ℝ)*v j) i) := by
        rw [hη0]; exact rootMultiplier_hasDerivAt_half
      exact hh.comp 0 hη
    have hM : HasDerivAt (fun t=>rootMean
        (rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3→ℝ) j+t*v j) i))
        (rootZ.mulVec v i) 0 := by
      have hh0 : HasDerivAt rootMean 1
          (rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3→ℝ) j+(0:ℝ)*v j) i) := by
        rw [hη0]; simpa using rootMean_hasDerivAt (1/2)
      have hh:=hh0.comp 0 hη
      convert hh using 1 <;> first | rfl | simp
    have hh:=hH.mul ((hasDerivAt_const 0 (rootProbability (1/16) 0 i)).sub hM)
    convert hh using 1
    dsimp only [Pi.sub_apply]
    rw [hη0,rootMultiplier_half,rootMean]
    ring
  have hd (j : Fin 3) := HasDerivAt.fun_sum (u:=Finset.univ)
    (fun i _=>(hi i).const_mul (rootLaw i*rootZ i j))
  have hv:=hasDerivAt_pi.mpr hd
  convert hv using 1
  · funext t j
    unfold rootScore fExpectation
    apply Finset.sum_congr rfl
    intro i _
    ring
  · ext j
    fin_cases j <;>norm_num [rootProbability,rootBaseline,rootLaw,rootZ,rootX,rootD,rootE,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;>ring

lemma rootScore_epsilon : HasDerivAt (fun ε=>rootScore (1/16) ε ![1/2,0,0]) ![0,10/9,0] 0 := by
  have hd (j : Fin 3) : HasDerivAt (fun ε=>rootScore (1/16) ε (![1/2,0,0] : Fin 3→ℝ) j)
      (∑ i,rootLaw i*rootZ i j*(16/3)*(rootD i-rootE (rootX i))) 0 := by
    unfold rootScore fExpectation
    have hi (i : Fin 6) : HasDerivAt
        (fun ε=>rootLaw i*(rootZ i j*scoreMultiplier rootMean (rootZ.mulVec ![1/2,0,0] i)*
          (rootProbability (1/16) ε i-rootMean (rootZ.mulVec ![1/2,0,0] i))))
        (rootLaw i*rootZ i j*(16/3)*(rootD i-rootE (rootX i))) 0 := by
      rw [root_half_predictor,rootMultiplier_half]
      unfold rootProbability
      convert (((((hasDerivAt_id 0).mul_const (rootD i-rootE (rootX i))).const_add
        (rootBaseline (1/16) (rootX i))).sub_const (rootMean (1/2))).const_mul (rootLaw i*(rootZ i j*(16/3)))) using 1
      · funext ε; dsimp; ring
      · ring
    exact HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=>hi i)
  convert hasDerivAt_pi.mpr hd using 1
  ext j
  fin_cases j <;>norm_num [rootLaw,rootZ,rootD,rootX,rootE,Fin.sum_univ_succ]

theorem root_score_calculus_completed :
    (∀ η : ℝ, 0<η → η<1 → scoreMultiplier rootMean η=2/(η*(1-η^2))) ∧
    deriv rootMean (1/2)=1 ∧ scoreMultiplier rootMean (1/2)=16/3 ∧
    deriv (scoreMultiplier rootMean) (1/2)= -32/9 ∧
    rootScore (1/16) 0 ![1/2,0,0]=0 ∧
    (∀ v : Fin 3 → ℝ, HasDerivAt
      (fun t => rootScore (1/16) 0 (fun j => (![1/2,0,0] : Fin 3 → ℝ) j+t*v j))
      ((!![-16/3,0,0;0,-119/108,0;0,0,-100/27] : Matrix (Fin 3) (Fin 3) ℝ).mulVec v) 0) ∧
    HasDerivAt (fun ε => rootScore (1/16) ε ![1/2,0,0]) ![0,10/9,0] 0 ∧
    (∀ a ε θ v, (a=0 ∨ a=1/16) → |ε| ≤ 1/16 → rootAdmissible θ → HasDerivAt
      (fun t => rootLikelihood a ε (fun j => θ j+t*v j)) (dotProduct (rootScore a ε θ) v) 0) := by
  refine ⟨rootMultiplier_admissible,?_,rootMultiplier_half,rootMultiplier_hasDerivAt_half.deriv,?_,
    rootScore_directional,rootScore_epsilon,?_⟩
  · simpa using (rootMean_hasDerivAt (1/2)).deriv
  · ext j
    fin_cases j <;>norm_num [rootScore,fExpectation,root_half_predictor,rootMultiplier_half,
      rootProbability,rootBaseline,rootMean,rootLaw,rootZ,rootX,rootD,rootE,Fin.sum_univ_succ]
  · intro a ε θ v _ _ hθ
    exact rootLikelihood_hasDerivAt a ε θ v hθ

end
end RootCompletion

/-- T7(b),(c): the score multiplier, its derivative and the true score
derivatives coincide with the separately computed finite matrices, connecting
the arithmetic to the actual maximum-likelihood object. -/
theorem root_score_calculus :
    (∀ η : ℝ, 0<η → η<1 → scoreMultiplier rootMean η=2/(η*(1-η^2))) ∧
    deriv rootMean (1/2)=1 ∧ scoreMultiplier rootMean (1/2)=16/3 ∧
    deriv (scoreMultiplier rootMean) (1/2)= -32/9 ∧
    rootScore (1/16) 0 ![1/2,0,0]=0 ∧
    (∀ v : Fin 3 → ℝ, HasDerivAt
      (fun t => rootScore (1/16) 0 (fun j => (![1/2,0,0] : Fin 3 → ℝ) j+t*v j))
      ((!![-16/3,0,0;0,-119/108,0;0,0,-100/27] : Matrix (Fin 3) (Fin 3) ℝ).mulVec v) 0) ∧
    HasDerivAt (fun ε => rootScore (1/16) ε ![1/2,0,0]) ![0,10/9,0] 0 ∧
    (∀ a ε θ v, (a=0 ∨ a=1/16) → |ε| ≤ 1/16 → rootAdmissible θ → HasDerivAt
      (fun t => rootLikelihood a ε (fun j => θ j+t*v j)) (dotProduct (rootScore a ε θ) v) 0) := by
  exact RootCompletion.root_score_calculus_completed

/-- T11(c)'s precise radius: the complexified inverse-logit Taylor series
at zero has radius π, owing to its nearest complex singularities ±iπ. -/
theorem logistic_power_series_radius :
    ∃ s : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun z : ℂ => (1+Complex.exp (-z))⁻¹) s 0 ∧
      s.radius=ENNReal.ofReal Real.pi := by
  exact TaylorCompletion.logistic_power_series_radius_completed

/-- T11(a),(b),(e)'s finite data properties: the two rows repeated 100
times give a nonsingular full design, both outcomes occur in each binomial
cell, and the exact treatment likelihood score at the fitted values is zero. -/
theorem extreme_grouped_data_arithmetic :
    let W : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;1,1]
    let L := Real.log 99
    ((100 : ℝ) • (W.transpose*W)).det=10000 ∧
    (0:ℝ)<1 ∧ (1:ℝ)<100 ∧ (0:ℝ)<99 ∧ (99:ℝ)<100 ∧
    groupedResidual W (fun _ => 100) ![1,99] logistic ![-L,2*L]=0 := by
  dsimp only
  have hp := extreme_sigmoid_arithmetic.1
  have hn := extreme_sigmoid_arithmetic.2.1
  have hη : ( !![1,0;1,1] : Matrix (Fin 2) (Fin 2) ℝ).mulVec
      ![-Real.log 99,2*Real.log 99] = ![-Real.log 99,Real.log 99] := by
    ext i
    fin_cases i <;>
      norm_num [Matrix.mulVec,Matrix.vecMul,vecHead,vecTail,dotProduct,Fin.sum_univ_succ]
    <;> ring
  refine ⟨?_,by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
  · norm_num [Matrix.det_fin_two,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ]
  · unfold groupedResidual
    rw [hη]
    ext j
    fin_cases j <;>
      norm_num [Fin.sum_univ_succ,hp,hn]

/-- T9's estimator calculated from the raw group covariance
matrices V_g=Z_g I Z_g′+I, with S=I and σ_g²=1. The raw GLS treatment
coefficient is -10/61 even though both actual within-group OLS slopes are zero;
therefore no scalar weighting of those slopes can equal the GLS slope. -/
theorem group_raw_gls_counterexample :
    let V₁ : Matrix (Fin 3) (Fin 3) ℝ :=
      groupZ₁*(1 : Matrix (Fin 2) (Fin 2) ℝ)*groupZ₁.transpose+1
    let V₂ : Matrix (Fin 3) (Fin 3) ℝ :=
      groupZ₂*(1 : Matrix (Fin 2) (Fin 2) ℝ)*groupZ₂.transpose+1
    let raw := (groupZ₁.transpose*V₁⁻¹*groupZ₁+groupZ₂.transpose*V₂⁻¹*groupZ₂)⁻¹.mulVec
      ((groupZ₁.transpose*V₁⁻¹).mulVec 0+(groupZ₂.transpose*V₂⁻¹).mulVec (fun _ => 2))
    (1 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef ∧
    raw=![68/61,-10/61] ∧ ols groupZ₁ 0 1=0 ∧ ols groupZ₂ (fun _ => 2) 1=0 ∧
    (∀ a₁ a₂ : ℝ, raw 1≠a₁*ols groupZ₁ 0 1+a₂*ols groupZ₂ (fun _ => 2) 1) := by
  dsimp only
  let V₁ : Matrix (Fin 3) (Fin 3) ℝ :=
    groupZ₁*(1 : Matrix (Fin 2) (Fin 2) ℝ)*groupZ₁.transpose+1
  let V₂ : Matrix (Fin 3) (Fin 3) ℝ :=
    groupZ₂*(1 : Matrix (Fin 2) (Fin 2) ℝ)*groupZ₂.transpose+1
  have hi₁ : V₁⁻¹=(!![5/8,-1/8,-1/8;-1/8,5/8,-3/8;-1/8,-3/8,5/8] :
      Matrix (Fin 3) (Fin 3) ℝ) := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [V₁,groupZ₁,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,
        Matrix.vecMul,vecHead,vecTail,dotProduct,
        Fin.sum_univ_succ]
  have hi₂ : V₂⁻¹=(!![5/7,-2/7,-1/7;-2/7,5/7,-1/7;-1/7,-1/7,3/7] :
      Matrix (Fin 3) (Fin 3) ℝ) := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [V₂,groupZ₂,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,
        Matrix.vecMul,vecHead,vecTail,dotProduct,
        Fin.sum_univ_succ]
  have hH : (groupZ₁.transpose*V₁⁻¹*groupZ₁+groupZ₂.transpose*V₂⁻¹*groupZ₂)⁻¹=groupHinv := by
    rw [hi₁,hi₂]
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [groupZ₁,groupZ₂,groupHinv,Matrix.mul_apply,Matrix.transpose_apply,
        Matrix.one_apply,Fin.sum_univ_succ]
  have hraw : (groupZ₁.transpose*V₁⁻¹*groupZ₁+groupZ₂.transpose*V₂⁻¹*groupZ₂)⁻¹.mulVec
      ((groupZ₁.transpose*V₁⁻¹).mulVec 0+(groupZ₂.transpose*V₂⁻¹).mulVec (fun _ => 2))=
        ![68/61,-10/61] := by
    rw [hH,hi₁,hi₂]
    norm_num [groupZ₁,groupZ₂,groupHinv,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.mulVec,Matrix.vecMul,vecHead,vecTail,dotProduct,
      Fin.sum_univ_succ,funext_iff,Fin.forall_fin_succ]
  have h₁ : ols groupZ₁ 0 1=0 := by simp [ols]
  have h₂ : ols groupZ₂ (fun _ => 2) 1=0 := by
    have hc : (fun _ : Fin 3 => (2:ℝ))=![2,2,2] := by
      funext i
      fin_cases i <;> rfl
    rw [hc]
    simpa using congrFun group_pooling_counterexample.2.2.2.1 1
  refine ⟨Matrix.PosSemidef.one,hraw,h₁,h₂,?_⟩
  intro a₁ a₂
  rw [hraw,h₁,h₂]
  norm_num

end

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Topology
open Finset Matrix MeasureTheory ProbabilityTheory Filter

/-! Finite probability models and complete counterexamples. -/

/-- Conditional independence (2)/(11), pp. 253/260, for a genuine finite
probability law when potential outcomes are deterministic functions of X. -/
theorem finite_unconfounded {A B C : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (g : B → C) (D : A → ℝ) (hlaw : IsLaw p) :
    fCondIndep p X (fun a => g (X a)) D := by
  exact finite_unconfounded_algebra p X g D

/-- T1(d), p. 261: Chebyshev's bound on a normalized finite probability law. -/
theorem finite_chebyshev {A : Type*} [Fintype A] (p Z : A → ℝ)
    (hlaw : IsLaw p) (δ : ℝ) (hδ : 0 < δ) :
    fMass p (fun a => δ ≤ |Z a-fExpectation p Z|) ≤ fVariance p Z/δ^2 := by
  exact finite_chebyshev_algebra p Z hlaw.1 δ hδ

/-- T1(d): product moments under the actual independent sampling design,
with nonnegative normalized probabilities as in the p. 252 super-population reading. -/
theorem iid_tensor_expectation {A : Type*} [Fintype A] (p : A → ℝ)
    (hlaw : IsLaw p) (n : ℕ) (G : Fin n → A → ℝ) :
    fExpectation (iidLaw p n) (fun a => ∏ i, G i (a i)) =
      ∏ i, fExpectation p (G i) := by
  exact iid_tensor_expectation_algebra p n G

/-- T1(c), p. 261: for every 0<epsilon<1/2 this actual causal model is a
probability law, has positivity and a linear propensity, and its effective X=0
mass is epsilon(1-epsilon)/(epsilon(1-epsilon)+1/4), strictly between 0 and 4epsilon. -/
theorem rare_profile_bound (ε : ℝ) (hε : 0 < ε) (hu : ε < 1/2) :
    IsLaw (rareLaw ε) ∧
    (∀ a d, rareY a d = rareY a 0+(1+binaryX a)*d) ∧
    fCondIndep (rareLaw ε) binaryX (fun a => (rareY a 0,1+binaryX a)) binaryD ∧
    (∀ x ∈ ({0,1} : Finset ℝ),
      fCondMean (rareLaw ε) binaryX binaryD x = ε+(1/2-ε)*x ∧
      0 < fCondProb (rareLaw ε) binaryX binaryD x 0 ∧
      0 < fCondProb (rareLaw ε) binaryX binaryD x 1) ∧
    fMass (fEffective (rareLaw ε) binaryX binaryD) (fun a => binaryX a=0) =
      ε*(1-ε)/(ε*(1-ε)+1/4) ∧
    0 < fMass (fEffective (rareLaw ε) binaryX binaryD) (fun a => binaryX a=0) ∧
    fMass (fEffective (rareLaw ε) binaryX binaryD) (fun a => binaryX a=0) < 4*ε := by
  have he : ε < 1 := by linarith
  have hlaw : IsLaw (rareLaw ε) := by
    constructor
    · intro a; fin_cases a <;> simp [rareLaw] <;> positivity
    · simp [rareLaw,Fin.sum_univ_succ]; ring
  have hc : fCondIndep (rareLaw ε) binaryX
      (fun a => (rareY a 0,1+binaryX a)) binaryD := by
    simpa [rareY] using finite_unconfounded (rareLaw ε) binaryX (fun x => (2*x,1+x)) binaryD hlaw
  have hm (x : ℝ) : fCondMean (rareLaw ε) binaryX binaryD x =
      if x=0 then ε else if x=1 then 1/2 else 0 := by
    by_cases hx : x=0
    · subst x; norm_num [fCondMean,fMass,fExpectation,rareLaw,binaryX,binaryD,Fin.sum_univ_succ]
      ring
    · by_cases hx1 : x=1
      · subst x; norm_num [fCondMean,fMass,fExpectation,rareLaw,binaryX,binaryD,Fin.sum_univ_succ]
      · simp [fCondMean,fMass,fExpectation,rareLaw,binaryX,binaryD,Fin.sum_univ_succ,hx,hx1,eq_comm]
  have hw : fWeight (rareLaw ε) binaryX binaryD = ![ε^2,(1-ε)^2,1/4,1/4] := by
    ext a
    simp only [fWeight,hm]
    fin_cases a <;> norm_num [binaryX,binaryD] <;> ring
  have hv : 0<ε*(1-ε) := mul_pos hε (by linarith)
  have hE : fExpectation (rareLaw ε) (fWeight (rareLaw ε) binaryX binaryD) =
      (ε*(1-ε)+1/4)/2 := by
    rw [hw]
    norm_num [fExpectation,rareLaw,Fin.sum_univ_succ]
    ring
  have hq : fMass (fEffective (rareLaw ε) binaryX binaryD) (fun a => binaryX a=0) =
      ε*(1-ε)/(ε*(1-ε)+1/4) := by
    simp only [fMass,fEffective]
    simp only [hE]
    simp only [hw]
    norm_num [rareLaw,binaryX,Fin.sum_univ_succ]
    have hd : ε*(1-ε)+1/4≠0 := ne_of_gt (by linarith)
    field_simp [hd]
    <;> ring
  refine ⟨hlaw,?_,hc,?_,hq,?_,?_⟩
  · intro a d; simp [rareY]
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp only [hm]
      norm_num [fCondProb,fMass,rareLaw,binaryX,binaryD,Fin.sum_univ_succ]
      have hhalf : (1-ε)/2+ε/2=(1/2:ℝ) := by ring
      rw [hhalf]
      constructor <;> positivity
    · simp only [hm]
      norm_num [fCondProb,fMass,rareLaw,binaryX,binaryD,Fin.sum_univ_succ]
  · rw [hq]; exact (rare_profile_ratio_bound ε hε hu).1
  · rw [hq]; exact (rare_profile_ratio_bound ε hε hu).2

/-- T2's independent sampling from the four equiprobable atoms. This is the
iid super-population reading on p. 252, applied to the two p. 261 outcome worlds. -/
def MultiSampling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (draw : ℕ → Ω → Fin 4) : Prop :=
  (∀ i, Measurable (draw i)) ∧ iIndepFun draw P ∧
    ∀ i a, P {s | draw i s=a}=ENNReal.ofReal (multiLaw a)

/-- T2(e), p. 261: under the specified iid observed law, an estimator cannot
be consistent for both nominal effects 1 and 2, or both effective effects 1 and 13/5. -/
theorem no_common_consistent_estimator {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (draw : ℕ → Ω → Fin 4)
    (hdraw : MultiSampling P draw) (T : ∀ n : ℕ, (Fin n → ℝ × ℝ × ℝ) → ℝ) :
    ¬ (TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldA (draw i s))) atTop (fun _ => (1:ℝ)) ∧
      TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldB (draw i s))) atTop (fun _ => (2:ℝ))) ∧
    ¬ (TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldA (draw i s))) atTop (fun _ => (1:ℝ)) ∧
      TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldB (draw i s))) atTop (fun _ => (13/5:ℝ))) := by
  exact ⟨observational_equality_no_two_limits P draw T 1 2 (by norm_num),
    observational_equality_no_two_limits P draw T 1 (13/5) (by norm_num)⟩

/-- T3: the sample tuple (0,0,2,3) really induces the stated (1,X) and D
matrices from the independent Bernoulli population, p. 261. -/
theorem zero_sample_link :
    ∀ i : Fin 4, zeroSampleV i 1=binaryX ((![0,0,2,3] : Fin 4 → Fin 4) i) ∧
      zeroSampleD i=binaryD ((![0,0,2,3] : Fin 4 → Fin 4) i) := by
  intro i
  fin_cases i <;> norm_num [zeroSampleV,zeroSampleD,binaryX,binaryD]

/-- T5: grouping the 72 binary observations preserves integer interior
counts, (1,D,X) regressors, fitted means and the genuine likelihood derivative,
Appendix C, pp. 264–265. -/
theorem odds_model_details :
    (∀ i : Fin 2 × Fin 3, oddsW i 0=1 ∧ (oddsW i 1=0 ∨ oddsW i 1=1) ∧
      oddsSuccess i = (if i.2=0 then (7:ℝ) else if i.2=1 then 6 else 10)) ∧
    (∀ i : Fin 2 × Fin 3, oddsMean (oddsW.mulVec ![1,0,1] i)=
      (![1/2,2/3,3/4] : Fin 3 → ℝ) i.2) ∧
    ((12:ℝ) • (oddsW.transpose*oddsW)).det=62208 ∧
    (∀ v : Fin 3 → ℝ, HasDerivAt
      (fun t => groupedLikelihood oddsW (fun _ => 12) oddsSuccess oddsMean
        (fun j => (![1,0,1] : Fin 3 → ℝ) j+t*v j))
      (dotProduct (![2/3,1/3,-2/3] : Fin 3 → ℝ) v) 0) := by
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨d,x⟩; fin_cases d <;> fin_cases x <;> norm_num [oddsW,oddsSuccess]
  · rintro ⟨d,x⟩; fin_cases d <;> fin_cases x <;>
      norm_num [oddsW,oddsMean,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · norm_num [Matrix.det_smul,odds_gram_determinant]
  · intro v
    have hm : ∀ i, DifferentiableAt ℝ oddsMean (oddsW.mulVec ![1,0,1] i) := by
      intro i
      unfold oddsMean
      exact differentiableAt_id.div ((differentiableAt_const (1:ℝ)).add differentiableAt_id)
        (by linarith [odds_score_counterexample.1 i])
    have hp : ∀ i, 0 < oddsMean (oddsW.mulVec ![1,0,1] i) := by
      intro i; unfold oddsMean; exact div_pos (odds_score_counterexample.1 i) (by linarith [odds_score_counterexample.1 i])
    have hu : ∀ i, oddsMean (oddsW.mulVec ![1,0,1] i)<1 := by
      intro i; unfold oddsMean
      exact (div_lt_one (by linarith [odds_score_counterexample.1 i])).2 (by linarith)
    have hd := likelihood_directional_derivative_calculus oddsW (fun _ => 12) oddsSuccess oddsMean ![1,0,1] v hm hp hu
    have hs := odds_score_counterexample.2.2.2.1
    have hsum : (∑ i, scoreMultiplier oddsMean (oddsW.mulVec ![1,0,1] i)*
        (oddsSuccess i-12*oddsMean (oddsW.mulVec ![1,0,1] i))*oddsW.mulVec v i) =
        dotProduct (![2/3,1/3,-2/3] : Fin 3 → ℝ) v := by
      rw [← hs]
      simp only [dotProduct,groupedScore,Matrix.mulVec]
      simp_rw [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rwa [hsum] at hd

/-- T6: the stated six probit cells are full rank after replication eight
times, have both binary outcomes, and use the paper's (1,D,X) design. -/
theorem probit_design_details :
    (∀ i : Fin 2 × Fin 3, probitW i 0=1 ∧ (probitW i 1=0 ∨ probitW i 1=1) ∧
      0<probitSuccess i ∧ probitSuccess i<8) ∧
    ((8:ℝ) • (probitW.transpose*probitW)).det=18432 := by
  constructor
  · rintro ⟨d,x⟩; fin_cases d <;> fin_cases x <;> norm_num [probitW,probitSuccess]
  · norm_num [Matrix.det_fin_three,Matrix.mul_apply,Matrix.transpose_apply,probitW,
      Fintype.sum_prod_type,Fin.sum_univ_succ]

/-- T8(i): the Bernoulli likelihood contribution at an actual binary outcome
has derivative h(eta)(Y-m(eta)), Appendix C, p. 265, corrected. -/
theorem bernoulli_score_derivative (m : ℝ → ℝ) (y η m' : ℝ)
    (hy : y=0 ∨ y=1) (hm : HasDerivAt m m' η) (hp : 0<m η) (hu : m η<1) :
    HasDerivAt (binomialLogLikelihood m 1 y) (m'/(m η*(1-m η))*(y-m η)) η := by
  simpa using bernoulli_score_derivative_calculus m 1 y η m' hm hp hu

/-- A valid scalar canonical exponential family in the T8(ii) repair:
log density is {y eta-kappa(eta)}/s+carrier(y), with one positive dispersion,
normalization for every admissible eta and observations in its response support. -/
def CanonicalFamily (ν : Measure ℝ) (κ : ℝ → ℝ) (s : ℝ) (carrier : ℝ → ℝ)
    (I support : Set ℝ) : Prop :=
  0<s ∧ IsOpen I ∧ MeasurableSet support ∧ ν supportᶜ=0 ∧
    ∀ η ∈ I, Integrable (fun y => Real.exp (canonicalLogLikelihood κ s y (carrier y) η)) ν ∧
      (∫ y, Real.exp (canonicalLogLikelihood κ s y (carrier y) η) ∂ν)=1

/-- T8(ii): differentiation of the log density in a valid common-dispersion
scalar canonical model gives (Y-kappa'(eta))/s, Appendix C's corrected extension. -/
theorem canonical_score_derivative (ν : Measure ℝ) (κ : ℝ → ℝ) (s : ℝ)
    (carrier : ℝ → ℝ) (I support : Set ℝ)
    (hfamily : CanonicalFamily ν κ s carrier I support)
    (y η κ' : ℝ) (hy : y∈support) (hη : η∈I) (hk : HasDerivAt κ κ' η) :
    HasDerivAt (canonicalLogLikelihood κ s y (carrier y)) ((y-κ')/s) η := by
  exact canonical_score_derivative_calculus κ s y (carrier y) η κ' hfamily.1 hk

/-- T8(i), Appendix C: the likelihood directional score for a binary dataset
grouped into integer success counts, with the paper's unit intercept. -/
theorem likelihood_directional_derivative {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (j₀ : Q) (hW : ∀ i, W i j₀=1) (n k : N → ℝ)
    (hcounts : ∀ i, ∃ a b : ℕ, n i=(a:ℝ) ∧ k i=(b:ℝ) ∧ b≤a)
    (m : ℝ → ℝ) (θ v : Q → ℝ)
    (hm : ∀ i, DifferentiableAt ℝ m (W.mulVec θ i))
    (hp : ∀ i, 0<m (W.mulVec θ i)) (hu : ∀ i, m (W.mulVec θ i)<1) :
    HasDerivAt (fun t => groupedLikelihood W n k m (fun j => θ j+t*v j))
      (∑ i, scoreMultiplier m (W.mulVec θ i)*(k i-n i*m (W.mulVec θ i))*W.mulVec v i) 0 := by
  exact likelihood_directional_derivative_calculus W n k m θ v hm hp hu

/-- T8(ii): the score and residual equations coincide for a valid scalar
canonical family with common nonzero dispersion and admissible responses. -/
theorem canonical_common_score {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (j₀ : Q) (hW : ∀ i, W i j₀=1)
    (ν : Measure ℝ) (κ : ℝ → ℝ) (s : ℝ) (carrier : ℝ → ℝ) (I support : Set ℝ)
    (hfamily : CanonicalFamily ν κ s carrier I support)
    (Y : N → ℝ) (hY : ∀ i, Y i∈support) (θ : Q → ℝ)
    (hθ : ∀ i, W.mulVec θ i∈I) (hκ : ∀ i, DifferentiableAt ℝ κ (W.mulVec θ i)) :
    (∀ v : Q → ℝ, HasDerivAt
      (fun t => canonicalLikelihood W κ s (fun i => Y i) (fun i => carrier (Y i)) (fun j => θ j+t*v j))
      (s⁻¹*(∑ i, (Y i-deriv κ (W.mulVec θ i))*W.mulVec v i)) 0) ∧
    ((∀ j, s⁻¹*(∑ i, W i j*(Y i-deriv κ (W.mulVec θ i)))=0) ↔
      ∀ j, (∑ i, W i j*(Y i-deriv κ (W.mulVec θ i)))=0) := by
  exact canonical_common_score_calculus W κ s hfamily.1 Y (fun i => carrier (Y i)) θ hκ

/-- T10(iii), p. 257 correction: the exact scalar treatment-row criterion
for A_g=(sum_h P_h)^(-1)P_g built from the full-rank GLS group designs. -/
theorem scalar_pooling_iff (G q : ℕ) (hG : 1≤G) (hq : 1≤q)
    (n : Fin G → ℕ) (Z : ∀ g, Matrix (Fin (n g)) (Fin q) ℝ)
    (S : Matrix (Fin q) (Fin q) ℝ) (σ₂ : Fin G → ℝ) (hS : S.PosSemidef)
    (hσ : ∀ g, 0<σ₂ g) (hQ : ∀ g, ((Z g).transpose*Z g).det≠0)
    (a : Fin G → ℝ) (b : Fin q) :
    let P := fun g => groupPrecision S ((Z g).transpose*Z g) (σ₂ g)
    let A := fun g => (∑ h, P h)⁻¹*P g
    (∀ t : Fin G → Fin q → ℝ, (∑ g, ∑ j, A g b j*t g j)=∑ g, a g*t g b) ↔
      ∀ g j, A g b j=if j=b then a g else 0 := by
  exact scalar_pooling_iff_algebra _ a b

/-- T16(iii), p. 259 correction: the four spending observations give an
actual zero OLS log-growth coefficient and exponentiated factor 1, although
their arithmetic mean spending rises from 1 to 3/2, or 50 percent. -/
theorem spending_mean_counterexample :
    let W : Matrix (Fin 4) (Fin 2) ℝ := !![1,0;1,0;1,1;1,1]
    let S : Fin 4 → ℝ := ![1,1,0,3]
    let Y := fun i => Real.log ((1+S i)/2)
    ols W Y 1=0 ∧ Real.exp (ols W Y 1)=1 ∧
    (Real.log (1/2)+Real.log 2)/2=0 ∧
    (S 0+S 1)/2=1 ∧ (S 2+S 3)/2=3/2 ∧ ((3/2:ℝ)/1-1)*100=50 := by
  have ho := spending_ols_counterexample
  have ha := spending_mean_arithmetic
  exact ⟨ho.1,ho.2.1,ha.1,ho.2.2.1,ho.2.2.2,ha.2.2.2.2⟩

/-- T15/T22, Expression (13), p. 263: the exact decomposition of the actual
OLS treatment coefficient using its fitted control residual, under full rank. -/
theorem regression_decomposition (n K : ℕ) (D Y₀ τ : Fin n → ℝ) (X : Fin n → Fin K → ℝ)
    (hQ : Matrix.det ((fun j k : Fin (K+2) =>
      ∑ i : Fin n, regressorRow (D i) (X i) j*regressorRow (D i) (X i) k) :
      Matrix (Fin (K+2)) (Fin (K+2)) ℝ)≠0) :
    let V : Matrix (Fin n) (Fin (K+1)) ℝ := fun i => controlRow (X i)
    let W : Matrix (Fin n) (Fin (K+2)) ℝ := fun i => regressorRow (D i) (X i)
    let m := V.mulVec (ols V D)
    let r := sampleResidual V D (ols V D)
    ols W (fun i => Y₀ i+τ i*D i) 1=
      (∑ i, r i*Y₀ i)/(∑ i, r i^2)+
      (∑ i, r i*m i*τ i)/(∑ i, r i^2)+
      (∑ i, r i^2*τ i)/(∑ i, r i^2) := by
  dsimp only
  have hf := partial_regression n K D (fun i => Y₀ i+τ i*D i) X hQ
  dsimp only at hf
  rw [hf.2.2]
  simpa only [sampleResidual, sub_add_cancel] using
    regression_decomposition_algebra
      (sampleResidual (fun i => controlRow (X i)) D (ols (fun i => controlRow (X i)) D))
      (Matrix.mulVec (fun i => controlRow (X i)) (ols (fun i => controlRow (X i)) D)) Y₀ τ

/-- T8(iv), corrected Appendix C: the exact first Taylor polynomial of the
full Bernoulli score includes the multiplier derivative. Its vector sum is
h0*r+(-h0*f0*A+h1*B)*delta. Twice differentiability of the mean alone does
not justify a quadratic remainder. -/
theorem full_score_firstTaylor (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K+2)) ℝ) (Y : Fin N → ℝ)
    (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (I : Set ℝ) (hI : IsOpen I) (m : ℝ → ℝ)
    (hm : DifferentiableOn ℝ m I) (hprob : ∀ η∈I, 0<m η ∧ m η<1)
    (η₀ p₀ : ℝ) (hη : η₀∈I) (hp : 0<p₀) (hu : p₀<1) (hmean : m η₀=p₀)
    (hm₂ : DifferentiableAt ℝ (deriv m) η₀) :
    let θ₀ : Fin (K+2) → ℝ := fun j => if j=0 then η₀ else 0
    let h := scoreMultiplier m
    let h₀ := h η₀
    let f₀ := deriv m η₀
    let h₁ := deriv h η₀
    let r := W.transpose.mulVec (fun i => Y i-p₀)
    let A := W.transpose*W
    let B : Matrix (Fin (K+2)) (Fin (K+2)) ℝ := fun j k => ∑ i, (Y i-p₀)*W i j*W i k
    ∀ δ : Fin (K+2) → ℝ,
      (fun j => ∑ i, W i j*firstTaylor (fun η => h η*(Y i-m η)) η₀ (W.mulVec (θ₀+δ) i)) =
        h₀ • r+((-h₀*f₀) • A+h₁ • B).mulVec δ := by
  dsimp only
  have hmd : DifferentiableAt ℝ m η₀ := hm.differentiableAt (hI.mem_nhds hη)
  have hden : m η₀*(1-m η₀)≠0 := by rw [hmean]; positivity
  have hhd : DifferentiableAt ℝ (scoreMultiplier m) η₀ := by
    unfold scoreMultiplier
    exact hm₂.div (hmd.mul ((differentiableAt_const (1:ℝ)).sub hmd)) hden
  intro δ
  have ht := fun i => scalar_full_score_firstTaylor m (scoreMultiplier m) η₀ p₀
    (deriv m η₀) (scoreMultiplier m η₀) (deriv (scoreMultiplier m) η₀) (Y i)
    hmd.hasDerivAt hhd.hasDerivAt hmean rfl
  have hpred : ∀ i, W.mulVec ((fun j => if j=0 then η₀ else 0)+δ) i=η₀+W.mulVec δ i := by
    intro i
    rw [Matrix.mulVec_add]
    simp [Matrix.mulVec,dotProduct,mul_ite,Finset.sum_ite_eq,hW]
  simp only [ht]
  simp only [hpred,add_sub_cancel_left]
  ext j
  let B : Matrix (Fin (K+2)) (Fin (K+2)) ℝ :=
    fun j k => ∑ i, (Y i-p₀)*W i j*W i k
  have hA : (W.transpose*W).mulVec δ j=∑ i, W i j*W.mulVec δ i := by
    rw [← Matrix.mulVec_mulVec]
    rfl
  have hB : B.mulVec δ j=∑ i, (Y i-p₀)*W i j*W.mulVec δ i := by
    change (∑ k, (∑ i, (Y i-p₀)*W i j*W i k)*δ k) =
      ∑ i, (Y i-p₀)*W i j*(∑ k, W i k*δ k)
    simp_rw [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  change (∑ i, W i j*(scoreMultiplier m η₀*(Y i-p₀)+
      (deriv (scoreMultiplier m) η₀*(Y i-p₀)-scoreMultiplier m η₀*deriv m η₀)*W.mulVec δ i)) =
    scoreMultiplier m η₀*(∑ i, W i j*(Y i-p₀))+
      (((-scoreMultiplier m η₀*deriv m η₀) • (W.transpose*W)+
        deriv (scoreMultiplier m) η₀ • B).mulVec δ) j
  rw [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.smul_mulVec]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hA,hB]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring


/-- Binary-cell likelihood inequality used in T11(a), p. 257. For positive
count n and an interior empirical success fraction p, its log likelihood is
maximal uniquely at fitted probability p. This finite inequality uses log t≤t-1. -/
theorem binomial_probability_unique_max (n p q : ℝ) (hn : 0<n)
    (hp : 0<p) (hpu : p<1) (hq : 0<q) (hqu : q<1) :
    n*p*Real.log q+(n-n*p)*Real.log (1-q) ≤
      n*p*Real.log p+(n-n*p)*Real.log (1-p) ∧
    (n*p*Real.log q+(n-n*p)*Real.log (1-q) =
      n*p*Real.log p+(n-n*p)*Real.log (1-p) ↔ q=p) := by
  have hpn : 0<n*p := mul_pos hn hp
  have hrest : 0<n-n*p := by nlinarith
  have hp' : 0<1-p := by linarith
  have hq' : 0<1-q := by linarith
  have hcancel : n*p*(q/p-1)+(n-n*p)*((1-q)/(1-p)-1)=0 := by
    field_simp [hp.ne',hp'.ne']
    <;> ring
  have hsecond := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hq' hp')) hrest.le
  rw [Real.log_div hq'.ne' hp'.ne'] at hsecond
  have hstrict : q≠p → n*p*Real.log q+(n-n*p)*Real.log (1-q) <
      n*p*Real.log p+(n-n*p)*Real.log (1-p) := by
    intro hne
    have hratio : q/p≠1 := by
      intro heq
      apply hne
      have hmul := (div_eq_iff hp.ne').mp heq
      simpa using hmul
    have hfirst := mul_lt_mul_of_pos_left
      (Real.log_lt_sub_one_of_pos (div_pos hq hp) hratio) hpn
    rw [Real.log_div hq.ne' hp.ne'] at hfirst
    nlinarith
  constructor
  · by_cases heq : q=p
    · subst q; exact le_rfl
    · exact (hstrict heq).le
  · constructor
    · intro heq
      by_contra hne
      linarith [hstrict hne]
    · rintro rfl; rfl

/-- T11(a), logistic-cell version: strict monotonicity of inverse logit
transfers the binary probability maximum to a unique real predictor. -/
theorem binomial_logistic_unique_max (n p η₀ : ℝ) (hn : 0<n)
    (hp : 0<p) (hu : p<1) (hfit : logistic η₀=p) (η : ℝ) :
    binomialLogLikelihood logistic n (n*p) η ≤ binomialLogLikelihood logistic n (n*p) η₀ ∧
    (binomialLogLikelihood logistic n (n*p) η=binomialLogLikelihood logistic n (n*p) η₀ ↔ η=η₀) := by
  have h := binomial_probability_unique_max n p (logistic η) hn hp hu
    (Real.sigmoid_pos η) (Real.sigmoid_lt_one η)
  constructor
  · simpa [binomialLogLikelihood,hfit] using h.1
  · constructor
    · intro heq
      have heq' : logistic η=p := h.2.mp (by simpa [binomialLogLikelihood,hfit] using heq)
      exact Real.sigmoid_injective (heq'.trans hfit.symm)
    · rintro rfl; rfl

/-- T11(a), p. 257 counterexample: the actual likelihood of the 200 binary
observations has the unique finite global ML maximizer (-log 99,2 log 99). -/
theorem extreme_unique_mle :
    let L := Real.log 99
    (∀ θ : Fin 2 → ℝ, extremeLikelihood θ ≤ extremeLikelihood ![-L,2*L]) ∧
    (∀ θ : Fin 2 → ℝ, extremeLikelihood θ=extremeLikelihood ![-L,2*L] → θ=![-L,2*L]) := by
  dsimp only
  let L := Real.log 99
  have hfit₀ : logistic (-L)=1/100 := extreme_sigmoid_arithmetic.2.1
  have hfit₁ : logistic L=99/100 := extreme_sigmoid_arithmetic.1
  have h₀ (η : ℝ) :
      binomialLogLikelihood logistic 100 1 η≤binomialLogLikelihood logistic 100 1 (-L) ∧
      (binomialLogLikelihood logistic 100 1 η=binomialLogLikelihood logistic 100 1 (-L) ↔ η= -L) := by
    convert binomial_logistic_unique_max 100 (1/100) (-L) (by norm_num) (by norm_num) (by norm_num) hfit₀ η using 1 <;> norm_num
  have h₁ (η : ℝ) :
      binomialLogLikelihood logistic 100 99 η≤binomialLogLikelihood logistic 100 99 L ∧
      (binomialLogLikelihood logistic 100 99 η=binomialLogLikelihood logistic 100 99 L ↔ η=L) := by
    convert binomial_logistic_unique_max 100 (99/100) L (by norm_num) (by norm_num) (by norm_num) hfit₁ η using 1 <;> norm_num
  have hl : -L+2*L=L := by ring
  constructor
  · intro θ
    change binomialLogLikelihood logistic 100 1 (θ 0)+
      binomialLogLikelihood logistic 100 99 (θ 0+θ 1) ≤
      binomialLogLikelihood logistic 100 1 (-L)+binomialLogLikelihood logistic 100 99 (-L+2*L)
    rw [hl]
    exact add_le_add (h₀ (θ 0)).1 (h₁ (θ 0+θ 1)).1
  · intro θ heq
    change binomialLogLikelihood logistic 100 1 (θ 0)+
      binomialLogLikelihood logistic 100 99 (θ 0+θ 1) =
      binomialLogLikelihood logistic 100 1 (-L)+binomialLogLikelihood logistic 100 99 (-L+2*L) at heq
    rw [hl] at heq
    have he₀ : binomialLogLikelihood logistic 100 1 (θ 0)=binomialLogLikelihood logistic 100 1 (-L) := by
      linarith [(h₀ (θ 0)).1,(h₁ (θ 0+θ 1)).1]
    have he₁ : binomialLogLikelihood logistic 100 99 (θ 0+θ 1)=binomialLogLikelihood logistic 100 99 L := by
      linarith [(h₀ (θ 0)).1,(h₁ (θ 0+θ 1)).1]
    have ht₀ := (h₀ (θ 0)).2.mp he₀
    have ht₁ := (h₁ (θ 0+θ 1)).2.mp he₁
    funext j
    fin_cases j
    · exact ht₀
    · change θ 1=2*L
      linarith

/-- P015-T1, p. 261: the complete explicit law, causal assumptions, positivity,
arbitrarily small effective-profile family, actual population OLS coefficient,
IPW moments, every-n Chebyshev bound, and convergence in probability. -/
def RareCounterexample : Prop :=
  (IsLaw (rareLaw (1/1000000)) ∧
    (∀ a d, rareY a d = rareY a 0 + (1 + binaryX a) * d) ∧
    fCondIndep (rareLaw (1/1000000)) binaryX
      (fun a => (rareY a 0, 1 + binaryX a)) binaryD ∧
    (∀ x ∈ ({0,1} : Finset ℝ),
      fCondMean (rareLaw (1/1000000)) binaryX binaryD x =
        1/1000000 + (1/2 - 1/1000000) * x ∧
      0 < fCondProb (rareLaw (1/1000000)) binaryX binaryD x 0 ∧
      0 < fCondProb (rareLaw (1/1000000)) binaryX binaryD x 1) ∧
    fCondMean (rareLaw (1/1000000)) binaryX
      (fWeight (rareLaw (1/1000000)) binaryX binaryD) 0 = 999999/1000000000000 ∧
    fCondMean (rareLaw (1/1000000)) binaryX
      (fWeight (rareLaw (1/1000000)) binaryX binaryD) 1 = 1/4 ∧
    fMass (rareLaw (1/1000000)) (fun a => binaryX a = 0) = 1/2 ∧
    fMass (fEffective (rareLaw (1/1000000)) binaryX binaryD)
      (fun a => binaryX a = 0) = 999999/250000999999 ∧
    (999999/250000999999 : ℝ) < 1/250000 ∧
    rareZ (1/1000000) = ![0,1000000,-4,8] ∧
    fExpectation (rareLaw (1/1000000)) (fun a => 1+binaryX a) = 3/2 ∧
    fExpectation (rareLaw (1/1000000)) (rareZ (1/1000000)) = 3/2 ∧
    fExpectation (rareLaw (1/1000000)) (fun a => rareZ (1/1000000) a ^ 2) = 500020 ∧
    fVariance (rareLaw (1/1000000)) (rareZ (1/1000000)) = 2000071/4 ∧
    fExpectation (fEffective (rareLaw (1/1000000)) binaryX binaryD)
      (fun a => 1+binaryX a) = 500000999999/250000999999 ∧
    (500000999999/250000999999 : ℝ) ≠ 3/2) ∧
  (∀ (ε : ℝ) (hε : 0 < ε) (hu : ε < 1/2),
    IsLaw (rareLaw ε) ∧
    (∀ a d, rareY a d = rareY a 0+(1+binaryX a)*d) ∧
    fCondIndep (rareLaw ε) binaryX (fun a => (rareY a 0,1+binaryX a)) binaryD ∧
    (∀ x ∈ ({0,1} : Finset ℝ),
      fCondMean (rareLaw ε) binaryX binaryD x = ε+(1/2-ε)*x ∧
      0 < fCondProb (rareLaw ε) binaryX binaryD x 0 ∧
      0 < fCondProb (rareLaw ε) binaryX binaryD x 1) ∧
    fMass (fEffective (rareLaw ε) binaryX binaryD) (fun a => binaryX a=0) =
      ε*(1-ε)/(ε*(1-ε)+1/4) ∧
    0 < fMass (fEffective (rareLaw ε) binaryX binaryD) (fun a => binaryX a=0) ∧
    fMass (fEffective (rareLaw ε) binaryX binaryD) (fun a => binaryX a=0) < 4*ε) ∧
  (let p := rareLaw (1/1000000);
    let W : Matrix (Fin 4) (Fin 3) ℝ := fun i => ![1,binaryD i,binaryX i];
    Matrix.det (fun j k => fExpectation p (fun i => W i j*W i k)) ≠ 0 ∧
    populationOLS p W (fun i => rareY i (binaryD i)) 1 = 500000999999/250000999999) ∧
  (∀ (n : ℕ) (hn : 1 ≤ n),
    IsLaw (iidLaw (rareLaw (1/1000000)) n) ∧
    fExpectation (iidLaw (rareLaw (1/1000000)) n)
      (sampleAverage (rareZ (1/1000000)) n) = 3/2 ∧
    fVariance (iidLaw (rareLaw (1/1000000)) n)
      (sampleAverage (rareZ (1/1000000)) n) = 2000071/(4*n) ∧
    (∀ δ : ℝ, 0 < δ → fMass (iidLaw (rareLaw (1/1000000)) n)
      (fun a => δ ≤ |sampleAverage (rareZ (1/1000000)) n a-3/2|) ≤
        2000071/(4*n*δ^2))) ∧
  (∀ (δ : ℝ) (hδ : 0 < δ),
    Tendsto (fun n : ℕ => fMass (iidLaw (rareLaw (1/1000000)) n)
      (fun a => δ ≤ |sampleAverage (rareZ (1/1000000)) n a-3/2|)) atTop (𝓝 0))

/-- P015-T1, p. 261: the complete explicit law, causal assumptions, positivity,
arbitrarily small effective-profile family, actual population OLS coefficient,
IPW moments, every-n Chebyshev bound, and convergence in probability. -/
theorem RareCounterexample_checked : RareCounterexample := by
  exact ⟨@rare_weight_counterexample, @rare_profile_bound, @rare_ols_arithmetic, @rare_ipw_all_n, @rare_ipw_tail_convergence⟩

/-- P015-T2, p. 261: positive weights with missing pair support, both
unconfounded worlds and their different nominal/effective effects, no common
pair, and impossibility of one observed-data estimator consistent in both worlds. -/
def MultivaluedCounterexample : Prop :=
  (IsLaw multiLaw ∧
    (∀ a, fCondMean multiLaw binaryX multiD (binaryX a) = 1/2 + binaryX a/2) ∧
    fWeight multiLaw binaryX multiD = ![1/4,1/4,1,1] ∧
    (∀ a, 0 < fWeight multiLaw binaryX multiD a) ∧
    fExpectation multiLaw (fWeight multiLaw binaryX multiD) = 5/8 ∧
    fEffective multiLaw binaryX multiD = ![1/10,1/10,2/5,2/5] ∧
    fMass (fEffective multiLaw binaryX multiD) (fun a => binaryX a = 0) = 1/5 ∧
    fMass (fEffective multiLaw binaryX multiD) (fun a => binaryX a = 1) = 4/5 ∧
    fCondProb multiLaw binaryX multiD 1 1 = 0 ∧
    fCondProb (fEffective multiLaw binaryX multiD) binaryX multiD 1 1 = 0 ∧
    fCondIndep multiLaw binaryX (fun a => (worldA a 0, worldA a 1, worldA a 2)) multiD ∧
    fCondIndep multiLaw binaryX (fun a => (worldB a 0, worldB a 1, worldB a 2)) multiD ∧
    (∀ a, worldA a (multiD a) = multiD a ∧ worldB a (multiD a) = multiD a) ∧
    fExpectation multiLaw (contrast worldA 0 1) = 1 ∧
    fExpectation multiLaw (contrast worldB 0 1) = 2 ∧
    fExpectation (fEffective multiLaw binaryX multiD) (contrast worldA 0 1) = 1 ∧
    fExpectation (fEffective multiLaw binaryX multiD) (contrast worldB 0 1) = 13/5) ∧
  ((∀ d : ℝ, (0 < fCondProb multiLaw binaryX multiD 0 d ∧
      0 < fCondProb multiLaw binaryX multiD 1 d) ↔ d=0) ∧
    (∀ d : ℝ, (0 < fCondProb (fEffective multiLaw binaryX multiD) binaryX multiD 0 d ∧
      0 < fCondProb (fEffective multiLaw binaryX multiD) binaryX multiD 1 d) ↔ d=0)) ∧
  (∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (draw : ℕ → Ω → Fin 4)
    (hdraw : MultiSampling P draw) (T : ∀ n : ℕ, (Fin n → ℝ × ℝ × ℝ) → ℝ),
    ¬ (TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldA (draw i s))) atTop (fun _ => (1:ℝ)) ∧
      TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldB (draw i s))) atTop (fun _ => (2:ℝ))) ∧
    ¬ (TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldA (draw i s))) atTop (fun _ => (1:ℝ)) ∧
      TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldB (draw i s))) atTop (fun _ => (13/5:ℝ))))

/-- P015-T2, p. 261: positive weights with missing pair support, both
unconfounded worlds and their different nominal/effective effects, no common
pair, and impossibility of one observed-data estimator consistent in both worlds. -/
theorem MultivaluedCounterexample_checked : MultivaluedCounterexample := by
  exact ⟨@multivalued_support_counterexample, @common_support_arithmetic, @no_common_consistent_estimator⟩

/-- P015-T3, p. 261: population positivity and variance, the positive-probability
ordered sample, its actual treatment OLS residuals and zero estimated weights,
and the nonsingular full regression design. -/
def FittedZeroCounterexample : Prop :=
  (IsLaw multiLaw ∧
    (∀ x ∈ ({0,1} : Finset ℝ), ∀ d ∈ ({0,1} : Finset ℝ),
      fCondProb multiLaw binaryX binaryD x d = 1/2) ∧
    (∀ x ∈ ({0,1} : Finset ℝ),
      fCondMean multiLaw binaryX (fWeight multiLaw binaryX binaryD) x = 1/4) ∧
    (1/4 : ℝ)^4 = 1/256 ∧ (0 : ℝ) < 1/256 ∧
    zeroSampleV.transpose * zeroSampleV = !![4,2;2,2] ∧
    zeroSampleV.transpose.mulVec zeroSampleD = ![1,1] ∧
    (!![4,2;2,2] : Matrix (Fin 2) (Fin 2) ℝ).mulVec ![0,1/2] = ![1,1] ∧
    (zeroSampleV.transpose * zeroSampleV).det ≠ 0 ∧
    sampleResidual zeroSampleV zeroSampleD ![0,1/2] = ![0,0,-1/2,1/2] ∧
    (fun a => sampleResidual zeroSampleV zeroSampleD ![0,1/2] a ^ 2) = ![0,0,1/4,1/4] ∧
    zeroSampleW.transpose * zeroSampleW = !![4,1,2;1,1,1;2,1,2] ∧
    (zeroSampleW.transpose * zeroSampleW).det = 2) ∧
  (ols zeroSampleV zeroSampleD=![0,1/2] ∧
    sampleResidual zeroSampleV zeroSampleD (ols zeroSampleV zeroSampleD)=![0,0,-1/2,1/2] ∧
    iidLaw multiLaw 4 (![0,0,2,3] : Fin 4 → Fin 4)=1/256) ∧
  (∀ i : Fin 4, zeroSampleV i 1=binaryX ((![0,0,2,3] : Fin 4 → Fin 4) i) ∧
      zeroSampleD i=binaryD ((![0,0,2,3] : Fin 4 → Fin 4) i))

/-- P015-T3, p. 261: population positivity and variance, the positive-probability
ordered sample, its actual treatment OLS residuals and zero estimated weights,
and the nonsingular full regression design. -/
theorem FittedZeroCounterexample_checked : FittedZeroCounterexample := by
  exact ⟨@fitted_zero_counterexample, @zero_sample_ols_arithmetic, @zero_sample_link⟩

/-- P015-T5, Appendix C: the exact 72-observation Bernoulli odds-link
counterexample, admissible fitted means, rank, zero substituted residual,
nonzero true score, true likelihood directional derivatives and nonmaximality. -/
def OddsCounterexample : Prop :=
  ((∀ i, 0 < oddsW.mulVec ![1,0,1] i) ∧
    (∀ i, 0 < oddsSuccess i ∧ oddsSuccess i < 12) ∧
    groupedResidual oddsW (fun _ => 12) oddsSuccess oddsMean ![1,0,1] = 0 ∧
    groupedScore oddsW (fun _ => 12) oddsSuccess oddsMean ![1,0,1] = ![2/3,1/3,-2/3] ∧
    groupedScore oddsW (fun _ => 12) oddsSuccess oddsMean ![1,0,1] ≠ 0) ∧
  (¬ ∀ θ : Fin 3 → ℝ, (∀ i, 0 < oddsW.mulVec θ i) →
    groupedLikelihood oddsW (fun _ => 12) oddsSuccess oddsMean θ ≤
      groupedLikelihood oddsW (fun _ => 12) oddsSuccess oddsMean ![1,0,1]) ∧
  ((oddsW.transpose*oddsW).det = 36) ∧
  ((∀ i : Fin 2 × Fin 3, oddsW i 0=1 ∧ (oddsW i 1=0 ∨ oddsW i 1=1) ∧
      oddsSuccess i = (if i.2=0 then (7:ℝ) else if i.2=1 then 6 else 10)) ∧
    (∀ i : Fin 2 × Fin 3, oddsMean (oddsW.mulVec ![1,0,1] i)=
      (![1/2,2/3,3/4] : Fin 3 → ℝ) i.2) ∧
    ((12:ℝ) • (oddsW.transpose*oddsW)).det=62208 ∧
    (∀ v : Fin 3 → ℝ, HasDerivAt
      (fun t => groupedLikelihood oddsW (fun _ => 12) oddsSuccess oddsMean
        (fun j => (![1,0,1] : Fin 3 → ℝ) j+t*v j))
      (dotProduct (![2/3,1/3,-2/3] : Fin 3 → ℝ) v) 0))

/-- P015-T5, Appendix C: the exact 72-observation Bernoulli odds-link
counterexample, admissible fitted means, rank, zero substituted residual,
nonzero true score, true likelihood directional derivatives and nonmaximality. -/
theorem OddsCounterexample_checked : OddsCounterexample := by
  exact ⟨@odds_score_counterexample, @odds_not_mle_calculus, @odds_gram_determinant, @odds_model_details⟩

/-- P015-T6, Appendix C: the fixed standard-normal quantile, all exact CDF
values, zero substituted equation, nonzero genuine score, strict rational
score bound and failure to maximize, with full rank and interior binary counts. -/
def ProbitCounterexample : Prop :=
  (0 < probitA ∧ probitA < 7/10 ∧
    normalCDF (-probitA) = 1/4 ∧ normalCDF 0 = 1/2 ∧ normalCDF probitA = 3/4 ∧
    groupedResidual probitW (fun _ => 8) probitSuccess normalCDF ![0,0,probitA] = 0 ∧
    groupedScore probitW (fun _ => 8) probitSuccess normalCDF ![0,0,probitA] =
      ![4*(probitH probitA-probitH 0),2*(probitH probitA-probitH 0),0] ∧
    probitH probitA = (16/3)*normalPDF probitA ∧ probitH 0 = 4*normalPDF 0 ∧
    13/625 < 2*(probitH probitA-probitH 0) ∧
    ¬ ∀ θ : Fin 3 → ℝ,
      groupedLikelihood probitW (fun _ => 8) probitSuccess normalCDF θ ≤
      groupedLikelihood probitW (fun _ => 8) probitSuccess normalCDF ![0,0,probitA]) ∧
  ((∀ i : Fin 2 × Fin 3, probitW i 0=1 ∧ (probitW i 1=0 ∨ probitW i 1=1) ∧
      0<probitSuccess i ∧ probitSuccess i<8) ∧
    ((8:ℝ) • (probitW.transpose*probitW)).det=18432)




/-- P015-T7, pp. 257/265: the specified probability law and uniform-U causal
model, actual score derivatives and finite matrices, and the actual ML branch
derivative 120/119 versus OLS derivative 1 at the same outcome mean. -/
def RootLinkCounterexample : Prop :=
  (RootMLDerivative (1/16) (120/119) ∧ RootMLDerivative 0 1 ∧
    (∀ ε, |ε| ≤ 1/16 → fExpectation rootLaw (rootProbability (1/16) ε) = 1/4) ∧
    (∀ ε, |ε| ≤ 1/16 → populationOLS rootLaw rootZ (rootProbability (1/16) ε) 1 = ε) ∧
    (120/119 : ℝ) ≠ 1) ∧
  (IsLaw rootLaw ∧
    (fun j k => fExpectation rootLaw (fun i => rootZ i j*rootZ i k)) =
      (!![1,0,0;0,5/24,0;0,0,2/3] : Matrix (Fin 3) (Fin 3) ℝ) ∧
    (fun j k => fExpectation rootLaw
      (fun i => rootZ i j*rootZ i k*(rootBaseline (1/16) (rootX i)-1/4))) =
      (!![0,0,0;0,-1/384,0;0,0,1/24] : Matrix (Fin 3) (Fin 3) ℝ) ∧
    ((-32/9 : ℝ) • (!![0,0,0;0,-1/384,0;0,0,1/24] : Matrix (Fin 3) (Fin 3) ℝ) -
      (16/3 : ℝ) • !![1,0,0;0,5/24,0;0,0,2/3]) = !![-16/3,0,0;0,-119/108,0;0,0,-100/27] ∧
    (∀ t : Fin 3 → ℝ,
      (!![-16/3,0,0;0,-119/108,0;0,0,-100/27] : Matrix (Fin 3) (Fin 3) ℝ).mulVec t+
        ![0,10/9,0] = 0 ↔ t = ![0,120/119,0]) ∧
    (120/119 : ℝ) ≠ 1) ∧
  (∀ (ε : ℝ) (hε : |ε| ≤ 1/16),
    fExpectation rootLaw (rootProbability (1/16) ε)=1/4 ∧
    populationOLS rootLaw rootZ (rootProbability (1/16) ε) 1=ε) ∧
  (IsProbabilityMeasure rootUniformLaw) ∧
  (IsProbabilityMeasure rootUnitLaw) ∧
  (∀ (a ε : ℝ) (ha : a=0 ∨ a=1/16) (hε : |ε|≤1/16),
    (∀ x ∈ ({-1,0,1} : Finset ℝ), rootUnitLaw {s | rootUnitX s=x}=1/3) ∧
    (∀ᵐ s ∂rootUnitLaw, rootUnitD s=0 ∨ rootUnitD s=1) ∧
    (∀ᵐ s ∂rootUnitLaw, 0≤rootUnitU s ∧ rootUnitU s≤1) ∧
    (∀ u : ℝ, 0≤u → u≤1 →
      rootUnitLaw {s | rootUnitU s≤u}=ENNReal.ofReal u) ∧
    IndepFun rootUnitU (fun s => (rootUnitX s,rootUnitD s)) rootUnitLaw ∧
    CondIndepFun (MeasurableSpace.comap rootUnitX inferInstance)
      (Measurable.comap_le (show Measurable rootUnitX from measurable_fst.fst))
      (fun s => (rootUnitY a ε 0 s,rootUnitTau a ε s)) rootUnitD rootUnitLaw ∧
    rootUnitLaw[rootUnitD | MeasurableSpace.comap rootUnitX inferInstance] =ᵐ[rootUnitLaw]
      (fun s => rootE (rootUnitX s)) ∧
    (∀ᵐ s ∂rootUnitLaw, rootUnitY a ε (rootUnitD s) s=
      rootUnitY a ε 0 s+rootUnitTau a ε s*rootUnitD s) ∧
    rootUnitLaw[(fun s => rootUnitY a ε (rootUnitD s) s) |
      MeasurableSpace.comap (fun s => (rootUnitX s,rootUnitD s)) inferInstance] =ᵐ[rootUnitLaw]
      (fun s => rootBaseline a (rootUnitX s)+ε*(rootUnitD s-rootE (rootUnitX s))) ∧
    (∫ s, rootUnitY a ε (rootUnitD s) s ∂rootUnitLaw)=1/4) ∧
  ((∀ η : ℝ, 0<η → η<1 → scoreMultiplier rootMean η=2/(η*(1-η^2))) ∧
    deriv rootMean (1/2)=1 ∧ scoreMultiplier rootMean (1/2)=16/3 ∧
    deriv (scoreMultiplier rootMean) (1/2)= -32/9 ∧
    rootScore (1/16) 0 ![1/2,0,0]=0 ∧
    (∀ v : Fin 3 → ℝ, HasDerivAt
      (fun t => rootScore (1/16) 0 (fun j => (![1/2,0,0] : Fin 3 → ℝ) j+t*v j))
      ((!![-16/3,0,0;0,-119/108,0;0,0,-100/27] : Matrix (Fin 3) (Fin 3) ℝ).mulVec v) 0) ∧
    HasDerivAt (fun ε => rootScore (1/16) ε ![1/2,0,0]) ![0,10/9,0] 0 ∧
    (∀ a ε θ v, (a=0 ∨ a=1/16) → |ε| ≤ 1/16 → rootAdmissible θ → HasDerivAt
      (fun t => rootLikelihood a ε (fun j => θ j+t*v j)) (dotProduct (rootScore a ε θ) v) 0))




/-- P015-T11, p. 257: the full ranked binary dataset, unique finite logistic
MLE, predictors ±log 99 outside the exact radius pi, and the probability
and score-error lower bounds for every Taylor degree. Every degree has
probability error ≥49/100 at both predictors and treatment score error ≥49. -/
def TaylorCounterexample : Prop :=
  (let L := Real.log 99;
    (∀ θ : Fin 2 → ℝ, extremeLikelihood θ ≤ extremeLikelihood ![-L,2*L]) ∧
    (∀ θ : Fin 2 → ℝ, extremeLikelihood θ = extremeLikelihood ![-L,2*L] → θ = ![-L,2*L]) ∧
    logistic (-L) = 1/100 ∧ logistic L = 99/100 ∧
    logit ((1+99)/200) = 0 ∧ 9/2 < L ∧ Real.pi < 9/2 ∧
    (∀ N : ℕ, 49/100 ≤ |logisticTaylor N 0 L-logistic L| ∧
      49/100 ≤ |logisticTaylor N 0 (-L)-logistic (-L)| ∧
      49 ≤ |100*(99/100-logisticTaylor N 0 L)|)) ∧
  (∃ s : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun z : ℂ => (1+Complex.exp (-z))⁻¹) s 0 ∧
      s.radius=ENNReal.ofReal Real.pi) ∧
  (let W : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;1,1]
    let L := Real.log 99;
    ((100 : ℝ) • (W.transpose*W)).det=10000 ∧
    (0:ℝ)<1 ∧ (1:ℝ)<100 ∧ (0:ℝ)<99 ∧ (99:ℝ)<100 ∧
    groupedResidual W (fun _ => 100) ![1,99] logistic ![-L,2*L]=0) ∧
  (logistic (Real.log 99) = 99/100 ∧ logistic (-Real.log 99) = 1/100 ∧
    logit ((1+99)/200) = 0 ∧ Real.pi < 9/2 ∧
    |logisticTaylor 0 0 (Real.log 99)-logistic (Real.log 99)| = 49/100) ∧
  (9/2 < Real.log 99)




/-- P015-T4, p. 261: the complete discrete-X finite-second-moment correction
for zero variance, two endpoints, binary variance and effective-law reversal,
with the three explicit failures of the invalid printed converses. -/
def PositivityCorrection : Prop :=
  (∀ {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] [Countable B] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (D : Ω → ℝ) (hX : Measurable X) (hD : Measurable D)
    (h₂ : MemLp D 2 P),
    (∀ x, 0 < P {s | X s = x} →
      (∀ d d', d ≠ d' → 0 < cellProb P X D x d → 0 < cellProb P X D x d' →
        0 < cellVar P X D x) ∧
      (cellVar P X D x = 0 → ∀ᵐ s ∂cellLaw P X x, D s = cellMean P X D x)) ∧
    ((∀ᵐ s ∂P, D s = 0 ∨ D s = 1) → ∀ x, 0 < P {s | X s = x} →
      cellVar P X D x = cellProb P X D x 1*(1-cellProb P X D x 1) ∧
      (0 < cellVar P X D x ↔ 0 < cellProb P X D x 1 ∧ cellProb P X D x 1 < 1)) ∧
    (0 < (∫ s, discreteWeight P X D s ∂P) →
      Integrable (discreteWeight P X D) P →
      ∀ x, 0 < P {s | X s = x} →
      (discreteEffective P X D {s | X s = x}).toReal =
        (P {s | X s = x}).toReal*cellVar P X D x/(∫ s, discreteWeight P X D s ∂P) ∧
      (discreteEffective P X D {s | X s = x} = 0 ↔ cellVar P X D x = 0) ∧
      ((∀ᵐ s ∂P, D s = 0 ∨ D s = 1) →
        0 < cellProb P X D x 1 → cellProb P X D x 1 < 1 →
        cellProb (discreteEffective P X D) X D x 1 = 1-cellProb P X D x 1 ∧
        cellProb (discreteEffective P X D) X D x 0 = cellProb P X D x 1))) ∧
  (RareCounterexample) ∧
  (MultivaluedCounterexample.{0}) ∧
  (FittedZeroCounterexample)





theorem rare_population_ols : RareCounterexample := RareCounterexample_checked


theorem rare_ipw_consistent : RareCounterexample := RareCounterexample_checked


theorem no_common_pair : MultivaluedCounterexample := MultivaluedCounterexample_checked


theorem fitted_zero_actual_ols : FittedZeroCounterexample := FittedZeroCounterexample_checked


theorem odds_not_mle : OddsCounterexample := OddsCounterexample_checked


theorem odds_design_full_rank : OddsCounterexample := OddsCounterexample_checked





































end
end AronowAudit.P015

namespace AronowAudit.P015.PositivityCompletion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

lemma cell_probability {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → B) (x : B) (hx : 0 < P {s | X s=x}) :
    IsProbabilityMeasure (cellLaw P X x) :=
  cond_isProbabilityMeasure hx.ne'

lemma cell_memLp {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → B) (D : Ω → ℝ) (x : B)
    (hx : 0 < P {s | X s=x}) (h₂ : MemLp D 2 P) : MemLp D 2 (cellLaw P X x) :=
  (h₂.restrict _).smul_measure (by simpa using ENNReal.inv_ne_top.mpr hx.ne')

lemma cell_ae_eq {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] (P : Measure Ω) (X : Ω → B)
    (hX : Measurable X) (x : B) : ∀ᵐ s ∂cellLaw P X x, X s=x :=
  Measure.ae_smul_measure (ae_restrict_mem (hX (measurableSet_singleton x))) _

lemma cell_ae_of_ae {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → B) (x : B) {p : Ω → Prop} (h : ∀ᵐ s ∂P, p s) :
    ∀ᵐ s ∂cellLaw P X x, p s :=
  Measure.ae_smul_measure (ae_restrict_of_ae h) _

lemma zero_variance_constant {Ω B : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → B) (D : Ω → ℝ)
    (x : B) (hx : 0 < P {s | X s=x}) (h₂ : MemLp D 2 P)
    (hv : cellVar P X D x=0) : ∀ᵐ s ∂cellLaw P X x, D s=cellMean P X D x := by
  letI := cell_probability P X x hx
  apply ae_eq_integral_of_variance_eq_zero (cell_memLp P X D x hx h₂)
  rw [variance_eq_integral (cell_memLp P X D x hx h₂).aemeasurable]
  exact hv

lemma positive_variance_of_endpoints {Ω B : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → B) (D : Ω → ℝ)
    (x : B) (hx : 0 < P {s | X s=x}) (h₂ : MemLp D 2 P)
    (d d' : ℝ) (hd : d≠d') (hp : 0 < cellProb P X D x d)
    (hp' : 0 < cellProb P X D x d') : 0 < cellVar P X D x := by
  have hv : 0 ≤ cellVar P X D x := integral_nonneg (fun _ => sq_nonneg _)
  by_contra h
  have hz : cellVar P X D x=0 := le_antisymm (le_of_not_gt h) hv
  have hc := zero_variance_constant P X D x hx h₂ hz
  have he (a : ℝ) (ha : 0 < cellProb P X D x a) : a=cellMean P X D x := by
    by_contra hn
    have hn' : cellMean P X D x ≠ a := Ne.symm hn
    have hm : cellLaw P X x {s | D s=a}=0 := by
      calc
        _ = cellLaw P X x ∅ := by
          apply measure_congr
          filter_upwards [hc] with s hs
          simp [hs,hn']
        _ = 0 := measure_empty
    simp [cellProb,hm] at ha
  exact hd ((he d hp).trans (he d' hp').symm)

lemma binary_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℝ) (hD : Measurable D) (hbin : ∀ᵐ s ∂μ, D s=0∨D s=1) :
    (∫ s,D s ∂μ)=(μ {s | D s=1}).toReal := by
  calc
    _ = ∫ s, ({s | D s=1} : Set Ω).indicator (fun _ => (1:ℝ)) s ∂μ := by
      apply integral_congr_ae
      filter_upwards [hbin] with s hs
      rcases hs with hs|hs <;> simp [hs]
    _ = _ := integral_indicator_one (hD (measurableSet_singleton 1))

lemma binary_probability_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (D : Ω → ℝ) (hD : Measurable D)
    (hbin : ∀ᵐ s ∂μ, D s=0∨D s=1) :
    (μ {s | D s=0}).toReal=1-(μ {s | D s=1}).toReal := by
  have he : (μ {s | D s=0}).toReal=(μ {s | D s=1}ᶜ).toReal := by
    apply measureReal_congr
    filter_upwards [hbin] with s hs
    rcases hs with hs|hs <;> simp [hs]
  rw [he]
  change μ.real {s | D s=1}ᶜ=1-μ.real {s | D s=1}
  rw [measureReal_compl (s:={s|D s=1}) (by exact hD (measurableSet_singleton 1)),probReal_univ]

lemma binary_cell_variance {Ω B : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → B) (D : Ω → ℝ)
    (hD : Measurable D) (x : B) (hx : 0 < P {s | X s=x})
    (hbin : ∀ᵐ s ∂P,D s=0∨D s=1) :
    cellVar P X D x=cellProb P X D x 1*(1-cellProb P X D x 1) ∧
    (0 < cellVar P X D x ↔ 0 < cellProb P X D x 1 ∧ cellProb P X D x 1<1) := by
  let μ:=cellLaw P X x
  letI : IsProbabilityMeasure μ:=cell_probability P X x hx
  have hb : ∀ᵐ s ∂μ,D s=0∨D s=1:=cell_ae_of_ae P X x hbin
  have h₂ : MemLp D 2 μ:=MemLp.of_bound hD.aestronglyMeasurable 1 (by
    filter_upwards [hb] with s hs
    rcases hs with hs|hs <;> simp [hs])
  have hm:=binary_mean μ D hD hb
  have hsq : (∫s,D s^2 ∂μ)=(∫s,D s ∂μ):=by
    apply integral_congr_ae
    filter_upwards [hb] with s hs
    rcases hs with hs|hs <;> simp [hs]
  have he : cellVar P X D x=cellProb P X D x 1*(1-cellProb P X D x 1):=by
    change (∫s,(D s-(∫t,D t ∂μ))^2 ∂μ)=_
    rw [←variance_eq_integral hD.aemeasurable,variance_eq_sub h₂]
    simp only [Pi.pow_apply]
    rw [hsq,hm]
    dsimp [cellProb,μ]
    ring
  refine ⟨he,?_⟩
  rw [he]
  have hp : 0≤cellProb P X D x 1:=ENNReal.toReal_nonneg
  have hu : cellProb P X D x 1≤1:=by exact measureReal_le_one
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨h,h'⟩
    exact mul_pos h (sub_pos.mpr h')

lemma normalized_density_mass {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : Ω → ℝ) (hw : Integrable w P) (hn : ∀ s,0≤w s) (S : Set Ω)
    (hS : MeasurableSet S) :
    (((ENNReal.ofReal (∫s,w s∂P))⁻¹ • P.withDensity (fun s=>ENNReal.ofReal (w s))) S).toReal=
      (∫s in S,w s∂P)/(∫s,w s∂P) := by
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (integral_nonneg hn),withDensity_apply _ hS,
    ←ofReal_integral_eq_lintegral_ofReal hw.restrict (Eventually.of_forall hn),
    ENNReal.toReal_ofReal (integral_nonneg hn)]
  ring


lemma cell_integral {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → B) (x : B) (hx : 0<P {s|X s=x}) (f : Ω → ℝ) :
    (∫s in {s|X s=x},f s∂P)=(P {s|X s=x}).toReal*(∫s,f s∂cellLaw P X x) := by
  have hp : (P {s|X s=x}).toReal≠0 :=
    (ENNReal.toReal_pos hx.ne' (measure_ne_top _ _)).ne'
  rw [cellLaw,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  field_simp

lemma weighted_cell_integral {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (D : Ω → ℝ) (hX : Measurable X) (x : B) (hx : 0<P {s|X s=x}) :
    (∫s in {s|X s=x},discreteWeight P X D s∂P)=
      (P {s|X s=x}).toReal*cellVar P X D x := by
  rw [cell_integral P X x hx]
  congr 1
  apply integral_congr_ae
  filter_upwards [cell_ae_eq P X hX x] with s hs
  simp [discreteWeight,cellVar,hs]

lemma effective_probability {Ω B : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → B) (D : Ω → ℝ)
    (hw : Integrable (discreteWeight P X D) P)
    (hpos : 0<∫s,discreteWeight P X D s∂P) :
    IsProbabilityMeasure (discreteEffective P X D) := by
  constructor
  unfold discreteEffective
  rw [Measure.smul_apply,smul_eq_mul,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall (fun _=>sq_nonneg _))]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top

lemma cellProb_ratio {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → B) (D : Ω → ℝ) (hD : Measurable D) (x : B) (d : ℝ) :
    cellProb P X D x d=(P {s|X s=x ∧ D s=d}).toReal/(P {s|X s=x}).toReal := by
  unfold cellProb cellLaw
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,
    Measure.restrict_apply (t:={s|D s=d}) (by exact hD (measurableSet_singleton d))]
  have hs : {s|D s=d}∩{s|X s=x}={s|X s=x ∧ D s=d}:=by ext s;simp only [Set.mem_inter_iff,Set.mem_setOf_eq];tauto
  rw [hs]
  ring

lemma weighted_joint_integral {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] (P : Measure Ω) (X : Ω → B) (D : Ω → ℝ)
    (hX : Measurable X) (hD : Measurable D) (x : B) (d : ℝ) :
    (∫s in {s|X s=x ∧ D s=d},discreteWeight P X D s∂P)=
      (P {s|X s=x ∧ D s=d}).toReal*(d-cellMean P X D x)^2 := by
  have hs : MeasurableSet {s|X s=x ∧ D s=d}:=
    (hX (measurableSet_singleton x)).inter (hD (measurableSet_singleton d))
  rw [setIntegral_congr_fun hs (g:=fun _=>(d-cellMean P X D x)^2) (by
    intro s hs; simp [discreteWeight,hs.1,hs.2]),setIntegral_const,smul_eq_mul]
  rfl

lemma effective_cell_mass {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (D : Ω → ℝ) (hX : Measurable X)
    (hw : Integrable (discreteWeight P X D) P) (x : B) (hx : 0<P {s|X s=x}) :
    (discreteEffective P X D {s|X s=x}).toReal=
      (P {s|X s=x}).toReal*cellVar P X D x/(∫s,discreteWeight P X D s∂P) := by
  rw [discreteEffective,normalized_density_mass P _ hw (fun _=>sq_nonneg _)
    {s|X s=x} (by exact hX (measurableSet_singleton x)),weighted_cell_integral P X D hX x hx]

lemma effective_cellProb {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (D : Ω → ℝ) (hX : Measurable X) (hD : Measurable D)
    (hw : Integrable (discreteWeight P X D) P)
    (hpos : 0<∫s,discreteWeight P X D s∂P) (x : B) (hx : 0<P {s|X s=x})
    (hv : 0<cellVar P X D x) (d : ℝ) :
    cellProb (discreteEffective P X D) X D x d=
      cellProb P X D x d*(d-cellMean P X D x)^2/cellVar P X D x := by
  rw [cellProb_ratio _ _ _ hD,cellProb_ratio _ _ _ hD,
    effective_cell_mass P X D hX hw x hx]
  have hs : MeasurableSet {s|X s=x ∧ D s=d}:=
    (hX (measurableSet_singleton x)).inter (hD (measurableSet_singleton d))
  rw [discreteEffective,normalized_density_mass P _ hw (fun _=>sq_nonneg _) _ hs,
    weighted_joint_integral P X D hX hD x d]
  have hp : (P {s|X s=x}).toReal≠0 :=
    (ENNReal.toReal_pos hx.ne' (measure_ne_top _ _)).ne'
  field_simp [hp,hpos.ne',hv.ne']

theorem corrected_positivity_completed {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] [Countable B] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (D : Ω → ℝ) (hX : Measurable X) (hD : Measurable D)
    (h₂ : MemLp D 2 P) :
    (∀ x, 0 < P {s | X s = x} →
      (∀ d d', d ≠ d' → 0 < cellProb P X D x d → 0 < cellProb P X D x d' →
        0 < cellVar P X D x) ∧
      (cellVar P X D x = 0 → ∀ᵐ s ∂cellLaw P X x, D s = cellMean P X D x)) ∧
    ((∀ᵐ s ∂P, D s = 0 ∨ D s = 1) → ∀ x, 0 < P {s | X s = x} →
      cellVar P X D x = cellProb P X D x 1*(1-cellProb P X D x 1) ∧
      (0 < cellVar P X D x ↔ 0 < cellProb P X D x 1 ∧ cellProb P X D x 1 < 1)) ∧
    (0 < (∫ s, discreteWeight P X D s ∂P) →
      Integrable (discreteWeight P X D) P →
      ∀ x, 0 < P {s | X s = x} →
      (discreteEffective P X D {s | X s = x}).toReal =
        (P {s | X s = x}).toReal*cellVar P X D x/(∫ s, discreteWeight P X D s ∂P) ∧
      (discreteEffective P X D {s | X s = x} = 0 ↔ cellVar P X D x = 0) ∧
      ((∀ᵐ s ∂P, D s = 0 ∨ D s = 1) →
        0 < cellProb P X D x 1 → cellProb P X D x 1 < 1 →
        cellProb (discreteEffective P X D) X D x 1 = 1-cellProb P X D x 1 ∧
        cellProb (discreteEffective P X D) X D x 0 = cellProb P X D x 1)) := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    exact ⟨fun d d' hd hp hp' => positive_variance_of_endpoints P X D x hx h₂ d d' hd hp hp',
      zero_variance_constant P X D x hx h₂⟩
  · intro hb x hx
    exact binary_cell_variance P X D hD x hx hb
  · intro hpos hw x hx
    letI := effective_probability P X D hw hpos
    have he:=effective_cell_mass P X D hX hw x hx
    have hp : (P {s|X s=x}).toReal≠0 :=
      (ENNReal.toReal_pos hx.ne' (measure_ne_top _ _)).ne'
    refine ⟨he,?_,?_⟩
    · have hq : discreteEffective P X D {s|X s=x}=0 ↔
          (discreteEffective P X D {s|X s=x}).toReal=0 := by
        simp [ENNReal.toReal_eq_zero_iff,measure_ne_top]
      rw [hq,he]
      simp [div_eq_zero_iff,mul_eq_zero,hp,hpos.ne']
    · intro hb ht hu
      have hv:0<cellVar P X D x:=(binary_cell_variance P X D hD x hx hb).2.mpr ⟨ht,hu⟩
      have hevar:cellVar P X D x=cellProb P X D x 1*(1-cellProb P X D x 1):=
        (binary_cell_variance P X D hD x hx hb).1
      have hm:cellMean P X D x=cellProb P X D x 1:=
        binary_mean (cellLaw P X x) D hD (cell_ae_of_ae P X x hb)
      have hzero:cellProb P X D x 0=1-cellProb P X D x 1:=by
        letI:=cell_probability P X x hx
        exact binary_probability_zero (cellLaw P X x) D hD (cell_ae_of_ae P X x hb)
      have hu0 : 1-cellProb P X D x 1≠0:=(sub_pos.mpr hu).ne'
      constructor
      · rw [effective_cellProb P X D hX hD hw hpos x hx hv 1,hm,hevar]
        field_simp [ht.ne',hu0]
      · rw [effective_cellProb P X D hX hD hw hpos x hx hv 0,hm,hevar,hzero]
        field_simp [ht.ne',hu0]
        <;> ring

 theorem positivity_implies_variance_completed {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] [Countable B] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (D : Ω → ℝ) (hX : Measurable X) (hD : Measurable D) (h₂ : MemLp D 2 P)
    (d d' : ℝ) (hd : d ≠ d')
    (hpositive : ∀ x, 0 < P {s | X s=x} → 0 < cellProb P X D x d ∧ 0 < cellProb P X D x d') :
    ∀ x, 0 < P {s | X s=x} → 0 < cellVar P X D x := by
  intro x hx
  exact positive_variance_of_endpoints P X D x hx h₂ d d' hd (hpositive x hx).1 (hpositive x hx).2

theorem PositivityCorrection_completed : PositivityCorrection :=
  ⟨@corrected_positivity_completed,@RareCounterexample_checked,
    @MultivaluedCounterexample_checked.{0},@FittedZeroCounterexample_checked⟩

end
end AronowAudit.P015.PositivityCompletion

namespace AronowAudit.P015
noncomputable section
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P015-T4(i)–(iii), the corrected positivity theorem (p. 261).
X is discrete and D has a finite second moment; the law can have infinitely many
or continuously distributed treatment values. The binary effective law reverses p to 1-p.
The three invalid converses are separately addressed by T1–T3.
T17(A): positivity at both distinct endpoints implies positive variance at
each represented profile. -/
theorem corrected_positivity {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] [Countable B] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (D : Ω → ℝ) (hX : Measurable X) (hD : Measurable D)
    (h₂ : MemLp D 2 P) :
    (∀ x, 0 < P {s | X s = x} →
      (∀ d d', d ≠ d' → 0 < cellProb P X D x d → 0 < cellProb P X D x d' →
        0 < cellVar P X D x) ∧
      (cellVar P X D x = 0 → ∀ᵐ s ∂cellLaw P X x, D s = cellMean P X D x)) ∧
    ((∀ᵐ s ∂P, D s = 0 ∨ D s = 1) → ∀ x, 0 < P {s | X s = x} →
      cellVar P X D x = cellProb P X D x 1*(1-cellProb P X D x 1) ∧
      (0 < cellVar P X D x ↔ 0 < cellProb P X D x 1 ∧ cellProb P X D x 1 < 1)) ∧
    (0 < (∫ s, discreteWeight P X D s ∂P) →
      Integrable (discreteWeight P X D) P →
      ∀ x, 0 < P {s | X s = x} →
      (discreteEffective P X D {s | X s = x}).toReal =
        (P {s | X s = x}).toReal*cellVar P X D x/(∫ s, discreteWeight P X D s ∂P) ∧
      (discreteEffective P X D {s | X s = x} = 0 ↔ cellVar P X D x = 0) ∧
      ((∀ᵐ s ∂P, D s = 0 ∨ D s = 1) →
        0 < cellProb P X D x 1 → cellProb P X D x 1 < 1 →
        cellProb (discreteEffective P X D) X D x 1 = 1-cellProb P X D x 1 ∧
        cellProb (discreteEffective P X D) X D x 0 = cellProb P X D x 1)) := by
  exact PositivityCompletion.corrected_positivity_completed P X D hX hD h₂

theorem positivity_implies_variance {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] [Countable B] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (D : Ω → ℝ) (hX : Measurable X) (hD : Measurable D) (h₂ : MemLp D 2 P)
    (d d' : ℝ) (hd : d ≠ d')
    (hpositive : ∀ x, 0 < P {s | X s=x} → 0 < cellProb P X D x d ∧ 0 < cellProb P X D x d') :
    ∀ x, 0 < P {s | X s=x} → 0 < cellVar P X D x := by
  exact PositivityCompletion.positivity_implies_variance_completed P X D hX hD h₂ d d' hd hpositive

theorem PositivityCorrection_checked : PositivityCorrection := by
  exact PositivityCompletion.PositivityCorrection_completed

theorem binary_variance_and_reversal : PositivityCorrection := PositivityCorrection_checked

theorem finite_zero_variance : PositivityCorrection := PositivityCorrection_checked

theorem finite_pair_positive_variance : PositivityCorrection := PositivityCorrection_checked

end
end AronowAudit.P015

namespace AronowAudit.P015.AnalyticCompletion
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
attribute [local instance] Classical.propDecidable

lemma normalPDF_eq (x : ℝ) : normalPDF x=(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-x^2/2) := by
  simp [normalPDF,gaussianPDFReal]

lemma normalPDF_pos (x : ℝ) : 0 < normalPDF x := gaussianPDFReal_pos 0 1 x (by norm_num)
lemma continuous_normalPDF : Continuous normalPDF := by unfold normalPDF gaussianPDFReal; fun_prop

lemma normalCDF_integral (x : ℝ) : normalCDF x=∫ y in Iic x,normalPDF y := by
  rw [normalCDF,cdf_eq_real,measureReal_def,gaussianReal_apply_eq_integral _ (by norm_num)]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun y=>gaussianPDFReal_nonneg 0 1 y))

lemma normalCDF_zero : normalCDF 0=1/2 := P053.NormalCompletion.normal_cdf_zero
lemma normalCDF_neg (x : ℝ) : normalCDF (-x)=1-normalCDF x := P053.NormalCompletion.normal_cdf_neg x
lemma strictMono_normalCDF : StrictMono normalCDF := P053.NormalCompletion.strictMono_normal_cdf

lemma normalCDF_integral_zero (x : ℝ) : normalCDF x=1/2+∫ y in (0:ℝ)..x,normalPDF y := by
  have hh:=intervalIntegral.integral_Iic_sub_Iic
    (integrable_gaussianPDFReal 0 1).integrableOn (integrable_gaussianPDFReal 0 1).integrableOn
    (a:=(0:ℝ)) (b:=x)
  change (∫ y in Iic x,normalPDF y)-(∫ y in Iic (0:ℝ),normalPDF y)=_ at hh
  rw [←normalCDF_integral,←normalCDF_integral,normalCDF_zero] at hh
  change normalCDF x-1/2=(∫ y in (0:ℝ)..x,normalPDF y) at hh
  linarith

lemma hasDerivAt_normalCDF (x : ℝ) : HasDerivAt normalCDF (normalPDF x) x := by
  have hh:= (intervalIntegral.integral_hasDerivAt_right
    (continuous_normalPDF.intervalIntegrable 0 x)
    continuous_normalPDF.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_normalPDF.continuousAt).const_add (1/2)
  convert hh using 1
  funext y
  rw [normalCDF_integral_zero]

lemma hasDerivAt_normalPDF (x : ℝ) : HasDerivAt normalPDF (-x*normalPDF x) x := by
  have hh:= (((hasDerivAt_pow 2 x).neg.div_const 2).exp).const_mul (Real.sqrt (2*Real.pi))⁻¹
  dsimp at hh
  convert hh using 1
  · exact funext normalPDF_eq
  · rw [normalPDF_eq]
    ring

lemma normalCDF_bounds (x : ℝ) : 0 < normalCDF x ∧ normalCDF x < 1 := by
  constructor
  · exact lt_of_le_of_lt (cdf_nonneg _ _) (strictMono_normalCDF (by linarith : x-1 < x))
  · exact lt_of_lt_of_le (strictMono_normalCDF (by linarith : x < x+1)) (cdf_le_one _ _)

lemma scoreMultiplier_normalCDF (x : ℝ) : scoreMultiplier normalCDF x=probitH x := by
  rw [scoreMultiplier,(hasDerivAt_normalCDF x).deriv,probitH]

lemma hasDerivAt_probitH_zero : HasDerivAt probitH 0 0 := by
  have hf:=hasDerivAt_normalCDF 0
  have hd:=hf.mul ((hasDerivAt_const 0 1).sub hf)
  have hq:=(hasDerivAt_normalPDF 0).div hd (by
    change normalCDF 0*(1-normalCDF 0)≠0
    rw [normalCDF_zero];norm_num)
  convert hq using 1
  · rfl
  · dsimp only [Pi.mul_apply,Pi.sub_apply]
    rw [normalCDF_zero]
    ring

lemma probitH_nonconstant : ¬ ∃ c : ℝ,∀ x : ℝ,probitH x=c := by
  rintro ⟨c,hc⟩
  have hden (x : ℝ) : normalCDF x*(1-normalCDF x)≠0 := by
    have hh:=normalCDF_bounds x
    exact mul_ne_zero hh.1.ne' (sub_pos.mpr hh.2).ne'
  have he (x : ℝ) : normalPDF x=c*(normalCDF x*(1-normalCDF x)) := by
    exact (div_eq_iff (hden x)).mp (hc x)
  have hefun : normalPDF=(fun x=>c*(normalCDF x*(1-normalCDF x))) := funext he
  have hcpos : 0 < c := by
    have hh:=he 0
    rw [normalCDF_zero] at hh
    nlinarith [normalPDF_pos 0]
  have hder (x : ℝ) : -x=c*(1-2*normalCDF x) := by
    have hf:=hasDerivAt_normalCDF x
    have hh:=((hf.mul ((hasDerivAt_const x 1).sub hf)).const_mul c)
    simp only [Pi.mul_apply,Pi.sub_apply] at hh
    have hh' : -x*normalPDF x=c*(normalPDF x*(1-normalCDF x)+normalCDF x*(0-normalPDF x)) := by
      have hd:=congrArg (fun f : ℝ→ℝ=>deriv f x) hefun
      rw [(hasDerivAt_normalPDF x).deriv,hh.deriv] at hd
      exact hd
    have hfac : normalPDF x*(-x)=normalPDF x*(c*(1-2*normalCDF x)) := by nlinarith only [hh']
    exact (mul_left_cancel₀ (normalPDF_pos x).ne') hfac
  have hh:=hder c
  have hp:=normalCDF_bounds c
  have hprod:=mul_pos hcpos (sub_pos.mpr hp.2)
  nlinarith

 theorem probit_multiplier_at_half_completed : normalCDF 0=1/2 ∧ deriv probitH 0=0 :=
  ⟨normalCDF_zero,hasDerivAt_probitH_zero.deriv⟩

 theorem corrected_probit_score_completed (N K : ℕ) (W : Matrix (Fin N) (Fin (K+2)) ℝ)
    (Y : Fin N → ℝ) (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (θ v : Fin (K+2) → ℝ) :
    HasDerivAt (fun t => groupedLikelihood W (fun _ => 1) Y normalCDF (fun j => θ j+t*v j))
      (∑ i, probitH (W.mulVec θ i)*(Y i-normalCDF (W.mulVec θ i))*W.mulVec v i) 0 ∧
    ¬ ∃ c : ℝ, ∀ η : ℝ, probitH η = c := by
  refine ⟨?_,probitH_nonconstant⟩
  simpa only [scoreMultiplier_normalCDF,one_mul] using
    likelihood_directional_derivative_calculus W (fun _=>1) Y normalCDF θ v
      (fun i=>(hasDerivAt_normalCDF _).differentiableAt)
      (fun i=>(normalCDF_bounds _).1) (fun i=>(normalCDF_bounds _).2)

lemma normalPDF_zero_lower : (39:ℝ)/100 < normalPDF 0 := by
  rw [normalPDF_eq]
  norm_num only [zero_pow (by norm_num : 2≠0),neg_zero,zero_div,Real.exp_zero,mul_one]
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [inv_eq_one_div]
  apply (lt_div_iff₀ hs).mpr
  have hs2:=Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hp:=Real.pi_lt_d2
  nlinarith

lemma normalPDF_exp (x : ℝ) : normalPDF x=normalPDF 0*Real.exp (-x^2/2) := by
  rw [normalPDF_eq,normalPDF_eq]
  norm_num

lemma normalCDF_cubic_lower (x : ℝ) (hx : 0 ≤ x) :
    normalPDF 0*(x-x^3/6) ≤ normalCDF x-1/2 := by
  let F : ℝ→ℝ:=fun t=>normalCDF t-normalPDF 0*(t-t^3/6)
  have hd (t : ℝ) : HasDerivAt F (normalPDF t-normalPDF 0*(1-t^2/2)) t := by
    have hh:=(hasDerivAt_normalCDF t).sub
      ((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6))).const_mul (normalPDF 0))
    convert hh using 1
    · rfl
    · ring
  have hm : Monotone F:=monotone_of_hasDerivAt_nonneg hd (by
    intro t
    change 0 ≤ normalPDF t-normalPDF 0*(1-t^2/2)
    rw [normalPDF_exp t]
    have hh:=mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-t^2/2)) (normalPDF_pos 0).le
    nlinarith)
  have hh:=hm hx
  dsimp [F] at hh
  rw [normalCDF_zero] at hh
  nlinarith

lemma normalCDF_seven_tenths : (3:ℝ)/4 < normalCDF (7/10) := by
  have hh:=normalCDF_cubic_lower (7/10) (by norm_num)
  nlinarith [normalPDF_zero_lower]

lemma probitA_eq_critical : probitA=P053.normalCritical (1/2) := by
  unfold probitA P053.normalCritical P053.standardNormalCDF
  congr 1
  ext a
  norm_num [normalCDF,cdf_eq_real,measureReal_def]

lemma probitA_cdf : normalCDF probitA=3/4 := by
  rw [probitA_eq_critical]
  have hh:=P053.NormalCompletion.normalCritical_cdf (1/2) (by norm_num) (by norm_num)
  rw [P053.NormalCompletion.standardNormalCDF_eq_cdf] at hh
  norm_num only [show (1:ℝ)-(1/2)/2=3/4 by norm_num] at hh
  exact hh

lemma probitA_bounds : 0 < probitA ∧ probitA < 7/10 := by
  constructor
  · apply strictMono_normalCDF.lt_iff_lt.mp
    rw [normalCDF_zero,probitA_cdf]
    norm_num
  · apply strictMono_normalCDF.lt_iff_lt.mp
    rw [probitA_cdf]
    exact normalCDF_seven_tenths

lemma probit_score_gap : (13:ℝ)/625 < 2*(probitH probitA-probitH 0) := by
  have hzero:=normalPDF_zero_lower
  have ha:=probitA_bounds
  have he:=Real.add_one_le_exp (-probitA^2/2)
  have hh:=normalPDF_exp probitA
  have ha2 : probitA^2 < (49:ℝ)/100 := by nlinarith
  have hpdf : (151:ℝ)/200*normalPDF 0 < normalPDF probitA := by
    have hm:=mul_le_mul_of_nonneg_left he (normalPDF_pos 0).le
    have hp:=mul_pos (normalPDF_pos 0) (show 0 < (49:ℝ)/100-probitA^2 by linarith)
    nlinarith
  unfold probitH
  rw [probitA_cdf,normalCDF_zero]
  norm_num
  linarith

lemma normalPDF_neg (x : ℝ) : normalPDF (-x)=normalPDF x := by
  rw [normalPDF_eq,normalPDF_eq]
  simp

lemma probitH_neg (x : ℝ) : probitH (-x)=probitH x := by
  unfold probitH
  rw [normalPDF_neg,normalCDF_neg]
  congr 1
  ring

lemma probitH_values : probitH probitA=(16/3)*normalPDF probitA ∧ probitH 0=4*normalPDF 0 := by
  constructor
  · unfold probitH
    rw [probitA_cdf]
    ring
  · unfold probitH
    rw [normalCDF_zero]
    ring

lemma probit_grouped_score :
    groupedScore probitW (fun _=>8) probitSuccess normalCDF ![0,0,probitA]=
      ![4*(probitH probitA-probitH 0),2*(probitH probitA-probitH 0),0] := by
  ext j
  fin_cases j <;>
    norm_num [groupedScore,scoreMultiplier_normalCDF,probitW,probitSuccess,Matrix.mulVec,
      dotProduct,Fintype.sum_prod_type,Fin.sum_univ_succ,probitH_neg,normalCDF_neg,
      probitA_cdf,normalCDF_zero] <;> ring

lemma probit_not_mle : ¬∀θ : Fin 3→ℝ,
    groupedLikelihood probitW (fun _=>8) probitSuccess normalCDF θ≤
      groupedLikelihood probitW (fun _=>8) probitSuccess normalCDF ![0,0,probitA] := by
  intro hmax
  let F : ℝ→ℝ:=fun t=>groupedLikelihood probitW (fun _=>8) probitSuccess normalCDF
    (fun j=>(![0,0,probitA] : Fin 3→ℝ) j+t*(![0,1,0] : Fin 3→ℝ) j)
  have hd:=likelihood_directional_derivative_calculus probitW (fun _=>8) probitSuccess normalCDF
    ![0,0,probitA] ![0,1,0]
    (fun i=>(hasDerivAt_normalCDF _).differentiableAt)
    (fun i=>(normalCDF_bounds _).1) (fun i=>(normalCDF_bounds _).2)
  have hs : (∑ i,scoreMultiplier normalCDF (probitW.mulVec ![0,0,probitA] i)*
      (probitSuccess i-8*normalCDF (probitW.mulVec ![0,0,probitA] i))*
      probitW.mulVec ![0,1,0] i)=2*(probitH probitA-probitH 0) := by
    norm_num [scoreMultiplier_normalCDF,probitW,probitSuccess,Matrix.mulVec,
      dotProduct,Fintype.sum_prod_type,Fin.sum_univ_succ,probitH_neg,normalCDF_neg,
      probitA_cdf,normalCDF_zero]
    ring
  rw [hs] at hd
  change HasDerivAt F (2*(probitH probitA-probitH 0)) 0 at hd
  have hlocal : IsLocalMax F 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa [F] using hmax (fun j=>(![0,0,probitA] : Fin 3→ℝ) j+t*(![0,1,0] : Fin 3→ℝ) j)
  have hz:=hlocal.hasDerivAt_eq_zero hd
  linarith [probit_score_gap]

 theorem probit_score_counterexample_completed :
    0 < probitA ∧ probitA < 7/10 ∧
    normalCDF (-probitA) = 1/4 ∧ normalCDF 0 = 1/2 ∧ normalCDF probitA = 3/4 ∧
    groupedResidual probitW (fun _ => 8) probitSuccess normalCDF ![0,0,probitA] = 0 ∧
    groupedScore probitW (fun _ => 8) probitSuccess normalCDF ![0,0,probitA] =
      ![4*(probitH probitA-probitH 0),2*(probitH probitA-probitH 0),0] ∧
    probitH probitA = (16/3)*normalPDF probitA ∧ probitH 0 = 4*normalPDF 0 ∧
    13/625 < 2*(probitH probitA-probitH 0) ∧
    ¬ ∀ θ : Fin 3 → ℝ,
      groupedLikelihood probitW (fun _ => 8) probitSuccess normalCDF θ ≤
      groupedLikelihood probitW (fun _ => 8) probitSuccess normalCDF ![0,0,probitA] := by
  have hn : normalCDF (-probitA)=1/4 := by rw [normalCDF_neg,probitA_cdf];norm_num
  exact ⟨probitA_bounds.1,probitA_bounds.2,hn,normalCDF_zero,probitA_cdf,
    probit_residual_conditional probitA hn normalCDF_zero probitA_cdf,
    probit_grouped_score,probitH_values.1,probitH_values.2,probit_score_gap,probit_not_mle⟩

 theorem ProbitCounterexample_checked_completed : ProbitCounterexample :=
  ⟨probit_score_counterexample_completed,probit_design_details⟩

end
end AronowAudit.P015.AnalyticCompletion

namespace AronowAudit.P015
noncomputable section
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P015-T6, the explicitly named probit model: the substituted equation
has a zero at (0,0,Φ⁻¹(3/4)), but the genuine score has treatment coordinate
strictly above 13/625 and that point is not an ML maximizer. -/
theorem probit_score_counterexample :
    0 < probitA ∧ probitA < 7/10 ∧
    normalCDF (-probitA) = 1/4 ∧ normalCDF 0 = 1/2 ∧ normalCDF probitA = 3/4 ∧
    groupedResidual probitW (fun _ => 8) probitSuccess normalCDF ![0,0,probitA] = 0 ∧
    groupedScore probitW (fun _ => 8) probitSuccess normalCDF ![0,0,probitA] =
      ![4*(probitH probitA-probitH 0),2*(probitH probitA-probitH 0),0] ∧
    probitH probitA = (16/3)*normalPDF probitA ∧ probitH 0 = 4*normalPDF 0 ∧
    13/625 < 2*(probitH probitA-probitH 0) ∧
    ¬ ∀ θ : Fin 3 → ℝ,
      groupedLikelihood probitW (fun _ => 8) probitSuccess normalCDF θ ≤
      groupedLikelihood probitW (fun _ => 8) probitSuccess normalCDF ![0,0,probitA] := by
  exact AnalyticCompletion.probit_score_counterexample_completed

/-- T8(iii): the corrected probit score keeps φ/[Φ(1-Φ)] and this
multiplier is nonconstant. -/
theorem corrected_probit_score (N K : ℕ) (W : Matrix (Fin N) (Fin (K+2)) ℝ)
    (Y : Fin N → ℝ) (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (θ v : Fin (K+2) → ℝ) :
    HasDerivAt (fun t => groupedLikelihood W (fun _ => 1) Y normalCDF (fun j => θ j+t*v j))
      (∑ i, probitH (W.mulVec θ i)*(Y i-normalCDF (W.mulVec θ i))*W.mulVec v i) 0 ∧
    ¬ ∃ c : ℝ, ∀ η : ℝ, probitH η = c := by
  exact AnalyticCompletion.corrected_probit_score_completed N K W Y hY hW θ v

/-- T8(iv)'s specified symmetric probit point: although the probit multiplier
is not constant, its derivative vanishes at η₀=0, where Φ(0)=1/2. -/
theorem probit_multiplier_at_half :
    normalCDF 0=1/2 ∧ deriv probitH 0=0 := by
  exact AnalyticCompletion.probit_multiplier_at_half_completed

theorem ProbitCounterexample_checked : ProbitCounterexample := by
  exact AnalyticCompletion.ProbitCounterexample_checked_completed

theorem probit_residual_core : ProbitCounterexample := ProbitCounterexample_checked

end
end AronowAudit.P015

namespace AronowAudit.P015.RootMLCompletion
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
attribute [local instance] Classical.propDecidable

lemma scalar_tangent (q η ξ : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hη0 : 0 < η) (hη1 : η < 1) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    binomialLogLikelihood rootMean 1 q η - binomialLogLikelihood rootMean 1 q ξ ≤
      (2*q/ξ-2*(1-q)*ξ/(1-ξ^2))*(η-ξ) - (1-q)/(1-ξ^2)*(η-ξ)^2 := by
  have hηsq : 0 < 1-η^2 := by nlinarith
  have hξsq : 0 < 1-ξ^2 := by nlinarith
  have hl1 := Real.log_le_sub_one_of_pos (div_pos hη0 hξ0)
  have hl2 := Real.log_le_sub_one_of_pos (div_pos hηsq hξsq)
  rw [Real.log_div hη0.ne' hξ0.ne'] at hl1
  rw [Real.log_div hηsq.ne' hξsq.ne'] at hl2
  have h1 := mul_le_mul_of_nonneg_left hl1 (show 0 ≤ 2*q by positivity)
  have h2 := mul_le_mul_of_nonneg_left hl2 (show 0 ≤ 1-q by linarith)
  unfold binomialLogLikelihood rootMean
  rw [Real.log_pow,Real.log_pow]
  have heq : (2*q/ξ-2*(1-q)*ξ/(1-ξ^2))*(η-ξ) - (1-q)/(1-ξ^2)*(η-ξ)^2 =
      2*q*(η/ξ-1)+(1-q)*((1-η^2)/(1-ξ^2)-1) := by
    field_simp [hξ0.ne',hξsq.ne']
    <;> ring
  rw [heq]
  nlinarith

lemma rootProbability_bounds (a ε : ℝ) (ha : a=0 ∨ a=1/16) (hε : |ε|≤1/16) (i : Fin 6) :
    0 < rootProbability a ε i ∧ rootProbability a ε i < 1 := by
  have hε' := abs_le.mp hε
  rcases ha with rfl | rfl <;> fin_cases i <;>
    norm_num [rootProbability,rootBaseline,rootX,rootD,rootE] <;> constructor <;> linarith

lemma rootZ_injective : Function.Injective rootZ.mulVec := by
  intro θ t h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  norm_num [rootZ,rootX,rootD,rootE,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1 h2
  ext j
  fin_cases j <;> simp only [Fin.reduceFinMk] <;> linarith

lemma rootLikelihood_tangent (a ε : ℝ) (ha : a=0 ∨ a=1/16) (hε : |ε|≤1/16)
    (θ t : Fin 3 → ℝ) (hθ : rootAdmissible θ) (ht : rootAdmissible t) :
    rootLikelihood a ε t-rootLikelihood a ε θ ≤ dotProduct (rootScore a ε θ) (t-θ) -
      ∑ i, rootLaw i*(1-rootProbability a ε i)/(1-(rootZ.mulVec θ i)^2)*
        (rootZ.mulVec t i-rootZ.mulVec θ i)^2 := by
  have hb (i : Fin 6) := scalar_tangent (rootProbability a ε i) (rootZ.mulVec t i)
    (rootZ.mulVec θ i) (rootProbability_bounds a ε ha hε i).1
      (rootProbability_bounds a ε ha hε i).2 (ht i).1 (ht i).2 (hθ i).1 (hθ i).2
  have heq (i : Fin 6) : 2*rootProbability a ε i/(rootZ.mulVec θ i)-
      2*(1-rootProbability a ε i)*(rootZ.mulVec θ i)/(1-(rootZ.mulVec θ i)^2) =
        scoreMultiplier rootMean (rootZ.mulVec θ i)*(rootProbability a ε i-rootMean (rootZ.mulVec θ i)) := by
    rw [RootCompletion.rootMultiplier_admissible _ (hθ i).1 (hθ i).2,rootMean]
    have hsq : 1-(rootZ.mulVec θ i)^2≠0 := by have h:=hθ i; nlinarith
    field_simp [(hθ i).1.ne',hsq]
    <;> ring
  have hw (i : Fin 6) : 0 ≤ rootLaw i := root_link_matrix_arithmetic.1.1 i
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>mul_le_mul_of_nonneg_left (hb i) (hw i))
  simp_rw [heq] at hsum
  convert hsum using 1
  · unfold rootLikelihood
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · unfold rootScore fExpectation dotProduct
    simp only [Matrix.mulVec,dotProduct,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]
    rw [Finset.sum_comm,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hh : (∑ j,rootLaw i*(rootZ i j*scoreMultiplier rootMean (∑ k,rootZ i k*θ k)*
        (rootProbability a ε i-rootMean (∑ k,rootZ i k*θ k)))*(t-θ) j) =
      rootLaw i*scoreMultiplier rootMean (∑ k,rootZ i k*θ k)*
        (rootProbability a ε i-rootMean (∑ k,rootZ i k*θ k))*
          ((∑ j,rootZ i j*t j)-(∑ j,rootZ i j*θ j)) := by
      rw [← Finset.sum_sub_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.sub_apply]
      ring
    rw [hh]
    ring

lemma root_stationary_unique_max (a ε : ℝ) (ha : a=0 ∨ a=1/16) (hε : |ε|≤1/16)
    (θ : Fin 3 → ℝ) (hθ : rootAdmissible θ) (hs : rootScore a ε θ=0) :
    (∀ t,rootAdmissible t → rootLikelihood a ε t≤rootLikelihood a ε θ) ∧
    (∀ t,rootAdmissible t → rootLikelihood a ε t=rootLikelihood a ε θ → t=θ) := by
  let c : Fin 6 → ℝ := fun i=>rootLaw i*(1-rootProbability a ε i)/(1-(rootZ.mulVec θ i)^2)
  have hc (i : Fin 6) : 0 < c i := by
    have hw : 0 < rootLaw i := by fin_cases i <;> norm_num [rootLaw]
    have hp := rootProbability_bounds a ε ha hε i
    have hη := hθ i
    dsimp [c]
    exact div_pos (mul_pos hw (by linarith)) (by nlinarith)
  have hb (t : Fin 3 → ℝ) (ht : rootAdmissible t) : rootLikelihood a ε t-rootLikelihood a ε θ ≤
      -(∑ i,c i*(rootZ.mulVec t i-rootZ.mulVec θ i)^2) := by
    simpa [hs,c] using rootLikelihood_tangent a ε ha hε θ t hθ ht
  constructor
  · intro t ht
    have hnonneg : 0 ≤ ∑ i,c i*(rootZ.mulVec t i-rootZ.mulVec θ i)^2 :=
      Finset.sum_nonneg (fun i _=>mul_nonneg (hc i).le (sq_nonneg _))
    linarith [hb t ht]
  · intro t ht heq
    apply rootZ_injective
    funext i
    have hsum : (∑ i,c i*(rootZ.mulVec t i-rootZ.mulVec θ i)^2) ≤ 0 := by
      have := hb t ht
      rw [heq] at this
      linarith
    have hi : c i*(rootZ.mulVec t i-rootZ.mulVec θ i)^2 ≤ 0 :=
      (Finset.single_le_sum (fun j _=>mul_nonneg (hc j).le (sq_nonneg (rootZ.mulVec t j-rootZ.mulVec θ j))) (Finset.mem_univ i)).trans hsum
    have hsq : (rootZ.mulVec t i-rootZ.mulVec θ i)^2=0 := by nlinarith [sq_nonneg (rootZ.mulVec t i-rootZ.mulVec θ i),hc i]
    nlinarith [hsq]

lemma rootScore_directional (a : ℝ) (v : Fin 3 → ℝ) : HasDerivAt
    (fun t=>rootScore a 0 (fun j=>(![1/2,0,0] : Fin 3 → ℝ) j+t*v j))
    ((!![-16/3,0,0;0,(4*a-30)/27,0;0,0,(-96-64*a)/27] : Matrix (Fin 3) (Fin 3) ℝ).mulVec v) 0 := by
  have hi (i : Fin 6) : HasDerivAt
      (fun t=>scoreMultiplier rootMean (rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3 → ℝ) j+t*v j) i)*
        (rootProbability a 0 i-rootMean (rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3 → ℝ) j+t*v j) i)))
      (((-32/9)*(rootProbability a 0 i-1/4)-16/3)*rootZ.mulVec v i) 0 := by
    have hη:=RootCompletion.matrix_affine_hasDerivAt rootZ (![1/2,0,0] : Fin 3 → ℝ) v i
    have hη0 : rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3 → ℝ) j+(0:ℝ)*v j) i=1/2 := by simpa using RootCompletion.root_half_predictor i
    have hH : HasDerivAt (fun t=>scoreMultiplier rootMean
        (rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3 → ℝ) j+t*v j) i))
        ((-32/9)*rootZ.mulVec v i) 0 := by
      have hh : HasDerivAt (scoreMultiplier rootMean) (-32/9)
          (rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3 → ℝ) j+(0:ℝ)*v j) i) := by
        rw [hη0]; exact RootCompletion.rootMultiplier_hasDerivAt_half
      exact hh.comp 0 hη
    have hM : HasDerivAt (fun t=>rootMean
        (rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3 → ℝ) j+t*v j) i))
        (rootZ.mulVec v i) 0 := by
      have hh0 : HasDerivAt rootMean 1
          (rootZ.mulVec (fun j=>(![1/2,0,0] : Fin 3 → ℝ) j+(0:ℝ)*v j) i) := by
        rw [hη0]; simpa using RootCompletion.rootMean_hasDerivAt (1/2)
      have hh:=hh0.comp 0 hη
      convert hh using 1 <;> first | rfl | simp
    have hh:=hH.mul ((hasDerivAt_const 0 (rootProbability a 0 i)).sub hM)
    convert hh using 1
    dsimp only [Pi.sub_apply]
    rw [hη0,RootCompletion.rootMultiplier_half,rootMean]
    ring
  have hd (j : Fin 3) := HasDerivAt.fun_sum (u:=Finset.univ)
    (fun i _=>(hi i).const_mul (rootLaw i*rootZ i j))
  have hv:=hasDerivAt_pi.mpr hd
  convert hv using 1
  · funext t j
    unfold rootScore fExpectation
    apply Finset.sum_congr rfl
    intro i _
    ring
  · ext j
    fin_cases j <;>norm_num [rootProbability,rootBaseline,rootLaw,rootZ,rootX,rootD,rootE,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;>ring

lemma rootScore_epsilon (a : ℝ) : HasDerivAt (fun ε=>rootScore a ε ![1/2,0,0]) ![0,10/9,0] 0 := by
  have hd (j : Fin 3) : HasDerivAt (fun ε=>rootScore a ε (![1/2,0,0] : Fin 3 → ℝ) j)
      (∑ i,rootLaw i*rootZ i j*(16/3)*(rootD i-rootE (rootX i))) 0 := by
    unfold rootScore fExpectation
    have hi (i : Fin 6) : HasDerivAt
        (fun ε=>rootLaw i*(rootZ i j*scoreMultiplier rootMean (rootZ.mulVec ![1/2,0,0] i)*
          (rootProbability a ε i-rootMean (rootZ.mulVec ![1/2,0,0] i))))
        (rootLaw i*rootZ i j*(16/3)*(rootD i-rootE (rootX i))) 0 := by
      rw [RootCompletion.root_half_predictor,RootCompletion.rootMultiplier_half]
      unfold rootProbability
      convert (((((hasDerivAt_id 0).mul_const (rootD i-rootE (rootX i))).const_add
        (rootBaseline a (rootX i))).sub_const (rootMean (1/2))).const_mul (rootLaw i*(rootZ i j*(16/3)))) using 1
      · funext ε; dsimp; ring
      · ring
    exact HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=>hi i)
  convert hasDerivAt_pi.mpr hd using 1
  ext j
  fin_cases j <;>norm_num [rootLaw,rootZ,rootD,rootX,rootE,Fin.sum_univ_succ]

abbrev RootSpace := ℝ × (Fin 3 → ℝ)
def center : RootSpace := (0,![1/2,0,0])
def rootChart (a : ℝ) (z : RootSpace) : RootSpace := (z.1,rootScore a z.1 z.2)
def jacDiag (a : ℝ) : Fin 3 → ℝ := ![-16/3,(4*a-30)/27,(-96-64*a)/27]
def epsVec : Fin 3 → ℝ := ![0,10/9,0]

lemma jacDiag_ne_zero (a : ℝ) (ha : a=0 ∨ a=1/16) (j : Fin 3) : jacDiag a j≠0 := by
  rcases ha with rfl | rfl <;> fin_cases j <;> norm_num [jacDiag]

def chartEquiv (a : ℝ) (ha : a=0 ∨ a=1/16) : RootSpace ≃L[ℝ] RootSpace :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun z=>(z.1,fun j=>jacDiag a j*z.2 j+epsVec j*z.1)
    invFun := fun z=>(z.1,fun j=>(z.2 j-epsVec j*z.1)/jacDiag a j)
    left_inv := by
      intro z
      apply Prod.ext
      · rfl
      · funext j
        dsimp
        field_simp [jacDiag_ne_zero a ha j]
        <;> ring
    right_inv := by
      intro z
      apply Prod.ext
      · rfl
      · funext j
        dsimp
        field_simp [jacDiag_ne_zero a ha j]
        <;> ring
    map_add' := by
      intro x y
      apply Prod.ext
      · rfl
      · funext j
        dsimp
        ring
    map_smul' := by
      intro c z
      apply Prod.ext
      · rfl
      · funext j
        dsimp
        ring }

lemma rootChart_contDiffAt (a : ℝ) : ContDiffAt ℝ 1 (rootChart a) center := by
  unfold rootChart
  apply ContDiffAt.prodMk
  · fun_prop
  · unfold rootScore fExpectation
    simp_rw [RootCompletion.rootMultiplier_eq]
    apply contDiffAt_pi.mpr
    intro j
    apply ContDiffAt.sum
    intro i _
    have hpred : rootZ.mulVec center.2 i=1/2 := RootCompletion.root_half_predictor i
    have hden : (rootZ.mulVec center.2 i)^2*(1-(rootZ.mulVec center.2 i)^2)≠0 := by
      rw [hpred]
      norm_num
    unfold rootProbability rootMean Matrix.mulVec dotProduct
    fun_prop (disch := exact hden)

lemma rootScore_center (a : ℝ) : rootScore a 0 ![1/2,0,0]=0 := by
  ext j
  fin_cases j <;> norm_num [rootScore,fExpectation,RootCompletion.root_half_predictor,
    RootCompletion.rootMultiplier_half,rootProbability,rootBaseline,rootMean,rootLaw,rootZ,
    rootX,rootD,rootE,Fin.sum_univ_succ] <;> ring

lemma rootChart_center (a : ℝ) : rootChart a center=(0,0) := by
  change (0,rootScore a 0 ![1/2,0,0])=(0,0)
  rw [rootScore_center]

lemma rootChart_hasStrictFDerivAt (a : ℝ) (ha : a=0 ∨ a=1/16) :
    HasStrictFDerivAt (rootChart a) (chartEquiv a ha : RootSpace →L[ℝ]RootSpace) center := by
  have hf := (rootChart_contDiffAt a).hasStrictFDerivAt (by norm_num)
  let D := fderiv ℝ (rootChart a) center
  have hv (v : Fin 3 → ℝ) : D (0,v)=(0,fun j=>jacDiag a j*v j) := by
    have hl : HasDerivAt (fun t : ℝ=>((0:ℝ),fun j=>(![1/2,0,0] : Fin 3 → ℝ) j+t*v j))
        ((0:ℝ),v) 0 := by
      apply (hasDerivAt_const 0 (0:ℝ)).prodMk
      apply hasDerivAt_pi.mpr
      intro j
      convert (hasDerivAt_const 0 ((![1/2,0,0] : Fin 3 → ℝ) j)).add
        ((hasDerivAt_id 0).mul_const (v j)) using 1 <;> first | rfl | simp
    have hd := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp [center])
    have hh := (hasDerivAt_const 0 (0:ℝ)).prodMk (rootScore_directional a v)
    have heq : ((!![-16/3,0,0;0,(4*a-30)/27,0;0,0,(-96-64*a)/27] : Matrix (Fin 3) (Fin 3) ℝ).mulVec v)=
        (fun j=>jacDiag a j*v j) := by
      ext j
      fin_cases j <;> simp [jacDiag,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    rw [heq] at hh
    exact hd.unique hh
  have hε : D (1,0)=(1,epsVec) := by
    have hl : HasDerivAt (fun ε : ℝ=>(ε,(![1/2,0,0] : Fin 3 → ℝ))) ((1:ℝ),0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 _)
    have hd := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl rfl
    have hh := (hasDerivAt_id 0).prodMk (rootScore_epsilon a)
    exact hd.unique hh
  have hD : D=(chartEquiv a ha : RootSpace →L[ℝ]RootSpace) := by
    apply ContinuousLinearMap.ext
    intro z
    have hz : z=z.1 • ((1:ℝ),(0 : Fin 3 → ℝ))+(0,z.2) := by
      ext <;> simp
    rw [hz,map_add,map_smul,hε,hv]
    apply Prod.ext
    · simp [chartEquiv]
    · funext j
      simp [chartEquiv]
      ring
  exact hD ▸ hf

theorem rootMLDerivative_actual (a : ℝ) (ha : a=0 ∨ a=1/16) :
    RootMLDerivative a (30/(30-4*a)) := by
  let hf := rootChart_hasStrictFDerivAt a ha
  let inv := hf.localInverse (rootChart a) (chartEquiv a ha) center
  let θ : ℝ → Fin 3 → ℝ := fun ε=>(inv (ε,0)).2
  have hinv0 : inv (0,0)=center := by
    simpa only [rootChart_center] using hf.localInverse_apply_image
  have hθ0 : θ 0=![1/2,0,0] := congrArg Prod.snd hinv0
  have harg : HasDerivAt (fun ε : ℝ=>(ε,(0 : Fin 3 → ℝ))) ((1:ℝ),0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 _)
  have hder : HasDerivAt (fun ε : ℝ=>inv (ε,0)) ((chartEquiv a ha).symm (1,0)) 0 := by
    exact hf.to_localInverse.hasFDerivAt.comp_hasDerivAt_of_eq 0 harg (rootChart_center a)
  have hθder : HasDerivAt θ (((chartEquiv a ha).symm (1,0)).2) 0 :=
    (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)).hasFDerivAt.comp_hasDerivAt 0 hder
  have htreat : HasDerivAt (fun ε=>θ ε 1) (30/(30-4*a)) 0 := by
    have hh := hasDerivAt_pi.mp hθder 1
    convert hh using 1
    rcases ha with rfl | rfl <;> norm_num [chartEquiv,jacDiag,epsVec]
  have hstat : ∀ᶠ ε in 𝓝 (0:ℝ), rootScore a ε (θ ε)=0 := by
    have ht : Tendsto (fun ε : ℝ=>(ε,(0 : Fin 3 → ℝ))) (𝓝 0) (𝓝 (rootChart a center)) := by
      rw [rootChart_center]
      exact harg.continuousAt.tendsto
    filter_upwards [ht.eventually hf.eventually_right_inverse] with ε hε
    have hfirst := congrArg Prod.fst hε
    have hsecond := congrArg Prod.snd hε
    change (inv (ε,0)).1=ε at hfirst
    change rootScore a (inv (ε,0)).1 (θ ε)=0 at hsecond
    rwa [hfirst] at hsecond
  have had : ∀ᶠ ε in 𝓝 (0:ℝ), rootAdmissible (θ ε) := by
    apply eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun ε=>rootZ.mulVec (θ ε) i) 0 := by
      unfold Matrix.mulVec dotProduct
      exact (HasDerivAt.fun_sum (u:=Finset.univ)
        (fun j _=>(hasDerivAt_pi.mp hθder j).const_mul (rootZ i j))).continuousAt
    have hv : rootZ.mulVec (θ 0) i=1/2 := by rw [hθ0];exact RootCompletion.root_half_predictor i
    have hp : (0:ℝ)<rootZ.mulVec (θ 0) i := by rw [hv];norm_num
    have hu : rootZ.mulVec (θ 0) i<1 := by rw [hv];norm_num
    exact (hc.eventually_const_lt hp).and (hc.eventually_lt_const hu)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (had.and hstat)
  refine ⟨θ,hθ0,⟨min r (1/16),lt_min hr (by norm_num),min_le_right _ _,?_⟩,htreat⟩
  intro ε hε
  have hεr : |ε|<r := lt_of_lt_of_le hε (min_le_left _ _)
  have hp := hball (show dist ε 0<r by simpa [Real.dist_eq] using hεr)
  have hεsmall : |ε|≤1/16 := le_trans hε.le (min_le_right _ _)
  exact ⟨hp.1,root_stationary_unique_max a ε ha hεsmall (θ ε) hp.1 hp.2⟩

theorem root_link_first_order_counterexample_completed :
    RootMLDerivative (1/16) (120/119) ∧ RootMLDerivative 0 1 ∧
    (∀ ε, |ε| ≤ 1/16 → fExpectation rootLaw (rootProbability (1/16) ε) = 1/4) ∧
    (∀ ε, |ε| ≤ 1/16 → populationOLS rootLaw rootZ (rootProbability (1/16) ε) 1 = ε) ∧
    (120/119 : ℝ) ≠ 1 := by
  refine ⟨?_,?_,fun ε hε=>(root_ols_arithmetic ε hε).1,fun ε hε=>(root_ols_arithmetic ε hε).2,by norm_num⟩
  · convert rootMLDerivative_actual (1/16) (Or.inr rfl) using 1 <;> norm_num
  · convert rootMLDerivative_actual 0 (Or.inl rfl) using 1 <;> norm_num

end
end AronowAudit.P015.RootMLCompletion

namespace AronowAudit.P015
noncomputable section
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P015-T7(c)–(e): the actual ML treatment derivative is 120/119, although
the mean-only recipe gives 1; the same outcome mean with a=0 gives derivative 1. -/
theorem root_link_first_order_counterexample :
    RootMLDerivative (1/16) (120/119) ∧ RootMLDerivative 0 1 ∧
    (∀ ε, |ε| ≤ 1/16 → fExpectation rootLaw (rootProbability (1/16) ε) = 1/4) ∧
    (∀ ε, |ε| ≤ 1/16 → populationOLS rootLaw rootZ (rootProbability (1/16) ε) 1 = ε) ∧
    (120/119 : ℝ) ≠ 1 := by
  exact RootMLCompletion.root_link_first_order_counterexample_completed

end
end AronowAudit.P015

namespace AronowAudit.P015.ActualOLSCompletion
noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators Topology
open ConvergenceCompletion OLSCompletion
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

lemma control_conditioning_measurable {Ω : Type*} [MeasurableSpace Ω] {K:ℕ}
    (X:Ω→Fin K→ℝ) (j:Fin (K+1)) :
    Measurable[MeasurableSpace.comap X inferInstance] (fun s=>controlRow (X s) j) := by
  have hX : Measurable[MeasurableSpace.comap X inferInstance] X:=measurable_iff_comap_le.mpr le_rfl
  refine Fin.cases ?_ (fun k=>?_) j
  · simp [controlRow]
  · simpa [controlRow,Function.comp_def] using (measurable_pi_apply k).comp hX

lemma omegaHat_limit {Ω : Type*} [MeasurableSpace Ω] (P:Measure Ω) [IsProbabilityMeasure P]
    (K:ℕ) (D:ℕ→Ω→ℝ) (X:ℕ→Ω→Fin K→ℝ) (hX:Measurable (X 0))
    (ω:Fin (K+1)→ℝ)
    (hlinear:P[D 0|MeasurableSpace.comap (X 0) inferInstance]=ᵐ[P] fun s=>dotProduct (controlRow (X 0 s)) ω)
    (hVV:∀j k,MomentLLN P (fun i s=>controlRow (X i s) j*controlRow (X i s) k))
    (hVD:∀j,MomentLLN P (fun i s=>controlRow (X i s) j*D i s))
    (hdet:Matrix.det (fun j k=>∫s,controlRow (X 0 s) j*controlRow (X 0 s) k∂P)≠0) :
    ∀j,TendstoInMeasure P (fun n s=>omegaHat D X n s j) atTop (fun _=>ω j) := by
  let G:Matrix (Fin (K+1)) (Fin (K+1)) ℝ:=fun j k=>∫s,controlRow (X 0 s) j*controlRow (X 0 s) k∂P
  let b:Fin (K+1)→ℝ:=fun j=>∫s,controlRow (X 0 s) j*D 0 s∂P
  have hiD:Integrable (D 0) P:=by simpa [controlRow] using (hVD 0).1 0
  have he:G.mulVec ω=b:=projection_population_equations P (X 0) hX
    (fun s=>controlRow (X 0 s)) (control_conditioning_measurable (X 0))
    (D 0) hiD ω hlinear (fun j=>(hVD j).1 0) (fun j k=>(hVV j k).1 0)
  have hinv:G⁻¹.mulVec b=ω:=by
    rw [←he,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)]
    simp
  have h:=ols_moment_limit P (fun i s=>controlRow (X i s)) D G b hdet
    (fun j k=>(hVV j k).2) (fun j=>(hVD j).2)
  intro j
  change TendstoInMeasure P (fun n s => ols (fun i : Fin n => controlRow (X i s))
    (fun i => D i s) j) atTop (fun _ => ω j)
  simpa only [hinv] using h j

theorem effective_covariate_mean_limit_completed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Z : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : ∀ i, Measurable (D i)) (hZ : ∀ i, Measurable (Z i)) (hX : ∀ i, Measurable (X i))
    (hiid : iIndepFun (fun i s => (D i s,Z i s,X i s)) P)
    (hident : ∀ i, IdentDistrib (fun s => (D i s,Z i s,X i s)) (fun s => (D 0 s,Z 0 s,X 0 s)) P P)
    (ω : Fin (K+1) → ℝ)
    (hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlRow (X 0 s)) ω)
    (hreg : CovariateRegularity P D Z X ω) :
    TendstoInMeasure P (fun n s =>
      (∑ i : Fin n, residualHat D X n s i^2*Z i s)/(∑ i : Fin n, residualHat D X n s i^2))
      atTop (fun _ => (∫ s, populationWeight P (D 0) (X 0) s*Z 0 s ∂P)/
        (∫ s, populationWeight P (D 0) (X 0) s ∂P)) := by
  rcases hreg with ⟨hVV,hVD,hr2Z,hr2,hrZV,hrV,hZVV,hdet,hpos⟩
  let V:ℕ→Ω→Fin (K+1)→ℝ:=fun i s=>controlRow (X i s)
  let r:ℕ→Ω→ℝ:=fun i s=>D i s-dotProduct (V i s) ω
  let Δ:ℕ→Ω→Fin (K+1)→ℝ:=fun n s j=>omegaHat D X n s j-ω j
  have hΩ:=omegaHat_limit P K D X (hX 0) ω hlinear hVV hVD hdet
  have hΔ:∀j,TendstoInMeasure P (fun n s=>Δ n s j) atTop (fun _=>0):=by
    intro j
    simpa [Δ] using sub_limit P (hΩ j) (constant_limit P (ω j))
  have hrhat(n:ℕ)(s:Ω)(i:Fin n):residualHat D X n s i=
      r i s-Matrix.mulVec (fun i:Fin n=>V i s) (Δ n s) i:=by
    change D i s-(∑j,V i s j*omegaHat D X n s j)=
      (D i s-∑j,V i s j*ω j)-∑j,V i s j*(omegaHat D X n s j-ω j)
    simp only [mul_sub,Finset.sum_sub_distrib]
    ring
  have hN:=weighted_perturbation_limit P r Z V Δ
    (∫s,r 0 s^2*Z 0 s∂P)
    (fun j=>∫s,r 0 s*Z 0 s*V 0 s j∂P)
    (fun j k=>∫s,Z 0 s*V 0 s j*V 0 s k∂P)
    hΔ hr2Z.2 (fun j=>(hrZV j).2) (fun j k=>(hZVV j k).2)
  have hD0:=weighted_perturbation_limit P r (fun _ _=>1) V Δ
    (∫s,r 0 s^2∂P)
    (fun j=>∫s,r 0 s*V 0 s j∂P)
    (fun j k=>∫s,V 0 s j*V 0 s k∂P)
    hΔ (by simpa using hr2.2) (fun j=>by simpa using (hrV j).2)
    (fun j k=>by simpa using (hVV j k).2)
  have hNum:TendstoInMeasure P (fun n s=>(∑i:Fin n,residualHat D X n s i^2*Z i s)/(n:ℝ))
      atTop (fun _=>∫s,r 0 s^2*Z 0 s∂P):=by
    apply TendstoInMeasure.congr_left (fun n=>Eventually.of_forall (fun s=>?_)) hN
    simp_rw [hrhat]
  have hDen:TendstoInMeasure P (fun n s=>(∑i:Fin n,residualHat D X n s i^2)/(n:ℝ))
      atTop (fun _=>∫s,r 0 s^2∂P):=by
    apply TendstoInMeasure.congr_left (fun n=>Eventually.of_forall (fun s=>?_)) hD0
    simp only [mul_one]
    simp_rw [hrhat]
  have hRatio:=div_limit P hNum hDen hpos.ne'
  have he:∀ᶠn:ℕ in atTop,(fun s=>((∑i:Fin n,residualHat D X n s i^2*Z i s)/(n:ℝ))/
      ((∑i:Fin n,residualHat D X n s i^2)/(n:ℝ)))=ᵐ[P]
      fun s=>(∑i:Fin n,residualHat D X n s i^2*Z i s)/(∑i:Fin n,residualHat D X n s i^2):=by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact Eventually.of_forall (fun s=>div_div_div_cancel_right₀ (by exact_mod_cast (by omega:n≠0)) _ _)
  have hActual:=TendstoInMeasure.congr' he EventuallyEq.rfl hRatio
  have hw:populationWeight P (D 0) (X 0)=ᵐ[P] fun s=>r 0 s^2:=by
    filter_upwards [hlinear] with s hs
    simp [populationWeight,r,V,hs]
  have hEW:(∫s,populationWeight P (D 0) (X 0) s∂P)=(∫s,r 0 s^2∂P):=integral_congr_ae hw
  have hEWZ:(∫s,populationWeight P (D 0) (X 0) s*Z 0 s∂P)=(∫s,r 0 s^2*Z 0 s∂P):=by
    apply integral_congr_ae
    filter_upwards [hw] with s hs
    rw [hs]
  rw [←hEWZ,←hEW] at hActual
  exact hActual

end
end AronowAudit.P015.ActualOLSCompletion

namespace AronowAudit.P015.WeightedOLSCompletion
noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators Topology
open ConvergenceCompletion OLSCompletion PopulationMomentCompletion
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

def treatmentLastEquiv (K : ℕ) : (Fin (K+1) ⊕ Unit) ≃ Fin (K+2) :=
  ((finSuccEquiv' (1 : Fin (K+2))).trans (Equiv.optionEquivSumPUnit (Fin (K+1)))).symm

lemma treatmentLastEquiv_right (K : ℕ) : treatmentLastEquiv K (Sum.inr ())=1 := rfl

lemma regressor_reindex {K : ℕ} (d : ℝ) (x : Fin K → ℝ) :
    regressorRow d x ∘ treatmentLastEquiv K = Sum.elim (controlRow x) (fun _ : Unit => d) := by
  funext j
  rcases j with j | u
  · refine Fin.cases ?_ (fun k=>?_) j
    · simp [treatmentLastEquiv, regressorRow, controlRow, Fin.succAbove]
    · simp [treatmentLastEquiv, regressorRow, controlRow, Fin.succAbove]
  · cases u
    change regressorRow d x (Fin.succ (0 : Fin (K+1)))=d
    rfl

lemma betaHat_reindex {Ω : Type*} {K : ℕ} (D Y₀ τ : ℕ → Ω → ℝ)
    (X : ℕ → Ω → Fin K → ℝ) (n : ℕ) (s : Ω) :
    betaHat D Y₀ τ X n s =
      ols (fun i : Fin n => Sum.elim (controlRow (X i s)) (fun _ : Unit => D i s))
        (fun i => affineOutcome (Y₀ i s) (τ i s) (D i s)) (Sum.inr ()) := by
  have h := congrFun (ols_reindex (designW D X n s)
    (fun i => affineOutcome (Y₀ i s) (τ i s) (D i s)) (treatmentLastEquiv K)) (Sum.inr ())
  have he : (designW D X n s).submatrix id (treatmentLastEquiv K) =
      fun i : Fin n => Sum.elim (controlRow (X i s)) (fun _ : Unit => D i s) := by
    ext i j
    exact congrFun (regressor_reindex (D i s) (X i s)) j
  rw [he] at h
  simpa [Function.comp_def,treatmentLastEquiv_right,betaHat] using h.symm

lemma momentLLN_add {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z W : ℕ → Ω → ℝ) (hZ : MomentLLN P Z) (hW : MomentLLN P W) :
    MomentLLN P (fun i s => Z i s+W i s) := by
  refine ⟨fun i => (hZ.1 i).add (hW.1 i), ?_⟩
  have h := add_limit P hZ.2 hW.2
  simpa only [Finset.sum_add_distrib,add_div,integral_add (hZ.1 0) (hW.1 0)] using h

lemma momentLLN_congr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z W : ℕ → Ω → ℝ) (he : ∀ i s, Z i s=W i s) (hZ : MomentLLN P Z) :
    MomentLLN P W := by
  have h : Z=W := by funext i s; exact he i s
  rwa [←h]

lemma sum_design_moments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : ℕ) (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hreg : OLSRegularity P D Y₀ τ X) :
    let W : ℕ → Ω → (Fin (K+1) ⊕ Unit) → ℝ := fun i s =>
      Sum.elim (controlRow (X i s)) (fun _ => D i s)
    (∀ j k, MomentLLN P (fun i s => W i s j*W i s k)) ∧
      (∀ j, MomentLLN P (fun i s => W i s j*affineOutcome (Y₀ i s) (τ i s) (D i s))) := by
  rcases hreg with ⟨hVV,hVD,hD2,hDY,hVY,hD2T,hVDT,hVVT,hdet,hiw,hw⟩
  dsimp only
  constructor
  · intro j k
    rcases j with j | u <;> rcases k with k | v
    · exact hVV j k
    · exact hVD j
    · exact momentLLN_congr P _ _ (fun i s => mul_comm _ _) (hVD k)
    · exact momentLLN_congr P _ _ (fun i s => pow_two _) hD2
  · intro j
    rcases j with j | u
    · apply momentLLN_congr P _ _ (fun i s => ?_) (momentLLN_add P _ _ (hVY j) (hVDT j))
      simp only [affineOutcome,Sum.elim_inl]
      ring
    · apply momentLLN_congr P _ _ (fun i s => ?_) (momentLLN_add P _ _ hDY hD2T)
      simp only [affineOutcome,Sum.elim_inr]
      ring


lemma control_measurable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (X : Ω → Fin K → ℝ) (j : Fin (K+1)) :
    Measurable[MeasurableSpace.comap X inferInstance] (fun s => controlRow (X s) j) := by
  have hX : Measurable[MeasurableSpace.comap X inferInstance] X :=
    measurable_iff_comap_le.mpr le_rfl
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa [controlRow] using (measurable_const : Measurable[MeasurableSpace.comap X inferInstance]
      (fun _ : Ω => (1 : ℝ)))
  · simpa [controlRow,Function.comp_def] using (measurable_pi_apply k).comp hX

/-- T22 population identities (15) and the unnumbered residual-effect
display, pp. 262–263. These require unconfoundedness as well as a linear
treatment mean. -/
lemma population_ols_identification {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : Measurable (D 0)) (hY : Measurable (Y₀ 0))
    (hτ : Measurable (τ 0)) (hX : Measurable (X 0))
    (hunconf : CondIndepFun (MeasurableSpace.comap (X 0) inferInstance)
      (Measurable.comap_le hX) (fun s => (Y₀ 0 s,τ 0 s)) (D 0) P)
    (ω : Fin (K+1) → ℝ)
    (hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlRow (X 0 s)) ω)
    (hreg : OLSRegularity P D Y₀ τ X) :
    let W : Ω → (Fin (K+1) ⊕ Unit) → ℝ := fun s =>
      Sum.elim (controlRow (X 0 s)) (fun _ => D 0 s)
    let G : Matrix (Fin (K+1) ⊕ Unit) (Fin (K+1) ⊕ Unit) ℝ :=
      fun j k => ∫ s, W s j*W s k ∂P
    let c := fun j => ∫ s, W s j*affineOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P
    G.det ≠ 0 ∧ G⁻¹.mulVec c (Sum.inr ()) =
      (∫ s, populationWeight P (D 0) (X 0) s*τ 0 s ∂P)/
        (∫ s, populationWeight P (D 0) (X 0) s ∂P) := by
  rcases hreg with ⟨hVV,hVD,hD2,hDY,hVY,hD2T,hVDT,hVVT,hdet,hiw,hw⟩
  let V : Ω → Fin (K+1) → ℝ := fun s => controlRow (X 0 s)
  let M : Ω → ℝ := fun s => dotProduct (V s) ω
  let A : Matrix (Fin (K+1)) (Fin (K+1)) ℝ := fun j k => ∫ s, V s j*V s k ∂P
  let b : Fin (K+1) → ℝ := fun j => ∫ s, V s j*D 0 s ∂P
  let d : ℝ := ∫ s, D 0 s^2 ∂P
  let W : Ω → (Fin (K+1) ⊕ Unit) → ℝ := fun s => Sum.elim (V s) (fun _ => D 0 s)
  let G : Matrix (Fin (K+1) ⊕ Unit) (Fin (K+1) ⊕ Unit) ℝ := fun j k => ∫ s, W s j*W s k ∂P
  let c : (Fin (K+1) ⊕ Unit) → ℝ := fun j => ∫ s, W s j*affineOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P
  change G.det ≠ 0 ∧ _
  have hiD : Integrable (D 0) P := by simpa [controlRow] using (hVD 0).1 0
  have hiY : Integrable (Y₀ 0) P := by simpa [controlRow] using (hVY 0).1 0
  have hiT : Integrable (τ 0) P := by simpa [controlRow] using (hVVT 0 0).1 0
  have hiDT : Integrable (fun s => D 0 s*τ 0 s) P := by simpa [controlRow] using (hVDT 0).1 0
  have hiVT : ∀ j, Integrable (fun s => V s j*τ 0 s) P := by
    intro j
    simpa [V,controlRow] using (hVVT j 0).1 0
  have hiMY := linear_mul_integrable P V ω (Y₀ 0) (fun j => (hVY j).1 0)
  have hiMT := linear_mul_integrable P V ω (τ 0) hiVT
  have hiRT : Integrable (fun s => (D 0 s-M s)*τ 0 s) P :=
    (hiDT.sub hiMT).congr (Eventually.of_forall (fun s => by dsimp [M]; ring))
  have hiDMT := linear_mul_integrable P V ω (fun s => D 0 s*τ 0 s) (fun j =>
    ((hVDT j).1 0).congr (Eventually.of_forall (fun s => by dsimp [V]; ring)))
  have hiMMT := linear_product_integrable P V ω (τ 0) (fun j k => (hVVT j k).1 0)
  have hiRMT : Integrable (fun s => (D 0 s-M s)*M s*τ 0 s) P :=
    (hiDMT.sub hiMMT).congr (Eventually.of_forall (fun s => by
      simp only [Pi.sub_apply]; dsimp [M]; ring))
  have hzero := unconfounded_zero_terms P K (D 0) (Y₀ 0) (τ 0) (X 0) hX hD hY hτ
    hunconf ω hlinear hiD hiY hiT (hDY.1 0) hiMY hiRT hiRMT
  have hproj : A.mulVec ω=b := projection_population_equations P (X 0) hX V
    (control_measurable (X 0)) (D 0) hiD ω hlinear
    (fun j => (hVD j).1 0) (fun j k => (hVV j k).1 0)
  have hsym : ∀ j k, A j k=A k j := by
    intro j k
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => mul_comm _ _)
  have hquad : (∑ j, ∑ k, ω j*ω k*A j k)=dotProduct ω (A.mulVec ω) := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hwr : populationWeight P (D 0) (X 0) =ᵐ[P] fun s => (D 0 s-M s)^2 := by
    filter_upwards [hlinear] with s hs
    simp only [populationWeight,hs,M,V]
  have hEW : (∫ s, populationWeight P (D 0) (X 0) s ∂P)=
      d-dotProduct ω (A.mulVec ω) := by
    rw [integral_congr_ae hwr]
    have h := integral_residual_sq P V ω (D 0) (fun _ => 1)
      (by simpa using hD2.1 0) (fun j => by simpa using (hVD j).1 0)
      (fun j k => by simpa using (hVV j k).1 0)
    simp only [mul_one] at h
    change (∫ s, (D 0 s-M s)^2 ∂P)=d-2*dotProduct ω b+
      (∑ j, ∑ k, ω j*ω k*A j k) at h
    rw [hquad,←hproj] at h
    dsimp only [M]
    rw [h]
    ring
  have hs : 0<d-dotProduct ω (A.mulVec ω) := by rwa [hEW] at hw
  have hblock := SchurCompletion.block_ols_coefficient A hsym hdet ω d hs
  let B := Matrix.fromBlocks A (Matrix.replicateCol Unit (A.mulVec ω))
    (Matrix.replicateRow Unit (A.mulVec ω)) (fun (_ _ : Unit) => d)
  have hGB : G=B := by
    ext j k
    rcases j with j | u <;> rcases k with k | v
    · rfl
    · change b j=A.mulVec ω j
      exact (congrFun hproj j).symm
    · change (∫ s, D 0 s*V s k ∂P)=A.mulVec ω k
      rw [congrFun hproj k]
      exact integral_congr_ae (Eventually.of_forall (fun s => mul_comm _ _))
    · apply integral_congr_ae
      exact Eventually.of_forall (fun s => (pow_two _).symm)
  have hcV : ∀ j, c (Sum.inl j)=(∫ s, V s j*Y₀ 0 s ∂P)+(∫ s, V s j*D 0 s*τ 0 s ∂P) := by
    intro j
    have he : (fun s => V s j*affineOutcome (Y₀ 0 s) (τ 0 s) (D 0 s)) =
        fun s => V s j*Y₀ 0 s+V s j*D 0 s*τ 0 s := by funext s; dsimp [affineOutcome]; ring
    change (∫ s, V s j*affineOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P)=_
    rw [he,integral_add ((hVY j).1 0) ((hVDT j).1 0)]
  have hcD : c (Sum.inr ())=(∫ s, D 0 s*Y₀ 0 s ∂P)+(∫ s, D 0 s^2*τ 0 s ∂P) := by
    have he : (fun s => D 0 s*affineOutcome (Y₀ 0 s) (τ 0 s) (D 0 s)) =
        fun s => D 0 s*Y₀ 0 s+D 0 s^2*τ 0 s := by funext s; dsimp [affineOutcome]; ring
    change (∫ s, D 0 s*affineOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P)=_
    rw [he,integral_add (hDY.1 0) (hD2T.1 0)]
  have hvc : dotProduct ω (fun j => c (Sum.inl j))=
      (∫ s, M s*Y₀ 0 s ∂P)+(∫ s, M s*(D 0 s*τ 0 s) ∂P) := by
    simp_rw [hcV]
    change dotProduct ω ((fun j => ∫ s, V s j*Y₀ 0 s ∂P)+
      (fun j => ∫ s, V s j*D 0 s*τ 0 s ∂P))=_
    rw [dotProduct_add,integral_linear_mul P V ω (Y₀ 0) (fun j => (hVY j).1 0)]
    rw [integral_linear_mul P V ω (fun s => D 0 s*τ 0 s) (fun j =>
      ((hVDT j).1 0).congr (Eventually.of_forall (fun s => by dsimp [V]; ring)))]
    simp only [M,mul_assoc]
  have hmix : (∫ s, M s*(D 0 s*τ 0 s) ∂P)-
      (∫ s, M s*M s*τ 0 s ∂P)=0 := by
    have h := integral_sub hiDMT hiMMT
    change (∫ s, M s*(D 0 s*τ 0 s)-M s*M s*τ 0 s ∂P)=_ at h
    rw [←h]
    convert hzero.2.2.2 using 1
    congr 1
    funext s
    dsimp [M]
    ring
  have hR2T := integral_residual_sq P V ω (D 0) (τ 0) (hD2T.1 0)
    (fun j => (hVDT j).1 0) (fun j k => (hVVT j k).1 0)
  have hMDT := integral_linear_mul P V ω (fun s => D 0 s*τ 0 s) (fun j =>
    ((hVDT j).1 0).congr (Eventually.of_forall (fun s => by dsimp [V]; ring)))
  have hMMT := integral_linear_product P V ω (τ 0) (fun j k => (hVVT j k).1 0)
  have htarget : c (Sum.inr ())-dotProduct ω (fun j => c (Sum.inl j))=
      (∫ s, populationWeight P (D 0) (X 0) s*τ 0 s ∂P) := by
    have hwT : (∫ s, populationWeight P (D 0) (X 0) s*τ 0 s ∂P)=
        (∫ s, (D 0 s-M s)^2*τ 0 s ∂P) := by
      apply integral_congr_ae
      filter_upwards [hwr] with s hs
      rw [hs]
    rw [hwT,hcD,hvc]
    have hbase := hzero.2.2.1
    change (∫ s, D 0 s*Y₀ 0 s ∂P)-(∫ s, M s*Y₀ 0 s ∂P)=0 at hbase
    try simp only [mul_assoc] at hMDT
    change (∫ s, M s*(D 0 s*τ 0 s) ∂P)=_ at hMDT
    change (∫ s, M s*M s*τ 0 s ∂P)=_ at hMMT
    change (∫ s, (D 0 s-M s)^2*τ 0 s ∂P)=_ at hR2T
    simp only [mul_assoc] at hbase hmix hR2T hMDT hMMT ⊢
    linarith [hbase,hmix,hR2T,hMDT,hMMT]
  refine ⟨by simpa only [hGB] using hblock.1, ?_⟩
  have hc : c=Sum.elim (fun j => c (Sum.inl j)) (fun _ : Unit => c (Sum.inr ())) := by
    funext j
    rcases j with j | u
    · rfl
    · cases u; rfl
  change G⁻¹.mulVec c (Sum.inr ())=_
  rw [hGB,hc]
  rw [hblock.2 (fun j => c (Sum.inl j)) (c (Sum.inr ())), htarget, ←hEW]

theorem ols_weighted_effect_limit_completed {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : ∀ i, Measurable (D i)) (hY : ∀ i, Measurable (Y₀ i))
    (hτ : ∀ i, Measurable (τ i)) (hX : ∀ i, Measurable (X i))
    (hiid : iIndepFun (fun i s => (D i s,Y₀ i s,τ i s,X i s)) P)
    (hident : ∀ i, IdentDistrib (fun s => (D i s,Y₀ i s,τ i s,X i s))
      (fun s => (D 0 s,Y₀ 0 s,τ 0 s,X 0 s)) P P)
    (hunconf : CondIndepFun (MeasurableSpace.comap (X 0) inferInstance)
      (Measurable.comap_le (hX 0)) (fun s => (Y₀ 0 s,τ 0 s)) (D 0) P)
    (ω : Fin (K+1) → ℝ)
    (hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlRow (X 0 s)) ω)
    (hreg : OLSRegularity P D Y₀ τ X) :
    TendstoInMeasure P (betaHat D Y₀ τ X) atTop
      (fun _ => (∫ s, populationWeight P (D 0) (X 0) s*τ 0 s ∂P)/
        (∫ s, populationWeight P (D 0) (X 0) s ∂P)) := by
  let W : ℕ → Ω → (Fin (K+1) ⊕ Unit) → ℝ := fun i s =>
    Sum.elim (controlRow (X i s)) (fun _ => D i s)
  let G : Matrix (Fin (K+1) ⊕ Unit) (Fin (K+1) ⊕ Unit) ℝ :=
    fun j k => ∫ s, W 0 s j*W 0 s k ∂P
  let c : (Fin (K+1) ⊕ Unit) → ℝ :=
    fun j => ∫ s, W 0 s j*affineOutcome (Y₀ 0 s) (τ 0 s) (D 0 s) ∂P
  have hm := sum_design_moments P K D Y₀ τ X hreg
  have hp := population_ols_identification P K D Y₀ τ X (hD 0) (hY 0) (hτ 0) (hX 0)
    hunconf ω hlinear hreg
  change G.det ≠ 0 ∧ G⁻¹.mulVec c (Sum.inr ()) = _ at hp
  have h := ols_moment_limit P W (fun i s => affineOutcome (Y₀ i s) (τ i s) (D i s))
    G c hp.1 (fun j k => (hm.1 j k).2) (fun j => (hm.2 j).2) (Sum.inr ())
  have hbeta : TendstoInMeasure P (betaHat D Y₀ τ X) atTop
      (fun _ => G⁻¹.mulVec c (Sum.inr ())) := by
    apply TendstoInMeasure.congr_left (fun n => Eventually.of_forall (fun s => ?_)) h
    exact (betaHat_reindex D Y₀ τ X n s).symm
  simpa only [hp.2] using hbeta

end
end AronowAudit.P015.WeightedOLSCompletion

namespace AronowAudit.P015.ProbabilityCompletion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
set_option backward.isDefEq.respectTransparency false

/-- The population cancellation under the paper's common random
assignment, using its conditional-mean weight. -/
theorem randomization_population_weight_cancels {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : Ω → ℝ) (X : Ω → Fin K → ℝ)
    (hD : Measurable D) (hY : Measurable Y₀) (hτ : Measurable τ) (hX : Measurable X)
    (hrandom : IndepFun D (fun s=>(Y₀ s,τ s,X s)) P)
    (h₂ : MemLp D 2 P) (hτi : Integrable τ P) (hpos : 0<variance D P) :
    (P[D|MeasurableSpace.comap X inferInstance]=ᵐ[P] fun _=>∫s,D s∂P) ∧
    (populationWeight P D X=ᵐ[P] fun s=>(D s-(∫t,D t∂P))^2) ∧
    (∫s,populationWeight P D X s*τ s∂P)=
      (∫s,populationWeight P D X s∂P)*(∫s,τ s∂P) ∧
    (∫s,populationWeight P D X s*τ s∂P)/(∫s,populationWeight P D X s∂P)=∫s,τ s∂P := by
  have hIX : IndepFun D X P:=by
    convert hrandom.comp measurable_id (measurable_snd.comp measurable_snd) using 1 <;> rfl
  have hIT : IndepFun D τ P:=by
    convert hrandom.comp measurable_id (measurable_fst.comp measurable_snd) using 1 <;> rfl
  have hDm : Measurable[MeasurableSpace.comap D inferInstance] D:=measurable_iff_comap_le.mpr le_rfl
  have hCE : P[D|MeasurableSpace.comap X inferInstance]=ᵐ[P] fun _=>∫s,D s∂P:=
    condExp_indep_eq hD.comap_le hX.comap_le hDm.stronglyMeasurable ((IndepFun_iff_Indep D X P).mp hIX)
  have hW : populationWeight P D X=ᵐ[P] fun s=>(D s-(∫t,D t∂P))^2:=by
    filter_upwards [hCE] with s hs
    simp [populationWeight,hs]
  have hWi : Integrable (fun s=>(D s-(∫t,D t∂P))^2) P:=(h₂.sub (memLp_const _)).integrable_sq
  have hpos' : 0<∫s,(D s-(∫t,D t∂P))^2∂P:=by
    simpa only [variance_eq_integral hD.aemeasurable] using hpos
  have hh:=randomization_weight_cancels P D τ hD hτ hIT (∫s,D s∂P) hWi hτi hpos'
  have hden:(∫s,populationWeight P D X s∂P)=(∫s,(D s-(∫t,D t∂P))^2∂P):=integral_congr_ae hW
  have hnum:(∫s,populationWeight P D X s*τ s∂P)=(∫s,(D s-(∫t,D t∂P))^2*τ s∂P):=by
    apply integral_congr_ae
    filter_upwards [hW] with s hs
    rw [hs]
  exact ⟨hCE,hW,by rw [hnum,hden];exact hh.1,by rw [hnum,hden];exact hh.2⟩
end
end AronowAudit.P015.ProbabilityCompletion

namespace AronowAudit.P015.RandomizedOLSCompletion
noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

theorem randomized_ols_limit_completed {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : ∀ i, Measurable (D i)) (hY : ∀ i, Measurable (Y₀ i))
    (hτ : ∀ i, Measurable (τ i)) (hX : ∀ i, Measurable (X i))
    (hiid : iIndepFun (fun i s => (D i s,Y₀ i s,τ i s,X i s)) P)
    (hident : ∀ i, IdentDistrib (fun s => (D i s,Y₀ i s,τ i s,X i s))
      (fun s => (D 0 s,Y₀ 0 s,τ 0 s,X 0 s)) P P)
    (hrandom : IndepFun (D 0) (fun s => (Y₀ 0 s,τ 0 s,X 0 s)) P)
    (hreg : OLSRegularity P D Y₀ τ X) :
    TendstoInMeasure P (betaHat D Y₀ τ X) atTop (fun _ => ∫ s, τ 0 s ∂P) := by
  have hreg' := hreg
  rcases hreg' with ⟨hVV,hVD,hD2,hDY,hVY,hD2T,hVDT,hVVT,hdet,hiw,hw⟩
  have hIX : IndepFun (D 0) (X 0) P := by
    convert hrandom.comp measurable_id (measurable_snd.comp measurable_snd) using 1 <;> rfl
  have hDm : Measurable[MeasurableSpace.comap (D 0) inferInstance] (D 0) :=
    measurable_iff_comap_le.mpr le_rfl
  have hCE : P[D 0|MeasurableSpace.comap (X 0) inferInstance]=ᵐ[P] fun _=>∫s,D 0 s∂P :=
    condExp_indep_eq (hD 0).comap_le (hX 0).comap_le hDm.stronglyMeasurable
      ((IndepFun_iff_Indep (D 0) (X 0) P).mp hIX)
  let ω : Fin (K+1) → ℝ := Fin.cases (∫s,D 0 s∂P) (fun _=>0)
  have hω : ∀s,dotProduct (controlRow (X 0 s)) ω=∫s,D 0 s∂P := by
    intro s
    simp [dotProduct,controlRow,ω,Fin.sum_univ_succ]
  have hlinear : P[D 0|MeasurableSpace.comap (X 0) inferInstance]=ᵐ[P]
      fun s=>dotProduct (controlRow (X 0 s)) ω := by
    filter_upwards [hCE] with s hs
    rw [hs,hω]
  have htwo : MemLp (D 0) 2 P := (memLp_two_iff_integrable_sq (hD 0).aestronglyMeasurable).2 (hD2.1 0)
  have hiτ : Integrable (τ 0) P := by simpa [controlRow] using (hVVT 0 0).1 0
  have hweight : populationWeight P (D 0) (X 0)=ᵐ[P]
      fun s=>(D 0 s-(∫t,D 0 t∂P))^2 := by
    filter_upwards [hCE] with s hs
    simp [populationWeight,hs]
  have hvar : 0<variance (D 0) P := by
    rw [variance_eq_integral (hD 0).aemeasurable,←integral_congr_ae hweight]
    exact hw
  have hcancel := ProbabilityCompletion.randomization_population_weight_cancels P K
    (D 0) (Y₀ 0) (τ 0) (X 0) (hD 0) (hY 0) (hτ 0) (hX 0) hrandom htwo hiτ hvar
  have hRI : IndepFun (D 0) (fun s=>((Y₀ 0 s,τ 0 s),X 0 s)) P := by
    convert hrandom.comp measurable_id
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)) using 1 <;> rfl
  have hunconf : CondIndepFun (MeasurableSpace.comap (X 0) inferInstance)
      (Measurable.comap_le (hX 0)) (fun s=>(Y₀ 0 s,τ 0 s)) (D 0) P :=
    RandomizationKernelCompletion.condIndepFun_of_indep_joint P (D 0) (fun s=>(Y₀ 0 s,τ 0 s)) (X 0)
      (hD 0) ((hY 0).prodMk (hτ 0)) (hX 0) hRI
  have h := WeightedOLSCompletion.ols_weighted_effect_limit_completed P K D Y₀ τ X
    hD hY hτ hX hiid hident hunconf ω hlinear hreg
  simpa only [hcancel.2.2.2] using h

end
end AronowAudit.P015.RandomizedOLSCompletion

namespace AronowAudit.P015.RootPotentialCompletion
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped ENNReal BigOperators ProbabilityTheory Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable

lemma coe_nnReal (r : ℝ) : ((r.toNNReal : NNReal) : ENNReal)=ENNReal.ofReal r := rfl

def atomLaw : Measure (ℝ×ℝ) := ∑ i : Fin 6,(rootLaw i).toNNReal • Measure.dirac (rootX i,rootD i)
lemma atomLaw_probability : IsProbabilityMeasure atomLaw := by
  constructor
  norm_num [atomLaw,rootLaw,Fin.sum_univ_succ,Measure.add_apply,Measure.smul_apply,coe_nnReal,ENNReal.ofReal_div_of_pos,←mul_assoc]
  all_goals
    try dsimp only [Set.preimage]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    norm_num
    <;> first | rfl | ring

attribute [local instance] atomLaw_probability
lemma unit_eq_prod : rootUnitLaw=atomLaw.prod rootUniformLaw := by
  simp [atomLaw,rootUnitLaw,Fin.sum_univ_succ,Measure.add_prod,Measure.prod_smul_left]

lemma ae_unit {P : ((ℝ×ℝ)×ℝ) → Prop}
    (h : ∀ i : Fin 6,∀ᵐ u∂rootUniformLaw,P ((rootX i,rootD i),u)) : ∀ᵐ s∂rootUnitLaw,P s := by
  unfold rootUnitLaw
  rw [ae_finsetSum_measure_iff]
  intro i _
  apply Measure.ae_smul_measure
  rw [Measure.dirac_prod]
  exact (measurableEmbedding_prodMk_left (rootX i,rootD i)).ae_map_iff.mpr (h i)

lemma unit_apply (A : Set ((ℝ×ℝ)×ℝ)) (hA : MeasurableSet A) :
    rootUnitLaw A=∑i : Fin 6,((rootLaw i).toNNReal : ENNReal)*
      rootUniformLaw {u | ((rootX i,rootD i),u)∈A} := by
  unfold rootUnitLaw
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.smul_apply,Measure.dirac_prod,Measure.map_apply (by fun_prop) hA]
  rfl

lemma conditional_atom (i : Fin 6) : rootUnitLaw[|{s | s.1=(rootX i,rootD i)}]=
    (Measure.dirac (rootX i,rootD i)).prod rootUniformLaw := by
  ext A hA
  have hS : MeasurableSet {s : ((ℝ×ℝ)×ℝ) | s.1=(rootX i,rootD i)} :=
    measurable_fst (measurableSet_singleton _)
  rw [ProbabilityTheory.cond_apply hS,unit_apply _ (hS.inter hA),unit_apply _ hS]
  rw [Measure.dirac_prod,Measure.map_apply (by fun_prop) hA]
  fin_cases i <;> norm_num [rootLaw,rootX,rootD,Fin.sum_univ_succ,coe_nnReal,ENNReal.ofReal_div_of_pos,←mul_assoc]
  all_goals
    try dsimp only [Set.preimage]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    norm_num
    <;> first | rfl | ring

def dCell (x : ℝ) : Measure (ℝ×ℝ) :=
  (1-rootE x).toNNReal • Measure.dirac (x,0)+(rootE x).toNNReal • Measure.dirac (x,1)

lemma dCell_probability (x : ℝ) (hx : x∈({-1,0,1}:Finset ℝ)) : IsProbabilityMeasure (dCell x) := by
  constructor
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;>
    norm_num [dCell,rootE,Measure.add_apply,Measure.smul_apply,coe_nnReal,ENNReal.ofReal_div_of_pos,←mul_assoc]
  all_goals
    try dsimp only [Set.preimage]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    norm_num
    <;> first | rfl | ring

lemma conditional_X (x : ℝ) (hx : x∈({-1,0,1}:Finset ℝ)) :
    rootUnitLaw[|{s | rootUnitX s=x}]=(dCell x).prod rootUniformLaw := by
  ext A hA
  have hS : MeasurableSet {s | rootUnitX s=x} := measurable_fst.fst (measurableSet_singleton x)
  rw [ProbabilityTheory.cond_apply hS,unit_apply _ (hS.inter hA),unit_apply _ hS]
  simp only [dCell,Measure.add_prod,Measure.prod_smul_left,Measure.add_apply,Measure.smul_apply,Measure.dirac_prod]
  rw [Measure.map_apply (by fun_prop) hA,Measure.map_apply (by fun_prop) hA]
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;>
    norm_num [rootUnitX,rootLaw,rootX,rootD,rootE,Fin.sum_univ_succ,mul_add,coe_nnReal,ENNReal.ofReal_div_of_pos,←mul_assoc]
  all_goals
    have hsum1 : ((4:ENNReal)⁻¹+12⁻¹)⁻¹≠∞ := by simp
    have hsum2 : ((6:ENNReal)⁻¹+6⁻¹)⁻¹≠∞ := by simp
    have hsum3 : ((12:ENNReal)⁻¹+4⁻¹)⁻¹≠∞ := by simp
    try dsimp only [Set.preimage]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    norm_num
    <;> first | rfl | ring

lemma uniform_support : ∀ᵐ u∂rootUniformLaw,0≤u ∧ u≤1 := ae_restrict_mem measurableSet_Icc
lemma unit_support : ∀ᵐ s∂rootUnitLaw,
    (rootUnitX s= -1 ∨ rootUnitX s=0 ∨ rootUnitX s=1) ∧
    (rootUnitD s=0 ∨ rootUnitD s=1) ∧ (0≤rootUnitU s ∧ rootUnitU s≤1) := by
  apply ae_unit
  intro i
  filter_upwards [uniform_support] with u hu
  fin_cases i <;> norm_num [rootUnitX,rootUnitD,rootUnitU,rootX,rootD] <;> exact hu

lemma uniform_cdf (u : ℝ) (hu : 0≤u) (hu1 : u≤1) :
    rootUniformLaw {v | v≤u}=ENNReal.ofReal u := by
  change (volume.restrict (Icc (0:ℝ) 1)) (Iic u)=ENNReal.ofReal u
  rw [Measure.restrict_apply measurableSet_Iic]
  have he : Iic u∩Icc (0:ℝ) 1=Icc 0 u := by
    ext v
    constructor
    · rintro ⟨hvu,hv0,hv1⟩
      exact ⟨hv0,hvu⟩
    · rintro ⟨hv0,hvu⟩
      exact ⟨hvu,hv0,le_trans hvu hu1⟩
  rw [he]
  simp [Real.volume_Icc]

lemma unit_X_mass (x : ℝ) (hx : x∈({-1,0,1}:Finset ℝ)) :
    rootUnitLaw {s | rootUnitX s=x}=1/3 := by
  rw [unit_eq_prod]
  change (atomLaw.prod rootUniformLaw) (Prod.fst ⁻¹' {z : ℝ×ℝ | z.1=x})=1/3
  rw [← Measure.fst_apply (show MeasurableSet {z : ℝ×ℝ | z.1=x} from measurableSet_eq_fun measurable_fst measurable_const),Measure.fst_prod]
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;>
    norm_num [atomLaw,rootLaw,rootX,rootD,Fin.sum_univ_succ,Measure.add_apply,Measure.smul_apply,coe_nnReal,ENNReal.ofReal_div_of_pos,←mul_assoc]
  all_goals
    try dsimp only [Set.preimage]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    norm_num
    <;> first | rfl | ring

lemma unit_U_cdf (u : ℝ) (hu : 0≤u) (hu1 : u≤1) :
    rootUnitLaw {s | rootUnitU s≤u}=ENNReal.ofReal u := by
  rw [unit_eq_prod]
  change (atomLaw.prod rootUniformLaw) (Prod.snd ⁻¹' Iic u)=ENNReal.ofReal u
  rw [← Measure.snd_apply measurableSet_Iic,Measure.snd_prod]
  exact uniform_cdf u hu hu1

lemma unit_indep : IndepFun rootUnitU (fun s=>(rootUnitX s,rootUnitD s)) rootUnitLaw := by
  rw [unit_eq_prod]
  exact (indepFun_prod (μ:=atomLaw) (ν:=rootUniformLaw) measurable_id measurable_id).symm

lemma affine_observed (a ε : ℝ) : ∀ᵐ s∂rootUnitLaw,rootUnitY a ε (rootUnitD s) s=
    rootUnitY a ε 0 s+rootUnitTau a ε s*rootUnitD s := by
  filter_upwards [unit_support] with s hs
  rcases hs.2.1 with h | h <;> simp [h,rootUnitTau]

lemma potential_measurable_u (a ε x d : ℝ) : Measurable (fun u=>rootPotential a ε x u d) := by
  unfold rootPotential
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

lemma unitY_measurable (a ε : ℝ) (d : ((ℝ×ℝ)×ℝ) → ℝ) (hd : Measurable d) :
    Measurable (fun s=>rootUnitY a ε (d s) s) := by
  unfold rootUnitY rootPotential rootUnitX rootUnitU rootBaseline rootE
  apply Measurable.ite _ measurable_const measurable_const
  apply measurableSet_le measurable_snd
  fun_prop

lemma cell_X_support (x : ℝ) : ∀ᵐ s∂(dCell x).prod rootUniformLaw,rootUnitX s=x := by
  apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet {s : ((ℝ×ℝ)×ℝ) | rootUnitX s=x} from measurableSet_eq_fun measurable_fst.fst measurable_const)).mpr
  have hd : ∀ᵐ z∂dCell x,z.1=x := by
    unfold dCell
    rw [ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure <;> simp
  filter_upwards [hd] with z hz
  exact ae_of_all _ (fun _=>hz)

lemma cell_indep (a ε x : ℝ) (hx : x∈({-1,0,1}:Finset ℝ)) :
    IndepFun (fun s=>(rootUnitY a ε 0 s,rootUnitTau a ε s)) rootUnitD
      rootUnitLaw[|{s | rootUnitX s=x}] := by
  rw [conditional_X x hx]
  letI := dCell_probability x hx
  have hm : Measurable (fun u=>(rootPotential a ε x u 0,
      rootPotential a ε x u 1-rootPotential a ε x u 0)) :=
    (potential_measurable_u a ε x 0).prodMk
      ((potential_measurable_u a ε x 1).sub (potential_measurable_u a ε x 0))
  have hind := (indepFun_prod (μ:=dCell x) (ν:=rootUniformLaw) measurable_snd hm).symm
  apply hind.congr _ (ae_of_all _ (fun _=>rfl))
  filter_upwards [cell_X_support x] with s hs
  simp only [rootUnitY,rootUnitTau,rootUnitU]
  rw [hs]

lemma unit_condIndep (a ε : ℝ) : CondIndepFun (MeasurableSpace.comap rootUnitX inferInstance)
    (Measurable.comap_le (show Measurable rootUnitX from measurable_fst.fst))
    (fun s=>(rootUnitY a ε 0 s,rootUnitTau a ε s)) rootUnitD rootUnitLaw := by
  apply FiniteConditioning.condIndep_of_fiber_indep rootUnitLaw rootUnitX measurable_fst.fst
    ({-1,0,1}:Finset ℝ) _ _ _ _ measurable_fst.snd (cell_indep a ε)
  · filter_upwards [unit_support] with s hs
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hs.1
  · exact (unitY_measurable a ε (fun _=>0) measurable_const).prodMk
      ((unitY_measurable a ε (fun _=>1) measurable_const).sub
        (unitY_measurable a ε (fun _=>0) measurable_const))

lemma integrable_atom_D (x d : ℝ) :
    Integrable rootUnitD ((Measure.dirac (x,d)).prod rootUniformLaw) := by
  rw [Measure.dirac_prod]
  apply (integrable_map_measure measurable_fst.snd.aestronglyMeasurable
    (show Measurable (Prod.mk (x,d)) from measurable_const.prodMk measurable_id).aemeasurable).mpr
  change Integrable (fun _ : ℝ=>d) rootUniformLaw
  exact integrable_const d

lemma integral_atom_D (x d : ℝ) :
    (∫s,rootUnitD s∂(Measure.dirac (x,d)).prod rootUniformLaw)=d := by
  change (∫s,s.1.2∂(Measure.dirac (x,d)).prod rootUniformLaw)=d
  rw [Measure.dirac_prod,integral_map_of_stronglyMeasurable (by fun_prop) measurable_fst.snd.stronglyMeasurable]
  simp [rootUnitD]

lemma cell_D_mean (x : ℝ) (hx : x∈({-1,0,1}:Finset ℝ)) :
    (∫s,rootUnitD s∂rootUnitLaw[|{s | rootUnitX s=x}])=rootE x := by
  rw [conditional_X x hx]
  simp only [dCell,Measure.add_prod,Measure.prod_smul_left]
  rw [integral_add_measure (integrable_atom_D x 0).smul_measure_nnreal
    (integrable_atom_D x 1).smul_measure_nnreal]
  simp only [integral_smul_nnreal_measure,integral_atom_D,NNReal.smul_def,smul_eq_mul,mul_zero,zero_add,mul_one]
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> norm_num [rootE,Real.coe_toNNReal]

lemma unit_D_integrable : Integrable rootUnitD rootUnitLaw := by
  apply (integrable_const (1:ℝ)).mono' measurable_fst.snd.aestronglyMeasurable
  filter_upwards [unit_support] with s hs
  rcases hs.2.1 with h | h <;> change |rootUnitD s|≤1 <;> simp only [h] <;> norm_num

lemma unit_D_condExp : rootUnitLaw[rootUnitD | MeasurableSpace.comap rootUnitX inferInstance] =ᵐ[rootUnitLaw]
    (fun s=>rootE (rootUnitX s)) := by
  apply FiniteConditioning.condExp_eq_of_fiber_integrals rootUnitLaw rootUnitX measurable_fst.fst
    ({-1,0,1}:Finset ℝ) _ rootUnitD unit_D_integrable rootE cell_D_mean
  filter_upwards [unit_support] with s hs
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hs.1

lemma unitY_bounds (a ε d : ℝ) (s : ((ℝ×ℝ)×ℝ)) :
    0≤rootUnitY a ε d s ∧ rootUnitY a ε d s≤1 := by
  unfold rootUnitY rootPotential
  split_ifs <;> norm_num

lemma unitY_integrable (μ : Measure ((ℝ×ℝ)×ℝ)) [IsFiniteMeasure μ] (a ε : ℝ)
    (d : ((ℝ×ℝ)×ℝ) → ℝ) (hd : Measurable d) : Integrable (fun s=>rootUnitY a ε (d s) s) μ := by
  apply (integrable_const (1:ℝ)).mono' (unitY_measurable a ε d hd).aestronglyMeasurable
  apply ae_of_all
  intro s
  rw [Real.norm_eq_abs,abs_of_nonneg (unitY_bounds a ε (d s) s).1]
  exact (unitY_bounds a ε (d s) s).2

lemma atom_observed_mean (a ε : ℝ) (ha : a=0 ∨ a=1/16) (hε : |ε|≤1/16) (i : Fin 6) :
    (∫s,rootUnitY a ε (rootUnitD s) s∂(Measure.dirac (rootX i,rootD i)).prod rootUniformLaw)=rootProbability a ε i := by
  have hp : 0<rootProbability a ε i ∧ rootProbability a ε i<1 := by
    have he := abs_le.mp hε
    rcases ha with rfl | rfl <;> fin_cases i <;>
      norm_num [rootProbability,rootBaseline,rootX,rootD,rootE] <;> constructor <;>linarith
  rw [Measure.dirac_prod,integral_map_of_stronglyMeasurable (by fun_prop)
    (unitY_measurable a ε rootUnitD measurable_fst.snd).stronglyMeasurable]
  change (∫u,(Iic (rootProbability a ε i)).indicator (fun _=>(1:ℝ)) u∂rootUniformLaw)=rootProbability a ε i
  rw [integral_indicator_const (1:ℝ) measurableSet_Iic]
  simp only [Measure.real,smul_eq_mul,mul_one]
  change (rootUniformLaw {u | u≤rootProbability a ε i}).toReal=rootProbability a ε i
  rw [uniform_cdf _ hp.1.le hp.2.le,ENNReal.toReal_ofReal hp.1.le]

def pairSupport : Finset (ℝ×ℝ) := Finset.univ.image (fun i : Fin 6=>(rootX i,rootD i))
lemma pair_support : ∀ᵐ s∂rootUnitLaw,(rootUnitX s,rootUnitD s)∈pairSupport := by
  apply ae_unit
  intro i
  exact ae_of_all _ (fun _=>by exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)

lemma observed_condExp (a ε : ℝ) (ha : a=0 ∨ a=1/16) (hε : |ε|≤1/16) :
    rootUnitLaw[(fun s=>rootUnitY a ε (rootUnitD s) s) |
      MeasurableSpace.comap (fun s=>(rootUnitX s,rootUnitD s)) inferInstance] =ᵐ[rootUnitLaw]
        (fun s=>rootBaseline a (rootUnitX s)+ε*(rootUnitD s-rootE (rootUnitX s))) := by
  apply FiniteConditioning.condExp_eq_of_fiber_integrals rootUnitLaw
    (fun s=>(rootUnitX s,rootUnitD s)) measurable_fst pairSupport pair_support _
    (unitY_integrable rootUnitLaw a ε rootUnitD measurable_fst.snd)
    (fun z=>rootBaseline a z.1+ε*(z.2-rootE z.1))
  intro z hz
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
  rw [show {s | (rootUnitX s,rootUnitD s)=(rootX i,rootD i)}={s | s.1=(rootX i,rootD i)} from rfl,
    conditional_atom]
  exact atom_observed_mean a ε ha hε i

lemma observed_mean (a ε : ℝ) (ha : a=0 ∨ a=1/16) (hε : |ε|≤1/16) :
    (∫s,rootUnitY a ε (rootUnitD s) s∂rootUnitLaw)=1/4 := by
  unfold rootUnitLaw
  rw [integral_finsetSum_measure (fun i _=>(unitY_integrable _ a ε rootUnitD measurable_fst.snd).smul_measure_nnreal)]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul]
  simp_rw [atom_observed_mean a ε ha hε]
  have hc (i : Fin 6) : ((rootLaw i).toNNReal : ℝ)=rootLaw i := Real.coe_toNNReal _ (root_link_matrix_arithmetic.1.1 i)
  simp_rw [hc]
  norm_num [rootLaw,rootProbability,rootBaseline,rootX,rootD,rootE,Fin.sum_univ_succ]
  <;> ring

theorem root_potential_model_completed (a ε : ℝ) (ha : a=0 ∨ a=1/16) (hε : |ε|≤1/16) :
    (∀ x ∈ ({-1,0,1} : Finset ℝ), rootUnitLaw {s | rootUnitX s=x}=1/3) ∧
    (∀ᵐ s ∂rootUnitLaw, rootUnitD s=0 ∨ rootUnitD s=1) ∧
    (∀ᵐ s ∂rootUnitLaw, 0≤rootUnitU s ∧ rootUnitU s≤1) ∧
    (∀ u : ℝ, 0≤u → u≤1 →
      rootUnitLaw {s | rootUnitU s≤u}=ENNReal.ofReal u) ∧
    IndepFun rootUnitU (fun s => (rootUnitX s,rootUnitD s)) rootUnitLaw ∧
    CondIndepFun (MeasurableSpace.comap rootUnitX inferInstance)
      (Measurable.comap_le (show Measurable rootUnitX from measurable_fst.fst))
      (fun s => (rootUnitY a ε 0 s,rootUnitTau a ε s)) rootUnitD rootUnitLaw ∧
    rootUnitLaw[rootUnitD | MeasurableSpace.comap rootUnitX inferInstance] =ᵐ[rootUnitLaw]
      (fun s => rootE (rootUnitX s)) ∧
    (∀ᵐ s ∂rootUnitLaw, rootUnitY a ε (rootUnitD s) s=
      rootUnitY a ε 0 s+rootUnitTau a ε s*rootUnitD s) ∧
    rootUnitLaw[(fun s => rootUnitY a ε (rootUnitD s) s) |
      MeasurableSpace.comap (fun s => (rootUnitX s,rootUnitD s)) inferInstance] =ᵐ[rootUnitLaw]
      (fun s => rootBaseline a (rootUnitX s)+ε*(rootUnitD s-rootE (rootUnitX s))) ∧
    (∫ s, rootUnitY a ε (rootUnitD s) s ∂rootUnitLaw)=1/4 := by
  exact ⟨unit_X_mass,unit_support.mono (fun _ hs=>hs.2.1),unit_support.mono (fun _ hs=>hs.2.2),
    unit_U_cdf,unit_indep,unit_condIndep a ε,unit_D_condExp,affine_observed a ε,
    observed_condExp a ε ha hε,observed_mean a ε ha hε⟩


end
end AronowAudit.P015.RootPotentialCompletion

namespace AronowAudit.P015
noncomputable section
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P015-T23, Expression (9), pp. 255–256: the covariate mean with fitted
squared OLS residual weights converges in probability to E[wZ]/E[w]. -/
theorem effective_covariate_mean_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Z : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : ∀ i, Measurable (D i)) (hZ : ∀ i, Measurable (Z i)) (hX : ∀ i, Measurable (X i))
    (hiid : iIndepFun (fun i s => (D i s,Z i s,X i s)) P)
    (hident : ∀ i, IdentDistrib (fun s => (D i s,Z i s,X i s)) (fun s => (D 0 s,Z 0 s,X 0 s)) P P)
    (ω : Fin (K+1) → ℝ)
    (hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlRow (X 0 s)) ω)
    (hreg : CovariateRegularity P D Z X ω) :
    TendstoInMeasure P (fun n s =>
      (∑ i : Fin n, residualHat D X n s i^2*Z i s)/(∑ i : Fin n, residualHat D X n s i^2))
      atTop (fun _ => (∫ s, populationWeight P (D 0) (X 0) s*Z 0 s ∂P)/
        (∫ s, populationWeight P (D 0) (X 0) s ∂P)) := by
  exact ActualOLSCompletion.effective_covariate_mean_limit_completed (Ω := Ω) (P := P) (K := K) (D := D) (Z := Z) (X := X) (hD := hD) (hZ := hZ) (hX := hX) (hiid := hiid) (hident := hident) (ω := ω) (hlinear := hlinear) (hreg := hreg)

/-- Theorem A.1 (P015-T22) and the identical corrected Expression (7) (T15).
The three causal assumptions and the explicit moment/LLN/nonsingularity
conditions imply convergence in probability of the OLS coefficient. -/
theorem ols_weighted_effect_limit {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : ∀ i, Measurable (D i)) (hY : ∀ i, Measurable (Y₀ i))
    (hτ : ∀ i, Measurable (τ i)) (hX : ∀ i, Measurable (X i))
    (hiid : iIndepFun (fun i s => (D i s,Y₀ i s,τ i s,X i s)) P)
    (hident : ∀ i, IdentDistrib (fun s => (D i s,Y₀ i s,τ i s,X i s))
      (fun s => (D 0 s,Y₀ 0 s,τ 0 s,X 0 s)) P P)
    (hunconf : CondIndepFun (MeasurableSpace.comap (X 0) inferInstance)
      (Measurable.comap_le (hX 0)) (fun s => (Y₀ 0 s,τ 0 s)) (D 0) P)
    (ω : Fin (K+1) → ℝ)
    (hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlRow (X 0 s)) ω)
    (hreg : OLSRegularity P D Y₀ τ X) :
    TendstoInMeasure P (betaHat D Y₀ τ X) atTop
      (fun _ => (∫ s, populationWeight P (D 0) (X 0) s*τ 0 s ∂P)/
        (∫ s, populationWeight P (D 0) (X 0) s ∂P)) := by
  exact WeightedOLSCompletion.ols_weighted_effect_limit_completed (Ω := Ω) (P := P) (K := K) (D := D) (Y₀ := Y₀) (τ := τ) (X := X) (hD := hD) (hY := hY) (hτ := hτ) (hX := hX) (hiid := hiid) (hident := hident) (hunconf := hunconf) (ω := ω) (hlinear := hlinear) (hreg := hreg)

/-- P015-T24, Corollary A.1, p. 263: common-distribution treatment assignment
independent of baseline, effects and controls makes the actual OLS estimate converge
in probability to E[τ]. Unequal assignment probabilities are excluded as in footnote 15. -/
theorem randomized_ols_limit {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : ∀ i, Measurable (D i)) (hY : ∀ i, Measurable (Y₀ i))
    (hτ : ∀ i, Measurable (τ i)) (hX : ∀ i, Measurable (X i))
    (hiid : iIndepFun (fun i s => (D i s,Y₀ i s,τ i s,X i s)) P)
    (hident : ∀ i, IdentDistrib (fun s => (D i s,Y₀ i s,τ i s,X i s))
      (fun s => (D 0 s,Y₀ 0 s,τ 0 s,X 0 s)) P P)
    (hrandom : IndepFun (D 0) (fun s => (Y₀ 0 s,τ 0 s,X 0 s)) P)
    (hreg : OLSRegularity P D Y₀ τ X) :
    TendstoInMeasure P (betaHat D Y₀ τ X) atTop (fun _ => ∫ s, τ 0 s ∂P) := by
  exact RandomizedOLSCompletion.randomized_ols_limit_completed (Ω := Ω) (P := P) (K := K) (D := D) (Y₀ := Y₀) (τ := τ) (X := X) (hD := hD) (hY := hY) (hτ := hτ) (hX := hX) (hiid := hiid) (hident := hident) (hrandom := hrandom) (hreg := hreg)

/-- T7's complete standing hypotheses are stated for the fixed product
distribution: uniform X, binary D, uniform independent U, unconfoundedness,
affine observed outcomes, linear E[D|X], the exact Bernoulli success probability,
and the constant outcome mean 1/4. Both a=1/16 and a=0 models are included. -/
theorem root_potential_model (a ε : ℝ) (ha : a=0 ∨ a=1/16) (hε : |ε|≤1/16) :
    (∀ x ∈ ({-1,0,1} : Finset ℝ), rootUnitLaw {s | rootUnitX s=x}=1/3) ∧
    (∀ᵐ s ∂rootUnitLaw, rootUnitD s=0 ∨ rootUnitD s=1) ∧
    (∀ᵐ s ∂rootUnitLaw, 0≤rootUnitU s ∧ rootUnitU s≤1) ∧
    (∀ u : ℝ, 0≤u → u≤1 →
      rootUnitLaw {s | rootUnitU s≤u}=ENNReal.ofReal u) ∧
    IndepFun rootUnitU (fun s => (rootUnitX s,rootUnitD s)) rootUnitLaw ∧
    CondIndepFun (MeasurableSpace.comap rootUnitX inferInstance)
      (Measurable.comap_le (show Measurable rootUnitX from measurable_fst.fst))
      (fun s => (rootUnitY a ε 0 s,rootUnitTau a ε s)) rootUnitD rootUnitLaw ∧
    rootUnitLaw[rootUnitD | MeasurableSpace.comap rootUnitX inferInstance] =ᵐ[rootUnitLaw]
      (fun s => rootE (rootUnitX s)) ∧
    (∀ᵐ s ∂rootUnitLaw, rootUnitY a ε (rootUnitD s) s=
      rootUnitY a ε 0 s+rootUnitTau a ε s*rootUnitD s) ∧
    rootUnitLaw[(fun s => rootUnitY a ε (rootUnitD s) s) |
      MeasurableSpace.comap (fun s => (rootUnitX s,rootUnitD s)) inferInstance] =ᵐ[rootUnitLaw]
      (fun s => rootBaseline a (rootUnitX s)+ε*(rootUnitD s-rootE (rootUnitX s))) ∧
    (∫ s, rootUnitY a ε (rootUnitD s) s ∂rootUnitLaw)=1/4 := by
  exact RootPotentialCompletion.root_potential_model_completed (a := a) (ε := ε) (ha := ha) (hε := hε)

theorem RootLinkCounterexample_checked : RootLinkCounterexample := by
  exact ⟨@root_link_first_order_counterexample, @root_link_matrix_arithmetic, @root_ols_arithmetic, @root_uniform_is_probability, @root_unit_is_probability, @root_potential_model, @root_score_calculus⟩

theorem root_link_finite_core : RootLinkCounterexample := RootLinkCounterexample_checked

theorem root_population_core : RootLinkCounterexample := RootLinkCounterexample_checked

theorem root_uniform_probability : RootLinkCounterexample := RootLinkCounterexample_checked

theorem root_unit_probability : RootLinkCounterexample := RootLinkCounterexample_checked

end
end AronowAudit.P015

namespace AronowAudit.P015
noncomputable section
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem all_degree_taylor_counterexample :
    let L := Real.log 99
    (∀ θ : Fin 2 → ℝ, extremeLikelihood θ ≤ extremeLikelihood ![-L,2*L]) ∧
    (∀ θ : Fin 2 → ℝ, extremeLikelihood θ = extremeLikelihood ![-L,2*L] → θ = ![-L,2*L]) ∧
    logistic (-L) = 1/100 ∧ logistic L = 99/100 ∧
    logit ((1+99)/200) = 0 ∧ 9/2 < L ∧ Real.pi < 9/2 ∧
    (∀ N : ℕ, 49/100 ≤ |logisticTaylor N 0 L-logistic L| ∧
      49/100 ≤ |logisticTaylor N 0 (-L)-logistic (-L)| ∧
      49 ≤ |100*(99/100-logisticTaylor N 0 L)|) := by
  dsimp only
  have hfit : logistic (Real.log 99)=99/100 := extreme_sigmoid_arithmetic.1
  have hfit' : Real.sigmoid (Real.log 99)=99/100 := hfit
  refine ⟨extreme_unique_mle.1,extreme_unique_mle.2,extreme_sigmoid_arithmetic.2.1,
    hfit,extreme_sigmoid_arithmetic.2.2.1,log99_lower_bound,?_,?_⟩
  · linarith [Real.pi_lt_four]
  · intro N
    have hp := LogisticTaylorCompletion.all_degree_error log99_lower_bound.le hfit' N
    have hn := LogisticTaylorCompletion.all_degree_negative_error log99_lower_bound.le hfit' N
    refine ⟨hp,hn,?_⟩
    have hpp : (49:ℝ)/100≤|logisticTaylor N 0 (Real.log 99)-99/100| := by
      simpa only [logisticTaylor,logistic,hfit'] using hp
    calc
      (49:ℝ)=100*(49/100) := by norm_num
      _ ≤ 100*|logisticTaylor N 0 (Real.log 99)-99/100| := by gcongr
      _ = |100*(99/100-logisticTaylor N 0 (Real.log 99))| := by
        rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<100),abs_sub_comm]

theorem TaylorCounterexample_checked : TaylorCounterexample := by
  exact ⟨@all_degree_taylor_counterexample, @logistic_power_series_radius, @extreme_grouped_data_arithmetic, @extreme_sigmoid_arithmetic, @log99_lower_bound⟩

theorem extreme_logistic_values : TaylorCounterexample := TaylorCounterexample_checked

theorem extreme_predictor_large : TaylorCounterexample := TaylorCounterexample_checked

theorem logistic_radius_zero : TaylorCounterexample := TaylorCounterexample_checked

theorem extreme_data_properties : TaylorCounterexample := TaylorCounterexample_checked

end
end AronowAudit.P015

