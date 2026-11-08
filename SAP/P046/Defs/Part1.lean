import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

def bit (b : Bool) : ℝ := if b then 1 else 0

/-- A full-data unit consists of W, X, Y(0), Y(1). The paper observes only
(W,Y,X), Section 2, p. 5: "an i.i.d. sample (W_i,Y_i,X_i)". -/
abbrev Unit := ℝ × (Bool × (Bool × Bool))
/-- "W_i is the covariate", Section 2, p. 5. -/
def W (o : Unit) : ℝ := o.1
/-- "X_i is the treatment", Section 2, p. 5, binary coded as zero or one. -/
def X (o : Unit) : ℝ := bit o.2.1
/-- The untreated potential outcome Y_i(0), consistency display on p. 5. -/
def Y0 (o : Unit) : ℝ := bit o.2.2.1
/-- The treated potential outcome Y_i(1), estimand display on p. 5. -/
def Y1 (o : Unit) : ℝ := bit o.2.2.2

/-- Consistency, p. 5: "Y_i = (1-X_i)Y_i(0) + X_iY_i(1)". -/
def Y (o : Unit) : ℝ := (1 - X o) * Y0 o + X o * Y1 o

/-- The observed triple, p. 5: "(W_i,Y_i,X_i)". Estimators of Proposition 1
receive this triple, never the potential outcomes or the unknown propensity. -/
abbrev Observed := ℝ × (ℝ × ℝ)
/-- The observed sample triple "(W_i,Y_i,X_i)", p. 5. -/
def observe (o : Unit) : Observed := (W o, (Y o, X o))

/-- Conditioning on the observed covariate W_i, p. 5 unconfoundedness display. -/
def covariateSigma : MeasurableSpace Unit := MeasurableSpace.comap W inferInstance

/-- A candidate population law with a supplied version of pi and m. Section 2,
p. 5: "pi(w) = Pr(X_i=1|W_i=w)", "mu = E[Y_i(1)]"; m is the
regression "E[Y_i(1)|W_i=w]" written out on p. 7. ValidStudy supplies precisely
the probability, continuity, positivity and conditional independence conditions. -/
structure Study where
  law : Measure Unit
  pi : ℝ → ℝ
  m : ℝ → ℝ
  delta : ℝ

/-- The standing assumptions on p. 5. Continuity means an atomless W marginal.
The stored regression is a measurable version of the conditional mean. Its
[0,1] bound follows mathematically from the binary potential outcome; storing
that bound specifies a version and does not require a correct working regression.
Unconfoundedness is imposed separately for each potential outcome, not jointly. -/
structure ValidStudy (M : Study) : Prop where
  probability : IsProbabilityMeasure M.law
  continuous : ∀ w : ℝ, M.law {o | W o = w} = 0
  measurable_pi : Measurable M.pi
  measurable_m : Measurable M.m
  delta_pos : 0 < M.delta
  positivity : ∀ᵐ o ∂M.law, M.delta < M.pi (W o) ∧ M.pi (W o) < 1 - M.delta
  propensity : condExp covariateSigma M.law X =ᵐ[M.law] fun o => M.pi (W o)
  regression : condExp covariateSigma M.law Y1 =ᵐ[M.law] fun o => M.m (W o)
  regression_range : ∀ᵐ o ∂M.law, 0 ≤ M.m (W o) ∧ M.m (W o) ≤ 1
  unconfounded0 : letI := probability
    CondIndepFun covariateSigma (by exact measurable_fst.comap_le) Y0 X M.law
  unconfounded1 : letI := probability
    CondIndepFun covariateSigma (by exact measurable_fst.comap_le) Y1 X M.law

/-- "mu = E[Y_i(1)]", p. 5. This is the population mean, never a
covariate-conditional or finite-population target. -/
def mu (M : Study) : ℝ := ∫ o, Y1 o ∂M.law

/-- The i.i.d. sample of size n, p. 5 and footnote 2 on p. 6. -/
abbrev Sample (n : ℕ) := Fin n → Unit
/-- "We assume ... an i.i.d. sample", p. 5 and p. 6 footnote 2; a finite product law. -/
def sampleLaw (M : Study) (n : ℕ) : Measure (Sample n) := Measure.pi (fun _ => M.law)
instance sampleLaw_probability (M : Study) (n : ℕ) [IsProbabilityMeasure M.law] :
    IsProbabilityMeasure (sampleLaw M n) := by
  unfold sampleLaw
  infer_instance
/-- "W=(W_1,W_2,...,W_n)", Appendix A, p. 16. -/
def covariates {n : ℕ} (a : Sample n) : Fin n → ℝ := fun i => W (a i)
/-- Conditioning on the full covariate vector W, Appendix A, p. 16. -/
def sampleCovariateSigma (n : ℕ) : MeasurableSpace (Sample n) :=
  MeasurableSpace.comap (covariates (n := n)) inferInstance

/-- Horvitz--Thompson summand, Proposition 2, p. 6: "[pi(W_i)]^{-1} X_i Y_i". -/
def htTerm (p x y : ℝ) : ℝ := x * y / p

/-- Horvitz--Thompson estimator, Proposition 2, p. 6:
"mu-hat = n^{-1} sum_{i=1}^n [pi(W_i)]^{-1}X_iY_i". -/
def ht (M : Study) {n : ℕ} (a : Sample n) : ℝ :=
  (∑ i, htTerm (M.pi (W (a i))) (X (a i)) (Y (a i))) / n

/-- "xi = n^{-1} sum_{i=1}^n [pi(W_i)]^{-2}", Proposition 3, p. 7.
It is a random statistic of the covariates, not a deterministic population bound. -/
def xi (M : Study) {n : ℕ} (a : Sample n) : ℝ :=
  (∑ i, (M.pi (W (a i)))⁻¹ ^ 2) / n

/-- Validators' mu_W = n^{-1} sum_i m(W_i), the conditional centre of the
printed estimator; Appendix A, p. 16, corrected by target T3. -/
def muW (M : Study) {n : ℕ} (a : Sample n) : ℝ := (∑ i, M.m (W (a i))) / n

/-- The printed radius, Proposition 3, p. 7 and Appendix A pp. 15--16:
"sqrt(xi log(2/alpha)/(2n))". -/
def printedRadius (M : Study) {n : ℕ} (alpha : ℝ) (a : Sample n) : ℝ :=
  Real.sqrt (xi M a * Real.log (2 / alpha) / (2 * n))

/-- Corrected radius, target T3, validator E001 section 7:
"(sqrt(xi)+1) sqrt(log(4/alpha)/(2n))". -/
def correctedRadius (M : Study) {n : ℕ} (alpha : ℝ) (a : Sample n) : ℝ :=
  (Real.sqrt (xi M a) + 1) * Real.sqrt (Real.log (4 / alpha) / (2 * n))

/-- A tail probability is over repeated i.i.d. samples; finite-sample validity
on p. 7 means coverage "greater or equal to its nominal level". -/
def tailProb (M : Study) {n : ℕ} (est radius : Sample n → ℝ) : ℝ :=
  (sampleLaw M n {a | radius a ≤ |est a - mu M|}).toReal

/-- Fixed-regression summand, p. 7:
"X_i[Y_i - g(W_i)]/pi(W_i) + g(W_i)". -/
def adjustedTerm (p x y g : ℝ) : ℝ := x * (y - g) / p + g

/-- The p. 7 estimator with a fixed regression g instead of fitted predictions. -/
def fixedAdjusted (M : Study) (g : ℝ → ℝ) {n : ℕ} (a : Sample n) : ℝ :=
  (∑ i, adjustedTerm (M.pi (W (a i))) (X (a i)) (Y (a i)) (g (W (a i)))) / n

/-- Cross-fitting, p. 7: "g-hat_0 is estimated using observations {i:s(i)=1}
... g-hat_1 ... {i:s(i)=0}". The fitted function is measurable and depends
only on observed triples in the opposite fold. No correctness of either fit
is assumed. Integrability, when needed for unbiasedness, is stated explicitly. -/
structure CrossFit (n : ℕ) where
  fold : Fin n → Bool
  g : Bool → Sample n → ℝ → ℝ
  measurable_g : ∀ j, Measurable (fun z : Sample n × ℝ => g j z.1 z.2)
  opposite_fold : ∀ j a b,
    (∀ i, fold i ≠ j → observe (a i) = observe (b i)) → g j a = g j b

/-- Regression estimator, p. 7:
"mu-hat_R = (1/n) sum_i {X_i[Y_i-g-hat_{s(i)}(W_i)]/pi(W_i)
+ g-hat_{s(i)}(W_i)}". -/
def adjusted (M : Study) {n : ℕ} (F : CrossFit n) (a : Sample n) : ℝ :=
  (∑ i, adjustedTerm (M.pi (W (a i))) (X (a i)) (Y (a i))
    (F.g (F.fold i) a (W (a i)))) / n

/-- "roughly equal size", p. 7, for an asymptotic fold sequence: each fold's
fraction tends to 1/2. Empty folds at very small n are permitted. -/
def Balanced (F : ∀ n, CrossFit n) : Prop := ∀ j : Bool,
  Tendsto (fun n => ((Finset.univ.filter (fun i => (F n).fold i = j)).card : ℝ) / n)
    atTop (nhds (1 / 2))

/-- Validators' q(w)=(1-pi(w))/pi(w), T5, not a separately printed object. -/
def q (M : Study) (w : ℝ) : ℝ := (1 - M.pi w) / M.pi w

/-- Population weighted risk, T5, validator E002 section 5:
"R(g)=E[q(W)(Y(1)-g(W))^2]". -/
def risk (M : Study) (g : ℝ → ℝ) : ℝ := ∫ o, q M (W o) * (Y1 o - g (W o))^2 ∂M.law

/-- Target T5 weighted squared norm "E[q(W)g(W)^2]", E002 section 6. -/
def weightedNormSq (M : Study) (g : ℝ → ℝ) : ℝ := ∫ o, q M (W o) * (g (W o))^2 ∂M.law

/-- Squared L2(F_W) prediction norm, targets T5/T9, E003 doubt section 3. -/
def l2Sq (M : Study) (g : ℝ → ℝ) : ℝ := ∫ o, (g (W o))^2 ∂M.law

/-- Validator's V(g)=Var(Y(1))+R(g), exact variance identity used in T5. -/
def V (M : Study) (g : ℝ → ℝ) : ℝ := variance Y1 M.law + risk M g

/-- Hahn benchmark for the single potential-outcome mean, target T9:
"E[m(W)(1-m(W))/pi(W)] + Var(m(W))". The model has unrestricted F_W.
This does not assert efficiency relative to a model fixing F_W. -/
def hahnBound (M : Study) : ℝ :=
  (∫ o, M.m (W o) * (1 - M.m (W o)) / M.pi (W o) ∂M.law) +
    variance (fun o => M.m (W o)) M.law

/-- Empirical treated-case weighted squared error, Proposition 4(c), p. 8,
read as in target T5: "Q_T(g)=sum_{i in T} X_i (1-pi_i)/pi_i^2 (Y_i-g(W_i))^2". -/
def empiricalRisk (M : Study) {n : ℕ} (T : Finset (Fin n)) (a : Sample n)
    (g : ℝ → ℝ) : ℝ :=
  ∑ i ∈ T, X (a i) * (1 - M.pi (W (a i))) / (M.pi (W (a i)))^2 *
    (Y (a i) - g (W (a i)))^2

/-- Root-n consistency, T9's reading of Proposition 4(b): tightness of
sqrt(n)(est_n-mu), with the population law fixed. -/
def RootN (M : Study) (est : ∀ n, Sample n → ℝ) : Prop :=
  ∀ eps > 0, ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N,
    (sampleLaw M n {a | C < Real.sqrt n * |est n a - mu M|}).toReal ≤ eps

/-- Convergence to N(0,v), T7/T9: weak convergence of the laws of
sqrt(n)(est_n-mu). Variance zero is represented by a point mass. -/
def NormalLimit (M : Study) (est : ∀ n, Sample n → ℝ) (v : ℝ) : Prop :=
  0 ≤ v ∧ ∃ hprob : IsProbabilityMeasure M.law, letI := hprob
    TendstoInDistribution (fun (n : ℕ) a => Real.sqrt n * (est n a - mu M)) atTop
      (fun z : ℝ => z) (fun n => sampleLaw M n) (gaussianReal 0 v.toNNReal)

/-- L2(F_W) consistency in probability of cross-fitted predictions, T5/T9.
The squared norm is used; its convergence to zero is equivalent to norm convergence. -/
def L2InProbability (M : Study) (F : ∀ n, CrossFit n) (j : Bool) (g : ℝ → ℝ) : Prop :=
  ∀ eps > 0, Tendsto (fun n => (sampleLaw M n
    {a | eps < l2Sq M (fun w => (F n).g j a w - g w)}).toReal) atTop (nhds 0)

/-- Stronger mean-square reading of "convergent in mean square", 4(b), T9:
expectation over the training sample of the squared L2 prediction error tends to zero. -/
def L2InMeanSquare (M : Study) (F : ∀ n, CrossFit n) (j : Bool) (g : ℝ → ℝ) : Prop :=
  Tendsto (fun n => ∫ a, l2Sq M (fun w => (F n).g j a w - g w) ∂sampleLaw M n)
    atTop (nhds 0) ∧
  (∀ n, Integrable (fun a => l2Sq M (fun w => (F n).g j a w - g w)) (sampleLaw M n))

/-- Uniform root-n consistency, T7: for a common positivity constant delta,
the tails are uniformly small over n>=1 and all valid laws with that constant.
This uses quantifiers equivalent to the double supremum in targets.json. -/
def UniformRootN (delta : ℝ) : Prop := ∀ eps > 0, ∃ C > 0,
  ∀ (M : Study), ValidStudy M → M.delta = delta → ∀ n : ℕ, 0 < n →
    (sampleLaw M n {a | C < Real.sqrt n * |ht M a - mu M|}).toReal ≤ eps

/-- Zero belongs to the working family or its weighted L2 closure, corrected
Proposition 4(c), T5. The sequence formulation is the metric closure criterion. -/
def ZeroBenchmark (M : Study) (G : Set (ℝ → ℝ)) : Prop :=
  (fun _ => (0 : ℝ)) ∈ G ∨ ∃ h : ℕ → ℝ → ℝ,
    (∀ k, h k ∈ G) ∧ Tendsto (fun k => weightedNormSq M (h k)) atTop (nhds 0)


end
end SAP.P046
