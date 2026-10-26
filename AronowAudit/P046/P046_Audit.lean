import Mathlib

/-!
P046: Nonparametric identification is not enough, but randomized controlled trials are.
Definitions, finite-sample identities, concentration bounds, asymptotic results,
and counterexample constructions for the paper.
-/
namespace AronowAudit.P046

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

/-- Binary coding of the paper's X and Y (Section 2, printed p. 5): "Y_i and X_i
are binary". Potential outcomes are also coded as bits, as justified by positivity,
consistency and unconfoundedness in the targets' standing assumptions. -/
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

/-- mu_W = n^{-1} sum_i m(W_i), the conditional centre of the
printed estimator; Appendix A, p. 16, corrected by target T3. -/
def muW (M : Study) {n : ℕ} (a : Sample n) : ℝ := (∑ i, M.m (W (a i))) / n

/-- The printed radius, Proposition 3, p. 7 and Appendix A pp. 15--16:
"sqrt(xi log(2/alpha)/(2n))". -/
def printedRadius (M : Study) {n : ℕ} (alpha : ℝ) (a : Sample n) : ℝ :=
  Real.sqrt (xi M a * Real.log (2 / alpha) / (2 * n))

/-- Corrected radius, target T3:
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

/-- q(w)=(1-pi(w))/pi(w), T5, not a separately printed object. -/
def q (M : Study) (w : ℝ) : ℝ := (1 - M.pi w) / M.pi w

/-- Population weighted risk, T5:
"R(g)=E[q(W)(Y(1)-g(W))^2]". -/
def risk (M : Study) (g : ℝ → ℝ) : ℝ := ∫ o, q M (W o) * (Y1 o - g (W o))^2 ∂M.law

/-- Target T5 weighted squared norm "E[q(W)g(W)^2]". -/
def weightedNormSq (M : Study) (g : ℝ → ℝ) : ℝ := ∫ o, q M (W o) * (g (W o))^2 ∂M.law

/-- Squared L2(F_W) prediction norm, targets T5/T9. -/
def l2Sq (M : Study) (g : ℝ → ℝ) : ℝ := ∫ o, (g (W o))^2 ∂M.law

/-- V(g)=Var(Y(1))+R(g), exact variance identity used in T5. -/
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
  ∃ hprob : IsProbabilityMeasure M.law, letI := hprob
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
the tails are uniformly small over n>=1 and all valid laws with that constant. -/
def UniformRootN (delta : ℝ) : Prop := ∀ eps > 0, ∃ C > 0,
  ∀ (M : Study), ValidStudy M → M.delta = delta → ∀ n : ℕ, 0 < n →
    (sampleLaw M n {a | C < Real.sqrt n * |ht M a - mu M|}).toReal ≤ eps

/-- Zero belongs to the working family or its weighted L2 closure, corrected
Proposition 4(c), T5. The sequence formulation is the metric closure criterion. -/
def ZeroBenchmark (M : Study) (G : Set (ℝ → ℝ)) : Prop :=
  (fun _ => (0 : ℝ)) ∈ G ∨ ∃ h : ℕ → ℝ → ℝ,
    (∀ k, h k ∈ G) ∧ Tendsto (fun k => weightedNormSq M (h k)) atTop (nhds 0)


/-- Proposition 1's estimator is a measurable function of observed samples only;
the same functions are used under every population, without the unknown pi. -/
abbrev ObservationalEstimator := ∀ n : ℕ, (Fin n → Observed) → ℝ


/-- Consistency identity XY=XY(1), used in Appendix A's proof of 4(a), p. 16. -/
theorem consistency_treated (o : Unit) : X o * Y o = X o * Y1 o := by
  rcases o with ⟨w, x, y0, y1⟩
  cases x <;> simp [X, Y, Y0, Y1, bit]

/-- T7(ii): binary HT summands lie in [0,1/pi], hence below 1/delta. -/
theorem ht_binary_range (p delta : ℝ) (hp : delta < p) (hd : 0 < delta)
    (x y : Bool) : 0 ≤ htTerm p (bit x) (bit y) ∧ htTerm p (bit x) (bit y) < delta⁻¹ := by
  have hp0 : 0 < p := lt_trans hd hp
  have hi : p⁻¹ < delta⁻¹ := (inv_lt_inv₀ hp0 hd).2 hp
  cases x <;> cases y <;> simp [bit, htTerm, hp0.le, inv_pos.mpr hd, hi]

/-- A fixed predictor's augmentation decomposition, target T5(a). -/
theorem adjusted_decomposition (p x y g : ℝ) :
    adjustedTerm p x y g = htTerm p x y + (1 - x / p) * g := by
  simp only [adjustedTerm, htTerm, div_eq_mul_inv]
  ring

/-- Fixed-prediction increment, T5(e) and T9(b): nuisance errors multiply 1-X/pi. -/
theorem adjusted_increment (p x y g e : ℝ) :
    adjustedTerm p x y (g + e) - adjustedTerm p x y g = (1 - x / p) * e := by
  simp only [adjustedTerm, div_eq_mul_inv]
  ring

/-- The finite conditional expectation of a binary variable with success probability p.
This represents the Bernoulli assignment given W, p. 5. -/
def bernE (p : ℝ) (f : Bool → ℝ) : ℝ := (1 - p) * f false + p * f true

/-- Bernoulli weights are normalized; this is not an extra sampling assumption. -/
theorem bern_normalization (p : ℝ) : bernE p (fun _ => 1) = 1 := by
  simp [bernE]

/-- Correct conditional centring given W,Y(1), target T5(a). -/
theorem bern_adjusted_mean (p t g : ℝ) (hp : p ≠ 0) :
    bernE p (fun x => adjustedTerm p (bit x) t g) = t := by
  simp only [bernE, adjustedTerm, bit, Bool.false_eq_true, if_false, if_true]
  field_simp
  <;> ring

/-- Conditional assignment variance, target T5(a): q(W)(Y(1)-g(W))^2. -/
theorem bern_adjusted_variance (p t g : ℝ) (hp : p ≠ 0) :
    bernE p (fun x => (adjustedTerm p (bit x) t g - t)^2) =
      (1 - p) / p * (t - g)^2 := by
  simp only [bernE, adjustedTerm, bit, Bool.false_eq_true, if_false, if_true]
  field_simp
  <;> ring

/-- T9(c): the nuisance-error multiplier has conditional mean zero. -/
theorem bern_multiplier_mean (p : ℝ) (hp : p ≠ 0) :
    bernE p (fun x => 1 - bit x / p) = 0 := by
  simp only [bernE, bit, Bool.false_eq_true, if_false, if_true]
  field_simp
  <;> ring

/-- T9(c): its conditional second moment is (1-pi)/pi. -/
theorem bern_multiplier_second (p : ℝ) (hp : p ≠ 0) :
    bernE p (fun x => (1 - bit x / p)^2) = (1 - p) / p := by
  simp only [bernE, bit, Bool.false_eq_true, if_false, if_true]
  field_simp
  <;> ring

/-- Conditional binary outcome expectation, T3(i), T7(i): E[XY(1)/pi|W]=m(W). -/
theorem bern_ht_mean (p m : ℝ) (hp : p ≠ 0) :
    bernE m (fun t => bernE p (fun x => htTerm p (bit x) (bit t))) = m := by
  simp only [bernE, htTerm, bit, Bool.false_eq_true, if_false, if_true]
  field_simp
  <;> ring

/-- T7(iii), exact binary second moment conditional on W. -/
theorem bern_ht_second (p m : ℝ) (hp : p ≠ 0) :
    bernE m (fun t => bernE p (fun x => (htTerm p (bit x) (bit t))^2)) = m / p := by
  simp only [bernE, htTerm, bit, Bool.false_eq_true, if_false, if_true]
  field_simp
  <;> ring

/-- T9(a): the fixed prediction's variance given W equals
m(1-m)/pi + q(m-g)^2. Adding Var(m(W)) gives the Hahn decomposition. -/
theorem bern_conditional_variance (p m g : ℝ) (hp : p ≠ 0) :
    bernE m (fun t => bernE p (fun x => (adjustedTerm p (bit x) (bit t) g - m)^2)) =
      m * (1 - m) / p + (1 - p) / p * (m - g)^2 := by
  simp only [bernE, adjustedTerm, bit, Bool.false_eq_true, if_false, if_true]
  field_simp
  <;> ring

/-- T3(iv), actual probability triangle/union bound. The two radii may be
random functions of the sample and the two errors need not be independent. -/
theorem two_error_union_bound {A : Type*} [MeasurableSpace A]
    (nu : Measure A) [IsProbabilityMeasure nu] (f c : A → ℝ) (m : ℝ)
    (r1 r2 : A → ℝ) (alpha : ℝ)
    (h1 : nu.real {a | r1 a ≤ |f a - c a|} ≤ alpha / 2)
    (h2 : nu.real {a | r2 a ≤ |c a - m|} ≤ alpha / 2) :
    nu.real {a | r1 a + r2 a ≤ |f a - m|} ≤ alpha := by
  have hs : {a | r1 a + r2 a ≤ |f a - m|} ⊆
      {a | r1 a ≤ |f a - c a|} ∪ {a | r2 a ≤ |c a - m|} := by
    intro a ha
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at h
    have ht : |f a - m| ≤ |f a - c a| + |c a - m| := by
      convert abs_add_le (f a - c a) (c a - m) using 1 <;> ring
    simp only [Set.mem_setOf_eq] at ha
    linarith
  have hu := measureReal_union_le (μ := nu)
    {a | r1 a ≤ |f a - c a|} {a | r2 a ≤ |c a - m|}
  have hm := measureReal_mono (μ := nu) hs
  linarith

/-- T5 benchmark implication when the family actually contains zero: a
risk minimizer cannot have larger V=Var(Y(1))+R than the HT benchmark. -/
theorem risk_minimizer_zero (M : Study) (G : Set (ℝ → ℝ))
    (hz : (fun _ => (0 : ℝ)) ∈ G) (gstar : ℝ → ℝ)
    (hm : ∀ g ∈ G, risk M gstar ≤ risk M g) : V M gstar ≤ V M (fun _ => 0) := by
  unfold V
  linarith [hm _ hz]

/-- Exact i.i.d. sample-mean variance, the finite step used by T4, T7 and T9.
No asymptotic or normal approximation is asserted in this lemma. -/
theorem iid_mean_variance {A : Type*} [MeasurableSpace A]
    (nu : Measure A) [IsProbabilityMeasure nu] (f : A → ℝ) (hf : MemLp f 2 nu)
    (n : ℕ) (hn : 0 < n) :
    variance (fun a : Fin n → A => (∑ i, f (a i)) / n) (Measure.pi (fun _ => nu)) =
      variance f nu / n := by
  have heq : (fun a : Fin n → A => (∑ i, f (a i)) / n) =
      (fun a => (n : ℝ)⁻¹ * (∑ i, f (a i))) := by
    funext a
    ring
  rw [heq, variance_const_mul]
  have hs : variance (fun a : Fin n → A => ∑ i, f (a i)) (Measure.pi (fun _ => nu)) =
      ∑ _ : Fin n, variance f nu := by
    simpa only [Finset.sum_fn] using variance_sum_pi (fun _ : Fin n => hf)
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp
  <;> ring

/-- Uniform(0,1) covariate/auxiliary randomization law for the concrete
counterexamples T1, T2 and T4. Endpoints have probability zero. -/
def unitUniform : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- Lebesgue measure of [0,1] is one. This witnesses the corrected
continuous Uniform(0,1) law used in T1, T2, T4 and T10, not counting measure. -/
instance unitUniform_probability : IsProbabilityMeasure unitUniform where
  measure_univ := by simp [unitUniform, Real.volume_Icc]


namespace IntervalExample

/-- T1's known score is 13/20 below 3/5 and 99/100 above it. -/
def score (w : ℝ) : ℝ := if w ≤ 3/5 then 13/20 else 99/100

def generate (z : ℝ × ℝ) : Unit :=
  (z.1, (decide (z.2 ≤ score z.1), (false, decide (z.1 ≤ 3/5))))

/-- Fully continuous law specified by independent U(0,1) W and assignment U;
Y(1)=1{W<=3/5}, Y(0)=0 and X=1{U<=pi(W)}, target T1. -/
def study : Study := ⟨Measure.map generate (unitUniform.prod unitUniform), score,
  (fun w => if w ≤ 3/5 then 1 else 0), 1/200⟩


/-- T1: both concrete scores meet strict positivity with delta=1/200. -/
theorem score_positivity (w : ℝ) : 1/200 < score w ∧ score w < 1 - 1/200 := by
  unfold score
  split <;> norm_num

/-- T1's exact count-state statistic xi_k. -/
def xiK (k : ℕ) : ℝ := (400 * k / 169 + 10000 * (100 - (k : ℝ)) / 9801) / 100

/-- T1's integer multinomial numerator of P(K=k,S=s), denominator 100^100. -/
def massNumerator (k s : ℕ) : ℕ :=
  Nat.choose 100 k * Nat.choose k s * 39^s * 21^(k-s) * 40^(100-k)

/-- A kernel-checkable rational cutoff: T_{k,s}>17. Since log(20000000)<17,
these states are a subset of the actual noncoverage states. -/
def cut17 (k s : ℕ) : Bool := decide
  (7840800 * (if s ≤ 39 then 39-s else s-39)^2 >
    17 * (3920400*k + 1690000*(100-k)))

/-- Explicit rational lower-bound mass from cutoff 17, using the exact
multinomial state probabilities; a subset, not the full 1946-state failure mass. -/
def lowerNumerator : ℕ := ∑ k ∈ Finset.range 101, ∑ s ∈ Finset.range (k+1),
  if cut17 k s then massNumerator k s else 0

/-- T1's logarithm is less than 17, proved by a finite lower Taylor bound for exp(1). -/
theorem log_lt_seventeen : Real.log 20000000 < 17 := by
  have h := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have he : (27/10 : ℝ) < Real.exp 1 := by linarith
  have hp : (20000000 : ℝ) < Real.exp 17 := by
    have hh := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 27/10) (by decide : 17 ≠ 0)
    have hr : Real.exp 17 = Real.exp 1 ^ 17 := by
      simpa using Real.exp_nat_mul 1 17
    rw [hr]
    norm_num at hh ⊢
    linarith
  exact (Real.log_lt_iff_lt_exp (by norm_num)).2 hp

/-- T1 finite rational certificate: the cutoff-17 state mass exceeds alpha.
The proof is kernel reduction on natural arithmetic, without native_decide. -/
theorem lower_mass_exceeds_alpha : 10000000 * lowerNumerator > 100^100 := by
  simp only [lowerNumerator, massNumerator, Nat.choose_eq_fast_choose]
  decide


end IntervalExample

namespace ConditionalExample

/-- T2: constant known propensity 9/10, Y(1)=1{W>=1/2}, Y(0)=0. -/
def generate (z : ℝ × ℝ) : Unit :=
  (z.1, (decide (z.2 ≤ (9/10 : ℝ)), (false, decide ((1/2 : ℝ) ≤ z.1))))

def study : Study := ⟨Measure.map generate (unitUniform.prod unitUniform), (fun _ => 9/10),
  (fun w => if 1/2 ≤ w then 1 else 0), 1/20⟩

/-- The covariate event E={all W_i<1/2}, T2. -/
def E : Set (Sample 100) := {a | ∀ i, W (a i) < 1/2}


/-- T2: strict positivity at delta=1/20 for the constant score 9/10. -/
theorem score_positivity : (1/20 : ℝ) < 9/10 ∧ (9/10 : ℝ) < 1-1/20 := by norm_num

/-- T2: the squared radius log(40)/162 is strictly less than 1/4. -/
theorem radius_sq_lt : Real.log 40 / 162 < (1/4 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (x := 40) (by norm_num)
  linarith

/-- T2: the radius is less than 1/2, so the covariate-conditional deviation
of 1/2 strictly exceeds it. -/
theorem radius_lt_half : Real.sqrt (Real.log 40 / 162) < (1/2 : ℝ) := by
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1/2)).2
  norm_num
  exact radius_sq_lt

/-- T2: the covariate event probability 2^{-100} is positive. -/
theorem event_positive : (0 : ℝ) < (1/2 : ℝ)^100 := by positivity

/-- T2: the printed right side simplifies exactly to alpha=1/20. -/
theorem printed_rhs : 2 * Real.exp (-Real.log 40) = (1/20 : ℝ) := by
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 40)]
  norm_num

end ConditionalExample

namespace RegressionExample

/-- T4: the lower-half score is 1/4, the upper-half score is 3/4. -/
def scoreL (l : Bool) : ℝ := if l then 1/4 else 3/4

def score (w : ℝ) : ℝ := scoreL (decide (w ≤ (1/2 : ℝ)))

/-- T4: one unrestricted real parameter, with g_theta=1/2 on the lower
half and theta on the upper half. This family does not include zero. -/
def predictionL (theta : ℝ) (l : Bool) : ℝ := if l then 1/2 else theta
def prediction (theta w : ℝ) : ℝ := predictionL theta (decide (w ≤ (1/2 : ℝ)))

def generate (z : (ℝ × ℝ) × ℝ) : Unit :=
  let l := decide (z.1.1 ≤ (1/2 : ℝ))
  let b := l && decide (z.1.2 ≤ (1/10 : ℝ))
  (z.1.1, (decide (z.2 ≤ score z.1.1), (b, b)))

/-- T4's continuous law: W uniform, Z Bernoulli(1/10) independent of W,
X|W independent of Z, and Y(0)=Y(1)=LZ. -/
def study : Study :=
  ⟨Measure.map generate ((unitUniform.prod unitUniform).prod unitUniform), score,
    (fun w => if w ≤ 1/2 then 1/10 else 0), 1/8⟩

/-- Exact eight-atom expectation of (L,Z,X). The covariate
W remains continuous; only the statistics constant on its two halves are reduced. -/
def atomE (f : Bool → Bool → Bool → ℝ) : ℝ :=
  (1/2) * bernE (1/10) (fun z => bernE (1/4) (fun x => f true z x)) +
  (1/2) * bernE (1/10) (fun z => bernE (3/4) (fun x => f false z x))

/-- T4 potential and observed outcome "LZ". -/
def outcomeL (l z : Bool) : ℝ := bit l * bit z

/-- T4 "H=XY/pi(W)". -/
def H (l z x : Bool) : ℝ := htTerm (scoreL l) (bit x) (outcomeL l z)
/-- T4 "A=X[Y-g_*(W)]/pi(W)+g_*(W)". -/
def A (l z x : Bool) : ℝ := adjustedTerm (scoreL l) (bit x) (outcomeL l z) (predictionL 0 l)

/-- T4 treated-case training loss, p. 8 weights. -/
def loss (theta : ℝ) (l z x : Bool) : ℝ :=
  bit x * (1 - scoreL l) / (scoreL l)^2 * (outcomeL l z - predictionL theta l)^2

/-- T4: the exact finite law has nonnegative normalized mass. -/
theorem atom_normalization : atomE (fun _ _ _ => 1) = 1 := by norm_num [atomE, bernE]

/-- T4: both propensity values satisfy strict positivity with delta=1/8. -/
theorem score_positivity (l : Bool) : 1/8 < scoreL l ∧ scoreL l < 1 - 1/8 := by
  cases l <;> norm_num [scoreL]

/-- T4(a): changing theta from zero increases each training loss by a
nonnegative multiple of theta^2, including empty or untreated folds. -/
theorem loss_increase (theta : ℝ) (l z x : Bool) :
    loss theta l z x - loss 0 l z x = (if l then 0 else (4/9) * bit x * theta^2) := by
  cases l <;> cases z <;> cases x <;> norm_num [loss, scoreL, outcomeL, predictionL, bit] <;> ring <;> simp

/-- T4(a): theta=0 minimizes the empirical weighted criterion for every
training set, regardless of sample size or whether treated observations are present. -/
theorem empirical_minimizer {n : ℕ} (T : Finset (Fin n))
    (l z x : Fin n → Bool) (theta : ℝ) :
    (∑ i ∈ T, loss 0 (l i) (z i) (x i)) ≤ ∑ i ∈ T, loss theta (l i) (z i) (x i) := by
  apply Finset.sum_le_sum
  intro i hi
  have hh := loss_increase theta (l i) (z i) (x i)
  have hn : (0 : ℝ) ≤ (if l i then 0 else (4/9) * bit (x i) * theta^2) := by
    cases l i <;> cases x i <;> simp [bit] <;> positivity
  linarith

/-- T4(b): the population weighted criterion equals 3/8+theta^2/6. -/
theorem population_loss (theta : ℝ) :
    atomE (loss theta) = 3/8 + theta^2/6 := by
  simp [atomE, bernE, loss, scoreL, outcomeL, predictionL, bit]
  ring

/-- T4(b): the population criterion is uniquely minimized at zero. -/
theorem population_unique_minimum (theta : ℝ) :
    atomE (loss 0) ≤ atomE (loss theta) ∧
    (atomE (loss theta) = atomE (loss 0) ↔ theta = 0) := by
  rw [population_loss, population_loss]
  constructor
  · nlinarith [sq_nonneg theta]
  · constructor
    · intro h
      nlinarith [sq_nonneg theta]
    · intro h
      simp [h]

/-- T4(c): exact first and second moments under the eight-atom pushforward. -/
theorem atom_moments : atomE H = 1/20 ∧ atomE A = 1/20 ∧
    atomE (fun l z x => H l z x ^ 2) = 1/5 ∧
    atomE (fun l z x => A l z x ^ 2) = 17/40 := by
  norm_num [atomE, bernE, H, A, htTerm, adjustedTerm, scoreL, outcomeL, predictionL, bit]

/-- T4(c): centred variances are 79/400 for HT and 169/400 for adjustment,
so the excess is 9/40 and the variance ratio is 169/79. -/
theorem atom_variances :
    atomE (fun l z x => (H l z x - 1/20)^2) = 79/400 ∧
    atomE (fun l z x => (A l z x - 1/20)^2) = 169/400 ∧
    (169/400 : ℝ) - 79/400 = 9/40 ∧
    (169/400 : ℝ) / (79/400) = 169/79 ∧ (79/400 : ℝ) < 169/400 := by
  norm_num [atomE, bernE, H, A, htTerm, adjustedTerm, scoreL, outcomeL, predictionL, bit]

/-- T4(e): zero is not in this family's weighted L2 closure; every member
has weighted squared norm at least 3/8. -/
theorem zero_not_in_closure (theta : ℝ) :
    atomE (fun l _ _ => (1-scoreL l)/scoreL l * (predictionL theta l)^2) =
      3/8 + theta^2/6 ∧ (3/8 : ℝ) ≤ 3/8 + theta^2/6 := by
  constructor
  · simp [atomE, bernE, scoreL, predictionL]
    ring
  · nlinarith [sq_nonneg theta]


end RegressionExample

/-- T10(a): a randomly mixed bin type has precisely the observable law of
law A, although the mean potential outcomes differ. These are exact numbers. -/
theorem robins_ritov_single_bin :
    (1/2 : ℝ)*(1/4)*1 + (1/2)*(3/4)*(1/3) = 1/4 ∧
    (1/2 : ℝ)*(1/4)*0 + (1/2)*(3/4)*(2/3) = 1/4 ∧
    (1/2 : ℝ)*(3/4) + (1/2)*(1/4) = 1/2 ∧
    (1/2 : ℝ)*1 + (1/2)*(1/3) = 2/3 ∧ (2/3 : ℝ) - 1/2 = 1/6 := by
  norm_num

/-- Bin labels in the T10 finite lower-bound construction: n independent
uniform labels among K bins. This is the pushforward of continuous uniform W. -/
def binLaw (K n : ℕ) : Measure (Fin n → Fin K) :=
  Measure.pi (fun _ => uniformOn (Set.univ : Set (Fin K)))


/-- T10(d): the mean under the random-bin prior is 2/3 and the one-bin
variance of the potential-outcome mean (1 or 1/3 equiprobably) is 1/9. -/
theorem robins_ritov_prior_moments :
    bernE (1/2) (fun t => if t then 1 else 1/3) = 2/3 ∧
    bernE (1/2) (fun t => ((if t then 1 else 1/3)-2/3)^2) = 1/9 := by
  norm_num [bernE]
/-- T3(v), finite strict positivity bound on sqrt(xi) at each sample. -/
theorem sqrt_mean_inverse_sq_lt (n : ℕ) (hn : 0 < n) (delta : ℝ) (hd : 0 < delta)
    (p : Fin n → ℝ) (hp : ∀ i, delta < p i) :
    Real.sqrt ((∑ i, (p i)⁻¹^2) / n) < delta⁻¹ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hi : ∀ i, (p i)⁻¹ < delta⁻¹ := fun i =>
    (inv_lt_inv₀ (lt_trans hd (hp i)) hd).2 (hp i)
  have hs : ∀ i, (p i)⁻¹^2 < delta⁻¹^2 := by
    intro i
    exact pow_lt_pow_left₀ (hi i) (le_of_lt (inv_pos.mpr (lt_trans hd (hp i)))) (by decide : 2 ≠ 0)
  have hsum : (∑ i, (p i)⁻¹^2) < ∑ _ : Fin n, delta⁻¹^2 := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (hs i).le
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _, hs ⟨0, hn⟩⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  apply (Real.sqrt_lt' (inv_pos.mpr hd)).2
  apply (div_lt_iff₀ hnR).2
  simpa [mul_comm] using hsum

/-- T3(v): strict radius bound and a uniform-in-samples O(n^{-1/2}) width
bound for each fixed alpha. This is an explicit quantifier formulation of the
width rate, rather than an alteration of the confidence-coverage statement. -/
theorem corrected_width (M : Study) (hM : ValidStudy M)
    (alpha : ℝ) (ha : 0 < alpha ∧ alpha < 1) :
    (∀ n : ℕ, 0 < n → ∀ᵐ a ∂sampleLaw M n,
      correctedRadius M alpha a <
        (M.delta⁻¹+1) * Real.sqrt (Real.log (4/alpha)/(2*n))) ∧
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ᵐ a ∂sampleLaw M n,
      2 * correctedRadius M alpha a ≤ C / Real.sqrt n := by
  letI := hM.probability
  have hlog : 0 < Real.log (4/alpha) := Real.log_pos (by
    apply (lt_div_iff₀ ha.1).2
    linarith [ha.2])
  have hb : ∀ n : ℕ, 0 < n → ∀ᵐ a ∂sampleLaw M n,
      correctedRadius M alpha a < (M.delta⁻¹+1) * Real.sqrt (Real.log (4/alpha)/(2*n)) := by
    intro n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hall : ∀ᵐ a ∂sampleLaw M n, ∀ i, M.delta < M.pi (W (a i)) := by
      change ∀ᵐ a ∂Measure.pi (fun _ : Fin n => M.law), ∀ i, M.delta < M.pi (W (a i))
      exact ae_all_iff.2 (fun i =>
        (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => M.law) (i := i)).eventually
          (hM.positivity.mono fun _ h => h.1))
    filter_upwards [hall] with a ha
    have hs := sqrt_mean_inverse_sq_lt n hn M.delta hM.delta_pos (fun i => M.pi (W (a i))) ha
    unfold correctedRadius xi
    exact mul_lt_mul_of_pos_right (by linarith [hs])
      (Real.sqrt_pos.2 (div_pos hlog (by positivity)))
  have hd := hM.delta_pos
  refine ⟨hb, 2 * (M.delta⁻¹+1) * Real.sqrt (Real.log (4/alpha)/2), by positivity, ?_⟩
  intro n hn
  filter_upwards [hb n hn] with a ha
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have heq : Real.sqrt (Real.log (4/alpha)/(2*n)) =
      Real.sqrt (Real.log (4/alpha)/2) / Real.sqrt n := by
    rw [show Real.log (4/alpha)/(2*n) = (Real.log (4/alpha)/2)/n by ring]
    exact Real.sqrt_div (by positivity) n
  calc
    2 * correctedRadius M alpha a ≤
        2 * ((M.delta⁻¹+1) * Real.sqrt (Real.log (4/alpha)/(2*n))) := by linarith
    _ = _ := by rw [heq]; ring

/-- Fixed-fold leading average for T9(b), allowing different deterministic
regression limits g_0 and g_1. -/
def leading (M : Study) {n : ℕ} (F : CrossFit n) (g : Bool → ℝ → ℝ) (a : Sample n) : ℝ :=
  (∑ i, adjustedTerm (M.pi (W (a i))) (X (a i)) (Y (a i)) (g (F.fold i) (W (a i)))) / n

/-- T5(e), T9(b): R_j=(1/n) sum_{i in I_j}(1-X_i/pi_i)(g-hat_j-g_j)(W_i). -/
def foldRemainder (M : Study) {n : ℕ} (F : CrossFit n) (j : Bool)
    (g : ℝ → ℝ) (a : Sample n) : ℝ :=
  (∑ i, if F.fold i = j then
    (1-X (a i)/M.pi (W (a i))) * (F.g j a (W (a i)) - g (W (a i))) else 0) / n

/-- T9(b): exact two-fold decomposition for every fixed sample and arbitrary
fitted functions; at g_0=g_1=m the leading term is the Hahn influence-function mean. -/
theorem crossfit_decomposition (M : Study) {n : ℕ} (F : CrossFit n)
    (g : Bool → ℝ → ℝ) (a : Sample n) :
    adjusted M F a - mu M = leading M F g a - mu M +
      foldRemainder M F false (g false) a + foldRemainder M F true (g true) a := by
  have hi : ∀ i : Fin n,
      adjustedTerm (M.pi (W (a i))) (X (a i)) (Y (a i)) (F.g (F.fold i) a (W (a i))) =
      adjustedTerm (M.pi (W (a i))) (X (a i)) (Y (a i)) (g (F.fold i) (W (a i))) +
      (if F.fold i = false then (1-X (a i)/M.pi (W (a i))) *
        (F.g false a (W (a i)) - g false (W (a i))) else 0) +
      (if F.fold i = true then (1-X (a i)/M.pi (W (a i))) *
        (F.g true a (W (a i)) - g true (W (a i))) else 0) := by
    intro i
    cases hf : F.fold i <;> simp [hf, adjustedTerm, div_eq_mul_inv] <;> ring
  unfold adjusted leading foldRemainder
  simp_rw [hi]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- The sigma-algebra generated by the opposite fold's observed triples,
used for conditioning on the training data, T9(c). -/
def trainingSigma {n : ℕ} (F : CrossFit n) (j : Bool) : MeasurableSpace (Sample n) :=
  MeasurableSpace.comap (fun a i => if F.fold i ≠ j then observe (a i) else (0, (0, 0)))
    (inferInstance : MeasurableSpace (Fin n → Observed))


/-- T3(i): iterating the chosen conditional regression gives E[m(W)]=mu.
This is an actual continuous-law integral identity, not an eight-atom calculation. -/
theorem regression_mean (M : Study) (hM : ValidStudy M) :
    (∫ o, M.m (W o) ∂M.law) = mu M := by
  letI := hM.probability
  have hm : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  letI : IsFiniteMeasure (M.law.trim hm) := isFiniteMeasure_trim hm
  calc
    (∫ o, M.m (W o) ∂M.law) = ∫ o, condExp covariateSigma M.law Y1 o ∂M.law :=
      integral_congr_ae hM.regression.symm
    _ = mu M := integral_condExp hm

/-- T3(i), T7(i): the expectation of a finite i.i.d. sample mean equals the
one-unit expectation, when the summand is integrable. -/
theorem iid_mean_integral {A : Type*} [MeasurableSpace A]
    (nu : Measure A) [IsProbabilityMeasure nu] (f : A → ℝ) (hf : Integrable f nu)
    (n : ℕ) (hn : 0 < n) :
    (∫ a : Fin n → A, (∑ i, f (a i)) / n ∂Measure.pi (fun _ => nu)) = ∫ x, f x ∂nu := by
  have hi : ∀ i : Fin n, Integrable (fun a : Fin n → A => f (a i)) (Measure.pi (fun _ => nu)) :=
    fun i => (measurePreserving_eval (fun _ => nu) i).integrable_comp_of_integrable hf
  have hs : (∫ a : Fin n → A, (∑ i, f (a i)) ∂Measure.pi (fun _ => nu)) =
      ∑ i, ∫ a : Fin n → A, f (a i) ∂Measure.pi (fun _ => nu) := by
    simpa only [Finset.sum_fn] using integral_finsetSum Finset.univ (fun i _ => hi i)
  have he : ∀ i : Fin n,
      (∫ a : Fin n → A, f (a i) ∂Measure.pi (fun _ => nu)) = ∫ x, f x ∂nu := by
    intro i
    have hp := measurePreserving_eval (fun _ : Fin n => nu) i
    have hfm : AEStronglyMeasurable f
        (Measure.map (fun a : Fin n → A => a i) (Measure.pi (fun _ => nu))) := by
      rw [hp.map_eq]
      exact hf.aestronglyMeasurable
    calc
      _ = ∫ x, f x ∂Measure.map (fun a : Fin n → A => a i) (Measure.pi (fun _ => nu)) :=
        (integral_map hp.measurable.aemeasurable hfm).symm
      _ = _ := by rw [hp.map_eq]
  rw [integral_div, hs]
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp

/-- T3(i): the sample covariate centre mu_W is itself unbiased for the
population mean. Its random variation cannot be discarded in conditional inference. -/
theorem muW_unbiased (M : Study) (hM : ValidStudy M) (n : ℕ) (hn : 0 < n) :
    (∫ a, muW M a ∂sampleLaw M n) = mu M := by
  letI := hM.probability
  have hi : Integrable (fun o => M.m (W o)) M.law := integrable_condExp.congr hM.regression
  unfold muW sampleLaw
  rw [iid_mean_integral M.law _ hi n hn]
  exact regression_mean M hM

namespace RobinsRitov

/-- T10 construction: equal bins of (0,1) for uniform W. The endpoint W=1
is assigned to bin zero; it has probability zero and changes no population law. -/
def bin (K : ℕ) (hK : 0 < K) (w : ℝ) : Fin K :=
  ⟨(⌊(K : ℝ)*w⌋₊) % K, Nat.mod_lt _ hK⟩

/-- T10's two bin types: (pi,m)=(1/4,1) or (3/4,1/3), target finite construction. -/
def piB {K : ℕ} (hK : 0 < K) (tau : Fin K → Bool) (w : ℝ) : ℝ :=
  if tau (bin K hK w) then 1/4 else 3/4
/-- Outcome means 1 and 1/3 in the two bin types, T10 finite construction. -/
def mB {K : ℕ} (hK : 0 < K) (tau : Fin K → Bool) (w : ℝ) : ℝ :=
  if tau (bin K hK w) then 1 else 1/3

def generate (pi m : ℝ → ℝ) (z : (ℝ × ℝ) × ℝ) : Unit :=
  (z.1.1, (decide (z.1.2 ≤ pi z.1.1), (false, decide (z.2 ≤ m z.1.1))))

/-- Law A in the T10 construction: pi=m=1/2, W uniform, Y(0)=0. -/
def lawA : Study :=
  ⟨Measure.map (generate (fun _ => 1/2) (fun _ => 1/2))
    ((unitUniform.prod unitUniform).prod unitUniform), (fun _ => 1/2), (fun _ => 1/2), 1/8⟩

/-- Law B_tau in T10: independent assignment/outcome uniforms conditional on
continuous W, with the two bin types. Delta=1/8 is common to A and every B_tau. -/
def lawB {K : ℕ} (hK : 0 < K) (tau : Fin K → Bool) : Study :=
  ⟨Measure.map (generate (piB hK tau) (mB hK tau))
    ((unitUniform.prod unitUniform).prod unitUniform), piB hK tau, mB hK tau, 1/8⟩

/-- T10's independent equiprobable prior on the K bin types. -/
def prior (K : ℕ) : Measure (Fin K → Bool) := Measure.pi (fun _ => uniformOn (Set.univ : Set Bool))

/-- Mixture of B_tau sample laws in the lower-bound argument, T10(c). -/
def mixture {K : ℕ} (hK : 0 < K) (n : ℕ) : Measure (Sample n) :=
  (prior K).bind (fun tau => sampleLaw (lawB hK tau) n)


end RobinsRitov
namespace IntervalExample

/-- T1 finite radius comparison: every valid count state with rational
cutoff T_{k,s}>17 strictly excludes mu, using the proved log upper bound. -/
theorem cutoff_implies_squared_exclusion (k s : ℕ) (hk : k ≤ 100)
    (hs : s ≤ k) (hc : cut17 k s = true) :
    xiK k * Real.log 20000000 / 200 < ((s : ℝ) - 39)^2 / 65^2 := by
  have hN : 17*(3920400*k + 1690000*(100-k)) <
      7840800*(if s ≤ 39 then 39-s else s-39)^2 := by
    simpa [cut17] using hc
  have hR : (17 : ℝ)*(3920400*(k : ℝ) + 1690000*((100-k : ℕ) : ℝ)) <
      7840800*((if s ≤ 39 then 39-s else s-39 : ℕ) : ℝ)^2 := by
    exact_mod_cast hN
  rw [Nat.cast_sub hk] at hR
  have hd : (17 : ℝ)*(3920400*(k : ℝ) + 1690000*(100-(k : ℝ))) <
      7840800*((s : ℝ)-39)^2 := by
    by_cases h : s ≤ 39
    · rw [if_pos h, Nat.cast_sub h] at hR
      norm_num at hR
      nlinarith
    · rw [if_neg h, Nat.cast_sub (Nat.le_of_lt (Nat.lt_of_not_ge h))] at hR
      norm_num at hR
      nlinarith
  have hx : 0 < xiK k := by
    dsimp [xiK]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have h17 : xiK k * 17 / 200 < ((s : ℝ)-39)^2 / 65^2 := by
    dsimp [xiK]
    nlinarith [hd]
  calc
    xiK k * Real.log 20000000 / 200 < xiK k * 17 / 200 := by
      gcongr
      exact log_lt_seventeen
    _ < _ := h17

/-- T1: exactly 1928 states have threshold greater than 17. This counts the
sufficient subset used here, not the target's 1946 states above log(20000000). -/
theorem cutoff_state_count :
    (∑ k ∈ Finset.range 101, ∑ s ∈ Finset.range (k+1), if cut17 k s then (1 : ℕ) else 0) = 1928 := by
  decide

end IntervalExample

/-- T7(i), actual conditional-independence identity: E[XY(1)|W]=pi(W)m(W).
It follows from separate unconfoundedness for Y(1) and the binary event indicators. -/
theorem conditional_xy_factorization (M : Study) (hM : ValidStudy M) :
    condExp covariateSigma M.law (fun o => X o * Y1 o) =ᵐ[M.law]
      fun o => M.pi (W o) * M.m (W o) := by
  letI := hM.probability
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have hy : (Y1 ⁻¹' ({1} : Set ℝ)).indicator (fun _ => (1 : ℝ)) = Y1 := by
    funext o
    rcases o with ⟨w, x, y0, y1⟩
    cases y1 <;> simp [Y1, bit, Set.indicator]
  have hx : (X ⁻¹' ({1} : Set ℝ)).indicator (fun _ => (1 : ℝ)) = X := by
    funext o
    rcases o with ⟨w, x, y0, y1⟩
    cases x <;> simp [X, bit, Set.indicator]
  have hxy : ((Y1 ⁻¹' ({1} : Set ℝ)) ∩ (X ⁻¹' ({1} : Set ℝ))).indicator
      (fun _ => (1 : ℝ)) = fun o => X o * Y1 o := by
    funext o
    rcases o with ⟨w, x, y0, y1⟩
    cases x <;> cases y1 <;> simp [X, Y1, bit, Set.indicator]
  have h := (condIndepFun_iff_condExp_inter_preimage_eq_mul my mx).1 hM.unconfounded1
    ({1} : Set ℝ) ({1} : Set ℝ) (measurableSet_singleton 1) (measurableSet_singleton 1)
  simp only [hy, hx, hxy] at h
  filter_upwards [h, hM.regression, hM.propensity] with o ho hreg hprop
  rw [ho, hreg, hprop, mul_comm]

/-- T7(i): an HT summand is integrable and its continuous-law expectation is mu.
This uses conditional independence, pull-out and iterated expectation, rather
than assuming its expectation as part of the statistical model. -/
theorem ht_unit_facts (M : Study) (hM : ValidStudy M) :
    Integrable (fun o => htTerm (M.pi (W o)) (X o) (Y o)) M.law ∧
    (∫ o, htTerm (M.pi (W o)) (X o) (Y o) ∂M.law) = mu M := by
  letI := hM.probability
  have hm : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  letI : IsFiniteMeasure (M.law.trim hm) := isFiniteMeasure_trim hm
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have mw : Measurable W := measurable_fst
  have mp : Measurable (fun o => M.pi (W o)) := hM.measurable_pi.comp mw
  have mht : Measurable (fun o => htTerm (M.pi (W o)) (X o) (Y1 o)) := (mx.mul my).div mp
  have bh : ∀ᵐ o ∂M.law, htTerm (M.pi (W o)) (X o) (Y1 o) ∈ Set.Icc 0 M.delta⁻¹ := by
    filter_upwards [hM.positivity] with o ho
    have hh := ht_binary_range (M.pi (W o)) M.delta ho.1 hM.delta_pos o.2.1 o.2.2.2
    exact ⟨hh.1, hh.2.le⟩
  have iht : Integrable (fun o => htTerm (M.pi (W o)) (X o) (Y1 o)) M.law :=
    memLp_one_iff_integrable.1 (memLp_of_bounded bh mht.aestronglyMeasurable 1)
  have bg : ∀ᵐ o ∂M.law, X o * Y1 o ∈ Set.Icc (0 : ℝ) 1 := by
    apply Filter.Eventually.of_forall
    intro o
    rcases o with ⟨w, x, y0, y1⟩
    cases x <;> cases y1 <;> norm_num [X, Y1, bit]
  have ig : Integrable (fun o => X o * Y1 o) M.law :=
    memLp_one_iff_integrable.1 (memLp_of_bounded bg (mx.mul my).aestronglyMeasurable 1)
  have hfun : (fun o => (M.pi (W o))⁻¹ * (X o * Y1 o)) =
      (fun o => htTerm (M.pi (W o)) (X o) (Y1 o)) := by
    funext o
    simp only [htTerm, div_eq_mul_inv]
    ring
  have mip : StronglyMeasurable[covariateSigma] (fun o => (M.pi (W o))⁻¹) :=
    (hM.measurable_pi.comp (comap_measurable W)).inv.stronglyMeasurable
  have hprod : Integrable ((fun o => (M.pi (W o))⁻¹) * (fun o => X o * Y1 o)) M.law := by
    change Integrable (fun o => (M.pi (W o))⁻¹ * (X o * Y1 o)) M.law
    rw [hfun]
    exact iht
  have hpull := condExp_mul_of_stronglyMeasurable_left mip hprod ig
  have hc : condExp covariateSigma M.law
      (fun o => htTerm (M.pi (W o)) (X o) (Y1 o)) =ᵐ[M.law] fun o => M.m (W o) := by
    change condExp covariateSigma M.law (fun o => (M.pi (W o))⁻¹ * (X o * Y1 o)) =ᵐ[M.law]
      (fun o => (M.pi (W o))⁻¹ * condExp covariateSigma M.law (fun o => X o * Y1 o) o) at hpull
    rw [hfun] at hpull
    filter_upwards [hpull, conditional_xy_factorization M hM, hM.positivity] with o h1 h2 ho
    rw [h1, h2]
    have hn : M.pi (W o) ≠ 0 := ne_of_gt (lt_trans hM.delta_pos ho.1)
    field_simp
  have hcons : (fun o => htTerm (M.pi (W o)) (X o) (Y o)) =
      (fun o => htTerm (M.pi (W o)) (X o) (Y1 o)) := by
    funext o
    simp only [htTerm, consistency_treated]
  rw [hcons]
  refine ⟨iht, ?_⟩
  calc
    _ = ∫ o, condExp covariateSigma M.law
        (fun o => htTerm (M.pi (W o)) (X o) (Y1 o)) o ∂M.law :=
      (integral_condExp hm).symm
    _ = ∫ o, M.m (W o) ∂M.law := integral_congr_ae hc
    _ = mu M := regression_mean M hM

/-- Proposition 2, p. 6 (T7), exact finite-sample part: HT is unbiased. -/
theorem ht_unbiased (M : Study) (hM : ValidStudy M) (n : ℕ) (hn : 0 < n) :
    (∫ a, ht M a ∂sampleLaw M n) = mu M := by
  letI := hM.probability
  unfold ht sampleLaw
  rw [iid_mean_integral M.law _ (ht_unit_facts M hM).1 n hn]
  exact (ht_unit_facts M hM).2

/-- Uniform(0,1) lower-tail probability for 0<=t<=1; the T1/T2/T4 generators. -/
theorem unitUniform_Iic (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    unitUniform (Set.Iic t) = ENNReal.ofReal t := by
  rw [unitUniform, Measure.restrict_apply measurableSet_Iic]
  have hi : Set.Iic t ∩ Set.Icc 0 1 = Set.Icc 0 t := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · intro h
      exact ⟨h.2.1, h.1⟩
    · intro h
      exact ⟨h.2, h.1, le_trans h.2 h1⟩
  rw [hi, Real.volume_Icc, sub_zero]

/-- Uniform(0,1) has no atoms; the continuous covariate assumption, p. 5. -/
theorem unitUniform_singleton (t : ℝ) : unitUniform {t} = 0 := by
  rw [unitUniform, Measure.restrict_apply (measurableSet_singleton t)]
  exact measure_mono_null Set.inter_subset_left Real.volume_singleton

/-- A uniform threshold generates the exact Bernoulli expectation; T1/T2/T4 assignment and outcome generators. -/
theorem unitUniform_bernE (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (f : Bool → ℝ) :
    (∫ u, f (decide (u ≤ p)) ∂unitUniform) = bernE p f := by
  have hf : (fun u : ℝ => f (decide (u ≤ p))) =
      (Set.Iic p).piecewise (fun _ => f true) (fun _ => f false) := by
    funext u
    by_cases h : u ≤ p <;> simp [h, Set.piecewise, Set.mem_Iic]
  rw [hf, integral_piecewise measurableSet_Iic (integrable_const _) (integrable_const _)]
  simp only [setIntegral_const, smul_eq_mul]
  rw [probReal_compl_eq_one_sub measurableSet_Iic]
  have hp : unitUniform.real (Set.Iic p) = p := by
    rw [Measure.real, unitUniform_Iic p h0 h1, ENNReal.toReal_ofReal h0]
  rw [hp]
  simp only [bernE]
  ring

namespace IntervalExample

/-- T1: rigorous logarithm bounds from Mathlib's positive series and remainder. This coarser enclosure still separates every count state. -/
theorem log_certified_bounds : (1681/100 : ℝ) < Real.log 20000000 ∧
    Real.log 20000000 < (3363/200 : ℝ) := by
  have hl1 := Real.sum_range_le_log_div (x := (1/3 : ℝ)) (by norm_num) (by norm_num) 6
  have hu1 := Real.log_div_le_sum_range_add (x := (1/3 : ℝ)) (by norm_num) (by norm_num) 6
  have hl2 := Real.sum_range_le_log_div (x := (12589/143661 : ℝ)) (by norm_num) (by norm_num) 3
  have hu2 := Real.log_div_le_sum_range_add (x := (12589/143661 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at hl1 hu1 hl2 hu2
  have heq : (20000000 : ℝ) = (2 : ℝ)^24 * (156250/131072) := by norm_num
  have hlog : Real.log 20000000 = 24 * Real.log 2 + Real.log (156250/131072) := by
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [hlog]
  constructor <;> linarith

/-- T1 rational count-state cutoff T_(k,s)>3363/200. The certified logarithm enclosure makes this exactly the failing-state test. -/
def certifiedCut (k s : ℕ) : Bool := decide
  (200 * 7840800 * (if s ≤ 39 then 39-s else s-39)^2 >
    3363 * (3920400*k + 1690000*(100-k)))

/-- T1 exact integer sum of all 1946 failing multinomial count-state masses, denominator 100^100. -/
def certifiedNumerator : ℕ := ∑ k ∈ Finset.range 101, ∑ s ∈ Finset.range (k+1),
  if certifiedCut k s then massNumerator k s else 0

/-- T1: the certified rational cutoff classifies exactly 1946 failing states. -/
theorem certified_state_count :
    (∑ k ∈ Finset.range 101, ∑ s ∈ Finset.range (k+1), if certifiedCut k s then (1 : ℕ) else 0)
      = 1946 := by decide

/-- T1: every state outside the rational failing set lies strictly below the logarithm's lower bound; this certifies exhaustive classification. -/
theorem certified_partition : ∀ k : Fin 101, ∀ s : Fin (k.val+1),
    certifiedCut k s = false →
      100 * 7840800 * (if s.val ≤ 39 then 39-s.val else s.val-39)^2 <
        1681 * (3920400*k.val + 1690000*(100-k.val)) := by decide

/-- T1: the exact failure-mass numerator is computed by kernel arithmetic
on the finite multinomial sum. -/
theorem certified_mass_exact : certifiedNumerator =
  11979291069795625472576722625601454579193931030581441019247695948117336197717708252113744670235734049700195915329948439938976976688794607547282140972800735873954434550061258658968400997158933003 := by
  simp only [certifiedNumerator, massNumerator, Nat.choose_eq_fast_choose]
  decide

/-- T1: the exact multinomial failure mass exceeds 119/10^9 and hence alpha=10^-7. -/
theorem certified_mass_gt : (119 : ℕ) * 100^100 < 10^9 * certifiedNumerator := by
  rw [certified_mass_exact]
  norm_num

end IntervalExample

namespace IntervalExample

/-- T1: cast the natural absolute difference into the squared real deviation
used by the printed interval, without truncated subtraction. -/
theorem count_deviation_sq (s : ℕ) :
    (((if s ≤ 39 then 39-s else s-39 : ℕ) : ℝ))^2 = ((s : ℝ)-39)^2 := by
  by_cases hs : s ≤ 39
  · rw [if_pos hs, Nat.cast_sub hs]
    norm_num
    ring
  · rw [if_neg hs, Nat.cast_sub (Nat.le_of_lt (Nat.lt_of_not_ge hs))]
    norm_num

/-- T1: the certified rational test is exactly strict exclusion of the
population mean by the printed radius in every possible count state. -/
theorem certified_cut_iff_exclusion (k s : ℕ) (hk : k ≤ 100) (hs : s ≤ k) :
    certifiedCut k s = true ↔
      xiK k * Real.log 20000000 / 200 < ((s : ℝ)-39)^2 / 65^2 := by
  have hx : 0 < xiK k := by
    dsimp [xiK]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hden : ((3920400*k + 1690000*(100-k) : ℕ) : ℝ) =
      3920400*(k : ℝ) + 1690000*(100-(k : ℝ)) := by
    push_cast [Nat.cast_sub hk]
    rfl
  by_cases hc : certifiedCut k s = true
  · have hN : 3363*(3920400*k + 1690000*(100-k)) <
        200*7840800*(if s ≤ 39 then 39-s else s-39)^2 := by
      simpa [certifiedCut] using hc
    have hR : (3363 : ℝ)*((3920400*k + 1690000*(100-k) : ℕ) : ℝ) <
        200*7840800*(((if s ≤ 39 then 39-s else s-39 : ℕ) : ℝ))^2 := by
      exact_mod_cast hN
    rw [hden, count_deviation_sq] at hR
    have hbound : xiK k * (3363/200) / 200 < ((s : ℝ)-39)^2 / 65^2 := by
      dsimp [xiK]
      nlinarith [hR]
    have hfail : xiK k * Real.log 20000000 / 200 < ((s : ℝ)-39)^2 / 65^2 := by
      calc
        _ < xiK k * (3363/200) / 200 := by
          gcongr
          exact log_certified_bounds.2
        _ < _ := hbound
    exact ⟨fun _ => hfail, fun _ => hc⟩
  · have hf : certifiedCut k s = false := by cases h : certifiedCut k s <;> simp_all
    have hN := certified_partition (⟨k, by omega⟩ : Fin 101)
      (⟨s, by change s < k+1; omega⟩ : Fin (k+1)) hf
    have hR : (100 : ℝ)*7840800*(((if s ≤ 39 then 39-s else s-39 : ℕ) : ℝ))^2 <
        1681*((3920400*k + 1690000*(100-k) : ℕ) : ℝ) := by
      exact_mod_cast hN
    rw [hden, count_deviation_sq] at hR
    have hbound : ((s : ℝ)-39)^2 / 65^2 < xiK k * (1681/100) / 200 := by
      dsimp [xiK]
      nlinarith [hR]
    have hno : ¬xiK k * Real.log 20000000 / 200 < ((s : ℝ)-39)^2 / 65^2 := by
      have hl : xiK k * (1681/100) / 200 < xiK k * Real.log 20000000 / 200 := by
        gcongr
        exact log_certified_bounds.1
      linarith
    exact iff_of_false hc hno

/-- T1: exactly 1946 of the 5151 count states strictly exclude the mean
using the actual natural logarithm. -/
theorem exact_failure_state_count :
    (∑ k ∈ Finset.range 101, ∑ s ∈ Finset.range (k+1),
      if xiK k * Real.log 20000000 / 200 < ((s : ℝ)-39)^2 / 65^2 then (1 : ℕ) else 0) =
        1946 := by
  classical
  calc
    _ = ∑ k ∈ Finset.range 101, ∑ s ∈ Finset.range (k+1),
        if certifiedCut k s then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro s hs
      simp only [← certified_cut_iff_exclusion k s (by simpa using Nat.le_of_lt_succ (Finset.mem_range.1 hk))
        (Nat.le_of_lt_succ (Finset.mem_range.1 hs))]
    _ = 1946 := certified_state_count


end IntervalExample

/-- Uniform(0,1) upper-tail probability for the T2 generator. -/
theorem unitUniform_Ici (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    unitUniform (Set.Ici t) = ENNReal.ofReal (1-t) := by
  rw [unitUniform, Measure.restrict_apply measurableSet_Ici]
  have hi : Set.Ici t ∩ Set.Icc 0 1 = Set.Icc t 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    constructor
    · intro h
      exact ⟨h.1, h.2.2⟩
    · intro h
      exact ⟨h.1, le_trans h0 h.1, h.2⟩
  rw [hi, Real.volume_Icc]

/-- Thresholding measurable real variables produces a measurable binary
variable, as in all three counterexample generators. -/
theorem measurable_threshold {A : Type*} [MeasurableSpace A]
    (f g : A → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => decide (f a ≤ g a)) := by
  apply measurable_to_bool
  convert measurableSet_le hf hg using 1
  ext a
  simp

/-- A study whose covariate marginal is Uniform(0,1) has continuous W,
the standing assumption on printed p. 5; no zero-law shortcut is used. -/
theorem atomless_of_uniform_marginal (nu : Measure Unit)
    (hm : Measure.map W nu = unitUniform) (w : ℝ) : nu {o | W o = w} = 0 := by
  have hw : Measurable W := measurable_fst
  have h := Measure.map_apply hw (measurableSet_singleton w) (μ := nu)
  rw [hm, unitUniform_singleton] at h
  exact h.symm

namespace IntervalExample

/-- T1's actual continuous generating map is measurable. -/
theorem measurable_generate : Measurable generate := by
  have ms : Measurable score := by
    unfold score
    exact measurable_const.ite measurableSet_Iic measurable_const
  have mx := measurable_threshold (fun z : ℝ × ℝ => z.2) (fun z => score z.1)
    measurable_snd (ms.comp measurable_fst)
  have my := measurable_threshold (fun z : ℝ × ℝ => z.1) (fun _ => (3/5 : ℝ))
    measurable_fst measurable_const
  exact measurable_fst.prodMk (mx.prodMk (measurable_const.prodMk my))

/-- T1's full-data law has covariate marginal Uniform(0,1). -/
theorem covariate_law : Measure.map W study.law = unitUniform := by
  change Measure.map W (Measure.map generate (unitUniform.prod unitUniform)) = unitUniform
  rw [Measure.map_map (show Measurable W from measurable_fst) measurable_generate]
  change Measure.map Prod.fst (unitUniform.prod unitUniform) = unitUniform
  simp

/-- T1: the concrete law is a probability law with continuous W
and population mean 3/5. -/
theorem probability_continuity_mean : IsProbabilityMeasure study.law ∧
    (∀ w : ℝ, study.law {o | W o = w} = 0) ∧ mu study = 3/5 := by
  have hp : IsProbabilityMeasure study.law := by dsimp [study]; infer_instance
  refine ⟨hp, atomless_of_uniform_marginal study.law covariate_law, ?_⟩
  have mb : Measurable bit := measurable_of_countable _
  have my : Measurable Y1 := mb.comp measurable_snd.snd.snd
  unfold mu
  change (∫ o, Y1 o ∂Measure.map generate (unitUniform.prod unitUniform)) = 3/5
  rw [integral_map measurable_generate.aemeasurable my.aestronglyMeasurable]
  change (∫ z : ℝ × ℝ, bit (decide (z.1 ≤ (3/5 : ℝ))) ∂unitUniform.prod unitUniform) = 3/5
  rw [integral_fun_fst (fun w : ℝ => bit (decide (w ≤ (3/5 : ℝ))))]
  simp only [probReal_univ, one_smul]
  rw [unitUniform_bernE (3/5) (by norm_num) (by norm_num) bit]
  norm_num [bernE, bit]

end IntervalExample

namespace ConditionalExample

/-- T2's continuous generating map is measurable. -/
theorem measurable_generate : Measurable generate := by
  have mx := measurable_threshold (fun z : ℝ × ℝ => z.2) (fun _ => (9/10 : ℝ))
    measurable_snd measurable_const
  have my := measurable_threshold (fun _ : ℝ × ℝ => (1/2 : ℝ)) (fun z => z.1)
    measurable_const measurable_fst
  exact measurable_fst.prodMk (mx.prodMk (measurable_const.prodMk my))

/-- T2's covariate is uniform on the real unit interval. -/
theorem covariate_law : Measure.map W study.law = unitUniform := by
  change Measure.map W (Measure.map generate (unitUniform.prod unitUniform)) = unitUniform
  rw [Measure.map_map (show Measurable W from measurable_fst) measurable_generate]
  change Measure.map Prod.fst (unitUniform.prod unitUniform) = unitUniform
  simp

/-- T2: the law has total mass one, continuous covariate,
and population mean 1/2. -/
theorem probability_continuity_mean : IsProbabilityMeasure study.law ∧
    (∀ w : ℝ, study.law {o | W o = w} = 0) ∧ mu study = 1/2 := by
  have hp : IsProbabilityMeasure study.law := by dsimp [study]; infer_instance
  refine ⟨hp, atomless_of_uniform_marginal study.law covariate_law, ?_⟩
  have mb : Measurable bit := measurable_of_countable _
  have my : Measurable Y1 := mb.comp measurable_snd.snd.snd
  unfold mu
  change (∫ o, Y1 o ∂Measure.map generate (unitUniform.prod unitUniform)) = 1/2
  rw [integral_map measurable_generate.aemeasurable my.aestronglyMeasurable]
  change (∫ z : ℝ × ℝ, bit (decide ((1/2 : ℝ) ≤ z.1)) ∂unitUniform.prod unitUniform) = 1/2
  rw [integral_fun_fst (fun w : ℝ => bit (decide ((1/2 : ℝ) ≤ w)))]
  simp only [probReal_univ, one_smul]
  have heq : (fun w : ℝ => bit (decide ((1/2 : ℝ) ≤ w))) =
      (Set.Ici (1/2 : ℝ)).indicator (fun _ => (1 : ℝ)) := by
    funext w
    by_cases h : (1/2 : ℝ) ≤ w <;> simp [bit, Set.indicator, Set.mem_Ici, h]
  rw [heq, integral_indicator measurableSet_Ici, setIntegral_const]
  rw [Measure.real, unitUniform_Ici (1/2) (by norm_num) (by norm_num)]
  norm_num

end ConditionalExample

namespace RegressionExample

/-- T4's continuous full-data map is measurable. -/
theorem measurable_generate : Measurable generate := by
  have ml := measurable_threshold (fun z : (ℝ × ℝ) × ℝ => z.1.1) (fun _ => (1/2 : ℝ))
    measurable_fst.fst measurable_const
  have mz := measurable_threshold (fun z : (ℝ × ℝ) × ℝ => z.1.2) (fun _ => (1/10 : ℝ))
    measurable_fst.snd measurable_const
  have mb : Measurable (fun z : (ℝ × ℝ) × ℝ =>
      decide (z.1.1 ≤ (1/2 : ℝ)) && decide (z.1.2 ≤ (1/10 : ℝ))) :=
    (measurable_of_countable (fun b : Bool × Bool => b.1 && b.2)).comp (ml.prodMk mz)
  have ms : Measurable score :=
    (measurable_of_countable scoreL).comp
      (measurable_threshold id (fun _ => (1/2 : ℝ)) measurable_id measurable_const)
  have mx := measurable_threshold (fun z : (ℝ × ℝ) × ℝ => z.2) (fun z => score z.1.1)
    measurable_snd (ms.comp measurable_fst.fst)
  exact measurable_fst.fst.prodMk (mx.prodMk (mb.prodMk mb))

/-- T4's covariate remains genuinely continuous; the eight-atom moments
do not replace its full-data population law. -/
theorem covariate_law : Measure.map W study.law = unitUniform := by
  change Measure.map W (Measure.map generate ((unitUniform.prod unitUniform).prod unitUniform)) = unitUniform
  rw [Measure.map_map (show Measurable W from measurable_fst) measurable_generate]
  change Measure.map (Prod.fst ∘ Prod.fst) ((unitUniform.prod unitUniform).prod unitUniform) = unitUniform
  rw [← Measure.map_map measurable_fst measurable_fst]
  simp

/-- T4: the law has mass one, continuous W and mean 1/20;
these are continuous-law facts rather than calculations on a disconnected table. -/
theorem probability_continuity_mean : IsProbabilityMeasure study.law ∧
    (∀ w : ℝ, study.law {o | W o = w} = 0) ∧ mu study = 1/20 := by
  have hp : IsProbabilityMeasure study.law := by dsimp [study]; infer_instance
  refine ⟨hp, atomless_of_uniform_marginal study.law covariate_law, ?_⟩
  have mb : Measurable bit := measurable_of_countable _
  have my : Measurable Y1 := mb.comp measurable_snd.snd.snd
  unfold mu
  change (∫ o, Y1 o ∂Measure.map generate ((unitUniform.prod unitUniform).prod unitUniform)) = 1/20
  rw [integral_map measurable_generate.aemeasurable my.aestronglyMeasurable]
  have heq : (fun z : (ℝ × ℝ) × ℝ => Y1 (generate z)) =
      (fun z => bit (decide (z.1.1 ≤ (1/2 : ℝ))) * bit (decide (z.1.2 ≤ (1/10 : ℝ)))) := by
    funext z
    dsimp [Y1, generate]
    cases decide (z.1.1 ≤ (1/2 : ℝ)) <;> cases decide (z.1.2 ≤ (1/10 : ℝ)) <;> simp [bit]
  rw [heq, integral_fun_fst (fun z : ℝ × ℝ =>
    bit (decide (z.1 ≤ (1/2 : ℝ))) * bit (decide (z.2 ≤ (1/10 : ℝ))))]
  simp only [probReal_univ, one_smul]
  rw [integral_prod_mul (fun w : ℝ => bit (decide (w ≤ (1/2 : ℝ))))
    (fun u : ℝ => bit (decide (u ≤ (1/10 : ℝ))))]
  rw [unitUniform_bernE (1/2) (by norm_num) (by norm_num) bit,
    unitUniform_bernE (1/10) (by norm_num) (by norm_num) bit]
  norm_num [bernE, bit]

end RegressionExample

namespace RegressionExample

/-- T4 actual fitted functions: the tie-breaking empirical rule always
selects theta=0 on both training folds. Evaluation folds
are the first floor(n/2) observations and the remainder, as on printed p. 7. -/
def fits (n : ℕ) : CrossFit n where
  fold i := decide (n/2 ≤ i.val)
  g _ _ := prediction 0
  measurable_g _ := by
    classical
    have hm : Measurable (prediction 0) := by
      have h : Measurable (fun w : ℝ => if w ≤ (1/2 : ℝ) then (1/2 : ℝ) else 0) :=
        Measurable.ite measurableSet_Iic measurable_const measurable_const
      have heq : prediction 0 = (fun w : ℝ => if w ≤ (1/2 : ℝ) then (1/2 : ℝ) else 0) := by
        funext w
        by_cases hw : w ≤ (1/2 : ℝ)
        · simp [prediction, predictionL, hw]
        · simp [prediction, predictionL, hw]
      rw [heq]
      exact h
    exact hm.comp measurable_snd
  opposite_fold _ _ _ _ := rfl

/-- T4's actual cross-fitted estimator equals the fixed-prediction sample
mean for every sample. -/
theorem fits_adjusted (n : ℕ) (a : Sample n) :
    adjusted study (fits n) a = fixedAdjusted study (prediction 0) a := rfl

/-- T4: both fitted regressions have zero L2 prediction error at every n,
hence converge in L2 in probability to g_*. -/
theorem fits_l2_convergence (j : Bool) : L2InProbability study fits j (prediction 0) := by
  intro eps heps
  have hf : (fun n => (sampleLaw study n
      {a | eps < l2Sq study (fun w => (fits n).g j a w - prediction 0 w)}).toReal) =
      (fun _ => (0 : ℝ)) := by
    funext n
    simp [fits, l2Sq, not_lt_of_ge heps.le]
  rw [hf]
  exact tendsto_const_nhds

/-- T4: the deterministic partition has asymptotically equal fold sizes,
which discharges the paper's "roughly equal size" condition. -/
theorem fits_balanced : Balanced fits := by
  have hc0 (n : ℕ) :
      (Finset.univ.filter (fun i => (fits n).fold i = false)).card = n/2 := by
    have heq : Finset.univ.filter (fun i => (fits n).fold i = false) =
        Finset.univ.filter (fun i : Fin n => i.val < n/2) := by
      ext i
      simp [fits, not_le]
    rw [heq, Fin.card_filter_val_lt, Nat.min_eq_right (Nat.div_le_self _ _)]
  have hc1 (n : ℕ) :
      (Finset.univ.filter (fun i => (fits n).fold i = true)).card = n - n/2 := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin n => (fits n).fold i = false)
    simp only [Finset.card_univ, Fintype.card_fin, hc0] at h
    have heq : Finset.univ.filter (fun i => ¬(fits n).fold i = false) =
        Finset.univ.filter (fun i => (fits n).fold i = true) := by
      ext i
      cases h : (fits n).fold i <;> simp [h]
    rw [heq] at h
    omega
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  intro j
  have hl : Tendsto (fun n : ℕ => (1/2 : ℝ) - 1/(n : ℝ)) atTop (nhds (1/2)) := by
    simpa using (tendsto_const_nhds (x := (1/2 : ℝ))).sub hinv
  have hu : Tendsto (fun n : ℕ => (1/2 : ℝ) + 1/(n : ℝ)) atTop (nhds (1/2)) := by
    simpa using (tendsto_const_nhds (x := (1/2 : ℝ))).add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  all_goals
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have h1 : 2*(n/2) ≤ n := by omega
    have h2 : n < 2*(n/2) + 2 := by omega
    have h1R : (2 : ℝ)*((n/2 : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
    have h2R : (n : ℝ) < 2*((n/2 : ℕ) : ℝ)+2 := by exact_mod_cast h2
    cases j <;> simp only [hc0, hc1, Nat.cast_sub (Nat.div_le_self n 2)]
    all_goals
      first
      | apply (le_div_iff₀ hnR).2
      | apply (div_le_iff₀ hnR).2
      field_simp [ne_of_gt hnR]
      nlinarith


end RegressionExample

/-- Uniform(0,1) strict lower-tail probability, for the T2 covariate event. -/
theorem unitUniform_Iio (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    unitUniform (Set.Iio t) = ENNReal.ofReal t := by
  rw [unitUniform, Measure.restrict_apply measurableSet_Iio]
  have hi : Set.Iio t ∩ Set.Icc 0 1 = Set.Ico 0 t := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    constructor
    · intro h
      exact ⟨h.2.1, h.1⟩
    · intro h
      exact ⟨h.2, h.1, le_trans h.2.le h1⟩
  rw [hi, Real.volume_Ico, sub_zero]

namespace ConditionalExample

/-- T2: the exceptional covariate event has exactly probability 2^-100
under the actual continuous sample law. -/
theorem covariate_event_mass : sampleLaw study 100 E = ENNReal.ofReal ((1/2 : ℝ)^100) := by
  letI := probability_continuity_mean.1
  have hh : study.law {o | W o < (1/2 : ℝ)} = ENNReal.ofReal (1/2) := by
    have h := Measure.map_apply (show Measurable W from measurable_fst)
      (measurableSet_Iio : MeasurableSet (Set.Iio (1/2 : ℝ))) (μ := study.law)
    rw [covariate_law, unitUniform_Iio (1/2) (by norm_num) (by norm_num)] at h
    exact h.symm
  have heq : E = Set.univ.pi (fun _ : Fin 100 => {o | W o < (1/2 : ℝ)}) := by
    ext a
    simp [E, Set.mem_pi]
  rw [heq, sampleLaw, Measure.pi_pi]
  simp only [hh, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by norm_num)]

/-- T2: the covariate event has strictly positive actual probability. -/
theorem covariate_event_positive : 0 < sampleLaw study 100 E := by
  rw [covariate_event_mass]
  exact ENNReal.ofReal_pos.2 event_positive

/-- T2: xi is identically 100/81 on samples of size 100. -/
theorem xi_value (a : Sample 100) : xi study a = 100/81 := by
  norm_num [xi, study]

end ConditionalExample

namespace RegressionExample

/-- T4: on actual sampled observations, the observed outcome is zero in
the upper covariate half. -/
theorem upper_outcome_zero : ∀ᵐ o ∂study.law, (1/2 : ℝ) < W o → Y o = 0 := by
  change ∀ᵐ o ∂Measure.map generate ((unitUniform.prod unitUniform).prod unitUniform),
    (1/2 : ℝ) < W o → Y o = 0
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
  have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have my : Measurable Y := ((measurable_const.sub mx).mul my0).add (mx.mul my1)
  apply (ae_map_iff measurable_generate.aemeasurable (by
    apply MeasurableSet.imp
    · exact measurableSet_lt measurable_const (show Measurable W from measurable_fst)
    · exact measurableSet_eq_fun my measurable_const)).2
  apply Filter.Eventually.of_forall
  intro z hz
  have hh : ¬z.1.1 ≤ (1/2 : ℝ) := not_le_of_gt hz
  have hl : decide (z.1.1 ≤ (1/2 : ℝ)) = false := decide_eq_false hh
  simp only [generate, hl, Bool.false_and]
  simp [Y, Y0, Y1, X, bit]

/-- T4: the concrete zero-parameter fits minimize the actual empirical
criterion on both training folds almost surely, including empty treatment
folds. -/
theorem fits_empirical_minimizer (n : ℕ) (j : Bool) :
    ∀ᵐ a ∂sampleLaw study n, ∀ theta,
      empiricalRisk study (Finset.univ.filter (fun i => (fits n).fold i ≠ j)) a (prediction 0) ≤
      empiricalRisk study (Finset.univ.filter (fun i => (fits n).fold i ≠ j)) a (prediction theta) := by
  letI := probability_continuity_mean.1
  have hall : ∀ᵐ a ∂sampleLaw study n, ∀ i, (1/2 : ℝ) < W (a i) → Y (a i) = 0 := by
    exact ae_all_iff.2 (fun i =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => study.law) (i := i)).eventually upper_outcome_zero)
  filter_upwards [hall] with a ha
  intro theta
  unfold empiricalRisk
  apply Finset.sum_le_sum
  intro i hi
  by_cases hw : W (a i) ≤ (1/2 : ℝ)
  · have hh : prediction theta (W (a i)) = prediction 0 (W (a i)) := by
      unfold prediction predictionL
      rw [decide_eq_true hw]
      simp
    rw [hh]
  · have hy := ha i (lt_of_not_ge hw)
    have hpt : prediction theta (W (a i)) = theta := by
      unfold prediction predictionL
      rw [decide_eq_false hw]
      simp
    have hp0 : prediction 0 (W (a i)) = 0 := by
      unfold prediction predictionL
      rw [decide_eq_false hw]
      simp
    have hpi : study.pi (W (a i)) = 3/4 := by
      change scoreL (decide (W (a i) ≤ (1/2 : ℝ))) = 3/4
      rw [decide_eq_false hw]
      rfl
    rw [hy, hpt, hp0, hpi]
    have hx : 0 ≤ X (a i) := by
      unfold X bit
      split <;> norm_num
    norm_num
    positivity

end RegressionExample

namespace ConditionalExample

/-- T2: the generated treated outcome agrees almost surely with its
covariate threshold. -/
theorem potential_outcome_version : ∀ᵐ o ∂study.law,
    Y1 o = bit (decide ((1/2 : ℝ) ≤ W o)) := by
  have mb : Measurable bit := measurable_of_countable _
  have my : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have mt := mb.comp (measurable_threshold (fun _ : Unit => (1/2 : ℝ)) W
    measurable_const measurable_fst)
  change ∀ᵐ o ∂Measure.map generate (unitUniform.prod unitUniform), _
  apply (ae_map_iff measurable_generate.aemeasurable (measurableSet_eq_fun my mt)).2
  exact ae_of_all _ (fun _ => rfl)

/-- T2: E is measurable with respect to the full covariate vector, so
conditional expectation can be localized to this positive-probability event. -/
theorem covariate_event_measurable : MeasurableSet[sampleCovariateSigma 100] E := by
  let S : Set (Fin 100 → ℝ) := {w | ∀ i, w i < (1/2 : ℝ)}
  have hs : MeasurableSet S := by
    have heq : S = ⋂ i : Fin 100, {w : Fin 100 → ℝ | w i < (1/2 : ℝ)} := by
      ext w
      simp [S]
    rw [heq]
    exact MeasurableSet.iInter (fun i => measurableSet_lt (measurable_pi_apply i) measurable_const)
  have h : Measurable[sampleCovariateSigma 100] (covariates (n := 100)) :=
    comap_measurable _
  exact h hs

/-- T2: on E the conditional probability of the printed population-centred
tail event is one. This proves the failed centring step on
the continuous law. -/
theorem conditional_event_tail :
    ∀ᵐ a ∂(sampleLaw study 100).restrict E,
      condExp (sampleCovariateSigma 100) (sampleLaw study 100)
        (fun b => if printedRadius study (1/20) b ≤ |ht study b - mu study| then (1 : ℝ) else 0) a
        = 1 := by
  classical
  letI := probability_continuity_mean.1
  let P := sampleLaw study 100
  have hcov : Measurable (covariates (n := 100)) :=
    measurable_pi_lambda (fun i => measurable_fst.comp (measurable_pi_apply i))
  have hle : (sampleCovariateSigma 100) ≤ (inferInstance : MeasurableSpace (Sample 100)) := hcov.comap_le
  letI : IsFiniteMeasure (P.trim hle) := isFiniteMeasure_trim hle
  have hE : MeasurableSet[(sampleCovariateSigma 100)] E := covariate_event_measurable
  have hEg : MeasurableSet E := hle _ hE
  have hradius (a : Sample 100) : printedRadius study (1/20) a = Real.sqrt (Real.log 40/162) := by
    unfold printedRadius
    rw [xi_value]
    congr 1
    norm_num <;> ring
  let f : Sample 100 → ℝ := fun a =>
    if printedRadius study (1/20) a ≤ |ht study a - mu study| then 1 else 0
  have mf : Measurable f := by
    have mb : Measurable bit := measurable_of_countable _
    have mx : Measurable X := mb.comp measurable_snd.fst
    have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
    have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
    have my : Measurable Y := ((measurable_const.sub mx).mul my0).add (mx.mul my1)
    have mht : Measurable (ht study (n := 100)) := by
      unfold ht htTerm
      exact (Finset.measurable_sum Finset.univ (fun i _ =>
        ((mx.comp (measurable_pi_apply i)).mul (my.comp (measurable_pi_apply i))).div_const (9/10))).div_const 100
    dsimp [f]
    simp_rw [hradius]
    exact measurable_const.ite (measurableSet_le measurable_const (mht.sub_const (mu study)).abs) measurable_const
  have hf : Integrable f P := by
    apply memLp_one_iff_integrable.1 (memLp_of_bounded (a := 0) (b := 1) _ mf.aestronglyMeasurable 1)
    exact ae_of_all _ (fun a => by dsimp [f]; split <;> norm_num)
  have hall : ∀ᵐ a ∂P, ∀ i, Y1 (a i) = bit (decide ((1/2 : ℝ) ≤ W (a i))) :=
    ae_all_iff.2 (fun i =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 100 => study.law) (i := i)).eventually potential_outcome_version)
  have heq : E.indicator f =ᵐ[P] E.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hall] with a ha
    by_cases he : a ∈ E
    · have hy (i : Fin 100) : Y1 (a i) = 0 := by
        rw [ha i]
        have hw : ¬(1/2 : ℝ) ≤ W (a i) := not_le_of_gt (he i)
        rw [decide_eq_false hw]
        simp [bit]
      have hzero : ht study a = 0 := by
        unfold ht htTerm
        simp only [consistency_treated, hy, mul_zero, zero_div, Finset.sum_const_zero]
      have htail : printedRadius study (1/20) a ≤ |ht study a - mu study| := by
        rw [hradius, hzero, probability_continuity_mean.2.2]
        simpa only [zero_sub, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)] using radius_lt_half.le
      rw [Set.indicator_of_mem he, Set.indicator_of_mem he]
      exact if_pos htail
    · simp [Set.indicator_of_notMem he]
  have hc : condExp (sampleCovariateSigma 100) P (E.indicator f) =ᵐ[P] E.indicator (fun _ => (1 : ℝ)) := by
    calc
      condExp (sampleCovariateSigma 100) P (E.indicator f) =ᵐ[P]
          condExp (sampleCovariateSigma 100) P (E.indicator (fun _ => (1 : ℝ))) :=
        condExp_congr_ae heq
      _ = _ := condExp_of_stronglyMeasurable hle (stronglyMeasurable_const.indicator hE)
        ((integrable_const 1).indicator hEg)
  have hh := (condExp_indicator hf hE).symm.trans hc
  filter_upwards [ae_restrict_of_ae hh, ae_restrict_mem hEg] with a ha he
  simpa only [Set.indicator_of_mem he] using ha

end ConditionalExample

/-- Independence transfers through a measurable generating map. This
supporting probability-law bridge is used for T2's independent uniform
covariate and assignment draw. -/
theorem indepFun_map_iff {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (nu : Measure A) [IsProbabilityMeasure nu]
    (gen : A → B) (f : B → C) (g : B → D)
    (hgen : Measurable gen) (hf : Measurable f) (hg : Measurable g) :
    IndepFun f g (Measure.map gen nu) ↔ IndepFun (f ∘ gen) (g ∘ gen) nu := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable,
    indepFun_iff_map_prod_eq_prod_map_map (hf.comp hgen).aemeasurable (hg.comp hgen).aemeasurable]
  rw [Measure.map_map (hf.prodMk hg) hgen, Measure.map_map hf hgen, Measure.map_map hg hgen]
  rfl

/-- Conditional independence is unchanged by almost-sure replacement of
the outcome. This allows T2's potential outcome to be replaced by its
covariate-measurable threshold under the actual generated law. -/
theorem condIndepFun_congr_left {A : Type*} (s : MeasurableSpace A)
    {mA : MeasurableSpace A} [StandardBorelSpace A]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (hle : s ≤ mA) (f f' g : A → ℝ)
    (hf : Measurable f) (hf' : Measurable f') (hg : Measurable g)
    (heq : f =ᵐ[nu] f') (hi : CondIndepFun s hle f' g nu) : CondIndepFun s hle f g nu := by
  classical
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg]
  intro u v hu hv
  have h1 : (f ⁻¹' u).indicator (fun _ => (1 : ℝ)) =ᵐ[nu]
      (f' ⁻¹' u).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [heq] with a ha
    change (if f a ∈ u then (1 : ℝ) else 0) = (if f' a ∈ u then (1 : ℝ) else 0)
    rw [ha]
  have h2 : ((f ⁻¹' u) ∩ (g ⁻¹' v)).indicator (fun _ => (1 : ℝ)) =ᵐ[nu]
      ((f' ⁻¹' u) ∩ (g ⁻¹' v)).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [heq] with a ha
    have hm : a ∈ (f ⁻¹' u) ∩ (g ⁻¹' v) ↔ a ∈ (f' ⁻¹' u) ∩ (g ⁻¹' v) := by
      change (f a ∈ u ∧ g a ∈ v) ↔ (f' a ∈ u ∧ g a ∈ v)
      rw [ha]
    by_cases h : a ∈ (f ⁻¹' u) ∩ (g ⁻¹' v)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.mp h)]
    · have h' : a ∉ (f' ⁻¹' u) ∩ (g ⁻¹' v) := fun hh => h (hm.mpr hh)
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  have hbase := (condIndepFun_iff_condExp_inter_preimage_eq_mul hf' hg).1 hi u v hu hv
  filter_upwards [condExp_congr_ae (m := s) h1, condExp_congr_ae (m := s) h2, hbase]
    with a ha hb hc
  rw [hb, hc, ha]

namespace ConditionalExample

/-- T2: Y(0) is zero almost surely under the generated population law. -/
theorem zero_potential_version : Y0 =ᵐ[study.law] fun _ => (0 : ℝ) := by
  have mb : Measurable bit := measurable_of_countable _
  have my : Measurable Y0 := mb.comp measurable_snd.snd.fst
  change ∀ᵐ o ∂Measure.map generate (unitUniform.prod unitUniform), Y0 o = 0
  apply (ae_map_iff measurable_generate.aemeasurable (measurableSet_eq_fun my measurable_const)).2
  exact ae_of_all _ (fun _ => by simp [generate, Y0, bit])

/-- T2: all standing assumptions on p. 5 hold for the concrete law. The
constant score 9/10 is its actual conditional treatment mean; both potential
outcomes are conditionally independent of treatment given the covariate. -/
theorem study_valid : ValidStudy study := by
  letI := probability_continuity_mean.1
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
  have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have mw : Measurable W := measurable_fst
  have hle : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := mw.comap_le
  letI : IsFiniteMeasure (study.law.trim hle) := isFiniteMeasure_trim hle
  let r : Unit → ℝ := fun o => bit (decide ((1/2 : ℝ) ≤ W o))
  have mt : Measurable (fun w : ℝ => bit (decide ((1/2 : ℝ) ≤ w))) :=
    mb.comp (measurable_threshold (fun _ : ℝ => (1/2 : ℝ)) id measurable_const measurable_id)
  have mr : Measurable r := mt.comp mw
  have mrs : Measurable[covariateSigma] r := mt.comp (comap_measurable W)
  have hr : Integrable r study.law := by
    apply memLp_one_iff_integrable.1 (memLp_of_bounded (a := 0) (b := 1) _ mr.aestronglyMeasurable 1)
    exact ae_of_all _ (fun o => by dsimp [r]; cases decide ((1/2 : ℝ) ≤ W o) <;> norm_num [bit])
  have mind : Measurable (fun u : ℝ => bit (decide (u ≤ (9/10 : ℝ)))) :=
    mb.comp (measurable_threshold id (fun _ : ℝ => (9/10 : ℝ)) measurable_id measurable_const)
  have hi : IndepFun X W study.law := by
    apply (indepFun_map_iff (unitUniform.prod unitUniform) generate X W measurable_generate mx mw).2
    simpa only [Function.comp_def, generate, X, W, id_eq] using
      (indepFun_prod (μ := unitUniform) (ν := unitUniform) measurable_id mind).symm
  have hmean : (∫ o, X o ∂study.law) = 9/10 := by
    change (∫ o, X o ∂Measure.map generate (unitUniform.prod unitUniform)) = 9/10
    rw [integral_map measurable_generate.aemeasurable mx.aestronglyMeasurable]
    change (∫ z : ℝ × ℝ, bit (decide (z.2 ≤ (9/10 : ℝ))) ∂unitUniform.prod unitUniform) = 9/10
    rw [integral_fun_snd (fun u : ℝ => bit (decide (u ≤ (9/10 : ℝ))))]
    simp only [probReal_univ, one_smul]
    rw [unitUniform_bernE (9/10) (by norm_num) (by norm_num) bit]
    norm_num [bernE, bit]
  refine ⟨probability_continuity_mean.1, probability_continuity_mean.2.1,
    measurable_const, ?_, by norm_num [study], ae_of_all _ (fun _ => score_positivity),
    ?_, ?_, ?_, ?_, ?_⟩
  · change Measurable (fun w : ℝ => if (1/2 : ℝ) ≤ w then (1 : ℝ) else 0)
    exact measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const
  · have hind : Indep (MeasurableSpace.comap X inferInstance) covariateSigma study.law := hi
    have hc := condExp_indep_eq mx.comap_le hle (comap_measurable X).stronglyMeasurable hind
    rw [hmean] at hc
    exact hc
  · calc
      condExp covariateSigma study.law Y1 =ᵐ[study.law] condExp covariateSigma study.law r :=
        condExp_congr_ae potential_outcome_version
      _ = _ := by
        rw [condExp_of_stronglyMeasurable hle mrs.stronglyMeasurable hr]
        funext o
        simp [r, study, bit]
  · exact ae_of_all _ (fun o => by dsimp [study]; split <;> norm_num)
  · exact condIndepFun_congr_left covariateSigma study.law hle Y0 (fun _ => 0) X
      my0 measurable_const mx zero_potential_version (condIndepFun_const_left 0 X)
  · exact condIndepFun_congr_left covariateSigma study.law hle Y1 r X
      my1 mr mx potential_outcome_version (condIndepFun_of_measurable_left mrs mx)

/-- T2: on a covariate event of probability 2^{-100}, the conditional tail
probability is 1, strictly exceeding the printed RHS alpha=1/20. This refutes
the proof's conditional centring step, without asserting unconditional 95% undercoverage. -/
theorem counterexample : ValidStudy study ∧ mu study = 1/2 ∧
    sampleLaw study 100 E = ENNReal.ofReal ((1/2 : ℝ)^100) ∧
    ∀ᵐ a ∂(sampleLaw study 100).restrict E,
      condExp (sampleCovariateSigma 100) (sampleLaw study 100)
        (fun b => if printedRadius study (1/20) b ≤ |ht study b - mu study| then (1 : ℝ) else 0) a
        = 1 ∧ (1 : ℝ) > 1/20 := by
  exact ⟨study_valid, probability_continuity_mean.2.2, covariate_event_mass,
    conditional_event_tail.mono (fun _ h => ⟨h, by norm_num⟩)⟩

end ConditionalExample

/-- T7 finite lemma: positivity and binary outcomes give finite second
moments for the observed HT summand on the actual population probability law. -/
theorem ht_unit_memLp (M : Study) (hM : ValidStudy M) :
    MemLp (fun o => htTerm (M.pi (W o)) (X o) (Y o)) 2 M.law := by
  letI := hM.probability
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have mp : Measurable (fun o => M.pi (W o)) := hM.measurable_pi.comp measurable_fst
  have hh : (fun o => htTerm (M.pi (W o)) (X o) (Y o)) =
      (fun o => htTerm (M.pi (W o)) (X o) (Y1 o)) := by
    funext o
    simp only [htTerm, consistency_treated]
  rw [hh]
  apply memLp_of_bounded (a := 0) (b := M.delta⁻¹)
  · filter_upwards [hM.positivity] with o ho
    have h := ht_binary_range (M.pi (W o)) M.delta ho.1 hM.delta_pos o.2.1 o.2.2.2
    exact ⟨h.1, h.2.le⟩
  · exact ((mx.mul my).div mp).aestronglyMeasurable

/-- T7 finite lemma: the exact second moment of an HT summand is E[m(W)/pi(W)]. -/
theorem ht_second_moment (M : Study) (hM : ValidStudy M) :
    (∫ o, (htTerm (M.pi (W o)) (X o) (Y o))^2 ∂M.law) =
      ∫ o, M.m (W o) / M.pi (W o) ∂M.law := by
  letI := hM.probability
  have hm : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) := measurable_fst.comap_le
  letI : IsFiniteMeasure (M.law.trim hm) := isFiniteMeasure_trim hm
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have hi := (ht_unit_memLp M hM).integrable_sq
  have heq : (fun o => (htTerm (M.pi (W o)) (X o) (Y o))^2) =
      (fun o => (M.pi (W o))⁻¹^2 * (X o * Y1 o)) := by
    funext o
    simp only [htTerm, consistency_treated]
    rcases o with ⟨w,x,y0,y1⟩
    cases x <;> cases y1 <;> simp [X, Y1, bit, div_eq_mul_inv]
  have bg : ∀ᵐ o ∂M.law, X o * Y1 o ∈ Set.Icc (0 : ℝ) 1 := by
    apply Filter.Eventually.of_forall
    intro o
    rcases o with ⟨w,x,y0,y1⟩
    cases x <;> cases y1 <;> norm_num [X, Y1, bit]
  have ig : Integrable (fun o => X o * Y1 o) M.law :=
    memLp_one_iff_integrable.1 (memLp_of_bounded bg (mx.mul my).aestronglyMeasurable 1)
  have mip : StronglyMeasurable[covariateSigma] (fun o => (M.pi (W o))⁻¹^2) :=
    ((hM.measurable_pi.comp (comap_measurable W)).inv.pow_const 2).stronglyMeasurable
  have hprod : Integrable ((fun o => (M.pi (W o))⁻¹^2) * (fun o => X o * Y1 o)) M.law := by
    change Integrable (fun o => (M.pi (W o))⁻¹^2 * (X o * Y1 o)) M.law
    rw [← heq]
    exact hi
  have hpull := condExp_mul_of_stronglyMeasurable_left mip hprod ig
  have hc : condExp covariateSigma M.law
      (fun o => (htTerm (M.pi (W o)) (X o) (Y o))^2) =ᵐ[M.law]
        fun o => M.m (W o) / M.pi (W o) := by
    change condExp covariateSigma M.law (fun o => (M.pi (W o))⁻¹^2 * (X o * Y1 o)) =ᵐ[M.law]
      (fun o => (M.pi (W o))⁻¹^2 * condExp covariateSigma M.law (fun o => X o * Y1 o) o) at hpull
    rw [← heq] at hpull
    filter_upwards [hpull, conditional_xy_factorization M hM, hM.positivity] with o h1 h2 ho
    rw [h1, h2]
    have hp : M.pi (W o) ≠ 0 := ne_of_gt (lt_trans hM.delta_pos ho.1)
    field_simp
  calc
    _ = ∫ o, condExp covariateSigma M.law
        (fun o => (htTerm (M.pi (W o)) (X o) (Y o))^2) o ∂M.law :=
      (integral_condExp hm).symm
    _ = _ := integral_congr_ae hc

/-- T7 finite lemma: exact HT sample variance and the uniform bound 1/(n delta). -/
theorem ht_variance (M : Study) (hM : ValidStudy M) (n : ℕ) (hn : 0 < n) :
    variance (ht M (n := n)) (sampleLaw M n) =
      ((∫ o, M.m (W o) / M.pi (W o) ∂M.law) - (mu M)^2) / n ∧
    variance (ht M (n := n)) (sampleLaw M n) ≤ 1 / (n * M.delta) := by
  letI := hM.probability
  have htmem := ht_unit_memLp M hM
  have hv : variance (ht M (n := n)) (sampleLaw M n) =
      ((∫ o, M.m (W o) / M.pi (W o) ∂M.law) - (mu M)^2) / n := by
    unfold ht sampleLaw
    rw [iid_mean_variance M.law _ htmem n hn, variance_eq_sub htmem]
    simp only [Pi.pow_apply]
    rw [ht_second_moment M hM, (ht_unit_facts M hM).2]
  refine ⟨hv, ?_⟩
  have mp : Measurable (fun o => M.pi (W o)) := hM.measurable_pi.comp measurable_fst
  have mm : Measurable (fun o => M.m (W o)) := hM.measurable_m.comp measurable_fst
  have hb : ∀ᵐ o ∂M.law, M.m (W o) / M.pi (W o) ∈ Set.Icc 0 M.delta⁻¹ := by
    filter_upwards [hM.positivity, hM.regression_range] with o hp hm
    have hp0 := lt_trans hM.delta_pos hp.1
    refine ⟨div_nonneg hm.1 hp0.le, ?_⟩
    calc
      M.m (W o) / M.pi (W o) ≤ 1 / M.pi (W o) := div_le_div_of_nonneg_right hm.2 hp0.le
      _ ≤ M.delta⁻¹ := by
        simpa [one_div] using ((inv_lt_inv₀ hp0 hM.delta_pos).2 hp.1).le
  have hi : Integrable (fun o => M.m (W o) / M.pi (W o)) M.law :=
    memLp_one_iff_integrable.1 (memLp_of_bounded hb (mm.div mp).aestronglyMeasurable 1)
  have hle : (∫ o, M.m (W o) / M.pi (W o) ∂M.law) ≤ M.delta⁻¹ := by
    simpa using integral_mono_ae hi (integrable_const M.delta⁻¹) (hb.mono fun _ h => h.2)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [hv]
  calc
    _ ≤ M.delta⁻¹ / n := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (mu M)]) hnR.le
    _ = _ := by field_simp

/-- T7 finite lemma: HT sample averages have finite second moments. -/
theorem ht_sample_memLp (M : Study) (hM : ValidStudy M) (n : ℕ) :
    MemLp (ht M (n := n)) 2 (sampleLaw M n) := by
  letI := hM.probability
  have hi : ∀ i : Fin n, MemLp
      (fun a : Sample n => htTerm (M.pi (W (a i))) (X (a i)) (Y (a i))) 2 (sampleLaw M n) :=
    fun i => (ht_unit_memLp M hM).comp_measurePreserving (measurePreserving_eval (fun _ => M.law) i)
  have hs := memLp_finsetSum Finset.univ (fun i _ => hi i)
  have heq : ht M (n := n) = fun a : Sample n =>
      (∑ i, htTerm (M.pi (W (a i))) (X (a i)) (Y (a i))) * (n : ℝ)⁻¹ := by
    funext a
    exact div_eq_mul_inv _ _
  rw [heq]
  exact hs.mul_const (n : ℝ)⁻¹

/-- T7 finite Chebyshev bound uniform in every n and valid population with
its given positivity constant. This is stronger than the required tightness. -/
theorem ht_chebyshev (M : Study) (hM : ValidStudy M) (n : ℕ) (hn : 0 < n)
    (C : ℝ) (hC : 0 < C) :
    (sampleLaw M n {a | C < Real.sqrt n * |ht M a - mu M|}).toReal ≤
      1 / (M.delta * C^2) := by
  letI := hM.probability
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hv := (ht_variance M hM n hn).2
  have hm := meas_ge_le_variance_div_sq (ht_sample_memLp M hM n) (div_pos hC hs)
  rw [ht_unbiased M hM n hn] at hm
  have hr : (sampleLaw M n).real {a | C / Real.sqrt n ≤ |ht M a - mu M|} ≤
      variance (ht M (n := n)) (sampleLaw M n) / (C / Real.sqrt n)^2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at h
    exact h
  calc
    _ ≤ (sampleLaw M n).real {a | C / Real.sqrt n ≤ |ht M a - mu M|} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro a ha
      exact ((div_lt_iff₀ hs).2 (by simpa [mul_comm] using ha)).le
    _ ≤ _ := hr
    _ ≤ (1 / (n * M.delta)) / (C / Real.sqrt n)^2 :=
      div_le_div_of_nonneg_right hv (sq_nonneg _)
    _ = 1 / (M.delta * C^2) := by
      rw [div_pow, Real.sq_sqrt hnR.le]
      field_simp

/-- Proposition 2, p. 6 (T7), uniform root-n part separately: the Chebyshev
constant is chosen before the population and sample size at a common delta. -/
theorem ht_uniform_root_n (delta : ℝ) (hd : 0 < delta) : UniformRootN delta := by
  intro eps heps
  let C := Real.sqrt (1 / (delta * eps))
  have hC : 0 < C := Real.sqrt_pos.2 (by positivity)
  refine ⟨C, hC, ?_⟩
  intro M hM heq n hn
  have h := ht_chebyshev M hM n hn C hC
  rw [heq] at h
  have hsq : C^2 = 1 / (delta * eps) := Real.sq_sqrt (by positivity)
  have hr : 1 / (delta * C^2) = eps := by
    rw [hsq]
    field_simp
  exact h.trans_eq hr

/-- The i.i.d. sample-mean CLT, used for Proposition 2 and the T4 concrete
asymptotic variance comparison. The finite-product sample spaces vary with n; their
laws are identified with takePrefixes of the infinite i.i.d. product. -/
theorem iid_mean_normal {A : Type*} [MeasurableSpace A]
    (nu : Measure A) [IsProbabilityMeasure nu] (f : A → ℝ)
    (hf : Measurable f) (hL2 : MemLp f 2 nu) :
    TendstoInDistribution
      (fun (n : ℕ) (a : Fin n → A) => Real.sqrt n * ((∑ i, f (a i)) / n - ∫ x, f x ∂nu))
      atTop (fun z : ℝ => z) (fun n => Measure.pi (fun _ : Fin n => nu))
      (gaussianReal 0 (variance f nu).toNNReal) := by
  let P := Measure.infinitePi (fun _ : ℕ => nu)
  let Z := fun (i : ℕ) (a : ℕ → A) => f (a i)
  have hid : ∀ i : ℕ, IdentDistrib (Z i) f P nu := by
    intro i
    refine ⟨(hf.comp (measurable_pi_apply i)).aemeasurable, hf.aemeasurable, ?_⟩
    change Measure.map (f ∘ Function.eval i) P = Measure.map f nu
    rw [← Measure.map_map hf (measurable_pi_apply i),
      (measurePreserving_eval_infinitePi (fun _ : ℕ => nu) i).map_eq]
  have hi : iIndepFun Z P := iIndepFun_infinitePi (fun _ => hf)
  have hident : ∀ i : ℕ, IdentDistrib (Z i) (Z 0) P P := fun i => (hid i).trans (hid 0).symm
  have hm : (∫ a, Z 0 a ∂P) = ∫ x, f x ∂nu := (hid 0).integral_eq
  have hv : variance (Z 0) P = variance f nu := (hid 0).variance_eq
  have hL : MemLp (Z 0) 2 P := (hid 0).memLp_iff.2 hL2
  have hgauss : HasLaw (fun z : ℝ => z) (gaussianReal 0 (variance (Z 0) P).toNNReal)
      (gaussianReal 0 (variance f nu).toNNReal) := by
    rw [hv]
    exact HasLaw.id
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hgauss hL hi hident
  simp only [hm, hv] at hclt
  let takePrefix := fun (n : ℕ) (a : ℕ → A) (i : Fin n) => a i
  have hpref (n : ℕ) : Measure.map (takePrefix n) P = Measure.pi (fun _ : Fin n => nu) := by
    have hcoord : iIndepFun (fun (i : Fin n) (a : ℕ → A) => a i) P :=
      (iIndepFun_infinitePi (P := fun _ : ℕ => nu) (fun _ => measurable_id)).precomp Fin.val_injective
    rw [iIndepFun.map_fun_eq_pi_map (ι := Fin n)
      (fun i : Fin n => (measurable_pi_apply (i : ℕ)).aemeasurable) hcoord]
    simp only [Measure.infinitePi_map_eval, P]
  have hmaps (n : ℕ) :
      Measure.map (fun a : Fin n → A => Real.sqrt n *
        ((∑ i, f (a i)) / n - ∫ x, f x ∂nu)) (Measure.pi (fun _ => nu)) =
      Measure.map (fun a : ℕ → A => (Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, Z k a - n * ∫ x, f x ∂nu)) P := by
    rw [← hpref n, Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext a
    dsimp [takePrefix, Function.comp_def, Z]
    rw [← Fin.sum_univ_eq_sum_range (fun k => f (a k))]
    by_cases hn : n = 0
    · subst n
      simp
    · have hnR : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
      have hs : (Real.sqrt n)^2 = n := Real.sq_sqrt hnR.le
      have hs0 : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
      field_simp [hs0, ne_of_gt hnR]
      rw [hs]
  refine ⟨fun n => ?_, measurable_id.aemeasurable, ?_⟩
  · exact (((Finset.measurable_sum Finset.univ (fun i _ => hf.comp (measurable_pi_apply i))).div_const (n : ℝ)).sub_const (∫ x, f x ∂nu)).const_mul (Real.sqrt n) |>.aemeasurable
  · exact hclt.tendsto.congr' (Filter.Eventually.of_forall (fun n => Subtype.ext (hmaps n).symm))

/-- Proposition 2, p. 6 (T7), asymptotic parts. Uniformity uses a
common delta. Normality is for each fixed law. -/
theorem proposition2_asymptotic :
    (∀ delta : ℝ, 0 < delta → UniformRootN delta) ∧
    (∀ M : Study, ValidStudy M → NormalLimit M (fun _ => ht M)
      ((∫ o, M.m (W o) / M.pi (W o) ∂M.law) - (mu M)^2)) := by
  refine ⟨ht_uniform_root_n, ?_⟩
  intro M hM
  letI := hM.probability
  refine ⟨hM.probability, ?_⟩
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
  have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have my : Measurable Y := ((measurable_const.sub mx).mul my0).add (mx.mul my1)
  have mf : Measurable (fun o => htTerm (M.pi (W o)) (X o) (Y o)) :=
    (mx.mul my).div (hM.measurable_pi.comp measurable_fst)
  have hvunit : variance (fun o => htTerm (M.pi (W o)) (X o) (Y o)) M.law =
      (∫ o, M.m (W o) / M.pi (W o) ∂M.law) - (mu M)^2 := by
    rw [variance_eq_sub (ht_unit_memLp M hM)]
    simp only [Pi.pow_apply]
    rw [ht_second_moment M hM, (ht_unit_facts M hM).2]
  have h := iid_mean_normal M.law _ mf (ht_unit_memLp M hM)
  simpa only [(ht_unit_facts M hM).2, hvunit, ht, sampleLaw] using h

/-- Two-sided Hoeffding for a finite i.i.d. sample mean of variables in
[0,b]. This is the unconditional finite lemma used by corrected Proposition 3
(T3) and its known-bound alternative. -/
theorem iid_mean_hoeffding {A : Type*} [MeasurableSpace A]
    (nu : Measure A) [IsProbabilityMeasure nu] (f : A → ℝ) (hf : Measurable f)
    (b : ℝ) (hb : 0 < b) (hrange : ∀ᵐ x ∂nu, f x ∈ Set.Icc 0 b)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin n => nu)).real
      {a | t ≤ |(∑ i, f (a i))/n - ∫ x, f x ∂nu|} ≤
        2 * Real.exp (-2 * n * t^2 / b^2) := by
  let P := Measure.pi (fun _ : Fin n => nu)
  let m := ∫ x, f x ∂nu
  let c : NNReal := (‖b - 0‖₊ / 2)^2
  have hunit : HasSubgaussianMGF (fun x => f x - m) c nu :=
    hasSubgaussianMGF_of_mem_Icc hf.aemeasurable hrange
  have hsub : ∀ i : Fin n,
      HasSubgaussianMGF (fun a : Fin n → A => f (a i)-m) c P := by
    intro i
    have hmap := (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq
    have h := hunit
    rw [← hmap] at h
    change HasSubgaussianMGF (fun x => f x-m) c (Measure.map (fun a : Fin n → A => a i) P) at h
    exact HasSubgaussianMGF.of_map (μ := P) (Y := fun a : Fin n → A => a i) (measurable_pi_apply i).aemeasurable h
  have hind : iIndepFun (fun (i : Fin n) (a : Fin n → A) => f (a i)-m) P :=
    iIndepFun_pi (fun _ => hf.aemeasurable.sub_const m)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ) (c := fun _ => c) (fun i _ => hsub i)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have htR : 0 ≤ (n : ℝ)*t := mul_nonneg hnR.le ht
  have hp := hsum.measure_ge_le htR
  have hm := hsum.neg.measure_ge_le htR
  have hc : (c : ℝ) = b^2/4 := by
    simp [c, Real.norm_eq_abs, abs_of_pos hb]
    ring
  have hden : (-(n*t)^2 / (2*((∑ _ : Fin n, c : NNReal) : ℝ))) = -2*n*t^2/b^2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      NNReal.coe_mul, NNReal.coe_natCast]
    rw [hc]
    field_simp [ne_of_gt hb, ne_of_gt hnR]
    ring
  rw [hden] at hp hm
  have hcenter (a : Fin n → A) : (∑ i, (f (a i)-m)) =
      (n : ℝ)*((∑ i, f (a i))/n - m) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt hnR] <;> ring
  have hset : {a : Fin n → A | t ≤ |(∑ i, f (a i))/n-m|} ⊆
      {a | (n : ℝ)*t ≤ ∑ i, (f (a i)-m)} ∪
      {a | (n : ℝ)*t ≤ -(∑ i, (f (a i)-m))} := by
    intro a ha
    change t ≤ |(∑ i, f (a i))/n-m| at ha
    change (n : ℝ)*t ≤ (∑ i, (f (a i)-m)) ∨ (n : ℝ)*t ≤ -(∑ i, (f (a i)-m))
    by_cases hsign : 0 ≤ (∑ i, f (a i))/n-m
    · apply Or.inl
      rw [abs_of_nonneg hsign] at ha
      rw [hcenter]
      exact mul_le_mul_of_nonneg_left ha hnR.le
    · apply Or.inr
      rw [abs_of_neg (lt_of_not_ge hsign)] at ha
      rw [hcenter, ← mul_neg]
      exact mul_le_mul_of_nonneg_left ha hnR.le
  have hh := measureReal_mono (μ := P) (h₂ := measure_ne_top _ _) hset
  have hu := measureReal_union_le (μ := P)
    {a | (n : ℝ)*t ≤ ∑ i, (f (a i)-m)} {a | (n : ℝ)*t ≤ -(∑ i, (f (a i)-m))}
  change P.real {a | t ≤ |(∑ i, f (a i))/n-m|} ≤ 2 * Real.exp (-2*n*t^2/b^2)
  calc
    _ ≤ P.real ({a | (n : ℝ)*t ≤ ∑ i, (f (a i)-m)} ∪
        {a | (n : ℝ)*t ≤ -(∑ i, (f (a i)-m))}) := hh
    _ ≤ P.real {a | (n : ℝ)*t ≤ ∑ i, (f (a i)-m)} +
        P.real {a | (n : ℝ)*t ≤ -(∑ i, (f (a i)-m))} := hu
    _ ≤ Real.exp (-2*n*t^2/b^2) + Real.exp (-2*n*t^2/b^2) := add_le_add hp hm
    _ = 2 * Real.exp (-2*n*t^2/b^2) := by ring

/-- T3(iii): Hoeffding for the i.i.d. [0,1] regression values m(W_i),
centred at the population mu. -/
theorem covariate_hoeffding (M : Study) (hM : ValidStudy M)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht0 : 0 ≤ t) :
    (sampleLaw M n {a | t ≤ |muW M a - mu M|}).toReal ≤ 2 * Real.exp (-2 * n * t^2) := by
  letI := hM.probability
  have hm : Measurable (fun o => M.m (W o)) := hM.measurable_m.comp measurable_fst
  have h := iid_mean_hoeffding M.law _ hm 1 (by norm_num) hM.regression_range n hn t ht0
  rw [regression_mean M hM] at h
  simpa [sampleLaw, muW, Measure.real] using h

/-- Alternative correction in T3: when the valid lower bound b is known,
the radius b^{-1} sqrt(log(2/alpha)/(2n)) has population coverage. -/
theorem proposition3_known_bound (M : Study) (hM : ValidStudy M)
    (b : ℝ) (hb : 0 < b) (hbound : ∀ᵐ o ∂M.law, b ≤ M.pi (W o))
    (n : ℕ) (hn : 0 < n) (alpha : ℝ) (ha : 0 < alpha ∧ alpha < 1) :
    tailProb M (ht M) (fun _ : Sample n => b⁻¹ * Real.sqrt (Real.log (2 / alpha) / (2 * n)))
      ≤ alpha := by
  letI := hM.probability
  have mb : Measurable bit := measurable_of_countable _
  have mx : Measurable X := mb.comp measurable_snd.fst
  have my0 : Measurable Y0 := mb.comp measurable_snd.snd.fst
  have my1 : Measurable Y1 := mb.comp measurable_snd.snd.snd
  have my : Measurable Y := ((measurable_const.sub mx).mul my0).add (mx.mul my1)
  have mf : Measurable (fun o => htTerm (M.pi (W o)) (X o) (Y o)) :=
    (mx.mul my).div (hM.measurable_pi.comp measurable_fst)
  have hrange : ∀ᵐ o ∂M.law, htTerm (M.pi (W o)) (X o) (Y o) ∈ Set.Icc 0 b⁻¹ := by
    filter_upwards [hbound] with o ho
    have hp0 : 0 < M.pi (W o) := lt_of_lt_of_le hb ho
    have hi : (M.pi (W o))⁻¹ ≤ b⁻¹ := (inv_le_inv₀ hp0 hb).2 ho
    have hh : 0 ≤ htTerm (M.pi (W o)) (X o) (Y o) ∧
        htTerm (M.pi (W o)) (X o) (Y o) ≤ (M.pi (W o))⁻¹ := by
      simp only [htTerm, consistency_treated]
      rcases o with ⟨w,x,y0,y1⟩
      cases x <;> cases y1 <;> simp [X, Y1, bit, one_div, (inv_pos.2 hp0).le]
    exact ⟨hh.1, hh.2.trans hi⟩
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hlog : 0 < Real.log (2/alpha) := Real.log_pos (by
    apply (lt_div_iff₀ ha.1).2
    linarith [ha.2])
  let t := b⁻¹ * Real.sqrt (Real.log (2/alpha)/(2*n))
  have hh := iid_mean_hoeffding M.law _ mf b⁻¹ (inv_pos.2 hb) hrange n hn t (by positivity)
  rw [(ht_unit_facts M hM).2] at hh
  have hex : -2*n*t^2/(b⁻¹)^2 = -Real.log (2/alpha) := by
    dsimp [t]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp [ne_of_gt hb, ne_of_gt hnR]
  rw [hex] at hh
  have he : 2 * Real.exp (-Real.log (2/alpha)) = alpha := by
    rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) ha.1)]
    field_simp
  rw [he] at hh
  exact hh

namespace RobinsRitov

/-- T10(d): the random-bin prior target has mean 2/3 and variance 1/(9K),
which tends to zero when K=n^3. Combined with T10(c), this separates the targets
by 1/6 while the observed sample laws become indistinguishable. -/
theorem rr_prior_target (K : ℕ) (hK : 0 < K) :
    (∫ tau, (∑ j : Fin K, if tau j then (1 : ℝ) else 1/3)/K ∂prior K) = 2/3 ∧
    variance (fun tau => (∑ j : Fin K, if tau j then (1 : ℝ) else 1/3)/K) (prior K) = 1/(9*K) := by
  let nu := uniformOn (Set.univ : Set Bool)
  let f := fun b : Bool => if b then (1 : ℝ) else 1/3
  have hf : MemLp f 2 nu := by
    apply memLp_of_bounded (a := (1/3 : ℝ)) (b := 1)
    · apply Filter.Eventually.of_forall
      intro b
      cases b <;> norm_num [f]
    · exact (measurable_of_countable f).aestronglyMeasurable
  have hs (b : Bool) : (nu {b}).toReal = 1/2 := by
    change ((uniformOn (Set.univ : Set Bool)) {b}).toReal = 1/2
    rw [uniformOn_univ]
    norm_num
  have hmean : (∫ b, f b ∂nu) = 2/3 := by
    rw [integral_fintype (memLp_one_iff_integrable.1 (hf.mono_exponent (by norm_num)))]
    simp only [Measure.real, hs]
    norm_num [f]
  have hL : Integrable (fun b => (f b - (2/3 : ℝ))^2) nu := by
    simpa only [Pi.sub_apply] using (hf.sub (memLp_const (2/3))).integrable_sq
  have hv : variance f nu = 1/9 := by
    rw [variance_eq_integral hf.aemeasurable, hmean,
      integral_fintype hL]
    simp only [Measure.real, hs]
    norm_num [f]
  constructor
  · change (∫ tau : Fin K → Bool, (∑ j, f (tau j))/K ∂Measure.pi (fun _ => nu)) = 2/3
    rw [iid_mean_integral nu f (memLp_one_iff_integrable.1 (hf.mono_exponent (by norm_num))) K hK, hmean]
  · change variance (fun tau : Fin K → Bool => (∑ j, f (tau j))/K) (Measure.pi (fun _ => nu)) = 1/(9*K)
    rw [iid_mean_variance nu f hf K hK, hv]
    field_simp

end RobinsRitov

/-- T10(b): the finite i.i.d. uniform-bin collision bound n(n-1)/(2K),
the union bound used in the Robins--Ritov lower-bound construction.
This lemma concerns the bin-index law; transferring continuous
uniform covariates to their bin indices is a separate mathematical step. -/
theorem robins_ritov_collision (K n : ℕ) (hK : 0 < K) :
    (binLaw K n {b | ∃ i j, i ≠ j ∧ b i = b j}).toReal ≤
      (n : ℝ) * (n-1) / (2*K) := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  let nu : Measure (Fin K) := uniformOn Set.univ
  let P := binLaw K n
  letI : IsProbabilityMeasure P := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin n => nu))
    infer_instance
  have hev (i : Fin n) (b : Fin K) : P {a | a i = b} = (K : ℝ≥0∞)⁻¹ := by
    have h := Measure.map_apply (measurable_pi_apply i)
      (measurableSet_singleton b) (μ := P)
    change (Measure.map (Function.eval i) (Measure.pi (fun _ : Fin n => nu))) {b} =
      P {a | a i = b} at h
    rw [(measurePreserving_eval (fun _ : Fin n => nu) i).map_eq] at h
    simpa [nu, uniformOn_univ] using h.symm
  have hpair (i j : Fin n) (hij : i ≠ j) : P.real {a | a i = a j} = 1 / (K : ℝ) := by
    have hind : IndepFun (fun a : Fin n → Fin K => a i) (fun a => a j) P :=
      (iIndepFun_pi (fun _ : Fin n => (measurable_id : Measurable (id : Fin K → Fin K)).aemeasurable)).indepFun hij
    have hmass (b : Fin K) : P.real {a | a i = b ∧ a j = b} = 1 / (K : ℝ)^2 := by
      have h := hind.measure_inter_preimage_eq_mul {b} {b}
        (measurableSet_singleton b) (measurableSet_singleton b)
      change P {a | a i = b ∧ a j = b} = P {a | a i = b} * P {a | a j = b} at h
      rw [Measure.real, h, hev, hev, ENNReal.toReal_mul]
      simp [ENNReal.toReal_inv]
      ring
    have heq : {a : Fin n → Fin K | a i = a j} =
        ⋃ b ∈ (Finset.univ : Finset (Fin K)), {a | a i = b ∧ a j = b} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and]
      constructor
      · intro h
        exact ⟨a i, rfl, h.symm⟩
      · rintro ⟨b, h1, h2⟩
        exact h1.trans h2.symm
    rw [heq, measureReal_biUnion_finset]
    · simp only [hmass, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hkR : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.ne_of_gt hK)
      field_simp
    · intro b hb c hc hbc
      apply Set.disjoint_left.2
      rintro a ⟨h1, h2⟩ ⟨h3, h4⟩
      exact hbc (h1.symm.trans h3)
    · intro b hb
      exact (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).inter
        (measurableSet_eq_fun (measurable_pi_apply j) measurable_const)
  let pairs := ((Finset.univ : Finset (Fin n)).product Finset.univ).filter
    (fun ij => ij.1 < ij.2)
  have hsub : {a : Fin n → Fin K | ¬ Function.Injective a} ⊆
      ⋃ ij ∈ pairs, {a | a ij.1 = a ij.2} := by
    intro a ha
    simp only [Set.mem_setOf_eq, Function.Injective] at ha
    push_neg at ha
    obtain ⟨i, j, heq, hne⟩ := ha
    simp only [Set.mem_iUnion, exists_prop]
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact ⟨(i,j), by simp [pairs, hij], heq⟩
    · exact ⟨(j,i), by simp [pairs, hji], heq.symm⟩
  have hsum : (∑ ij ∈ pairs, P.real {a | a ij.1 = a ij.2}) =
      (n : ℝ) * (n-1) / (2*K) := by
    calc
      _ = ∑ _ij ∈ pairs, 1/(K : ℝ) := by
        apply Finset.sum_congr rfl
        intro ij hij
        exact hpair ij.1 ij.2 (ne_of_lt (Finset.mem_filter.1 hij).2)
      _ = (n : ℝ) * (n-1) / (2*K) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [show pairs.card = n.choose 2 by
          simpa [pairs] using Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n)))]
        rw [Nat.cast_choose_two]
        ring
  have hevent : {b : Fin n → Fin K | ∃ i j, i ≠ j ∧ b i = b j} =
      {a | ¬ Function.Injective a} := by
    ext a
    constructor
    · rintro ⟨i,j,hne,heq⟩ hi
      exact hne (hi heq)
    · intro hi
      simp only [Function.Injective] at hi
      push_neg at hi
      obtain ⟨i,j,heq,hne⟩ := hi
      exact ⟨i,j,hne,heq⟩
  change P.real {b | ∃ i j, i ≠ j ∧ b i = b j} ≤ _
  rw [hevent]
  exact (measureReal_mono (h₂ := measure_ne_top _ _) hsub).trans
    ((measureReal_biUnion_finset_le pairs _).trans_eq hsum)

/-- T5: almost-sure membership in an L2 working family
supplies the fitted-L2 premise in corrected Proposition 4(c).
Thus that premise is redundant. -/
theorem fitted_L2_from_membership (M : Study) (d : ℕ)
    (family : (Fin d → ℝ) → ℝ → ℝ) (F : ∀ n, CrossFit n)
    (hG : ∀ theta, MemLp (fun o => family theta (W o)) 2 M.law)
    (hfit : ∀ n j, ∀ᵐ a ∂sampleLaw M n, ∃ theta, (F n).g j a = family theta) :
    ∀ n j, ∀ᵐ a ∂sampleLaw M n, MemLp (fun o => (F n).g j a (W o)) 2 M.law := by
  intro n j
  filter_upwards [hfit n j] with a ha
  obtain ⟨theta, heq⟩ := ha
  rw [heq]
  exact hG theta

end
end AronowAudit.P046

