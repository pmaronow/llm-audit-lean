import SAP.P001a.Defs.WholeW1
import SAP.P001a.Bridge
import SAP.P001a.WH.W1.Likelihood

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

universe u v

namespace SAP.P001a.WH.W1

/-- A positive-PDF neighborhood is not necessary. Delete the value of the uniform
PDF at zero; its law and mean stay unchanged. Transfer a.e. equality to Lebesgue
measure on (-1,1), use continuity, and differentiate the locally zero function.
The proof is a singleton-null density calculation and a local equality argument. -/
def T4_L1 : Prop :=
  HasPDF (uniformLaw (-1) 1) wholeHolePDF ∧
    Integrable id (uniformLaw (-1) 1) ∧ mean (uniformLaw (-1) 1) id = 0 ∧
    wholeHolePDF 0 = 0 ∧
    ∀ m : ℝ → ℝ, ContinuousOn m (Set.Ioo (-1 : ℝ) 1) →
      m =ᵐ[uniformLaw (-1) 1] (fun _ => 0) →
      Set.EqOn m (fun _ => 0) (Set.Ioo (-1 : ℝ) 1) ∧ HasDerivAt m 0 0

/-- Borel polynomial least-squares selection on every sample, including singular
and empty designs. Partition by the equality pattern of the finitely many X_i.
If there are at most J+1 distinct nodes, interpolate their response class means;
otherwise the Vandermonde Gram has full rank and use the inverse Gram formula.
Each partition is Borel and each coefficient is a rational expression there.
Pointwise existence alone, or a zero fallback at singular matrices, is insufficient. -/
def T6_L1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (X Y : ℕ → Ω → ℝ)
    (hm : ∀ i, Measurable (X i) ∧ Measurable (Y i)) (J : ℕ → ℕ),
    ∃ fit : ℕ → Ω → Polynomial ℝ, IsSieveLS X Y J fit ∧
      ∀ n k, Measurable (fun ω => (fit n ω).coeff k)

/-- Recover the donor's L2 and global-CEF premises from the local canonical ones.
Extend m by zero off [a,b]. Compactness bounds m(X); conditional variance gives
integrable squared noise; Y² ≤ 2 noise²+2 m(X)² gives Y in L2. The event A=univ
also gives V≥0. The extension is a measurable CEF and every polynomial risk is
integrable. No integrability of arbitrary off-support values is assumed. -/
def T6_L2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : ℕ → Ω → ℝ) (a b V : ℝ) (m : ℝ → ℝ)
    (h : WholeSieveData μ X Y a b V m),
    0 ≤ V ∧ MemLp (Y 0) 2 μ ∧
    IsCEF μ (X 0) (Y 0) ((Set.Icc a b).indicator m) ∧
    (∀ᵐ ω ∂μ, ((Set.Icc a b).indicator m) (X 0 ω) = m (X 0 ω)) ∧
    ∀ q : Polynomial ℝ, Integrable (fun x => (q.eval x - m x)^2) (μ.map (X 0))

/-- Affine transport of the uniform row-envelope bound to every interval.
For q_k(z)=p_k(a+(b-a)z), degree and probability orthonormality are preserved.
Apply the existing arbitrary-basis [0,1] bound and substitute z=(x-a)/(b-a).
There is no interval-length factor for a probability-normalized basis. -/
def T6_L3 : Prop :=
  ∀ (a b : ℝ) (hab : a < b) {K : ℕ} (hK : 0 < K)
    (p : Fin K → Polynomial ℝ) (hdeg : ∀ k, (p k).natDegree = k.val)
    (horth : ∀ j k, mean (uniformLaw a b)
      (fun x => (p j).eval x * (p k).eval x) = if j = k then 1 else 0),
    ∀ x ∈ Set.Icc a b, (∑ k, ((p k).eval x)^2) ≤ (K : ℝ)^2

/-- Rayleigh and Euclidean operator norms agree for the symmetric deviation G-I.
Use the self-adjoint Rayleigh-quotient norm formula through toEuclideanCLM.
The positive dimension guard makes the unit sphere nonempty, avoiding sSup ∅. -/
def T6_L4 : Prop :=
  ∀ {K : ℕ} (hK : 0 < K) (G : Matrix (Fin K) (Fin K) ℝ) (hG : G.IsSymm),
    gramDeviation G = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin K)) (G - 1)‖

/-- Finite normalized-section KL identity over an arbitrary reference measure.
Use t8_section_kl. Convert integrability of log g under f κ to integrability of
f log g under κ, and positivity under f κ to the required density domination.
Normalization comes from the two Markov kernels. The result is a finite real
section divergence and its nonnegativity, with no global entropy premise. -/
def T8_L1 : Prop :=
  ∀ {A : Type u} [MeasurableSpace A] (κ : Measure ℝ)
    (F G : WholeDensity A κ) (x : A)
    (hent : Integrable (fun y => F.density x y * Real.log (F.density x y)) κ)
    (hcross : Integrable (fun y => Real.log (G.density x y)) (F.kernel x))
    (hpos : ∀ᵐ y ∂(F.kernel x), 0 < G.density x y),
    InformationTheory.klDiv (F.kernel x) (G.kernel x) = ENNReal.ofReal
      (wholeSectionEntropy F x - ∫ y, Real.log (G.density x y) ∂(F.kernel x)) ∧
    0 ≤ wholeSectionEntropy F x - ∫ y, Real.log (G.density x y) ∂(F.kernel x)

/-- Binary conditional independence preserves the treatment CEF for a.e. binary D,
then gives the unique zero-placebo population coefficients. Use MarSelection.N3
with its proved N1/N2 and isCEF_condExp, followed by CondP001b_risk and
CondP001b_gram_unique. This extends the pointwise-binary donor without a
literature premise. All risk terms are integrable by the stated second moments. -/
def T18_L1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
    (γ : Fin (K + 1) → ℝ) (h : WholePlaceboNull μ X W D γ),
    WholePlaceboPopulation μ X W D γ

/-- Derive the OLS score moments under the placebo null from its enlarged CEF.
Conditional-expectation monotonicity gives 0≤m≤1 and |u|≤1. Pull out each L2
regressor to obtain E[Zu]=0. Bounded u preserves L2. Integrate squared directional
linear forms to prove Q, Omega and the sandwich are positive semidefinite.
No fourth moment or uniform overlap assumption is needed. -/
def T18_L2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
    (γ : Fin (K + 1) → ℝ) (h : WholePlaceboNull μ X W D γ)
    (hpop : WholePlaceboPopulation μ X W D γ),
    WholeScoreMoments μ (fun ω => wholeDesign (X ω) (W ω)) D (wholeNullCoef γ)

/-- Normal equations and excess risk for the general augmented BLP, without
conditional independence or a linear CEF. Expand the integrable quadratic risk,
use Q b=E[ZD], and use positive definiteness of the nonsingular Gram. Equality
with some reduced linear predictor is equivalent to the W block of b being zero.
This is the precise added-linear-predictive-content interpretation. -/
def T18_L3 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
    (h : WholePlaceboDesign μ X W D), WholeLinearContent μ X W D

/-- Sample Gram, inverse Gram, OLS consistency and true-residual meat laws.
Apply the real SLLN entrywise to ZZ', Zu and u²ZZ'. All are integrable under
WholeScoreMoments. Continuity of inversion at the nonsingular Q gives eventual
sample rank a.s.; normalized_ols bridges to the actual OLS formula. Establish
Borel measurability of the totalized formulas as well. No sample-rank premise at
small n is allowed. This is finite-coordinate LLN work, separate from the CLT. -/
def T18_L4 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (Z i ω, D i ω))) (b : Fin p → ℝ)
    (h : WholeScoreMoments μ (Z 0) (D 0) b), WholeGramLimits μ Z D b

/-- OLS Slutsky step and stochastic boundedness. On eventually nonsingular sample
Grams, sqrt(n)(bhat-b)=Q_n^{-1} times the standardized score sum. Pair the score
limit with inverse-Gram convergence, multiply continuously, and identify the
Gaussian covariance. Weak convergence to a probability law gives root-n
stochastic boundedness. Exceptional early samples do not affect these limits. -/
def T18_L5 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (Z i ω, D i ω))) (b : Fin p → ℝ)
    (h : WholeScoreMoments μ (Z 0) (D 0) b) (hgram : WholeGramLimits μ Z D b)
    (hscore : WeakLimit μ (wholeScoreSum Z D b)
      (normalVectorLaw (wholeOmega μ (Z 0) (D 0) b))),
    WeakLimit μ (wholeRootError Z D b) (normalVectorLaw (wholeSandwich μ (Z 0) (D 0) b)) ∧
    WholeTight μ (wholeRootError Z D b)

/-- Maximum row norm squared/n tends to zero under a finite second moment.
Use the union bound n P(||Z||²>n epsilon) and the integrable-tail bound
s P(H>s)≤E[H 1_{H>s}] for H=||Z||². Identical distributions suffice for this
bound; the iid premise supplies them. Treat n=0 by its assigned zero value. -/
def T18_L6 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ) (hiid : IID μ Z)
    (h2 : ∀ j, MemLp (fun ω => Z 0 ω j) 2 μ), CP μ (wholeMaxRow Z) 0

/-- Replacing true residuals by fitted residuals changes the normalized meat by
op(1), using only second moments. Write d=bhat-b. Bound the quadratic error by
||d||² max_i||Z_i||² (n^{-1}sum_i||Z_i||²), with dimension constants for the Pi
norm. Root-n tightness and the maximum-row tail make this vanish. Cauchy–Schwarz
controls the cross term against the bounded-residual true meat. Combine with
its LLN from WholeGramLimits. Avoid the fourth-moment residual-LLN shortcut. -/
def T18_L7 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (Z i ω, D i ω))) (b : Fin p → ℝ)
    (h : WholeScoreMoments μ (Z 0) (D 0) b) (hgram : WholeGramLimits μ Z D b)
    (htight : WholeTight μ (wholeRootError Z D b))
    (hmax : CP μ (wholeMaxRow Z) 0),
    CP μ (wholeFittedMeat Z D) (wholeOmega μ (Z 0) (D 0) b)

/-- Normalize HC0 correctly: for positive n and nonsingular Q_n,
n HC0=Q_n^{-1} fittedMeat_n Q_n^{-1}. Establish the finite matrix scaling identity
for the existing unnormalized formula, use Q_n symmetry, and apply continuous
matrix multiplication in probability. Eventual rank handles all early singular
samples. The covariance limit is V, not zero. -/
def T18_L8 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (Z i ω, D i ω))) (b : Fin p → ℝ)
    (h : WholeScoreMoments μ (Z 0) (D 0) b) (hgram : WholeGramLimits μ Z D b)
    (hmeat : CP μ (wholeFittedMeat Z D) (wholeOmega μ (Z 0) (D 0) b)),
    CP μ (fun n ω => (n : ℝ) • wholeHC0 Z D n ω) (wholeSandwich μ (Z 0) (D 0) b)

/-- Gaussian Wald quadratic form. If V is positive semidefinite and R V R' is
nonsingular, R G has positive definite covariance S. Whiten by S^{-1/2}; identify
the standard Gaussian via its covariance/characteristic function. Its squared
Euclidean norm is chi-square with L degrees of freedom. No nonsingularity of
V itself is required. The law on the right is the explicit sum-of-squares law. -/
def T18_L9 : Prop :=
  ∀ {p L : ℕ} (hL : 0 < L) (V : Matrix (Fin p) (Fin p) ℝ) (hV : V.PosSemidef)
    (R : Matrix (Fin L) (Fin p) ℝ) (hS : IsUnit (R * V * R.transpose).det),
    (normalVectorLaw V).map (fun z =>
      (R.mulVec z) ⬝ᵥ (R * V * R.transpose)⁻¹.mulVec (R.mulVec z)) = wholeChiSquare L

/-- Feasible Wald limit from the OLS Gaussian limit and scaled covariance
consistency. Pair sqrt(n)(bhat-b) with n C_n, use inversion continuous at
S=R V R', and the whitening law supplied as a premise. The equality R b=0
identifies the centered pivot with the actual statistic for positive n.
Translate weak convergence to CDF convergence at continuity points. -/
def T18_L10 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p L : ℕ} (hL : 0 < L) (b : Fin p → ℝ) (V : Matrix (Fin p) (Fin p) ℝ)
    (hV : V.PosSemidef) (R : Matrix (Fin L) (Fin p) ℝ)
    (hS : IsUnit (R * V * R.transpose).det) (hnull : R.mulVec b = 0)
    (B : ℕ → Ω → Fin p → ℝ) (C : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hB : ∀ n, Measurable (B n)) (hC : ∀ n, Measurable (C n))
    (hCLT : WeakLimit μ (fun n ω => Real.sqrt n • (B n ω - b)) (normalVectorLaw V))
    (hCov : CP μ (fun n ω => (n : ℝ) • C n ω) V)
    (hLaw : (normalVectorLaw V).map (fun z =>
      (R.mulVec z) ⬝ᵥ (R * V * R.transpose)⁻¹.mulVec (R.mulVec z)) = wholeChiSquare L),
    CD μ (fun n ω => wholeWald R (B n ω) (C n ω)) (wholeChiSquare L)

/-- Chi-square critical values and calibration. The explicit sum-of-squares law
has no atoms for L>0; its continuous CDF has limits zero and one, so every
1-alpha in (0,1) has a real quantile. Apply CDF convergence at that quantile
and complement the measurable lower-tail event to obtain rejection size alpha.
The returned lower-tail limit also proves coverage of the inverted region. -/
def T18_L11 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : ℕ) (hL : 0 < L) (T : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (T n))
    (hCD : CD μ T (wholeChiSquare L)) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1),
    ∃ q : ℝ, prob (wholeChiSquare L) (Set.Iic q) = 1 - α ∧
      Tendsto (fun n => prob μ {ω | q < T n ω}) atTop (nhds α) ∧
      Tendsto (fun n => prob μ {ω | T n ω ≤ q}) atTop (nhds (1 - α))

/-- Assembly of the local, law-level, and non-necessity clauses. -/
theorem T4_assembly (h1 : T4_L1) : T4WholeStatement.{u} := by
  refine ⟨?_, ?_, h1⟩
  · intro K U hU m m' hm hm' heq
    have he := local_continuous_eq U hU m m' hm hm' heq
    refine ⟨he, ?_⟩
    intro x k a M M' hM hM' hd
    apply derivative_of_eqOn U hU x.val x.property M M' _ k a hd
    intro y hy
    exact (hM ⟨y, hy⟩).trans ((congrFun he ⟨y, hy⟩).trans (hM' ⟨y, hy⟩).symm)
  · intro Ω _ μ _ K X Y hX hXi f hf U hU hmean hpositive m m' hm hm' hc hc'
    have he := cef_eq_on_positive_open μ X Y hX f hf U hU hpositive m m' hm hm' hc hc'
    exact ⟨he, fun k a hd => derivative_of_eqOn U hU _ hmean m m' he k a hd⟩

/-- The endpoint supplement has a direct, assumption-free counterexample. -/
theorem T5_assembly : T5WholeStatement := by
  have hu : IsProbabilityMeasure (uniformLaw 0 1) := by
    change IsProbabilityMeasure (AronowAudit.P001.uniformLaw 0 1)
    infer_instance
  letI : IsProbabilityMeasure (uniformLaw 0 1) := hu
  refine ⟨inferInstance, endpoint_coeff_measurable, ?_, endpoint_tail_zero, ?_⟩
  · intro xy
    refine ⟨endpoint_degree xy, endpoint_interpolates xy, ?_⟩
    intro q hq
    rw [endpoint_interpolates]
    simpa using sq_nonneg (xy.2 - q.eval xy.1)
  · rw [endpoint_tail_zero]
    norm_num

/-- The analytic and selection leaves fill exactly the gaps in the existing
stable-Gram theorem and its finite probability bounds. -/
theorem T6_assembly (h1 : T6_L1.{u}) (h2 : T6_L2.{u}) (h3 : T6_L3) (h4 : T6_L4) :
    T6WholeStatement.{u} := by
  refine ⟨h1, ?_, support_envelope_attained, ?_, ?_, ?_⟩
  · intro Ω _ μ _ X Y a b V m h p hdeg horth J hJ hrate c hc hgram fit hfit
    obtain ⟨hV, hY2, hcef, hae, hint⟩ := h2 μ X Y a b V m h
    refine ⟨fun n ω => hint (fit n ω), ?_⟩
    let m0 := (Set.Icc a b).indicator m
    have hm0 : ContinuousOn m0 (Set.Icc a b) := h.continuous.congr
      (fun x hx => by simp [m0, hx])
    have hvar : ∀ A : Set ℝ, MeasurableSet A →
        (∫ ω in (X 0) ⁻¹' A, (Y 0 ω - m0 (X 0 ω))^2 ∂μ) ≤
          V * prob μ ((X 0) ⁻¹' A) := by
      intro A hA
      convert h.variance_bound A hA using 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hae] with ω hω
      change (Y 0 ω - ((Set.Icc a b).indicator m) (X 0 ω))^2 = _
      rw [hω]
    have hcp := AronowAudit.P001.Wave1.TailB_sieve_consistency_stable_gram
      μ X Y h.iid a b V h.interval hV hY2 h.support m0 hm0 hcef hvar
      p hdeg horth J hJ hrate c hc hgram fit hfit
    have hs : ∀ᵐ x ∂(μ.map (X 0)), x ∈ Set.Icc a b :=
      (ae_map_iff (h.iid.1 0).fst.aemeasurable measurableSet_Icc).mpr h.support
    have he : (fun n ω => ∫ x, ((fit n ω).eval x - m x)^2 ∂(μ.map (X 0))) =
        (fun n ω => ∫ x, ((fit n ω).eval x - m0 x)^2 ∂(μ.map (X 0))) := by
      funext n ω
      apply integral_congr_ae
      filter_upwards [hs] with x hx
      simp [m0, hx]
    rw [he]
    exact hcp
  · intro Ω _ μ _ X hiid a b hab hsupp p horth J hrate
    have hrow : ∀ n, ∀ᵐ ω ∂μ,
        (∑ k : Fin (J n + 1), ((p k).eval (X 0 ω))^2) ≤
          wholeSieveEnvelope a b (fun k : Fin (J n + 1) => p k) := by
      intro n
      obtain ⟨x, hx, he, hb⟩ := support_envelope_attained a b hab (fun k : Fin (J n + 1) => p k)
      filter_upwards [hsupp] with ω hω using hb (X 0 ω) hω
    exact AronowAudit.P001.Wave1.general_gram_rate_stability_proof μ X hiid p horth J
      (fun n => wholeSieveEnvelope a b (fun k : Fin (J n + 1) => p k)) hrow hrate
  · intro Ω _ μ _ X hiid a b hab hlaw K n hK hn p hdeg horth
    have ho : ∀ j k, mean (uniformLaw a b) (fun x => (p j).eval x * (p k).eval x) =
        if j = k then 1 else 0 := by
      intro j k
      rw [mean, ← hlaw, integral_map (f := fun x => (p j).eval x * (p k).eval x) (hiid.1 0).aemeasurable
        ((p j).continuous.mul (p k).continuous).aestronglyMeasurable]
      exact horth j k
    have hr := h3 a b hab hK p hdeg ho
    obtain ⟨x, hx, he, hb⟩ := support_envelope_attained a b hab p
    refine ⟨by rw [he]; exact hr x hx, ?_⟩
    have hsupp : ∀ᵐ ω ∂μ, X 0 ω ∈ Set.Icc a b := by
      apply ae_of_ae_map (hiid.1 0).aemeasurable
      rw [hlaw]
      unfold uniformLaw
      have hd : Measurable (fun x : ℝ => ENNReal.ofReal (if x ∈ Set.Icc a b then (b - a)⁻¹ else 0)) :=
        (Measurable.ite measurableSet_Icc measurable_const measurable_const).ennreal_ofReal
      apply (ae_withDensity_iff' hd.aemeasurable).mpr
      filter_upwards with x hx
      by_contra hxnot
      simp [hxnot] at hx
    have hrow : ∀ᵐ ω ∂μ, (∑ k, ((p k).eval (X 0 ω))^2) ≤ (K : ℝ)^2 :=
      hsupp.mono (fun ω hω => hr (X 0 ω) hω)
    have hbound := AronowAudit.P001.Wave1.general_gram_finite_probability_bound
      μ hK X hiid p horth ((K : ℝ)^2) hrow n hn
    have hevent : {ω | (1 / 2 : ℝ) <
        ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin K)) (sampleGram p X n ω - 1)‖} =
        {ω | (1 / 2 : ℝ) < gramDeviation (sampleGram p X n ω)} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [h4 hK (sampleGram p X n ω) (by ext j k; simp [sampleGram, mul_comm])]
    rw [hevent]
    calc
      _ = AronowAudit.P001.prob μ {ω | (1 / 2 : ℝ) <
          AronowAudit.P001.gramDeviation (AronowAudit.P001.sampleGram p X n ω)} := rfl
      _ ≤ 4 * ((K : ℝ)^2 * K - K) / n := hbound
      _ = _ := by ring
  · intro Ω _ μ _ X hiid a b hab hlaw p hdeg horth J hrate
    exact AronowAudit.P001.Wave1.uniform_cubic_gram_rate_stability_proof
      μ X hiid a b hab hlaw p hdeg horth J hrate

/-- Sectionwise KL plus kernel Fubini proves the weak-entropy identity; subtraction
reverses the optimization order. The positive-sample likelihood argument and
compact separation use proved helpers, and self-KL gives the true-model clause. -/
theorem T8_assembly (h1 : T8_L1.{u}) : T8WholeStatement.{u} := by
  have hid := fun {A : Type u} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
      (κ : Measure ℝ) (F G : WholeDensity A κ) hent hlog =>
    kernel_finite_identity ν κ F G hent hlog (h1 κ F G)
  refine ⟨hid, ?_, ?_, ?_, ?_⟩
  · intro A _ ν _ κ F τ Θ G hent hlog s
    have hfin (t : Θ) := (hid ν κ F (G t) hent (hlog t)).1
    have hval (t : Θ) := (hid ν κ F (G t) hent (hlog t)).2
    constructor
    · intro h t
      have hc := (ENNReal.toReal_le_toReal (hfin s) (hfin t)).mpr (h t)
      rw [hval s, hval t] at hc
      linarith
    · intro h t
      apply (ENNReal.toReal_le_toReal (hfin s) (hfin t)).mp
      rw [hval s, hval t]
      linarith [h t]
  · intro Ω _ μ _ K τ X Y hiid ν _ κ F Θ G hlaw hlog tstar that hm e hen he M hsep hUC hmax
    exact likelihood_argmax μ X Y G M tstar that e hen he hsep hUC hmax
  · exact @AronowAudit.P001.compact_unique_maximum_separated
  · intro A _ ν _ κ τ Θ G θ tstar hu
    have hz : wholeAverageKL ν (G θ) (G θ) = 0 := by
      simp [wholeAverageKL, InformationTheory.klDiv_self]
    have hstar : wholeAverageKL ν (G θ) (G tstar) = 0 := by
      exact le_zero_iff.mp (by simpa [hz] using (hu θ).1)
    have he : tstar = θ := ((hu θ).2 (hz.trans hstar.symm)).symm
    refine ⟨hz, he, ?_⟩
    intro t
    constructor
    · intro ht
      exact ((hu t).2 (ht.trans hstar.symm)).trans he
    · intro ht
      simpa [ht] using hz

/-- The population, score, LLN, CLT, HC0, whitening and calibration leaves assemble
without extra sample-rank, moment, or overlap assumptions. -/
theorem T18_assembly (h1 : T18_L1.{u}) (h2 : T18_L2.{u}) (h3 : T18_L3.{u})
    (h4 : T18_L4.{u}) (h5 : T18_L5.{u}) (h6 : T18_L6.{u}) (h7 : T18_L7.{u})
    (h8 : T18_L8.{u}) (h9 : T18_L9) (h10 : T18_L10.{u}) (h11 : T18_L11.{u}) : T18WholeStatement.{u} := by
  refine ⟨h1, h3, ?_, ?_⟩
  · intro Ω _ μ _ K L X W D hiid γ h
    let Z := fun i ω => wholeDesign (X i ω) (W i ω)
    let b : Fin (K + L + 1) → ℝ := wholeNullCoef γ
    let f : (Fin K → ℝ) × (Fin L → ℝ) × ℝ → (Fin (K + L + 1) → ℝ) × ℝ :=
      fun z => (wholeDesign z.1 z.2.1, z.2.2)
    have hf : Measurable f := by
      have hZ : Measurable (fun z : (Fin K → ℝ) × (Fin L → ℝ) × ℝ =>
          wholeDesign z.1 z.2.1) := by
        apply Measurable.of_eval
        intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · simpa [wholeDesign] using (measurable_const : Measurable
            (fun _ : (Fin K → ℝ) × (Fin L → ℝ) × ℝ => (1 : ℝ)))
        · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
          · simpa [wholeDesign, Function.comp_def] using (measurable_pi_apply k).comp measurable_fst
          · simpa [wholeDesign, Function.comp_def] using (measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)
      exact hZ.prodMk (measurable_snd.comp measurable_snd)
    have hi : IID μ (fun i ω => (Z i ω, D i ω)) :=
      ⟨fun i => hf.comp (hiid.1 i), hiid.2.1.comp (fun _ => f) (fun _ => hf),
        fun i => (hiid.2.2 i).comp hf⟩
    have hmom := h2 μ (X 0) (W 0) (D 0) γ h (h1 μ (X 0) (W 0) (D 0) γ h)
    have hg := h4 μ Z D hi b hmom
    have hs := score_clt μ Z D hi b hmom
    obtain ⟨hclt, htight⟩ := h5 μ Z D hi b hmom hg hs
    have hiZ : IID μ Z := ⟨fun i => (hi.1 i).fst,
      hi.2.1.comp (fun _ => Prod.fst) (fun _ => measurable_fst),
      fun i => (hi.2.2 i).comp measurable_fst⟩
    have hmax := h6 μ Z hiZ hmom.secondZ
    have hmeat := h7 μ Z D hi b hmom hg htight hmax
    have hcov := h8 μ Z D hi b hmom hg hmeat
    refine ⟨hg.beta, hclt, hcov, ?_⟩
    intro r hr R hnull hrank α hα
    have hlaw := h9 hr _ hmom.positiveSandwich R hrank
    have hcd := h10 μ hr b _ hmom.positiveSandwich R hrank hnull
      (wholeBetaHat Z D) (wholeHC0 Z D) hg.measurableBeta hg.measurableHC0 hclt hcov hlaw
    obtain ⟨q, hq, hrej, hcover⟩ := h11 μ r hr _
      (fun n => measurable_wald R _ _ (hg.measurableBeta n) (hg.measurableHC0 n)) hcd α hα
    refine ⟨q, hq, hcd, hrej, ?_⟩
    simpa only [wholeJointRegion, Set.mem_ofPred_eq, sub_zero, wholeWald] using hcover
  · have hw := AronowAudit.P001.placebo_full_finite_counterexample
    exact ⟨hw.1, by norm_num, hw.2.2.2.2.2.1⟩

end SAP.P001a.WH.W1
