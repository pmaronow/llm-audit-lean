import SAP.P002a.Defs.WholeW2
import SAP.P002a.WH.W2.AssemblySupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W2
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

/-- Count treatment subsets by their intersections with the two sign classes.
Use the bijection with a product of powersetCard sets and card_powersetCard.
Treat l>m separately. All binomial denominators are positive since m≤2m. -/
def T14_L1 : Prop := W2T14Hypergeom

/-- Exact sample mean, second moment, variance-estimator and ratio formulas.
The balanced signs have mean zero and population variance 2m/(2m-1).
Use sample_mean_variance_proof, complementary totals and square_centering;
the actual variance denominator is supplied by missing_square_counterexample_proof. -/
def T14_L2 : Prop :=
  ∀ m, 2 ≤ m →
    (∀ O ∈ assignments (signModel m), observedW (signModel m) 0 O = W2sign m) ∧
    expectation (signModel m) (fun T => W2q m T^2) = 1/((2*m : ℕ)-(1 : ℝ)) ∧
    0 < designVariance (signModel m) (rawTau (signModel m) (W2sign m)) ∧
    (∀ T ∈ assignments (signModel m),
      armMean (W2sign m) T true = W2q m T ∧
      rawSigma2 (signModel m) (W2sign m) T = (1-W2q m T^2)/(4*(2*m : ℕ)) ∧
      W2U m T = 2*((2*m : ℕ)-(1 : ℝ))/Real.sqrt (2*m : ℕ)*Real.sqrt (1-W2q m T^2) ∧
      W2R m T = ((2*m : ℕ)-(1 : ℝ))*(1-W2q m T^2)/(2*m : ℕ))

/-- Discrete support gap, range and exact mean deficit, conditional on the exact
formulas in L2. Since 0≤K≤m, interior K gives 1-q²≥4(m-1)/m²;
clearing positive denominators gives U²≥9 for m≥2. The expectation of the
affine function of q² gives 2/n. No convergence theorem is needed here. -/
def T14_L3 : Prop := T14_L2 → W2T14Finite

/-- Probability limits from the exact finite formulas. Markov applied to q²
shows q²→0; continuity of sqrt at 1 gives U/sqrt(n)→2. Its lower tail,
together with sqrt(n)→infinity, gives divergence. Squeeze the corrected tails
using the existing 2/(n*kappa) bound. Works for every strict size subsequence. -/
def T14_L4 : Prop := W2T14Finite → W2T14Limits

/-- Export the corrected complier chain, including its exact first equality.
At the LATE both population and complier means agree across arms. Expand the
square about the common complier mean, relax delta to max(delta,0), apply
weighted AM-GM, and use group_variance_second_moment for the last step. -/
def T2_L1 : Prop := W2T2GroupChain

/-- Pass from the complier chain to the full-population C.8 inequality.
Outside the complier set the contrast is zero. Enlarge nonnegative sums;
for a singleton complier its contrast is zero directly from the LATE.
Then multiply by the nonnegative pi²(1-pi)²/(n-1). -/
def T2_L2 : Prop := W2T2GroupChain → W2T2Scaled

/-- Residual-square bound preceding E.10, allowing zero residual variances.
The intercept normal equation centers both residual schedules. Expand the
square sum, use Xi's covariance bound and weighted AM-GM with nonnegative
delta_plus, and multiply by the positive n-1. -/
def T2_L3 : Prop := W2T2Residual

/-- Export the exact grid moment identities. Induct on real-valued sums of
indices and their squares, expand the centered grid, and clear n>0.
Each grid coordinate has absolute value strictly below one, giving strict
mean fourth moment <1; n≥2 gives the lower bound 1/4 on its second moment. -/
def T4_L1 : Prop := W2T4Grid

/-- Six-unit population membership and observed full-rank exact fits.
Compute the population Gram, coefficients, residuals, LATE and grid moments
by Fin.sum_univ_succ. The 20 distinct triples have positive within-arm
covariate variance, so exact arm fits give observed statistic zero.
Heterogeneity is witnessed by indices 0 and 1. -/
def T4_L2 : Prop :=
  Xi W2Six 0 (1/4) 4 (1/2) (1/4) ∧ late W2Six.pop = 7/3 ∧
    (∃ i j, W2Six.pop.y i true-W2Six.pop.y i false ≠
      W2Six.pop.y j true-W2Six.pop.y j false) ∧
    (assignments W2Six.pop).card = 20 ∧
    (∀ O ∈ assignments W2Six.pop,
      adjustedAR W2Six (observedW W2Six.pop (7/3) O) O = 0 ∧
      ∀ α : ℝ, (0 < α ∧ α < 1) → adjustedAccepted W2Six (7/3) α O)

/-- Exact reassignment count for the six-unit model. Enumerate the twenty
triples and the 400 pairs, using the two-by-two inverse formula for each
nonsingular arm. A statistic has nonzero square iff its extended absolute
statistic is nonzero. Its numerator and residual sum of squares are rational,
so use kernel-checked rational arithmetic and avoid evaluating square roots. -/
def T4_L3 : Prop :=
  (((assignments W2Six.pop).product (assignments W2Six.pop)).filter fun OT =>
    adjustedAR W2Six (observedW W2Six.pop (7/3) OT.1) OT.2 ≠ 0).card = 312

/-- Export exact fitted coefficients and zero residual/statistic identities, and
extend acceptance to every deterministic completion on singular arms. Use the
population-intercept identity and mean_w_equal_at_late, then the exact-fit
recovery argument in PrintedTheorem2.n3_proof. For arbitrary completions the
full-rank event still has statistic zero and any extended quantile is nonnegative;
its probability is at least 1-1548/(n-1). No assertion about singular fits is needed. -/
def T4_L4 : Prop := W2T4Fits

/-- General small-kurtosis rigidity. Cauchy-Schwarz gives
(sum q²)²≤n sum q⁴. Taking fourth powers of the assumed root bound implies
A²≥(n-1)/n unless every coordinate vanishes. This sharp finite threshold
is the common input to both small-moment necessity arguments. -/
def T5_L1 : Prop :=
  ∀ {n : ℕ} (q : Fin n → ℝ) (A : ℝ), 2 ≤ n → 0 ≤ A →
    A^2 < ((n : ℝ)-1)/(n : ℝ) →
    fourthNorm q ≤ A*Real.sqrt ((∑ i, q i^2)/((n : ℝ)-1)) → ∀ i, q i = 0

/-- Nominal raw worst-case liminf forces A≥1, using L1.
For A<1 the threshold in L1 holds eventually. Apply it to both centered
adjusted schedules, equate their means at the LATE, and obtain coverage one.
On an unbounded nonempty-size set the liminf is one; on a bounded one it is
top. Neither is nominal for alpha in (0,1). -/
def T5_L2 : Prop := T5_L1 →
  ∀ δ r A α : ℝ, δ < 1 → (0 < r ∧ r ≤ 1/2) → 0 < A → (0 < α ∧ α < 1) →
    Filter.liminf (fun n => infCoverageTheta n δ r A α)
      (atTop ⊓ Filter.principal (thetaSizes δ r A)) = ENNReal.ofReal (1-α) → 1 ≤ A

/-- Nondegenerate raw sharpness witness with one complier and balanced signs.
The complier covariance is zero even for arbitrarily negative delta.
Its centered fourth norm is one and variance is n/(n-1)>0, so every A≥1
works. Complete randomization has n1=n/2 and thus every allowed r works. -/
def T5_L3 : Prop :=
  ∀ δ r A : ℝ, δ < 1 → (0 < r ∧ r ≤ 1/2) → 1 ≤ A → ∀ j,
    Theta (W2RawSharpModel j) δ r A ∧
    (∀ i, (W2RawSharpModel j).y i true = (W2RawSharpModel j).y i false) ∧
    0 < popVar (fun i => (W2RawSharpModel j).y i false)

/-- Necessary covariate-moment feasibility: every nonempty Xi class with k>0
has e²≤A. Use a coordinate unit vector in its Rayleigh bound and
Cauchy-Schwarz (mean x_s²)²≤mean x_s⁴. ValidDesign ensures n>0. -/
def T5_L4 : Prop :=
  ∀ {n k : ℕ} (P : CovPopulation n k) (δ e A B r : ℝ),
    0 < k → 0 < e → Xi P δ e A B r → e^2 ≤ A

/-- Nominal adjusted worst-case liminf forces B≥1, using L1.
For B<1, center the population residuals with their intercept normal equation
and apply L1 eventually. T2C_zero_coverage_seq and T2C_U_uniform_eventual
then give coverage tending uniformly to one. Include the bottom-filter case. -/
def T5_L5 : Prop := T5_L1 →
  ∀ (k : ℕ) (δ e A B r α : ℝ), 0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
    (0 < r ∧ r ≤ 1/2) → (0 < α ∧ α < 1) →
    Filter.liminf (fun n => infCoverageXi n k δ e A B r α)
      (atTop ⊓ Filter.principal (xiSizes k δ e A B r)) = ENNReal.ofReal (1-α) → 1 ≤ B

/-- Negative-delta obstruction, finite part. For delta<-1, covariance
Cauchy-Schwarz and Xi's lower bound force the product of residual variances
to vanish. D.5 then shows V≤(1-r)C, including the all-zero case.
Here C is the usual conservative oracle variance (the sum of arm terms). -/
def T5_L6 : Prop :=
  ∀ {n k : ℕ} (P : CovPopulation n k) (δ e A B r : ℝ),
    δ < -1 → 0 < e → (0 < r ∧ r ≤ 1/2) → Xi P δ e A B r →
    popVar (residual P true (late P.pop))*popVar (residual P false (late P.pop)) = 0 ∧
    designVariance P.pop (oracleTau P (late P.pop)) ≤
      (1-r)*(popVar (residual P true (late P.pop))/(P.pop.n1 : ℝ)+
        popVar (residual P false (late P.pop))/controlSize P.pop)

/-- A fixed strict conservative-variance ratio yields a uniform positive
coverage margin on every positive-residual sequence. Choose normal cutoffs
c,a,b with F(c)>1-alpha and sqrt(1-r)c<a<b but F(b)<1-alpha.
Repeat T2C_positive_coverage with V≤(1-r)C, retaining its existing numerator,
sigma and pooled-response error limits. gamma depends only on the fixed
parameters, never on the sequence. This is the sole new coverage-margin step. -/
def T5_L7 : Prop :=
  ∀ (k : ℕ) (δ e A B r α : ℝ), 0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
    (0 < r ∧ r ≤ 1/2) → (0 < α ∧ α < 1) →
    ∃ γ : ℝ, 0 < γ ∧ γ < α ∧
      ∀ (sizes : ℕ → ℕ), StrictMono sizes → ∀ (P : ∀ j, CovPopulation (sizes j) k),
        (∀ j, Xi (P j) δ e A B r) →
        (∀ j, 0 < popVar (residual (P j) true (late (P j).pop))+
          popVar (residual (P j) false (late (P j).pop))) →
        (∀ j, designVariance (P j).pop (oracleTau (P j) (late (P j).pop)) ≤
          (1-r)*(popVar (residual (P j) true (late (P j).pop))/((P j).pop.n1 : ℝ)+
            popVar (residual (P j) false (late (P j).pop))/controlSize (P j).pop)) →
        ∀ᶠ j in atTop, 1-α+γ ≤ adjustedCoverage (P j) (late (P j).pop) α

/-- Convert the finite obstruction and sequential margin to necessity of
delta≥-1. Uniformize the positive-residual branch using T2C_U_uniform_eventual;
the zero branch uses T2C_zero_coverage_seq. The resulting eventual uniform
margin contradicts nominal liminf, with bottom filter treated separately. -/
def T5_L8 : Prop := T5_L6 → T5_L7 →
  ∀ (k : ℕ) (δ e A B r α : ℝ), 0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
    (0 < r ∧ r ≤ 1/2) → (0 < α ∧ α < 1) →
    Filter.liminf (fun n => infCoverageXi n k δ e A B r α)
      (atTop ⊓ Filter.principal (xiSizes k δ e A B r)) = ENNReal.ofReal (1-α) → -1 ≤ δ

/-- Sign-cube orthogonality and moments. Use W2CubeEquiv to sum over
j+1 copies of the Boolean cube. Flipping one coordinate pairs each odd
character with its negative. Distinct coordinates and the response coordinate
are orthogonal; each squared sign is one. sqrt(e)^2=e since e>0. -/
def T5_L9 : Prop :=
  ∀ (k : ℕ) (e : ℝ) (j : ℕ), 0 < k → 0 < e →
    let P := W2CubeModel k e j
    (∑ i, P.pop.y i false) = 0 ∧
    mean (fun i => P.pop.y i false^2) = 1 ∧ mean (fun i => P.pop.y i false^4) = 1 ∧
    (∀ s, (∑ i, P.x i s) = 0) ∧
    (∀ s t, mean (fun i => P.x i s*P.x i t) = if s=t then e else 0) ∧
    (∀ s, mean (fun i => P.x i s^4) = e^2) ∧
    (∀ s, mean (fun i => P.x i s*P.pop.y i false) = 0)

/-- Admissibility of the cube at the original fixed constants, using L9.
Its full Gram is diag(1,e,...,e), its score is zero, and its residual is the
response sign with variance n/(n-1). Thus B≥1, delta≥-1 and e²≤A suffice.
The size is even and the design exactly balanced. -/
def T5_L10 : Prop := T5_L9 →
  ∀ (k : ℕ) (δ e A B r : ℝ), 0 < k → -1 ≤ δ → δ < 1 → 0 < e → e^2 ≤ A → 1 ≤ B →
    (0 < r ∧ r ≤ 1/2) → ∀ j,
    Xi (W2CubeModel k e j) δ e A B r ∧
    late (W2CubeModel k e j).pop = 0 ∧
    (∀ a, residual (W2CubeModel k e j) a 0 = fun i => (W2CubeModel k e j).pop.y i false) ∧
    0 < popVar (residual (W2CubeModel k e j) false (late (W2CubeModel k e j).pop))

/-- Two-sided studentized CDF convergence for adjusted constant-effect models.
The observed response is the fixed baseline; population residual schedules
coincide, hence oracle V=C exactly. T2C_oracle_abs_cdf plus the existing
numerator and sigma error limits sandwich the feasible absolute CDF between
F(t-epsilon) and F(t+epsilon). Continuity of F closes both sides. Handle
zero estimated variance via absStudent; positive limiting scale confines
that event to a sigma-error event. No arm-rank assumption is added. -/
def T5_L11 : Prop :=
  ∀ (sizes : ℕ → ℕ), StrictMono sizes → ∀ (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k)
    (δ e A B r : ℝ), 0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
    (0 < r ∧ r ≤ 1/2) → (∀ j, Xi (P j) δ e A B r) →
    (∀ j, ∃ β : ℝ, ∀ i, (P j).pop.y i true = (P j).pop.y i false+β) →
    (∀ j, 0 < popVar (residual (P j) false (late (P j).pop))) →
    ∀ t : ℝ, 0 < t → Tendsto (fun j => probability (P j).pop (fun S =>
      adjustedAR (P j) (fun i => (P j).pop.y i false) S ≤ ENNReal.ofReal t))
      atTop (nhds (W2AbsNormalCDF t))

/-- Existing certified counterexample, augmented by exact counting and limits. -/
theorem T14_assembly (h1 : T14_L1) (h2 : T14_L2) (h3 : T14_L3) (h4 : T14_L4) :
    T14WholeStatement := by
  exact ⟨restrictedT14, h1, h3 h2, h4 (h3 h2)⟩

/-- All newly exported twelve-unit details are proved finite calculations. -/
theorem T1_assembly : T1WholeStatement := by
  exact ⟨restrictedT1, t1_details⟩

/-- The final bounds are already certified; new leaves export their proof chains. -/
theorem T2_assembly (h1 : T2_L1) (h2 : T2_L2) (h3 : T2_L3) : T2WholeStatement := by
  refine ⟨restrictedT2, h1, h2 h1, h3, t2_inclusions, ?_⟩
  constructor
  · intro n P δ r A hd hδ hr hA hP
    simpa only [max_eq_left hd] using restrictedT2.1 P δ r A hδ hr hA hP
  · intro n k P δ e A B r hk hd hδ he hA hB hr hP
    simpa only [max_eq_left hd] using restrictedT2.2 P δ e A B r hk hδ he hA hB hr hP

/-- Retain the certified class-wide counterexamples and add their missing details. -/
theorem T4_assembly (h1 : T4_L1) (h2 : T4_L2) (h3 : T4_L3) (h4 : T4_L4) :
    T4WholeStatement := by
  refine ⟨restrictedT4, t4_raw_zeros, h4, t4_ranks, h1, ?_, t4_inf_bounds⟩
  rcases h2 with ⟨hXi, hl, hh, hc, ho⟩
  exact ⟨hXi, hl, hh, hc, ho, h3⟩

/-- Necessity constructs witnesses inside the original fixed classes.
The two uniform lower bounds and raw sharpness are existing certified results. -/
theorem T5_assembly (h1 : T5_L1) (h2 : T5_L2) (h3 : T5_L3) (h4 : T5_L4)
    (h5 : T5_L5) (h6 : T5_L6) (h7 : T5_L7) (h8 : T5_L8)
    (h9 : T5_L9) (h10 : T5_L10) (h11 : T5_L11) : T5WholeStatement := by
  refine ⟨?_, ?_, restrictedT5.2.2, ?_, ?_, restrictedT4.2.2.1, restrictedT4.2.2.2⟩
  · intro δ r A α hδ hr hA hα
    have h := AronowAudit.P002.Wave1.corrected_theorem1_proof δ r A α hδ hr hA hα
    simpa only [← infCoverageTheta_eq, ← thetaSizes_eq] using h
  · intro k δ e A B r α hk hδ he hA hB hr hα
    have h := AronowAudit.P002.Wave1.corrected_theorem2_proof k δ e A B r α hk hδ he hA hB hr hα
    simpa only [← infCoverageXi_eq, ← xiSizes_eq] using h
  · intro δ r A α hδ hr hA hα hlim
    have hA1 := h2 h1 δ r A α hδ hr hA hα hlim
    let sizes : ℕ → ℕ := fun j => 2*(j+1)
    have hmono : StrictMono sizes := by intro a b hab; dsimp [sizes]; omega
    have hP (j : ℕ) : Theta (W2RawSharpModel j) δ r A := (h3 δ r A hδ hr hA1 j).1
    have hc (j : ℕ) : ∃ β : ℝ, ∀ i,
        (W2RawSharpModel j).y i true = (W2RawSharpModel j).y i false+β := by
      refine ⟨0, ?_⟩
      intro i; simpa using (h3 δ r A hδ hr hA1 j).2.1 i
    have hn (j : ℕ) : 0 < popVar (fun i => (W2RawSharpModel j).y i false) :=
      (h3 δ r A hδ hr hA1 j).2.2
    have hnom := restrictedT5.2.2 sizes hmono W2RawSharpModel δ r A α hδ hr hA hα hP hc hn
    exact ⟨sizes, W2RawSharpModel, hmono, hP, hc, hn, hnom.1⟩
  · intro k δ e A B r α hk hδ he hA hB hr hα hlim
    have hB1 := h5 h1 k δ e A B r α hk hδ he hA hB hr hα hlim
    have hd1 := h8 h6 h7 k δ e A B r α hk hδ he hA hB hr hα hlim
    obtain ⟨n, Q, hQ⟩ := exists_xi_of_nominal k δ e A B r α hlim
    have heA := h4 Q δ e A B r hk he hQ
    let sizes : ℕ → ℕ := W2CubeSize k
    let P : ∀ j, CovPopulation (sizes j) k := W2CubeModel k e
    have hmono : StrictMono sizes := by
      intro a b hab
      dsimp [sizes, W2CubeSize]
      exact Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
    have hcube (j : ℕ) := h10 h9 k δ e A B r hk hd1 hδ he heA hB1 hr j
    have hP (j : ℕ) : Xi (P j) δ e A B r := (hcube j).1
    have hc (j : ℕ) : ∃ β : ℝ, ∀ i, (P j).pop.y i true = (P j).pop.y i false+β := by
      exact ⟨0, fun i => by simp [P, W2CubeModel]⟩
    have hn (j : ℕ) : 0 < popVar (residual (P j) false (late (P j).pop)) := (hcube j).2.2.2
    have hCDF := h11 sizes hmono k P δ e A B r hk hδ he hA hB hr hP hc hn
    have hnom := adjusted_nominal_of_cdf sizes k P δ e A B r α hα hP hc hCDF
    exact ⟨sizes, P, hmono, hP, hc, hn, hnom⟩

end
end SAP.P002a.WH.W2
