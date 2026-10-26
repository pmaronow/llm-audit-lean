import Mathlib

namespace AronowAudit.P020

open scoped BigOperators
open Filter

noncomputable section

/-- "the expected value ... (over all randomizations)", p. 42 (PDF p. 4).
A finite randomization law has nonnegative weights summing to one. Its support
may vary with population size; only assignments are random. -/
structure FiniteLaw (Ω : Type*) where
  support : Finset Ω
  weight : Ω → ℝ
  nonneg : ∀ ω ∈ support, 0 ≤ weight ω
  total : ∑ ω ∈ support, weight ω = 1

/-- Expectation over the randomization distribution, p. 42: a weighted finite sum. -/
def expectation {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) : ℝ :=
  ∑ ω ∈ L.support, L.weight ω * T ω

/-- "bias ... the difference between the expected value of the estimator ...
and the parameter of interest", p. 42 (PDF p. 4). -/
def designBias {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (d : ℝ) : ℝ :=
  expectation L T - d

/-- Design variance: expectation of the squared deviation from design expectation;
Section 4.2, pp. 50-51 (PDF pp. 12-13). -/
def designVariance {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) : ℝ :=
  expectation L (fun ω => (T ω - expectation L T)^2)

/-- Covariance over randomizations, equations (7)-(8), pp. 44-45. -/
def designCovariance {Ω : Type*} (L : FiniteLaw Ω) (T U : Ω → ℝ) : ℝ :=
  expectation L (fun ω => (T ω - expectation L T) * (U ω - expectation L U))

/-- "efficiency (typically mean square error)", p. 40 (PDF p. 2), made explicit
in correction P020-E001: E[(T - Δ)^2]. -/
def meanSquaredError {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (d : ℝ) : ℝ :=
  expectation L (fun ω => (T ω - d)^2)

/-- P(|T - Δ| > ε), the finite randomization probability used for convergence
in probability, Section 3.3, p. 45 (PDF p. 7). -/
def errorProbability {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (d ε : ℝ) : ℝ := by
  classical
  exact ∑ ω ∈ L.support, if ε < |T ω - d| then L.weight ω else 0

/-- "converges in probability ... as h → ∞", p. 45. Populations may have
different finite assignment spaces. Indices are natural numbers, and h = 0
is harmless for the atTop limit. -/
def DesignConsistent {Ω : ℕ → Type*} (L : ∀ h, FiniteLaw (Ω h))
    (T : ∀ h, Ω h → ℝ) (d : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun h => errorProbability (L h) (T h) (d h) ε) atTop (nhds 0)

/-- Linearity of design expectation: finite-sum lemma for pp. 42, 54 and 71. -/
theorem expectation_add {Ω : Type*} (L : FiniteLaw Ω) (T U : Ω → ℝ) :
    expectation L (fun ω => T ω + U ω) = expectation L T + expectation L U := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

/-- Linearity under subtraction, used in equation (1), p. 41. -/
theorem expectation_sub {Ω : Type*} (L : FiniteLaw Ω) (T U : Ω → ℝ) :
    expectation L (fun ω => T ω - U ω) = expectation L T - expectation L U := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

/-- A constant has its own design expectation, p. 42. -/
theorem expectation_const {Ω : Type*} (L : FiniteLaw Ω) (c : ℝ) :
    expectation L (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul, L.total]

/-- A coefficient fixed before randomization factors out of expectation,
equation (22), p. 54. -/
theorem expectation_mul_const {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (c : ℝ) :
    expectation L (fun ω => T ω * c) = expectation L T * c := by
  simp [expectation, ← mul_assoc, ← Finset.sum_mul]

/-- Nonnegative random variables have nonnegative design expectation. -/
theorem expectation_nonneg {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ)
    (hT : ∀ ω ∈ L.support, 0 ≤ T ω) : 0 ≤ expectation L T := by
  exact Finset.sum_nonneg (fun ω hω => mul_nonneg (L.nonneg ω hω) (hT ω hω))

/-- Variance over a finite randomization distribution is nonnegative (T2(a)). -/
theorem designVariance_nonneg {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) :
    0 ≤ designVariance L T := by
  exact expectation_nonneg L _ (fun _ _ => sq_nonneg _)

/-- Correction P020-E001(a), pp. 40 and 42: MSE equals variance plus squared bias
for each fixed finite population; no limit assumption is needed. -/
theorem mse_bias_variance {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (d : ℝ) :
    meanSquaredError L T d = designVariance L T + (designBias L T d)^2 := by
  unfold meanSquaredError
  calc
    expectation L (fun ω => (T ω - d)^2) =
      expectation L (fun ω => (T ω - expectation L T)^2 +
        (T ω - expectation L T) * (2 * (expectation L T - d)) +
        (expectation L T - d)^2) := by congr 1; funext ω; ring
    _ = designVariance L T + (designBias L T d)^2 := by
      rw [expectation_add, expectation_add, expectation_mul_const,
        expectation_sub, expectation_const, expectation_const]
      unfold designVariance designBias
      ring

/-- Correction P020-E001(a): the squared-bias term is a lower bound on MSE (T2). -/
theorem squared_bias_le_mse {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (d : ℝ) :
    (designBias L T d)^2 ≤ meanSquaredError L T d := by
  rw [mse_bias_variance]
  linarith [designVariance_nonneg L T]

/-- Correction P020-E001(c): finite-sum Markov bound for squared estimation error,
P(|U - Δ| > ε) ≤ MSE(U)/ε², with ε > 0 (T2 finite lemma). -/
theorem mse_markov_bound {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ)
    (d ε : ℝ) (hε : 0 < ε) :
    errorProbability L T d ε ≤ meanSquaredError L T d / ε^2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  unfold errorProbability meanSquaredError expectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω hω
  split_ifs with he
  · have habs : ε^2 ≤ (T ω - d)^2 := by
      have hs := sq_le_sq₀ (le_of_lt hε) (abs_nonneg (T ω - d)) |>.2 (le_of_lt he)
      simpa [sq_abs] using hs
    exact mul_le_mul_of_nonneg_left habs (L.nonneg ω hω)
  · simp only [zero_mul]
    exact mul_nonneg (L.nonneg ω hω) (sq_nonneg _)

/-- Correction P020-E001(b): a nonzero limiting bias guarantees eventual MSE
inferiority to a specified comparator whose MSE tends to zero (T2). -/
theorem eventual_mse_inferiority {Ω : ℕ → Type*}
    (L : ∀ h, FiniteLaw (Ω h)) (T U : ∀ h, Ω h → ℝ) (d : ℕ → ℝ)
    (b : ℝ) (hb : b ≠ 0)
    (hBias : Tendsto (fun h => designBias (L h) (T h) (d h)) atTop (nhds b))
    (hMSE : Tendsto (fun h => meanSquaredError (L h) (U h) (d h)) atTop (nhds 0)) :
    ∃ h₀ : ℕ, ∀ h ≥ h₀, meanSquaredError (L h) (U h) (d h) <
      meanSquaredError (L h) (T h) (d h) := by
  have hp : 0 < b^2 / 2 := by positivity
  have hsq : Tendsto (fun h => (designBias (L h) (T h) (d h))^2) atTop (nhds (b^2)) :=
    hBias.pow 2
  have ht : ∀ᶠ h in atTop, b^2 / 2 < (designBias (L h) (T h) (d h))^2 :=
    hsq.eventually_const_lt (by linarith)
  have hu : ∀ᶠ h in atTop, meanSquaredError (L h) (U h) (d h) < b^2 / 2 :=
    hMSE.eventually_lt_const hp
  have he : ∀ᶠ h in atTop, meanSquaredError (L h) (U h) (d h) <
      meanSquaredError (L h) (T h) (d h) := by
    filter_upwards [ht, hu] with h ht hu
    exact lt_of_lt_of_le (hu.trans ht) (squared_bias_le_mse (L h) (T h) (d h))
  exact Filter.eventually_atTop.1 he

/-- Correction P020-E001(c): vanishing MSE implies convergence in probability
for sequences of finite randomization distributions (T2). -/
theorem vanishing_mse_consistent {Ω : ℕ → Type*}
    (L : ∀ h, FiniteLaw (Ω h)) (U : ∀ h, Ω h → ℝ) (d : ℕ → ℝ)
    (hMSE : Tendsto (fun h => meanSquaredError (L h) (U h) (d h)) atTop (nhds 0)) :
    DesignConsistent L U d := by
  intro ε hε
  have hupper : Tendsto (fun h => meanSquaredError (L h) (U h) (d h) / ε^2)
      atTop (nhds 0) := by simpa using hMSE.div_const (ε^2)
  apply squeeze_zero _ (fun h => mse_markov_bound (L h) (U h) (d h) ε hε) hupper
  intro h
  unfold errorProbability
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs
  · exact (L h).nonneg ω hω
  · exact le_rfl

/-- A uniform law on a nonempty finite set. In the cluster experiment every
set of m_t treated clusters is equally likely, Section 3.2, p. 44. -/
def uniformLaw {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) : FiniteLaw Ω where
  support := s
  weight := fun _ => 1 / (s.card : ℝ)
  nonneg := by intros; positivity
  total := by
    have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hs)
    simp [Finset.sum_const, nsmul_eq_mul, hc]

/-- "Let n_j be the number of individuals in the jth cluster" (p. 44),
"Define Y^T_aj = ∑_i Y_aij" (p. 48), and "0 < m_t < M" (p. 44).
Only fixed sizes and potential totals are stored. Every individual population
induces these data; conversely arbitrary real totals are realizable in each
nonempty cluster, so this representation imposes no outcome restriction. -/
structure ClusterPopulation where
  M : ℕ
  mt : ℕ
  mt_pos : 0 < mt
  mt_lt : mt < M
  n : Fin M → ℕ
  n_pos : ∀ j, 0 < n j
  y0 : Fin M → ℝ
  y1 : Fin M → ℝ

/-- Individual-to-cluster aggregation "Y^T_aj = ∑_{i=1}^{n_j}Y_aij",
p. 48 (PDF p. 10). -/
def clusterTotal {n : ℕ} (Y : Fin n → ℝ) : ℝ := ∑ i, Y i

/-- "N = ∑_j n_j", pp. 44 and 48; exact positive integer population size. -/
def populationSize (P : ClusterPopulation) : ℕ := ∑ j, P.n j

/-- The remaining fixed number of control clusters "m_c = M - m_t", p. 44. -/
def controlCount (P : ClusterPopulation) : ℕ := P.M - P.mt

/-- Complete cluster randomization: all m_t-subsets of the M clusters, p. 44. -/
def assignments (P : ClusterPopulation) : Finset (Finset (Fin P.M)) :=
  Finset.univ.powersetCard P.mt

/-- Existence of assignments follows from 0 < m_t < M, p. 44. -/
theorem assignments_nonempty (P : ClusterPopulation) : (assignments P).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  have ht : P.M < P.mt := by
    simpa [assignments] using (Finset.powersetCard_eq_empty.mp he)
  exact (not_lt_of_ge (le_of_lt P.mt_lt)) ht

/-- The only randomness is the uniform allocation of clusters, pp. 41 and 44. -/
def clusterLaw (P : ClusterPopulation) : FiniteLaw (Finset (Fin P.M)) :=
  uniformLaw (assignments P) (assignments_nonempty P)

/-- "Define J_0 as ... D_j = 0 and J_1 as ... D_j = 1", p. 44.
An assignment s is J_1; J_0 is its complement. -/
def controls {M : ℕ} (s : Finset (Fin M)) : Finset (Fin M) := Finset.univ \ s

/-- "Y^T_j = D_j Y^T_1j + (1-D_j)Y^T_0j", p. 48. -/
def observedTotal (P : ClusterPopulation) (s : Finset (Fin P.M)) (j : Fin P.M) : ℝ :=
  if j ∈ s then P.y1 j else P.y0 j

/-- "Δ = (Y^T_1 - Y^T_0)/N", Section 4, p. 48; equation (1), p. 41. -/
def averageTreatmentEffect (P : ClusterPopulation) : ℝ :=
  ((∑ j, P.y1 j) - ∑ j, P.y0 j) / populationSize P

/-- The sum of a cluster feature over J_1 or J_0, Section 3.2, p. 44. -/
def armSum (P : ClusterPopulation) (treatment : Bool) (v : Fin P.M → ℝ)
    (s : Finset (Fin P.M)) : ℝ :=
  ∑ j ∈ (if treatment then s else controls s), v j

/-- "n_t = ∑_{j∈J_1} n_j" and "n_c = ∑_{j∈J_0} n_j", p. 44. -/
def armSize (P : ClusterPopulation) (treatment : Bool) (s : Finset (Fin P.M)) : ℝ :=
  armSum P treatment (fun j => (P.n j : ℝ)) s

/-- "n̄_tj = ∑_{j∈J_1}n_j/m_t" and the control analogue, Appendix B,
p. 71 (PDF p. 33); sizes remain random under cluster allocation. -/
def armMeanSize (P : ClusterPopulation) (treatment : Bool) (s : Finset (Fin P.M)) : ℝ :=
  armSize P treatment s / (if treatment then P.mt else controlCount P)

/-- Difference-in-means equation (6), p. 44: ratios of arm outcome totals to
arm individual counts. On J_a the observed totals equal potential totals Y^T_aj. -/
def differenceInMeans (P : ClusterPopulation) (s : Finset (Fin P.M)) : ℝ :=
  armSum P true P.y1 s / armSize P true s -
  armSum P false P.y0 s / armSize P false s

/-- HT total estimators, equations (11)-(12), p. 48: M/m_a times the arm sum. -/
def htTotal (P : ClusterPopulation) (treatment : Bool) (s : Finset (Fin P.M)) : ℝ :=
  (P.M : ℝ) / (if treatment then P.mt else controlCount P) *
    armSum P treatment (if treatment then P.y1 else P.y0) s

/-- HT ATE estimator equation (13), p. 49: (estimated Y^T_1 - estimated Y^T_0)/N. -/
def horvitzThompson (P : ClusterPopulation) (s : Finset (Fin P.M)) : ℝ :=
  (htTotal P true s - htTotal P false s) / populationSize P

/-- "finite population variance ... divisor M" and covariance, p. 50.
Appendix C uses E and overlines for this mean over clusters, p. 72. -/
def clusterMean {M : ℕ} (v : Fin M → ℝ) : ℝ := (∑ j, v j) / M

/-- Finite-population covariance σ(v_j,w_j), divisor M, p. 50 (PDF p. 12). -/
def clusterCovariance {M : ℕ} (v w : Fin M → ℝ) : ℝ :=
  clusterMean (fun j => (v j - clusterMean v) * (w j - clusterMean w))

/-- Finite-population variance σ²(v_j), divisor M, p. 50 (PDF p. 12). -/
def clusterVariance {M : ℕ} (v : Fin M → ℝ) : ℝ :=
  clusterMean (fun j => (v j - clusterMean v)^2)

/-- "U^T_j = Y^T_j - k(n_j - N/M)", p. 54. This definition is reused
for either potential version and arbitrary fixed cluster features. -/
def differenced {M : ℕ} (v size : Fin M → ℝ) (k : ℝ) : Fin M → ℝ :=
  fun j => v j - k * (size j - clusterMean size)

/-- Potential Des Raj totals U^T_aj, pp. 54-56. -/
def rajPotential (P : ClusterPopulation) (treatment : Bool) (k : ℝ) : Fin P.M → ℝ :=
  differenced (if treatment then P.y1 else P.y0) (fun j => (P.n j : ℝ)) k

/-- Des Raj total estimator, equations (20)-(21), p. 54. k is one coefficient
fixed before analysis, used in both arms. -/
def rajTotal (P : ClusterPopulation) (treatment : Bool) (k : ℝ)
    (s : Finset (Fin P.M)) : ℝ :=
  (P.M : ℝ) / (if treatment then P.mt else controlCount P) *
    armSum P treatment (rajPotential P treatment k) s

/-- Des Raj ATE estimator following equation (22), p. 54. -/
def desRaj (P : ClusterPopulation) (k : ℝ) (s : Finset (Fin P.M)) : ℝ :=
  (rajTotal P true k s - rajTotal P false k s) / populationSize P

/-- OLS slope of observed cluster totals on sizes, with an intercept,
Section 5.3, pp. 57-58 and Appendix B: σ(n,Y^T)/σ²(n). -/
def observedSlope (P : ClusterPopulation) (s : Finset (Fin P.M)) : ℝ :=
  clusterCovariance (fun j => (P.n j : ℝ)) (observedTotal P s) /
    clusterVariance (fun j => (P.n j : ℝ))

/-- Cluster means preserve subtraction, finite algebra behind Appendix C. -/
theorem clusterMean_sub {M : ℕ} (v w : Fin M → ℝ) :
    clusterMean (fun j => v j - w j) = clusterMean v - clusterMean w := by
  simp [clusterMean, Finset.sum_sub_distrib, sub_div]

/-- Cluster means preserve addition, finite algebra behind Appendix C. -/
theorem clusterMean_add {M : ℕ} (v w : Fin M → ℝ) :
    clusterMean (fun j => v j + w j) = clusterMean v + clusterMean w := by
  simp [clusterMean, Finset.sum_add_distrib, add_div]

/-- Cluster means preserve multiplication by fixed constants (Appendix C). -/
theorem clusterMean_mul {M : ℕ} (v : Fin M → ℝ) (k : ℝ) :
    clusterMean (fun j => v j * k) = clusterMean v * k := by
  simp [clusterMean, ← Finset.sum_mul]; ring

/-- With M > 0 a constant cluster feature has that constant mean, p. 50. -/
theorem clusterMean_const {M : ℕ} (hM : 0 < M) (k : ℝ) :
    clusterMean (fun _ : Fin M => k) = k := by
  have h : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  simp [clusterMean, h]

/-- Centered size has zero cluster mean (the zero in equation (35), p. 72). -/
theorem centered_mean_zero {M : ℕ} (hM : 0 < M) (v : Fin M → ℝ) :
    clusterMean (fun j => v j - clusterMean v) = 0 := by
  rw [clusterMean_sub, clusterMean_const hM]; ring

/-- Differencing by k times centered size preserves the cluster mean;
Appendix C, corrected equation (35), p. 72 (T8). -/
theorem differenced_mean {M : ℕ} (hM : 0 < M) (v size : Fin M → ℝ) (k : ℝ) :
    clusterMean (differenced v size k) = clusterMean v := by
  unfold differenced
  simp_rw [mul_comm k]
  rw [clusterMean_sub, clusterMean_mul, centered_mean_zero hM]
  ring

/-- Covariance equals mean of products minus product of means, the first line
of corrected equation (35), Appendix C, p. 72 (T8). -/
theorem clusterCovariance_product {M : ℕ} (hM : 0 < M) (v w : Fin M → ℝ) :
    clusterCovariance v w = clusterMean (fun j => v j * w j) - clusterMean v * clusterMean w := by
  unfold clusterCovariance
  have he : (fun j => (v j - clusterMean v) * (w j - clusterMean w)) =
      (fun j => v j * w j - v j * clusterMean w - w j * clusterMean v +
        clusterMean v * clusterMean w) := by funext j; ring
  rw [he, clusterMean_add, clusterMean_sub, clusterMean_sub,
    clusterMean_mul, clusterMean_mul, clusterMean_const hM]
  ring

/-- Corrected equations (33)-(34), Appendix C, p. 72: the variance of
Y^T_a - k(n-N/M) expands to σ²(Y^T_a)+k²σ²(n)-2kσ(Y^T_a,n) (T8). -/
theorem differenced_variance {M : ℕ} (hM : 0 < M) (v size : Fin M → ℝ) (k : ℝ) :
    clusterVariance (differenced v size k) = clusterVariance v +
      k^2 * clusterVariance size - 2 * k * clusterCovariance v size := by
  unfold clusterVariance
  rw [differenced_mean hM]
  have he : (fun j => (differenced v size k j - clusterMean v)^2) =
      (fun j => (v j - clusterMean v)^2 + (size j - clusterMean size)^2 * k^2 -
        ((v j - clusterMean v) * (size j - clusterMean size)) * (2 * k)) := by
    funext j; unfold differenced; ring
  rw [he, clusterMean_sub, clusterMean_add, clusterMean_mul, clusterMean_mul]
  unfold clusterCovariance
  ring

/-- Corrected equation (35), p. 72: both factors are inside the expectation
bracket, and the covariance expansion includes both size covariances (T8). -/
theorem differenced_covariance {M : ℕ} (hM : 0 < M)
    (v w size : Fin M → ℝ) (k : ℝ) :
    clusterCovariance (differenced v size k) (differenced w size k) =
      clusterMean (fun j => (v j - k * (size j - clusterMean size)) *
        (w j - k * (size j - clusterMean size))) - clusterMean v * clusterMean w ∧
    clusterCovariance (differenced v size k) (differenced w size k) =
      clusterCovariance v w - k * clusterCovariance v size -
        k * clusterCovariance w size + k^2 * clusterVariance size := by
  constructor
  · rw [clusterCovariance_product hM, differenced_mean hM, differenced_mean hM]
    rfl
  · unfold clusterCovariance
    rw [differenced_mean hM, differenced_mean hM]
    have he : (fun j => (differenced v size k j - clusterMean v) *
        (differenced w size k j - clusterMean w)) =
        (fun j => (v j - clusterMean v) * (w j - clusterMean w) -
          ((v j - clusterMean v) * (size j - clusterMean size)) * k -
          ((w j - clusterMean w) * (size j - clusterMean size)) * k +
          (size j - clusterMean size)^2 * k^2) := by
      funext j; unfold differenced; ring
    rw [he, clusterMean_add, clusterMean_sub, clusterMean_sub,
      clusterMean_mul, clusterMean_mul, clusterMean_mul]
    unfold clusterVariance
    ring

/-- The fixed population size N is positive since all M clusters are nonempty
and 0 < m_t < M, standing assumptions, pp. 44 and 48. -/
theorem populationSize_pos (P : ClusterPopulation) : 0 < populationSize P := by
  have hM : 0 < P.M := lt_trans P.mt_pos P.mt_lt
  have hne : (Finset.univ : Finset (Fin P.M)).Nonempty :=
    ⟨⟨0, hM⟩, Finset.mem_univ _⟩
  exact Finset.sum_pos (fun j _ => P.n_pos j) hne

/-- The sizes entering differencing have mean N/M, p. 54. -/
theorem mean_size (P : ClusterPopulation) :
    clusterMean (fun j => (P.n j : ℝ)) = (populationSize P : ℝ) / P.M := by
  simp [clusterMean, populationSize, Nat.cast_sum]


/-- A uniform design expectation is the arithmetic average over its support,
finite randomization reading of p. 42. -/
theorem uniform_expectation {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty)
    (v : Ω → ℝ) : expectation (uniformLaw s hs) v = (∑ ω ∈ s, v ω) / s.card := by
  simp [expectation, uniformLaw, ← Finset.mul_sum, div_eq_mul_inv]
  ring

/-- Counting treatment subsets containing one fixed cluster gives
choose(M-1,m_t-1), the inclusion probability step underlying p. 48. -/
theorem assignment_inclusion_count (P : ClusterPopulation) (j : Fin P.M) :
    ((assignments P).filter (fun s => j ∈ s)).card = (P.M - 1).choose (P.mt - 1) := by
  have h := Finset.card_filter_powersetCard_subset ({j} : Finset (Fin P.M))
    Finset.univ P.mt (Finset.subset_univ _) (by simpa using Nat.succ_le_of_lt P.mt_pos)
  simpa [assignments] using h

/-- Exact first moment of a selected cluster sum, obtained by counting all
m_t-subsets rather than assuming their inclusion probabilities, pp. 44,48,46. -/
theorem expected_treatment_sum (P : ClusterPopulation) (v : Fin P.M → ℝ) :
    expectation (clusterLaw P) (armSum P true v) =
      (P.mt : ℝ) / P.M * ∑ j, v j := by
  classical
  have hsum : (∑ s ∈ assignments P, ∑ j ∈ s, v j) =
      ((P.M - 1).choose (P.mt - 1) : ℝ) * ∑ j, v j := by
    calc
      (∑ s ∈ assignments P, ∑ j ∈ s, v j) =
          ∑ s ∈ assignments P, ∑ j : Fin P.M, if j ∈ s then v j else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        simp
      _ = ∑ j : Fin P.M, ∑ s ∈ assignments P, if j ∈ s then v j else 0 :=
        Finset.sum_comm
      _ = _ := by
        simp_rw [← Finset.sum_filter]
        simp [assignment_inclusion_count, ← Finset.mul_sum]
  have hM1 : P.M - 1 + 1 = P.M := by have := P.mt_pos; have := P.mt_lt; omega
  have ht1 : P.mt - 1 + 1 = P.mt := by have := P.mt_pos; omega
  have hcomb : P.M * (P.M - 1).choose (P.mt - 1) = P.M.choose P.mt * P.mt := by
    simpa only [hM1, ht1] using Nat.add_one_mul_choose_eq (P.M - 1) (P.mt - 1)
  have hcombR : (P.M : ℝ) * ((P.M - 1).choose (P.mt - 1) : ℝ) =
      (P.M.choose P.mt : ℝ) * (P.mt : ℝ) := by exact_mod_cast hcomb
  have hM : (P.M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt))
  have hC : (P.M.choose P.mt : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (le_of_lt P.mt_lt)))
  rw [clusterLaw, uniform_expectation]
  change (∑ s ∈ assignments P, ∑ j ∈ s, v j) / (assignments P).card = _
  rw [hsum]
  simp only [assignments, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  field_simp
  nlinarith only [congrArg (fun x : ℝ => x * ∑ j, v j) hcombR]

/-- Finite design covariance equals E[TU]-E[T]E[U], equations (7),(31). -/
theorem designCovariance_product {Ω : Type*} (L : FiniteLaw Ω) (T U : Ω → ℝ) :
    designCovariance L T U = expectation L (fun ω => T ω * U ω) -
      expectation L T * expectation L U := by
  unfold designCovariance
  have he : (fun ω => (T ω - expectation L T) * (U ω - expectation L U)) =
      (fun ω => T ω * U ω - T ω * expectation L U - U ω * expectation L T +
        expectation L T * expectation L U) := by funext ω; ring
  rw [he, expectation_add, expectation_sub, expectation_sub,
    expectation_mul_const, expectation_mul_const, expectation_const]
  ring

/-- Strict positivity survives finite expectation if the variable is positive
on the support, the denominator condition of the ratio identity (7). -/
theorem expectation_pos {Ω : Type*} (L : FiniteLaw Ω) (v : Ω → ℝ)
    (hv : ∀ ω ∈ L.support, 0 < v ω) : 0 < expectation L v := by
  obtain ⟨ω, hω, hw⟩ := (Finset.sum_pos_iff_of_nonneg L.nonneg).1
    (show 0 < ∑ ω ∈ L.support, L.weight ω by rw [L.total]; norm_num)
  apply (Finset.sum_pos_iff_of_nonneg (fun ω hω =>
    mul_nonneg (L.nonneg ω hω) (le_of_lt (hv ω hω)))).2
  exact ⟨ω, hω, mul_pos hw (hv ω hω)⟩
/-- The one-copy randomization means used in the four weak-law limits on
p. 46: for either arm, E[∑_{J_a} v_j] = (m_a/M)∑_j v_j (T17 finite lemma).
This is also the finite-sampling step in equations (8), (11)-(12), and (29)-(30). -/
theorem expected_arm_sum (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ) :
    expectation (clusterLaw P) (armSum P a v) =
      ((if a then P.mt else controlCount P) : ℝ) / P.M * ∑ j, v j := by
  cases a
  · have hcomp : armSum P false v = fun s => (∑ j, v j) - armSum P true v s := by
      funext s
      simpa [armSum, controls] using Finset.sum_sdiff (Finset.subset_univ s) (f := v)
    rw [hcomp, expectation_sub, expectation_const, expected_treatment_sum]
    have hcast : (controlCount P : ℝ) = (P.M : ℝ) - P.mt := by
      simp [controlCount, Nat.cast_sub (le_of_lt P.mt_lt)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hcast]
    have hM : (P.M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt))
    field_simp
    <;> ring
  · exact expected_treatment_sum P v

/-- Printed equation (7), p. 44: the exact Hartley-Ross ratio identity for
positive denominators, under a finite randomization distribution (T11(a)). -/
theorem ratio_expectation_identity {Ω : Type*} (L : FiniteLaw Ω) (u v : Ω → ℝ)
    (hv : ∀ ω ∈ L.support, 0 < v ω) :
    expectation L (fun ω => u ω / v ω) =
      (expectation L u - designCovariance L (fun ω => u ω / v ω) v) /
        expectation L v := by
  rw [designCovariance_product]
  have hu : expectation L (fun ω => u ω / v ω * v ω) = expectation L u := by
    unfold expectation
    apply Finset.sum_congr rfl
    intro ω hω
    change L.weight ω * (u ω / v ω * v ω) = L.weight ω * u ω
    rw [div_mul_cancel₀ _ (ne_of_gt (hv ω hω))]
  rw [hu]
  have hE := ne_of_gt (expectation_pos L v hv)
  field_simp
  <;> ring

/-- Every admissible assignment has the fixed printed arm cluster counts,
|J_1|=m_t, |J_0|=m_c, Section 3.2, p. 44. -/
theorem assignment_arm_counts (P : ClusterPopulation) (s : Finset (Fin P.M))
    (hs : s ∈ assignments P) : s.card = P.mt ∧ (controls s).card = controlCount P := by
  have ht : s.card = P.mt := (Finset.mem_powersetCard.mp hs).2
  refine ⟨ht, ?_⟩
  simp [controls, Finset.card_sdiff_of_subset (Finset.subset_univ s), ht, controlCount]


/-- Both arms contain positive individual counts for every admissible cluster
assignment, because m_t,m_c>0 and every n_j≥1, equation (7), pp. 44-45. -/
theorem arm_size_pos (P : ClusterPopulation) (a : Bool) (s : Finset (Fin P.M))
    (hs : s ∈ assignments P) : 0 < armSize P a s := by
  obtain ⟨htcard, hccard⟩ := assignment_arm_counts P s hs
  have ht : s.Nonempty := Finset.card_pos.mp (by rw [htcard]; exact P.mt_pos)
  have hc : (controls s).Nonempty := Finset.card_pos.mp
    (by rw [hccard]; exact Nat.sub_pos_of_lt P.mt_lt)
  cases a <;> unfold armSize armSum <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact Finset.sum_pos (fun j _ => by exact_mod_cast P.n_pos j) hc
  · exact Finset.sum_pos (fun j _ => by exact_mod_cast P.n_pos j) ht

/-- The expected selected individual count is (m_a/M)N, the denominator
expectation in the bias derivation (8), p. 45. -/
theorem expected_arm_size (P : ClusterPopulation) (a : Bool) :
    expectation (clusterLaw P) (armSize P a) =
      ((if a then P.mt else controlCount P) : ℝ) / P.M * populationSize P := by
  unfold armSize
  rw [expected_arm_sum]
  simp [populationSize, Nat.cast_sum]

/-- Equation (8), p. 45: exact expectation and bias of difference-in-means
under complete cluster randomization, including both arm covariance terms (T11(b)). -/
theorem difference_in_means_bias (P : ClusterPopulation) :
    expectation (clusterLaw P) (differenceInMeans P) = averageTreatmentEffect P -
      (P.M : ℝ) / populationSize P *
        (designCovariance (clusterLaw P)
          (fun s => armSum P true P.y1 s / armSize P true s) (armSize P true) / P.mt -
         designCovariance (clusterLaw P)
          (fun s => armSum P false P.y0 s / armSize P false s) (armSize P false) / controlCount P) ∧
    designBias (clusterLaw P) (differenceInMeans P) (averageTreatmentEffect P) =
      -((P.M : ℝ) / populationSize P) *
        (designCovariance (clusterLaw P)
          (fun s => armSum P true P.y1 s / armSize P true s) (armSize P true) / P.mt -
         designCovariance (clusterLaw P)
          (fun s => armSum P false P.y0 s / armSize P false s) (armSize P false) / controlCount P) := by
  have hvt : ∀ s ∈ (clusterLaw P).support, 0 < armSize P true s :=
    fun s hs => arm_size_pos P true s hs
  have hvc : ∀ s ∈ (clusterLaw P).support, 0 < armSize P false s :=
    fun s hs => arm_size_pos P false s hs
  have hEt := ratio_expectation_identity (clusterLaw P) (armSum P true P.y1) (armSize P true) hvt
  have hEc := ratio_expectation_identity (clusterLaw P) (armSum P false P.y0) (armSize P false) hvc
  rw [expected_arm_sum, expected_arm_size] at hEt hEc
  have hmt : (P.mt : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt P.mt_pos)
  have hmc : (controlCount P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt))
  have hM : (P.M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt))
  have hN : (populationSize P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (populationSize_pos P))
  have he : expectation (clusterLaw P) (differenceInMeans P) = averageTreatmentEffect P -
      (P.M : ℝ) / populationSize P *
        (designCovariance (clusterLaw P)
          (fun s => armSum P true P.y1 s / armSize P true s) (armSize P true) / P.mt -
         designCovariance (clusterLaw P)
          (fun s => armSum P false P.y0 s / armSize P false s) (armSize P false) / controlCount P) := by
    unfold differenceInMeans averageTreatmentEffect
    rw [expectation_sub, hEt, hEc]
    simp only [Bool.false_eq_true, ↓reduceIte]
    field_simp
    <;> ring
  refine ⟨he, ?_⟩
  unfold designBias
  rw [he]
  ring


/-- Left constant factors also leave design expectation, pp. 42 and 54. -/
theorem expectation_const_mul {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (c : ℝ) :
    expectation L (fun ω => c * T ω) = c * expectation L T := by
  simp_rw [mul_comm c]
  exact expectation_mul_const L T c


/-- Each HT potential-total estimator is unbiased, equations (11)-(12), p. 48,
by the proved exact inclusion-count first moment. -/
theorem ht_total_unbiased (P : ClusterPopulation) (a : Bool) :
    expectation (clusterLaw P) (htTotal P a) =
      ∑ j, (if a then P.y1 else P.y0) j := by
  unfold htTotal
  rw [expectation_const_mul, expected_arm_sum]
  have ha : ((if a then P.mt else controlCount P) : ℝ) ≠ 0 := by
    cases a
    · exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt))
    · exact_mod_cast (Nat.ne_of_gt P.mt_pos)
  have hM : (P.M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt))
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> field_simp <;> ring

/-- Differencing by centered size preserves the sum of potential totals,
finite algebra used for unbiasedness after equation (22), p. 54. -/
theorem raj_potential_sum (P : ClusterPopulation) (a : Bool) (k : ℝ) :
    (∑ j, rajPotential P a k j) = ∑ j, (if a then P.y1 else P.y0) j := by
  have hM : 0 < P.M := lt_trans P.mt_pos P.mt_lt
  have he := differenced_mean hM (if a then P.y1 else P.y0) (fun j => (P.n j : ℝ)) k
  unfold clusterMean at he
  have hMr : (P.M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  exact (div_left_inj' hMr).mp he

/-- Fixed-k Des Raj total estimators are unbiased, equations (20)-(22), p. 54. -/
theorem raj_total_unbiased (P : ClusterPopulation) (a : Bool) (k : ℝ) :
    expectation (clusterLaw P) (rajTotal P a k) = ∑ j, (if a then P.y1 else P.y0) j := by
  unfold rajTotal
  rw [expectation_const_mul, expected_arm_sum, raj_potential_sum]
  have ha : ((if a then P.mt else controlCount P) : ℝ) ≠ 0 := by
    cases a
    · exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt))
    · exact_mod_cast (Nat.ne_of_gt P.mt_pos)
  have hM : (P.M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt))
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> field_simp <;> ring

/-- The finite randomization mean of either arm's mean cluster size is N/M,
used in Appendix B equations (29)-(30), p. 71. -/
theorem expected_arm_mean_size (P : ClusterPopulation) (a : Bool) :
    expectation (clusterLaw P) (armMeanSize P a) = (populationSize P : ℝ) / P.M := by
  unfold armMeanSize armSize
  simp_rw [div_eq_mul_inv]
  rw [expectation_mul_const, expected_arm_sum]
  have ha : ((if a then P.mt else controlCount P) : ℝ) ≠ 0 := by
    cases a
    · exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt))
    · exact_mod_cast (Nat.ne_of_gt P.mt_pos)
  simp [populationSize, Nat.cast_sum]
  field_simp
  <;> ring

/-- Des Raj potential-total estimator equals HT minus M k times the selected
arm's mean size deviation, equations (20)-(21), p. 54 and Appendix B, p. 71. -/
theorem raj_total_identity (P : ClusterPopulation) (a : Bool) (k : ℝ)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P) :
    rajTotal P a k s = htTotal P a s - (P.M : ℝ) * k *
      (armMeanSize P a s - (populationSize P : ℝ) / P.M) := by
  obtain ⟨htcard, hccard⟩ := assignment_arm_counts P s hs
  have hmt : (P.mt : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt P.mt_pos)
  have hmc : (controlCount P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt))
  cases a <;>
    simp [rajTotal, rajPotential, differenced, htTotal, armMeanSize, armSize,
      armSum, mean_size, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, nsmul_eq_mul, htcard, hccard] <;>
    field_simp <;> ring
/-- Equations (11)-(13), pp. 48-49: HT estimates each potential total and the
individual ATE without bias under complete cluster randomization (T12(a)). -/
theorem ht_unbiased (P : ClusterPopulation) :
    expectation (clusterLaw P) (htTotal P false) = ∑ j, P.y0 j ∧
    expectation (clusterLaw P) (htTotal P true) = ∑ j, P.y1 j ∧
    expectation (clusterLaw P) (horvitzThompson P) = averageTreatmentEffect P := by
  refine ⟨ht_total_unbiased P false, ht_total_unbiased P true, ?_⟩
  unfold horvitzThompson averageTreatmentEffect
  simp_rw [div_eq_mul_inv]
  rw [expectation_mul_const, expectation_sub, ht_total_unbiased, ht_total_unbiased]
  rfl

/-- Individual transformation "Y*_aij = b_0 + b_1 Y_aij", p. 49;
Appendix A, p. 70, implies cluster totals n_j b_0 + b_1 Y^T_aj. -/
abbrev affinePopulation (P : ClusterPopulation) (b0 b1 : ℝ) : ClusterPopulation :=
  {P with y0 := fun j => (P.n j : ℝ) * b0 + b1 * P.y0 j,
          y1 := fun j => (P.n j : ℝ) * b0 + b1 * P.y1 j}

/-- Summing the individual transformation gives n_j b_0 + b_1 Y^T_aj,
Appendix A, p. 70. -/
theorem affine_cluster_total (n : ℕ) (Y : Fin n → ℝ) (b0 b1 : ℝ) :
    clusterTotal (fun i => b0 + b1 * Y i) = (n : ℝ) * b0 + b1 * clusterTotal Y := by
  simp [clusterTotal, Finset.sum_add_distrib, Finset.mul_sum]

/-- Equation (15), p. 49 and Appendix A, p. 70: exact shift term of HT
for every assignment after an individual affine outcome transformation (T12(b)). -/
theorem ht_affine_identity (P : ClusterPopulation) (b0 b1 : ℝ)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P) :
    horvitzThompson (affinePopulation P b0 b1) s =
      b0 * (P.M : ℝ) / populationSize P *
        (armMeanSize P true s - armMeanSize P false s) + b1 * horvitzThompson P s := by
  simp [horvitzThompson, htTotal, armMeanSize, armSize, armSum,
    affinePopulation, populationSize, controlCount, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  ring_nf
  all_goals rfl

/-- HT is not location invariant when b_0 ≠ 0 and arm mean cluster sizes
differ, as equation (15) states, p. 49 (T12(b)). -/
theorem ht_not_location_invariant (P : ClusterPopulation) (b0 b1 : ℝ)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P) (hb0 : b0 ≠ 0)
    (hsizes : armMeanSize P true s ≠ armMeanSize P false s) :
    horvitzThompson (affinePopulation P b0 b1) s ≠ b1 * horvitzThompson P s := by
  rw [ht_affine_identity P b0 b1 s hs]
  have hM : (P.M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt))
  have hN : (populationSize P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (populationSize_pos P))
  have hp : b0 * (P.M : ℝ) / populationSize P *
      (armMeanSize P true s - armMeanSize P false s) ≠ 0 :=
    mul_ne_zero (div_ne_zero (mul_ne_zero hb0 hM) hN) (sub_ne_zero.mpr hsizes)
  exact fun he => hp (by linarith)

/-- Equations (20)-(22), p. 54: for every single coefficient k fixed before
analysis, the Des Raj total and ATE estimators are unbiased (T13(a)). -/
theorem des_raj_unbiased (P : ClusterPopulation) (k : ℝ) :
    expectation (clusterLaw P) (rajTotal P false k) = ∑ j, P.y0 j ∧
    expectation (clusterLaw P) (rajTotal P true k) = ∑ j, P.y1 j ∧
    expectation (clusterLaw P) (desRaj P k) = averageTreatmentEffect P := by
  refine ⟨raj_total_unbiased P false k, raj_total_unbiased P true k, ?_⟩
  unfold desRaj averageTreatmentEffect
  simp_rw [div_eq_mul_inv]
  rw [expectation_mul_const, expectation_sub, raj_total_unbiased, raj_total_unbiased]
  rfl

/-- "X^T_aj = ∑_i X_aij" and fixed coefficients k', k_a, Section 5.4,
p. 58. Cluster covariate totals are stored as fixed features; their mean is
X^T_a/M. -/
def rajCovariatePotential (P : ClusterPopulation) {A : ℕ}
    (X : Fin A → Fin P.M → ℝ) (ks : ℝ) (ka : Fin A → ℝ)
    (a : Bool) : Fin P.M → ℝ := fun j =>
  rajPotential P a ks j - ∑ cov, ka cov * (X cov j - clusterMean (X cov))

/-- The Section 5.4 covariate Des Raj potential-total estimators, p. 58. -/
def rajCovariateTotal (P : ClusterPopulation) {A : ℕ}
    (X : Fin A → Fin P.M → ℝ) (ks : ℝ) (ka : Fin A → ℝ)
    (a : Bool) (s : Finset (Fin P.M)) : ℝ :=
  (P.M : ℝ) / (if a then P.mt else controlCount P) *
    armSum P a (rajCovariatePotential P X ks ka a) s

/-- Δ_R2 = (estimated Y^T_1,R2 - estimated Y^T_0,R2)/N, pp. 58-59. -/
def desRajCovariates (P : ClusterPopulation) {A : ℕ}
    (X : Fin A → Fin P.M → ℝ) (ks : ℝ) (ka : Fin A → ℝ)
    (s : Finset (Fin P.M)) : ℝ :=
  (rajCovariateTotal P X ks ka true s - rajCovariateTotal P X ks ka false s) / populationSize P

/-- A centered cluster feature sums to zero, p. 54 equation (22) and
Appendix C p. 72 equation (35). -/
theorem centered_sum_zero {M : ℕ} (hM : 0 < M) (v : Fin M → ℝ) :
    (∑ j, (v j - clusterMean v)) = 0 := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have he := centered_mean_zero hM v
  have hh := congrArg (fun x : ℝ => x * M) he
  simpa [clusterMean, div_mul_cancel₀ _ hMr] using hh

/-- Cluster covariate adjustment is a fixed linear combination of centered
features; its total is zero, Section 5.4, p. 58. -/
theorem covariate_adjustment_sum_zero (P : ClusterPopulation) {A : ℕ}
    (X : Fin A → Fin P.M → ℝ) (ka : Fin A → ℝ) :
    (∑ j, ∑ cov, ka cov * (X cov j - clusterMean (X cov))) = 0 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, centered_sum_zero (lt_trans P.mt_pos P.mt_lt)]
  simp

/-- Fixed covariate differencing preserves the potential population totals,
Section 5.4, p. 58. -/
theorem raj_covariate_potential_sum (P : ClusterPopulation) {A : ℕ}
    (X : Fin A → Fin P.M → ℝ) (ks : ℝ) (ka : Fin A → ℝ) (a : Bool) :
    (∑ j, rajCovariatePotential P X ks ka a j) = ∑ j, (if a then P.y1 else P.y0) j := by
  simp [rajCovariatePotential, Finset.sum_sub_distrib, raj_potential_sum,
    covariate_adjustment_sum_zero]

/-- Fixed-covariate Des Raj total estimators are unbiased, p. 58. -/
theorem raj_covariate_total_unbiased (P : ClusterPopulation) {A : ℕ}
    (X : Fin A → Fin P.M → ℝ) (ks : ℝ) (ka : Fin A → ℝ) (a : Bool) :
    expectation (clusterLaw P) (rajCovariateTotal P X ks ka a) =
      ∑ j, (if a then P.y1 else P.y0) j := by
  unfold rajCovariateTotal
  rw [expectation_const_mul, expected_arm_sum, raj_covariate_potential_sum]
  have ht : (P.mt : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt P.mt_pos)
  have hc : (controlCount P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt))
  have hM : (P.M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt))
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> field_simp <;> ring
/-- Section 5.4, pp. 58-59: fixed, assignment-unaffected covariates and fixed
coefficients preserve unbiasedness of both totals and the ATE (T13(b)). -/
theorem des_raj_covariates_unbiased (P : ClusterPopulation) {A : ℕ}
    (X : Fin A → Fin P.M → ℝ) (ks : ℝ) (ka : Fin A → ℝ) :
    expectation (clusterLaw P) (rajCovariateTotal P X ks ka false) = ∑ j, P.y0 j ∧
    expectation (clusterLaw P) (rajCovariateTotal P X ks ka true) = ∑ j, P.y1 j ∧
    expectation (clusterLaw P) (desRajCovariates P X ks ka) = averageTreatmentEffect P := by
  refine ⟨raj_covariate_total_unbiased P X ks ka false,
    raj_covariate_total_unbiased P X ks ka true, ?_⟩
  unfold desRajCovariates averageTreatmentEffect
  simp_rw [div_eq_mul_inv]
  rw [expectation_mul_const, expectation_sub,
    raj_covariate_total_unbiased, raj_covariate_total_unbiased]
  rfl


/-- Appendix B equations (29)-(30), p. 71: a coefficient estimated in the
same randomization changes each potential-total expectation by its covariance
with that arm's mean cluster size. -/
theorem estimated_raj_total_mean (P : ClusterPopulation) (a : Bool)
    (khat : Finset (Fin P.M) → ℝ) :
    expectation (clusterLaw P) (fun s => rajTotal P a (khat s) s) =
      (∑ j, (if a then P.y1 else P.y0) j) - (P.M : ℝ) *
        designCovariance (clusterLaw P) khat (armMeanSize P a) := by
  have he : expectation (clusterLaw P) (fun s => rajTotal P a (khat s) s) =
      expectation (clusterLaw P) (fun s => htTotal P a s - (P.M : ℝ) *
        (khat s * armMeanSize P a s - khat s * ((populationSize P : ℝ) / P.M))) := by
    unfold expectation
    apply Finset.sum_congr rfl
    intro s hs
    have hs' : s ∈ assignments P := hs
    change (clusterLaw P).weight s * rajTotal P a (khat s) s = _
    rw [raj_total_identity P a (khat s) s hs']
    ring
  rw [he, expectation_sub, expectation_const_mul, expectation_sub,
    expectation_mul_const, ht_total_unbiased, designCovariance_product,
    expected_arm_mean_size]
/-- Equations (29)-(30) and corrected (31), Appendix B, p. 71 (T5).
The same experiment supplies k-hat; it is an arbitrary function of assignment,
so the second covariance in (31) is with the treatment arm mean size. -/
theorem estimated_coefficient_bias (P : ClusterPopulation)
    (khat : Finset (Fin P.M) → ℝ) :
    expectation (clusterLaw P) (fun s => rajTotal P true (khat s) s) =
      (∑ j, P.y1 j) - (P.M : ℝ) *
        designCovariance (clusterLaw P) khat (armMeanSize P true) ∧
    expectation (clusterLaw P) (fun s => rajTotal P false (khat s) s) =
      (∑ j, P.y0 j) - (P.M : ℝ) *
        designCovariance (clusterLaw P) khat (armMeanSize P false) ∧
    expectation (clusterLaw P) (fun s => desRaj P (khat s) s) =
      averageTreatmentEffect P + (P.M : ℝ) / populationSize P *
        (designCovariance (clusterLaw P) khat (armMeanSize P false) -
         designCovariance (clusterLaw P) khat (armMeanSize P true)) := by
  refine ⟨estimated_raj_total_mean P true khat, estimated_raj_total_mean P false khat, ?_⟩
  unfold desRaj averageTreatmentEffect
  simp_rw [div_eq_mul_inv]
  rw [expectation_mul_const, expectation_sub, estimated_raj_total_mean, estimated_raj_total_mean]
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring

/-- Equations (24)-(25), pp. 55-56 as corrected: with k* = b_0+b_1 k,
both potential differenced totals acquire the same constant b_0 N/M and
scale b_1. The control sum uses U^T_0j (T7 finite algebra). -/
theorem raj_potential_affine (P : ClusterPopulation) (a : Bool) (b0 b1 k : ℝ)
    (j : Fin P.M) :
    rajPotential (affinePopulation P b0 b1) a (b0 + b1 * k) j =
      b0 * ((populationSize P : ℝ) / P.M) + b1 * rajPotential P a k j := by
  cases a <;>
    simp [rajPotential, differenced, affinePopulation, mean_size] <;> ring

/-- The corrected chain of equation (25), p. 56 (T7): every admissible
assignment yields Δ*_R1 = b_1 Δ_R1, with k* = b_0+b_1 k, for all real b_0,b_1,k. -/
theorem des_raj_affine_invariant (P : ClusterPopulation) (b0 b1 k : ℝ)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P) :
    desRaj (affinePopulation P b0 b1) (b0 + b1 * k) s =
      (P.M : ℝ) / populationSize P *
        ((∑ j ∈ s, (b0 * ((populationSize P : ℝ) / P.M) + b1 * rajPotential P true k j)) / P.mt -
         (∑ j ∈ controls s, (b0 * ((populationSize P : ℝ) / P.M) + b1 * rajPotential P false k j)) /
           controlCount P) ∧
    desRaj (affinePopulation P b0 b1) (b0 + b1 * k) s = b1 * desRaj P k s := by
  have hfirst : desRaj (affinePopulation P b0 b1) (b0 + b1 * k) s =
      (P.M : ℝ) / populationSize P *
        ((∑ j ∈ s, (b0 * ((populationSize P : ℝ) / P.M) + b1 * rajPotential P true k j)) / P.mt -
         (∑ j ∈ controls s, (b0 * ((populationSize P : ℝ) / P.M) + b1 * rajPotential P false k j)) /
           controlCount P) := by
    unfold desRaj rajTotal armSum
    simp_rw [raj_potential_affine]
    simp [affinePopulation, controlCount, populationSize]
    ring_nf
    all_goals rfl
  refine ⟨hfirst, ?_⟩
  rw [hfirst]
  obtain ⟨htcard, hccard⟩ := assignment_arm_counts P s hs
  have ht : (P.mt : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt P.mt_pos)
  have hc : (controlCount P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt))
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, htcard, hccard]
  unfold desRaj rajTotal armSum
  simp only [Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte]
  field_simp
  <;> ring

/-- The exact HT variance in equation (17), p. 51, expressed in the paper's
finite-population moments with divisor M. This is a formula, not a definition
of true design variance. -/
def htVarianceFormula (P : ClusterPopulation) : ℝ :=
  (P.M : ℝ)^2 / (populationSize P : ℝ)^2 *
    ((P.M : ℝ) / ((P.M : ℝ) - 1) *
      (clusterVariance P.y0 / controlCount P + clusterVariance P.y1 / P.mt) +
     1 / ((P.M : ℝ) - 1) *
      (2 * clusterCovariance P.y0 P.y1 - clusterVariance P.y0 - clusterVariance P.y1))

/-- V_apx, the conservative upper bound obtained by omitting the nonpositive
covariance remainder, p. 51. -/
def approximateVariance (P : ClusterPopulation) (v0 v1 : Fin P.M → ℝ) : ℝ :=
  (P.M : ℝ)^3 / ((populationSize P : ℝ)^2 * ((P.M : ℝ) - 1)) *
    (clusterVariance v0 / controlCount P + clusterVariance v1 / P.mt)

/-- Combined arm sample variance estimator, p. 51, and Des Raj equation (23),
p. 55. Each sample mean divides by the fixed number of clusters in that arm. -/
def combinedVarianceEstimator (P : ClusterPopulation) (v0 v1 : Fin P.M → ℝ)
    (s : Finset (Fin P.M)) : ℝ :=
  (P.M : ℝ)^2 / (populationSize P : ℝ)^2 *
    ((∑ j ∈ controls s, (v0 j - armSum P false v0 s / controlCount P)^2) /
      ((controlCount P : ℝ) * ((controlCount P : ℝ) - 1)) +
     (∑ j ∈ s, (v1 j - armSum P true v1 s / P.mt)^2) /
      ((P.mt : ℝ) * ((P.mt : ℝ) - 1)))

/-- The observed sharp-null variance estimator, p. 52:
M^4 σ²(Y^T_j)/(N²(M-1)m_c m_t). Its moment is over the observed totals. -/
def sharpNullVarianceEstimator (P : ClusterPopulation) (s : Finset (Fin P.M)) : ℝ :=
  (P.M : ℝ)^4 * clusterVariance (observedTotal P s) /
    ((populationSize P : ℝ)^2 * ((P.M : ℝ) - 1) * controlCount P * P.mt)


/-- Finite population covariance is symmetric, divisor M, p. 50. -/
theorem clusterCovariance_comm {M : ℕ} (v w : Fin M → ℝ) :
    clusterCovariance v w = clusterCovariance w v := by
  unfold clusterCovariance
  simp_rw [mul_comm]

/-- Covariance of a feature with itself is its finite population variance,
p. 50, the sharp-null covariance fact corrected on p. 52 (T10). -/
theorem clusterCovariance_self {M : ℕ} (v : Fin M → ℝ) :
    clusterCovariance v v = clusterVariance v := by
  simp [clusterCovariance, clusterVariance, pow_two]

/-- Every finite population variance is nonnegative, the finite bound used
in equations (17) and (26), pp. 51 and 57. -/
theorem clusterVariance_nonneg {M : ℕ} (v : Fin M → ℝ) : 0 ≤ clusterVariance v := by
  unfold clusterVariance clusterMean
  apply div_nonneg _ (Nat.cast_nonneg M)
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Variance of a difference is σ²(v)+σ²(w)-2σ(v,w), divisor M, p. 51. -/
theorem clusterVariance_sub {M : ℕ} (v w : Fin M → ℝ) :
    clusterVariance (fun j => v j - w j) = clusterVariance v + clusterVariance w -
      2 * clusterCovariance v w := by
  unfold clusterVariance
  rw [clusterMean_sub]
  have he : (fun j => (v j - w j - (clusterMean v - clusterMean w))^2) =
      (fun j => (v j - clusterMean v)^2 + (w j - clusterMean w)^2 -
        ((v j - clusterMean v) * (w j - clusterMean w)) * 2) := by funext j; ring
  rw [he, clusterMean_sub, clusterMean_add, clusterMean_mul]
  unfold clusterCovariance
  ring

/-- The covariance remainder in equation (17) is nonpositive:
2σ(Y^T_0,Y^T_1)-σ²(Y^T_0)-σ²(Y^T_1)≤0, p. 51 (T15(c) finite lemma). -/
theorem covariance_remainder_nonpos {M : ℕ} (v w : Fin M → ℝ) :
    2 * clusterCovariance v w - clusterVariance v - clusterVariance w ≤ 0 := by
  have hp := clusterVariance_nonneg (fun j => v j - w j)
  rw [clusterVariance_sub] at hp
  linarith

/-- The moment expression on the right of equation (17) is at most V_apx,
p. 51 (T15(c) algebraic finite lemma). The design-variance equality is
separately stated in ht_variance_identity_bound. -/
theorem variance_formula_le_approximate (P : ClusterPopulation) :
    htVarianceFormula P ≤ approximateVariance P P.y0 P.y1 := by
  have hM : (0 : ℝ) < (P.M : ℝ) - 1 := by
    have hm : 1 < P.M := lt_of_le_of_lt (Nat.succ_le_of_lt P.mt_pos) P.mt_lt
    have hmr : (1 : ℝ) < P.M := by exact_mod_cast hm
    linarith
  have hN : (0 : ℝ) < populationSize P := by exact_mod_cast populationSize_pos P
  have hr := covariance_remainder_nonpos P.y0 P.y1
  have hcoef : 0 ≤ (P.M : ℝ)^2 / (populationSize P : ℝ)^2 / ((P.M : ℝ) - 1) := by positivity
  have hb := mul_nonpos_of_nonneg_of_nonpos hcoef hr
  have he : htVarianceFormula P = approximateVariance P P.y0 P.y1 +
      ((P.M : ℝ)^2 / (populationSize P : ℝ)^2 / ((P.M : ℝ) - 1)) *
        (2 * clusterCovariance P.y0 P.y1 - clusterVariance P.y0 - clusterVariance P.y1) := by
    unfold htVarianceFormula approximateVariance
    field_simp
    <;> ring
  rw [he]
  linarith

/-- Randomization covariance is symmetric, equation (16), p. 50. -/
theorem designCovariance_comm {Ω : Type*} (L : FiniteLaw Ω) (T U : Ω → ℝ) :
    designCovariance L T U = designCovariance L U T := by
  unfold designCovariance
  simp_rw [mul_comm]

/-- Variance of a difference is the sum of variances minus twice covariance,
equation (16), p. 50, as a weighted finite-sum identity. -/
theorem designVariance_sub {Ω : Type*} (L : FiniteLaw Ω) (T U : Ω → ℝ) :
    designVariance L (fun ω => T ω - U ω) = designVariance L T + designVariance L U -
      2 * designCovariance L T U := by
  unfold designVariance
  rw [expectation_sub]
  have he : (fun ω => (T ω - U ω - (expectation L T - expectation L U))^2) =
      (fun ω => (T ω - expectation L T)^2 + (U ω - expectation L U)^2 -
        ((T ω - expectation L T) * (U ω - expectation L U)) * 2) := by funext ω; ring
  rw [he, expectation_sub, expectation_add, expectation_mul_const]
  unfold designCovariance
  ring

/-- Variance scales quadratically with a fixed scalar, equation (16), p. 50. -/
theorem designVariance_mul {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (c : ℝ) :
    designVariance L (fun ω => T ω * c) = designVariance L T * c^2 := by
  unfold designVariance
  rw [expectation_mul_const]
  have he : (fun ω => (T ω * c - expectation L T * c)^2) =
      (fun ω => (T ω - expectation L T)^2 * c^2) := by funext ω; ring
  rw [he, expectation_mul_const]

/-- Equation (16), p. 50, proved independently of the finite-sampling variance
formulas: V(Δ_HT) = [V(Yhat_0)+V(Yhat_1)-2Cov(Yhat_0,Yhat_1)]/N² (T15(a)). -/
theorem ate_variance_linear_identity (P : ClusterPopulation) :
    designVariance (clusterLaw P) (horvitzThompson P) =
      (designVariance (clusterLaw P) (htTotal P false) +
       designVariance (clusterLaw P) (htTotal P true) -
       2 * designCovariance (clusterLaw P) (htTotal P false) (htTotal P true)) /
        (populationSize P : ℝ)^2 := by
  unfold horvitzThompson
  simp_rw [div_eq_mul_inv]
  rw [designVariance_mul, designVariance_sub, designCovariance_comm]
  simp only [inv_pow]
  ring

/-- Covariance with itself is design variance, Section 4.2, p. 50. -/
theorem designCovariance_self {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) :
    designCovariance L T T = designVariance L T := by
  simp [designCovariance, designVariance, pow_two]

/-- Expectation commutes with a finite sum of cluster features; sampling
moment calculations for equation (17), p. 51. -/
theorem expectation_fintype_sum {Ω ι : Type*} [Fintype ι]
    (L : FiniteLaw Ω) (T : ι → Ω → ℝ) :
    expectation L (fun s => ∑ i, T i s) = ∑ i, expectation L (T i) := by
  classical
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- The exact single-cluster inclusion probability m_t/M, random allocation
on p. 44, used for the finite-sampling moments on p. 50. -/
theorem treatment_indicator_mean (P : ClusterPopulation) (i : Fin P.M) :
    expectation (clusterLaw P) (fun s => if i ∈ s then (1 : ℝ) else 0) =
      (P.mt : ℝ) / P.M := by
  have he : armSum P true (fun j => if j = i then (1 : ℝ) else 0) =
      fun s => if i ∈ s then (1 : ℝ) else 0 := by
    funext s
    simp [armSum]
  rw [← he]
  simpa using expected_treatment_sum P (fun j => if j = i then (1 : ℝ) else 0)

/-- Under complete cluster randomization, two distinct clusters are jointly
treated with probability m_t(m_t-1)/(M(M-1)); finite lemma for p. 50. -/
theorem treatment_pair_mean (P : ClusterPopulation) (i j : Fin P.M) (hij : i ≠ j) :
    expectation (clusterLaw P) (fun s => if i ∈ s ∧ j ∈ s then (1 : ℝ) else 0) =
      (P.mt : ℝ) * ((P.mt : ℝ) - 1) / ((P.M : ℝ) * ((P.M : ℝ) - 1)) := by
  classical
  have hM : (P.M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt))
  have hM1 : (P.M : ℝ) - 1 ≠ 0 := by
    have hh : (1 : ℝ) < P.M := by
      exact_mod_cast lt_of_le_of_lt (Nat.succ_le_of_lt P.mt_pos) P.mt_lt
    linarith
  by_cases hm : 2 ≤ P.mt
  · have hcount : ((assignments P).filter (fun s => i ∈ s ∧ j ∈ s)).card =
        (P.M - 2).choose (P.mt - 2) := by
      have h := Finset.card_filter_powersetCard_subset ({i,j} : Finset (Fin P.M))
        Finset.univ P.mt (Finset.subset_univ _) (by simpa [hij] using hm)
      simpa [assignments, hij, Finset.insert_subset_iff] using h
    have hcomb : (P.M.choose P.mt : ℝ) * (P.mt.choose 2 : ℝ) =
        (P.M.choose 2 : ℝ) * ((P.M - 2).choose (P.mt - 2) : ℝ) := by
      exact_mod_cast (Nat.choose_mul (n := P.M) (k := P.mt) (s := 2) hm)
    rw [Nat.cast_choose_two, Nat.cast_choose_two] at hcomb
    have hC : (P.M.choose P.mt : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (le_of_lt P.mt_lt))
    rw [clusterLaw, uniform_expectation]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcount]
    simp only [assignments, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    field_simp
    nlinarith only [hcomb]
  · have hmt : P.mt = 1 := by have := P.mt_pos; omega
    have hempty : ((assignments P).filter (fun s => i ∈ s ∧ j ∈ s)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro s hs
      obtain ⟨hs, hi, hj⟩ := Finset.mem_filter.mp hs
      have hc : s.card = 1 := by simpa [hmt] using (Finset.mem_powersetCard.mp hs).2
      have hsub : ({i,j} : Finset (Fin P.M)) ⊆ s := by
        exact Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj)
      have hh := Finset.card_le_card hsub
      simp [hij, hc] at hh
    rw [clusterLaw, uniform_expectation, ← Finset.sum_filter, hempty]
    simp [hmt]

/-- E[(sum of treated v)(sum of treated w)] splits into diagonal and
off-diagonal pairs; exact finite lemma underlying the variance on p. 50. -/
theorem treatment_sum_product (P : ClusterPopulation) (v w : Fin P.M → ℝ) :
    expectation (clusterLaw P) (fun s => armSum P true v s * armSum P true w s) =
      (P.mt : ℝ) / P.M * ∑ i, v i * w i +
      ((P.mt : ℝ) * ((P.mt : ℝ) - 1) / ((P.M : ℝ) * ((P.M : ℝ) - 1))) *
        ((∑ i, v i) * (∑ j, w j) - ∑ i, v i * w i) := by
  classical
  have he (s : Finset (Fin P.M)) : armSum P true v s * armSum P true w s =
      ∑ i, ∑ j, (if i ∈ s ∧ j ∈ s then (1 : ℝ) else 0) * (v i * w j) := by
    simp [armSum, Finset.sum_mul_sum, ite_and, Finset.sum_ite_irrel, Finset.sum_ite_mem_eq]
  simp_rw [he]
  rw [expectation_fintype_sum]
  simp_rw [expectation_fintype_sum, expectation_mul_const]
  have hpair (i j : Fin P.M) :
      expectation (clusterLaw P) (fun s => if i ∈ s ∧ j ∈ s then (1 : ℝ) else 0) =
      if i = j then (P.mt : ℝ) / P.M else
        (P.mt : ℝ) * ((P.mt : ℝ) - 1) / ((P.M : ℝ) * ((P.M : ℝ) - 1)) := by
    by_cases hh : i = j
    · subst j; simp [treatment_indicator_mean]
    · simp [hh, treatment_pair_mean P i j hh]
  simp_rw [hpair]
  have hp (i j : Fin P.M) :
      (if i = j then (P.mt : ℝ) / P.M else
        (P.mt : ℝ) * ((P.mt : ℝ) - 1) / ((P.M : ℝ) * ((P.M : ℝ) - 1))) *
          (v i * w j) =
      ((P.mt : ℝ) / P.M - (P.mt : ℝ) * ((P.mt : ℝ) - 1) /
        ((P.M : ℝ) * ((P.M : ℝ) - 1))) * (if i = j then v i * w j else 0) +
      ((P.mt : ℝ) * ((P.mt : ℝ) - 1) / ((P.M : ℝ) * ((P.M : ℝ) - 1))) * (v i * w j) := by
    split_ifs <;> ring
  simp_rw [hp]
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Covariance of two treated cluster sums is the finite-population covariance
times m_t(M-m_t)/(M-1), the second-moment identity needed on p. 50. -/
theorem treatment_sum_covariance (P : ClusterPopulation) (v w : Fin P.M → ℝ) :
    designCovariance (clusterLaw P) (armSum P true v) (armSum P true w) =
      (P.mt : ℝ) * ((P.M : ℝ) - P.mt) / ((P.M : ℝ) - 1) * clusterCovariance v w := by
  have hM : (P.M : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt)
  have hM1 : (P.M : ℝ) - 1 ≠ 0 := by
    have hh : (1 : ℝ) < P.M := by
      exact_mod_cast lt_of_le_of_lt (Nat.succ_le_of_lt P.mt_pos) P.mt_lt
    linarith
  rw [designCovariance_product, treatment_sum_product,
    expected_treatment_sum, expected_treatment_sum,
    clusterCovariance_product (lt_trans P.mt_pos P.mt_lt)]
  unfold clusterMean
  field_simp
  <;> ring
/-- Fixed coefficients scale covariance bilinearly, finite algebra for
HT totals in equations (11)-(12), p. 48. -/
theorem designCovariance_scale {Ω : Type*} (L : FiniteLaw Ω)
    (T U : Ω → ℝ) (c d : ℝ) :
    designCovariance L (fun s => c * T s) (fun s => d * U s) =
      c * d * designCovariance L T U := by
  unfold designCovariance
  rw [expectation_const_mul, expectation_const_mul]
  have he : (fun s => (c * T s - c * expectation L T) *
      (d * U s - d * expectation L U)) =
      (fun s => c * (d * ((T s - expectation L T) * (U s - expectation L U)))) := by
    funext s; ring
  rw [he, expectation_const_mul, expectation_const_mul]
  ring

/-- Taking a fixed total minus a sampled total reverses its covariance,
the control-treatment covariance sign on p. 50. -/
theorem designCovariance_const_sub_left {Ω : Type*} (L : FiniteLaw Ω)
    (T U : Ω → ℝ) (c : ℝ) :
    designCovariance L (fun s => c - T s) U = -designCovariance L T U := by
  unfold designCovariance
  rw [expectation_sub, expectation_const]
  have he : (fun s => (c - T s - (c - expectation L T)) *
      (U s - expectation L U)) =
      (fun s => ((T s - expectation L T) * (U s - expectation L U)) * (-1)) := by
    funext s; ring
  rw [he, expectation_mul_const]
  ring

/-- Complementary sampled totals have the same covariance as their treated
sums when both are complemented, p. 50. -/
theorem designCovariance_const_sub_both {Ω : Type*} (L : FiniteLaw Ω)
    (T U : Ω → ℝ) (c d : ℝ) :
    designCovariance L (fun s => c - T s) (fun s => d - U s) =
      designCovariance L T U := by
  rw [designCovariance_const_sub_left, designCovariance_comm,
    designCovariance_const_sub_left, designCovariance_comm]
  ring

/-- The control feature sum is the fixed population total minus the treated
feature sum, the complementary sampling design on p. 44. -/
theorem control_sum_complement (P : ClusterPopulation) (v : Fin P.M → ℝ) :
    armSum P false v = fun s => (∑ j, v j) - armSum P true v s := by
  funext s
  simpa [armSum, controls] using Finset.sum_sdiff (Finset.subset_univ s) (f := v)

/-- Joint moments of either pair of arm sums, including the negative
cross-arm covariance of p. 50. Both arms have the fixed complete-randomization law. -/
theorem arm_sum_covariance (P : ClusterPopulation) (a b : Bool) (v w : Fin P.M → ℝ) :
    designCovariance (clusterLaw P) (armSum P a v) (armSum P b w) =
      (if a = b then (1 : ℝ) else -1) *
        ((P.mt : ℝ) * controlCount P / ((P.M : ℝ) - 1)) * clusterCovariance v w := by
  have hc : (controlCount P : ℝ) = (P.M : ℝ) - P.mt := by
    simp [controlCount, Nat.cast_sub (le_of_lt P.mt_lt)]
  cases a <;> cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  · rw [control_sum_complement, control_sum_complement,
      designCovariance_const_sub_both, treatment_sum_covariance, hc]; ring
  · rw [control_sum_complement, designCovariance_const_sub_left,
      treatment_sum_covariance, hc]; ring
  · rw [designCovariance_comm, control_sum_complement,
      designCovariance_const_sub_left, treatment_sum_covariance,
      clusterCovariance_comm, hc]; ring
  · rw [treatment_sum_covariance, hc]; ring

/-- The exact arm HT variance from finite population sampling, p. 50:
M²/m_a times (M-m_a)/(M-1) times σ²(Y^T_a). -/
theorem ht_total_design_variance (P : ClusterPopulation) (a : Bool) :
    designVariance (clusterLaw P) (htTotal P a) =
      (P.M : ℝ)^2 / (if a then P.mt else controlCount P) *
        (((P.M : ℝ) - (if a then P.mt else controlCount P)) / ((P.M : ℝ) - 1)) *
          clusterVariance (if a then P.y1 else P.y0) := by
  have ht : (P.mt : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt P.mt_pos
  have hc : (controlCount P : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt)
  have hM1 : (P.M : ℝ) - 1 ≠ 0 := by
    have hh : (1 : ℝ) < P.M := by
      exact_mod_cast lt_of_le_of_lt (Nat.succ_le_of_lt P.mt_pos) P.mt_lt
    linarith
  rw [← designCovariance_self]
  unfold htTotal
  rw [designCovariance_scale, arm_sum_covariance, clusterCovariance_self]
  have hc' : (controlCount P : ℝ) = (P.M : ℝ) - P.mt := by
    simp [controlCount, Nat.cast_sub (le_of_lt P.mt_lt)]
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  all_goals
    rw [hc']
    have hmc : (P.M : ℝ) - P.mt ≠ 0 := by rw [← hc']; exact hc
    field_simp
    <;> ring

/-- The exact cross-arm HT covariance, with negative sign, p. 50. -/
theorem ht_total_design_covariance (P : ClusterPopulation) :
    designCovariance (clusterLaw P) (htTotal P false) (htTotal P true) =
      -((P.M : ℝ)^2 / ((P.M : ℝ) - 1)) * clusterCovariance P.y0 P.y1 := by
  have ht : (P.mt : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt P.mt_pos
  have hc : (controlCount P : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt)
  have hM1 : (P.M : ℝ) - 1 ≠ 0 := by
    have hh : (1 : ℝ) < P.M := by
      exact_mod_cast lt_of_le_of_lt (Nat.succ_le_of_lt P.mt_pos) P.mt_lt
    linarith
  unfold htTotal
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [designCovariance_scale, arm_sum_covariance]
  simp only [Bool.false_eq_true, ↓reduceIte]
  field_simp
  <;> ring

/-- The actual design variance equals the finite-population moment expression
of equation (17), p. 51. The equality is derived from the uniform sampling law. -/
theorem ht_design_variance_formula (P : ClusterPopulation) :
    designVariance (clusterLaw P) (horvitzThompson P) = htVarianceFormula P := by
  rw [ate_variance_linear_identity, ht_total_design_variance,
    ht_total_design_variance, ht_total_design_covariance]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold htVarianceFormula
  have ht : (P.mt : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt P.mt_pos
  have hc : (controlCount P : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt)
  field_simp [ht, hc]
  <;> ring
/-- Estimators equal on every randomization have equal expectations, p. 42. -/
theorem expectation_congr_support {Ω : Type*} (L : FiniteLaw Ω) (T U : Ω → ℝ)
    (h : ∀ s ∈ L.support, T s = U s) : expectation L T = expectation L U := by
  unfold expectation
  exact Finset.sum_congr rfl (fun s hs => congrArg (L.weight s * ·) (h s hs))

/-- The exact squared-sum moment for either arm, p. 50. -/
theorem arm_sum_second_moment (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ) :
    expectation (clusterLaw P) (fun s => (armSum P a v s)^2) =
      (P.mt : ℝ) * controlCount P / ((P.M : ℝ) - 1) * clusterVariance v +
        (((if a then P.mt else controlCount P) : ℝ) / P.M * ∑ j, v j)^2 := by
  have hh := arm_sum_covariance P a a v v
  rw [clusterCovariance_self, designCovariance_product,
    expected_arm_sum] at hh
  simpa [pow_two] using (show expectation (clusterLaw P) (fun s => armSum P a v s * armSum P a v s) =
      (P.mt : ℝ) * controlCount P / ((P.M : ℝ) - 1) * clusterVariance v +
        (((if a then P.mt else controlCount P) : ℝ) / P.M * ∑ j, v j) *
          (((if a then P.mt else controlCount P) : ℝ) / P.M * ∑ j, v j) by
    simp only [↓reduceIte, one_mul] at hh
    linarith)

/-- For a selected sample of m_a clusters, its sum of squared deviations
from its sample mean equals the sum of squares minus the squared sum/m_a.
Finite identity used by the combined variance estimator on p. 51. -/
theorem arm_sample_ssd_identity (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P) :
    (∑ j ∈ (if a then s else controls s),
      (v j - armSum P a v s / (if a then P.mt else controlCount P))^2) =
    armSum P a (fun j => (v j)^2) s -
      (armSum P a v s)^2 / (if a then P.mt else controlCount P) := by
  classical
  obtain ⟨hst,hsc⟩ := assignment_arm_counts P s hs
  have ht : (P.mt : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt P.mt_pos
  have hc : (controlCount P : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt)
  have he (x m : ℝ) : (x - m)^2 = x^2 - x * (2*m) + m^2 := by ring
  simp_rw [he]
  unfold armSum
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, hst,hsc]
  all_goals
    field_simp
    <;> ring

/-- Expected sample squared deviations equal (m_a-1)M/(M-1) times the
finite-population variance with divisor M, the sampling lemma on p. 51. -/
theorem arm_sample_ssd_expectation (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ) :
    expectation (clusterLaw P) (fun s =>
      ∑ j ∈ (if a then s else controls s),
        (v j - armSum P a v s / (if a then P.mt else controlCount P))^2) =
      (((if a then P.mt else controlCount P) : ℝ) - 1) *
        (P.M : ℝ) / ((P.M : ℝ) - 1) * clusterVariance v := by
  rw [expectation_congr_support (clusterLaw P) _
    (fun s => armSum P a (fun j => (v j)^2) s -
      (armSum P a v s)^2 / (if a then P.mt else controlCount P))
    (fun s hs => arm_sample_ssd_identity P a v s hs)]
  simp_rw [div_eq_mul_inv]
  rw [expectation_sub, expectation_mul_const, expected_arm_sum, arm_sum_second_moment]
  have hM : 0 < P.M := lt_trans P.mt_pos P.mt_lt
  have ht : (P.mt : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt P.mt_pos
  have hc : (controlCount P : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt)
  have hMr : (P.M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have hM1 : (P.M : ℝ) - 1 ≠ 0 := by
    have hh : (1 : ℝ) < P.M := by
      exact_mod_cast lt_of_le_of_lt (Nat.succ_le_of_lt P.mt_pos) P.mt_lt
    linarith
  rw [← clusterCovariance_self, clusterCovariance_product hM]
  unfold clusterMean
  have hc' : (controlCount P : ℝ) = (P.M : ℝ) - P.mt := by
    simp [controlCount, Nat.cast_sub (le_of_lt P.mt_lt)]
  have hmc : (P.M : ℝ) - P.mt ≠ 0 := by rw [← hc']; exact hc
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    rw [hc']
    field_simp
    <;> ring

/-- Substitution of the unbiased sample variances gives an unbiased estimate
of V_apx for any fixed potential-total vectors, p. 51 and equation (23), p. 55. -/
theorem combined_estimator_expectation (P : ClusterPopulation) (v0 v1 : Fin P.M → ℝ)
    (ht2 : 2 ≤ P.mt) (hc2 : 2 ≤ controlCount P) :
    expectation (clusterLaw P) (combinedVarianceEstimator P v0 v1) =
      approximateVariance P v0 v1 := by
  unfold combinedVarianceEstimator
  simp_rw [div_eq_mul_inv]
  rw [expectation_const_mul, expectation_add, expectation_mul_const, expectation_mul_const]
  have h0 := arm_sample_ssd_expectation P false v0
  have h1 := arm_sample_ssd_expectation P true v1
  simp only [div_eq_mul_inv, Bool.false_eq_true, ↓reduceIte] at h0 h1
  rw [h0,h1]
  have ht : (P.mt : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt P.mt_pos
  have hc : (controlCount P : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt)
  have ht1 : (P.mt : ℝ) - 1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ P.mt := by exact_mod_cast ht2
    linarith
  have hc1 : (controlCount P : ℝ) - 1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ controlCount P := by exact_mod_cast hc2
    linarith
  unfold approximateVariance
  field_simp
  <;> ring
/-- Individual sharp null implies equality of potential cluster totals,
corrected symbols on pp. 51-52 (T10). -/
theorem individual_sharp_null_total {n : ℕ} (Y0 Y1 : Fin n → ℝ)
    (hnull : ∀ i, Y0 i = Y1 i) : clusterTotal Y0 = clusterTotal Y1 := by
  unfold clusterTotal
  exact Finset.sum_congr rfl (fun i _ => hnull i)

/-- "let Y_1ij be ... if ... treatment and ... Y_0ij ... control", p. 44;
"Y^T_aj = ∑_{i=1}^{n_j}Y_aij", p. 48. Individual potential outcomes
are recorded together with their actual cluster totals. -/
structure IndividualPotentialOutcomes (P : ClusterPopulation) where
  Y0 : (j : Fin P.M) → Fin (P.n j) → ℝ
  Y1 : (j : Fin P.M) → Fin (P.n j) → ℝ
  total0 : ∀ j, clusterTotal (Y0 j) = P.y0 j
  total1 : ∀ j, clusterTotal (Y1 j) = P.y1 j

/-- "H_0: τ_i=0, ∀ i ... both potential outcomes are identical", pp. 51-52.
The equality is imposed on each individual, including within each cluster. -/
def IndividualSharpNull {P : ClusterPopulation} (I : IndividualPotentialOutcomes P) : Prop :=
  ∀ j i, I.Y0 j i = I.Y1 j i

/-- "Y_i=D_iY_1i+(1-D_i)Y_0i", p. 41, for cluster assignment, p. 44.
All individuals in a cluster have its common treatment indicator. -/
def observedIndividual {P : ClusterPopulation} (I : IndividualPotentialOutcomes P)
    (s : Finset (Fin P.M)) (j : Fin P.M) (i : Fin (P.n j)) : ℝ :=
  if j ∈ s then I.Y1 j i else I.Y0 j i

/-- Corrected individual equality Y_0i=Y_1i=Y_i, pp. 51-52 (T10).
The individual sharp null implies the cluster-total equalities used below. -/
theorem individual_sharp_null_facts (P : ClusterPopulation)
    (I : IndividualPotentialOutcomes P) (hnull : IndividualSharpNull I)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P) :
    (∀ j i, I.Y0 j i = observedIndividual I s j i ∧
      I.Y1 j i = observedIndividual I s j i) ∧ (∀ j, P.y0 j = P.y1 j) := by
  constructor
  · intro j i
    by_cases hj : j ∈ s <;> simp [observedIndividual, hj, hnull j i]
  · intro j
    rw [← I.total0 j, ← I.total1 j]
    exact individual_sharp_null_total _ _ (hnull j)

/-- Restored total superscripts in the sharp-null moment facts, p. 52:
observed totals agree with both potentials under the null; all variances and
covariance coincide for every assignment (T10 proved finite lemma). -/
theorem sharp_null_moment_facts (P : ClusterPopulation)
    (I : IndividualPotentialOutcomes P) (hnull : IndividualSharpNull I)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P) :
    (∀ j, P.y0 j = observedTotal P s j ∧ P.y1 j = observedTotal P s j) ∧
    clusterVariance P.y0 = clusterVariance P.y1 ∧
    clusterVariance P.y1 = clusterVariance (observedTotal P s) ∧
    clusterCovariance P.y0 P.y1 = clusterVariance (observedTotal P s) := by
  have htotal := (individual_sharp_null_facts P I hnull s hs).2
  have hY : P.y0 = P.y1 := funext htotal
  have hobs : observedTotal P s = P.y1 := by
    funext j
    simp [observedTotal, htotal]
  rw [hobs, hY, clusterCovariance_self]
  exact ⟨fun j => ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

/-- Substitution of the sharp-null moment facts into equation (17) gives
exactly the displayed M^4σ²/(N²(M-1)m_c m_t) formula, p. 52 (T10 algebra).
This is an algebraic identity, separate from the sampling identity. -/
theorem sharp_null_formula_algebra (P : ClusterPopulation)
    (I : IndividualPotentialOutcomes P) (hnull : IndividualSharpNull I)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P) :
    htVarianceFormula P = sharpNullVarianceEstimator P s := by
  have htotal := (individual_sharp_null_facts P I hnull s hs).2
  have hY : P.y0 = P.y1 := funext htotal
  have hobs : observedTotal P s = P.y1 := by funext j; simp [observedTotal, htotal]
  have hcounts : (controlCount P : ℝ) + P.mt = P.M := by
    simp [controlCount, Nat.cast_sub (le_of_lt P.mt_lt)]
  have ht : (P.mt : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt P.mt_pos)
  have hc : (controlCount P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt))
  have hN : (populationSize P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (populationSize_pos P))
  have hM : (P.M : ℝ) - 1 ≠ 0 := by
    have hpos : (1 : ℝ) < P.M := by exact_mod_cast (lt_of_le_of_lt (Nat.succ_le_of_lt P.mt_pos) P.mt_lt)
    linarith
  unfold htVarianceFormula sharpNullVarianceEstimator
  rw [hY, hobs, clusterCovariance_self]
  field_simp
  nlinarith only [congrArg (fun x : ℝ => x * ((P.M : ℝ)^3 * clusterVariance P.y1)) hcounts]
/-- Corrected sharp-null facts and exact variance, pp. 51-52 (T10).
The hypothesis is no treatment effect for every individual. The supplied
individual outcomes sum to the stored potential cluster totals; equality of
totals alone is not substituted for the paper’s individual sharp null. -/
theorem sharp_null_exact_variance (P : ClusterPopulation)
    (I : IndividualPotentialOutcomes P) (hnull : IndividualSharpNull I)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P) :
    (∀ j, P.y0 j = observedTotal P s j ∧ P.y1 j = observedTotal P s j) ∧
    clusterVariance P.y0 = clusterVariance P.y1 ∧
    clusterVariance P.y1 = clusterVariance (observedTotal P s) ∧
    clusterCovariance P.y0 P.y1 = clusterVariance (observedTotal P s) ∧
    designVariance (clusterLaw P) (horvitzThompson P) = htVarianceFormula P ∧
    htVarianceFormula P = sharpNullVarianceEstimator P s := by
  have h := sharp_null_moment_facts P I hnull s hs
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ht_design_variance_formula P,
    sharp_null_formula_algebra P I hnull s hs⟩

/-- Equation (16) and the finite-sampling arm variance/covariance formulas,
p. 50 (T15(a)). Covariance has the negative sign printed there. -/
theorem ht_variance_components (P : ClusterPopulation) :
    designVariance (clusterLaw P) (horvitzThompson P) =
      (designVariance (clusterLaw P) (htTotal P false) +
       designVariance (clusterLaw P) (htTotal P true) -
       2 * designCovariance (clusterLaw P) (htTotal P false) (htTotal P true)) /
        (populationSize P : ℝ)^2 ∧
    designVariance (clusterLaw P) (htTotal P false) =
      (P.M : ℝ)^2 / controlCount P *
        (((P.M : ℝ) - controlCount P) / ((P.M : ℝ) - 1)) * clusterVariance P.y0 ∧
    designVariance (clusterLaw P) (htTotal P true) =
      (P.M : ℝ)^2 / P.mt *
        (((P.M : ℝ) - P.mt) / ((P.M : ℝ) - 1)) * clusterVariance P.y1 ∧
    designCovariance (clusterLaw P) (htTotal P false) (htTotal P true) =
      -((P.M : ℝ)^2 / ((P.M : ℝ) - 1)) * clusterCovariance P.y0 P.y1 := by
  exact ⟨ate_variance_linear_identity P, ht_total_design_variance P false,
    ht_total_design_variance P true, ht_total_design_covariance P⟩

/-- Equation (17) and conservative upper bound, p. 51 (T15(b)-(c)).
The exact design variance is stated independently of the formula. -/
theorem ht_variance_identity_bound (P : ClusterPopulation) :
    designVariance (clusterLaw P) (horvitzThompson P) = htVarianceFormula P ∧
    designVariance (clusterLaw P) (horvitzThompson P) ≤ approximateVariance P P.y0 P.y1 := by
  exact ⟨ht_design_variance_formula P,
    (ht_design_variance_formula P).trans_le (variance_formula_le_approximate P)⟩

/-- The combined estimator of p. 51 is unbiased for V_apx and conservative
in expectation when both arms contain at least two clusters (T15(d)). -/
theorem combined_variance_conservative (P : ClusterPopulation)
    (ht : 2 ≤ P.mt) (hc : 2 ≤ controlCount P) :
    expectation (clusterLaw P) (combinedVarianceEstimator P P.y0 P.y1) =
      approximateVariance P P.y0 P.y1 ∧
    designVariance (clusterLaw P) (horvitzThompson P) ≤
      expectation (clusterLaw P) (combinedVarianceEstimator P P.y0 P.y1) := by
  rw [combined_estimator_expectation P P.y0 P.y1 ht hc]
  exact ⟨rfl, (ht_variance_identity_bound P).2⟩

/-- Des Raj equation (23), p. 55: substitute the two fixed-k potential U^T
vectors in the combined variance estimator to obtain a conservative estimator
in expectation, with at least two clusters in each arm (T15(e)). -/
theorem raj_variance_conservative (P : ClusterPopulation) (k : ℝ)
    (ht : 2 ≤ P.mt) (hc : 2 ≤ controlCount P) :
    expectation (clusterLaw P)
      (combinedVarianceEstimator P (rajPotential P false k) (rajPotential P true k)) =
      approximateVariance P (rajPotential P false k) (rajPotential P true k) ∧
    designVariance (clusterLaw P) (desRaj P k) ≤
      expectation (clusterLaw P)
        (combinedVarianceEstimator P (rajPotential P false k) (rajPotential P true k)) := by
  refine ⟨combined_estimator_expectation P (rajPotential P false k)
    (rajPotential P true k) ht hc, ?_⟩
  rw [combined_estimator_expectation P (rajPotential P false k) (rajPotential P true k) ht hc]
  let Q : ClusterPopulation := {P with y0 := rajPotential P false k, y1 := rajPotential P true k}
  change designVariance (clusterLaw Q) (horvitzThompson Q) ≤
    approximateVariance Q Q.y0 Q.y1
  exact (ht_variance_identity_bound Q).2

/-- Design variance equals the second moment minus the squared first moment,
finite-sum identity used for the observed pooled variance on p. 52. -/
theorem designVariance_product {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) :
    designVariance L T = expectation L (fun s => (T s)^2) - (expectation L T)^2 := by
  rw [← designCovariance_self, designCovariance_product]
  simp [pow_two]

/-- A fixed shift does not change design variance, Section 4.2, p. 50. -/
theorem designVariance_add_const {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (c : ℝ) :
    designVariance L (fun s => c + T s) = designVariance L T := by
  unfold designVariance
  rw [expectation_add, expectation_const]
  apply expectation_congr_support
  intro s _
  congr 1
  ring

/-- Finite-population variance equals the mean square minus the squared
cluster mean, divisor M, p. 50. -/
theorem clusterVariance_product {M : ℕ} (hM : 0 < M) (v : Fin M → ℝ) :
    clusterVariance v = clusterMean (fun j => (v j)^2) - (clusterMean v)^2 := by
  rw [← clusterCovariance_self, clusterCovariance_product hM]
  simp [pow_two]

/-- The observed cluster mean is its fixed control mean plus the sampled
sum of potential differences divided by M, pp. 48, 52. -/
theorem observed_cluster_mean_identity (P : ClusterPopulation) (s : Finset (Fin P.M)) :
    clusterMean (observedTotal P s) = clusterMean P.y0 +
      armSum P true (fun j => P.y1 j - P.y0 j) s / P.M := by
  have he (j : Fin P.M) : observedTotal P s j =
      P.y0 j + (if j ∈ s then P.y1 j - P.y0 j else 0) := by
    unfold observedTotal
    split_ifs <;> ring
  unfold clusterMean
  simp_rw [he]
  simp [armSum, Finset.sum_add_distrib, add_div]

/-- Expected finite-population variance of observed totals under complete
randomization, the exact pooled-moment identity behind p. 52 (T16 finite lemma). -/
theorem observed_variance_expectation (P : ClusterPopulation) :
    expectation (clusterLaw P) (fun s => clusterVariance (observedTotal P s)) =
      (P.mt : ℝ) / P.M * clusterVariance P.y1 +
      (controlCount P : ℝ) / P.M * clusterVariance P.y0 +
      ((P.mt : ℝ) / P.M) * ((controlCount P : ℝ) / P.M) *
        (clusterMean (fun j => P.y1 j - P.y0 j))^2 -
      (((P.mt : ℝ) / P.M) * ((controlCount P : ℝ) / P.M) / ((P.M : ℝ) - 1)) *
        clusterVariance (fun j => P.y1 j - P.y0 j) := by
  classical
  let d : Fin P.M → ℝ := fun j => P.y1 j - P.y0 j
  let O : Finset (Fin P.M) → ℝ := fun s => clusterMean (observedTotal P s)
  have hM : 0 < P.M := lt_trans P.mt_pos P.mt_lt
  have hMr : (P.M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have hM1 : (P.M : ℝ) - 1 ≠ 0 := by
    have hh : (1 : ℝ) < P.M := by
      exact_mod_cast lt_of_le_of_lt (Nat.succ_le_of_lt P.mt_pos) P.mt_lt
    linarith
  have hO : O = fun s => clusterMean P.y0 + armSum P true d s / P.M := by
    funext s; exact observed_cluster_mean_identity P s
  have hmean : expectation (clusterLaw P) O =
      clusterMean P.y0 + (P.mt : ℝ) / P.M * clusterMean d := by
    rw [hO,expectation_add,expectation_const]
    simp_rw [div_eq_mul_inv]
    rw [expectation_mul_const,expected_treatment_sum]
    unfold clusterMean
    ring
  have hvariance : designVariance (clusterLaw P) O =
      ((P.mt : ℝ) * controlCount P / ((P.M : ℝ) - 1)) * clusterVariance d / (P.M : ℝ)^2 := by
    rw [hO,designVariance_add_const]
    simp_rw [div_eq_mul_inv]
    rw [designVariance_mul,← designCovariance_self,arm_sum_covariance,clusterCovariance_self]
    simp only [↓reduceIte,one_mul]
    ring
  have hsecond : expectation (clusterLaw P) (fun s => (O s)^2) =
      designVariance (clusterLaw P) O + (expectation (clusterLaw P) O)^2 := by
    rw [designVariance_product]
    ring
  have hsquare (s : Finset (Fin P.M)) :
      clusterMean (fun j => (observedTotal P s j)^2) =
      clusterMean (fun j => (P.y0 j)^2) +
        armSum P true (fun j => (P.y1 j)^2 - (P.y0 j)^2) s / P.M := by
    have he (j : Fin P.M) : (observedTotal P s j)^2 =
        (P.y0 j)^2 + (if j ∈ s then (P.y1 j)^2 - (P.y0 j)^2 else 0) := by
      unfold observedTotal
      split_ifs <;> ring
    unfold clusterMean
    simp_rw [he]
    simp [armSum, Finset.sum_add_distrib, add_div]
  have hfirst : expectation (clusterLaw P) (fun s => clusterMean (fun j => (observedTotal P s j)^2)) =
      clusterMean (fun j => (P.y0 j)^2) + (P.mt : ℝ) / P.M *
        (clusterMean (fun j => (P.y1 j)^2) - clusterMean (fun j => (P.y0 j)^2)) := by
    simp_rw [hsquare]
    rw [expectation_add,expectation_const]
    simp_rw [div_eq_mul_inv]
    rw [expectation_mul_const,expected_treatment_sum]
    unfold clusterMean
    rw [Finset.sum_sub_distrib]
    ring
  have hv : (fun s => clusterVariance (observedTotal P s)) =
      (fun s => clusterMean (fun j => (observedTotal P s j)^2) - (O s)^2) := by
    funext s
    exact clusterVariance_product hM (observedTotal P s)
  rw [hv,expectation_sub,hfirst,hsecond,hvariance,hmean,
    clusterVariance_product hM P.y0,clusterVariance_product hM P.y1]
  change _ = (P.mt : ℝ) / P.M *
      (clusterMean (fun j => (P.y1 j)^2) - (clusterMean P.y1)^2) +
    (controlCount P : ℝ) / P.M *
      (clusterMean (fun j => (P.y0 j)^2) - (clusterMean P.y0)^2) +
    ((P.mt : ℝ) / P.M) * ((controlCount P : ℝ) / P.M) * (clusterMean d)^2 -
    (((P.mt : ℝ) / P.M) * ((controlCount P : ℝ) / P.M) / ((P.M : ℝ) - 1)) * clusterVariance d
  have hdm : clusterMean d = clusterMean P.y1 - clusterMean P.y0 := clusterMean_sub _ _
  rw [hdm]
  have hcounts : (controlCount P : ℝ) = (P.M : ℝ) - P.mt := by
    simp [controlCount,Nat.cast_sub (le_of_lt P.mt_lt)]
  rw [hcounts]
  field_simp [hMr, hM1]
  <;> ring

/-- The exact expected excess of the pooled sharp-null variance estimator
above true HT variance, p. 52 (T16 finite lemma). It exposes both sufficient conditions. -/
theorem pooled_variance_excess (P : ClusterPopulation) :
    expectation (clusterLaw P) (sharpNullVarianceEstimator P) -
      designVariance (clusterLaw P) (horvitzThompson P) =
    (P.M : ℝ)^2 / ((populationSize P : ℝ)^2 * ((P.M : ℝ) - 1)) *
      (((P.M : ℝ) * ((P.mt : ℝ) - controlCount P) /
        ((P.mt : ℝ) * controlCount P)) * (clusterVariance P.y1 - clusterVariance P.y0) +
       (clusterMean (fun j => P.y1 j - P.y0 j))^2 +
       (((P.M : ℝ) - 2) / ((P.M : ℝ) - 1)) *
         clusterVariance (fun j => P.y1 j - P.y0 j)) := by
  have he : sharpNullVarianceEstimator P = fun s =>
      ((P.M : ℝ)^4 / ((populationSize P : ℝ)^2 * ((P.M : ℝ) - 1) * controlCount P * P.mt)) *
        clusterVariance (observedTotal P s) := by
    funext s; unfold sharpNullVarianceEstimator; ring
  rw [he,expectation_const_mul,observed_variance_expectation,ht_design_variance_formula]
  simp_rw [clusterVariance_sub, clusterCovariance_comm P.y1 P.y0]
  unfold htVarianceFormula
  have ht : (P.mt : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt P.mt_pos
  have hc : (controlCount P : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt)
  have hM : (P.M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt)
  have hM1 : (P.M : ℝ) - 1 ≠ 0 := by
    have hh : (1 : ℝ) < P.M := by
      exact_mod_cast lt_of_le_of_lt (Nat.succ_le_of_lt P.mt_pos) P.mt_lt
    linarith
  have hN : (populationSize P : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (populationSize_pos P)
  have hcounts : (controlCount P : ℝ) = (P.M : ℝ) - P.mt := by
    simp [controlCount,Nat.cast_sub (le_of_lt P.mt_lt)]
  have hmc : (P.M : ℝ) - P.mt ≠ 0 := by rw [← hcounts]; exact hc
  rw [hcounts]
  field_simp [hM, hM1, hN, ht, hmc]
  <;> ring

/-- Adding a constant to every cluster total leaves its finite-population
variance unchanged, p. 50; used for constant effects at the cluster scale, p. 52. -/
theorem clusterVariance_add_const {M : ℕ} (hM : 0 < M) (v : Fin M → ℝ) (c : ℝ) :
    clusterVariance (fun j => v j + c) = clusterVariance v := by
  unfold clusterVariance
  rw [clusterMean_add,clusterMean_const hM]
  congr 1
  funext j
  congr 1
  ring

/-- Conservativeness of the pooled sharp-null estimator in expectation,
p. 52: it holds if cluster-total effects are constant or m_c=m_t (T16).
It does not assert dominance on each realized assignment. -/
theorem sharp_null_variance_conservative (P : ClusterPopulation)
    (hcondition : (∃ τ : ℝ, ∀ j, P.y1 j - P.y0 j = τ) ∨ controlCount P = P.mt) :
    designVariance (clusterLaw P) (horvitzThompson P) ≤
      expectation (clusterLaw P) (sharpNullVarianceEstimator P) := by
  have hM : 0 < P.M := lt_trans P.mt_pos P.mt_lt
  have hM2 : (2 : ℝ) ≤ P.M := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.succ_le_of_lt P.mt_pos) P.mt_lt)
  have hM1 : (0 : ℝ) < (P.M : ℝ) - 1 := by linarith
  have hcoef : 0 ≤ (P.M : ℝ)^2 / ((populationSize P : ℝ)^2 * ((P.M : ℝ) - 1)) := by positivity
  have he := pooled_variance_excess P
  rcases hcondition with hconstant | hbalance
  · obtain ⟨τ,hτ⟩ := hconstant
    have hd : (fun j => P.y1 j - P.y0 j) = fun _ => τ := by funext j; exact hτ j
    have hy : P.y1 = fun j => P.y0 j + τ := by funext j; linarith [hτ j]
    have hv : clusterVariance (fun _ : Fin P.M => τ) = 0 := by
      simp [clusterVariance,clusterMean_const hM]
    rw [hd,hy,clusterVariance_add_const hM,clusterMean_const hM,hv] at he
    have hn := mul_nonneg hcoef (sq_nonneg τ)
    nlinarith [he]
  · have hcast : (controlCount P : ℝ) = P.mt := by exact_mod_cast hbalance
    rw [hcast] at he
    simp only [sub_self,mul_zero,zero_div,zero_mul,zero_add] at he
    have hn : 0 ≤ (clusterMean (fun j => P.y1 j - P.y0 j))^2 +
        (((P.M : ℝ) - 2) / ((P.M : ℝ) - 1)) * clusterVariance (fun j => P.y1 j - P.y0 j) := by
      exact add_nonneg (sq_nonneg _) (mul_nonneg (div_nonneg (by linarith) (le_of_lt hM1)) (clusterVariance_nonneg _))
    have hh := mul_nonneg hcoef hn
    nlinarith [he]

/-- k_optim,a = σ(n,Y^T_a)/σ²(n), equation (26) and its treatment analogue,
p. 57. The theorems using this ratio explicitly require positive size variance. -/
def armOptimalCoefficient (P : ClusterPopulation) (a : Bool) : ℝ :=
  clusterCovariance (fun j => (P.n j : ℝ)) (if a then P.y1 else P.y0) /
    clusterVariance (fun j => (P.n j : ℝ))

/-- "k_optim* = m_t k_optim,c/M + m_c k_optim,t/M", p. 57 and Appendix C,
p. 73. The arm weights appear in the reversed order printed in the paper. -/
def optimalCoefficient (P : ClusterPopulation) : ℝ :=
  (P.mt : ℝ) / P.M * armOptimalCoefficient P false +
    (controlCount P : ℝ) / P.M * armOptimalCoefficient P true

/-- Exact completion of the square behind equation (26), pp. 56-57.
For σ²(n)>0 the excess differenced variance above its optimum is
σ²(n)(k-k_optim,a)² (T14 finite lemma). -/
theorem arm_variance_completed_square (P : ClusterPopulation) (a : Bool)
    (hsize : 0 < clusterVariance (fun j => (P.n j : ℝ))) (k : ℝ) :
    clusterVariance (rajPotential P a k) =
      clusterVariance (rajPotential P a (armOptimalCoefficient P a)) +
        clusterVariance (fun j => (P.n j : ℝ)) * (k - armOptimalCoefficient P a)^2 := by
  have hM : 0 < P.M := lt_trans P.mt_pos P.mt_lt
  unfold rajPotential
  rw [differenced_variance hM, differenced_variance hM]
  unfold armOptimalCoefficient
  rw [clusterCovariance_comm (fun j => (P.n j : ℝ))]
  field_simp
  <;> ring
/-- Equation (26), Section 5.3, pp. 56-57: each arm's optimal coefficient
uniquely minimizes its differenced potential-total variance when size variance
is positive (T14(a)). -/
theorem arm_coefficient_optimal (P : ClusterPopulation)
    (hsize : 0 < clusterVariance (fun j => (P.n j : ℝ))) (a : Bool) (k : ℝ) :
    clusterVariance (rajPotential P a (armOptimalCoefficient P a)) ≤
      clusterVariance (rajPotential P a k) ∧
    (clusterVariance (rajPotential P a (armOptimalCoefficient P a)) =
      clusterVariance (rajPotential P a k) ↔ k = armOptimalCoefficient P a) := by
  have he := arm_variance_completed_square P a hsize k
  have hnon : 0 ≤ clusterVariance (fun j => (P.n j : ℝ)) *
      (k - armOptimalCoefficient P a)^2 := mul_nonneg (le_of_lt hsize) (sq_nonneg _)
  constructor
  · linarith
  · constructor
    · intro hh
      have hz : clusterVariance (fun j => (P.n j : ℝ)) * (k - armOptimalCoefficient P a)^2 = 0 := by linarith
      have hsq : (k - armOptimalCoefficient P a)^2 = 0 :=
        (mul_eq_zero.mp hz).resolve_left (ne_of_gt hsize)
      have hsub : k - armOptimalCoefficient P a = 0 := (sq_eq_zero_iff).mp hsq
      linarith
    · intro hh; rw [hh]

/-- The interval descriptions in Section 5.3, p. 57, are exactly equivalent
to k² < 2 k k_optim*: (0,2k*) for k*>0 and (2k*,0) for k*<0 (T14(c)). -/
theorem coefficient_improvement_intervals (k star : ℝ) :
    (k^2 < 2 * k * star ↔
      (0 < star ∧ 0 < k ∧ k < 2 * star) ∨ (star < 0 ∧ 2 * star < k ∧ k < 0)) := by
  constructor
  · intro h
    by_cases hk : 0 ≤ k
    · left
      have hkp : 0 < k := by
        by_contra hh
        have hk0 : k = 0 := le_antisymm (not_lt.mp hh) hk
        rw [hk0] at h
        norm_num at h
      have hs : k < 2 * star := by nlinarith
      exact ⟨by linarith, hkp, hs⟩
    · right
      have hkn : k < 0 := lt_of_not_ge hk
      have hs : 2 * star < k := by nlinarith
      exact ⟨by linarith, hs, hkn⟩
  · rintro (⟨hs, hk, hks⟩ | ⟨hs, hks, hk⟩) <;> nlinarith

/-- If all clusters have equal size, every centered size is zero and every
fixed-k Des Raj estimator equals HT, the boundary case of Section 5.3 (T14). -/
theorem equal_size_raj_eq_ht (P : ClusterPopulation) (n : ℕ)
    (hn : ∀ j, P.n j = n) (k : ℝ) (s : Finset (Fin P.M)) :
    desRaj P k s = horvitzThompson P s := by
  have hM : 0 < P.M := lt_trans P.mt_pos P.mt_lt
  have hm : clusterMean (fun j => (P.n j : ℝ)) = n := by
    simp_rw [hn]
    exact clusterMean_const hM n
  have hU : ∀ a, rajPotential P a k = if a then P.y1 else P.y0 := by
    intro a
    funext j
    unfold rajPotential differenced
    rw [hm]
    simp [hn j]
  simp [desRaj, rajTotal, hU, horvitzThompson, htTotal]

/-- A uniform law on every point of a finite nonempty space. This is the
Cartesian-product representation of independent randomizations on pp. 46, 53. -/
def fullUniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω :=
  uniformLaw Finset.univ ⟨Classical.choice inferInstance, Finset.mem_univ _⟩

/-- Expectation under the full uniform law is the finite average, pp. 46, 53. -/
theorem full_uniform_expectation {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (T : Ω → ℝ) : expectation (fullUniformLaw Ω) T =
      (∑ s, T s) / (Fintype.card Ω : ℝ) := by
  classical
  change (∑ s : Ω, (1 / (Fintype.card Ω : ℝ)) * T s) = _
  rw [← Finset.mul_sum]
  ring

/-- A product of coordinate moments factors under the uniform finite
Cartesian-product law; independent blocks, p. 53, and copies, p. 46. -/
theorem uniform_product_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ω : ι → Type*) [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (f : ∀ i, Ω i → ℝ) :
    expectation (fullUniformLaw (∀ i, Ω i)) (fun s => ∏ i, f i (s i)) =
      ∏ i, expectation (fullUniformLaw (Ω i)) (f i) := by
  classical
  simp only [full_uniform_expectation]
  rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]

/-- One coordinate of a product randomization has its original uniform
law. This is the marginal identity for the independent copies on p. 46. -/
theorem uniform_coordinate_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ω : ι → Type*) [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (i : ι) (T : Ω i → ℝ) :
    expectation (fullUniformLaw (∀ j, Ω j)) (fun s => T (s i)) =
      expectation (fullUniformLaw (Ω i)) T := by
  classical
  let f : ∀ j, Ω j → ℝ := Function.update (fun j (_ : Ω j) => (1 : ℝ)) i T
  have hx (s : ∀ j, Ω j) : (∏ j, f j (s j)) = T (s i) := by
    rw [Finset.prod_eq_single i]
    · simp [f]
    · intro j _ hji; simp [f, Function.update_of_ne hji]
    · simp
  have hm : (∏ j, expectation (fullUniformLaw (Ω j)) (f j)) =
      expectation (fullUniformLaw (Ω i)) T := by
    rw [Finset.prod_eq_single i]
    · simp [f]
    · intro j _ hji; simp [f, Function.update_of_ne hji, expectation_const]
    · simp
  have h := uniform_product_moment Ω f
  simp_rw [hx] at h
  exact h.trans hm

/-- Distinct coordinates of the uniform product law have factored joint
moments. Independence here is proved by finite sums, pp. 46, 53. -/
theorem uniform_coordinate_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ω : ι → Type*) [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (i j : ι) (hij : i ≠ j) (T : Ω i → ℝ) (U : Ω j → ℝ) :
    expectation (fullUniformLaw (∀ k, Ω k)) (fun s => T (s i) * U (s j)) =
      expectation (fullUniformLaw (Ω i)) T * expectation (fullUniformLaw (Ω j)) U := by
  classical
  let f : ∀ k, Ω k → ℝ := Function.update (fun k (_ : Ω k) => (1 : ℝ)) i T
  let g : ∀ k, Ω k → ℝ := Function.update (fun k (_ : Ω k) => (1 : ℝ)) j U
  have hf (s : ∀ k, Ω k) : (∏ k, f k (s k)) = T (s i) := by
    rw [Finset.prod_eq_single i]
    · simp [f]
    · intro k _ hki; simp [f, Function.update_of_ne hki]
    · simp
  have hg (s : ∀ k, Ω k) : (∏ k, g k (s k)) = U (s j) := by
    rw [Finset.prod_eq_single j]
    · simp [g]
    · intro k _ hkj; simp [g, Function.update_of_ne hkj]
    · simp
  have he (k : ι) : expectation (fullUniformLaw (Ω k)) (fun x => f k x * g k x) =
      expectation (fullUniformLaw (Ω k)) (f k) *
        expectation (fullUniformLaw (Ω k)) (g k) := by
    by_cases hki : k = i
    · subst k; simp [g, Function.update_of_ne hij, expectation_const, f]
    · simp [f, Function.update_of_ne hki, expectation_const]
  have h := uniform_product_moment Ω (fun k x => f k x * g k x)
  simp_rw [Finset.prod_mul_distrib, hf, hg, he] at h
  rw [Finset.prod_mul_distrib, ← uniform_product_moment Ω f, ← uniform_product_moment Ω g] at h
  simp_rw [hf, hg] at h
  rw [uniform_coordinate_expectation, uniform_coordinate_expectation] at h
  exact h

/-- Covariance is bilinear over finite sums of estimators, equation (19), p. 53. -/
theorem designCovariance_sum_sum {Ω ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : FiniteLaw Ω) (T : ι → Ω → ℝ) (U : κ → Ω → ℝ) :
    designCovariance L (fun s => ∑ i, T i s) (fun s => ∑ j, U j s) =
      ∑ i, ∑ j, designCovariance L (T i) (U j) := by
  classical
  simp only [designCovariance_product, expectation_fintype_sum,
    Finset.sum_mul_sum, Finset.sum_sub_distrib]

/-- The variance of a sum of independent coordinate estimators is the sum
of their original variances, the finite identity on pp. 46, 53. -/
theorem uniform_sum_variance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ω : ι → Type*) [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (T : ∀ i, Ω i → ℝ) :
    designVariance (fullUniformLaw (∀ i, Ω i)) (fun s => ∑ i, T i (s i)) =
      ∑ i, designVariance (fullUniformLaw (Ω i)) (T i) := by
  classical
  rw [← designCovariance_self, designCovariance_sum_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [designCovariance_product,
      uniform_coordinate_expectation Ω i (fun x => T i x * T i x),
      uniform_coordinate_expectation Ω i (T i)]
    rw [← designCovariance_product, designCovariance_self]
  · intro j _ hij
    rw [designCovariance_product, uniform_coordinate_product Ω i j (Ne.symm hij),
      uniform_coordinate_expectation, uniform_coordinate_expectation]
    ring
  · simp

/-- A valid cluster assignment exists because 0 < m_t < M, p. 44. -/
instance assignmentSubtypeNonempty (P : ClusterPopulation) :
    Nonempty {s : Finset (Fin P.M) // s ∈ assignments P} :=
  ⟨⟨(assignments_nonempty P).choose, (assignments_nonempty P).choose_spec⟩⟩

/-- Finite sums on the subtype of valid assignments agree with sums on the
paper's randomization support; no new probability law is assumed. -/
theorem assignment_subtype_expectation (P : ClusterPopulation)
    (T : Finset (Fin P.M) → ℝ) :
    expectation (fullUniformLaw {s : Finset (Fin P.M) // s ∈ assignments P})
      (fun s => T s.val) = expectation (clusterLaw P) T := by
  classical
  rw [full_uniform_expectation, clusterLaw, uniform_expectation]
  simp [Fintype.card_coe, Finset.sum_attach]
/-- The variance of a subtype-indexed estimator agrees with variance over
all complete randomizations, the finite law of Section 3.2, p. 44. -/
theorem assignment_subtype_variance (P : ClusterPopulation)
    (T : Finset (Fin P.M) → ℝ) :
    designVariance (fullUniformLaw {s : Finset (Fin P.M) // s ∈ assignments P})
      (fun s => T s.val) = designVariance (clusterLaw P) T := by
  rw [← designCovariance_self, designCovariance_product]
  rw [assignment_subtype_expectation P (fun s => T s * T s),
    assignment_subtype_expectation P T]
  rw [← designCovariance_product, designCovariance_self]

/-- A fixed coefficient scales design variance by its square, p. 50. -/
theorem designVariance_const_mul {Ω : Type*} (L : FiniteLaw Ω)
    (T : Ω → ℝ) (c : ℝ) :
    designVariance L (fun s => c * T s) = c^2 * designVariance L T := by
  have he : (fun s => c * T s) = (fun s => T s * c) := by funext s; ring
  rw [he, designVariance_mul]
  ring
/-- Independent block assignments: a tuple of complete-randomization
assignments, one within each block, Section 4.3, p. 53. -/
abbrev BlockAssignments {B : ℕ} (P : Fin B → ClusterPopulation) :=
  (b : Fin B) → {s : Finset (Fin (P b).M) // s ∈ assignments (P b)}

/-- Uniform product law on independent block experiments, p. 53.
Equal weights on the Cartesian product give independence, with no assumed
covariance conclusions. -/
def blockLaw {B : ℕ} (P : Fin B → ClusterPopulation) : FiniteLaw (BlockAssignments P) :=
  uniformLaw Finset.univ ⟨(fun b =>
    ⟨(assignments_nonempty (P b)).choose, (assignments_nonempty (P b)).choose_spec⟩),
    Finset.mem_univ _⟩

/-- The total number of individuals over all blocks "N = ∑_b N_b", p. 53. -/
def blockedSize {B : ℕ} (P : Fin B → ClusterPopulation) : ℕ :=
  ∑ b, populationSize (P b)

/-- Equation (18), p. 53: Δ_HT^B = ∑_b (N_b/N) Δ_HT^b. -/
def blockedHT {B : ℕ} (P : Fin B → ClusterPopulation) (s : BlockAssignments P) : ℝ :=
  ∑ b, (populationSize (P b) : ℝ) / blockedSize P * horvitzThompson (P b) (s b).val

/-- Overall individual ATE across the B blocks, equation (18), p. 53. -/
def blockedATE {B : ℕ} (P : Fin B → ClusterPopulation) : ℝ :=
  (∑ b, ((∑ j, (P b).y1 j) - ∑ j, (P b).y0 j)) / blockedSize P

/-- Equations (18)-(19), p. 53 (T15(f)): block-weighted HT is unbiased
and its variance is the sum of squared weights times within-block variances.
The assignment law is the independent product of complete block randomizations. -/
theorem independent_blocks_unbiased_variance {B : ℕ} (hB : 0 < B)
    (P : Fin B → ClusterPopulation) :
    expectation (blockLaw P) (blockedHT P) = blockedATE P ∧
    designVariance (blockLaw P) (blockedHT P) =
      ∑ b, ((populationSize (P b) : ℝ) / blockedSize P)^2 *
        designVariance (clusterLaw (P b)) (horvitzThompson (P b)) := by
  classical
  have hN : (blockedSize P : ℝ) ≠ 0 := by
    have hh : 0 < blockedSize P := by
      unfold blockedSize
      exact Finset.sum_pos (fun b _ => populationSize_pos (P b))
        ⟨⟨0,hB⟩, Finset.mem_univ _⟩
    exact_mod_cast Nat.ne_of_gt hh
  constructor
  · change expectation (fullUniformLaw (BlockAssignments P)) (fun s => ∑ b,
        (populationSize (P b) : ℝ) / blockedSize P * horvitzThompson (P b) (s b).val) = _
    rw [expectation_fintype_sum]
    have hm (b : Fin B) : expectation (fullUniformLaw (BlockAssignments P))
        (fun s => horvitzThompson (P b) (s b).val) =
        expectation (clusterLaw (P b)) (horvitzThompson (P b)) := by
      exact (uniform_coordinate_expectation (fun b : Fin B => {s : Finset (Fin (P b).M) // s ∈ assignments (P b)}) b
        (fun s => horvitzThompson (P b) s.val)).trans
        (assignment_subtype_expectation (P b) (horvitzThompson (P b)))
    simp_rw [expectation_const_mul, hm]
    simp_rw [(ht_unbiased _).2.2]
    have he (b : Fin B) : (populationSize (P b) : ℝ) / blockedSize P *
        averageTreatmentEffect (P b) =
        ((∑ j, (P b).y1 j) - ∑ j, (P b).y0 j) / blockedSize P := by
      have hb : (populationSize (P b) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (populationSize_pos (P b))
      unfold averageTreatmentEffect
      field_simp
    simp_rw [he]
    simp only [blockedATE, div_eq_mul_inv, ← Finset.sum_mul]
  · change designVariance (fullUniformLaw (BlockAssignments P)) (fun s => ∑ b,
        (populationSize (P b) : ℝ) / blockedSize P * horvitzThompson (P b) (s b).val) = _
    rw [uniform_sum_variance (fun b : Fin B => {s : Finset (Fin (P b).M) // s ∈ assignments (P b)})
      (fun b s => (populationSize (P b) : ℝ) / blockedSize P * horvitzThompson (P b) s.val)]
    simp_rw [designVariance_const_mul, assignment_subtype_variance]

/-- The plug-in conservativeness assertion after equation (19), p. 53 (T15(f)):
any conservative variance estimators within independent blocks give a
conservative overall variance estimator with squared individual-count weights. -/
theorem independent_blocks_variance_estimator_conservative {B : ℕ} (hB : 0 < B)
    (P : Fin B → ClusterPopulation)
    (Vhat : (b : Fin B) → Finset (Fin (P b).M) → ℝ)
    (hVhat : ∀ b, designVariance (clusterLaw (P b)) (horvitzThompson (P b)) ≤
      expectation (clusterLaw (P b)) (Vhat b)) :
    designVariance (blockLaw P) (blockedHT P) ≤
      expectation (blockLaw P) (fun s => ∑ b,
        ((populationSize (P b) : ℝ) / blockedSize P)^2 * Vhat b (s b).val) := by
  classical
  rw [(independent_blocks_unbiased_variance hB P).2]
  change _ ≤ expectation (fullUniformLaw (BlockAssignments P)) (fun s => ∑ b,
    ((populationSize (P b) : ℝ) / blockedSize P)^2 * Vhat b (s b).val)
  rw [expectation_fintype_sum]
  have hm (b : Fin B) : expectation (fullUniformLaw (BlockAssignments P))
      (fun s => Vhat b (s b).val) = expectation (clusterLaw (P b)) (Vhat b) := by
    exact (uniform_coordinate_expectation (fun b : Fin B => {s : Finset (Fin (P b).M) // s ∈ assignments (P b)}) b
      (fun s => Vhat b s.val)).trans (assignment_subtype_expectation (P b) (Vhat b))
  simp_rw [expectation_const_mul, hm]
  exact Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hVhat b) (sq_nonneg _))

/-- Brewer replication with growing number of clusters: h independent
copies of the original population, each assigning exactly m_t clusters to
treatment, Section 3.3 and Figure 1A, pp. 46-47. -/
abbrev CopyAssignments (P : ClusterPopulation) (h : ℕ) :=
  Fin h → {s : Finset (Fin P.M) // s ∈ assignments P}

/-- Uniform Cartesian product of the per-copy assignment sets, the independent
randomizations in Figure 1A, p. 46. -/
def copyLaw (P : ClusterPopulation) (h : ℕ) : FiniteLaw (CopyAssignments P h) :=
  uniformLaw Finset.univ ⟨(fun _ =>
    ⟨(assignments_nonempty P).choose, (assignments_nonempty P).choose_spec⟩),
    Finset.mem_univ _⟩

/-- Pooled difference-in-means over h copies, equation (9), p. 46.
Both the numerator and individual-count denominator sum over the copies. -/
def copiedDifferenceInMeans (P : ClusterPopulation) (h : ℕ)
    (s : CopyAssignments P h) : ℝ :=
  (∑ r, armSum P true P.y1 (s r).val) / (∑ r, armSize P true (s r).val) -
  (∑ r, armSum P false P.y0 (s r).val) / (∑ r, armSize P false (s r).val)

/-- Per-copy normalized arm sums in the four weak-law limits on p. 46. -/
def copyAverage (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ) (h : ℕ)
    (s : CopyAssignments P h) : ℝ := (∑ r, armSum P a v (s r).val) / h

/-- Each selected arm feature sum is bounded by the fixed sum of absolute
cluster features. Thus all four per-copy variables used in the weak laws on
p. 46 are bounded for each original finite population (T17 finite lemma). -/
theorem arm_sum_bounded (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ)
    (s : Finset (Fin P.M)) : |armSum P a v s| ≤ ∑ j, |v j| := by
  unfold armSum
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => abs_nonneg (v j))

/-- For fixed h the per-copy average has the one-copy mean and variance
V(arm sum)/h, the finite identities supporting the weak laws on p. 46 (T17). -/
theorem copy_average_moments (P : ClusterPopulation) (a : Bool)
    (v : Fin P.M → ℝ) (h : ℕ) (hh : 0 < h) :
    expectation (copyLaw P h) (copyAverage P a v h) =
      ((if a then P.mt else controlCount P) : ℝ) / P.M * ∑ j, v j ∧
    designVariance (copyLaw P h) (copyAverage P a v h) =
      designVariance (clusterLaw P) (armSum P a v) / h := by
  classical
  have hhr : (h : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hh
  constructor
  · change expectation (fullUniformLaw (CopyAssignments P h))
      (fun s => (∑ r, armSum P a v (s r).val) / h) = _
    simp_rw [div_eq_mul_inv]
    rw [expectation_mul_const, expectation_fintype_sum]
    have hm (r : Fin h) : expectation (fullUniformLaw (CopyAssignments P h))
        (fun s => armSum P a v (s r).val) = expectation (clusterLaw P) (armSum P a v) := by
      exact (uniform_coordinate_expectation (fun _ : Fin h => {s : Finset (Fin P.M) // s ∈ assignments P}) r
        (fun s => armSum P a v s.val)).trans (assignment_subtype_expectation P (armSum P a v))
    simp_rw [hm, expected_arm_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    <;> ring
  · change designVariance (fullUniformLaw (CopyAssignments P h))
      (fun s => (∑ r, armSum P a v (s r).val) / h) = _
    simp_rw [div_eq_mul_inv]
    rw [designVariance_mul, uniform_sum_variance (fun _ : Fin h => {s : Finset (Fin P.M) // s ∈ assignments P})
      (fun _ s => armSum P a v s.val)]
    simp_rw [assignment_subtype_variance]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    <;> ring

/-- Pointwise inequalities on the randomization support pass through finite
expectation, p. 42. -/
theorem expectation_mono_support {Ω : Type*} (L : FiniteLaw Ω) (T U : Ω → ℝ)
    (h : ∀ s ∈ L.support, T s ≤ U s) : expectation L T ≤ expectation L U := by
  unfold expectation
  exact Finset.sum_le_sum (fun s hs => mul_le_mul_of_nonneg_left (h s hs) (L.nonneg s hs))

/-- A deterministic denominator lower bound controls the MSE of a ratio,
a finite substitute for the Slutsky step in equation (9), p. 46. -/
theorem ratio_mse_bound {Ω : Type*} (L : FiniteLaw Ω) (T U : Ω → ℝ)
    (a b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hU : ∀ s ∈ L.support, c ≤ U s) :
    meanSquaredError L (fun s => T s / U s) (a / b) ≤
      (2 / c^2) * (meanSquaredError L T a + (a / b)^2 * meanSquaredError L U b) := by
  have he : ∀ s ∈ L.support,
      c^2 * (T s / U s - a / b)^2 ≤
        2 * (T s - a)^2 + 2 * (a / b)^2 * (U s - b)^2 := by
    intro s hs
    have hu : 0 < U s := lt_of_lt_of_le hc (hU s hs)
    have hid : U s * (T s / U s - a / b) = (T s - a) - (a / b) * (U s - b) := by
      field_simp
      <;> ring
    have hcu : c^2 ≤ (U s)^2 := by nlinarith [hU s hs]
    have hmul := mul_le_mul_of_nonneg_right hcu (sq_nonneg (T s / U s - a / b))
    have hsquares : ((T s - a) - (a / b) * (U s - b))^2 ≤
        2 * (T s - a)^2 + 2 * ((a / b) * (U s - b))^2 := by
      nlinarith [sq_nonneg ((T s - a) + (a / b) * (U s - b))]
    calc
      c^2 * (T s / U s - a / b)^2 ≤
          (U s)^2 * (T s / U s - a / b)^2 := hmul
      _ = ((T s - a) - (a / b) * (U s - b))^2 := by rw [← mul_pow, hid]
      _ ≤ 2 * (T s - a)^2 + 2 * ((a / b) * (U s - b))^2 := hsquares
      _ = _ := by ring
  have he' := expectation_mono_support L _ _ he
  rw [expectation_const_mul, expectation_add, expectation_const_mul,
    expectation_const_mul] at he'
  change c^2 * meanSquaredError L (fun s => T s / U s) (a / b) ≤
    2 * meanSquaredError L T a + (2 * (a / b)^2) * meanSquaredError L U b at he'
  have he'' : meanSquaredError L (fun s => T s / U s) (a / b) ≤
      (2 * meanSquaredError L T a + (2 * (a / b)^2) * meanSquaredError L U b) / c^2 :=
    (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by nlinarith [he'])
  calc
    meanSquaredError L (fun s => T s / U s) (a / b) ≤
      (2 * meanSquaredError L T a + (2 * (a / b)^2) * meanSquaredError L U b) / c^2 := he''
    _ = _ := by ring

/-- The MSE of a difference is bounded by twice the sum of the two MSEs,
the finite error bound for the two arm ratios in equation (9), p. 46. -/
theorem difference_mse_bound {Ω : Type*} (L : FiniteLaw Ω) (T U : Ω → ℝ) (a b : ℝ) :
    meanSquaredError L (fun s => T s - U s) (a - b) ≤
      2 * (meanSquaredError L T a + meanSquaredError L U b) := by
  have he : ∀ s ∈ L.support,
      (T s - U s - (a - b))^2 ≤ 2 * (T s - a)^2 + 2 * (U s - b)^2 := by
    intro s _
    nlinarith [sq_nonneg ((T s - a) + (U s - b))]
  have hh := expectation_mono_support L _ _ he
  rw [expectation_add, expectation_const_mul, expectation_const_mul] at hh
  change meanSquaredError L (fun s => T s - U s) (a - b) ≤
    2 * meanSquaredError L T a + 2 * meanSquaredError L U b at hh
  linarith
/-- Squared estimation error has nonnegative finite design expectation,
Section 3.3, p. 45, and correction P020-E001. -/
theorem meanSquaredError_nonneg {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (d : ℝ) :
    0 ≤ meanSquaredError L T d :=
  expectation_nonneg L _ (fun _ _ => sq_nonneg _)

/-- A fixed real constant divided by the positive population index tends
to zero, the scalar rate used in Brewer replication on p. 46. -/
theorem constant_div_nat_tendsto (C : ℝ) :
    Tendsto (fun h : ℕ => C / (h : ℝ)) atTop (nhds 0) := by
  have hi : Tendsto (fun h : ℕ => (h : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hi :
    Tendsto (fun h : ℕ => C * (h : ℝ)⁻¹) atTop (nhds (C * 0)))

/-- An exact finite MSE bound C/h implies consistency over the varying
finite randomization spaces of Section 3.3, p. 45. -/
theorem mse_rate_consistent {Ω : ℕ → Type*} (L : ∀ h, FiniteLaw (Ω h))
    (T : ∀ h, Ω h → ℝ) (d : ℕ → ℝ) (C : ℝ)
    (hbound : ∀ h, 0 < h → meanSquaredError (L h) (T h) (d h) ≤ C / h) :
    DesignConsistent L T d := by
  apply vanishing_mse_consistent L T d
  apply squeeze_zero' (Filter.Eventually.of_forall (fun h => meanSquaredError_nonneg (L h) (T h) (d h)))
    _ (constant_div_nat_tendsto C)
  filter_upwards [Filter.eventually_gt_atTop 0] with h hh
  exact hbound h hh

/-- The average over h independent copies is unbiased, so its MSE equals
its one-copy design variance divided by h, the finite weak-law rate on p. 46. -/
theorem copy_average_mse (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ)
    (h : ℕ) (hh : 0 < h) :
    meanSquaredError (copyLaw P h) (copyAverage P a v h)
      (((if a then P.mt else controlCount P) : ℝ) / P.M * ∑ j, v j) =
        designVariance (clusterLaw P) (armSum P a v) / h := by
  rw [mse_bias_variance]
  unfold designBias
  obtain ⟨he,hv⟩ := copy_average_moments P a v h hh
  rw [he,hv]
  ring

/-- All per-copy averages of a fixed cluster feature converge in probability
to their one-copy means, the four weak-law statements on p. 46. -/
theorem copy_average_consistent (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ) :
    DesignConsistent (copyLaw P) (copyAverage P a v)
      (fun _ => ((if a then P.mt else controlCount P) : ℝ) / P.M * ∑ j, v j) := by
  apply mse_rate_consistent _ _ _ (designVariance (clusterLaw P) (armSum P a v))
  intro h hh
  exact le_of_eq (copy_average_mse P a v h hh)

/-- Every selected cluster contains at least one individual, so the arm's
individual count is at least its fixed cluster count, pp. 44, 46. -/
theorem arm_size_ge_count (P : ClusterPopulation) (a : Bool) (s : Finset (Fin P.M))
    (hs : s ∈ assignments P) : ((if a then P.mt else controlCount P) : ℝ) ≤ armSize P a s := by
  classical
  obtain ⟨ht,hc⟩ := assignment_arm_counts P s hs
  have hn (j : Fin P.M) : (1 : ℝ) ≤ P.n j := by exact_mod_cast Nat.succ_le_of_lt (P.n_pos j)
  cases a <;> unfold armSize armSum <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · calc
      (controlCount P : ℝ) = ∑ j ∈ controls s, (1 : ℝ) := by simp [hc]
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hn j)
  · calc
      (P.mt : ℝ) = ∑ j ∈ s, (1 : ℝ) := by simp [ht]
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hn j)

/-- The normalized arm-size denominator in every positive-h Brewer copy
population is bounded below by the original positive arm cluster count, p. 46. -/
theorem copy_size_ge_count (P : ClusterPopulation) (a : Bool) (h : ℕ) (hh : 0 < h)
    (s : CopyAssignments P h) :
    ((if a then P.mt else controlCount P) : ℝ) ≤ copyAverage P a (fun j => (P.n j : ℝ)) h s := by
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  apply (le_div_iff₀ hhr).mpr
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => arm_size_ge_count P a (s r).val (s r).property)
  simpa [copyAverage, armSize, Finset.sum_const, nsmul_eq_mul, mul_comm] using hs

/-- Pooling the h copies is the difference of the two ratios of normalized
arm sums, equation (9), p. 46. The same factor h cancels in each ratio. -/
theorem copied_ratio_identity (P : ClusterPopulation) (h : ℕ) (hh : 0 < h)
    (s : CopyAssignments P h) :
    copiedDifferenceInMeans P h s =
      copyAverage P true P.y1 h s / copyAverage P true (fun j => (P.n j : ℝ)) h s -
      copyAverage P false P.y0 h s / copyAverage P false (fun j => (P.n j : ℝ)) h s := by
  have hhr : (h : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hh
  simp only [copyAverage, copiedDifferenceInMeans, armSize]
  rw [div_div_div_cancel_right₀ hhr, div_div_div_cancel_right₀ hhr]
/-- Each arm's pooled individual mean in Brewer replication, equation (9),
p. 46: its normalized outcome sum divided by its normalized individual count. -/
def copyArmRatio (P : ClusterPopulation) (a : Bool) (h : ℕ) (s : CopyAssignments P h) : ℝ :=
  copyAverage P a (if a then P.y1 else P.y0) h s /
    copyAverage P a (fun j => (P.n j : ℝ)) h s

/-- A fixed-population finite bound coefficient for the MSE of the arm ratio
in equation (9), p. 46. Its two terms come from the one-copy outcome and size variances. -/
def copyArmRatioMSEConstant (P : ClusterPopulation) (a : Bool) : ℝ :=
  (2 / (((if a then P.mt else controlCount P) : ℝ)^2)) *
    (designVariance (clusterLaw P) (armSum P a (if a then P.y1 else P.y0)) +
      ((∑ j, (if a then P.y1 else P.y0) j) / (populationSize P : ℝ))^2 *
        designVariance (clusterLaw P) (armSum P a (fun j => (P.n j : ℝ))))

/-- Each arm ratio in equation (9), p. 46, has MSE at most a fixed constant
C_a/h. No additional moment assumption is used in this finite-population bound. -/
theorem copied_arm_ratio_mse_bound (P : ClusterPopulation) (a : Bool) (h : ℕ) (hh : 0 < h) :
    meanSquaredError (copyLaw P h) (copyArmRatio P a h)
      ((∑ j, (if a then P.y1 else P.y0) j) / (populationSize P : ℝ)) ≤
        copyArmRatioMSEConstant P a / h := by
  let v : Fin P.M → ℝ := if a then P.y1 else P.y0
  let m : ℝ := if a then P.mt else controlCount P
  have hm : 0 < m := by
    cases a <;> simp only [m, Bool.false_eq_true, ↓reduceIte]
    · exact_mod_cast Nat.sub_pos_of_lt P.mt_lt
    · exact_mod_cast P.mt_pos
  have hM : (0 : ℝ) < P.M := by exact_mod_cast lt_trans P.mt_pos P.mt_lt
  have hN : (0 : ℝ) < populationSize P := by exact_mod_cast populationSize_pos P
  have hb : 0 < m / P.M * (populationSize P : ℝ) := by positivity
  have hlim : (m / P.M * ∑ j, v j) / (m / P.M * (populationSize P : ℝ)) =
      (∑ j, v j) / (populationSize P : ℝ) := by
    field_simp
    <;> ring
  have hr := ratio_mse_bound (copyLaw P h) (copyAverage P a v h)
    (copyAverage P a (fun j => (P.n j : ℝ)) h)
    (m / P.M * ∑ j, v j) (m / P.M * (populationSize P : ℝ)) m hb hm
    (fun s _ => copy_size_ge_count P a h hh s)
  rw [hlim] at hr
  have hsize : ∑ j, (P.n j : ℝ) = populationSize P := by simp [populationSize, Nat.cast_sum]
  have hsizeMSE := copy_average_mse P a (fun j => (P.n j : ℝ)) h hh
  rw [hsize] at hsizeMSE
  rw [copy_average_mse P a v h hh, hsizeMSE] at hr
  change meanSquaredError (copyLaw P h) (copyArmRatio P a h)
    ((∑ j, (if a then P.y1 else P.y0) j) / (populationSize P : ℝ)) ≤ _ at hr
  exact hr.trans_eq (by unfold copyArmRatioMSEConstant; dsimp [v,m]; ring)

/-- The pooled difference-in-means has an exact finite MSE upper bound of
order 1/h along the paper's independent-copy sequence, equation (9), p. 46. -/
theorem copied_difference_mse_bound (P : ClusterPopulation) (h : ℕ) (hh : 0 < h) :
    meanSquaredError (copyLaw P h) (copiedDifferenceInMeans P h) (averageTreatmentEffect P) ≤
      (2 * copyArmRatioMSEConstant P true + 2 * copyArmRatioMSEConstant P false) / h := by
  have hid : copiedDifferenceInMeans P h = fun s => copyArmRatio P true h s - copyArmRatio P false h s := by
    funext s
    exact copied_ratio_identity P h hh s
  have hd : averageTreatmentEffect P =
      (∑ j, P.y1 j) / (populationSize P : ℝ) - (∑ j, P.y0 j) / (populationSize P : ℝ) := by
    simp [averageTreatmentEffect, sub_div]
  rw [hid,hd]
  have hb := difference_mse_bound (copyLaw P h) (copyArmRatio P true h) (copyArmRatio P false h)
    ((∑ j, P.y1 j) / (populationSize P : ℝ)) ((∑ j, P.y0 j) / (populationSize P : ℝ))
  have ht := copied_arm_ratio_mse_bound P true h hh
  have hc := copied_arm_ratio_mse_bound P false h hh
  simp only [Bool.false_eq_true, ↓reduceIte] at ht hc
  calc
    _ ≤ 2 * (meanSquaredError (copyLaw P h) (copyArmRatio P true h) ((∑ j, P.y1 j) / (populationSize P : ℝ)) +
      meanSquaredError (copyLaw P h) (copyArmRatio P false h) ((∑ j, P.y0 j) / (populationSize P : ℝ))) := hb
    _ ≤ 2 * (copyArmRatioMSEConstant P true / h + copyArmRatioMSEConstant P false / h) := by linarith
    _ = _ := by ring

/-- The four weak-law limits and the final Slutsky conclusion of equation (9),
p. 46 (T17(b)). This is the exact independent Brewer replication sequence,
with the original ATE constant across copies. -/
theorem growing_clusters_consistent (P : ClusterPopulation) :
    DesignConsistent (copyLaw P) (copyAverage P true P.y1)
      (fun _ => (P.mt : ℝ) / P.M * ∑ j, P.y1 j) ∧
    DesignConsistent (copyLaw P) (copyAverage P false P.y0)
      (fun _ => (controlCount P : ℝ) / P.M * ∑ j, P.y0 j) ∧
    DesignConsistent (copyLaw P) (copyAverage P true (fun j => (P.n j : ℝ)))
      (fun _ => (P.mt : ℝ) / P.M * populationSize P) ∧
    DesignConsistent (copyLaw P) (copyAverage P false (fun j => (P.n j : ℝ)))
      (fun _ => (controlCount P : ℝ) / P.M * populationSize P) ∧
    DesignConsistent (copyLaw P) (copiedDifferenceInMeans P)
      (fun _ => averageTreatmentEffect P) := by
  refine ⟨copy_average_consistent P true P.y1, copy_average_consistent P false P.y0, ?_, ?_, ?_⟩
  · simpa [populationSize, Nat.cast_sum] using copy_average_consistent P true (fun j => (P.n j : ℝ))
  · simpa [populationSize, Nat.cast_sum] using copy_average_consistent P false (fun j => (P.n j : ℝ))
  · apply mse_rate_consistent _ _ _
      (2 * copyArmRatioMSEConstant P true + 2 * copyArmRatioMSEConstant P false)
    intro h hh
    exact copied_difference_mse_bound P h hh

/-- The algebraic right-hand identity of equation (9), p. 46, with all
nonzero denominators supplied by the standing assumptions (T17 finite lemma). -/
theorem limit_ratio_identity (P : ClusterPopulation) :
    ((∑ j, P.y1 j) * ((P.mt : ℝ) / P.M)) /
        ((populationSize P : ℝ) * ((P.mt : ℝ) / P.M)) -
    ((∑ j, P.y0 j) * ((controlCount P : ℝ) / P.M)) /
        ((populationSize P : ℝ) * ((controlCount P : ℝ) / P.M)) = averageTreatmentEffect P := by
  have hM : (P.M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt))
  have ht : (P.mt : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt P.mt_pos)
  have hc : (controlCount P : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt))
  have hN : (populationSize P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (populationSize_pos P))
  unfold averageTreatmentEffect
  field_simp
  <;> ring

/-- Figure 1B and equation (10), p. 47: multiply every size and potential
total by the positive integer h, while M and m_t stay fixed. This represents
copying each individual h times within its own cluster. -/
abbrev replicateWithin (P : ClusterPopulation) (h : ℕ) (hh : 0 < h) : ClusterPopulation :=
  { P with
    n := fun j => h * P.n j
    n_pos := fun j => Nat.mul_pos hh (P.n_pos j)
    y0 := fun j => (h : ℝ) * P.y0 j
    y1 := fun j => (h : ℝ) * P.y1 j }

/-- The population size in Figure 1B is N_h = hN (T17 finite lemma). -/
theorem replicated_size (P : ClusterPopulation) (h : ℕ) (hh : 0 < h) :
    populationSize (replicateWithin P h hh) = h * populationSize P := by
  simp [populationSize, replicateWithin, Finset.mul_sum]
  all_goals rfl


/-- Within-cluster replication multiplies both potential differenced totals
by h, so the single fixed k has the same scale, pp. 47 and 54. -/
theorem replicated_raj_potential (P : ClusterPopulation) (h : ℕ) (hh : 0 < h)
    (a : Bool) (k : ℝ) (j : Fin P.M) :
    rajPotential (replicateWithin P h hh) a k j = (h : ℝ) * rajPotential P a k j := by
  cases a <;>
    simp [rajPotential, differenced, replicateWithin, clusterMean,
      Nat.cast_mul, ← Finset.mul_sum] <;> ring

/-- Within-cluster replication multiplies both estimated Des Raj potential
totals by h, pp. 47 and 54. -/
theorem replicated_raj_total (P : ClusterPopulation) (h : ℕ) (hh : 0 < h)
    (a : Bool) (k : ℝ) (s : Finset (Fin P.M)) :
    rajTotal (replicateWithin P h hh) a k s = (h : ℝ) * rajTotal P a k s := by
  unfold rajTotal armSum
  simp_rw [replicated_raj_potential]
  simp [replicateWithin, controlCount, ← Finset.mul_sum]
  ring

/-- The replication leaves the assignment law itself unchanged, Figure 1B,
p. 46 and equation (10), p. 47. -/
theorem replicated_law (P : ClusterPopulation) (h : ℕ) (hh : 0 < h) :
    clusterLaw (replicateWithin P h hh) = clusterLaw P := by
  rfl
/-- Equation (10), p. 47, plus the corresponding ATE, HT and fixed-k Des Raj
identities: all ratios cancel h for every assignment in the fixed-M replication
sequence (T17(c) and T1(v)). -/
theorem within_replication_invariant (P : ClusterPopulation) (h : ℕ) (hh : 0 < h)
    (s : Finset (Fin P.M)) (k : ℝ) :
    averageTreatmentEffect (replicateWithin P h hh) = averageTreatmentEffect P ∧
    differenceInMeans (replicateWithin P h hh) s = differenceInMeans P s ∧
    horvitzThompson (replicateWithin P h hh) s = horvitzThompson P s ∧
    desRaj (replicateWithin P h hh) k s = desRaj P k s := by
  have hr : (h : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
  constructor
  · unfold averageTreatmentEffect
    rw [replicated_size]
    simp [replicateWithin, Nat.cast_mul, ← Finset.mul_sum, ← mul_sub,
      mul_div_mul_left _ _ hr]
  constructor
  · simp [differenceInMeans, armSize, armSum, replicateWithin, Nat.cast_mul,
      ← Finset.mul_sum, mul_div_mul_left _ _ hr]
  constructor
  · unfold horvitzThompson
    rw [replicated_size]
    simp [htTotal, controlCount, armSum, replicateWithin, Nat.cast_mul, ← Finset.mul_sum]
    field_simp
    <;> ring
  · unfold desRaj
    rw [replicated_raj_total, replicated_raj_total, replicated_size]
    simp [Nat.cast_mul, ← mul_sub, mul_div_mul_left _ _ hr]


/-- For a fixed finite randomization law and fixed population, a nonzero bias
precludes convergence in probability to the ATE along the constant sequence.
This makes the fixed-M conclusion after equation (10), p. 47, precise (T17). -/
theorem constant_design_biased_inconsistent {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ)
    (d : ℝ) (hb : designBias L T d ≠ 0) :
    ¬ DesignConsistent (fun _ : ℕ => L) (fun _ : ℕ => T) (fun _ : ℕ => d) := by
  classical
  intro hc
  have heprob : ∀ ε : ℝ, 0 < ε → errorProbability L T d ε = 0 := by
    intro ε hε
    exact tendsto_nhds_unique tendsto_const_nhds (hc ε hε)
  have he : expectation L T = d := by
    rw [← expectation_const L d]
    unfold expectation
    apply Finset.sum_congr rfl
    intro ω hω
    change L.weight ω * T ω = L.weight ω * d
    by_cases hw : L.weight ω = 0
    · simp [hw]
    · have hwp : 0 < L.weight ω := lt_of_le_of_ne (L.nonneg ω hω) (Ne.symm hw)
      have hTd : T ω = d := by
        by_contra hne
        have he : 0 < |T ω - d| := abs_pos.mpr (sub_ne_zero.mpr hne)
        have hε : 0 < |T ω - d| / 2 := by linarith
        have hlarge : |T ω - d| / 2 < |T ω - d| := by linarith
        have hterm : L.weight ω ≤ errorProbability L T d (|T ω - d| / 2) := by
          unfold errorProbability
          have hh := Finset.single_le_sum (f := fun a =>
            if |T ω - d| / 2 < |T a - d| then L.weight a else 0)
            (fun a ha => by split_ifs; exact L.nonneg a ha; exact le_rfl) hω
          simpa only [if_pos hlarge] using hh
        rw [heprob _ hε] at hterm
        linarith
      rw [hTd]
  apply hb
  unfold designBias
  rw [he]
  ring

/-- Equation (10) implies identical expectation and bias for each h in the
fixed-M sequence, and nonzero original bias precludes consistency (T17(c)). -/
theorem fixed_clusters_persistent_bias (P : ClusterPopulation)
    (hbias : designBias (clusterLaw P) (differenceInMeans P) (averageTreatmentEffect P) ≠ 0) :
    (∀ h (hh : 0 < h),
      designBias (clusterLaw (replicateWithin P h hh))
        (differenceInMeans (replicateWithin P h hh))
        (averageTreatmentEffect (replicateWithin P h hh)) =
        designBias (clusterLaw P) (differenceInMeans P) (averageTreatmentEffect P)) ∧
    ¬ DesignConsistent (fun _ : ℕ => clusterLaw P)
        (fun _ : ℕ => differenceInMeans P) (fun _ : ℕ => averageTreatmentEffect P) := by
  constructor
  · intro h hh
    rw [replicated_law]
    have hi := within_replication_invariant P h hh
    have hd : differenceInMeans (replicateWithin P h hh) = differenceInMeans P := by
      funext s; exact (hi s 0).2.1
    rw [hd, (hi ∅ 0).1]
  · exact constant_design_biased_inconsistent (clusterLaw P) (differenceInMeans P)
      (averageTreatmentEffect P) hbias

/-- The finite index set for three clusters, used only to evaluate the exact
counterexamples without changing their assignment distribution. -/
theorem univ_three : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide

/-- P020-E001's concrete admissible population for T1: M=3, m_t=1,
n=(1,2,4), Y^T_0=(0,1,1), Y^T_1=(0,0,0), N=7. It realizes the
individual outcomes (0), (1,0), (1,0,0,0), with all treatment outcomes zero.
P020-E001, correction of pp. 40,42; equations (6),(13),(20)-(21). -/
abbrev efficiencyPopulation : ClusterPopulation where
  M := 3
  mt := 1
  mt_pos := by decide
  mt_lt := by decide
  n := ![1, 2, 4]
  n_pos := by intro j; fin_cases j <;> norm_num
  y0 := ![0, 1, 1]
  y1 := ![0, 0, 0]

/-- The three equally likely assignments of the P020-E001 instance exhaust the
complete cluster randomization distribution (T1). -/
theorem efficiency_assignments : assignments efficiencyPopulation =
    ({({0} : Finset (Fin 3)), {1}, {2}} : Finset (Finset (Fin 3))) := by decide

/-- The stored totals of P020-E001 are the sums of the exact binary individual
potential outcomes in T1, with the first control individual equal to one
in clusters 2 and 3 and every other outcome zero. -/
theorem efficiency_individual_realization (j : Fin 3) :
    clusterTotal (fun i : Fin (efficiencyPopulation.n j) =>
      if j = 0 then (0 : ℝ) else if i.val = 0 then 1 else 0) = efficiencyPopulation.y0 j ∧
    clusterTotal (fun _ : Fin (efficiencyPopulation.n j) => (0 : ℝ)) = efficiencyPopulation.y1 j := by
  fin_cases j <;> norm_num [efficiencyPopulation, clusterTotal, Fin.sum_univ_succ] <;> decide

/-- Exact assignmentwise values, ATE, bias and MSE in P020-E001 (T1(i)-(ii)).
The three assignments are listed in treated-cluster order. -/
theorem efficiency_exact_values :
    populationSize efficiencyPopulation = 7 ∧
    averageTreatmentEffect efficiencyPopulation = -(2 : ℝ) / 7 ∧
    differenceInMeans efficiencyPopulation {0} = -(1 : ℝ) / 3 ∧
    differenceInMeans efficiencyPopulation {1} = -(1 : ℝ) / 5 ∧
    differenceInMeans efficiencyPopulation {2} = -(1 : ℝ) / 3 ∧
    horvitzThompson efficiencyPopulation {0} = -(3 : ℝ) / 7 ∧
    horvitzThompson efficiencyPopulation {1} = -(3 : ℝ) / 14 ∧
    horvitzThompson efficiencyPopulation {2} = -(3 : ℝ) / 14 ∧
    expectation (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation) = -(13 : ℝ) / 45 ∧
    designBias (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation)
      (averageTreatmentEffect efficiencyPopulation) = -(1 : ℝ) / 315 ∧
    meanSquaredError (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation)
      (averageTreatmentEffect efficiencyPopulation) = (131 : ℝ) / 33075 ∧
    expectation (clusterLaw efficiencyPopulation) (horvitzThompson efficiencyPopulation) =
      averageTreatmentEffect efficiencyPopulation ∧
    meanSquaredError (clusterLaw efficiencyPopulation) (horvitzThompson efficiencyPopulation)
      (averageTreatmentEffect efficiencyPopulation) = (1 : ℝ) / 98 := by
  norm_num [expectation, clusterLaw, uniformLaw, efficiency_assignments,
    designBias, meanSquaredError, averageTreatmentEffect, differenceInMeans,
    horvitzThompson, htTotal, armSize, armSum, controls, controlCount,
    populationSize, efficiencyPopulation, Fin.sum_univ_succ, univ_three]

/-- P020-E001's exact fixed-k Des Raj assignment values, unbiased expectation,
and completed-square MSE with minimum attained iff k=2/21 (T1(iii)). -/
theorem efficiency_raj_mse (k : ℝ) :
    desRaj efficiencyPopulation k {0} = -3 / 7 + 6 / 7 * k ∧
    desRaj efficiencyPopulation k {1} = -3 / 14 + 3 / 14 * k ∧
    desRaj efficiencyPopulation k {2} = -3 / 14 - 15 / 14 * k ∧
    expectation (clusterLaw efficiencyPopulation) (desRaj efficiencyPopulation k) =
      averageTreatmentEffect efficiencyPopulation ∧
    meanSquaredError (clusterLaw efficiencyPopulation) (desRaj efficiencyPopulation k)
      (averageTreatmentEffect efficiencyPopulation) = 1 / 98 - 6 / 49 * k + 9 / 14 * k^2 ∧
    meanSquaredError (clusterLaw efficiencyPopulation) (desRaj efficiencyPopulation k)
      (averageTreatmentEffect efficiencyPopulation) = 3 / 686 + 9 / 14 * (k - 2 / 21)^2 ∧
    (meanSquaredError (clusterLaw efficiencyPopulation) (desRaj efficiencyPopulation k)
      (averageTreatmentEffect efficiencyPopulation) = 3 / 686 ↔ k = 2 / 21) := by
  norm_num [expectation, clusterLaw, uniformLaw, efficiency_assignments,
    meanSquaredError, averageTreatmentEffect, desRaj, rajTotal, rajPotential,
    differenced, clusterMean, armSum, controls, controlCount,
    populationSize, efficiencyPopulation, Fin.sum_univ_succ, univ_three]
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
  · ring
  constructor
  · intro he; nlinarith [sq_nonneg (k - 2 / 21)]
  · intro he; rw [he]; norm_num

/-- P020-E001's population size moments and optimal coefficient agree with
Section 5.3: σ²(n)=14/9, σ(n,Y^T_0)=4/9, σ(n,Y^T_1)=0 and k*=2/21 (T1(iii)). -/
theorem efficiency_optimal_coefficient :
    clusterVariance (fun j => (efficiencyPopulation.n j : ℝ)) = 14 / 9 ∧
    clusterCovariance (fun j => (efficiencyPopulation.n j : ℝ)) efficiencyPopulation.y0 = 4 / 9 ∧
    clusterCovariance (fun j => (efficiencyPopulation.n j : ℝ)) efficiencyPopulation.y1 = 0 ∧
    optimalCoefficient efficiencyPopulation = 2 / 21 := by
  norm_num [clusterVariance, clusterCovariance, clusterMean, optimalCoefficient,
    armOptimalCoefficient, controlCount, efficiencyPopulation, Fin.sum_univ_succ]

/-- P020-E001: biased difference-in-means has strictly smaller MSE than the
best fixed-k Des Raj estimator and HT; it beats every fixed real k (T1(iv)). -/
theorem efficiency_mse_counterexample (k : ℝ) :
    (131 : ℝ) / 33075 < 3 / 686 ∧ (3 : ℝ) / 686 < 1 / 98 ∧
    meanSquaredError (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation)
      (averageTreatmentEffect efficiencyPopulation) <
    meanSquaredError (clusterLaw efficiencyPopulation) (desRaj efficiencyPopulation k)
      (averageTreatmentEffect efficiencyPopulation) := by
  have hDM := efficiency_exact_values
  have hR := efficiency_raj_mse k
  have heDM : meanSquaredError (clusterLaw efficiencyPopulation)
      (differenceInMeans efficiencyPopulation) (averageTreatmentEffect efficiencyPopulation) =
      (131 : ℝ) / 33075 := hDM.2.2.2.2.2.2.2.2.2.2.1
  have heR := hR.2.2.2.2.2.1
  rw [heDM, heR]
  refine ⟨by norm_num, by norm_num, ?_⟩
  nlinarith [sq_nonneg (k - 2 / 21)]

/-- P020-E001's probability of an absolute error greater than 1/25 is exactly
one, providing an explicit inconsistency witness (T1(v)). -/
theorem efficiency_error_probability :
    errorProbability (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation)
      (averageTreatmentEffect efficiencyPopulation) (1 / 25) = 1 := by
  norm_num [errorProbability, clusterLaw, uniformLaw, efficiency_assignments,
    averageTreatmentEffect, differenceInMeans, armSize, armSum, controls,
    populationSize, efficiencyPopulation, Fin.sum_univ_succ, univ_three]

/-- Full all-h P020-E001 refutation of eventual relative-MSE inferiority under
persistent bias (T1(v)). Copying each individual h times keeps every estimator,
bias, MSE and the probability-one error witness unchanged. k may depend on h.
The sample size N_h = 7h grows without bound. -/
theorem efficiency_all_replications_counterexample (h : ℕ) (hh : 0 < h) (k : ℝ) :
    populationSize (replicateWithin efficiencyPopulation h hh) = 7 * h ∧
    averageTreatmentEffect (replicateWithin efficiencyPopulation h hh) = -(2 : ℝ) / 7 ∧
    (∀ s, differenceInMeans (replicateWithin efficiencyPopulation h hh) s =
      differenceInMeans efficiencyPopulation s ∧
      horvitzThompson (replicateWithin efficiencyPopulation h hh) s = horvitzThompson efficiencyPopulation s ∧
      desRaj (replicateWithin efficiencyPopulation h hh) k s = desRaj efficiencyPopulation k s) ∧
    designBias (clusterLaw (replicateWithin efficiencyPopulation h hh))
      (differenceInMeans (replicateWithin efficiencyPopulation h hh))
      (averageTreatmentEffect (replicateWithin efficiencyPopulation h hh)) = -(1 : ℝ) / 315 ∧
    errorProbability (clusterLaw (replicateWithin efficiencyPopulation h hh))
      (differenceInMeans (replicateWithin efficiencyPopulation h hh))
      (averageTreatmentEffect (replicateWithin efficiencyPopulation h hh)) (1 / 25) = 1 ∧
    meanSquaredError (clusterLaw (replicateWithin efficiencyPopulation h hh))
      (differenceInMeans (replicateWithin efficiencyPopulation h hh))
      (averageTreatmentEffect (replicateWithin efficiencyPopulation h hh)) <
    meanSquaredError (clusterLaw (replicateWithin efficiencyPopulation h hh))
      (desRaj (replicateWithin efficiencyPopulation h hh) k)
      (averageTreatmentEffect (replicateWithin efficiencyPopulation h hh)) := by
  have hInv := within_replication_invariant efficiencyPopulation h hh
  have hATE : averageTreatmentEffect (replicateWithin efficiencyPopulation h hh) =
      averageTreatmentEffect efficiencyPopulation := (hInv ∅ k).1
  have hDM : differenceInMeans (replicateWithin efficiencyPopulation h hh) =
      differenceInMeans efficiencyPopulation := by funext s; exact (hInv s k).2.1
  have hR : desRaj (replicateWithin efficiencyPopulation h hh) k =
      desRaj efficiencyPopulation k := by funext s; exact (hInv s k).2.2.2
  simp only [replicated_size, hATE, hDM, hR, replicated_law]
  refine ⟨?_, efficiency_exact_values.2.1, ?_, ?_, efficiency_error_probability,
    (efficiency_mse_counterexample k).2.2⟩
  · rw [efficiency_exact_values.1]; omega
  · intro s
    exact ⟨trivial, (hInv s k).2.2.1, trivial⟩
  · exact efficiency_exact_values.2.2.2.2.2.2.2.2.2.1

/-- The P020-E001 replication has arbitrarily large sample size N_h = 7h,
expressed as divergence of its exact size formula to infinity (T1(v)). -/
theorem efficiency_sample_size_grows : Tendsto (fun h : ℕ => 7 * h) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [Filter.eventually_ge_atTop b] with h hh
  omega

/-- P020-E001's fixed-M sequence is inconsistent despite uniformly beating both
specified unbiased comparator families; its bias is the same nonzero constant
-1/315 at every h (T1(v)). -/
theorem efficiency_inconsistent :
    ¬ DesignConsistent (fun _ : ℕ => clusterLaw efficiencyPopulation)
      (fun _ : ℕ => differenceInMeans efficiencyPopulation)
      (fun _ : ℕ => averageTreatmentEffect efficiencyPopulation) := by
  apply constant_design_biased_inconsistent
  rw [efficiency_exact_values.2.2.2.2.2.2.2.2.2.1]
  norm_num

/-- P020-E005's concrete admissible population for equation (31): M=3, m_t=1,
n=(1,2,3), Y^T_0=(0,0,0), Y^T_1=(0,0,3), N=6 (T6). It can be realized
with control individual outcomes zero and every treatment individual in
cluster 3 equal to one, every other treatment individual equal to zero. -/
abbrev slopePopulation : ClusterPopulation where
  M := 3
  mt := 1
  mt_pos := by decide
  mt_lt := by decide
  n := ![1, 2, 3]
  n_pos := by intro j; fin_cases j <;> norm_num
  y0 := ![0, 0, 0]
  y1 := ![0, 0, 3]

/-- All three assignments of the P020-E005 instance are equally likely (T6). -/
theorem slope_assignments : assignments slopePopulation =
    ({({0} : Finset (Fin 3)), {1}, {2}} : Finset (Finset (Fin 3))) := by decide

/-- P020-E005: k-hat is the OLS slope of observed totals on size, with intercept.
It equals (0,0,3/2); estimates equal (0,0,3/8), and E[Δ_R1]=1/8≠1/2.
Both covariances in the corrected (31) yield bias -3/8, whereas the printed
repeated-control covariance expression is identically zero (T6). -/
theorem estimated_slope_counterexample :
    averageTreatmentEffect slopePopulation = (1 : ℝ) / 2 ∧
    observedSlope slopePopulation {0} = 0 ∧
    observedSlope slopePopulation {1} = 0 ∧
    observedSlope slopePopulation {2} = 3 / 2 ∧
    desRaj slopePopulation (observedSlope slopePopulation {0}) {0} = 0 ∧
    desRaj slopePopulation (observedSlope slopePopulation {1}) {1} = 0 ∧
    desRaj slopePopulation (observedSlope slopePopulation {2}) {2} = 3 / 8 ∧
    expectation (clusterLaw slopePopulation)
      (fun s => desRaj slopePopulation (observedSlope slopePopulation s) s) = 1 / 8 ∧
    expectation (clusterLaw slopePopulation)
      (fun s => desRaj slopePopulation (observedSlope slopePopulation s) s) ≠
      averageTreatmentEffect slopePopulation ∧
    designBias (clusterLaw slopePopulation)
      (fun s => desRaj slopePopulation (observedSlope slopePopulation s) s)
      (averageTreatmentEffect slopePopulation) = -3 / 8 ∧
    designCovariance (clusterLaw slopePopulation) (observedSlope slopePopulation)
      (armMeanSize slopePopulation true) = 1 / 2 ∧
    designCovariance (clusterLaw slopePopulation) (observedSlope slopePopulation)
      (armMeanSize slopePopulation false) = -1 / 4 := by
  norm_num [expectation, clusterLaw, uniformLaw, slope_assignments,
    averageTreatmentEffect, observedSlope, observedTotal, desRaj, rajTotal, rajPotential,
    designCovariance, designBias, clusterCovariance, clusterVariance, clusterMean,
    differenced, armMeanSize, armSize, armSum, controls, controlCount,
    populationSize, slopePopulation, Fin.sum_univ_succ, univ_three]

/-- P020-E010(e)'s concrete population: M=2, m_t=m_c=1, n=(1,2),
Y^T_0=(0,0), Y^T_1=(1,2), N=3; k=b_0=0,b_1=1 (T9(a)). -/
abbrev subscriptPopulation : ClusterPopulation where
  M := 2
  mt := 1
  mt_pos := by decide
  mt_lt := by decide
  n := ![1, 2]
  n_pos := by intro j; fin_cases j <;> norm_num
  y0 := ![0, 0]
  y1 := ![1, 2]

/-- In equation (25)'s misprinted second line, using treatment potentials
in the control sum gives -2/3 instead of the correct transformed Des Raj
estimate +2/3, for the admissible assignment J_1={1} (zero-based {0}) (T9(a)). -/
theorem control_subscript_counterexample :
    ({0} : Finset (Fin 2)) ∈ assignments subscriptPopulation ∧
    desRaj (affinePopulation subscriptPopulation 0 1) 0 {0} = (2 : ℝ) / 3 ∧
    (subscriptPopulation.M : ℝ) / populationSize subscriptPopulation *
      (armSum subscriptPopulation true (rajPotential subscriptPopulation true 0) {0} /
          subscriptPopulation.mt -
       armSum subscriptPopulation false (rajPotential subscriptPopulation true 0) {0} /
          controlCount subscriptPopulation) = -(2 : ℝ) / 3 ∧
    desRaj (affinePopulation subscriptPopulation 0 1) 0 {0} ≠
      (subscriptPopulation.M : ℝ) / populationSize subscriptPopulation *
        (armSum subscriptPopulation true (rajPotential subscriptPopulation true 0) {0} /
          subscriptPopulation.mt -
         armSum subscriptPopulation false (rajPotential subscriptPopulation true 0) {0} /
          controlCount subscriptPopulation) := by
  norm_num [assignments, Finset.mem_powersetCard, desRaj, affinePopulation,
    rajTotal, rajPotential, differenced, clusterMean, armSum, controls, controlCount,
    populationSize, subscriptPopulation, Fin.sum_univ_succ, Finset.univ_fin2]

/-- P020-E010(i)'s bracket error in equation (35): for M=2, k=0 and both
potential-total vectors (0,2), correct covariance is 1. The expression with
only the first factor inside E is -1 at cluster 1 (zero-based 0), and +1
at cluster 2 (zero-based 1), so it is not the covariance (T9(b)). -/
theorem expectation_bracket_counterexample :
    clusterCovariance (![0, 2] : Fin 2 → ℝ) ![0, 2] = 1 ∧
    clusterMean (![0, 2] : Fin 2 → ℝ) * (![0, 2] : Fin 2 → ℝ) 0 -
      clusterMean (![0, 2] : Fin 2 → ℝ) * clusterMean (![0, 2] : Fin 2 → ℝ) = -1 ∧
    clusterMean (![0, 2] : Fin 2 → ℝ) * (![0, 2] : Fin 2 → ℝ) 1 -
      clusterMean (![0, 2] : Fin 2 → ℝ) * clusterMean (![0, 2] : Fin 2 → ℝ) = 1 ∧
    clusterCovariance (![0, 2] : Fin 2 → ℝ) ![0, 2] ≠
      clusterMean (![0, 2] : Fin 2 → ℝ) * (![0, 2] : Fin 2 → ℝ) 0 -
        clusterMean (![0, 2] : Fin 2 → ℝ) * clusterMean (![0, 2] : Fin 2 → ℝ) := by
  norm_num [clusterCovariance, clusterMean, Fin.sum_univ_succ]

/-- The third line of corrected equation (25), p. 56: the common affine
constant cancels, leaving the scaled treatment sum and the scaled control
sum, and this equals b_1 times the original estimate (T7). -/
theorem corrected_affine_chain (P : ClusterPopulation) (b0 b1 k : ℝ)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P) :
    desRaj (affinePopulation P b0 b1) (b0 + b1 * k) s =
      (P.M : ℝ) / populationSize P *
        (b1 * armSum P true (rajPotential P true k) s / P.mt -
         b1 * armSum P false (rajPotential P false k) s / controlCount P) ∧
    (P.M : ℝ) / populationSize P *
        (b1 * armSum P true (rajPotential P true k) s / P.mt -
         b1 * armSum P false (rajPotential P false k) s / controlCount P) =
      b1 * desRaj P k s := by
  have hi := (des_raj_affine_invariant P b0 b1 k s hs).2
  have he : (P.M : ℝ) / populationSize P *
        (b1 * armSum P true (rajPotential P true k) s / P.mt -
         b1 * armSum P false (rajPotential P false k) s / controlCount P) =
      b1 * desRaj P k s := by
    simp [desRaj, rajTotal]
    ring
  exact ⟨hi.trans he.symm, he⟩

/-- An admissible M=2,m_t=m_c=1 population with counts (1,2) and both
potential-total vectors (0,2), giving the bracket counterexample in equation
(35), p. 72 (T9(b)). -/
abbrev bracketPopulation : ClusterPopulation :=
  { subscriptPopulation with y0 := ![0, 2], y1 := ![0, 2] }

/-- The bracket counterexample has a valid assignment, actual covariance 1,
and the printed expectation-scope expression -1 at cluster 1 (T9(b)). -/
theorem bracket_admissible_counterexample :
    ({0} : Finset (Fin 2)) ∈ assignments bracketPopulation ∧
    clusterCovariance bracketPopulation.y0 bracketPopulation.y1 = 1 ∧
    clusterMean bracketPopulation.y0 * bracketPopulation.y1 0 -
      clusterMean bracketPopulation.y0 * clusterMean bracketPopulation.y1 = -1 ∧
    clusterCovariance bracketPopulation.y0 bracketPopulation.y1 ≠
      clusterMean bracketPopulation.y0 * bracketPopulation.y1 0 -
        clusterMean bracketPopulation.y0 * clusterMean bracketPopulation.y1 := by
  norm_num [bracketPopulation, subscriptPopulation, assignments, Finset.mem_powersetCard,
    clusterCovariance, clusterMean, Fin.sum_univ_succ]

/-- The moment expression cσ²(U^T_0)+tσ²(U^T_1)+2σ(U^T_0,U^T_1) in
Appendix C equation (32), p. 71; c=(M-m_c)/m_c and t=(M-m_t)/m_t.
This is a finite-moment objective. Its identification with scaled true design
variance is not assumed by this definition. -/
def rajMomentObjective (P : ClusterPopulation) (k : ℝ) : ℝ :=
  (((P.M : ℝ) - controlCount P) / controlCount P) * clusterVariance (rajPotential P false k) +
  (((P.M : ℝ) - P.mt) / P.mt) * clusterVariance (rajPotential P true k) +
  2 * clusterCovariance (rajPotential P false k) (rajPotential P true k)

/-- At k=0 the Des Raj differenced feature is the original feature,
p. 56: the HT estimator is a special case of Des Raj. -/
theorem differenced_zero {M : ℕ} (v size : Fin M → ℝ) : differenced v size 0 = v := by
  funext j
  simp [differenced]

/-- The exact quadratic identity in Appendix C, pp. 72-73 (T14 finite lemma):
the moment objective changes relative to k=0 by (c+t+2)σ²(n)k(k-2k*).
Positive size variance is explicit. The actual design-variance
identification is stated in optimal_raj_variance. -/
theorem raj_moment_quadratic_identity (P : ClusterPopulation) (k : ℝ)
    (hsize : 0 < clusterVariance (fun j => (P.n j : ℝ))) :
    rajMomentObjective P k - rajMomentObjective P 0 =
      ((((P.M : ℝ) - controlCount P) / controlCount P) +
       (((P.M : ℝ) - P.mt) / P.mt) + 2) *
      clusterVariance (fun j => (P.n j : ℝ)) * k * (k - 2 * optimalCoefficient P) := by
  have hM : 0 < P.M := lt_trans P.mt_pos P.mt_lt
  have hs : clusterVariance (fun j => (P.n j : ℝ)) ≠ 0 := ne_of_gt hsize
  have ht : (P.mt : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt P.mt_pos)
  have hc : (controlCount P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt))
  have hMr : (P.M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hcounts : (controlCount P : ℝ) + P.mt = P.M := by
    simp [controlCount, Nat.cast_sub (le_of_lt P.mt_lt)]
  unfold rajMomentObjective rajPotential
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [differenced_variance hM, differenced_variance hM,
    (differenced_covariance hM P.y0 P.y1 (fun j => (P.n j : ℝ)) k).2]
  simp only [differenced_zero]
  unfold optimalCoefficient armOptimalCoefficient
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [clusterCovariance_comm (fun j => (P.n j : ℝ)) P.y0,
    clusterCovariance_comm (fun j => (P.n j : ℝ)) P.y1]
  rw [← hcounts]
  field_simp
  <;> ring

/-- The coefficient of k² in the true Des Raj variance from
Appendix C equations (32)-(35), pp. 71-73; finite moments use divisor M. -/
def rajVarianceCurvature (P : ClusterPopulation) : ℝ :=
  (P.M : ℝ)^2 / ((populationSize P : ℝ)^2 * ((P.M : ℝ) - 1)) *
    ((((P.M : ℝ) - controlCount P) / controlCount P) +
      (((P.M : ℝ) - P.mt) / P.mt) + 2) *
    clusterVariance (fun j => (P.n j : ℝ))

/-- The curvature in Appendix C is positive when cluster sizes have positive
finite-population variance, the nondegeneracy hypothesis of T14. -/
theorem raj_variance_curvature_pos (P : ClusterPopulation)
    (hsize : 0 < clusterVariance (fun j => (P.n j : ℝ))) :
    0 < rajVarianceCurvature P := by
  have hM : (0 : ℝ) < P.M := by exact_mod_cast lt_trans P.mt_pos P.mt_lt
  have ht : (0 : ℝ) < P.mt := by exact_mod_cast P.mt_pos
  have hc : (0 : ℝ) < controlCount P := by exact_mod_cast Nat.sub_pos_of_lt P.mt_lt
  have hN : (0 : ℝ) < populationSize P := by exact_mod_cast populationSize_pos P
  have hMt : (0 : ℝ) < (P.M : ℝ) - P.mt := by
    have hh : (P.mt : ℝ) < P.M := by exact_mod_cast P.mt_lt
    linarith
  have hMc : (P.M : ℝ) - controlCount P = P.mt := by
    simp [controlCount, Nat.cast_sub (le_of_lt P.mt_lt)]
  have hM1 : (0 : ℝ) < (P.M : ℝ) - 1 := by
    have hh : (1 : ℝ) < P.M := by
      exact_mod_cast lt_of_le_of_lt (Nat.succ_le_of_lt P.mt_pos) P.mt_lt
    linarith
  unfold rajVarianceCurvature
  rw [hMc]
  positivity

/-- Equation (32), Appendix C, p. 71: the actual Des Raj design variance
is M²/[N²(M-1)] times the finite-moment objective. -/
theorem raj_design_variance_moment (P : ClusterPopulation) (k : ℝ) :
    designVariance (clusterLaw P) (desRaj P k) =
      (P.M : ℝ)^2 / ((populationSize P : ℝ)^2 * ((P.M : ℝ) - 1)) *
        rajMomentObjective P k := by
  let Q : ClusterPopulation := {P with y0 := rajPotential P false k, y1 := rajPotential P true k}
  have hh := ht_design_variance_formula Q
  change designVariance (clusterLaw P) (desRaj P k) = htVarianceFormula Q at hh
  rw [hh]
  unfold htVarianceFormula rajMomentObjective
  change (P.M : ℝ)^2 / (populationSize P : ℝ)^2 *
    ((P.M : ℝ) / ((P.M : ℝ) - 1) *
      (clusterVariance (rajPotential P false k) / controlCount P +
       clusterVariance (rajPotential P true k) / P.mt) +
     1 / ((P.M : ℝ) - 1) *
      (2 * clusterCovariance (rajPotential P false k) (rajPotential P true k) -
       clusterVariance (rajPotential P false k) - clusterVariance (rajPotential P true k))) = _
  have ht : (P.mt : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt P.mt_pos
  have hc : (controlCount P : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt P.mt_lt)
  field_simp [ht, hc]
  <;> ring

/-- The exact variance difference in Appendix C, pp. 72-73, is a positive
quadratic coefficient times k(k-2k_optim*), assuming positive size variance. -/
theorem raj_design_variance_gap (P : ClusterPopulation) (k : ℝ)
    (hsize : 0 < clusterVariance (fun j => (P.n j : ℝ))) :
    designVariance (clusterLaw P) (desRaj P k) -
      designVariance (clusterLaw P) (horvitzThompson P) =
      rajVarianceCurvature P * k * (k - 2 * optimalCoefficient P) := by
  have hzero : desRaj P 0 = horvitzThompson P := by
    funext s
    simp [desRaj, rajTotal, horvitzThompson, htTotal, rajPotential, differenced, armSum]
  rw [← hzero, raj_design_variance_moment, raj_design_variance_moment, ← mul_sub,
    raj_moment_quadratic_identity P k hsize]
  unfold rajVarianceCurvature
  ring

/-- Completing the square in true design variance, Appendix C, pp. 72-73. -/
theorem raj_design_variance_completed_square (P : ClusterPopulation) (k : ℝ)
    (hsize : 0 < clusterVariance (fun j => (P.n j : ℝ))) :
    designVariance (clusterLaw P) (desRaj P k) =
      designVariance (clusterLaw P) (desRaj P (optimalCoefficient P)) +
        rajVarianceCurvature P * (k - optimalCoefficient P)^2 := by
  have hk := raj_design_variance_gap P k hsize
  have hs := raj_design_variance_gap P (optimalCoefficient P) hsize
  linear_combination hk - hs

/-- Appendix C, equation (32) to the final inequality, pp. 71-73 (T14(b)-(c)).
With positive size variance, k_optim* uniquely minimizes true Des Raj variance;
strict improvement over HT occurs iff k² < 2 k k_optim*, and equality occurs
at precisely k=0 or k=2 k_optim*. -/
theorem optimal_raj_variance (P : ClusterPopulation)
    (hsize : 0 < clusterVariance (fun j => (P.n j : ℝ))) (k : ℝ) :
    designVariance (clusterLaw P) (desRaj P (optimalCoefficient P)) ≤
      designVariance (clusterLaw P) (desRaj P k) ∧
    (designVariance (clusterLaw P) (desRaj P (optimalCoefficient P)) =
      designVariance (clusterLaw P) (desRaj P k) ↔ k = optimalCoefficient P) ∧
    (designVariance (clusterLaw P) (desRaj P k) <
      designVariance (clusterLaw P) (horvitzThompson P) ↔ k^2 < 2 * k * optimalCoefficient P) ∧
    (designVariance (clusterLaw P) (desRaj P k) =
      designVariance (clusterLaw P) (horvitzThompson P) ↔ k = 0 ∨ k = 2 * optimalCoefficient P) := by
  have hC := raj_variance_curvature_pos P hsize
  have hcomp := raj_design_variance_completed_square P k hsize
  have hgap := raj_design_variance_gap P k hsize
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hn := mul_nonneg (le_of_lt hC) (sq_nonneg (k - optimalCoefficient P))
    linarith
  · constructor
    · intro he
      have hz : rajVarianceCurvature P * (k - optimalCoefficient P)^2 = 0 := by linarith
      have hs : (k - optimalCoefficient P)^2 = 0 :=
        (mul_eq_zero.mp hz).resolve_left (ne_of_gt hC)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    · intro he; rw [he]
  · constructor
    · intro he
      have hh : rajVarianceCurvature P * (k * (k - 2 * optimalCoefficient P)) < 0 := by
        nlinarith [hgap]
      have hn : k * (k - 2 * optimalCoefficient P) < 0 :=
        neg_of_mul_neg_right hh (le_of_lt hC)
      nlinarith
    · intro he
      have hn : k * (k - 2 * optimalCoefficient P) < 0 := by nlinarith
      have hh := mul_neg_of_pos_of_neg hC hn
      nlinarith [hgap]
  · constructor
    · intro he
      have hz : rajVarianceCurvature P * (k * (k - 2 * optimalCoefficient P)) = 0 := by
        nlinarith [hgap]
      have hk : k * (k - 2 * optimalCoefficient P) = 0 :=
        (mul_eq_zero.mp hz).resolve_left (ne_of_gt hC)
      exact (mul_eq_zero.mp hk).imp id sub_eq_zero.mp
    · rintro (hk | hk) <;> rw [hk] <;> rw [hk] at hgap <;> nlinarith [hgap]


end
end AronowAudit.P020

