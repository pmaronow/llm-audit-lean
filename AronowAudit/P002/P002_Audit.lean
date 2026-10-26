import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Algebra.Polynomial.Roots

/-! Finite-population randomization inference (P002).  All randomness is complete randomization.
`Real` division is used only for ordinary finite quantities.  Absolute studentized
statistics live in `ENNReal`, so nonzero/zero is infinity and zero/zero is zero.
-/
namespace AronowAudit.P002
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

/-- "potential outcome ... under ... treatment receipt" and "compliance decision"
(main pp. 3-4, Assumptions 1-2). Exclusion is encoded by the absence of an assignment
argument in `y`; monotonicity is a separate hypothesis. Units are indexed from zero. -/
structure Population (n : ℕ) where
  y : Fin n → Bool → ℝ
  d : Fin n → Bool → Bool
  n1 : ℕ

/-- "each unit ... covariate ... x_i ∈ R^k" (main p. 8). -/
structure CovPopulation (n k : ℕ) where
  pop : Population n
  x : Fin n → Fin k → ℝ

/-- Binary receipt as a real number (main p. 4). -/
def binary (b : Bool) : ℝ := if b then 1 else 0
/-- "C = {i : d_i(0)=0, d_i(1)=1}" (main p. 4, (1)). -/
def compliers {n} (P : Population n) : Finset (Fin n) :=
  Finset.univ.filter fun i => P.d i false = false ∧ P.d i true = true
/-- Assumption 2, monotonicity (main p. 4). -/
def MonotoneReceipt {n} (P : Population n) : Prop :=
  ∀ i, P.d i false = true → P.d i true = true
/-- "mu_q = (1/n) sum q_i" (Supplement p. 21, A.1). -/
def mean {n} (q : Fin n → ℝ) : ℝ := (∑ i, q i) / (n : ℝ)
/-- Mean on a finite group, including singleton compliers (main p. 7, Assumption 3). -/
def groupMean {n} (S : Finset (Fin n)) (q : Fin n → ℝ) : ℝ :=
  (∑ i ∈ S, q i) / (S.card : ℝ)
/-- "beta-bar = 1/|C| sum_C (y_i(1)-y_i(0))" (main p. 4, (2)). -/
def late {n} (P : Population n) : ℝ :=
  groupMean (compliers P) fun i => P.y i true - P.y i false
/-- "sigma_q^2 = 1/(n-1) sum (q_i-mu_q)^2" (Supplement p. 21, A.1). -/
def popVar {n} (q : Fin n → ℝ) : ℝ :=
  (∑ i, (q i - mean q) ^ 2) / ((n : ℝ) - 1)
/-- Population covariance with divisor n-1 (Supplement p. 21, A.1). -/
def popCov {n} (q t : Fin n → ℝ) : ℝ :=
  (∑ i, (q i - mean q) * (t i - mean t)) / ((n : ℝ) - 1)
/-- Complier covariance, defined to be zero for a singleton (main p. 7, Assumption 3(i)). -/
def groupCov {n} (S : Finset (Fin n)) (q t : Fin n → ℝ) : ℝ :=
  if 2 ≤ S.card then
    (∑ i ∈ S, (q i - groupMean S q) * (t i - groupMean S t)) / ((S.card : ℝ) - 1)
  else 0
/-- Complier variance with the main-text singleton convention (main p. 7). -/
def groupVar {n} (S : Finset (Fin n)) (q : Fin n → ℝ) : ℝ := groupCov S q q
/-- "w_i(a,beta)=y_i(d_i(a))-beta d_i(a)" (Supplement p. 31, (D.1)). -/
def w {n} (P : Population n) (a : Bool) (β : ℝ) (i : Fin n) : ℝ :=
  P.y i (P.d i a) - β * binary (P.d i a)
/-- Population-centred v_i(a,beta) (Supplement p. 22, (B.3)-(B.4)). -/
def v {n} (P : Population n) (a : Bool) (β : ℝ) (i : Fin n) : ℝ :=
  w P a β i - mean (w P a β)
/-- pi = n1/n, n0 = n-n1 (main p. 4). -/
def fraction {n} (P : Population n) : ℝ := (P.n1 : ℝ) / (n : ℝ)
/-- "n_0=n-n_1", main p. 5, Section 3.1. -/
def controlSize {n} (P : Population n) : ℝ := (n : ℝ) - (P.n1 : ℝ)
/-- Positive treatment and control arms, n≥2 (standing complete-randomization design). -/
def ValidDesign {n} (P : Population n) : Prop := 2 ≤ n ∧ 0 < P.n1 ∧ P.n1 < n
/-- "n1 units ... chosen uniformly at random" (main p. 4, Section 2.2).
An assignment is its treated subset. This finset contains every subset of that size. -/
def assignments {n} (P : Population n) : Finset (Finset (Fin n)) :=
  Finset.univ.powersetCard P.n1
/-- Finite uniform expectation over the complete-randomization assignments (main p. 4). -/
def expectation {n} (P : Population n) (f : Finset (Fin n) → ℝ) : ℝ :=
  (∑ S ∈ assignments P, f S) / ((assignments P).card : ℝ)
/-- Actual design variance: finite average of squared deviations from the design mean. -/
def designVariance {n} (P : Population n) (f : Finset (Fin n) → ℝ) : ℝ :=
  expectation P fun S => (f S - expectation P f) ^ 2
/-- Finite uniform probability, conditional probability uses the same operator over Z*. -/
def probability {n} (P : Population n) (E : Finset (Fin n) → Prop) : ℝ :=
  (((assignments P).filter E).card : ℝ) / ((assignments P).card : ℝ)
/-- "D_i=d_i(Z_i), Y_i=y_i(D_i)" (main p. 4). -/
def observedD {n} (P : Population n) (S : Finset (Fin n)) (i : Fin n) : Bool :=
  P.d i (decide (i ∈ S))
/-- "Y_i=y_i(D_i)", main p. 4, Section 2.2. -/
def observedY {n} (P : Population n) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  P.y i (observedD P S i)
/-- Observed adjusted outcomes Y_i-beta D_i (main pp. 4-5). -/
def observedW {n} (P : Population n) (β : ℝ) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  observedY P S i - β * binary (observedD P S i)
/-- "tau-hat = (1/n) sum (Y_i-beta D_i)(Z_i-pi)" (main p. 4).
`q` is fixed when reassignment S varies. -/
def rawTau {n} (P : Population n) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ i, q i * ((if i ∈ S then 1 else 0) - fraction P)) / (n : ℝ)
/-- tau-hat(beta), main pp. 4-5. -/
def tau {n} (P : Population n) (β : ℝ) (S : Finset (Fin n)) : ℝ :=
  rawTau P (observedW P β S) S
/-- Arm means and residuals used in (3) and (5), main pp. 5-6. -/
def armMean {n} (q : Fin n → ℝ) (S : Finset (Fin n)) (a : Bool) : ℝ :=
  groupMean (if a then S else Sᶜ) q
/-- "sigma-hat squared", main pp. 5-6 before (4)-(5); the arm divisors are squared. -/
def rawSigma2 {n} (P : Population n) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (fraction P) ^ 2 * (1 - fraction P) ^ 2 *
    ((∑ i ∈ S, (q i - armMean q S true) ^ 2) / (P.n1 : ℝ) ^ 2 +
     (∑ i ∈ Sᶜ, (q i - armMean q S false) ^ 2) / (controlSize P) ^ 2)
/-- Absolute AR statistic with support [0,infinity] (main p. 6) and 0/0=0
(Supplement p. 23). A nonzero numerator over a zero standard deviation is infinity. -/
def absStudent (t s2 : ℝ) : ℝ≥0∞ :=
  if s2 = 0 then (if t = 0 then 0 else ⊤) else ENNReal.ofReal (|t| / Real.sqrt s2)
/-- |Delta| and |Delta*|, main (4)-(5); q is fixed for reassignments. -/
def rawAR {n} (P : Population n) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ≥0∞ :=
  absStudent (rawTau P q S) (rawSigma2 P q S)
/-- Smallest attainable value with cumulative probability ≥1-alpha (main p. 6, (6)).
The fallback infinity handles empty designs and out-of-range alpha; admissible
inputs always have a qualifying attainable value. -/
def quantile {n} (P : Population n) (g : Finset (Fin n) → ℝ≥0∞) (α : ℝ) : ℝ≥0∞ :=
  let C := ((assignments P).image g).filter fun t => 1 - α ≤ probability P (fun S => g S ≤ t)
  if h : C.Nonempty then C.min' h else ⊤
/-- I*_{1-alpha}(Z) by inversion of the full distribution, main p. 6, (7). -/
def accepted {n} (P : Population n) (β α : ℝ) (S : Finset (Fin n)) : Prop :=
  rawAR P (observedW P β S) S ≤ quantile P (rawAR P (observedW P β S)) α
/-- Coverage under P_theta, main Theorem 1. -/
def coverage {n} (P : Population n) (β α : ℝ) : ℝ :=
  probability P (accepted P β α)
/-- Scaled population variances S1², S0² and S10² (Supplement p. 22, (B.2)). -/
def S2 {n} (P : Population n) (β : ℝ) (a : Bool) : ℝ :=
  (fraction P)^2 * (1-fraction P)^2 * popVar (w P a β)
/-- "S_10² = pi²(1-pi)²/(n-1) sum_i (v_i(1,beta)-v_i(0,beta))²", Supplement p. 22, (B.2). -/
def Sdiff2 {n} (P : Population n) (β : ℝ) : ℝ :=
  (fraction P)^2 * (1-fraction P)^2 *
    (∑ i, (v P true β i - v P false β i)^2) / ((n : ℝ)-1)
/-- Fourth-root moment, written as two nonnegative square roots (main Assumptions 3(ii),5(ii)). -/
def fourthNorm {n} (q : Fin n → ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (mean fun i => q i ^ 4))
/-- Assumptions 1-4 and at least one complier, main pp. 3-8.
Exclusion is structural in Population; the remaining assumptions are explicit. -/
def Theta {n} (P : Population n) (δ r A : ℝ) : Prop :=
  ValidDesign P ∧ MonotoneReceipt P ∧ (compliers P).Nonempty ∧
  r * (n : ℝ) ≤ (P.n1 : ℝ) ∧ (P.n1 : ℝ) ≤ (1-r) * (n : ℝ) ∧
  groupCov (compliers P) (w P true (late P)) (w P false (late P)) ≥
    -δ * Real.sqrt (groupVar (compliers P) (w P true (late P))) *
      Real.sqrt (groupVar (compliers P) (w P false (late P))) ∧
  ∀ a, fourthNorm (v P a (late P)) ≤ A * Real.sqrt (popVar (w P a (late P)))

/-- "tilde x_i=[1,x_i']'", Supplement p. 32, (E.1). Option indexes intercept and slopes. -/
def augmented {n k} (x : Fin n → Fin k → ℝ) (i : Fin n) : Option (Fin k) → ℝ
  | none => 1
  | some s => x i s
/-- x_i^circ=[0,x_i']', Supplement p. 32. -/
def xCirc {n k} (x : Fin n → Fin k → ℝ) (i : Fin n) : Option (Fin k) → ℝ
  | none => 0
  | some s => x i s
/-- "standard l2 vector norm" (Supplement p. 21), represented here by its square, sum of coordinate squares. -/
def normSq {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := ∑ j, v j ^ 2
/-- Gram matrix and score of an intercept-and-covariate regression, (D.2),(E.2)-(E.3). -/
def gram {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n)) :
    Matrix (Option (Fin k)) (Option (Fin k)) ℝ :=
  fun s t => groupMean S fun i => augmented x i s * augmented x i t
/-- The vector "(1/n_a) sum_{T(a)} tilde x_i epsilon_i(a,beta)" in (E.2)-(E.3), Supplement p. 32; q can also be a response. -/
def score {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n)) (q : Fin n → ℝ) :
    Option (Fin k) → ℝ := fun s => groupMean S fun i => augmented x i s * q i
/-- Residual sum of squares defining OLS, (8),(D.2). -/
def rss {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n))
    (q : Fin n → ℝ) (c : Option (Fin k) → ℝ) : ℝ :=
  ∑ i ∈ S, (q i - dotProduct (augmented x i) c)^2
/-- OLS coefficients: inverse normal-equation formula when full rank; otherwise
choose an RSS minimizer using Classical.choice (main (8), Supplement (D.2)).
Finite real least squares has a minimizer; existence is also stated below as a lemma.
The paper leaves singular arms unspecified. This fixed choice depends only on x,q,S. -/
def ols {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n)) (q : Fin n → ℝ) :
    Option (Fin k) → ℝ :=
  if (gram x S).det ≠ 0 then (gram x S)⁻¹ *ᵥ score x S q
  else if h : ∃ c, ∀ b, rss x S q c ≤ rss x S q b then Classical.choose h else 0
/-- Population coefficient vector psi(a,beta) and residual epsilon_i(a,beta),
Supplement p. 31 (D.2) and p. 32 (E.1). -/
def psi {n k} (P : CovPopulation n k) (a : Bool) (β : ℝ) :=
  ols P.x Finset.univ (w P.pop a β)
/-- "epsilon_i(a,beta) = y_i(d_i(a))-beta*d_i(a)-x_i'gamma(a,beta)
-varphi(a,beta)", Supplement p. 32, (E.1), population regression residual. -/
def residual {n k} (P : CovPopulation n k) (a : Bool) (β : ℝ) (i : Fin n) : ℝ :=
  w P.pop a β i - dotProduct (augmented P.x i) (psi P a β)
/-- Fitted psi-hat in (8),(E.1), q may be the fixed observed outcome vector. -/
def fitted {n k} (P : CovPopulation n k) (q : Fin n → ℝ)
    (S : Finset (Fin n)) (a : Bool) := ols P.x (if a then S else Sᶜ) q
/-- Slope contribution x_i'gamma; the intercept is omitted, as in (9),(D.4). -/
def slopeDot {k} (x : Fin k → ℝ) (c : Option (Fin k) → ℝ) : ℝ :=
  ∑ j, x j * c (some j)
/-- Adjusted difference of arm means for supplied slopes, main p. 9 (9), Supp. (D.4). -/
def adjustedWith {n k} (P : CovPopulation n k) (q : Fin n → ℝ)
    (S : Finset (Fin n)) (c1 c0 : Option (Fin k) → ℝ) : ℝ :=
  groupMean S (fun i => q i - slopeDot (P.x i) c1) -
  groupMean Sᶜ (fun i => q i - slopeDot (P.x i) c0)
/-- Feasible adjusted statistic, re-estimating both regressions for S, main (9). -/
def adjustedTau {n k} (P : CovPopulation n k) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  adjustedWith P q S (fitted P q S true) (fitted P q S false)
/-- Oracle statistic tilde tau, population slopes fixed as Z varies, Supplement (D.4). -/
def oracleTau {n k} (P : CovPopulation n k) (β : ℝ) (S : Finset (Fin n)) : ℝ :=
  adjustedWith P (observedW P.pop β S) S (psi P true β) (psi P false β)
/-- Randomization oracle tilde tau*, pooled observed-outcome coefficients fixed as Z* varies,
Supplement (D.3)-(D.6). -/
def oracleStar {n k} (P : CovPopulation n k) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  adjustedWith P q S (ols P.x Finset.univ q) (ols P.x Finset.univ q)
/-- Adjusted residual variance estimator, main p. 9 before (10). -/
def adjustedSigma2 {n k} (P : CovPopulation n k) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  rss P.x S q (fitted P q S true) / (P.pop.n1 : ℝ)^2 +
  rss P.x Sᶜ q (fitted P q S false) / (controlSize P.pop)^2
/-- Adjusted absolute AR and confidence set (10)-(11), main pp. 9-10. -/
def adjustedAR {n k} (P : CovPopulation n k) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ≥0∞ :=
  absStudent (adjustedTau P q S) (adjustedSigma2 P q S)
/-- "I_adj,* = {beta : |Delta_adj(beta)| ≤ eta_adj,*}", main p. 10, (11). -/
def adjustedAccepted {n k} (P : CovPopulation n k) (β α : ℝ) (S : Finset (Fin n)) : Prop :=
  adjustedAR P (observedW P.pop β S) S ≤
    quantile P.pop (adjustedAR P (observedW P.pop β S)) α
/-- "P_theta{beta ∈ I_adj,*(Z)}", main p. 11, Theorem 2. -/
def adjustedCoverage {n k} (P : CovPopulation n k) (β α : ℝ) : ℝ :=
  probability P.pop (adjustedAccepted P β α)
/-- Xi_n: Assumptions 1,2,4,5, main pp. 10-11. The smallest-eigenvalue bound
is represented by its equivalent Rayleigh inequality for the real symmetric Gram matrix. -/
def Xi {n k} (P : CovPopulation n k) (δ e A B r : ℝ) : Prop :=
  ValidDesign P.pop ∧ MonotoneReceipt P.pop ∧ (compliers P.pop).Nonempty ∧
  r * (n : ℝ) ≤ (P.pop.n1 : ℝ) ∧ (P.pop.n1 : ℝ) ≤ (1-r) * (n : ℝ) ∧
  popCov (residual P true (late P.pop)) (residual P false (late P.pop)) ≥
    -δ * Real.sqrt (popVar (residual P true (late P.pop))) *
      Real.sqrt (popVar (residual P false (late P.pop))) ∧
  (∀ a, fourthNorm (residual P a (late P.pop)) ≤
      B * Real.sqrt (popVar (residual P a (late P.pop)))) ∧
  (∀ s, ∑ i, P.x i s = 0) ∧ (∀ s, mean (fun i => P.x i s ^ 4) ≤ A) ∧
  (∀ b : Fin k → ℝ, e * normSq b ≤ mean (fun i => (dotProduct (P.x i) b)^2))

/-- Every finite real least-squares problem has an RSS minimizer, implicit in (8),(D.2). -/
theorem ols_minimizer_exists {n k} (x : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (q : Fin n → ℝ) :
    ∃ c, ∀ b, rss x S q c ≤ rss x S q b := by
  let L : (Option (Fin k) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun := fun c => WithLp.toLp 2 (fun i =>
        if i ∈ S then dotProduct (augmented x i) c else 0)
      map_add' := by
        intro a b
        ext i
        change (if i ∈ S then dotProduct (augmented x i) (a+b) else 0) =
          (if i ∈ S then dotProduct (augmented x i) a else 0) +
          (if i ∈ S then dotProduct (augmented x i) b else 0)
        by_cases hi : i ∈ S <;> simp [hi, dotProduct_add]
      map_smul' := by
        intro r b
        ext i
        change (if i ∈ S then dotProduct (augmented x i) (r • b) else 0) =
          r * (if i ∈ S then dotProduct (augmented x i) b else 0)
        by_cases hi : i ∈ S <;> simp [hi, dotProduct_smul, smul_eq_mul] }
  let u : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun i => if i ∈ S then q i else 0)
  obtain ⟨v, hv, hmin⟩ := L.range.exists_norm_eq_iInf_of_complete_subspace
    L.range.complete_of_finiteDimensional u
  obtain ⟨c, rfl⟩ := hv
  refine ⟨c, fun b => ?_⟩
  have hbound : BddBelow (Set.range fun v :
      {v : EuclideanSpace ℝ (Fin n) // v ∈ L.range} => ‖u-v.val‖) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact norm_nonneg _
  have hnorm : ‖u-L c‖ ≤ ‖u-L b‖ := by
    rw [hmin]
    exact ciInf_le hbound ⟨L b, LinearMap.mem_range_self L b⟩
  have hsquare := (sq_le_sq₀ (norm_nonneg (u-L c)) (norm_nonneg (u-L b))).mpr hnorm
  have hident (b : Option (Fin k) → ℝ) : ‖u-L b‖^2 = rss x S q b := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i, ((if i ∈ S then q i else 0) -
      (if i ∈ S then dotProduct (augmented x i) b else 0))^2) =
      ∑ i ∈ S, (q i-dotProduct (augmented x i) b)^2
    have hi (i : Fin n) : ((if i ∈ S then q i else 0) -
        (if i ∈ S then dotProduct (augmented x i) b else 0))^2 =
        if i ∈ S then (q i-dotProduct (augmented x i) b)^2 else 0 := by
      by_cases hi : i ∈ S <;> simp [hi]
    simp_rw [hi]
    exact Finset.sum_ite_mem_eq S (fun i => (q i-dotProduct (augmented x i) b)^2)
  simpa only [hident] using hsquare

/-- Exact finite linearity of an arm mean (used throughout the paper). -/
theorem groupMean_sub_smul {n} (S : Finset (Fin n)) (q d : Fin n → ℝ) (β : ℝ) :
    groupMean S (fun i => q i - β * d i) = groupMean S q - β * groupMean S d := by
  simp only [groupMean, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Population mean is linear, used in corrected centring and LATE identities. -/
theorem mean_sub_smul {n} (q d : Fin n → ℝ) (β : ℝ) :
    mean (fun i => q i-β*d i)=mean q-β*mean d := by
  simp only [mean, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- OLS score is linear in its response, Supplement p. 45, (I.1). -/
theorem score_linear {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n))
    (q d : Fin n → ℝ) (β : ℝ) :
    score x S (fun i => q i - β * d i) = score x S q - β • score x S d := by
  ext s
  simp only [score, groupMean, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (augmented x _ s) β, ← Finset.mul_sum]
  ring

/-- Unique OLS coefficients are linear in the response, Supplement p. 45, (I.1). -/
theorem ols_linear {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n))
    (q d : Fin n → ℝ) (β : ℝ) (h : (gram x S).det ≠ 0) :
    ols x S (fun i => q i - β * d i) = ols x S q - β • ols x S d := by
  simp only [ols, if_pos h, score_linear, Matrix.mulVec_sub, Matrix.mulVec_smul]

/-- Slope-adjusted arm means are linear jointly in response and coefficients,
Supplement pp. 45-46, corrected (I.2). -/
theorem adjustedWith_linear {n k} (P : CovPopulation n k) (S : Finset (Fin n))
    (q d : Fin n → ℝ) (β : ℝ) (y1 y0 d1 d0 : Option (Fin k) → ℝ) :
    adjustedWith P (fun i => q i - β * d i) S (y1 - β • d1) (y0 - β • d0) =
      adjustedWith P q S y1 y0 - β * adjustedWith P d S d1 d0 := by
  have hs (i : Fin n) (a b : Option (Fin k) → ℝ) :
      q i - β * d i - slopeDot (P.x i) (a - β • b) =
      (q i - slopeDot (P.x i) a) - β * (d i - slopeDot (P.x i) b) := by
    simp only [slopeDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib]
    simp_rw [mul_left_comm (P.x i _) β, ← Finset.mul_sum]
    ring
  simp only [adjustedWith, hs, groupMean_sub_smul]
  ring

/-- T24: corrected (I.1)-(I.2), for full-rank arms. The slopes are gamma, and
the statistic is tau_adj. The adjusted Wald value zeroes the numerator. -/
theorem corrected_I1_I2 {n k} (P : CovPopulation n k) (S : Finset (Fin n))
    (Y D : Fin n → ℝ) (β : ℝ)
    (h1 : (gram P.x S).det ≠ 0) (h0 : (gram P.x Sᶜ).det ≠ 0) :
    (∀ a, fitted P (fun i => Y i - β * D i) S a =
      fitted P Y S a - β • fitted P D S a) ∧
    adjustedTau P (fun i => Y i - β * D i) S =
      adjustedTau P Y S - β * adjustedTau P D S ∧
    (adjustedTau P D S ≠ 0 →
      adjustedTau P (fun i => Y i - (adjustedTau P Y S / adjustedTau P D S) * D i) S = 0) := by
  have hl (b : ℝ) (a : Bool) : fitted P (fun i => Y i - b * D i) S a =
      fitted P Y S a - b • fitted P D S a := by
    cases a
    · exact ols_linear _ _ _ _ _ h0
    · exact ols_linear _ _ _ _ _ h1
  have ht (b : ℝ) : adjustedTau P (fun i => Y i - b * D i) S =
      adjustedTau P Y S - b * adjustedTau P D S := by
    simp only [adjustedTau, hl]
    exact adjustedWith_linear _ _ _ _ _ _ _ _ _
  refine ⟨hl β, ht β, ?_⟩
  intro hd
  rw [ht]
  field_simp [hd]
  <;> ring

/-- T18, first corrected identity: fitted minus oracle has a minus treated
slope error and a plus control slope error (Supplement p. 36). No rank
assumption is needed for the subtraction identity. -/
theorem corrected_adjusted_difference {n k} (P : CovPopulation n k)
    (β : ℝ) (S : Finset (Fin n)) :
    adjustedTau P (observedW P.pop β S) S - oracleTau P β S =
      -groupMean S (fun i => slopeDot (P.x i)
        (fitted P (observedW P.pop β S) S true - psi P true β)) +
       groupMean Sᶜ (fun i => slopeDot (P.x i)
        (fitted P (observedW P.pop β S) S false - psi P false β)) := by
  simp only [adjustedTau, oracleTau, adjustedWith, groupMean, slopeDot, Pi.sub_apply,
    mul_sub, Finset.sum_sub_distrib, sub_div]
  ring

/-- Arm score of residuals is the response score minus Gram times coefficients;
this is the finite normal-equation algebra behind (E.2)-(E.3). -/
theorem score_residual {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n))
    (q : Fin n → ℝ) (c : Option (Fin k) → ℝ) :
    score x S (fun i => q i - dotProduct (augmented x i) c) =
      score x S q - gram x S *ᵥ c := by
  ext s
  simp only [score, gram, groupMean, Matrix.mulVec, dotProduct, Pi.sub_apply,
    mul_sub, Finset.sum_sub_distrib, sub_div]
  congr 1
  simp only [Finset.mul_sum, div_mul_eq_mul_div]
  rw [Finset.sum_comm]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Correct finite OLS error, (E.2)-(E.3), valid for any reference coefficients. -/
theorem ols_error {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n))
    (q : Fin n → ℝ) (c : Option (Fin k) → ℝ) (h : (gram x S).det ≠ 0) :
    ols x S q - c = (gram x S)⁻¹ *ᵥ score x S (fun i => q i - dotProduct (augmented x i) c) := by
  rw [score_residual, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h), Matrix.one_mulVec]
  simp only [ols, if_pos h]

/-- T19: corrected (E.41) and the cross term after (E.46). Population minus
fitted is minus inverse-Gram times residual score; the cross term is -2h'G^-1h.
The statement is exact whenever the arm Gram matrix is invertible. -/
theorem corrected_E41_cross_term {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n))
    (q : Fin n → ℝ) (c : Option (Fin k) → ℝ) (h : (gram x S).det ≠ 0) :
    c - ols x S q = -(gram x S)⁻¹ *ᵥ
      score x S (fun i => q i - dotProduct (augmented x i) c) ∧
    -2 * dotProduct (score x S (fun i => q i - dotProduct (augmented x i) c))
      (ols x S q - c) =
    -2 * dotProduct (score x S (fun i => q i - dotProduct (augmented x i) c))
      ((gram x S)⁻¹ *ᵥ score x S (fun i => q i - dotProduct (augmented x i) c)) := by
  have he := ols_error x S q c h
  constructor
  · rw [Matrix.neg_mulVec, ← he]
    abel
  · rw [he]

/-- The residual-score inner product is exactly the finite arm cross term
in (E.39), not a separate probabilistic or OLS assumption. -/
theorem score_dot {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n))
    (q : Fin n → ℝ) (c : Option (Fin k) → ℝ) :
    dotProduct (score x S q) c=groupMean S (fun i => q i*dotProduct (augmented x i) c) := by
  simp only [dotProduct, score, groupMean, Finset.mul_sum, div_mul_eq_mul_div,
    Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exclusion and monotonicity make adjusted potential differences vanish off
compliers, and equal y(1)-y(0)-beta on compliers, used in (C.2),(C.8). -/
theorem w_difference_compliers {n} (P : Population n) (hm : MonotoneReceipt P)
    (β : ℝ) (i : Fin n) :
    w P true β i-w P false β i =
      if i ∈ compliers P then P.y i true-P.y i false-β else 0 := by
  cases h0 : P.d i false <;> cases h1 : P.d i true
  · simp [w, binary, compliers, h0, h1]
  · simp [w, binary, compliers, h0, h1]
    ring
  · have hh := hm i h0
    simp [h1] at hh
  · simp [w, binary, compliers, h0, h1]
/-- The total adjusted potential difference is |C|*(LATE-beta). This is the
finite identity behind unbiasedness, moment collapse, and equal intercepts. -/
theorem sum_w_difference {n} (P : Population n) (hm : MonotoneReceipt P)
    (hc : (compliers P).Nonempty) (β : ℝ) :
    (∑ i : Fin n, (w P true β i-w P false β i))=((compliers P).card : ℝ)*(late P-β) := by
  have hcard : ((compliers P).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hc)
  have hrestrict : (∑ i : Fin n, (w P true β i-w P false β i))=
      ∑ i ∈ compliers P, (w P true β i-w P false β i) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hin
    rw [w_difference_compliers P hm β i, if_neg hin]
  rw [hrestrict]
  simp_rw [w_difference_compliers P hm β]
  have hs : (∑ i ∈ compliers P,
      if i ∈ compliers P then P.y i true-P.y i false-β else 0) =
      (∑ i ∈ compliers P, (P.y i true-P.y i false))-((compliers P).card : ℝ)*β := by
    simp [Finset.sum_sub_distrib]
  rw [hs]
  unfold late groupMean
  field_simp [hcard]
  <;> ring
/-- At beta=LATE, the two population means of w coincide (C.2), Supplement p. 24. -/
theorem mean_w_equal_at_late {n} (P : Population n) (hm : MonotoneReceipt P)
    (hc : (compliers P).Nonempty) : mean (w P true (late P))=mean (w P false (late P)) := by
  have h := sum_w_difference P hm hc (late P)
  simp only [sub_self, mul_zero, Finset.sum_sub_distrib, sub_eq_zero] at h
  simp only [mean, h]

/-- The score of a linear fitted response is Gram times its coefficient vector,
the finite normal-equation identity used in Supplement (E.38)-(E.41). -/
theorem score_of_dot {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n))
    (c : Option (Fin k) → ℝ) :
    score x S (fun i => dotProduct (augmented x i) c)=gram x S *ᵥ c := by
  have H := score_residual x S (fun i => dotProduct (augmented x i) c) c
  have hz : (fun i => dotProduct (augmented x i) c-dotProduct (augmented x i) c)=0 := by
    funext i
    exact sub_self _
  have hs : score x S 0=0 := by
    funext s
    simp [score, groupMean]
  rw [hz, hs] at H
  exact sub_eq_zero.mp H.symm

/-- The finite Gram quadratic form is the arm mean of squared fitted values,
the positive-semidefinite identity behind the OLS and eigenvalue arguments,
Supplement pp.32,39-42. -/
theorem gram_quadratic {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n))
    (c : Option (Fin k) → ℝ) :
    dotProduct c (gram x S *ᵥ c)=groupMean S (fun i => (dotProduct (augmented x i) c)^2) := by
  have H := score_dot x S (fun i => dotProduct (augmented x i) c) c
  rw [score_of_dot] at H
  calc
    _ = dotProduct (gram x S *ᵥ c) c := dotProduct_comm _ _
    _ = _ := by simpa only [pow_two] using H

/-- Exact residual sum of squares decrease under an arm OLS projection.
This is the finite projection identity (P002-E003) behind corrected
(E.38)–(E.39). It uses actual fitted coefficients and inverse arm Gram, not an
assumed variance-consistency conclusion. -/
theorem residual_sum_squares_identity {n k} (x : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (q : Fin n → ℝ) (c : Option (Fin k) → ℝ)
    (hS : S.Nonempty) (hg : (gram x S).det ≠ 0) :
    rss x S q (ols x S q)/(S.card : ℝ) =
      groupMean S (fun i => (q i-dotProduct (augmented x i) c)^2) -
      dotProduct (score x S (fun i => q i-dotProduct (augmented x i) c))
        ((gram x S)⁻¹ *ᵥ score x S (fun i => q i-dotProduct (augmented x i) c)) := by
  let r : Fin n → ℝ := fun i => q i-dotProduct (augmented x i) c
  let h := score x S r
  let e := ols x S q-c
  have he : e=(gram x S)⁻¹ *ᵥ h := ols_error x S q c hg
  have hGe : gram x S *ᵥ e=h := by
    rw [he, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg), Matrix.one_mulVec]
  have hcross : groupMean S (fun i => r i*dotProduct (augmented x i) e)=dotProduct h e :=
    (score_dot x S r e).symm
  have H := score_dot x S (fun i => dotProduct (augmented x i) e) e
  rw [score_of_dot, hGe] at H
  have hquad : groupMean S (fun i => (dotProduct (augmented x i) e)^2)=dotProduct h e := by
    simpa only [pow_two] using H.symm
  have hf (i : Fin n) : q i-dotProduct (augmented x i) (ols x S q)=
      r i-dotProduct (augmented x i) e := by
    dsimp only [r, e]
    rw [dotProduct_sub]
    ring
  have hexpand : groupMean S (fun i => (r i-dotProduct (augmented x i) e)^2)=
      groupMean S (fun i => r i^2)-2*groupMean S (fun i => r i*dotProduct (augmented x i) e)+
        groupMean S (fun i => (dotProduct (augmented x i) e)^2) := by
    simp only [groupMean, sub_sq, mul_assoc, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  change groupMean S (fun i => (q i-dotProduct (augmented x i) (ols x S q))^2)=
    groupMean S (fun i => r i^2)-dotProduct h ((gram x S)⁻¹ *ᵥ h)
  simp_rw [hf]
  rw [hexpand, hcross, hquad, he]
  ring

/-- The inverse-normal-equation OLS rule is an actual least-squares minimizer
on every nonempty full-rank arm (main (8), Supplement (D.2)), proved from the
finite RSS identity and Gram nonnegativity. Singular-arm existence is separate. -/
theorem ols_minimizer_fullrank {n k} (x : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (q : Fin n → ℝ) (hS : S.Nonempty)
    (hg : (gram x S).det ≠ 0) : ∀ c, rss x S q (ols x S q) ≤ rss x S q c := by
  intro c
  let h := score x S (fun i => q i-dotProduct (augmented x i) c)
  let e := (gram x S)⁻¹ *ᵥ h
  have he : gram x S *ᵥ e=h := by
    dsimp only [e]
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg), Matrix.one_mulVec]
  have hn : 0 ≤ dotProduct h e := by
    calc
      _ ≤ groupMean S (fun i => (dotProduct (augmented x i) e)^2) := by
        unfold groupMean
        exact div_nonneg (Finset.sum_nonneg fun i hi => sq_nonneg _) (Nat.cast_nonneg _)
      _ = dotProduct h e := by
        rw [← gram_quadratic, he]
        exact dotProduct_comm _ _
  have H := residual_sum_squares_identity x S q c hS hg
  have Hle := H.le.trans (sub_le_self _ hn)
  change rss x S q (ols x S q)/(S.card : ℝ) ≤ rss x S q c/(S.card : ℝ) at Hle
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  exact (div_le_div_iff_of_pos_right hcard).mp Hle

/-- Exact number of complete-randomization assignments that contain a specified
set R of units. This is the finite inclusion-count lemma underlying the
expectations and covariances in (B.1), (C.17), and (C.30). -/
theorem assignment_inclusion_count {n} (P : Population n) (R : Finset (Fin n))
    (hR : R.card ≤ P.n1) :
    ((assignments P).filter (fun S => R ⊆ S)).card=
      Nat.choose (n-R.card) (P.n1-R.card) := by
  simpa only [assignments, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_powersetCard_subset R Finset.univ P.n1 (Finset.subset_univ R) hR

/-- The treatment inclusion probability is n1/n under complete randomization
(main p. 4, Section 2.2), derived from counts of the actual assignment set. -/
theorem assignment_marginal {n} (P : Population n) (h : ValidDesign P) (i : Fin n) :
    expectation P (fun S => if i ∈ S then (1 : ℝ) else 0)=fraction P := by
  have hn2 := h.1
  have hk0 := h.2.1
  have hn : 1 ≤ n := by omega
  have hk : 1 ≤ P.n1 := by omega
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  have hC : (n.choose P.n1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (Nat.le_of_lt h.2.2)))
  have hcard : (assignments P).card=n.choose P.n1 := by
    simp [assignments]
  have hfilter : ((assignments P).filter (fun S => i ∈ S)).card=
      (n-1).choose (P.n1-1) := by
    simpa only [Finset.card_singleton, Finset.singleton_subset_iff] using
      assignment_inclusion_count P {i} (by simpa only [Finset.card_singleton] using hk)
  have hid : n*(n-1).choose (P.n1-1)=n.choose P.n1*P.n1 := by
    simpa only [Nat.sub_add_cancel hn, Nat.sub_add_cancel hk] using
      Nat.add_one_mul_choose_eq (n-1) (P.n1-1)
  have hidR : (n : ℝ)*((n-1).choose (P.n1-1) : ℝ)=
      (n.choose P.n1 : ℝ)*(P.n1 : ℝ) := by exact_mod_cast hid
  have he : expectation P (fun S => if i ∈ S then (1 : ℝ) else 0)=
      (((assignments P).filter (fun S => i ∈ S)).card : ℝ)/((assignments P).card : ℝ) := by
    simp [expectation, Finset.sum_ite]
  rw [he, hfilter, hcard, fraction]
  apply (div_eq_div_iff hC hN).mpr
  nlinarith only [hidR]

/-- Finite linearity of design expectation (main p. 4, design-based framework). -/
theorem expectation_sub {n} (P : Population n) (f g : Finset (Fin n) → ℝ) :
    expectation P (fun S => f S-g S)=expectation P f-expectation P g := by
  simp only [expectation, Finset.sum_sub_distrib, sub_div]

/-- A fixed real coefficient may be moved through the finite randomization
expectation (main p. 4, design-based framework). -/
theorem expectation_mul {n} (P : Population n) (a : ℝ) (f : Finset (Fin n) → ℝ) :
    expectation P (fun S => a*f S)=a*expectation P f := by
  simp only [expectation, ← Finset.mul_sum]
  ring

/-- A fixed denominator may be moved through the finite randomization
expectation (main p. 4, design-based framework). -/
theorem expectation_div {n} (P : Population n) (f : Finset (Fin n) → ℝ) (a : ℝ) :
    expectation P (fun S => f S/a)=expectation P f/a := by
  simp only [expectation, ← Finset.sum_div]
  ring

/-- A finite sum may be interchanged with design expectation, the finite
calculation implicit in Supplement p. 22, Lemmas 2-3. -/
theorem expectation_sum {n} (P : Population n) (f : Fin n → Finset (Fin n) → ℝ) :
    expectation P (fun S => ∑ i, f i S)=∑ i, expectation P (f i) := by
  unfold expectation
  rw [Finset.sum_comm, Finset.sum_div]

/-- A valid finite randomization distribution gives a fixed quantity its own
expectation (main p. 4); nonempty support is derived from the design. -/
theorem expectation_const {n} (P : Population n) (h : ValidDesign P) (a : ℝ) :
    expectation P (fun _ => a)=a := by
  have hF : (assignments P).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa using Nat.le_of_lt h.2.2
  have hcard : ((assignments P).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hF)
  simp [expectation, hcard]

/-- The expectation of tau-hat(beta) equals pi(1-pi) times the population
adjusted-potential-outcome contrast. This is the finite calculation in
Supplement p. 22, Lemma 3, before beta is set equal to the LATE. -/
theorem tau_expectation {n} (P : Population n) (h : ValidDesign P) (β : ℝ) :
    expectation P (tau P β)=fraction P*(1-fraction P)*
      (mean (w P true β)-mean (w P false β)) := by
  let c := fraction P
  have hp (S : Finset (Fin n)) (i : Fin n) :
      observedW P β S i*((if i ∈ S then 1 else 0)-c)=
        (if i ∈ S then 1 else 0)*((1-c)*w P true β i+c*w P false β i)-c*w P false β i := by
    by_cases hi : i ∈ S
    · have hw : observedW P β S i=w P true β i := by
        simp [observedW, observedY, observedD, w, hi]
      rw [hw]
      simp only [hi, ite_true]
      ring
    · have hw : observedW P β S i=w P false β i := by
        simp [observedW, observedY, observedD, w, hi]
      rw [hw]
      simp only [hi, ite_false]
      ring
  have hf (S : Finset (Fin n)) : tau P β S=
      (∑ i, (((1-c)*w P true β i+c*w P false β i)*(if i ∈ S then 1 else 0)-
        c*w P false β i))/(n : ℝ) := by
    simp only [tau, rawTau]
    apply congrArg (fun t : ℝ => t/(n : ℝ))
    apply Finset.sum_congr rfl
    intro i hi
    rw [hp]
    ring
  have hfun := funext hf
  rw [hfun, expectation_div, expectation_sum]
  simp_rw [expectation_sub, expectation_mul, assignment_marginal P h, expectation_const P h]
  dsimp [c]
  simp only [mean, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Unbiasedness at the sample LATE, Supplement p. 22, Lemma 3. -/
theorem tau_mean_zero {n} (P : Population n) (h : ValidDesign P)
    (hm : MonotoneReceipt P) (hc : (compliers P).Nonempty) :
    expectation P (tau P (late P)) = 0 := by
  rw [tau_expectation P h (late P), mean_w_equal_at_late P hm hc]
  ring

/-- Nonnegative covariance constants may be relaxed to delta-plus=max(delta,0);
this is the corrected weighted-square step (C.4) and (E.10). -/
theorem corrected_variance_algebra (n0 n1 a b C δ : ℝ) (h0 : 0 < n0) (h1 : 0 < n1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : -δ*a*b ≤ C) :
    (1-max δ 0) * (n0/((n0+n1)*n1)*a^2 + n1/((n0+n1)*n0)*b^2) ≤
      a^2/n1 + b^2/n0 - (a^2+b^2-2*C)/(n0+n1) := by
  have hd : 0 ≤ max δ 0 := le_max_right _ _
  have hδ : δ ≤ max δ 0 := le_max_left _ _
  have hab : 0 ≤ a*b := mul_nonneg ha hb
  have hc : -(max δ 0)*a*b ≤ C := by
    have := mul_le_mul_of_nonneg_right hδ hab
    nlinarith
  have hw : 2*n0*n1*a*b ≤ n0^2*a^2+n1^2*b^2 := by
    nlinarith [sq_nonneg (n0*a-n1*b)]
  have hw' := mul_le_mul_of_nonneg_left hw hd
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*n0*n1 by positivity)
  have hn : 0 ≤ (max δ 0)*(n0^2*a^2+n1^2*b^2)+2*n0*n1*C := by
    nlinarith [hw', hc']
  have he : (a^2/n1+b^2/n0-(a^2+b^2-2*C)/(n0+n1)) -
      (1-max δ 0)*(n0/((n0+n1)*n1)*a^2+n1/((n0+n1)*n0)*b^2) =
      ((max δ 0)*(n0^2*a^2+n1^2*b^2)+2*n0*n1*C)/((n0+n1)*n0*n1) := by
    field_simp
    <;> ring
  apply sub_nonneg.mp
  rw [he]
  exact div_nonneg hn (by positivity)

/- T3(a): Lemma 5 exactly as printed, Supplement p. 23; false for negative delta. -/

/- T3(b): Lemma 16(1), (E.10) as printed. Its pointwise bound is false and
therefore also false along the repeated-block subsequence of T1. -/


/-- T1's repeated four-unit block: three copies at n=12, then 3m copies at n=12m.
The coordinates are (-1,-1),(-1,1),(1,-1),(1,1), all units compliers, y(1)=y(0).
P002-E002; Supplement (C.3)-(C.8),(E.10). -/
def negativeDeltaModel (m : ℕ) : CovPopulation (12*m) 1 where
  pop := {y := fun i _ => if i.val % 2 = 0 then -1 else 1,
          d := fun _ a => a, n1 := 2*m}
  x := fun i _ => if i.val % 4 < 2 then -1 else 1
/-- All 66 equally likely treated pairs in the 12-unit model (P002-E002). -/
theorem negative_delta_assignments : assignments (negativeDeltaModel 1).pop =
    ({{0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {0,6}, {0,7}, {0,8}, {0,9}, {0,10}, {0,11}, {1,2}, {1,3}, {1,4}, {1,5}, {1,6}, {1,7}, {1,8}, {1,9}, {1,10}, {1,11}, {2,3}, {2,4}, {2,5}, {2,6}, {2,7}, {2,8}, {2,9}, {2,10}, {2,11}, {3,4}, {3,5}, {3,6}, {3,7}, {3,8}, {3,9}, {3,10}, {3,11}, {4,5}, {4,6}, {4,7}, {4,8}, {4,9}, {4,10}, {4,11}, {5,6}, {5,7}, {5,8}, {5,9}, {5,10}, {5,11}, {6,7}, {6,8}, {6,9}, {6,10}, {6,11}, {7,8}, {7,9}, {7,10}, {7,11}, {8,9}, {8,10}, {8,11}, {9,10}, {9,11}, {10,11}} : Finset (Finset (Fin 12))) := by
  decide
/-- Population OLS coefficients in the negative-delta example are zero, exactly
by the orthogonality calculation. -/
theorem negative_delta_population_ols (a : Bool) : psi (negativeDeltaModel 1) a 0 = 0 := by
  have hg : gram (negativeDeltaModel 1).x Finset.univ = 1 := by
    ext s t
    rcases s with _ | s <;> rcases t with _ | t
    · norm_num [gram, groupMean, augmented, negativeDeltaModel, Matrix.one_apply, Fin.sum_univ_succ]
    · fin_cases t
      norm_num [gram, groupMean, augmented, negativeDeltaModel, Matrix.one_apply, Fin.sum_univ_succ]
    · fin_cases s
      norm_num [gram, groupMean, augmented, negativeDeltaModel, Matrix.one_apply, Fin.sum_univ_succ]
    · fin_cases s; fin_cases t
      norm_num [gram, groupMean, augmented, negativeDeltaModel, Matrix.one_apply, Fin.sum_univ_succ]
  have hs : score (negativeDeltaModel 1).x Finset.univ (w (negativeDeltaModel 1).pop a 0) = 0 := by
    ext s
    rcases s with _ | s
    · norm_num [score, groupMean, augmented, w, negativeDeltaModel, binary, Fin.sum_univ_succ]
    · fin_cases s
      norm_num [score, groupMean, augmented, w, negativeDeltaModel, binary, Fin.sum_univ_succ]
  simp [psi, ols, hg, hs]

/-- The finite control-arm total is the population total minus the treatment-arm
total, a deterministic complete-randomization identity used in (D.4)-(D.5). -/
theorem sum_complement_eq {n} (S : Finset (Fin n)) (q : Fin n → ℝ) :
    (∑ i ∈ Sᶜ, q i)=(∑ i, q i)-(∑ i ∈ S, q i) := by
  have H := Finset.sum_add_sum_compl S q
  linarith

/-- The raw statistic is the treated total minus pi times the population total,
all divided by n, main pp. 4-5, Section 3.1. This finite identity also avoids
re-expanding binary indicators when checking the concrete counterexamples. -/
theorem rawTau_sum {n} (P : Population n) (q : Fin n → ℝ) (S : Finset (Fin n)) :
    rawTau P q S=((∑ i ∈ S, q i)-fraction P*(∑ i, q i))/(n : ℝ) := by
  simp only [rawTau, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  congr 1
  have ht : (∑ i : Fin n, q i*(if i ∈ S then (1 : ℝ) else 0))=∑ i ∈ S, q i := by
    simp only [mul_ite, mul_one, mul_zero]
    exact Finset.sum_ite_mem_eq S q
  rw [ht, ← Finset.sum_mul]
  ring

set_option maxHeartbeats 8000000 in
/-- T1(a)-(c): the 12-unit instance satisfies every assumption in both classes,
and its actual design variances are 5/396 and 36/55, below the printed bounds.
No variance formula is substituted for the randomization distribution. -/
theorem negative_delta_counterexample :
    let P := negativeDeltaModel 1
    Theta P.pop (-1/2) (1/6) 2 ∧ Xi P (-1/2) (1/2) 2 2 (1/6) ∧
    late P.pop = 0 ∧ (assignments P.pop).card = 66 ∧
    S2 P.pop 0 true = 25/1188 ∧ S2 P.pop 0 false = 25/1188 ∧
    designVariance P.pop (tau P.pop 0) = 5/396 ∧
    designVariance P.pop (oracleTau P 0) = 36/55 ∧
    designVariance P.pop (tau P.pop 0) <
      (1-(-1/2 : ℝ))*(controlSize P.pop/(12*2)*S2 P.pop 0 true +
        2/(12*controlSize P.pop)*S2 P.pop 0 false) ∧
    designVariance P.pop (oracleTau P 0) <
      (1-(-1/2 : ℝ))*(controlSize P.pop/(12*2)*popVar (residual P true 0) +
        2/(12*controlSize P.pop)*popVar (residual P false 0)) := by
  dsimp only
  have hroot : 1 ≤ Real.sqrt (12/11 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  rw [Real.sqrt_div (show (0 : ℝ)≤12 by norm_num)] at hroot
  have hratio : (Real.sqrt (12 : ℝ)/Real.sqrt 11)^2=12/11 := by
    rw [div_pow, Real.sq_sqrt (show (0 : ℝ)≤12 by norm_num),
      Real.sq_sqrt (show (0 : ℝ)≤11 by norm_num)]
  have hl : late (negativeDeltaModel 1).pop=0 := by
    norm_num [late, groupMean, compliers, negativeDeltaModel, Fin.sum_univ_succ]
  have heps (a : Bool) : residual (negativeDeltaModel 1) a 0=
      fun i => if i.val % 2=0 then (-1 : ℝ) else 1 := by
    funext i
    simp only [residual, negative_delta_population_ols, dotProduct_zero, sub_zero]
    simp [w, negativeDeltaModel]
  have ht : Theta (negativeDeltaModel 1).pop (-1/2) (1/6) 2 := by
    simp only [Theta, hl]
    norm_num [ValidDesign, MonotoneReceipt, compliers, negativeDeltaModel,
      groupMean, groupCov, groupVar, mean, w, v, binary,
      fraction, controlSize, fourthNorm, popVar, Fin.sum_univ_succ]
    constructor <;> nlinarith [hratio]
  have hx : Xi (negativeDeltaModel 1) (-1/2) (1/2) 2 2 (1/6) := by
    simp only [Xi, hl, heps]
    norm_num [ValidDesign, MonotoneReceipt, compliers, negativeDeltaModel,
      dotProduct, mean, w, binary,
      normSq, popCov, fourthNorm, popVar, Fin.sum_univ_succ]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [hratio]
    · nlinarith
    · intro b
      nlinarith [sq_nonneg (b 0)]
  have hcard : (assignments (negativeDeltaModel 1).pop).card=66 := by
    norm_num [assignments, negativeDeltaModel] <;> decide
  have het : expectation (negativeDeltaModel 1).pop
      (tau (negativeDeltaModel 1).pop 0)=0 := by
    simp only [expectation, hcard]
    rw [negative_delta_assignments]
    simp (config := {maxSteps := 1000000}) (discharger := decide) only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty]
    norm_num (config := {maxSteps := 1000000}) [tau, rawTau_sum, fraction, negativeDeltaModel,
      observedW, observedY, observedD, binary, Fin.sum_univ_succ, Finset.sum_insert]
  have heo : expectation (negativeDeltaModel 1).pop
      (oracleTau (negativeDeltaModel 1) 0)=0 := by
    simp only [expectation, hcard]
    rw [negative_delta_assignments]
    simp only [oracleTau, adjustedWith, negative_delta_population_ols]
    simp (config := {maxSteps := 1000000}) (discharger := decide) only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty]
    norm_num (config := {maxSteps := 1000000}) [groupMean, slopeDot, fraction, negativeDeltaModel,
      observedW, observedY, observedD, binary, Fin.sum_univ_succ, Finset.sum_insert,
      sum_complement_eq, Finset.card_compl]
  have hvt : designVariance (negativeDeltaModel 1).pop
      (tau (negativeDeltaModel 1).pop 0)=5/396 := by
    simp only [designVariance, het, sub_zero]
    simp only [expectation, hcard]
    rw [negative_delta_assignments]
    simp (config := {maxSteps := 1000000}) (discharger := decide) only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty]
    norm_num (config := {maxSteps := 1000000}) [tau, rawTau_sum, fraction, negativeDeltaModel,
      observedW, observedY, observedD, binary, Fin.sum_univ_succ, Finset.sum_insert]
  have hvo : designVariance (negativeDeltaModel 1).pop
      (oracleTau (negativeDeltaModel 1) 0)=36/55 := by
    simp only [designVariance, heo, sub_zero]
    simp only [expectation, hcard]
    rw [negative_delta_assignments]
    simp only [oracleTau, adjustedWith, negative_delta_population_ols]
    simp (config := {maxSteps := 1000000}) (discharger := decide) only [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty]
    norm_num (config := {maxSteps := 1000000}) [groupMean, slopeDot, fraction, negativeDeltaModel,
      observedW, observedY, observedD, binary, Fin.sum_univ_succ, Finset.sum_insert,
      sum_complement_eq, Finset.card_compl]
  refine ⟨ht, hx, hl, ?_⟩
  simp only [hcard, hvt, hvo, heps]
  norm_num [S2, popVar, fraction, mean, w, binary,
    negativeDeltaModel, controlSize, Fin.sum_univ_succ]


/-- T1(e): the particular negative-delta weighted-AMGM step reverses the
inequality: (C.3)=12/11 while (C.4)=-36/55. This arithmetic is supplementary
to the complete design-based counterexample and does not alone prove the variance comparison. -/
theorem negative_delta_AMGM_failure :
    (12/11 : ℝ)+12/11+2*(-1/2)*12/11=12/11 ∧
    (12/11 : ℝ)+12/11+(-1/2)*(10/2)*(12/11)+(-1/2)*(2/10)*(12/11)= -36/55 ∧
    ¬((12/11 : ℝ) ≤ -36/55) := by
  norm_num

/-- Sample-centred square identity used before corrected (C.17), Supp. p. 26. -/
theorem square_centering {n} (S : Finset (Fin n)) (q : Fin n → ℝ) (c : ℝ)
    (hS : S.Nonempty) :
    groupMean S (fun i => (q i-groupMean S q)^2) =
      groupMean S (fun i => (q i-c)^2) - (groupMean S q-c)^2 := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hS)
  have he (b : ℝ) : groupMean S (fun i => (q i-b)^2) =
      groupMean S (fun i => q i^2)-2*b*groupMean S q+b^2 := by
    simp only [groupMean, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard]
    try simp only [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [he, he]
  ring


/-- T10's four-unit all-complier constant-effect model, P002-E004, Supp. p. 26. -/
def centringModel : Population 4 where
  y := fun i a => (if i.val < 2 then -1 else 1) + (if a then 2 else 0)
  d := fun _ a => a
  n1 := 2
/-- Explicit full assignment enumeration for the four-unit counterexample. -/
theorem centring_assignments : assignments centringModel = ({{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}} : Finset (Finset (Fin 4))) := by
  decide

/-- T10: every hypothesis holds, the printed identity gives -24 while the true
left side is 0; over all six assignments the printed squared bracket has mean 49/3. -/
theorem centring_counterexample :
    Theta centringModel 0 (1/2) 1 ∧ late centringModel = 2 ∧
    let S : Finset (Fin 4) := {0,1}
    S ∈ assignments centringModel ∧
    groupMean S (fun i => (observedW centringModel 2 S i-
      armMean (observedW centringModel 2 S) S true)^2) = 0 ∧
    groupMean S (fun i => v centringModel true 2 i^2) -
      (groupMean S (w centringModel true 2) -
        mean (fun i => centringModel.y i (centringModel.d i true)) -
        2*mean (fun i => binary (centringModel.d i true)))^2 = -24 ∧
    expectation centringModel (fun T => (groupMean T (w centringModel true 2) -
      mean (fun i => centringModel.y i (centringModel.d i true)) -
      2*mean (fun i => binary (centringModel.d i true)))^2) = 49/3 ∧
    controlSize centringModel/(2*4*(4-1))*∑ i, v centringModel true 2 i^2 = 1/3 := by
  have hTheta : Theta centringModel 0 (1/2) 1 := by
    norm_num [Theta, ValidDesign, MonotoneReceipt, compliers, centringModel,
      late, groupMean, groupCov, groupVar, mean, w, v, binary, fraction,
      controlSize, fourthNorm, popVar, Fin.sum_univ_succ, Real.one_le_sqrt]
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<3))).mpr
    nlinarith [Real.sq_sqrt (show (0 : ℝ)≤3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  refine ⟨hTheta, ?_, ?_⟩
  · norm_num [late, compliers, groupMean, centringModel, Fin.sum_univ_succ]
  · simp only [expectation, centring_assignments]
    simp (discharger := decide) only [Finset.sum_insert, Finset.sum_singleton,
      Finset.sum_empty, Finset.card_insert_of_notMem, Finset.card_singleton, Finset.card_empty]
    norm_num [observedW, observedY, observedD, armMean,
      groupMean, centringModel, w, v, mean, binary, expectation,
      controlSize, Fin.sum_univ_succ, Finset.sum_insert]

/-- T12 and T14's balanced sign population, every unit a complier with zero effect. -/
def signModel (m : ℕ) : Population (2*m) where
  y := fun i _ => if i.val < m then -1 else 1
  d := fun _ a => a
  n1 := m
/-- Full enumeration of the 70 reassignments in the (C.31) counterexample. -/
theorem C31_assignments : assignments (signModel 4) = ({{0,1,2,3}, {0,1,2,4}, {0,1,2,5}, {0,1,2,6}, {0,1,2,7}, {0,1,3,4}, {0,1,3,5}, {0,1,3,6}, {0,1,3,7}, {0,1,4,5}, {0,1,4,6}, {0,1,4,7}, {0,1,5,6}, {0,1,5,7}, {0,1,6,7}, {0,2,3,4}, {0,2,3,5}, {0,2,3,6}, {0,2,3,7}, {0,2,4,5}, {0,2,4,6}, {0,2,4,7}, {0,2,5,6}, {0,2,5,7}, {0,2,6,7}, {0,3,4,5}, {0,3,4,6}, {0,3,4,7}, {0,3,5,6}, {0,3,5,7}, {0,3,6,7}, {0,4,5,6}, {0,4,5,7}, {0,4,6,7}, {0,5,6,7}, {1,2,3,4}, {1,2,3,5}, {1,2,3,6}, {1,2,3,7}, {1,2,4,5}, {1,2,4,6}, {1,2,4,7}, {1,2,5,6}, {1,2,5,7}, {1,2,6,7}, {1,3,4,5}, {1,3,4,6}, {1,3,4,7}, {1,3,5,6}, {1,3,5,7}, {1,3,6,7}, {1,4,5,6}, {1,4,5,7}, {1,4,6,7}, {1,5,6,7}, {2,3,4,5}, {2,3,4,6}, {2,3,4,7}, {2,3,5,6}, {2,3,5,7}, {2,3,6,7}, {2,4,5,6}, {2,4,5,7}, {2,4,6,7}, {2,5,6,7}, {3,4,5,6}, {3,4,5,7}, {3,4,6,7}, {3,5,6,7}, {4,5,6,7}} : Finset (Finset (Fin 8))) := by
  decide

set_option maxHeartbeats 8000000 in
/-- T12: n=8, the original assignment treats all four -1 units. The actual
randomization variance is 1/28, while printed (C.31) demands at least 1/14. -/
theorem C31_counterexample :
    let P := signModel 4
    let S : Finset (Fin 8) := {0,1,2,3}
    Theta P 0 (1/2) 1 ∧ late P = 0 ∧ S ∈ assignments P ∧
    designVariance P (rawTau P (observedW P 0 S)) = 1/28 ∧
    (fraction P)^2*(1-fraction P)^2/(8-1) *
      (controlSize P*(P.n1 : ℝ)/8) *
      (armMean (observedW P 0 S) S true-armMean (observedW P 0 S) S false)^2 = 1/14 ∧
    designVariance P (rawTau P (observedW P 0 S)) <
      (fraction P)^2*(1-fraction P)^2/(8-1) *
      (controlSize P*(P.n1 : ℝ)/8) *
      (armMean (observedW P 0 S) S true-armMean (observedW P 0 S) S false)^2 := by
  dsimp only
  have hTheta : Theta (signModel 4) 0 (1/2) 1 := by
    norm_num [Theta, ValidDesign, MonotoneReceipt, compliers, signModel,
      late, groupMean, groupCov, groupVar, mean, w, v, binary, fraction,
      controlSize, fourthNorm, popVar, Fin.sum_univ_succ, Real.one_le_sqrt]
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<7))).mpr
    simpa using Real.sqrt_le_sqrt (show (7 : ℝ)≤8 by norm_num)
  refine ⟨hTheta, ?_, ?_⟩
  · norm_num [late, compliers, groupMean, signModel, Fin.sum_univ_succ]
  · have hc : ({0,1,2,3} : Finset (Fin 8))ᶜ = {4,5,6,7} := by decide
    simp only [designVariance, expectation, C31_assignments]
    simp (config := {maxSteps := 1000000}) (discharger := decide) only [Finset.sum_insert, Finset.sum_singleton,
      Finset.sum_empty, Finset.card_insert_of_notMem, Finset.card_singleton, Finset.card_empty]
    norm_num (config := {maxSteps := 1000000}) [hc, designVariance, expectation, rawTau_sum,
      observedW, observedY, observedD, signModel, fraction, controlSize,
      armMean, groupMean, binary, Fin.sum_univ_succ, Finset.sum_insert,
      Finset.filter_insert, Finset.filter_empty]


/-- T8's centered alternating covariate example (n=2,k=1), P002-E010.
It satisfies Assumption 5(iii)-(v) with A=16, epsilon-tilde=2. -/
def interceptExampleX (i : Fin 2) (_ : Fin 1) : ℝ := if i = 0 then 2 else -2
/-- T8: the covariate Gram is 4, but the augmented intercept direction has
Rayleigh quotient 1<2. This refutes the eigenvalue implication, not Lemma 19. -/
theorem intercept_eigenvalue_counterexample :
    (∀ s, ∑ i, interceptExampleX i s = 0) ∧
    (∀ s, mean (fun i => interceptExampleX i s^4) = 16) ∧
    (∀ b : Fin 1 → ℝ, 2*normSq b ≤ mean (fun i => (dotProduct (interceptExampleX i) b)^2)) ∧
    let v : Option (Fin 1) → ℝ := fun j => if j = none then 1 else 0
    mean (fun i => (dotProduct (augmented interceptExampleX i) v)^2) = 1 ∧
    normSq v = 1 ∧
    mean (fun i => (dotProduct (augmented interceptExampleX i) v)^2) < 2*normSq v := by
  norm_num [interceptExampleX, mean, normSq, augmented, dotProduct,
    Fin.sum_univ_succ, Fintype.sum_option]
  intro b
  nlinarith [sq_nonneg (b 0)]

/-- T9: exact corrected augmented-Gram bound. Under centered covariates and the
Rayleigh form of Assumption 5(v), the intercept adds a 1 block and changes the
lower bound to min(1,epsilon-tilde), for every vector in R^(k+1). -/
theorem corrected_augmented_gram {n k} (x : Fin n → Fin k → ℝ)
    (hn : 0 < n) (e : ℝ) (hx : ∀ s, ∑ i, x i s = 0)
    (he : ∀ b : Fin k → ℝ, e*normSq b ≤ mean (fun i => (dotProduct (x i) b)^2)) :
    (gram x Finset.univ) none none = 1 ∧
    (∀ s, (gram x Finset.univ) none (some s) = 0 ∧
          (gram x Finset.univ) (some s) none = 0) ∧
    (∀ s t, (gram x Finset.univ) (some s) (some t) = mean (fun i => x i s*x i t)) ∧
    (∀ b : Option (Fin k) → ℝ,
      min 1 e * normSq b ≤ mean (fun i => (dotProduct (augmented x i) b)^2)) := by
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [gram, groupMean, augmented, hN]
  · intro t
    constructor <;> simp [gram, groupMean, augmented, hx]
  · intro t u
    simp [gram, groupMean, augmented, mean]
  · intro b
    let z : Fin n → ℝ := fun i => dotProduct (x i) (fun t => b (some t))
    have hz : ∑ i, z i=0 := by
      dsimp [z, dotProduct]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hx, zero_mul]
      simp
    have hd (i : Fin n) : dotProduct (augmented x i) b=b none+z i := by
      simp [dotProduct, Fintype.sum_option, augmented, z]
    have hm : mean (fun i => (dotProduct (augmented x i) b)^2)=b none^2+mean (fun i => z i^2) := by
      simp_rw [hd, add_sq]
      simp only [mean, Finset.sum_add_distrib, Finset.sum_mul, ← Finset.mul_sum,
        hz, mul_zero, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      field_simp [hN]
      <;> ring
    have hb := he (fun t => b (some t))
    change e*(∑ t, b (some t)^2) ≤ mean (fun i => z i^2) at hb
    have hh : 0 ≤ ∑ t, b (some t)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hmin : min 1 e ≤ e := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right hmin hh
    have hconst := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) e) (sq_nonneg (b none))
    rw [hm]
    simp only [normSq, Fintype.sum_option]
    nlinarith

/-- Smallest eigenvalue of a real symmetric Gram matrix, via the equivalent
minimum unit-vector Rayleigh quotient (main Assumption 5(v)). -/
def leastRayleigh {n k} (x : Fin n → Fin k → ℝ) : ℝ :=
  sInf {t | ∃ b : Fin k → ℝ, normSq b=1 ∧ mean (fun i => (dotProduct (x i) b)^2)=t}
/-- The minimum unit-vector Rayleigh quotient bounds the quadratic form
on every vector by homogeneity. This is the finite spectral fact used in
Assumption 5(v) and corrected T9, Supplement p. 42. -/
theorem leastRayleigh_lower {n k} (x : Fin n → Fin k → ℝ)
    (b : Fin k → ℝ) :
    leastRayleigh x*normSq b ≤ mean (fun i => (dotProduct (x i) b)^2) := by
  let R : Set ℝ := {t | ∃ v : Fin k → ℝ, normSq v=1 ∧
    mean (fun i => (dotProduct (x i) v)^2)=t}
  have hbdd : BddBelow R := by
    refine ⟨0, ?_⟩
    rintro t ⟨v, hv, rfl⟩
    exact div_nonneg (Finset.sum_nonneg fun i hi => sq_nonneg _) (Nat.cast_nonneg _)
  have hnorm : 0 ≤ normSq b := Finset.sum_nonneg fun i hi => sq_nonneg _
  have hscaleN (a : ℝ) : normSq (a • b)=a^2*normSq b := by
    simp only [normSq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  have hscaleQ (a : ℝ) : mean (fun i => (dotProduct (x i) (a • b))^2)=
      a^2*mean (fun i => (dotProduct (x i) b)^2) := by
    simp only [dotProduct_smul, smul_eq_mul, mul_pow, mean, ← Finset.mul_sum]
    ring
  by_cases hz : normSq b=0
  · rw [hz, mul_zero]
    exact div_nonneg (Finset.sum_nonneg fun i hi => sq_nonneg _) (Nat.cast_nonneg _)
  · let t := Real.sqrt (normSq b)
    have ht : 0 < t := Real.sqrt_pos.mpr (lt_of_le_of_ne hnorm (Ne.symm hz))
    have htne : t ≠ 0 := ne_of_gt ht
    have ht2 : t^2=normSq b := Real.sq_sqrt hnorm
    have hunit : normSq (t⁻¹ • b)=1 := by
      rw [hscaleN, ← ht2]
      field_simp [htne]
    have hm : mean (fun i => (dotProduct (x i) (t⁻¹ • b))^2) ∈ R :=
      ⟨t⁻¹ • b, hunit, rfl⟩
    have hl : leastRayleigh x ≤ mean (fun i => (dotProduct (x i) (t⁻¹ • b))^2) :=
      csInf_le hbdd hm
    rw [hscaleQ] at hl
    have hh := mul_le_mul_of_nonneg_right hl (sq_nonneg t)
    have hc : (t⁻¹)^2*mean (fun i => (dotProduct (x i) b)^2)*t^2=
        mean (fun i => (dotProduct (x i) b)^2) := by
      field_simp [htne]
    rw [hc, ht2] at hh
    exact hh

/-- T9's exact spectral identity: centered covariates give augmented minimum
eigenvalue min(1,lambda_min), not lambda_min alone. -/
theorem corrected_min_eigenvalue {n k} (x : Fin n → Fin k → ℝ)
    (hn : 0 < n) (hk : 0 < k) (hx : ∀ s, ∑ i, x i s=0) :
    sInf {t | ∃ b : Option (Fin k) → ℝ, normSq b=1 ∧
      mean (fun i => (dotProduct (augmented x i) b)^2)=t} = min 1 (leastRayleigh x) := by
  let R : Set ℝ := {t | ∃ b : Option (Fin k) → ℝ, normSq b=1 ∧
    mean (fun i => (dotProduct (augmented x i) b)^2)=t}
  let C : Set ℝ := {t | ∃ b : Fin k → ℝ, normSq b=1 ∧
    mean (fun i => (dotProduct (x i) b)^2)=t}
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hRbdd : BddBelow R := by
    refine ⟨0, ?_⟩
    rintro t ⟨b, hb, rfl⟩
    exact div_nonneg (Finset.sum_nonneg fun i hi => sq_nonneg _) (Nat.cast_nonneg _)
  let e : Option (Fin k) → ℝ := fun j => if j=none then 1 else 0
  have henorm : normSq e=1 := by simp [normSq, e, Fintype.sum_option]
  have heform : mean (fun i => (dotProduct (augmented x i) e)^2)=1 := by
    simp [dotProduct, augmented, e, Fintype.sum_option, mean, hN]
  have he : (1 : ℝ) ∈ R := ⟨e, henorm, heform⟩
  have hRne : R.Nonempty := ⟨1, he⟩
  let v : Fin k → ℝ := fun j => if j=⟨0, hk⟩ then 1 else 0
  have hvnorm : normSq v=1 := by simp [normSq, v]
  have hCne : C.Nonempty :=
    ⟨mean (fun i => (dotProduct (x i) v)^2), v, hvnorm, rfl⟩
  change sInf R=min 1 (sInf C)
  apply le_antisymm
  · apply le_min
    · exact csInf_le hRbdd he
    · apply le_csInf hCne
      rintro t ⟨b, hb, hbt⟩
      let a : Option (Fin k) → ℝ := fun j => match j with
        | none => 0
        | some s => b s
      have hanorm : normSq a=1 := by simpa [normSq, a, Fintype.sum_option] using hb
      have haform : mean (fun i => (dotProduct (augmented x i) a)^2)=t := by
        simpa [dotProduct, augmented, a, Fintype.sum_option] using hbt
      exact csInf_le hRbdd ⟨a, hanorm, haform⟩
  · apply le_csInf hRne
    rintro t ⟨b, hb, rfl⟩
    have H := (corrected_augmented_gram x hn (leastRayleigh x) hx
      (leastRayleigh_lower x)).2.2.2 b
    simpa only [hb, mul_one, leastRayleigh] using H

/-- Corrected almost-sure eigenvalue step of T9: convergence of the sample Gram
in quadratic form implies a min(1,e)+o(1) bound, uniformly in the coefficient error.
The error sequence is supplied explicitly, avoiding an unspecified o(1) symbol. -/
theorem corrected_gram_perturbation {ι : Type*} [Fintype ι]
    (G : Matrix ι ι ℝ) (H : ℕ → Matrix ι ι ℝ) (e : ℝ) (err : ℕ → ℝ)
    (hG : ∀ b, min 1 e*normSq b ≤ dotProduct b (G *ᵥ b))
    (hH : ∀ j b, |dotProduct b ((H j-G) *ᵥ b)| ≤ err j*normSq b)
    (herr : Tendsto err atTop (nhds 0)) :
    Tendsto (fun j => -err j) atTop (nhds 0) ∧
    ∀ j b, (min 1 e-err j)*normSq b ≤ dotProduct b (H j *ᵥ b) := by
  refine ⟨?_, ?_⟩
  · simpa only [neg_zero] using herr.neg
  intro j b
  have hh := (abs_le.mp (hH j b)).1
  have hg := hG b
  simp only [Matrix.sub_mulVec, dotProduct_sub] at hh
  nlinarith

/-- T16's nonsingular four-row covariate array, P002-E007, Supplement (E.14). -/
def coordinateExample (i : Fin 4) (s : Fin 2) : ℝ :=
  if i.val = 0 then (if s.val = 0 then 1 else 0)
  else if i.val = 1 then (if s.val = 0 then -1 else 0)
  else if i.val = 2 then (if s.val = 1 then 1 else 0)
  else (if s.val = 1 then -1 else 0)
/-- Full finite-population extension of T16's covariate array. All units are
compliers with zero treatment effect and residual outcomes (1,1,-1,-1), so
this counterexample can satisfy all of Xi's standing hypotheses as well. -/
def coordinateModel : CovPopulation 4 2 where
  pop := {y := fun i _ => if i.val < 2 then 1 else -1, d := fun _ a => a, n1 := 2}
  x := coordinateExample
/-- Population OLS of the coordinate counterexample has zero coefficients. -/
theorem coordinate_population_ols (a : Bool) : psi coordinateModel a 0=0 := by
  have hg : gram coordinateModel.x Finset.univ =
      Matrix.diagonal (fun s : Option (Fin 2) => if s=none then 1 else (1/2 : ℝ)) := by
    ext s t
    rcases s with _ | s <;> rcases t with _ | t
    · norm_num [gram, groupMean, augmented, coordinateModel, coordinateExample,
        Matrix.diagonal_apply, Fin.sum_univ_succ]
    · fin_cases t <;> norm_num [gram, groupMean, augmented, coordinateModel,
        coordinateExample, Matrix.diagonal_apply, Fin.sum_univ_succ]
    · fin_cases s <;> norm_num [gram, groupMean, augmented, coordinateModel,
        coordinateExample, Matrix.diagonal_apply, Fin.sum_univ_succ]
    · fin_cases s <;> fin_cases t <;> norm_num [gram, groupMean, augmented,
        coordinateModel, coordinateExample, Matrix.diagonal_apply, Fin.sum_univ_succ]
  have hdet : (gram coordinateModel.x Finset.univ).det ≠ 0 := by
    rw [hg, Matrix.det_diagonal]
    norm_num [Fintype.prod_option, Fin.prod_univ_succ]
  have hs : score coordinateModel.x Finset.univ (w coordinateModel.pop a 0)=0 := by
    ext s
    rcases s with _ | s
    · norm_num [score, groupMean, augmented, w, coordinateModel, coordinateExample,
        binary, Fin.sum_univ_succ]
    · fin_cases s <;> norm_num [score, groupMean, augmented, w, coordinateModel,
        coordinateExample, binary, Fin.sum_univ_succ]
  simp [psi, ols, hdet, hs]
/-- The full T16 population obeys Assumptions 1,2,4,5 with explicit constants. -/
theorem coordinate_example_admissible : Xi coordinateModel 0 (1/2) 1 1 (1/2) := by
  have hl : late coordinateModel.pop=0 := by
    norm_num [late, groupMean, compliers, coordinateModel, Fin.sum_univ_succ]
  have hr (a : Bool) : residual coordinateModel a 0=
      fun i => if i.val < 2 then (1 : ℝ) else -1 := by
    funext i
    simp only [residual, coordinate_population_ols, dotProduct_zero, sub_zero]
    simp [w, coordinateModel]
  simp only [Xi, hl, hr]
  norm_num [ValidDesign, MonotoneReceipt, compliers, coordinateModel,
    coordinateExample, dotProduct, mean,
    w, binary, normSq, popCov, fourthNorm, popVar, Fin.sum_univ_succ, Real.one_le_sqrt]
  constructor
  · apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<3))).mpr
    nlinarith [Real.sq_sqrt (show (0 : ℝ)≤3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  · intro b
    nlinarith

/-- Finite maximum of a nonnegative array, with zero adjoined only for the empty array.
This is the paper's max for every positive population size. -/
def maximum {n} (q : Fin n → ℝ) : ℝ := (insert 0 (Finset.univ.image q)).max' (by simp)
/-- Every coordinate is below the finite maximum (supporting corrected (E.14)). -/
theorem le_maximum {n} (q : Fin n → ℝ) (i : Fin n) : q i ≤ maximum q := by
  unfold maximum
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
/-- A coordinatewise upper bound and a nonnegative bound control the finite maximum. -/
theorem maximum_le {n} (q : Fin n → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hq : ∀ i, q i ≤ b) : maximum q ≤ b := by
  unfold maximum
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_insert.mp hy with h | h
  · simpa [h] using hb
  · rcases Finset.mem_image.mp h with ⟨i, hi, rfl⟩
    exact hq i

/-- T16: the maximum augmented squared norm is 2, whereas one plus the sum of
coordinate squared maxima is 3; centered covariates have Gram (1/2) I. -/
theorem maximum_counterexample :
    Xi coordinateModel 0 (1/2) 1 1 (1/2) ∧
    (∀ s, ∑ i, coordinateExample i s = 0) ∧
    (∀ s, mean (fun i => coordinateExample i s^4) = 1/2) ∧
    (∀ s t, mean (fun i => coordinateExample i s*coordinateExample i t) =
      if s=t then 1/2 else 0) ∧
    maximum (fun i => normSq (augmented coordinateExample i)) = 2 ∧
    1 + (∑ s, maximum (fun i => coordinateExample i s^2)) = 3 := by
  have hn (i : Fin 4) : normSq (augmented coordinateExample i)=2 := by
    simp only [normSq, Fintype.sum_option, augmented, Fin.sum_univ_succ]
    fin_cases i <;> norm_num [coordinateExample]
  have hnorm : maximum (fun i => normSq (augmented coordinateExample i))=2 := by
    apply le_antisymm
    · exact maximum_le _ 2 (by norm_num) (fun i => (hn i).le)
    · have h := le_maximum (fun i => normSq (augmented coordinateExample i)) 0
      rw [hn 0] at h
      exact h
  have hm (s : Fin 2) : maximum (fun i => coordinateExample i s^2)=1 := by
    apply le_antisymm
    · apply maximum_le _ 1 (by norm_num)
      intro i
      fin_cases s <;> fin_cases i <;> norm_num [coordinateExample]
    · fin_cases s
      · calc
          1 = coordinateExample (0 : Fin 4) (0 : Fin 2)^2 := by norm_num [coordinateExample]
          _ ≤ _ := le_maximum (fun i => coordinateExample i 0^2) 0
      · calc
          1 = coordinateExample (2 : Fin 4) (1 : Fin 2)^2 := by norm_num [coordinateExample]
          _ ≤ _ := le_maximum (fun i => coordinateExample i 1^2) 2
  refine ⟨coordinate_example_admissible, ?_, ?_, ?_, hnorm, ?_⟩
  · intro s
    fin_cases s <;> norm_num [coordinateExample, Fin.sum_univ_succ]
  · intro s
    fin_cases s <;> norm_num [coordinateExample, mean, Fin.sum_univ_succ]
  · intro s t
    fin_cases s <;> fin_cases t <;> norm_num [coordinateExample, mean, Fin.sum_univ_succ]
  · norm_num [hm, Fin.sum_univ_succ]

/-- T17: corrected (E.14), explicit finite bounds on the coordinate maxima and
on the augmented squared norm, with exactly Assumption 5(iv). -/
theorem corrected_E14 {n k} (x : Fin n → Fin k → ℝ) (hn : 0 < n)
    (A : ℝ) (hA : 0 ≤ A) (hx : ∀ s, mean (fun i => x i s^4) ≤ A) :
    (∀ s, maximum (fun i => |x i s|) ≤ Real.sqrt (Real.sqrt (A*(n : ℝ)))) ∧
    maximum (fun i => normSq (augmented x i)) ≤
      1 + (∑ s, maximum (fun i => x i s^2)) ∧
    1 + (∑ s, maximum (fun i => x i s^2)) ≤ 1 + (k : ℝ)*Real.sqrt (A*(n : ℝ)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum (s : Fin k) : (∑ i, x i s^4) ≤ A*(n : ℝ) := by
    exact (div_le_iff₀ hN).mp (hx s)
  have hfour (i : Fin n) (s : Fin k) : x i s^4 ≤ A*(n : ℝ) := by
    calc
      x i s^4 ≤ ∑ j, x j s^4 := Finset.single_le_sum (f := fun j : Fin n => x j s^4) (fun j _ => by positivity) (Finset.mem_univ i)
      _ ≤ _ := hsum s
  have hsq (i : Fin n) (s : Fin k) : x i s^2 ≤ Real.sqrt (A*(n : ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [← pow_mul] using hfour i s
  have habs (i : Fin n) (s : Fin k) : |x i s| ≤ Real.sqrt (Real.sqrt (A*(n : ℝ))) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [sq_abs] using hsq i s
  have hm (s : Fin k) : maximum (fun i => x i s^2) ≤ Real.sqrt (A*(n : ℝ)) :=
    maximum_le _ _ (Real.sqrt_nonneg _) (fun i => hsq i s)
  have hm0 (s : Fin k) : 0 ≤ maximum (fun i => x i s^2) := by
    unfold maximum
    apply Finset.le_max'
    exact Finset.mem_insert_self _ _
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact maximum_le _ _ (Real.sqrt_nonneg _) (fun i => habs i s)
  · apply maximum_le (fun i => normSq (augmented x i))
    · exact add_nonneg (by norm_num) (Finset.sum_nonneg (fun s _ => hm0 s))
    · intro i
      simp only [normSq, Fintype.sum_option, augmented, one_pow]
      exact add_le_add (le_refl 1) (Finset.sum_le_sum (fun s _ => le_maximum (fun j => x j s^2) i))
  · have H := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin k))) => hm s)
    simpa using add_le_add (le_refl 1) H

/-- T17's order statement: for fixed k and A, the maximum augmented squared
norm is O(sqrt(n)) for every sequence obeying Assumption 5(iv), Supplement
p. 35 (E.14). Starting at n=1 removes only the empty population index. -/
theorem corrected_E14_order (k : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (x : ∀ j, Fin (j+1) → Fin k → ℝ)
    (hx : ∀ j s, mean (fun i => x j i s^4) ≤ A) :
    Asymptotics.IsBigO atTop (fun j => maximum (fun i => normSq (augmented (x j) i)))
      (fun j => Real.sqrt ((j+1 : ℕ) : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨1+(k : ℝ)*Real.sqrt A, Filter.Eventually.of_forall ?_⟩
  intro j
  have H := corrected_E14 (x j) (by omega) A hA (hx j)
  have hb := H.2.1.trans H.2.2
  have hm : 0 ≤ maximum (fun i => normSq (augmented (x j) i)) := by
    unfold maximum
    apply Finset.le_max'
    exact Finset.mem_insert_self _ _
  have hr : 1 ≤ Real.sqrt ((j+1 : ℕ) : ℝ) := by
    apply Real.one_le_sqrt.mpr
    exact_mod_cast (by omega : 1 ≤ j+1)
  simp only [Real.norm_eq_abs, abs_of_nonneg hm, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sqrt_mul hA] at hb
  nlinarith

/-- Observed adjusted outcomes equal the treatment potential vector on the treated arm. -/
theorem observedW_treated {n} (P : Population n) (β : ℝ) (S : Finset (Fin n))
    (i : Fin n) (hi : i ∈ S) : observedW P β S i=w P true β i := by
  simp [observedW, observedY, observedD, w, hi]
/-- Observed adjusted outcomes equal the control potential vector on the control arm. -/
theorem observedW_control {n} (P : Population n) (β : ℝ) (S : Finset (Fin n))
    (i : Fin n) (hi : i ∈ Sᶜ) : observedW P β S i=w P false β i := by
  have hn : i ∉ S := Finset.mem_compl.mp hi
  simp [observedW, observedY, observedD, w, hn]
/-- Finite arm means depend only on outcomes in that arm. -/
theorem groupMean_congr {n} (S : Finset (Fin n)) (q t : Fin n → ℝ)
    (h : ∀ i ∈ S, q i=t i) : groupMean S q=groupMean S t := by
  unfold groupMean
  rw [Finset.sum_congr rfl h]
/-- T11's corrected finite centring identity on the actual observed treatment
arm, Supplement p. 26. The bracket is sample w minus mean y plus beta mean d.
No population or sample variance formula is assumed in this proof. -/
theorem corrected_C17_identity {n} (P : Population n) (hP : ValidDesign P) (β : ℝ)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    groupMean S (fun i => (observedW P β S i-armMean (observedW P β S) S true)^2) =
      groupMean S (fun i => v P true β i^2) -
        (groupMean S (w P true β)-mean (fun i => P.y i (P.d i true)) +
          β*mean (fun i => binary (P.d i true)))^2 := by
  have hsz : S.card=P.n1 := (Finset.mem_powersetCard.mp hS).2
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hsz]; exact hP.2.1)
  have hw : groupMean S (observedW P β S)=groupMean S (w P true β) :=
    groupMean_congr S _ _ (fun i hi => observedW_treated P β S i hi)
  have hleft : groupMean S (fun i => (observedW P β S i-armMean (observedW P β S) S true)^2) =
      groupMean S (fun i => (w P true β i-groupMean S (w P true β))^2) := by
    apply groupMean_congr
    intro i hi
    simp only [armMean, if_true, hw, observedW_treated P β S i hi]
  have hm : mean (w P true β)=mean (fun i => P.y i (P.d i true))-
      β*mean (fun i => binary (P.d i true)) := mean_sub_smul _ _ β
  have hb : groupMean S (w P true β)-mean (w P true β)=
      groupMean S (w P true β)-mean (fun i => P.y i (P.d i true)) +
        β*mean (fun i => binary (P.d i true)) := by rw [hm]; ring
  rw [hleft]
  simpa only [v, hb] using square_centering S (w P true β) (mean (w P true β)) hSne

/-- Within-group variance is bounded by the second moment about any center,
the exact finite projection inequality (C.7) supporting corrected Lemma 5. -/
theorem group_variance_second_moment {n} (S : Finset (Fin n)) (q : Fin n → ℝ)
    (c : ℝ) (hS : 2 ≤ S.card) :
    groupVar S q ≤ (∑ i ∈ S, (q i-c)^2)/((S.card : ℝ)-1) := by
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hden : 0 ≤ (S.card : ℝ)-1 := by
    have h : (1 : ℝ) ≤ S.card := by exact_mod_cast (show 1 ≤ S.card by omega)
    linarith
  have hm : groupMean S (fun i => (q i-groupMean S q)^2) ≤ groupMean S (fun i => (q i-c)^2) := by
    rw [square_centering S q c hSne]
    exact sub_le_self _ (sq_nonneg _)
  have hs : (∑ i ∈ S, (q i-groupMean S q)^2) ≤ ∑ i ∈ S, (q i-c)^2 :=
    (div_le_div_iff_of_pos_right hcard).mp hm
  simp only [groupVar, groupCov, if_pos hS]
  have hp : (∑ i ∈ S, (q i-groupMean S q)*(q i-groupMean S q)) =
      ∑ i ∈ S, (q i-groupMean S q)^2 := by apply Finset.sum_congr rfl; intro i hi; ring
  rw [hp]
  exact div_le_div_of_nonneg_right hs hden
/-- OLS scores depend only on outcomes in the fitted arm. -/
theorem score_congr {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n))
    (q t : Fin n → ℝ) (h : ∀ i ∈ S, q i=t i) : score x S q=score x S t := by
  ext s
  apply groupMean_congr
  intro i hi
  rw [h i hi]
/-- x-circ omits the intercept, so its dot product equals the slope contribution. -/
theorem dot_xCirc {n k} (x : Fin n → Fin k → ℝ) (i : Fin n)
    (c : Option (Fin k) → ℝ) : dotProduct (xCirc x i) c=slopeDot (x i) c := by
  simp [dotProduct, xCirc, slopeDot, Fintype.sum_option]

/-- T18: corrected inverse-Gram expansion (E.21)-(E.23), valid for full-rank arms. -/
theorem corrected_E21_E23 {n k} (P : CovPopulation n k) (β : ℝ) (S : Finset (Fin n))
    (hS : S ∈ assignments P.pop) (h1 : (gram P.x S).det ≠ 0)
    (h0 : (gram P.x Sᶜ).det ≠ 0) :
    adjustedTau P (observedW P.pop β S) S - oracleTau P β S =
      -groupMean S (fun i => dotProduct (xCirc P.x i)
        ((gram P.x S)⁻¹ *ᵥ score P.x S (residual P true β))) +
       groupMean Sᶜ (fun i => dotProduct (xCirc P.x i)
        ((gram P.x Sᶜ)⁻¹ *ᵥ score P.x Sᶜ (residual P false β))) := by
  have h1e : fitted P (observedW P.pop β S) S true-psi P true β =
      (gram P.x S)⁻¹ *ᵥ score P.x S (residual P true β) := by
    change ols P.x S (observedW P.pop β S)-psi P true β = _
    rw [ols_error _ _ _ _ h1]
    congr 1
    apply score_congr
    intro i hi
    rw [observedW_treated _ _ _ _ hi]
    rfl
  have h0e : fitted P (observedW P.pop β S) S false-psi P false β =
      (gram P.x Sᶜ)⁻¹ *ᵥ score P.x Sᶜ (residual P false β) := by
    change ols P.x Sᶜ (observedW P.pop β S)-psi P false β = _
    rw [ols_error _ _ _ _ h0]
    congr 1
    apply score_congr
    intro i hi
    rw [observedW_control _ _ _ _ hi]
    rfl
  rw [corrected_adjusted_difference, h1e, h0e]
  simp only [dot_xCirc]

/-- Full-rank OLS satisfies its finite normal equations (Supplement Lemma 14). -/
theorem ols_normal_equations {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n))
    (q : Fin n → ℝ) (h : (gram x S).det ≠ 0) :
    gram x S *ᵥ ols x S q=score x S q := by
  simp only [ols, if_pos h, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h), Matrix.one_mulVec]
/-- Centering the covariates makes the population OLS intercept equal its
response mean, Supplement p. 37 (used in the corrected oracle expansion). -/
theorem population_intercept_mean {n k} (x : Fin n → Fin k → ℝ) (q : Fin n → ℝ)
    (hn : 0 < n) (hx : ∀ s, ∑ i, x i s=0) (hg : (gram x Finset.univ).det ≠ 0) :
    ols x Finset.univ q none=mean q := by
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnone : gram x Finset.univ none none=1 := by simp [gram, groupMean, augmented, hN]
  have hoff (s : Fin k) : gram x Finset.univ none (some s)=0 := by
    simp [gram, groupMean, augmented, hx]
  have H := congrFun (ols_normal_equations x Finset.univ q hg) none
  simpa [Matrix.mulVec, dotProduct, Fintype.sum_option, hnone, hoff, score,
    groupMean, augmented, mean] using H
/-- Finite arm means of q plus a constant, for a nonempty arm. -/
theorem groupMean_add_const {n} (S : Finset (Fin n)) (q : Fin n → ℝ) (c : ℝ)
    (hS : S.Nonempty) : groupMean S (fun i => q i+c)=groupMean S q+c := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hS)
  simp only [groupMean, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp [hcard]
  <;> ring

/-- T20(ii): corrected oracle expansion at the LATE, with treatment and control
indicators inside their respective sums, and equal population intercepts. -/
theorem corrected_oracle_expansion {n k} (P : CovPopulation n k)
    (hP : ValidDesign P.pop) (hm : MonotoneReceipt P.pop)
    (hc : (compliers P.pop).Nonempty) (hx : ∀ s, ∑ i, P.x i s = 0)
    (hg : (gram P.x Finset.univ).det ≠ 0)
    (S : Finset (Fin n)) (hS : S ∈ assignments P.pop) :
    psi P true (late P.pop) none = psi P false (late P.pop) none ∧
    oracleTau P (late P.pop) S = groupMean S (residual P true (late P.pop)) -
      groupMean Sᶜ (residual P false (late P.pop)) := by
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hP.1
  have hphi (a : Bool) : psi P a (late P.pop) none=mean (w P.pop a (late P.pop)) :=
    population_intercept_mean P.x _ hn hx hg
  have hphieq : psi P true (late P.pop) none=psi P false (late P.pop) none := by
    rw [hphi, hphi, mean_w_equal_at_late P.pop hm hc]
  have hsizes : S.card=P.pop.n1 := (Finset.mem_powersetCard.mp hS).2
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hsizes]; exact hP.2.1)
  have hCne : Sᶜ.Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_compl, Fintype.card_fin, hsizes]
    exact Nat.sub_pos_of_lt hP.2.2)
  have h1w : groupMean S (fun i => observedW P.pop (late P.pop) S i-
      slopeDot (P.x i) (psi P true (late P.pop))) =
      groupMean S (residual P true (late P.pop))+psi P true (late P.pop) none := by
    calc
      _ = groupMean S (fun i => residual P true (late P.pop) i+psi P true (late P.pop) none) := by
        apply groupMean_congr
        intro i hi
        rw [observedW_treated _ _ _ _ hi]
        simp only [residual, dotProduct, Fintype.sum_option, augmented, one_mul, slopeDot]
        ring
      _ = _ := groupMean_add_const _ _ _ hSne
  have h0w : groupMean Sᶜ (fun i => observedW P.pop (late P.pop) S i-
      slopeDot (P.x i) (psi P false (late P.pop))) =
      groupMean Sᶜ (residual P false (late P.pop))+psi P false (late P.pop) none := by
    calc
      _ = groupMean Sᶜ (fun i => residual P false (late P.pop) i+psi P false (late P.pop) none) := by
        apply groupMean_congr
        intro i hi
        rw [observedW_control _ _ _ _ hi]
        simp only [residual, dotProduct, Fintype.sum_option, augmented, one_mul, slopeDot]
        ring
      _ = _ := groupMean_add_const _ _ _ hCne
  refine ⟨hphieq, ?_⟩
  unfold oracleTau adjustedWith
  rw [h1w, h0w, hphieq]
  ring

/-- The sample-space infimum in Theorem 1, retaining its printed nested beta infimum.
Empty inner classes have value infinity, explicitly resolving the paper's omission. -/
def infCoverageTheta (n : ℕ) (δ r A α : ℝ) : ℝ≥0∞ :=
  ⨅ β : ℝ, ⨅ P : {P : Population n // Theta P δ r A ∧ late P = β},
    ENNReal.ofReal (coverage P.val β α)
/-- Nested coverage infimum of Theorem 2, with the same empty-class convention. -/
def infCoverageXi (n k : ℕ) (δ e A B r α : ℝ) : ℝ≥0∞ :=
  ⨅ β : ℝ, ⨅ P : {P : CovPopulation n k // Xi P δ e A B r ∧ late P.pop = β},
    ENNReal.ofReal (adjustedCoverage P.val β α)

/- T29: main Theorem 1 as printed. It asserts existence of the limit and nominal
sharpness for every admitted tuple of constants; T4 refutes that assertion. -/

/-- Moment-collapse algebra (P002-E001). This is a
supporting lemma, not by itself a counterexample to a coverage infimum. -/
theorem collapse_moments (N M2 M4 : ℝ) (hN : 2 ≤ N)
    (hCS : M2^2 ≤ N*M4) (hbound : 16*(N-1)^2*M4 ≤ N*M2^2) : M2 = 0 := by
  have hN0 : 0 ≤ N := by linarith
  have hc : 0 ≤ 16*(N-1)^2 := by positivity
  have hgap : 0 < 16*(N-1)^2-N^2 := by nlinarith [sq_nonneg (N-2)]
  have h1 := mul_le_mul_of_nonneg_left hCS hc
  have h2 := mul_le_mul_of_nonneg_left hbound hN0
  have hp : (16*(N-1)^2-N^2)*M2^2 ≤ 0 := by nlinarith [h1,h2]
  by_contra hne
  have hs : 0 < M2^2 := sq_pos_of_ne_zero hne
  have hpos := mul_pos hgap hs
  linarith
/-- Cauchy-Schwarz fourth-moment inequality for any finite vector, supporting T4(a). -/
theorem fourth_moment_CS (n : ℕ) (q : Fin n → ℝ) :
    (∑ i, q i^2)^2 ≤ (n : ℝ)*(∑ i, q i^4) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun i => q i^2) (fun _ => (1 : ℝ))
  have hp : ∀ i, (q i^2)^2 = q i^4 := by intro i; ring
  simpa [hp, mul_comm] using h
/-- T4(a): the actual printed fourth-root moment condition with constant 1/2
forces every coordinate to vanish for n≥2. -/
theorem half_moment_collapse {n} (q : Fin n → ℝ) (hn : 2 ≤ n)
    (hq : fourthNorm q ≤ (1/2)*Real.sqrt ((∑ i, q i^2)/((n : ℝ)-1))) :
    ∀ i, q i = 0 := by
  let N : ℝ := n
  let S2 : ℝ := ∑ i, q i^2
  let S4 : ℝ := ∑ i, q i^4
  have hN : 2 ≤ N := by dsimp [N]; exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have ht : 0 < N-1 := by linarith
  have h2 : 0 ≤ S2 := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  have h4 : 0 ≤ S4 := Finset.sum_nonneg fun i _ => by positivity
  have hq' : Real.sqrt (Real.sqrt (S4/N)) ≤ (1/2)*Real.sqrt (S2/(N-1)) := hq
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg (Real.sqrt (S4/N))) hq' 4
  have hroot : (Real.sqrt (Real.sqrt (S4/N)))^4 = S4/N := by
    calc
      _ = ((Real.sqrt (Real.sqrt (S4/N)))^2)^2 := by ring
      _ = (Real.sqrt (S4/N))^2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = S4/N := Real.sq_sqrt (div_nonneg h4 hN0.le)
  have hroot2 : ((1/2 : ℝ)*Real.sqrt (S2/(N-1)))^4 = S2^2/(16*(N-1)^2) := by
    rw [mul_pow]
    have hs : (Real.sqrt (S2/(N-1)))^4 = (S2/(N-1))^2 := by
      calc
        _ = ((Real.sqrt (S2/(N-1)))^2)^2 := by ring
        _ = (S2/(N-1))^2 := by rw [Real.sq_sqrt (div_nonneg h2 ht.le)]
    rw [hs]
    field_simp [ne_of_gt ht]
    <;> ring
  rw [hroot, hroot2] at hp
  have hb : 16*(N-1)^2*S4 ≤ N*S2^2 := by
    have H := (div_le_div_iff₀ hN0 (show 0 < 16*(N-1)^2 by positivity)).mp hp
    nlinarith [H]
  have hz : S2=0 := collapse_moments N S2 S4 hN (fourth_moment_CS n q) hb
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (q j))).mp hz i (Finset.mem_univ i)
  nlinarith [sq_nonneg (q i)]

/-- Assumption 3(ii) at A=1/2 forces the two LATE-adjusted potential vectors
to be the same constant, for every model in the entire class, P002-E001.
This is a class-wide statement, using actual potential outcomes and the LATE. -/
theorem theta_half_moment_constant {n} (P : Population n)
    (hP : Theta P 0 (1/4) (1/2)) :
    ∃ c : ℝ, ∀ a i, w P a (late P) i=c := by
  rcases hP with ⟨hD, hm, hc, _, _, _, hf⟩
  have hv (a : Bool) : ∀ i, v P a (late P) i=0 := by
    apply half_moment_collapse _ hD.1
    simpa only [popVar, v] using hf a
  have he := mean_w_equal_at_late P hm hc
  refine ⟨mean (w P false (late P)), ?_⟩
  intro a i
  have hi := hv a i
  dsimp only [v] at hi
  cases a
  · linarith
  · linarith

/-- Constant adjusted potential outcomes give the same observed vector on
every assignment (P002-E001), including assignments outside the design. -/
theorem observedW_constant {n} (P : Population n) (β c : ℝ)
    (hw : ∀ a i, w P a β i=c) (S : Finset (Fin n)) :
    observedW P β S=fun _ => c := by
  funext i
  change w P (decide (i ∈ S)) β i=c
  exact hw _ i

/-- A constant response has tau-hat zero on every complete-randomization
assignment; this uses n1 selected units and pi=n1/n, rather than assuming tau=0. -/
theorem rawTau_constant {n} (P : Population n) (hP : ValidDesign P) (c : ℝ)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    rawTau P (fun _ => c) S=0 := by
  have hsz : S.card=P.n1 := (Finset.mem_powersetCard.mp hS).2
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hP.1))
  have hcount : (∑ i : Fin n, (if i ∈ S then (1 : ℝ) else 0))=(P.n1 : ℝ) := by
    simp [Finset.sum_ite, Finset.filter_mem_eq_inter, hsz]
  simp only [rawTau, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hcount, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, fraction]
  field_simp [hN]
  <;> ring

/-- Diagnostic finite lemma for T15: the zero response has zero actual
design variance, and its auxiliary variance-ratio error probability is one at
kappa=1/2 with Lean's total real division. The paper only specifies 0/0 for
studentized statistics; this records the unresolved zero-denominator issue
without strengthening corrected Lemma 12's parameter class. -/
theorem zero_response_ratio_failure {n} (P : Population n) (hP : ValidDesign P) :
    designVariance P (rawTau P (fun _ => 0))=0 ∧
    probability P (fun S => |rawSigma2 P (fun _ => 0) S /
      designVariance P (rawTau P (fun _ => 0))-1| ≥ 1/2)=1 := by
  have hF : (assignments P).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa using Nat.le_of_lt hP.2.2
  have hcard : ((assignments P).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hF)
  norm_num [designVariance, expectation, rawTau, rawSigma2, armMean,
    groupMean, probability, hcard]

/-- Every model of Theta_n(0,1/4,1/2), n≥2, has finite coverage one at its
LATE. Only nonnegativity of the full randomization absolute cutoff is used;
the design probability is the actual finite count (P002-E001). -/
theorem theta_half_moment_coverage {n} (P : Population n)
    (hP : Theta P 0 (1/4) (1/2)) (α : ℝ) : coverage P (late P) α=1 := by
  obtain ⟨c,hc⟩ := theta_half_moment_constant P hP
  have hD := hP.1
  have htrue : ∀ S ∈ assignments P, accepted P (late P) α S := by
    intro S hS
    unfold accepted
    rw [observedW_constant P (late P) c hc S]
    have hz : rawAR P (fun _ => c) S=0 := by
      simp [rawAR, rawTau_constant P hD c S hS, absStudent]
    rw [hz]
    exact bot_le
  have hF : (assignments P).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa using Nat.le_of_lt hD.2.2
  have hcard : ((assignments P).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hF)
  unfold coverage probability
  rw [Finset.filter_eq_self.mpr htrue]
  exact div_self hcard

/-- Constant-effect model in `Theta_n(0,1/4,1/2)` for every `n ≥ 2`, used in T4(b). -/
def degenerateModel (n : ℕ) (β : ℝ) : Population n where
  y := fun _ a => if a then β else 0
  d := fun _ a => a
  n1 := n/2
/-- For every n≥2 and every real beta, the explicit all-complier model with
y(0)=0, y(1)=beta, n1=floor(n/2) belongs to the fixed class in T4(b).
This proves actual nonemptiness for each beta, not just for one estimand value. -/
theorem degenerate_model_admissible (n : ℕ) (hn : 2 ≤ n) (β : ℝ) :
    Theta (degenerateModel n β) 0 (1/4) (1/2) ∧ late (degenerateModel n β)=β := by
  let P := degenerateModel n β
  have hnp : 0 < n := by omega
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hnp
  have hc : compliers P=Finset.univ := by simp [compliers, P, degenerateModel]
  have hl : late P=β := by
    rw [late, groupMean, hc]
    simp [P, degenerateModel, hN]
  have hw (a : Bool) : w P a (late P)=0 := by
    funext i
    rw [hl]
    cases a <;> simp [w, P, degenerateModel, binary]
  have hv (a : Bool) : v P a (late P)=0 := by
    funext i
    simp [v, hw, mean]
  refine ⟨?_, hl⟩
  change Theta P 0 (1/4) (1/2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 2 ≤ n ∧ 0 < n/2 ∧ n/2 < n
    omega
  · intro i hi
    rfl
  · rw [hc]
    exact ⟨⟨0, hnp⟩, Finset.mem_univ _⟩
  · have H : n ≤ 4*(n/2) := by omega
    have H' : (n : ℝ) ≤ 4*((n/2 : ℕ) : ℝ) := by exact_mod_cast H
    change (1/4 : ℝ)*(n : ℝ) ≤ ((n/2 : ℕ) : ℝ)
    linarith
  · have H : 4*(n/2) ≤ 3*n := by omega
    have H' : 4*((n/2 : ℕ) : ℝ) ≤ 3*(n : ℝ) := by exact_mod_cast H
    change ((n/2 : ℕ) : ℝ) ≤ (1-(1/4 : ℝ))*(n : ℝ)
    linarith
  · simp [hw, groupCov, groupVar, groupMean]
  · intro a
    simp [hw, hv, fourthNorm, mean, popVar]
/-- T4(b): the entire fixed nonempty class has coverage one, for every n≥2 and
beta. This universal quantifier is essential: one coverage-one model does not
refute a worst-case infimum. The limit consequently differs from nominal coverage. -/
theorem theorem1_sharpness_counterexample (α : ℝ) (hα : 0 < α ∧ α < 1) :
    (∀ n, 2 ≤ n → ∀ β, Theta (degenerateModel n β) 0 (1/4) (1/2) ∧
      late (degenerateModel n β) = β) ∧
    (∀ n, 2 ≤ n → ∀ P : Population n, Theta P 0 (1/4) (1/2) →
      coverage P (late P) α = 1) ∧
    (∀ n, 2 ≤ n → infCoverageTheta n 0 (1/4) (1/2) α = 1) ∧
    Tendsto (fun n => infCoverageTheta n 0 (1/4) (1/2) α) atTop (nhds 1) ∧
    ¬Tendsto (fun n => infCoverageTheta n 0 (1/4) (1/2) α) atTop
      (nhds (ENNReal.ofReal (1-α))) := by
  have hi (n : ℕ) (hn : 2 ≤ n) : infCoverageTheta n 0 (1/4) (1/2) α=1 := by
    unfold infCoverageTheta
    apply le_antisymm
    · apply iInf_le_of_le (0 : ℝ)
      let Q : {Q : Population n // Theta Q 0 (1/4) (1/2) ∧ late Q=0} :=
        ⟨degenerateModel n 0, degenerate_model_admissible n hn 0⟩
      calc
        _ ≤ ENNReal.ofReal (coverage Q.val 0 α) := iInf_le _ Q
        _ = 1 := by
          have H : coverage Q.val 0 α=1 := by
            simpa only [Q.property.2] using theta_half_moment_coverage Q.val Q.property.1 α
          rw [H]
          simp
    · apply le_iInf
      intro β
      apply le_iInf
      intro Q
      have H : coverage Q.val β α=1 := by
        simpa only [Q.property.2] using theta_half_moment_coverage Q.val Q.property.1 α
      simp only [H, ENNReal.ofReal_one, le_refl]
  have heq : (fun n => infCoverageTheta n 0 (1/4) (1/2) α) =ᶠ[atTop] fun _ => 1 :=
    eventually_atTop.mpr ⟨2, fun n hn => hi n hn⟩
  have ht : Tendsto (fun n => infCoverageTheta n 0 (1/4) (1/2) α) atTop (nhds 1) :=
    (tendsto_congr' heq).mpr tendsto_const_nhds
  refine ⟨degenerate_model_admissible, ?_, hi, ht, ?_⟩
  · intro n hn P hP
    exact theta_half_moment_coverage P hP α
  · intro hbad
    have he := tendsto_nhds_unique ht hbad
    have hlt : ENNReal.ofReal (1-α) < 1 := ENNReal.ofReal_lt_one.mpr (by linarith [hα.1])
    exact (ne_of_lt hlt) he.symm
/-- Covariate grid x_i=(2i-n-1)/n, with i=1,...,n (P002-E001, T4(c)). -/
def gridX {n} (i : Fin n) (_ : Fin 1) : ℝ := (2*((i.val : ℝ)+1)-(n : ℝ)-1)/(n : ℝ)
/-- All-complier constant-effect models with the centered grid covariates, P002-E001, T4. -/
def degenerateCovModel (n : ℕ) (β : ℝ) : CovPopulation n 1 :=
  ⟨degenerateModel n β, gridX⟩

/-- A sequence of completely randomized assignment vectors with their exact
finite marginal laws. Every assignment-event preimage is required to be measurable.
The Supplement specifies mutual independence across population sizes (p. 27);
this definition imposes only the marginals and leaves the joint coupling unrestricted. -/
def RandomizationSequence {Ω : Type*} [MeasurableSpace Ω] {sizes : ℕ → ℕ}
    (P : ∀ j, Population (sizes j)) (μ : Measure Ω)
    (Z : ∀ j, Ω → Finset (Fin (sizes j))) : Prop :=
  ∀ j (E : Finset (Fin (sizes j)) → Prop),
    MeasurableSet {ω | E (Z j ω)} ∧
      μ {ω | E (Z j ω)} = ENNReal.ofReal (probability (P j) E)

/-- Standard normal absolute tail probability, Supplement p. 21, A.2. -/
def normalTail (x : ℝ) : ℝ := (ProbabilityTheory.gaussianReal 0 1 {z : ℝ | x ≤ |z|}).toReal
/-- z_{1-alpha/2}, normal quantile (Supplement p. 21). -/
def normalCritical (α : ℝ) : ℝ :=
  sInf {z : ℝ | ENNReal.ofReal (1-α/2) ≤ ProbabilityTheory.gaussianReal 0 1 (Set.Iic z)}

/-- Even subsequence (P002-E003): eta=2^(-n^2), two nearly coincident
covariate blocks, all units compliers with identical potential outcomes. -/
def nearSingularModel (m : ℕ) : CovPopulation (2*m) 1 :=
  let t : Fin (2*m) → ℝ := fun i => (2*(i.val % m : ℕ)-(m : ℝ)+1)/((m : ℝ)-1)
  let vm : ℝ := ((m : ℝ)+1)/(3*((m : ℝ)-1))
  let η : ℝ := 1/(2 : ℝ)^((2*m)^2)
  {pop := {y := fun i _ => t i+(1/10)*(t i^2-vm), d := fun _ a => a, n1 := m},
   x := fun i _ => (if i.val < m then 1 else -1)+η*t i}
/-- The odd-size extension of T6: distinct equally spaced x in [-1,1],
y=(x²-mean x²)/10, all units compliers, floor(n/2) treated. -/
def oddNearModel (n : ℕ) : CovPopulation n 1 :=
  let x : Fin n → Fin 1 → ℝ := fun i _ => 2*(i.val : ℝ)/((n : ℝ)-1)-1
  {pop := {y := fun i _ => (1/10)*(x i 0^2-mean (fun l => x l 0^2)),
           d := fun _ a => a, n1 := n/2}, x := x}

/-- Corrected control remainder (E.29), with (1-Z_i) in the leading arm mean. -/
def controlRemainder {n k} (P : CovPopulation n k) (S : Finset (Fin n)) : ℝ :=
  groupMean Sᶜ (fun i => dotProduct (xCirc P.x i)
    ((gram P.x Sᶜ)⁻¹ *ᵥ score P.x Sᶜ (residual P false (late P.pop)))) /
      Real.sqrt (designVariance P.pop (oracleTau P (late P.pop)))
/-- Uniform tail supremum over Xi and the printed nested beta index, corrected (E.36). -/
def supAdjustedTail (n k : ℕ) (δ e A B r α κ : ℝ) : ℝ≥0∞ :=
  ⨆ β : ℝ, ⨆ P : {P : CovPopulation n k // Xi P δ e A B r ∧ late P.pop = β},
    ENNReal.ofReal (probability P.val.pop (fun S =>
      (normalCritical α-κ < 0 ∨ adjustedAR P.val (observedW P.val.pop β S) S > ENNReal.ofReal (normalCritical α-κ))))

/-- T25(a): under a constant additive receipt effect, the adjusted observed
outcomes recover y_i(0) for every assignment. Main pp. 4-5, Section 3.1. -/
theorem constant_effect_adjusted_outcomes {n} (P : Population n) (β : ℝ)
    (hy : ∀ i, P.y i true = P.y i false + β) (S : Finset (Fin n)) :
    observedW P β S = fun i => P.y i false := by
  funext i
  unfold observedW observedY
  cases h : observedD P S i
  · simp [h, binary]
  · simp [h, binary, hy]

/-- Finite quantile validity, (6): the non-strict lower-tail acceptance has
probability at least 1-alpha for a full uniform randomization distribution. -/
theorem quantile_valid {n} (P : Population n) (hP : ValidDesign P)
    (g : Finset (Fin n) → ℝ≥0∞) (α : ℝ) (hα : 0 < α ∧ α < 1) :
    1-α ≤ probability P (fun S => g S ≤ quantile P g α) := by
  have hF : (assignments P).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa using (Nat.le_of_lt hP.2.2)
  have hcard : ((assignments P).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hF)
  unfold quantile
  dsimp only
  split_ifs with h
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2
  · have he : probability P (fun S => g S ≤ ⊤) = 1 := by
      simp [probability, hcard]
    rw [he]
    linarith [hα.1]

/-- T25(b)-(c): finite-sample coverage of both full-distribution confidence sets
under a constant additive effect, at every valid sample size. Covariates are arbitrary;
OLS uses the fixed rule above also on singular arms. No asymptotics are assumed. -/
theorem constant_effect_coverage {n k} (P : CovPopulation n k) (β α : ℝ)
    (hP : ValidDesign P.pop) (hm : MonotoneReceipt P.pop)
    (hc : (compliers P.pop).Nonempty) (hy : ∀ i, P.pop.y i true = P.pop.y i false + β)
    (hα : 0 < α ∧ α < 1) :
    late P.pop = β ∧ 1-α ≤ coverage P.pop β α ∧ 1-α ≤ adjustedCoverage P β α := by
  have hcard : ((compliers P.pop).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hc)
  have hl : late P.pop = β := by
    simp [late, groupMean, hy, hcard]
  refine ⟨hl, ?_, ?_⟩
  · unfold coverage accepted
    simp_rw [constant_effect_adjusted_outcomes P.pop β hy]
    exact quantile_valid P.pop hP _ α hα
  · unfold adjustedCoverage adjustedAccepted
    simp_rw [constant_effect_adjusted_outcomes P.pop β hy]
    exact quantile_valid P.pop hP _ α hα

/-- Remark 4's adjusted Wald estimator, main p. 10, (12). -/
def adjustedWald {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  adjustedTau P Y S / adjustedTau P D S
/-- T26(a)-(b): Wald zeroes tau_adj and Delta_adj and belongs to the full
randomization confidence set, whenever both observed arms have full column rank
and its denominator is nonzero (main Remark 4, (12)). -/
theorem adjusted_wald_in_set {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) (α : ℝ) (h1 : (gram P.x S).det ≠ 0)
    (h0 : (gram P.x Sᶜ).det ≠ 0) (hd : adjustedTau P D S ≠ 0)
    (hα : 0 < α ∧ α < 1) :
    (∀ β, adjustedTau P (fun i => Y i-β*D i) S = adjustedTau P Y S-β*adjustedTau P D S) ∧
    adjustedTau P (fun i => Y i-adjustedWald P Y D S*D i) S = 0 ∧
    adjustedAR P (fun i => Y i-adjustedWald P Y D S*D i) S = 0 ∧
    adjustedAR P (fun i => Y i-adjustedWald P Y D S*D i) S ≤
      quantile P.pop (adjustedAR P (fun i => Y i-adjustedWald P Y D S*D i)) α := by
  have hz := (corrected_I1_I2 P S Y D 0 h1 h0).2.2 hd
  change adjustedTau P (fun i => Y i-adjustedWald P Y D S*D i) S = 0 at hz
  have hzero (s : ℝ) : absStudent 0 s = 0 := by
    by_cases hs : s=0
    · simp [absStudent, hs]
    · simp [absStudent, hs]
  have har : adjustedAR P (fun i => Y i-adjustedWald P Y D S*D i) S = 0 := by
    unfold adjustedAR
    rw [hz, hzero]
  refine ⟨?_, hz, har, ?_⟩
  · intro β
    exact (corrected_I1_I2 P S Y D β h1 h0).2.1
  · rw [har]
    exact bot_le

/-- Column order in Supplement p. 46, (I.3): D or Z, intercept, then two
interacted covariate blocks. `Fin 2` indexes the first two columns. -/
abbrev IVIndex (k : ℕ) := Sum (Fin 2) (Bool × Fin k)
/-- "tilde X_i=(D_i,1,Z_i x_i', (1-Z_i)x_i')'", Supplement p. 46, (I.3). -/
def ivRow {n k} (P : CovPopulation n k) (D : Fin n → ℝ)
    (S : Finset (Fin n)) (i : Fin n) : IVIndex k → ℝ
  | .inl j => if j=0 then D i else 1
  | .inr (a,s) => if decide (i ∈ S) = a then P.x i s else 0
/-- Instruments (Z,1,Zx,(1-Z)x), Supplement (I.3). -/
def instrumentRow {n k} (P : CovPopulation n k) (S : Finset (Fin n)) (i : Fin n) :=
  ivRow P (fun l => if l ∈ S then 1 else 0) S i
/-- "(1/n) sum_i tilde W_i tilde X_i'", Supplement p. 46, (I.3). -/
def ivCross {n k} (P : CovPopulation n k) (D : Fin n → ℝ) (S : Finset (Fin n)) :
    Matrix (IVIndex k) (IVIndex k) ℝ :=
  fun s t => mean fun i => instrumentRow P S i s * ivRow P D S i t
/-- "(1/n) sum_i tilde W_i tilde W_i'", Supplement pp. 46-47. -/
def instrumentGram {n k} (P : CovPopulation n k) (S : Finset (Fin n)) :
    Matrix (IVIndex k) (IVIndex k) ℝ :=
  fun s t => mean fun i => instrumentRow P S i s * instrumentRow P S i t
/-- Just-identified IV coefficients ((1/n) sum W_i X_i')^-1 (1/n) sum W_iY_i,
Supplement p. 46, (I.3). -/
def ivCoefficients {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ) (S : Finset (Fin n)) :=
  (ivCross P D S)⁻¹ *ᵥ (fun s => mean fun i => instrumentRow P S i s*Y i)

/-- Squared AR function, ratios of quadratics (15)-(16), main pp. 12-14;
(F.1)-(F.2), Supplement p. 43. The numerator and denominator are the paper's
polynomials; their positivity assumptions are separate, not built into the type. -/
structure QuadraticAR where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  f : ℝ
/-- "Delta_m^{*2}(beta)" as the ratio of the two quadratics in (16),
main p. 13, or the adjusted ratio in Supplement (F.2). -/
def arFunction (Q : QuadraticAR) (β : ℝ) : ℝ :=
  (Q.a*β^2+Q.b*β+Q.c)/(Q.d*β^2+Q.e*β+Q.f)
/-- Assumptions 6 and 7: variance denominators strictly positive on the entire real line.
The nonnegative numerator records that these are squared studentized statistics. -/
def ARRegular (Q : QuadraticAR) : Prop :=
  (∀ β, 0 < Q.d*β^2+Q.e*β+Q.f) ∧ (∀ β, 0 ≤ Q.a*β^2+Q.b*β+Q.c)
/-- Empirical critical value, the smallest observed absolute AR value satisfying (13).
Squared curves are passed to this function, so absolute values are their square roots. -/
def mcCritical {M} (g : Fin M → ℝ → ℝ) (α β : ℝ) : ℝ :=
  let C := (Finset.univ.image (fun m => Real.sqrt (g m β))).filter fun q =>
    (1-α)*(M : ℝ) ≤ ((Finset.univ.filter (fun m => Real.sqrt (g m β) ≤ q)).card : ℝ)
  if h : C.Nonempty then C.min' h else 0
/-- "I(beta)={m:|Delta_m*(beta)|=eta-hat*(beta,Z)}", main p. 14, (17). -/
def mcIndices {M} (g : Fin M → ℝ → ℝ) (α β : ℝ) : Finset (Fin M) :=
  Finset.univ.filter fun m => Real.sqrt (g m β) = mcCritical g α β
/-- Monte Carlo confidence set (14), or adjusted (F.4), with observed squared curve f. -/
def mcSet {M} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ) (α : ℝ) : Set ℝ :=
  {β | Real.sqrt (f β) ≤ mcCritical g α β}
/-- Closed and open parameter intervals including the allowed infinite endpoints,
main Lemma 1 and Algorithms 1-4. All elements of these sets are real parameters. -/
def closedInterval (l u : EReal) : Set ℝ := {β | l ≤ (β : EReal) ∧ (β : EReal) ≤ u}
/-- "open interval (beta_1,beta_2)", allowing infinite endpoints,
main p. 14, Lemma 1. Its members are real parameters. -/
def openInterval (l u : EReal) : Set ℝ := {β | l < (β : EReal) ∧ (β : EReal) < u}
/-- Distinct curves meet at beta; identical curves do not contribute intersections,
main p. 14, Remark 7. -/
def crossing {M} (g : Fin M → ℝ → ℝ) (β : ℝ) : Prop :=
  ∃ s t, g s ≠ g t ∧ g s β = g t β
/-- Equivalent cardinal description of the quantile index (T27), with both
strict and non-strict comparisons. -/
theorem quantile_index_rank {M} (g : Fin M → ℝ → ℝ) (hM : 0 < M)
    (α β : ℝ) (hα : 0 < α ∧ α < 1) (hn : ∀ m, 0 ≤ g m β) (m : Fin M) :
    m ∈ mcIndices g α β ↔
      (1-α)*(M : ℝ) ≤ ((Finset.univ.filter (fun s => g s β ≤ g m β)).card : ℝ) ∧
      (((Finset.univ.filter (fun s => g s β < g m β)).card : ℕ) : ℝ) < (1-α)*(M : ℝ) := by
  let f : Fin M → ℝ := fun s => Real.sqrt (g s β)
  let c : ℝ := (1-α)*(M : ℝ)
  let V : Finset ℝ := Finset.univ.image f
  let C : Finset ℝ := V.filter fun q =>
    c ≤ ((Finset.univ.filter (fun s : Fin M => f s ≤ q)).card : ℝ)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hc0 : 0 < c := mul_pos (sub_pos.mpr hα.2) hMr
  have hcM : c ≤ (M : ℝ) := by
    dsimp [c]
    nlinarith [mul_nonneg hα.1.le hMr.le]
  have hfm (s : Fin M) : f s ∈ V :=
    Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
  have hV : V.Nonempty := ⟨f m, hfm m⟩
  have hmax (s : Fin M) : f s ≤ V.max' hV :=
    Finset.le_max' V (f s) (hfm s)
  have hmaxfilter :
      Finset.univ.filter (fun s : Fin M => f s ≤ V.max' hV) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro s _
    exact hmax s
  have hC : C.Nonempty := by
    refine ⟨V.max' hV, Finset.mem_filter.mpr ⟨Finset.max'_mem V hV, ?_⟩⟩
    rw [hmaxfilter]
    simpa only [Finset.card_univ, Fintype.card_fin] using hcM
  have hcrit : mcCritical g α β = C.min' hC := by
    change (if h : C.Nonempty then C.min' h else 0) = C.min' hC
    rw [dif_pos hC]
  have hlefilter :
      Finset.univ.filter (fun s : Fin M => f s ≤ f m) =
        Finset.univ.filter (fun s : Fin M => g s β ≤ g m β) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Real.sqrt_le_sqrt_iff (hn m)
  have hltfilter :
      Finset.univ.filter (fun s : Fin M => f s < f m) =
        Finset.univ.filter (fun s : Fin M => g s β < g m β) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Real.sqrt_lt_sqrt_iff (hn s)
  simp only [mcIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  change f m = mcCritical g α β ↔
    c ≤ ((Finset.univ.filter (fun s : Fin M => g s β ≤ g m β)).card : ℝ) ∧
      ((Finset.univ.filter (fun s : Fin M => g s β < g m β)).card : ℝ) < c
  rw [hcrit, ← hlefilter, ← hltfilter]
  let L : Finset (Fin M) := Finset.univ.filter fun s => f s < f m
  change f m = C.min' hC ↔
    c ≤ ((Finset.univ.filter (fun s : Fin M => f s ≤ f m)).card : ℝ) ∧
      (L.card : ℝ) < c
  constructor
  · intro hm
    constructor
    · have H := (Finset.mem_filter.mp (Finset.min'_mem C hC)).2
      simpa only [← hm] using H
    · by_contra hnot
      have hlarge : c ≤ (L.card : ℝ) := by linarith
      have hLcard : 0 < L.card := by
        exact_mod_cast (lt_of_lt_of_le hc0 hlarge)
      have hL : L.Nonempty := Finset.card_pos.mp hLcard
      let B : Finset ℝ := L.image f
      have hB : B.Nonempty := hL.image f
      have htB : B.max' hB ∈ B := Finset.max'_mem B hB
      rcases Finset.mem_image.mp htB with ⟨j, hj, hjf⟩
      have htlt : B.max' hB < f m := by
        rw [← hjf]
        exact (Finset.mem_filter.mp hj).2
      have hsub : L ⊆ Finset.univ.filter (fun s : Fin M => f s ≤ B.max' hB) := by
        intro s hs
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Finset.le_max' B (f s) (Finset.mem_image.mpr ⟨s, hs, rfl⟩)⟩
      have hcardle : (L.card : ℝ) ≤
          ((Finset.univ.filter (fun s : Fin M => f s ≤ B.max' hB)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have htC : B.max' hB ∈ C := by
        apply Finset.mem_filter.mpr
        refine ⟨?_, hlarge.trans hcardle⟩
        rw [← hjf]
        exact hfm j
      have hminle := Finset.min'_le C (B.max' hB) htC
      rw [← hm] at hminle
      exact (not_lt_of_ge hminle) htlt
  · rintro ⟨hweak, hstrict⟩
    have hmC : f m ∈ C := Finset.mem_filter.mpr ⟨hfm m, hweak⟩
    apply le_antisymm
    · by_contra hnot
      have hlt : C.min' hC < f m := by linarith
      have hsub : Finset.univ.filter (fun s : Fin M => f s ≤ C.min' hC) ⊆ L := by
        intro s hs
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          lt_of_le_of_lt (Finset.mem_filter.mp hs).2 hlt⟩
      have hcardle :
          ((Finset.univ.filter (fun s : Fin M => f s ≤ C.min' hC)).card : ℝ) ≤
            (L.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hminweak : c ≤
          ((Finset.univ.filter (fun s : Fin M => f s ≤ C.min' hC)).card : ℝ) :=
        (Finset.mem_filter.mp (Finset.min'_mem C hC)).2
      exact (not_le_of_gt hstrict) (hminweak.trans hcardle)
    · exact Finset.min'_le C (f m) hmC

/-- A pair recorded by Algorithm 2 Step 4, corrected indexing: ([e_(k-1),e_k],m_k). -/
structure RecordedPiece (M : ℕ) where
  left : EReal
  right : EReal
  index : Fin M
/-- Step 5 set, main Algorithms 1-2 and Supplement Algorithms 3-4. -/
def pieceSet {M} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ) (p : RecordedPiece M) : Set ℝ :=
  {β | β ∈ closedInterval p.left p.right ∧ f β ≤ g p.index β}
/-- Step 6 return value, union of the recorded Step 4 pairs without shifting indices. -/
def returnedSet {M} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ) (pieces : List (RecordedPiece M)) : Set ℝ :=
  {β | ∃ p ∈ pieces, β ∈ pieceSet f g p}
/-- Complete sorted finite intersection list from Step 1, main p. 15. -/
def IntersectionList {M} (g : Fin M → ℝ → ℝ) (J : List ℝ) : Prop :=
  J.Pairwise (· < ·) ∧ ∀ β, β ∈ J ↔ crossing g β
/-- Algorithm 1 Step 3's representative point in a gap, including unbounded gaps. -/
def gapSample (l u : EReal) : ℝ :=
  if l=⊥ then (if u=⊤ then 0 else u.toReal-1)
  else if u=⊤ then l.toReal+1 else (l.toReal+u.toReal)/2
/-- Intersections partition the real line into closed gaps, Algorithm 1 Step 2. -/
def gapEndpoints (J : List ℝ) : List (EReal × EReal) :=
  (⊥ :: J.map (fun x => (x : EReal))).zip (J.map (fun x => (x : EReal)) ++ [⊤])
/-- Algorithm 1/3 records every gap and an admissible quantile index at its
prescribed sample. No interval-wide quantile conclusion is part of this definition. -/
def Algorithm1Run {M} (g : Fin M → ℝ → ℝ) (α : ℝ) (J : List ℝ)
    (pieces : List (RecordedPiece M)) : Prop :=
  IntersectionList g J ∧ pieces.map (fun p => (p.left,p.right)) = gapEndpoints J ∧
  ∀ p ∈ pieces, p.index ∈ mcIndices g α (gapSample p.left p.right)
/-- A single step of Algorithm 2/4. It records the least subsequent crossing of
its selected curve, or infinity if none exists; the next index is chosen after that
crossing and before the next global crossing, exactly as Step 4 specifies. -/
def Algorithm2Step {M} (g : Fin M → ℝ → ℝ) (α : ℝ) (J : List ℝ)
    (p : RecordedPiece M) (next : Option (RecordedPiece M)) : Prop :=
  let C : Set ℝ := {β | p.left < (β : EReal) ∧ ∃ m, g m ≠ g p.index ∧ g m β=g p.index β}
  (if C.Nonempty then ∃ e : ℝ, IsLeast C e ∧ p.right=(e : EReal)
    else p.right=⊤) ∧
  (match next with
   | none => p.right=⊤
   | some q => p.right ≠ ⊤ ∧ q.left=p.right ∧
       let E : List ℝ := J.filter fun β => p.right < (β : EReal)
       q.index ∈ mcIndices g α
         (if E=[] then (p.right.toReal : ℝ)+1
           else ((p.right.toReal : ℝ)+(E.head! : ℝ))/(2 : ℝ)))
/-- Finite prefix of the Step 4 loop, including its initialization and terminal
step. -/
def Algorithm2Run {M} (g : Fin M → ℝ → ℝ) (α : ℝ) (J : List ℝ)
    (pieces : List (RecordedPiece M)) : Prop :=
  IntersectionList g J ∧ J ≠ [] ∧ pieces ≠ [] ∧
  (∀ p, pieces.head?=some p → p.left=⊥ ∧
    p.index ∈ mcIndices g α (J.head!-1)) ∧
  (∀ i : Fin pieces.length,
    Algorithm2Step g α J (pieces.get i) (pieces[i.val+1]?))
/-- Regular family of squared curves needed by the algorithms: continuity,
nonnegativity, and finitely many intersections of each distinct pair. Ratios
of quadratics under Assumptions 6/7 satisfy these conditions. -/
def CurveRegularity {M} (g : Fin M → ℝ → ℝ) : Prop :=
  (∀ m, Continuous (g m)) ∧ (∀ m β, 0 ≤ g m β) ∧
  ∀ s t, g s ≠ g t → {β | g s β=g t β}.Finite

/-- The cross term in the unadjusted variance polynomial, main pp. 12-13,
coefficients e in (15)-(16). Both vectors are fixed under reassignment. -/
def rawVarianceCross {n} (P : Population n) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  (fraction P)^2*(1-fraction P)^2 *
    ((∑ i ∈ S, (Y i-armMean Y S true)*(D i-armMean D S true))/(P.n1 : ℝ)^2 +
     (∑ i ∈ Sᶜ, (Y i-armMean Y S false)*(D i-armMean D S false))/(controlSize P)^2)

/-- The six data-generated unadjusted coefficients in (15)-(16), main pp. 12-13.
Y and D are the observed vectors, and S is the observed or simulated assignment. -/
def rawCoefficients {n} (P : Population n) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) : QuadraticAR where
  a := (rawTau P D S)^2
  b := -2*rawTau P Y S*rawTau P D S
  c := (rawTau P Y S)^2
  d := rawSigma2 P D S
  e := -2*rawVarianceCross P Y D S
  f := rawSigma2 P Y S

/-- The residual cross moment r_yd in Supplement p. 43, (F.1)-(F.2).
Fitted Y and fitted D use the same interacted arm designs. -/
def adjustedVarianceCross {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  (∑ i ∈ S, (Y i-dotProduct (augmented P.x i) (fitted P Y S true))*
      (D i-dotProduct (augmented P.x i) (fitted P D S true)))/(P.pop.n1 : ℝ)^2 +
  (∑ i ∈ Sᶜ, (Y i-dotProduct (augmented P.x i) (fitted P Y S false))*
      (D i-dotProduct (augmented P.x i) (fitted P D S false)))/(controlSize P.pop)^2

/-- The adjusted data-generated coefficients a=t_d², b=-2t_y t_d, c=t_y²,
d=r_d, e=-2r_yd, f=r_y (Supplement p. 43, (F.1)-(F.2)). -/
def adjustedCoefficients {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) : QuadraticAR where
  a := (adjustedTau P D S)^2
  b := -2*adjustedTau P Y S*adjustedTau P D S
  c := (adjustedTau P Y S)^2
  d := adjustedSigma2 P D S
  e := -2*adjustedVarianceCross P Y D S
  f := adjustedSigma2 P Y S

/-- Finite expansion of the squared centered affine response underlying
the variance coefficients in (15)-(16) and (F.1)-(F.2). -/
theorem sum_affine_square {n} (S : Finset (Fin n)) (Y D : Fin n → ℝ)
    (c d β : ℝ) :
    (∑ i ∈ S, ((Y i-β*D i)-(c-β*d))^2) =
      (∑ i ∈ S, (Y i-c)^2) - 2*β*(∑ i ∈ S, (Y i-c)*(D i-d)) +
        β^2*(∑ i ∈ S, (D i-d)^2) := by
  calc
    _ = ∑ i ∈ S, ((Y i-c)^2 - (2*β)*((Y i-c)*(D i-d)) + β^2*(D i-d)^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Exact affine dependence of the fixed-outcome tau statistic on beta,
main p. 12, coefficients in (15). -/
theorem rawTau_linear {n} (P : Population n) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) (β : ℝ) :
    rawTau P (fun i => Y i-β*D i) S = rawTau P Y S-β*rawTau P D S := by
  simp only [rawTau, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The unadjusted variance of Y-beta D is its exact quadratic polynomial,
main pp. 12-13, denominator of (15)-(16). -/
theorem rawSigma2_affine {n} (P : Population n) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) (β : ℝ) :
    rawSigma2 P (fun i => Y i-β*D i) S =
      rawSigma2 P Y S-2*β*rawVarianceCross P Y D S+β^2*rawSigma2 P D S := by
  have hm (a : Bool) : armMean (fun i => Y i-β*D i) S a =
      armMean Y S a-β*armMean D S a :=
    groupMean_sub_smul (if a then S else Sᶜ) Y D β
  simp only [rawSigma2, hm]
  rw [sum_affine_square, sum_affine_square]
  unfold rawVarianceCross
  ring

/-- The data-generated coefficients recover both polynomials in (15)-(16) and
their ratio using total real division, for every beta. When the variance denominator
is positive, `raw_ar_bridge` identifies its square root with the absolute AR statistic. -/
theorem raw_coefficients_formula {n} (P : Population n) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) (β : ℝ) :
    let Q := rawCoefficients P Y D S
    Q.a*β^2+Q.b*β+Q.c=(rawTau P (fun i => Y i-β*D i) S)^2 ∧
    Q.d*β^2+Q.e*β+Q.f=rawSigma2 P (fun i => Y i-β*D i) S ∧
    arFunction Q β=(rawTau P (fun i => Y i-β*D i) S)^2 /
      rawSigma2 P (fun i => Y i-β*D i) S := by
  have hn : (rawCoefficients P Y D S).a*β^2+(rawCoefficients P Y D S).b*β+
      (rawCoefficients P Y D S).c=(rawTau P (fun i => Y i-β*D i) S)^2 := by
    rw [rawTau_linear]
    dsimp [rawCoefficients]
    ring
  have hd : (rawCoefficients P Y D S).d*β^2+(rawCoefficients P Y D S).e*β+
      (rawCoefficients P Y D S).f=rawSigma2 P (fun i => Y i-β*D i) S := by
    rw [rawSigma2_affine]
    dsimp [rawCoefficients]
    ring
  exact ⟨hn, hd, by unfold arFunction; rw [hn, hd]⟩

/-- Interacted fitted residuals are affine in beta whenever both arm designs
have full column rank, as required by the inverses in Supplement (F.1). -/
theorem fitted_residual_linear {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) (h1 : (gram P.x S).det ≠ 0)
    (h0 : (gram P.x Sᶜ).det ≠ 0) (β : ℝ) (a : Bool) (i : Fin n) :
    (Y i-β*D i)-dotProduct (augmented P.x i) (fitted P (fun j => Y j-β*D j) S a) =
      (Y i-dotProduct (augmented P.x i) (fitted P Y S a)) -
        β*(D i-dotProduct (augmented P.x i) (fitted P D S a)) := by
  have hf : fitted P (fun j => Y j-β*D j) S a =
      fitted P Y S a-β • fitted P D S a := by
    cases a
    · exact ols_linear P.x Sᶜ Y D β h0
    · exact ols_linear P.x S Y D β h1
  rw [hf]
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ring

/-- The adjusted variance is the exact quadratic in beta of Supplement p. 43,
with cross coefficient -2r_yd; the arm OLS matrices have full rank. -/
theorem adjustedSigma2_affine {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) (h1 : (gram P.x S).det ≠ 0)
    (h0 : (gram P.x Sᶜ).det ≠ 0) (β : ℝ) :
    adjustedSigma2 P (fun i => Y i-β*D i) S =
      adjustedSigma2 P Y S-2*β*adjustedVarianceCross P Y D S+
        β^2*adjustedSigma2 P D S := by
  have hs (U : Finset (Fin n)) (a : Bool) :
      rss P.x U (fun i => Y i-β*D i) (fitted P (fun i => Y i-β*D i) S a) =
        rss P.x U Y (fitted P Y S a) -
        2*β*(∑ i ∈ U, (Y i-dotProduct (augmented P.x i) (fitted P Y S a))*
          (D i-dotProduct (augmented P.x i) (fitted P D S a))) +
        β^2*rss P.x U D (fitted P D S a) := by
    unfold rss
    simp_rw [fitted_residual_linear P Y D S h1 h0 β a]
    simpa only [mul_zero, sub_self, sub_zero] using sum_affine_square U
      (fun i => Y i-dotProduct (augmented P.x i) (fitted P Y S a))
      (fun i => D i-dotProduct (augmented P.x i) (fitted P D S a)) 0 0 β
  simp only [adjustedSigma2, hs]
  unfold adjustedVarianceCross
  ring

/-- Under full-rank arm OLS, the data-generated adjusted coefficients recover
both polynomials in (F.1)-(F.2) and their ratio using total real division. When the
variance denominator is positive, `adjusted_ar_bridge` identifies its square root
with the absolute adjusted AR statistic. -/
theorem adjusted_coefficients_formula {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) (h1 : (gram P.x S).det ≠ 0)
    (h0 : (gram P.x Sᶜ).det ≠ 0) (β : ℝ) :
    let Q := adjustedCoefficients P Y D S
    Q.a*β^2+Q.b*β+Q.c=(adjustedTau P (fun i => Y i-β*D i) S)^2 ∧
    Q.d*β^2+Q.e*β+Q.f=adjustedSigma2 P (fun i => Y i-β*D i) S ∧
    arFunction Q β=(adjustedTau P (fun i => Y i-β*D i) S)^2 /
      adjustedSigma2 P (fun i => Y i-β*D i) S := by
  have ht := (corrected_I1_I2 P S Y D β h1 h0).2.1
  have hn : (adjustedCoefficients P Y D S).a*β^2+(adjustedCoefficients P Y D S).b*β+
      (adjustedCoefficients P Y D S).c=(adjustedTau P (fun i => Y i-β*D i) S)^2 := by
    rw [ht]
    dsimp [adjustedCoefficients]
    ring
  have hd : (adjustedCoefficients P Y D S).d*β^2+(adjustedCoefficients P Y D S).e*β+
      (adjustedCoefficients P Y D S).f=adjustedSigma2 P (fun i => Y i-β*D i) S := by
    rw [adjustedSigma2_affine P Y D S h1 h0 β]
    dsimp [adjustedCoefficients]
    ring
  exact ⟨hn, hd, by unfold arFunction; rw [hn, hd]⟩

/-- Under a positive variance denominator, the square root of (15)-(16)
equals the actual absolute unadjusted statistic (4)-(5). -/
theorem raw_ar_bridge {n} (P : Population n) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) (β : ℝ)
    (hp : 0 < rawSigma2 P (fun i => Y i-β*D i) S) :
    ENNReal.ofReal (Real.sqrt (arFunction (rawCoefficients P Y D S) β))=
      rawAR P (fun i => Y i-β*D i) S := by
  rw [(raw_coefficients_formula P Y D S β).2.2]
  rw [Real.sqrt_div (sq_nonneg _) _, Real.sqrt_sq_eq_abs]
  simp only [rawAR, absStudent, if_neg (ne_of_gt hp)]

/-- Under Assumption 7's positive denominator and full-rank OLS, the square
root of (F.1)-(F.2) equals the absolute adjusted statistic (10). -/
theorem adjusted_ar_bridge {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) (h1 : (gram P.x S).det ≠ 0)
    (h0 : (gram P.x Sᶜ).det ≠ 0) (β : ℝ)
    (hp : 0 < adjustedSigma2 P (fun i => Y i-β*D i) S) :
    ENNReal.ofReal (Real.sqrt (arFunction (adjustedCoefficients P Y D S) β))=
      adjustedAR P (fun i => Y i-β*D i) S := by
  rw [(adjusted_coefficients_formula P Y D S h1 h0 β).2.2]
  rw [Real.sqrt_div (sq_nonneg _) _, Real.sqrt_sq_eq_abs]
  simp only [adjustedAR, absStudent, if_neg (ne_of_gt hp)]

/-- (15)-(16) and (F.1)-(F.2) use the same observed Y,D for every simulated
assignment. This function fixes the vectors at the observed assignment O;
only the regression and assignment in T vary. -/
def dataCoefficients {n k} (P : CovPopulation n k) (adjusted : Bool)
    (O T : Finset (Fin n)) : QuadraticAR :=
  let Y := observedY P.pop O
  let D := fun i => binary (observedD P.pop O i)
  if adjusted then adjustedCoefficients P Y D T else rawCoefficients P.pop Y D T

/-- A common observed dataset and M simulated completely randomized assignments
generate the observed and simulated AR coefficients by (15)-(16) or (F.1)-(F.2).
Binary receipts, exclusion, monotonicity, a complier, and common arm sizes
are retained. In the adjusted case covariates
are centered and the arm matrices inverted in (F.1) have full column rank.
Positivity of the variance polynomials is the separate Assumption 6/7. -/
def DataGeneratedCoefficients {M} (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) : Prop :=
  ∃ (n k : ℕ) (P : CovPopulation n k) (adjusted : Bool)
    (O : Finset (Fin n)) (T : Fin M → Finset (Fin n)),
    ValidDesign P.pop ∧ MonotoneReceipt P.pop ∧ (compliers P.pop).Nonempty ∧
    O ∈ assignments P.pop ∧ (∀ m, T m ∈ assignments P.pop) ∧
    (adjusted=true → 0 < k ∧ (∀ s, ∑ i, P.x i s=0) ∧
      ∀ R, (R=O ∨ ∃ m, R=T m) → (gram P.x R).det ≠ 0 ∧ (gram P.x Rᶜ).det ≠ 0) ∧
    Qf=dataCoefficients P adjusted O O ∧ ∀ m, Qg m=dataCoefficients P adjusted O (T m)


/-- Necessary algebraic coefficient condition from "a=tau_d^2, b=-2 tau_y
tau_d, c=tau_y^2" (main pp. 12-13, (15)-(16)), with positive variance
denominator as in Assumption 6/7. This predicate alone admits arbitrary such
coefficients; DataGeneratedCoefficients additionally requires the common
observed dataset and simulated assignments in the algorithm statements. -/
def PaperAR (Q : QuadraticAR) : Prop :=
  (∀ β, 0 < Q.d*β^2+Q.e*β+Q.f) ∧
  ∃ u v : ℝ, Q.a=v^2 ∧ Q.b= -2*u*v ∧ Q.c=u^2

/-- The coefficients in (15)-(16), with Assumption 6/7, give a nonnegative
squared statistic and hence satisfy the generic regularity predicate. -/
theorem paperAR_regular (Q : QuadraticAR) (hQ : PaperAR Q) : ARRegular Q := by
  refine ⟨hQ.1, ?_⟩
  obtain ⟨u,v,ha,hb,hc⟩ := hQ.2
  intro β
  rw [ha,hb,hc]
  nlinarith [sq_nonneg (u-β*v)]

/-- Four all-complier units, n1=2, y_i(1)=y_i(0)=(0,1,2,4), used only
to demonstrate that the common-data AR hypotheses are satisfiable. -/
def commonDataExample : CovPopulation 4 0 where
  pop := {y := fun i _ => if i=0 then 0 else if i=1 then 1 else if i=2 then 2 else 4,
          d := fun _ a => a, n1 := 2}
  x := fun _ j => Fin.elim0 j

/-- Data-generated curves can satisfy Assumption 6 and have a genuine crossing.
For the explicit four-unit dataset the observed assignment is {0,1}; the two
simulations are {0,1} and {0,2}. Their AR functions meet at beta=-1. This is a
satisfiable instance of the algorithm hypotheses; it does not prove correctness. -/
theorem data_ar_nonvacuous :
    ∃ (Qf : QuadraticAR) (Qg : Fin 2 → QuadraticAR),
      DataGeneratedCoefficients Qf Qg ∧ PaperAR Qf ∧
      (∀ m, PaperAR (Qg m)) ∧ crossing (fun m => arFunction (Qg m)) (-1) := by
  let P := commonDataExample
  let O : Finset (Fin 4) := {0,1}
  let U : Finset (Fin 4) := {0,2}
  let T : Fin 2 → Finset (Fin 4) := fun m => if m=0 then O else U
  let Q0 : QuadraticAR := ⟨1/16, 5/16, 25/64, 0, 0, 5/128⟩
  let Q1 : QuadraticAR := ⟨0, 0, 9/64, 1/64, 5/64, 13/128⟩
  let Qg : Fin 2 → QuadraticAR := fun m => if m=0 then Q0 else Q1
  have hO : Oᶜ=({2,3} : Finset (Fin 4)) := by decide
  have hU : Uᶜ=({1,3} : Finset (Fin 4)) := by decide
  have hc0 : dataCoefficients P false O O=Q0 := by
    dsimp only [dataCoefficients, rawCoefficients, Q0]
    congr 1 <;>
      simp only [rawVarianceCross, rawSigma2, rawTau, armMean, groupMean,
        Bool.false_eq_true, ite_false, ite_true, hO, hU] <;>
      norm_num [
      rawTau, armMean, groupMean, observedD, observedY, binary, fraction, controlSize,
      P, commonDataExample, O, Q0, Fin.sum_univ_succ, Finset.sum_insert,
      Finset.sum_singleton, Finset.filter_insert, Finset.filter_singleton, Finset.filter_empty]
  have hc1 : dataCoefficients P false O U=Q1 := by
    dsimp only [dataCoefficients, rawCoefficients, Q1]
    congr 1 <;>
      simp only [rawVarianceCross, rawSigma2, rawTau, armMean, groupMean,
        Bool.false_eq_true, ite_false, ite_true, hO, hU] <;>
      norm_num [
      rawTau, armMean, groupMean, observedD, observedY, binary, fraction, controlSize,
      P, commonDataExample, O, U, Q1, Fin.sum_univ_succ, Finset.sum_insert,
      Finset.sum_singleton, Finset.filter_insert, Finset.filter_singleton, Finset.filter_empty]
  have hp0 : PaperAR Q0 := by
    refine ⟨?_, -5/8, 1/4, ?_, ?_, ?_⟩ <;> norm_num [Q0]
  have hp1 : PaperAR Q1 := by
    refine ⟨?_, -3/8, 0, ?_, ?_, ?_⟩ <;> norm_num [Q1]
    intro β
    nlinarith [sq_nonneg (β+5/2)]
  refine ⟨Q0, Qg, ?_, hp0, ?_, ?_⟩
  · refine ⟨4, 0, P, false, O, T, ?_, ?_, ?_, ?_, ?_, ?_, hc0.symm, ?_⟩
    · norm_num [ValidDesign, P, commonDataExample]
    · simp [MonotoneReceipt, P, commonDataExample]
    · simp [compliers, P, commonDataExample]
    · decide
    · intro m
      fin_cases m <;> decide
    · simp
    · intro m
      fin_cases m
      · simpa [Qg, T] using hc0.symm
      · simpa [Qg, T] using hc1.symm
  · intro m
    fin_cases m
    · simpa [Qg] using hp0
    · simpa [Qg] using hp1
  · refine ⟨0, 1, ?_, ?_⟩
    · intro he
      have H := congrFun he 0
      norm_num [Qg, arFunction, Q0, Q1] at H
    · norm_num [Qg, arFunction, Q0, Q1]

/-- A ratio of the quadratics in (15)-(16) or (F.1)-(F.2) is continuous
when its variance denominator is positive for every real beta. -/
theorem arFunction_continuous (Q : QuadraticAR) (hQ : ARRegular Q) :
    Continuous (arFunction Q) := by
  unfold arFunction
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro β
    exact ne_of_gt (hQ.1 β)

/-- The ratio-of-quadratics family has continuous nonnegative curves and
finitely many intersections of every distinct pair (main Remark 7, p. 14;
Supplement p. 43). Distinctness makes the cross-multiplied polynomial nonzero,
so its real root set is finite; no rank-constancy conclusion is assumed. -/
theorem arFamily_regular {M} (Q : Fin M → QuadraticAR)
    (hQ : ∀ m, ARRegular (Q m)) :
    CurveRegularity (fun m => arFunction (Q m)) := by
  refine ⟨fun m => arFunction_continuous (Q m) (hQ m), ?_, ?_⟩
  · intro m β
    exact div_nonneg ((hQ m).2 β) (le_of_lt ((hQ m).1 β))
  · intro s t hst
    let num (q : QuadraticAR) : Polynomial ℝ :=
      Polynomial.C q.a*Polynomial.X^2+Polynomial.C q.b*Polynomial.X+Polynomial.C q.c
    let den (q : QuadraticAR) : Polynomial ℝ :=
      Polynomial.C q.d*Polynomial.X^2+Polynomial.C q.e*Polynomial.X+Polynomial.C q.f
    let R : Polynomial ℝ := num (Q s)*den (Q t)-num (Q t)*den (Q s)
    have heval (β : ℝ) : R.eval β =
        ((Q s).a*β^2+(Q s).b*β+(Q s).c)*((Q t).d*β^2+(Q t).e*β+(Q t).f) -
        ((Q t).a*β^2+(Q t).b*β+(Q t).c)*((Q s).d*β^2+(Q s).e*β+(Q s).f) := by
      simp [R,num,den]
    have hD (m : Fin M) (β : ℝ) : (Q m).d*β^2+(Q m).e*β+(Q m).f ≠ 0 :=
      ne_of_gt ((hQ m).1 β)
    have hR : R ≠ 0 := by
      intro hz
      apply hst
      funext β
      change ((Q s).a*β^2+(Q s).b*β+(Q s).c)/((Q s).d*β^2+(Q s).e*β+(Q s).f) =
        ((Q t).a*β^2+(Q t).b*β+(Q t).c)/((Q t).d*β^2+(Q t).e*β+(Q t).f)
      apply (div_eq_div_iff (hD s β) (hD t β)).mpr
      have H : R.eval β=0 := by rw [hz]; simp
      rw [heval] at H
      exact sub_eq_zero.mp H
    apply (Polynomial.finite_setOfPred_isRoot hR).subset
    intro β hβ
    change R.eval β=0
    change ((Q s).a*β^2+(Q s).b*β+(Q s).c)/((Q s).d*β^2+(Q s).e*β+(Q s).f) =
      ((Q t).a*β^2+(Q t).b*β+(Q t).c)/((Q t).d*β^2+(Q t).e*β+(Q t).f) at hβ
    have H := (div_eq_div_iff (hD s β) (hD t β)).mp hβ
    rw [heval]
    exact sub_eq_zero.mpr H


end

end AronowAudit.P002
