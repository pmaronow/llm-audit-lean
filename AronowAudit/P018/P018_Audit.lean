import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction


/-!
P018: Aronow, Samii and Assenova (2015), pp. 564--577.
The printed claims and their corrections are kept separate.
All random designs below use probability measures, never the zero measure.
-/

noncomputable section
namespace AronowAudit.P018
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- "k-length column vector" (p. 566). Coordinates represent the paper's real vectors. -/
abbrev Vec (k : ℕ) := Fin k → ℝ
/-- "k x k" coefficient covariance matrices (equations (1)--(3), pp. 566--567). -/
abbrev Mat (k : ℕ) := Matrix (Fin k) (Fin k) ℝ

/-- "X_d" is a k-length column vector (p. 566). `outer x y` is X_d X_{d'}'. -/
def outer {k : ℕ} (x y : Vec k) : Mat k := fun a b => x a * y b


/-- Entrywise evaluation of a matrix-valued indicator, used in the finite
score sums of Proposition 2 and corrected Appendix C (pp. 568,575). -/
theorem matrix_ite_apply {k : ℕ} (p : Prop) [Decidable p] (A B : Mat k) (i j : Fin k) :
    (if p then A else B) i j = if p then A i j else B i j := by
  split_ifs <;> rfl

/-- "X'_d beta" is the scalar linear predictor (p. 566; corrected Appendix E, p. 576). -/
def dot {k : ℕ} (x y : Vec k) : ℝ := ∑ a, x a * y a

/-- "D = binom(N,2)" and "no d(i,i) type dyads" (p. 566).
Unordered dyads are two-element subsets of the N sampled units. -/
def dyads (N : ℕ) : Finset (Finset (Fin N)) := univ.powersetCard 2
/-- "D = binom(N,2)" unordered dyads, without self-dyads (p. 566). -/
abbrev Dyad (N : ℕ) := ↥(dyads N)

/-- The inverse correspondence "s(d(i,j)) = {i,j}" (p. 566). -/
def members {N : ℕ} (d : Dyad N) : Finset (Fin N) := d.val

/-- The definition of s(d) has exactly two distinct units (p. 566). -/
theorem members_card {N : ℕ} (d : Dyad N) : (members d).card = 2 := by
  exact (mem_powersetCard.mp d.property).2

/-- "S(d) ... the set of dyads other than d that share a member" (p. 566). -/
def neighbors {N : ℕ} (d : Dyad N) : Finset (Dyad N) :=
  univ.filter (fun q => q ≠ d ∧ (members d ∩ members q).Nonempty)

/-- Ordered equal-or-overlapping dyads, the I_{d,d'} in Appendix B (p. 574). -/
def overlap {N : ℕ} (d q : Dyad N) : Prop := (members d ∩ members q).Nonempty

instance {N : ℕ} (d q : Dyad N) : Decidable (overlap d q) :=
  inferInstanceAs (Decidable ((members d ∩ members q).Nonempty))

/-- "(X'X)^(-1) [meat] (X'X)^(-1)" (eq. (3), p. 567).
The argument P is the bread matrix; no rank is needed for finite algebra. -/
def sandwich {k : ℕ} (P M : Mat k) : Mat k := P * M * P

/-- "X_de_d" (eq. (3)); in the repeated case the block score is sum_t X_dt e_dt (p. 567). -/
def score {k : ℕ} (x : Vec k) (r : ℝ) : Vec k := r • x

/-- "sum_d [X_d X'_d e_d^2 + sum_{d' in S(d)} X_d X'_{d'} e_d e_{d'}]"
(eq. (3), p. 567), also the repeated block-score meat (Corollary 1). -/
def meat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (q : E → Vec k) : Mat k :=
  ∑ d, ∑ f, if (s d ∩ s f).Nonempty then outer (q d) (q f) else 0

/-- Cluster sum U_i = sum_{d: i in s(d)} X'_d e_d (Appendix C, pp. 574--575). -/
def unitScore {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (q : E → Vec k) (i : V) : Vec k :=
  ∑ d, if i ∈ s d then q d else 0

/-- "Sigma_D = sum_d X'_d e_d e'_d X_d" (Proposition 2, p. 568). -/
def dyadMeat {E : Type*} [Fintype E] {k : ℕ} (q : E → Vec k) : Mat k :=
  ∑ d, outer (q d) (q d)

/-- "Sigma_0 = sum_d sum_t X_dt X'_dt e_dt^2" (Proposition 2, p. 568). -/
def individualMeat {E : Type*} [Fintype E] {k : ℕ}
    (T : E → ℕ) (q : (d : E) → Fin (T d) → Vec k) : Mat k :=
  ∑ d, ∑ t, outer (q d t) (q d t)

/-- Corrected "E_i = sum_{j<k, j,k ne i} sum_t ..." (Appendix C, p. 575).
Each non-incident dyad is counted once. -/
def nonincidentMeat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (T : E → ℕ)
    (q : (d : E) → Fin (T d) → Vec k) (i : V) : Mat k :=
  ∑ d, if i ∉ s d then ∑ t, outer (q d t) (q d t) else 0

/-- Corrected "Sigma_{C,i}" (Proposition 2, p. 568): one cluster for incident
blocks, singleton clusters for each non-incident record. -/
def clusterMeat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (T : E → ℕ)
    (q : (d : E) → Fin (T d) → Vec k) (i : V) : Mat k :=
  outer (unitScore s (fun d => ∑ t, q d t) i)
    (unitScore s (fun d => ∑ t, q d t) i) + nonincidentMeat s T q i

/-- Two different two-element dyads share either zero or one unit;
identical dyads share two (the count used in Appendix C, pp. 574--575). -/
theorem intersection_count {V E : Type*} [DecidableEq V] [DecidableEq E]
    (s : E → Finset V) (hs : ∀ d, (s d).card = 2) (hinj : Function.Injective s)
    (d f : E) : ((s d ∩ s f).card : ℝ) =
      (if (s d ∩ s f).Nonempty then 1 else 0) + (if d = f then 1 else 0) := by
  classical
  by_cases hdf : d = f
  · subst f
    have hne : (s d).Nonempty := Finset.card_pos.mp (by rw [hs d]; omega)
    norm_num [hs d, hne]
  · have hc : (s d ∩ s f).card ≤ 2 := by
      calc
        _ ≤ (s d).card := Finset.card_le_card inter_subset_left
        _ = 2 := hs d
    have hn : (s d ∩ s f).card ≠ 2 := by
      intro h
      have h1 : s d ∩ s f = s d := Finset.eq_of_subset_of_card_le inter_subset_left (by rw [hs d, h])
      have h2 : s d ∩ s f = s f := Finset.eq_of_subset_of_card_le inter_subset_right (by rw [hs f, h])
      exact hdf (hinj (h1.symm.trans h2))
    by_cases he : (s d ∩ s f).Nonempty
    · have : (s d ∩ s f).card = 1 := by have := card_pos.mpr he; omega
      simp [he, hdf, this]
    · simp [he, hdf, Finset.not_nonempty_iff_eq_empty.mp he]

/-- The unit-cluster sum counts identical dyads twice and distinct overlapping
ordered pairs once (Appendix C, pp. 574--575; T3(b), T13(e), T14(ii), T18(i)). -/
theorem overlap_meat_identity {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (s : E → Finset V)
    (hs : ∀ d, (s d).card = 2) (hinj : Function.Injective s)
    {k : ℕ} (q : E → Vec k) :
    meat s q = (∑ i, outer (unitScore s q i) (unitScore s q i)) - dyadMeat q := by
  classical
  ext a b
  simp only [meat, unitScore, outer, Matrix.of_apply, dyadMeat, Matrix.sub_apply, Pi.sub_apply, Matrix.sum_apply, Finset.sum_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hswap : (∑ i : V, ∑ d : E, ∑ f : E,
      (if i ∈ s d then q d else 0) a*(if i ∈ s f then q f else 0) b) =
      ∑ d : E, ∑ f : E, ∑ i : V,
        (if i ∈ s d then q d else 0) a*(if i ∈ s f then q f else 0) b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_comm]
  rw [hswap]
  have hterm (d f : E) :
      (∑ i : V, (if i ∈ s d then q d else 0) a * (if i ∈ s f then q f else 0) b) =
        (if (s d ∩ s f).Nonempty then q d a * q f b else 0) +
        (if d = f then q d a * q f b else 0) := by
    have ht : (∑ i : V, (if i ∈ s d then q d else 0) a * (if i ∈ s f then q f else 0) b) =
        ((s d ∩ s f).card : ℝ) * (q d a * q f b) := by
      simp_rw [ite_apply, Pi.zero_apply]
      simp only [ite_mul, zero_mul, mul_ite, mul_zero]
      simp_rw [← ite_and]
      simp [← Finset.mem_inter, ← Finset.sum_filter, Finset.inter_comm]
    rw [ht, intersection_count s hs hinj d f, add_mul]
    split_ifs <;> ring
  simp_rw [hterm, Finset.sum_add_distrib]
  simp only [matrix_ite_apply,Matrix.zero_apply,outer, Matrix.of_apply,Finset.sum_ite_eq, mem_univ, if_true]
  ring

/-- Each two-element dyad avoids exactly N-2 units (Appendix C, p. 575). -/
theorem nonincident_sum {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (s : E → Finset V) (hs : ∀ d, (s d).card = 2)
    {k : ℕ} (T : E → ℕ) (q : (d : E) → Fin (T d) → Vec k) :
    (∑ i, nonincidentMeat s T q i) =
      ((Fintype.card V : ℝ) - 2) • individualMeat T q := by
  classical
  ext a b
  simp only [nonincidentMeat, individualMeat, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [matrix_ite_apply, Matrix.sum_apply, Matrix.zero_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hc (d : E) : ((univ.filter (fun i => i ∉ s d)).card : ℝ) = (Fintype.card V : ℝ) - 2 := by
    have he : univ.filter (fun i => i ∉ s d) = univ \ s d := by ext i; simp
    rw [he, card_sdiff_of_subset (subset_univ _), card_univ,
      Nat.cast_sub (Finset.card_le_univ (s d)), hs d]
    norm_num
  simp_rw [Finset.sum_const, nsmul_eq_mul, hc]
  rw [Finset.mul_sum]

/-- Proposition 2, corrected: the non-incident sum is over unordered dyads
once. This identity holds for all real record scores and every bread P (p. 568;
Appendix C, pp. 574--575), without any sampling or OLS assumptions. -/
theorem proposition2_corrected {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (s : E → Finset V)
    (hs : ∀ d, (s d).card = 2) (hinj : Function.Injective s)
    {k : ℕ} (T : E → ℕ) (q : (d : E) → Fin (T d) → Vec k) (P : Mat k) :
    let block := fun d => ∑ t, q d t
    meat s block = (∑ i, clusterMeat s T q i) - dyadMeat block -
      ((Fintype.card V : ℝ) - 2) • individualMeat T q ∧
    sandwich P (meat s block) = (∑ i, sandwich P (clusterMeat s T q i)) -
      sandwich P (dyadMeat block) -
      ((Fintype.card V : ℝ) - 2) • sandwich P (individualMeat T q) := by
  dsimp only
  have he := overlap_meat_identity s hs hinj (fun d => ∑ t, q d t)
  have hn := nonincident_sum s hs T q
  have hm : meat s (fun d => ∑ t, q d t) =
      (∑ i, clusterMeat s T q i) - dyadMeat (fun d => ∑ t, q d t) -
      ((Fintype.card V : ℝ) - 2) • individualMeat T q := by
    simp only [clusterMeat, Finset.sum_add_distrib]
    rw [hn, he]
    abel
  refine ⟨hm, ?_⟩
  rw [hm]
  simp only [sandwich, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]

/-- `expit(t)=1/(1+exp(-t))`, the predicted probability in Appendix E, p. 576. -/
def expit (t : ℝ) : ℝ := 1 / (1 + Real.exp (-t))

/-- Logistic "r_d=Y_d-p_d" and score "X_d(Y_d-p_d)" (Appendix E, p. 576). -/
def logisticScore {k : ℕ} (x : Vec k) (y : ℝ) (β : Vec k) : Vec k :=
  score x (y - expit (dot x β))

/-- Logistic bread "X'MX", M_dd=p_d(1-p_d) (Appendix E, p. 576). -/
def logisticBread {E : Type*} [Fintype E] {k : ℕ}
    (X : E → Vec k) (β : Vec k) : Mat k :=
  ∑ d, (expit (dot (X d) β) * (1 - expit (dot (X d) β))) • outer (X d) (X d)

/-- Corrected logistic estimator: cross term X_d X_{d'}' r_d r_{d'}
(Appendix E, p. 576; T14). -/
def logisticVariance {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (X : E → Vec k) (Y : E → ℝ) (β : Vec k) : Mat k :=
  sandwich (logisticBread X β)⁻¹ (meat s (fun d => logisticScore (X d) (Y d) β))

/-- The literal printed Appendix E meat uses X_d X_d' in the cross term (p. 576). -/
def printedLogisticMeat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (X : E → Vec k) (r : E → ℝ) : Mat k :=
  ∑ d, ∑ f, if (s d ∩ s f).Nonempty then (r d * r f) • outer (X d) (X d) else 0

/-- Multiplying two scores gives the corrected cross-regressor product
(Appendix E, p. 576, T14(i) and T23(iv)). -/
theorem score_product {k : ℕ} (x y : Vec k) (r t : ℝ) :
    outer (score x r) (score y t) = (r * t) • outer x y := by
  ext a b
  simp [outer, Matrix.of_apply, score]
  ring

/-- Logistic probabilities are real scalars strictly between zero and one
(Appendix E, corrected predictor, T23(i)). -/
theorem expit_bounds (t : ℝ) : 0 < expit t ∧ expit t < 1 := by
  have h := Real.exp_pos (-t)
  constructor
  · exact one_div_pos.mpr (by linarith)
  · dsimp [expit]
    apply (div_lt_iff₀ (by linarith : 0 < 1 + Real.exp (-t))).mpr
    linarith

/-- Corrected logistic score meat is symmetric (Appendix E, T14(ii)). -/
theorem meat_symmetric {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (q : E → Vec k) : (meat s q).transpose = meat s q := by
  classical
  ext a b
  simp only [Matrix.transpose_apply, meat, Matrix.sum_apply, Finset.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro f hf
  simp only [Finset.inter_comm (s f) (s d)]
  split_ifs <;> simp [outer, Matrix.of_apply, mul_comm]

/-- The explicit six unordered dyads of four units, in Table-witness order
{1,2},{1,3},{1,4},{2,3},{2,4},{3,4} (T13, T15, T17). -/
def sixMembers : Fin 6 → Finset (Fin 4) := ![{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}]


/-- Six-dyad logistic witness x=(0,2,5,5,1,1), Y=(1,1,1,0,0,0)
(T13, P018-E005, Appendix E p. 576). -/
def logitX : Fin 6 → Vec 2 := fun d => ![1, (![0,2,5,5,1,1] : Fin 6 → ℝ) d]
/-- Binary outcomes (1,1,1,0,0,0) in the T13 witness (P018-E005; Appendix E, p. 576). -/
def logitY : Fin 6 → ℝ := ![1,1,1,0,0,0]
/-- Fitted residuals r_d=Y_d-p_d in the T13 zero-parameter witness (Appendix E, p. 576). -/
def logitR : Fin 6 → ℝ := ![1/2,1/2,1/2,-1/2,-1/2,-1/2]
/-- The exact X'MX bread of the T13 witness (Appendix E, p. 576; P018-E005). -/
def logitH : Mat 2 := !![3/2,7/2;7/2,14]
/-- The inverse of X'MX in the T13 witness (Appendix E, p. 576; P018-E005). -/
def logitHinv : Mat 2 := !![8/5,-2/5;-2/5,6/35]

/-- The numerical logistic score is zero, the bread is nonsingular, and the
printed and corrected meats give distinct covariances (T13(b)--(d), p. 576).
This finite certificate does not establish uniqueness of the logistic MLE. -/
theorem logistic_numeric_certificate :
    (∑ d, score (logitX d) (logitR d)) = 0 ∧
    (∑ d, (1/4 : ℝ) • outer (logitX d) (logitX d)) = logitH ∧
    logitH.det = 35/4 ∧ logitHinv * logitH = 1 ∧
    printedLogisticMeat sixMembers logitX logitR = logitH ∧
    meat sixMembers (fun d => score (logitX d) (logitR d)) = !![3/2,7/2;7/2,27/2] ∧
    sandwich logitHinv logitH = logitHinv ∧
    sandwich logitHinv (!![3/2,7/2;7/2,27/2]) = !![38/25,-64/175;-64/175,192/1225] ∧
    sandwich logitHinv logitH ≠ sandwich logitHinv (!![3/2,7/2;7/2,27/2]) := by
  norm_num [logitX, logitR, logitH, logitHinv, score, outer, Matrix.of_apply, sandwich,
    printedLogisticMeat, meat, sixMembers, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.vecMul, dotProduct, Matrix.det_fin_two,
    Fin.sum_univ_succ, Matrix.one_apply, funext_iff, funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]


/-- The sample Gram matrix X'X (p. 566). -/
def sampleGram {E : Type*} [Fintype E] {k : ℕ} (X : E → Vec k) : Mat k :=
  ∑ d, outer (X d) (X d)

/-- "beta_hat = (X'X)^(-1) X'Y" (p. 566); the inverse is totalized only
on singular samples, a convention irrelevant on the full-rank witnesses. -/
def sampleOLS {E : Type*} [Fintype E] {k : ℕ} (X : E → Vec k) (Y : E → ℝ) : Vec k :=
  (sampleGram X)⁻¹.mulVec (∑ d, score (X d) (Y d))

/-- "e_d = Y_d - X'_d beta_hat" (p. 566), distinct from population epsilon. -/
def fittedResidual {E : Type*} [Fintype E] {k : ℕ}
    (X : E → Vec k) (Y : E → ℝ) (d : E) : ℝ := Y d - dot (X d) (sampleOLS X Y)

/-- The dyadic variance estimator of equation (3), p. 567. -/
def sampleVariance {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (X : E → Vec k) (Y : E → ℝ) : Mat k :=
  sandwich (sampleGram X)⁻¹ (meat s (fun d => score (X d) (fittedResidual X Y d)))

/-- First- and second-role incidence in the N=3 witness (T5(d), eq. (4), p. 569). -/
def roleZ1 : Matrix (Fin 3) (Fin 3) ℝ := !![1,0,0;1,0,0;0,1,0]
/-- Second-role incidence in the T5 three-unit witness (P018-E008, correcting the comparison on pp. 569--570). -/
def roleZ2 : Matrix (Fin 3) (Fin 3) ℝ := !![0,1,0;0,0,1;0,0,1]

/-- Shared-node covariance "C=ZZ'+I" for design (4) (p. 569, T5--T6). -/
def sharedCov3 (τ σ : ℝ) : Mat 3 :=
  τ • ((roleZ1 + roleZ2) * (roleZ1 + roleZ2).transpose) + σ • 1

/-- Covariance family "t1 Z1 Z1' + t2 Z2 Z2' + s I" of the fitted
two-role comparison (T5--T6; replication formula recorded in P018-E008). -/
def twoRoleCov3 (t1 t2 σ : ℝ) : Mat 3 :=
  t1 • (roleZ1 * roleZ1.transpose) + t2 • (roleZ2 * roleZ2.transpose) + σ • 1

/-- Exact N=3 covariance mismatch for every nonnegative working parameter:
dyads {1,2} and {2,3} have covariance one in design (4) and zero in the
fitted family (T5(c)--(d), pp. 569--570). -/
theorem two_role_counterexample (t1 t2 σ : ℝ) :
    sharedCov3 1 1 = !![3,1,1;1,3,1;1,1,3] ∧
    twoRoleCov3 t1 t2 σ = !![t1+t2+σ,t1,0;t1,t1+t2+σ,t2;0,t2,t1+t2+σ] ∧
    sharedCov3 1 1 ≠ twoRoleCov3 t1 t2 σ := by
  have h1 : sharedCov3 1 1 = !![3,1,1;1,3,1;1,1,3] := by
    norm_num [sharedCov3, roleZ1, roleZ2, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Matrix.one_apply, funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]
  have h2 : twoRoleCov3 t1 t2 σ = !![t1+t2+σ,t1,0;t1,t1+t2+σ,t2;0,t2,t1+t2+σ] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [twoRoleCov3, roleZ1, roleZ2, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]
  refine ⟨h1, h2, ?_⟩
  intro h
  have := congrArg (fun M : Mat 3 => M 0 2) h
  rw [h1, h2] at this
  norm_num at this

/-- A single shared-node effect supplies both missing role-cross terms
(T6(ii)--(iii), corrected benchmark, pp. 569--570). -/
theorem shared_role_expansion {m n : ℕ} (Z1 Z2 : Matrix (Fin m) (Fin n) ℝ)
    (τ σ : ℝ) :
    τ • ((Z1 + Z2) * (Z1 + Z2).transpose) + σ • (1 : Mat m) =
      τ • (Z1 * Z1.transpose + Z2 * Z2.transpose +
        Z1 * Z2.transpose + Z2 * Z1.transpose) + σ • 1 := by
  simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
  congr 2
  abel

/-- Exact GLS design and working bread in the T5(e) witness (P018-E008). -/
def glsF : Matrix (Fin 3) (Fin 2) ℝ := !![1,1;1,3;1,2]
/-- Fixed working covariance inverse in the T5 GLS witness (P018-E008, pp. 569--570). -/
def glsWinv : Mat 3 := (1/21 : ℝ) • !![8,-3,1;-3,9,-3;1,-3,8]
/-- Reported GLS coefficient covariance in the T5 witness (P018-E008, pp. 569--570). -/
def glsR : Mat 2 := (1/16 : ℝ) • !![71,-27;-27,15]
/-- Linear GLS coefficient map in the T5 witness (P018-E008, pp. 569--570). -/
def glsL : Matrix (Fin 2) (Fin 3) ℝ := !![19/16,-13/16,5/8;-7/16,9/16,-1/8]

/-- The working GLS estimator is unbiased, but its reported intercept
variance 71/16 differs from the actual 379/64 (T5(e), P018-E008).
Components are fixed at one; this asserts nothing about fitted REML limits. -/
theorem gls_variance_counterexample :
    glsWinv * twoRoleCov3 1 1 1 = 1 ∧
    glsR * (glsF.transpose * glsWinv * glsF) = 1 ∧
    glsR * glsF.transpose * glsWinv = glsL ∧ glsL * glsF = 1 ∧
    glsL * sharedCov3 1 1 * glsL.transpose = (1/64 : ℝ) • !![379,-135;-135,67] ∧
    glsR 0 0 / (glsL * sharedCov3 1 1 * glsL.transpose) 0 0 = 284/379 ∧
    (284/379 : ℝ) < 1 := by
  have ht := (two_role_counterexample (1 : ℝ) 1 1).2.1
  have hc := (two_role_counterexample (1 : ℝ) 1 1).1
  rw [ht,hc]
  and_intros
  all_goals first
    | (ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [glsWinv,glsR,glsF,glsL,twoRoleCov3,sharedCov3,roleZ1,roleZ2,
          Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply,Matrix.vecMul,dotProduct,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_succ,Matrix.one_apply])
    | norm_num [glsWinv,glsR,glsF,glsL,twoRoleCov3,sharedCov3,roleZ1,roleZ2,
        Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply,Matrix.vecMul,dotProduct,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_succ,Matrix.one_apply]


/-- GLS with the true symmetric invertible covariance C has exactly the
reported covariance and LF=I (T6(iv)); nonsingularity of F'C^(-1)F is the
algebraic consequence of positive definiteness and full column rank. -/
theorem correct_gls_identity {m k : ℕ} (C : Mat m)
    (F : Matrix (Fin m) (Fin k) ℝ) (hC : IsUnit C.det)
    (hsym : C.transpose = C) (hG : IsUnit (F.transpose * C⁻¹ * F).det) :
    let G := F.transpose * C⁻¹ * F
    let L := G⁻¹ * F.transpose * C⁻¹
    L * F = 1 ∧ L * C * L.transpose = G⁻¹ := by
  dsimp only
  have hi : C⁻¹.transpose = C⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsym]
  have hgs : (F.transpose * C⁻¹ * F).transpose = F.transpose * C⁻¹ * F := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hi, Matrix.mul_assoc]
  have hgi : (F.transpose * C⁻¹ * F)⁻¹.transpose = (F.transpose * C⁻¹ * F)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hgs]
  constructor
  · simpa only [Matrix.mul_assoc] using Matrix.nonsing_inv_mul _ hG
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hi, hgi]
    calc
      _ = (F.transpose * C⁻¹ * F)⁻¹ * (F.transpose * C⁻¹ * F) *
          (F.transpose * C⁻¹ * F)⁻¹ := by
            simp only [Matrix.mul_assoc, ← Matrix.mul_assoc C⁻¹ C,
              Matrix.nonsing_inv_mul C hC, Matrix.one_mul]
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]

/-- Scores 1,2,3,4,5,6 on the six dyads (T15(b), Proposition 2 p. 568). -/
def orderedWitness : Fin 6 → Vec 1 := fun d => ![(![1,2,3,4,5,6] : Fin 6 → ℝ) d]

/-- The ordered reading of the non-incident term gives 567 instead of 385
in a fully explicit six-dyad algebraic instance (T15(b), pp. 568 and 575). -/
theorem ordered_index_counterexample :
    dyadMeat orderedWitness = !![91] ∧
    meat sixMembers orderedWitness = !![385] ∧
    (∑ i : Fin 4, outer (unitScore sixMembers orderedWitness i)
      (unitScore sixMembers orderedWitness i)) = !![476] ∧
    (∑ i : Fin 4, nonincidentMeat sixMembers (fun _ => 1)
      (fun d _ => orderedWitness d) i) = !![182] ∧
    (476 + 2 * 182 - 91 - 2 * 91 : ℝ) = 567 ∧ (567 : ℝ) ≠ 385 := by
  norm_num [orderedWitness, dyadMeat, meat, outer, Matrix.of_apply, unitScore, nonincidentMeat,
    sixMembers, Fin.sum_univ_succ, funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]

/-- Negative-variance-estimate witness with a full-rank intercept-and-slope
sample and actual OLS residuals (T17(c), p. 567; P018-N003). -/
def negativeX : Fin 6 → Vec 2 := fun d => ![1, (![1,2,3,1,2,1] : Fin 6 → ℝ) d]
/-- Response values in the T17 full-rank negative-variance sample (P018-N003, equation (3), p. 567). -/
def negativeY : Fin 6 → ℝ := ![4,3,5,3,3,4]
/-- OLS residuals in the T17 negative-variance sample (P018-N003, equation (3), p. 567). -/
def negativeE : Fin 6 → ℝ := ![3/5,-4/5,4/5,-2/5,-4/5,3/5]
/-- Inverse sample X'X in the T17 negative-variance sample (P018-N003, p. 567). -/
def negativeGinv : Mat 2 := !![1,-1/2;-1/2,3/10]

/-- Equation (3) can have both diagonals negative with a full-rank design
and least-squares residuals (T17(c)). -/
theorem negative_ols_certificate :
    sampleGram negativeX = !![6,10;10,20] ∧
    (sampleGram negativeX).det = 20 ∧
    sampleOLS negativeX negativeY = ![3,2/5] ∧
    (∀ d, fittedResidual negativeX negativeY d = negativeE d) ∧
    (∑ d, score (negativeX d) (negativeE d)) = 0 ∧
    sampleVariance sixMembers negativeX negativeY = !![-17/50,21/125;21/125,-58/625] ∧
    (sampleVariance sixMembers negativeX negativeY) 0 0 < 0 ∧
    (sampleVariance sixMembers negativeX negativeY) 1 1 < 0 := by
  have hg : sampleGram negativeX = !![6,10;10,20] := by
    norm_num [sampleGram, outer, Matrix.of_apply, negativeX, Fin.sum_univ_succ,
      funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]
  have hinv : (sampleGram negativeX)⁻¹ = negativeGinv := by
    apply Matrix.inv_eq_left_inv
    rw [hg]
    norm_num [negativeGinv, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_succ,
      Matrix.one_apply, funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]
  have hb : sampleOLS negativeX negativeY = ![3,2/5] := by
    simp only [sampleOLS, hinv]
    norm_num [negativeGinv, negativeX, negativeY, score, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]
  have he : ∀ d, fittedResidual negativeX negativeY d = negativeE d := by
    intro d
    simp only [fittedResidual, hb]
    fin_cases d <;> norm_num [negativeX, negativeY, negativeE,
      dot, Fin.sum_univ_succ]
  have hv : sampleVariance sixMembers negativeX negativeY = !![-17/50,21/125;21/125,-58/625] := by
    simp only [sampleVariance, hinv, he]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sandwich, negativeGinv, meat, score, outer, Matrix.of_apply, sixMembers, negativeX,
      negativeE, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_succ, funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]
  refine ⟨hg, ?_, hb, he, ?_, hv, ?_, ?_⟩
  · rw [hg]; norm_num [Matrix.det_fin_two]
  · norm_num [score, negativeX, negativeE, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]
  · rw [hv]; norm_num
  · rw [hv]; norm_num

/-- Standard error has a restricted real domain (T18(iv), correction to
p. 567): negative entries give `none`, not Lean's totalized Real.sqrt. -/
def standardError (v : ℝ) : Option ℝ := if 0 ≤ v then some (Real.sqrt v) else none

/-- A real square root standard error exists exactly for nonnegative entries
(T18(iv)). -/
theorem standard_error_domain (v : ℝ) :
    (∃ se, standardError v = some se) ↔ 0 ≤ v := by
  by_cases hv : 0 ≤ v <;> simp [standardError, hv]

/-- Truncation at zero is 1-Lipschitz (T18(ii), p. 567 correction). -/
theorem truncation_contraction (a b : ℝ) : |max a 0 - max b 0| ≤ |a-b| := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · simp [max_eq_left ha, max_eq_left hb]
  · rw [max_eq_left ha, max_eq_right (le_of_not_ge hb)]
    simp only [sub_zero]
    rw [abs_of_nonneg ha, abs_of_nonneg (by linarith)]
    linarith
  · rw [max_eq_right (le_of_not_ge ha), max_eq_left hb]
    rw [zero_sub, abs_neg, abs_of_nonneg hb, abs_of_nonpos (by linarith)]
    linarith
  · simp [max_eq_right (le_of_not_ge ha), max_eq_right (le_of_not_ge hb)]

/-- N-scaled truncation cannot increase the error when the target diagonal
is nonnegative (T18(ii)). -/
theorem scaled_truncation (N : ℝ) (hN : 0 ≤ N) (v V : ℝ) (hV : 0 ≤ V) :
    |N * max v 0 - V| ≤ |N*v - V| := by
  have he : N * max v 0 = max (N*v) 0 := by
    by_cases hv : 0 ≤ v
    · simp [max_eq_left hv, max_eq_left (mul_nonneg hN hv)]
    · simp [max_eq_right (le_of_not_ge hv), max_eq_right (mul_nonpos_of_nonneg_of_nonpos hN (le_of_not_ge hv))]
  rw [he]
  simpa only [max_eq_left hV] using truncation_contraction (N*v) V

/-- A negative estimate is contained in the deviation event of size V
when V>0 (T18(iii)). -/
theorem negative_implies_deviation (N : ℝ) (hN : 0 ≤ N) (v V : ℝ)
    (hV : 0 < V) (hv : v < 0) : V ≤ |N*v-V| := by
  have : N*v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN hv.le
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- The Table 1 standard errors, columns (4),(5),(6), in printed row order
(p. 572). Exact rationals represent the printed decimal values. -/
def tableSE : List (ℚ × ℚ × ℚ) :=
  [(69/1000,175/1000,265/1000),(20/1000,47/1000,70/1000),
   (5/1000,10/1000,15/1000),(10734/1000,17560/1000,24749/1000),
   (2/1000,5/1000,8/1000),(74/1000,181/1000,185/1000),
   (26/1000,68/1000,102/1000),(78/1000,188/1000,344/1000),
   (211/1000,562/1000,840/1000)]

/-- The nine Table 1 ratios lie between 24749/10734 and 172/39, below five;
D>C>H, with D/C between 185/181 and 86/47 (T24(i),(iii), pp. 571--572). -/
theorem table_ratios_corrected :
    ∀ r ∈ tableSE,
      24749/10734 ≤ r.2.2/r.1 ∧ r.2.2/r.1 ≤ 172/39 ∧ r.2.2/r.1 < 5 ∧
      r.1 < r.2.1 ∧ r.2.1 < r.2.2 ∧
      185/181 ≤ r.2.2/r.2.1 ∧ r.2.2/r.2.1 ≤ 86/47 := by
  norm_num [tableSE]

/-- No underlying real SEs that round to Table 1 can have a tenfold ratio;
the worst rounding bound is 17/3 (T24(ii), pp. 571--572). -/
theorem table_rounding_constraints :
    ∀ r ∈ tableSE,
      0 < (r.1 : ℝ)-1/2000 ∧
      (r.2.2 : ℝ)+1/2000 < 10*((r.1 : ℝ)-1/2000) ∧
      ((r.2.2 : ℝ)+1/2000)/((r.1 : ℝ)-1/2000) ≤ 17/3 := by
  norm_num [tableSE]

/-- All values in the conservative rounding intervals have D/H<10
(T24(ii)). -/
theorem table_rounding_ratio (r : ℚ × ℚ × ℚ) (hr : r ∈ tableSE) (h d : ℝ)
    (hh : (r.1 : ℝ)-1/2000 ≤ h) (hd : d ≤ (r.2.2 : ℝ)+1/2000) : d/h < 10 := by
  obtain ⟨hp,hb,_⟩ := table_rounding_constraints r hr
  have hpos : 0 < h := lt_of_lt_of_le hp hh
  apply (div_lt_iff₀ hpos).mpr
  linarith

/- The HC significance-ratio implication of T24(iv) is false without a
positivity assumption on se: se=0 and se<0 give counterexamples.
The printed table has positive standard errors. -/



/-- Exact obstruction to the literal final implication of T24(iv):
b=21/2000 and se=0 meet its inequalities but give a ratio below 21/5.
Real division is totalized at zero; se=-1 provides the same obstruction
with a nonzero denominator. These do not challenge the printed positive SE. -/
theorem significance_rounding_literal_fails :
    (21/2000 : ℝ) ≤ |21/2000| ∧ (0 : ℝ) ≤ 5/2000 ∧
    ¬((21/5 : ℝ) ≤ |21/2000|/0) ∧
    (-1 : ℝ) ≤ 5/2000 ∧ ¬((21/5 : ℝ) ≤ |21/2000|/(-1)) := by
  norm_num


/-- The main correction to the Table 1 magnitude claim, pp. 571--572
(T24): exact extreme ratios, all displayed comparisons, and rounding bounds. -/
theorem table_magnitude_correction :
    (24749/1000 : ℚ)/(10734/1000) = 24749/10734 ∧
    (344/1000 : ℚ)/(78/1000) = 172/39 ∧
    (∀ r ∈ tableSE, 24749/10734 ≤ r.2.2/r.1 ∧ r.2.2/r.1 ≤ 172/39 ∧ r.2.2/r.1 < 5 ∧
      r.1 < r.2.1 ∧ r.2.1 < r.2.2 ∧ 185/181 ≤ r.2.2/r.2.1 ∧ r.2.2/r.2.1 ≤ 86/47) ∧
    (∀ (r : ℚ × ℚ × ℚ), r ∈ tableSE → ∀ h d : ℝ,
      (r.1 : ℝ)-1/2000 ≤ h → d ≤ (r.2.2 : ℝ)+1/2000 → d/h < 10) ∧
    (11/8 : ℝ) < 41/25 := by
  refine ⟨by norm_num, by norm_num, table_ratios_corrected, ?_, by norm_num⟩
  exact fun r hr h d hh hd => table_rounding_ratio r hr h d hh hd


/-! Probability objects: every variance is an actual covariance integral;
statements about finite-sample moments assert L2 membership explicitly. -/

/-- Expectations of coefficient vectors over unit sampling (p. 566). -/
def meanVec {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (μ : Measure Ω) (f : Ω → Vec k) : Vec k :=
  fun a => ∫ ω, f ω a ∂ μ

/-- A matrix of unconditional expectations (eqs. (1),(6), pp. 566,573). -/
def meanMat {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (μ : Measure Ω) (f : Ω → Mat k) : Mat k :=
  fun a b => ∫ ω, f ω a b ∂ μ

/-- Covariance of two vector scores, entry by entry (eq. (6), p. 573). -/
def covMat {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (f g : Ω → Vec k) : Mat k :=
  fun a b => ProbabilityTheory.covariance (fun ω => f ω a) (fun ω => g ω b) μ

/-- "Var[sum_d X_d epsilon_d]" (eq. (1), p. 566). -/
def varMat {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (μ : Measure Ω) (f : Ω → Vec k) : Mat k :=
  covMat μ f f

/-- In-probability convergence as N grows, also for changing sample spaces.
For each positive epsilon the probability of norm error >=epsilon tends to zero.
This is a convergence predicate, not a variance or an expectation hypothesis. -/
def inProbability {Ω : ℕ → Type*} [∀ N : ℕ, MeasurableSpace (Ω N)]
    {E : Type*} [NormedAddCommGroup E] (μ : ∀ N : ℕ, Measure (Ω N))
    (f : ∀ N : ℕ, Ω N → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun N : ℕ => (μ N {ω | ε ≤ ‖f N ω‖}).toReal) atTop (𝓝 0)

/-- Weak convergence of laws, expressed by every bounded continuous real
function. The functions are a.e. measurable; used for printed distributional
claims and the corrected projection CLT (pp. 566--567). -/
def weakLimit {Ω : ℕ → Type*} [∀ N : ℕ, MeasurableSpace (Ω N)]
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : ∀ N : ℕ, Measure (Ω N)) (f : ∀ N : ℕ, Ω N → E) (ν : Measure E) : Prop :=
  (∀ N : ℕ, AEMeasurable (f N) (μ N)) ∧ IsProbabilityMeasure ν ∧
  ∀ g : E →ᵇ ℝ, Tendsto (fun N : ℕ => ∫ ω, g (f N ω) ∂ μ N) atTop (𝓝 (∫ x, g x ∂ ν))

/-- A mean-zero multivariate normal law, possibly singular: every contrast
has the mean-zero Gaussian law with variance c'Vc (T8, projection CLT). -/
def centeredNormalLaw {k : ℕ} (ν : Measure (Vec k)) (V : Mat k) : Prop :=
  V.PosSemidef ∧ IsProbabilityMeasure ν ∧ ∀ c : Vec k,
    ν.map (fun x => dot c x) = gaussianReal 0 (dot c (V.mulVec c)).toNNReal

/-- Data "determined by the characteristics of the units i and j" (p. 566).
`μ` is the unit law; `X,Y` are the same symmetric measurable dyad kernels.
The standing assumptions below require μ to be a probability measure. -/
structure Kernel (U : Type*) [MeasurableSpace U] (k : ℕ) where
  μ : Measure U
  X : U → U → Vec k
  Y : U → U → ℝ

/-- "random (i.i.d.) sample of units" (p. 566), realized as the finite product law. -/
def unitSampleLaw {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) (N : ℕ) :
    Measure (Fin N → U) := Measure.pi (fun _ => K.μ)

/-- Q=E[X_d X'_d], the population coefficient Gram matrix (eq. (1), p. 566). -/
def populationGram {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Mat k :=
  meanMat (K.μ.prod K.μ) (fun uv => outer (K.X uv.1 uv.2) (K.X uv.1 uv.2))

/-- "beta is the slope ... if we could fit ... to the entire population"
(p. 566), interpreted as the least-squares projection Q^(-1)E[XY]. -/
def populationBeta {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Vec k :=
  (populationGram K)⁻¹.mulVec (meanVec (K.μ.prod K.μ) (fun uv => score (K.X uv.1 uv.2) (K.Y uv.1 uv.2)))

/-- "epsilon ... corresponding population residual" (p. 566), retaining
possible nonlinear conditional means and dependence on regressors. -/
def populationResidual {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (u v : U) : ℝ := K.Y u v - dot (K.X u v) (populationBeta K)

/-- The smaller endpoint i of the unordered dyad d(i,j) (p. 566). -/
def firstUnit {N : ℕ} (d : Dyad N) : Fin N :=
  (members d).min' (Finset.card_pos.mp (by rw [members_card]; omega))
/-- The larger endpoint j of the unordered dyad d(i,j) (p. 566). -/
def secondUnit {N : ℕ} (d : Dyad N) : Fin N :=
  (members d).max' (Finset.card_pos.mp (by rw [members_card]; omega))

/-- The whole sample design "bold X=(X_1 ... X_D)'" (p. 566). -/
def design {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k)
    (ω : Fin N → U) : Dyad N → Vec k :=
  fun d => K.X (ω (firstUnit d)) (ω (secondUnit d))

/-- "Y = (Y_1 ... Y_D)'" (p. 566), evaluated on the sampled unit characteristics. -/
def response {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k)
    (ω : Fin N → U) : Dyad N → ℝ :=
  fun d => K.Y (ω (firstUnit d)) (ω (secondUnit d))

/-- "corresponding population residual" epsilon_d (p. 566), evaluated on the sampled units. -/
def epsilon {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k)
    (ω : Fin N → U) (d : Dyad N) : ℝ :=
  populationResidual K (ω (firstUnit d)) (ω (secondUnit d))

/-- The population score h_d=X_d epsilon_d (eq. (1), p. 566). -/
def populationScore {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (u v : U) : Vec k := score (K.X u v) (populationResidual K u v)

/-- "sum_d X_d epsilon_d" in equations (1)--(2) (p. 566). -/
def scoreSum {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k) (ω : Fin N → U) : Vec k :=
  ∑ d : Dyad N, score (design K ω d) (epsilon K ω d)

/-- The standing model (p. 566): a genuine unit
probability law, bounded symmetric measurable dyad data, an intercept, and a
nonsingular population Gram matrix. No conditional mean-zero assumption. -/
def Standing {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Prop :=
  IsProbabilityMeasure K.μ ∧
  Measurable (fun uv : U × U => K.X uv.1 uv.2) ∧
  Measurable (fun uv : U × U => K.Y uv.1 uv.2) ∧
  (∀ u v, K.X u v = K.X v u ∧ K.Y u v = K.Y v u) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ uv ∂ K.μ.prod K.μ, ‖K.X uv.1 uv.2‖ ≤ C ∧ |K.Y uv.1 uv.2| ≤ C) ∧
  (∃ j : Fin k, ∀ u v, K.X u v j = 1) ∧ (populationGram K).det ≠ 0

/-- "X_d and e_d ... bounded support with nonzero second moments and
cross-moments" (Proposition 1, p. 567). Residual moments are those of the
sample-fitted e_d, over the entire N-unit design, and hold eventually in N.
This asymptotic quantifier avoids requiring nonzero residuals in saturated
small samples. Regressor moments are interpreted entrywise. -/
def Proposition1Extra {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ᵐ ω ∂ unitSampleLaw K N,
    ∀ d, |fittedResidual (design K ω) (response K ω) d| ≤ C) ∧
  (∀ a b, (populationGram K) a b ≠ 0) ∧
  (∀ a b, (meanMat (Measure.pi (fun _ : Fin 3 => K.μ)) (fun u =>
    outer (K.X (u 0) (u 1)) (K.X (u 0) (u 2)))) a b ≠ 0) ∧
  (∀ᶠ N : ℕ in atTop,
    (∀ d : Dyad N, (∫ ω, (fittedResidual (design K ω) (response K ω) d)^2
      ∂ unitSampleLaw K N) ≠ 0) ∧
    (∀ d f : Dyad N, f ∈ neighbors d →
      (∫ ω, fittedResidual (design K ω) (response K ω) d *
        fittedResidual (design K ω) (response K ω) f ∂ unitSampleLaw K N) ≠ 0))


/-- Almost-sure sample rank, when required literally (Appendix A, p. 573).
Asymptotic corrections allow arbitrary definitions on singular samples. -/
def SampleRank {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Prop :=
  ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ᵐ ω ∂ unitSampleLaw K N, (sampleGram (design K ω)).det ≠ 0

/-- D=binom(N,2), as a real normalization (p. 566). -/
def Dreal (N : ℕ) : ℝ := (N : ℝ) * ((N : ℝ)-1) / 2

/-- Equation (1)'s true unconditional covariance target; it depends on N. -/
def trueTarget {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) (N : ℕ) : Mat k :=
  ((N : ℝ) / (Dreal N)^2) • sandwich (populationGram K)⁻¹
    (varMat (unitSampleLaw K N) (scoreSum K))

/-- Conditioning on the entire design bold X (eq. (2), p. 566), the
comap sigma-algebra of the full random array of regressors. -/
def designSigma {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k) :
    MeasurableSpace (Fin N → U) := MeasurableSpace.comap (design K) inferInstance

/-- m_d=E[epsilon_d | bold X], using actual conditional expectation (T2(iii)). -/
def conditionalResidualMean {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (d : Dyad N) : (Fin N → U) → ℝ :=
  MeasureTheory.condExp (designSigma K) (unitSampleLaw K N) (fun ω => epsilon K ω d)

/-- Conditional covariance of population residuals, centered by their
conditional means (eqs. (2),(6), pp. 566,573). It is not E[epsilon_d epsilon_q|X]. -/
def conditionalResidualCov {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (d f : Dyad N) : (Fin N → U) → ℝ :=
  MeasureTheory.condExp (designSigma K) (unitSampleLaw K N) (fun ω =>
    (epsilon K ω d - conditionalResidualMean K d ω) *
    (epsilon K ω f - conditionalResidualMean K f ω))

/-- E[X_d X_f' Cov(epsilon_d,epsilon_f|bold X)] (eq. (6), p. 573). -/
def conditionalTerm {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (d f : Dyad N) : Mat k :=
  meanMat (unitSampleLaw K N) (fun ω =>
    conditionalResidualCov K d f ω • outer (design K ω d) (design K ω f))

/-- The printed Sigma, with only equal/overlapping conditional terms
(eq. (2), p. 566; Appendix B, p. 573). -/
def printedSigma {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) (N : ℕ) : Mat k :=
  ∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then conditionalTerm K d f else 0

/-- The corrected unconditional score-moment Sigma_N^* (T2(ii), eq. (2) repair). -/
def correctedSigma {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) (N : ℕ) : Mat k :=
  meanMat (unitSampleLaw K N) (fun ω => meat members (fun d => score (design K ω d) (epsilon K ω d)))

/-- Same-dyad score moment H and unit projection Gamma (T2(v), T8).
The projection g integrates an independent neighbor with respect to the unit law. -/
def scoreH {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Mat k :=
  meanMat (K.μ.prod K.μ) (fun uv => outer (populationScore K uv.1 uv.2) (populationScore K uv.1 uv.2))
/-- The unit-score projection g(u)=E[h(u,U')] in corrected T2(v), T8 (P018-E001/P018-E002). -/
def projection {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) (u : U) : Vec k :=
  meanVec K.μ (populationScore K u)
/-- Gamma=E[g(U)g(U)'] in corrected T2(v), T8 (P018-E001/P018-E002). -/
def projectionGamma {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Mat k :=
  meanMat K.μ (fun u => outer (projection K u) (projection K u))
/-- The corrected limit 4 Q^(-1) Gamma Q^(-1) (T2(v), T8, P018-E001/P018-E002). -/
def limitingTarget {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Mat k :=
  (4 : ℝ) • sandwich (populationGram K)⁻¹ (projectionGamma K)


/-- The first equality of equation (6) is an exact sum-of-covariances identity
for all finite L2 scores (T26(F3), p. 573), independent of the false later lines. -/
theorem variance_sum_identity {Ω E : Type*} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} (q : E → Ω → Vec k)
    (hq : ∀ d a, MemLp (fun ω => q d ω a) 2 μ) :
    varMat μ (fun ω => ∑ d, q d ω) = ∑ d, ∑ f, covMat μ (q d) (q f) := by
  ext a b
  simp only [varMat, covMat, Matrix.sum_apply, Finset.sum_apply]
  exact ProbabilityTheory.covariance_fun_sum_fun_sum (fun d => hq d a) (fun f => hq f b)

/-- The unscaled coefficient error β̂ − β, used in the Appendix A and
corrected Appendix B arguments (T4). -/
def coefficientError {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (ω : Fin N → U) : Vec k := sampleOLS (design K ω) (response K ω) - populationBeta K

/-- M_N(r)=(N/D^2) times the overlapping residual-product meat (T4, replacement for Appendix B, pp. 573--574). -/
def scaledMeat {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (r : (Fin N → U) → Dyad N → ℝ) (ω : Fin N → U) : Mat k :=
  ((N : ℝ)/(Dreal N)^2) • meat members (fun d => score (design K ω d) (r ω d))


/-- Exact algebraic last step of the replacement consistency proof
(T4(L6), Appendix B correction, pp. 573--574). -/
theorem sandwich_difference {k : ℕ} (BN B M T : Mat k) :
    BN*M*BN - B*T*B = BN*(M-T)*BN + (BN-B)*T*BN + B*T*(BN-B) := by
  noncomm_ring

/-- Correct Chebyshev/Markov condition for a real estimator Z=N Vhat:
its variance plus squared mean error controls squared error (T4, p. 573).
The probability bound and sufficiency are stated with finite L2 moments. -/
theorem corrected_chebyshev {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : MemLp Z 2 μ) (V c : ℝ) (hc : 0 < c) :
    (μ {ω | c < |Z ω - V|}).toReal ≤
      (c⁻¹)^2 * (ProbabilityTheory.variance Z μ + ((∫ ω, Z ω ∂ μ)-V)^2) := by
  have hY : MemLp (fun ω => Z ω-V) 2 μ := hZ.sub (memLp_const V)
  have hmean : (∫ ω, Z ω-V ∂ μ) = (∫ ω, Z ω ∂ μ)-V := by
    rw [integral_sub (hZ.integrable one_le_two) (integrable_const V)]
    simp
  have hrisk : (∫ ω, (Z ω-V)^2 ∂ μ) =
      ProbabilityTheory.variance Z μ+((∫ ω, Z ω ∂ μ)-V)^2 := by
    have h := ProbabilityTheory.variance_eq_sub hY
    rw [ProbabilityTheory.variance_sub_const hZ.aestronglyMeasurable V, hmean] at h
    simpa only [Pi.pow_apply] using (eq_add_of_sub_eq h.symm)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (Z ω-V))) hY.integrable_sq (c^2)
  have hsub : (μ {ω | c < |Z ω-V|}).toReal ≤ (μ {ω | c^2 ≤ (Z ω-V)^2}).toReal := by
    apply ENNReal.toReal_mono (measure_ne_top μ _)
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    nlinarith [sq_abs (Z ω-V)]
  have hbound : (μ {ω | c < |Z ω-V|}).toReal ≤
      (ProbabilityTheory.variance Z μ+((∫ ω, Z ω ∂ μ)-V)^2)/c^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    rw [← hrisk]
    calc
      _ ≤ c^2*(μ {ω | c^2 ≤ (Z ω-V)^2}).toReal := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsub (sq_nonneg c)
      _ ≤ _ := hmark
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using hbound


/-- Uniform[-1,1] unit law, normalized restriction of Lebesgue measure
(T1, P018-E001, eq. (2) counterexample). -/
def uniformUnitLaw : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)

instance : IsProbabilityMeasure uniformUnitLaw := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · norm_num [Real.volume_Icc]
  · norm_num [Real.volume_Icc]


/-- Actual monomial moments of the iid Uniform[-1,1] unit law in the
nonlinear counterexample (T1(a),(c), P018-E001). The expectation
is with respect to the normalized Lebesgue restriction, not assigned constants. -/
theorem uniform_unit_moment (n : ℕ) :
    (∫ z, z^n ∂ uniformUnitLaw) =
      (1-(-1 : ℝ)^(n+1))/(2*(n+1 : ℝ)) := by
  calc
    _ = (1/2 : ℝ)*(∫ z in (-1 : ℝ)..1, z^n) := by
      unfold uniformUnitLaw ProbabilityTheory.cond
      rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      norm_num [Real.volume_Icc]
    _ = _ := by
      rw [_root_.integral_pow]
      simp only [one_pow, Nat.cast_add, Nat.cast_one]
      have hn : (n : ℝ)+1 ≠ 0 := by positivity
      field_simp [hn]
      <;> ring

/-- First, second, fourth and sixth moments used in the exact nonlinear
dyadic score calculations (T1(a),(c)): 0,1/3,1/5,1/7 respectively. -/
theorem uniform_unit_moments :
    (∫ z, z ∂ uniformUnitLaw) = 0 ∧
    (∫ z, z^2 ∂ uniformUnitLaw) = 1/3 ∧
    (∫ z, z^4 ∂ uniformUnitLaw) = 1/5 ∧
    (∫ z, z^6 ∂ uniformUnitLaw) = 1/7 := by
  have h1 := uniform_unit_moment 1
  have h2 := uniform_unit_moment 2
  have h4 := uniform_unit_moment 4
  have h6 := uniform_unit_moment 6
  norm_num at h1 h2 h4 h6
  exact ⟨h1,h2,h4,h6⟩

/-- Product monomial moments of two independently sampled uniform units
(T1(a),(c)): expectations factor and equal the explicit one-unit integrals. -/
theorem uniform_pair_monomial (a b : ℕ) :
    (∫ uv : ℝ × ℝ, uv.1^a * uv.2^b ∂ uniformUnitLaw.prod uniformUnitLaw) =
      ((1-(-1 : ℝ)^(a+1))/(2*(a+1 : ℝ))) *
        ((1-(-1 : ℝ)^(b+1))/(2*(b+1 : ℝ))) := by
  rw [integral_prod_mul (fun z : ℝ => z^a) (fun z : ℝ => z^b), uniform_unit_moment, uniform_unit_moment]


/-- Every power of a Uniform[-1,1] unit has finite second moment
(T1(a),(c)). The proof uses the actual bounded support of the normalized law. -/
theorem uniform_unit_power_L2 (n : ℕ) :
    MemLp (fun z : ℝ => z^n) 2 uniformUnitLaw := by
  apply MemLp.of_bound (by fun_prop) 1
  have hs : ∀ᵐ z ∂ uniformUnitLaw, z ∈ Set.Icc (-1 : ℝ) 1 :=
    ProbabilityTheory.ae_cond_mem measurableSet_Icc
  filter_upwards [hs] with z hz
  simp only [norm_pow, Real.norm_eq_abs]
  exact pow_le_one₀ (abs_nonneg z) (abs_le.mpr hz)

/-- Two-unit monomials are integrable under the actual iid uniform law
(T1(a),(c)); finite polynomial expectation calculations can therefore use
linearity without assuming the required moment values. -/
theorem uniform_pair_monomial_integrable (a b : ℕ) :
    Integrable (fun uv : ℝ × ℝ => uv.1^a * uv.2^b)
      (uniformUnitLaw.prod uniformUnitLaw) :=
  ((uniform_unit_power_L2 a).integrable one_le_two).mul_prod
    ((uniform_unit_power_L2 b).integrable one_le_two)

/-- Exact expectation of any finite polynomial monomial sum in two
independent uniform units (T1(a),(c), P018-E001). -/
theorem uniform_polynomial_integral {m : ℕ} (c : Fin m → ℝ) (a b : Fin m → ℕ) :
    (∫ uv : ℝ × ℝ, ∑ i, c i * (uv.1^(a i) * uv.2^(b i))
      ∂ uniformUnitLaw.prod uniformUnitLaw) =
    ∑ i, c i * (((1-(-1 : ℝ)^(a i+1))/(2*(a i+1 : ℝ))) *
      ((1-(-1 : ℝ)^(b i+1))/(2*(b i+1 : ℝ)))) := by
  rw [integral_finsetSum univ
    (fun i _ => (uniform_pair_monomial_integrable (a i) (b i)).const_mul (c i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, uniform_pair_monomial]

/-- The exact nonlinear bounded witness X=(1,2+z+z'), Y=(z+z')^2
(T1, P018-E001; does not assume conditional mean-zero residuals). -/
def nonlinearKernel : Kernel ℝ 2 :=
  ⟨uniformUnitLaw, fun z t => ![1,2+z+t], fun z t => (z+t)^2⟩

/-- The exact population Gram Q in the T1 uniform witness (P018-E001, equation (2), p. 566). -/
def nonlinearQ : Mat 2 := !![1,2;2,14/3]
/-- The same-dyad score moment H in the T1 uniform witness (P018-E001, p. 566). -/
def nonlinearH : Mat 2 := !![28/45,56/45;56/45,3448/945]
/-- The overlapping score moment Gamma in the T1 uniform witness (P018-E001, p. 566). -/
def nonlinearGamma : Mat 2 := !![4/45,8/45;8/45,632/945]
/-- The positive limiting covariance in the T1 uniform witness (P018-E001, pp. 566,573). -/
def nonlinearVstar : Mat 2 := !![3664/315,-592/105;-592/105,296/105]


/-- The nonlinear counterexample's population Gram and projection
coefficients are actual expectation calculations: Q=[[1,2],[2,14/3]],
E[XY]=(2/3,4/3), det(Q)=2/3 and beta=(2/3,0)
(T1(a), p. 566 equation (2); P018-E001). -/
theorem nonlinear_population_projection :
    populationGram nonlinearKernel = nonlinearQ ∧
    meanVec (uniformUnitLaw.prod uniformUnitLaw) (fun uv =>
      score (nonlinearKernel.X uv.1 uv.2) (nonlinearKernel.Y uv.1 uv.2)) = ![2/3,4/3] ∧
    nonlinearQ.det = 2/3 ∧ populationBeta nonlinearKernel = ![2/3,0] := by
  have q01 : (∫ uv : ℝ × ℝ, 2+uv.1+uv.2 ∂ uniformUnitLaw.prod uniformUnitLaw) = 2 := by
    have h := uniform_polynomial_integral (![2,1,1] : Fin 3 → ℝ)
      (![0,1,0] : Fin 3 → ℕ) (![0,0,1] : Fin 3 → ℕ)
    have he : (fun uv : ℝ × ℝ => ∑ i : Fin 3,
        (![2,1,1] : Fin 3 → ℝ) i *
          (uv.1^((![0,1,0] : Fin 3 → ℕ) i) * uv.2^((![0,0,1] : Fin 3 → ℕ) i))) =
        fun uv => 2+uv.1+uv.2 := by
      funext uv
      simp [Fin.sum_univ_succ]
      ring
    rw [he] at h
    norm_num [Fin.sum_univ_succ] at h
    exact h
  have q11 : (∫ uv : ℝ × ℝ, (2+uv.1+uv.2)^2 ∂ uniformUnitLaw.prod uniformUnitLaw) = 14/3 := by
    have h := uniform_polynomial_integral (![4,4,4,1,2,1] : Fin 6 → ℝ)
      (![0,1,0,2,1,0] : Fin 6 → ℕ) (![0,0,1,0,1,2] : Fin 6 → ℕ)
    have he : (fun uv : ℝ × ℝ => ∑ i : Fin 6,
        (![4,4,4,1,2,1] : Fin 6 → ℝ) i *
          (uv.1^((![0,1,0,2,1,0] : Fin 6 → ℕ) i) * uv.2^((![0,0,1,0,1,2] : Fin 6 → ℕ) i))) =
        fun uv => (2+uv.1+uv.2)^2 := by
      funext uv
      simp [Fin.sum_univ_succ]
      ring
    rw [he] at h
    norm_num [Fin.sum_univ_succ] at h
    exact h
  have xy0 : (∫ uv : ℝ × ℝ, (uv.1+uv.2)^2 ∂ uniformUnitLaw.prod uniformUnitLaw) = 2/3 := by
    have h := uniform_polynomial_integral (![1,2,1] : Fin 3 → ℝ)
      (![2,1,0] : Fin 3 → ℕ) (![0,1,2] : Fin 3 → ℕ)
    have he : (fun uv : ℝ × ℝ => ∑ i : Fin 3,
        (![1,2,1] : Fin 3 → ℝ) i *
          (uv.1^((![2,1,0] : Fin 3 → ℕ) i) * uv.2^((![0,1,2] : Fin 3 → ℕ) i))) =
        fun uv => (uv.1+uv.2)^2 := by
      funext uv
      simp [Fin.sum_univ_succ]
      ring
    rw [he] at h
    norm_num [Fin.sum_univ_succ] at h
    exact h
  have xy1 : (∫ uv : ℝ × ℝ, (uv.1+uv.2)^2*(2+uv.1+uv.2)
      ∂ uniformUnitLaw.prod uniformUnitLaw) = 4/3 := by
    have h := uniform_polynomial_integral (![2,4,2,1,3,3,1] : Fin 7 → ℝ)
      (![2,1,0,3,2,1,0] : Fin 7 → ℕ) (![0,1,2,0,1,2,3] : Fin 7 → ℕ)
    have he : (fun uv : ℝ × ℝ => ∑ i : Fin 7,
        (![2,4,2,1,3,3,1] : Fin 7 → ℝ) i *
          (uv.1^((![2,1,0,3,2,1,0] : Fin 7 → ℕ) i) * uv.2^((![0,1,2,0,1,2,3] : Fin 7 → ℕ) i))) =
        fun uv => (uv.1+uv.2)^2*(2+uv.1+uv.2) := by
      funext uv
      simp [Fin.sum_univ_succ]
      ring
    rw [he] at h
    norm_num [Fin.sum_univ_succ] at h
    exact h
  have hQ : populationGram nonlinearKernel = nonlinearQ := by
    ext a b
    fin_cases a <;> fin_cases b
    · norm_num [populationGram, meanMat, nonlinearKernel, outer, nonlinearQ]
    · simpa [populationGram, meanMat, nonlinearKernel, outer, nonlinearQ] using q01
    · simpa [populationGram, meanMat, nonlinearKernel, outer, nonlinearQ] using q01
    · simpa [populationGram, meanMat, nonlinearKernel, outer, nonlinearQ, ← pow_two] using q11
  have hxy : meanVec (uniformUnitLaw.prod uniformUnitLaw) (fun uv =>
      score (nonlinearKernel.X uv.1 uv.2) (nonlinearKernel.Y uv.1 uv.2)) = ![2/3,4/3] := by
    ext a
    fin_cases a
    · simpa [meanVec, nonlinearKernel, score] using xy0
    · simpa [meanVec, nonlinearKernel, score] using xy1
  have hi : nonlinearQ⁻¹ = (!![7,-3;-3,3/2] : Mat 2) := by
    apply Matrix.inv_eq_left_inv
    norm_num [nonlinearQ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]
  refine ⟨hQ,hxy,?_,?_⟩
  · norm_num [nonlinearQ, Matrix.det_fin_two]
  · simp only [populationBeta, hQ, hi]
    change (!![7,-3;-3,3/2] : Mat 2).mulVec
      (meanVec (uniformUnitLaw.prod uniformUnitLaw) (fun uv =>
        score (nonlinearKernel.X uv.1 uv.2) (nonlinearKernel.Y uv.1 uv.2))) = ![2/3,0]
    rw [hxy]
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      funext_iff, Fin.forall_fin_succ]


/-- The iid nonlinear counterexample satisfies the bounded data, symmetric
kernel, intercept and nonsingular population design assumptions of p. 566
(T1(a)). Sample rank and the variance/CLT assertions remain separate. -/
theorem nonlinear_model_assumptions : Standing nonlinearKernel := by
  refine ⟨(by change IsProbabilityMeasure uniformUnitLaw; infer_instance), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold nonlinearKernel
    fun_prop
  · unfold nonlinearKernel
    fun_prop
  · intro z t
    dsimp [nonlinearKernel]
    constructor
    · ext a
      fin_cases a <;> simp <;> ring
    · ring
  · refine ⟨4, by norm_num, ?_⟩
    have hs : ∀ᵐ z ∂ uniformUnitLaw, z ∈ Set.Icc (-1 : ℝ) 1 :=
      ProbabilityTheory.ae_cond_mem measurableSet_Icc
    have hfst : ∀ᵐ uv ∂ uniformUnitLaw.prod uniformUnitLaw,
        uv.1 ∈ Set.Icc (-1 : ℝ) 1 :=
      (measurePreserving_fst (μ := uniformUnitLaw) (ν := uniformUnitLaw)).quasiMeasurePreserving.tendsto_ae hs
    have hsnd : ∀ᵐ uv ∂ uniformUnitLaw.prod uniformUnitLaw,
        uv.2 ∈ Set.Icc (-1 : ℝ) 1 :=
      (measurePreserving_snd (μ := uniformUnitLaw) (ν := uniformUnitLaw)).quasiMeasurePreserving.tendsto_ae hs
    filter_upwards [hfst,hsnd] with uv hz ht
    change ‖(![1,2+uv.1+uv.2] : Vec 2)‖ ≤ 4 ∧ |(uv.1+uv.2)^2| ≤ 4
    have hz' : -1 ≤ uv.1 ∧ uv.1 ≤ 1 := hz
    have ht' : -1 ≤ uv.2 ∧ uv.2 ≤ 1 := ht
    have hlo : 0 ≤ 2+uv.1+uv.2 := by linarith
    have hhi : 2+uv.1+uv.2 ≤ 4 := by linarith
    constructor
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)).mpr
      intro a
      fin_cases a
      · norm_num
      · simpa [Real.norm_eq_abs, abs_of_nonneg hlo] using hhi
    · rw [abs_of_nonneg (sq_nonneg _)]
      have h1 : -2 ≤ uv.1+uv.2 := by linarith
      have h2 : uv.1+uv.2 ≤ 2 := by linarith
      nlinarith
  · exact ⟨0, by intros; rfl⟩
  · rw [nonlinear_population_projection.1]
    norm_num [nonlinearQ, Matrix.det_fin_two]


/-- Exact rational matrix checks in the uniform witness (T1(a),(c),(d)).
These identities do not identify the constants with probability moments. -/
theorem nonlinear_matrix_certificate :
    nonlinearQ.det = 2/3 ∧ nonlinearGamma.det = 1184/42525 ∧
    (nonlinearGamma 0 0 : ℝ) > 0 ∧ nonlinearVstar.det = 4736/4725 ∧
    (nonlinearVstar 0 0 : ℝ) > 0 ∧
    (3 : ℝ) • nonlinearH + (6 : ℝ) • nonlinearGamma = !![12/5,24/5;24/5,4712/315] := by
  norm_num [nonlinearQ, nonlinearGamma, nonlinearH, nonlinearVstar, Matrix.det_fin_two,
    funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]

/-- Fair-sign unit law and its intercept-only data (T3, T9, T11).
The finite iid sample is exactly a product of uniform two-point laws. -/
def fairLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

/-- The values +1,-1 of each fair iid unit in the T3 witness (P018-E006, pp. 573--574). -/
def signValue (b : Bool) : ℝ := if b then 1 else -1

/-- The intercept-only model X_ij=1, Y_ij=U_i+U_j in T3/T9/T11. -/
def signKernel : Kernel Bool 1 :=
  ⟨fairLaw, fun _ _ => ![1], fun b c => signValue b + signValue c⟩


/-- The deterministic counterexample to Appendix B's printed Chebyshev
sufficiency claim: Vhat_N=V=1 gives unscaled mean error zero and scaled
variance zero but N Vhat_N-V=N-1, failing both deterministic and
in-probability convergence (T3(e)). -/
theorem missing_N_counterexample :
    (∀ N : ℕ, (∫ _ : Unit, (1 : ℝ)-1 ∂ Measure.dirac ()) = 0 ∧
      ProbabilityTheory.variance (fun _ : Unit => (N : ℝ)*1) (Measure.dirac ()) = 0) ∧
    ¬Tendsto (fun N : ℕ => (N : ℝ)*1-1) atTop (𝓝 0) ∧
    ¬inProbability (fun _ : ℕ => Measure.dirac ())
      (fun (N : ℕ) (_ : Unit) => (N : ℝ)*1-1) := by
  refine ⟨?_,?_,?_⟩
  · intro N
    simp [ProbabilityTheory.variance, ProbabilityTheory.evariance]
  · intro h
    have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      simpa using h.add_const 1
    exact not_tendsto_nhds_of_tendsto_atTop (tendsto_natCast_atTop_atTop (R := ℝ)) 1 hcast
  · intro h
    have hzero := h (1/2) (by norm_num)
    have hone : Tendsto (fun N : ℕ =>
        ((Measure.dirac ()) {ω : Unit | (1/2 : ℝ) ≤ ‖(N : ℝ)*1-1‖}).toReal)
        atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have he : {ω : Unit | (1/2 : ℝ) ≤ ‖(N : ℝ)*1-1‖} = Set.univ := by
        ext ω
        simp only [Set.mem_setOf_eq,Set.mem_univ,iff_true]
        rw [mul_one,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
        linarith
      rw [he]
      simp
    have hn : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
    norm_num at hn


/-- Finite fair-sign expectation, an explicit 2^N-point probability sum.
At each recursion the new unit is +1 or -1 with probability 1/2 (T3,T7,T11). -/
def fairAverage : (N : ℕ) → ((Fin N → ℝ) → ℝ) → ℝ
  | 0, f => f (Fin.elim0)
  | N+1, f => (fairAverage N (fun u => f (Matrix.vecCons 1 u)) +
      fairAverage N (fun u => f (Matrix.vecCons (-1) u))) / 2

/-- Actual N=4 fitted residual e_ij=U_i+U_j-(1/2)sum_i U_i (T3(a)). -/
def signResidual4 (u : Fin 4 → ℝ) (d : Fin 6) : ℝ :=
  (∑ i ∈ sixMembers d, u i) - (∑ i, u i)/2

/-- The exact N=4 mean meat is 6 versus true Sigma=36, and
E[Vhat-4]=-23/6 (T3(c),(d)). This finite probability certificate directly
uses the 16 equiprobable iid sign outcomes, rather than postulated moments. -/
theorem sign_mean_counterexample :
    fairAverage 4 (fun u => (∑ i, u i)^2) = 4 ∧
    fairAverage 4 (fun u => (meat sixMembers (fun d => ![signResidual4 u d])) 0 0) = 6 ∧
    fairAverage 4 (fun u => (meat sixMembers (fun d => ![signResidual4 u d])) 0 0 / 36 - 4) = -23/6 ∧
    fairAverage 4 (fun u => (3 * ∑ i, u i)^2) = 36 := by
  norm_num [fairAverage, signResidual4, meat, outer, Matrix.of_apply, sixMembers, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_succ']

/-- Weighted counterexample's deterministic weights 2^(-i-j), with paper
indices 1,...,N represented by Fin N indices plus one (T9). -/
def concentratedWeight {N : ℕ} (d : Dyad N) : ℝ :=
  (2 : ℝ) ^ (-((firstUnit d).val + (secondUnit d).val + 2 : ℤ))

/-- Weighted Gram, population projection and residuals (Appendix D, p. 575;
weighted beta is the population projection and is undefined in the printed paper). -/
def weightedGram {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k)
    (w : Dyad N → ℝ) (ω : Fin N → U) : Mat k :=
  ∑ d, w d • outer (design K ω d) (design K ω d)
/-- "beta_hat_w = (X' W X)^(-1) X' W Y" (Appendix D, p. 575). -/
def weightedOLS {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k)
    (w : Dyad N → ℝ) (ω : Fin N → U) : Vec k :=
  (weightedGram K w ω)⁻¹.mulVec (∑ d, score (design K ω d) (w d * response K ω d))
/-- Corrected H_w=D^(-1) sum_d E[w_d X_d X_d'] (T12, P018-E004). -/
def weightedPopulationGram {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) : Mat k :=
  (Dreal N)⁻¹ • meanMat (unitSampleLaw K N) (weightedGram K w)
/-- Population weighted projection beta_w (T12; beta_w is undefined in the printed Appendix D). -/
def weightedPopulationBeta {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) : Vec k :=
  (meanMat (unitSampleLaw K N) (weightedGram K w))⁻¹.mulVec
    (meanVec (unitSampleLaw K N) (fun ω => ∑ d, score (design K ω d) (w d * response K ω d)))
/-- S_w=sum_d w_d X_d epsilon_d (corrected T12, P018-E004). -/
def weightedScoreSum {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) (ω : Fin N → U) : Vec k :=
  ∑ d, score (design K ω d) (w d * (response K ω d - dot (design K ω d) (weightedPopulationBeta K w)))
/-- "variance estimator" of equation (7), with weights in both score factors (pp. 575--576). -/
def weightedVariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) (ω : Fin N → U) : Mat k :=
  sandwich (weightedGram K w ω)⁻¹ (meat members (fun d =>
    score (design K ω d) (w d * (response K ω d - dot (design K ω d) (weightedOLS K w ω)))))
/-- Corrected V_w=(N/D^2) H_w^(-1) Omega_w H_w^(-1) (T12, P018-E004). -/
def weightedTarget {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) : Mat k :=
  ((N : ℝ)/(Dreal N)^2) • sandwich (weightedPopulationGram K w)⁻¹
    (varMat (unitSampleLaw K N) (weightedScoreSum K w))


/-- Restoring the dyad sum changes the scalar printed target 4/D to the
true target 4 (T11(b),(d), pp. 568,576). -/
theorem scalar_target_counterexample (N : ℕ) (hN : 3 ≤ N) :
    (N : ℝ)*(2*(N : ℝ)-2)/(Dreal N)^2 = 4 / Dreal N ∧
    (N : ℝ)*((N : ℝ)*((N : ℝ)-1)^2)/(Dreal N)^2 = 4 ∧
    (N : ℝ)*(2*(N : ℝ)-2)/(Dreal N)^2 ≠ 4 := by
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
  have hD : 3 ≤ Dreal N := by
    unfold Dreal
    nlinarith [sq_nonneg ((N : ℝ)-3)]
  have hp : (N : ℝ)*(2*(N : ℝ)-2)/(Dreal N)^2 = 4 / Dreal N := by
    unfold Dreal
    field_simp [hn0,hn1] <;> ring
  refine ⟨hp,?_,?_⟩
  · unfold Dreal
    field_simp [hn0,hn1] <;> ring
  · rw [hp]
    apply ne_of_lt
    apply (div_lt_iff₀ (by linarith : 0 < Dreal N)).mpr
    linarith


/-- Repeated observations "t=1,...,T(d), fixed and finite" and blocks
X_d, Y_d (p. 567). Kernels may vary by deterministic block and record; they
remain functions only of the two member units. -/
structure RepeatedKernel (U : Type*) [MeasurableSpace U] (k : ℕ) where
  μ : Measure U
  T : (N : ℕ) → Dyad N → ℕ
  X : (N : ℕ) → (d : Dyad N) → Fin (T N d) → U → U → Vec k
  Y : (N : ℕ) → (d : Dyad N) → Fin (T N d) → U → U → ℝ

/-- "random (i.i.d.) sample of units" (p. 566), for repeated dyad blocks (p. 567). -/
def repeatedLaw {U : Type*} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) (N : ℕ) :
    Measure (Fin N → U) := Measure.pi (fun _ => R.μ)
/-- L=sum_d T(d), the total observation count (corrected T12, P018-E004). -/
def repeatedL {U : Type*} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) (N : ℕ) : ℝ :=
  ∑ d : Dyad N, (R.T N d : ℝ)
/-- "X_dt" record regressor (p. 567), evaluated on the dyad's sampled units. -/
def repeatedX {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (ω : Fin N → U) (d : Dyad N) (t : Fin (R.T N d)) : Vec k :=
  R.X N d t (ω (firstUnit d)) (ω (secondUnit d))
/-- "Y_dt" record response (p. 567), evaluated on the dyad's sampled units. -/
def repeatedY {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (ω : Fin N → U) (d : Dyad N) (t : Fin (R.T N d)) : ℝ :=
  R.Y N d t (ω (firstUnit d)) (ω (secondUnit d))
/-- Stacked sample X'X=sum_d sum_t X_dt X_dt' (pp. 567--568). -/
def repeatedGram {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k) (ω : Fin N → U) : Mat k :=
  ∑ d : Dyad N, ∑ t, outer (repeatedX R ω d t) (repeatedX R ω d t)
/-- Corrected H_r=L^(-1) sum_d E[X_d'X_d] (T12, P018-E004). -/
def repeatedH {U : Type*} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) (N : ℕ) : Mat k :=
  (repeatedL R N)⁻¹ • meanMat (repeatedLaw R N) (repeatedGram R)
/-- Population projection beta_r on the stacked repeated data (p. 567). -/
def repeatedBeta {U : Type*} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) (N : ℕ) : Vec k :=
  (meanMat (repeatedLaw R N) (repeatedGram R))⁻¹.mulVec
    (meanVec (repeatedLaw R N) (fun ω => ∑ d : Dyad N, ∑ t, score (repeatedX R ω d t) (repeatedY R ω d t)))
/-- "OLS estimator ... applied to the repeated dyads data" (p. 567). -/
def repeatedOLS {U : Type*} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k) (ω : Fin N → U) : Vec k :=
  (repeatedGram R ω)⁻¹.mulVec (∑ d : Dyad N, ∑ t, score (repeatedX R ω d t) (repeatedY R ω d t))
/-- X_d' epsilon_d=sum_t X_dt epsilon_dt, with a supplied coefficient (pp. 567--568; T12). -/
def repeatedBlockScore {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (β : Vec k) (ω : Fin N → U) (d : Dyad N) : Vec k :=
  ∑ t, score (repeatedX R ω d t) (repeatedY R ω d t - dot (repeatedX R ω d t) β)
/-- "variance estimator" Vhat_r in Corollary 1 (pp. 567--568). -/
def repeatedVariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (ω : Fin N → U) : Mat k :=
  sandwich (repeatedGram R ω)⁻¹ (meat members (repeatedBlockScore R (repeatedOLS R ω) ω))
/-- Corrected V_r=(N/L^2) H_r^(-1) Omega_r H_r^(-1) (T12, P018-E004). -/
def repeatedTarget {U : Type*} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) (N : ℕ) : Mat k :=
  ((N : ℝ)/(repeatedL R N)^2) • sandwich (repeatedH R N)⁻¹
    (varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N, repeatedBlockScore R (repeatedBeta R N) ω d))

/-- "same conditions" for bounded repeated data (pp. 567--568), with the
intercept and positive record counts. Record kernels may depend on the
deterministic block, N and record, and may be directed. No common symmetric
time kernel or full rank at every small sample size is imposed. Population
rank is supplied locally, or by the positive limiting normalized design. -/
def RepeatedStanding {U : Type*} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) : Prop :=
  IsProbabilityMeasure R.μ ∧
  (∀ N : ℕ, 2 ≤ N → ∀ d : Dyad N, 0 < R.T N d) ∧
  (∀ N d t, Measurable (fun uv : U × U => R.X N d t uv.1 uv.2) ∧
    Measurable (fun uv : U × U => R.Y N d t uv.1 uv.2)) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ N d t, ∀ᵐ uv ∂ R.μ.prod R.μ,
    ‖R.X N d t uv.1 uv.2‖ ≤ C ∧ |R.Y N d t uv.1 uv.2| ≤ C) ∧
  (∃ j : Fin k, ∀ N d t u v, R.X N d t u v j = 1)

/-- Bounded measurable dyad records under iid unit sampling at one fixed N
(T12, pp. 567--568,575--576). Only this size is constrained. Directed and
block-specific records are allowed. Rank is a separate local hypothesis. -/
def RepeatedAtSize {U : Type*} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (N : ℕ) : Prop :=
  IsProbabilityMeasure R.μ ∧
  (∀ d : Dyad N, 0 < R.T N d) ∧
  (∀ d t, Measurable (fun uv : U × U => R.X N d t uv.1 uv.2) ∧
    Measurable (fun uv : U × U => R.Y N d t uv.1 uv.2)) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ d t, ∀ᵐ uv ∂ R.μ.prod R.μ,
    ‖R.X N d t uv.1 uv.2‖ ≤ C ∧ |R.Y N d t uv.1 uv.2| ≤ C)

/-- "X' W X" for weighted directed observations (Appendix D, p. 575).
The two directions may be distinct records of one unordered unit pair,
as explicitly described on p. 567; weights are fixed per record. -/
def recordWeightedGram {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (ω : Fin N → U) : Mat k :=
  ∑ d : Dyad N, ∑ t, w d t • outer (repeatedX R ω d t) (repeatedX R ω d t)

/-- "X' W Y" (Appendix D, p. 575), as a sum over weighted records. -/
def recordWeightedXY {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (ω : Fin N → U) : Vec k :=
  ∑ d : Dyad N, ∑ t, score (repeatedX R ω d t) (w d t * repeatedY R ω d t)

/-- "beta_hat_w=(X'WX)^(-1)X'WY" (Appendix D, p. 575), allowing directed records. -/
def recordWeightedOLS {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (ω : Fin N → U) : Vec k :=
  (recordWeightedGram R w ω)⁻¹.mulVec (recordWeightedXY R w ω)

/-- Population weighted projection beta_w
(T12; the paper leaves beta_w undefined). Uses the expected weighted Gram. -/
def recordWeightedBeta {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ) : Vec k :=
  (meanMat (repeatedLaw R N) (recordWeightedGram R w))⁻¹.mulVec
    (meanVec (repeatedLaw R N) (recordWeightedXY R w))

/-- Weighted block score sum_t w_dt X_dt epsilon_dt (Appendix D, eq. (7),
pp. 575--576), grouping directed records on their common two-unit dyad. -/
def recordWeightedBlockScore {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (β : Vec k) (ω : Fin N → U) (d : Dyad N) : Vec k :=
  ∑ t, score (repeatedX R ω d t)
    (w d t * (repeatedY R ω d t - dot (repeatedX R ω d t) β))

/-- H_w=D^(-1) sum E[w_dt X_dt X_dt'] (T12, corrected p. 576).
D=binom(N,2) counts the unordered unit pairs; all directed
records enter the numerator. The chosen common normalization cancels in V_w. -/
def recordWeightedH {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ) : Mat k :=
  (Dreal N)⁻¹ • meanMat (repeatedLaw R N) (recordWeightedGram R w)

/-- The equation (7) sandwich estimator, with all record pairs sharing
an endpoint included, also within the same unordered dyad (pp. 575--576). -/
def recordWeightedVariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (ω : Fin N → U) : Mat k :=
  sandwich (recordWeightedGram R w ω)⁻¹
    (meat members (recordWeightedBlockScore R w (recordWeightedOLS R w ω) ω))

/-- V_w=(N/D^2)H_w^(-1)Var(sum w_dt X_dt epsilon_dt)H_w^(-1)
(T12, corrected display p. 576). D=binom(N,2) is the same normalization used by recordWeightedH;
all directed records enter the total score. A common normalization cancels. -/
def recordWeightedTarget {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ) : Mat k :=
  ((N : ℝ)/(Dreal N)^2) • sandwich (recordWeightedH R w)⁻¹
    (varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N,
      recordWeightedBlockScore R w (recordWeightedBeta R w) ω d))


/-- Moment convergence with uniformly integrable squared coefficient errors,
explicitly for changing finite iid-unit sampling spaces (T20(iii)). UI is
expressed by its uniform tail criterion, which includes finite second moments. -/
def uiSquares {Ω : ℕ → Type*} [∀ N : ℕ, MeasurableSpace (Ω N)] {k : ℕ}
    (μ : ∀ N : ℕ, Measure (Ω N)) (ξ : ∀ N : ℕ, Ω N → Vec k) : Prop :=
  (∀ N a, MemLp (fun ω => ξ N ω a) 2 (μ N)) ∧
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    (∫ ω, (if C < ∑ a, (ξ N ω a)^2 then ∑ a, (ξ N ω a)^2 else 0) ∂ μ N) < ε


/-- Block/weighted sandwich scale algebra (T10(C3)): normal equations have
bread a^(-1)P and meat a^2 M after a common positive weight rescaling. -/
theorem sandwich_scale_invariance {k : ℕ} (a : ℝ) (ha : a ≠ 0) (P M : Mat k) :
    sandwich (a⁻¹ • P) ((a^2) • M) = sandwich P M := by
  simp only [sandwich, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h : a⁻¹ * (a^2 * a⁻¹) = 1 := by field_simp
  rw [h, one_smul]


/-- The logistic Hessian/bread is symmetric (Appendix E, T14(ii), T23(iii)). -/
theorem logistic_bread_symmetric {E : Type*} [Fintype E] {k : ℕ}
    (X : E → Vec k) (β : Vec k) : (logisticBread X β).transpose = logisticBread X β := by
  ext a b
  simp only [logisticBread, Matrix.transpose_apply, Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, outer, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Symmetry survives multiplication by the same symmetric bread on both
sides (equations (3),(7), Appendix E). -/
theorem sandwich_symmetric {k : ℕ} (P M : Mat k)
    (hP : P.transpose = P) (hM : M.transpose = M) :
    (sandwich P M).transpose = sandwich P M := by
  simp [sandwich, Matrix.transpose_mul, hP, hM, Matrix.mul_assoc]

/-- The literal printed logistic meat factors into the single-dyad outer
product times r_d times its overlapping residual sum (T14(iii), p. 576). -/
theorem printed_logistic_factorization {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (X : E → Vec k) (r : E → ℝ) :
    printedLogisticMeat s X r = ∑ d, (r d * ∑ f, if (s d ∩ s f).Nonempty then r f else 0) • outer (X d) (X d) := by
  classical
  ext a b
  simp only [printedLogisticMeat, Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro f hf
  split_ifs <;> simp [mul_assoc]

/-- Corrected Appendix E estimator for any real parameter and data (T14,
p. 576): the cross factor is the product of the two scores, the meat has the
unit-incidence decomposition, and the full covariance estimator is symmetric. -/
theorem logistic_correction {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (s : E → Finset V)
    (hs : ∀ d, (s d).card = 2) (hi : Function.Injective s)
    {k : ℕ} (X : E → Vec k) (Y : E → ℝ) (β : Vec k)
    (hY : ∀ d, Y d = 0 ∨ Y d = 1) (hH : (logisticBread X β).det ≠ 0) :
    let r := fun d => Y d - expit (dot (X d) β)
    let q := fun d => logisticScore (X d) (Y d) β
    (∀ d f, outer (q d) (q f) = (r d * r f) • outer (X d) (X f)) ∧
    meat s q = (∑ i, outer (unitScore s q i) (unitScore s q i)) - dyadMeat q ∧
    (logisticVariance s X Y β).transpose = logisticVariance s X Y β ∧
    printedLogisticMeat s X r = ∑ d, (r d * ∑ f, if (s d ∩ s f).Nonempty then r f else 0) • outer (X d) (X d) := by
  dsimp only
  refine ⟨?_, overlap_meat_identity s hs hi _, ?_, printed_logistic_factorization s X _⟩
  · intro d f
    exact score_product _ _ _ _
  · apply sandwich_symmetric
    · rw [Matrix.transpose_nonsing_inv, logistic_bread_symmetric]
    · exact meat_symmetric s _

/-- Bernoulli log likelihood per observation (Appendix E, T23(ii), p. 576). -/
def logLikelihood {k : ℕ} (x : Vec k) (y : ℝ) (β : Vec k) : ℝ :=
  y * dot x β - Real.log (1 + Real.exp (dot x β))


/-- Supporting-line bound for a logistic observation at zero; equality is
possible only when its predictor is zero (used for T13's exact fitted MLE). -/
theorem logistic_tangent_bound (t : ℝ) :
    Real.log 2 + t/2 ≤ Real.log (1+Real.exp t) ∧
    (t ≠ 0 → Real.log 2 + t/2 < Real.log (1+Real.exp t)) := by
  have he1 := Real.add_one_le_exp (t/2)
  have he2 := Real.add_one_le_exp (-(t/2))
  have htwo : 2 ≤ Real.exp (t/2)+Real.exp (-(t/2)) := by linarith
  have hp : 0 < Real.exp (t/2)+Real.exp (-(t/2)) := by positivity
  have hid : 1+Real.exp t = Real.exp (t/2)*(Real.exp (t/2)+Real.exp (-(t/2))) := by
    rw [mul_add, ← Real.exp_add, ← Real.exp_add]
    have h1 : t/2+t/2=t := by ring
    have h2 : t/2+-(t/2)=0 := by ring
    rw [h1,h2,Real.exp_zero]
    ring
  have hlog : Real.log (1+Real.exp t) = t/2 + Real.log (Real.exp (t/2)+Real.exp (-(t/2))) := by
    rw [hid, Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hp), Real.log_exp]
  rw [hlog]
  constructor
  · have h := Real.log_le_log (by norm_num : (0 : ℝ)<2) htwo
    linarith
  · intro ht
    have hne : t/2 ≠ 0 := by intro h; apply ht; linarith
    have he := Real.add_one_lt_exp hne
    have hs : 2 < Real.exp (t/2)+Real.exp (-(t/2)) := by linarith
    have h := Real.log_lt_log (by norm_num : (0 : ℝ)<2) hs
    linarith

/-- Logistic likelihood is bounded by its supporting line at zero, strictly
when the predictor is nonzero (T13(a), Appendix E p. 576). -/
theorem logLikelihood_tangent {k : ℕ} (x : Vec k) (y : ℝ) (β : Vec k) :
    logLikelihood x y β ≤ -Real.log 2+(y-1/2)*dot x β ∧
    (dot x β ≠ 0 → logLikelihood x y β < -Real.log 2+(y-1/2)*dot x β) := by
  have h := logistic_tangent_bound (dot x β)
  dsimp [logLikelihood]
  constructor
  · nlinarith [h.1]
  · intro ht
    nlinarith [h.2 ht]

/-- The logistic witness's exact finite fit is uniquely zero (T13(a)); the
algebraic covariance mismatch is proved separately by its numeric certificate. -/
theorem logistic_witness_is_MLE :
    (∀ β : Vec 2, (∑ d, logLikelihood (logitX d) (logitY d) β) ≤
      ∑ d, logLikelihood (logitX d) (logitY d) 0) ∧
    (∀ β : Vec 2, (∑ d, logLikelihood (logitX d) (logitY d) β) =
      (∑ d, logLikelihood (logitX d) (logitY d) 0) → β = 0) ∧
    (∀ d, logisticScore (logitX d) (logitY d) 0 = score (logitX d) (logitR d)) := by
  have hz (β : Vec 2) : (∑ d, (logitY d-1/2)*dot (logitX d) β) = 0 := by
    simp [logitY,logitX,dot,Fin.sum_univ_succ]
    ring
  have hzero : (∑ d, logLikelihood (logitX d) (logitY d) 0) =
      ∑ _ : Fin 6, -Real.log 2 := by
    norm_num [logLikelihood,dot]
  have hsum (β : Vec 2) :
      (∑ d : Fin 6, (-Real.log 2+(logitY d-1/2)*dot (logitX d) β)) =
        ∑ d, logLikelihood (logitX d) (logitY d) 0 := by
    rw [Finset.sum_add_distrib,hz,add_zero,hzero]
  have hindex (β : Vec 2) (hne : β ≠ 0) : ∃ d : Fin 6, dot (logitX d) β ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 := hc 0
    have h1 := hc 1
    simp [logitX,dot,Fin.sum_univ_succ] at h0 h1
    apply hne
    ext a
    fin_cases a
    · change β 0 = 0
      exact h0
    · change β 1 = 0
      linarith
  refine ⟨?_, ?_, ?_⟩
  · intro β
    rw [← hsum β]
    exact Finset.sum_le_sum (fun d _ => (logLikelihood_tangent (logitX d) (logitY d) β).1)
  · intro β heq
    by_contra hne
    obtain ⟨d,hd⟩ := hindex β hne
    have hlt : (∑ d, logLikelihood (logitX d) (logitY d) β) <
        ∑ d : Fin 6, (-Real.log 2+(logitY d-1/2)*dot (logitX d) β) := by
      apply Finset.sum_lt_sum
      · intro f hf
        exact (logLikelihood_tangent (logitX f) (logitY f) β).1
      · exact ⟨d,mem_univ d,(logLikelihood_tangent (logitX d) (logitY d) β).2 hd⟩
    rw [hsum,heq] at hlt
    exact (lt_irrefl _ hlt)
  · intro d
    fin_cases d <;> norm_num [logisticScore,logitY,logitR,expit,dot,Fin.sum_univ_succ]


/-- Corrected generic score second moment B=E[psi(D;theta)psi(D;theta)']
(Appendix E, p. 576). Both factors use the same data argument. -/
def genericScoreMeat {Ω Θ : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (ψ : Ω → Θ → Vec k) (θ : Θ) : Mat k :=
  meanMat μ (fun data => outer (ψ data θ) (ψ data θ))

/-- Coordinate negative Jacobian of the logistic score (Appendix E, T23).
Each coordinate derivative varies the matching component of beta. -/
def logisticNegativeJacobian {k : ℕ} (x : Vec k) (y : ℝ) (β : Vec k) : Mat k :=
  fun a b => -deriv (fun t => logisticScore x y (Function.update β b t) a) (β b)


/-- First- and second-role incidence of ordered endpoints of each unordered
dyad (T5--T6, p. 569). First means the smaller unit index. -/
def endpointZ1 (N : ℕ) : Matrix (Dyad N) (Fin N) ℝ :=
  fun d i => if firstUnit d = i then 1 else 0
/-- Second-role incidence Z_2 of each unordered dyad (T5/T6, P018-E008, pp. 569--570). -/
def endpointZ2 (N : ℕ) : Matrix (Dyad N) (Fin N) ℝ :=
  fun d i => if secondUnit d = i then 1 else 0

/-- C=tau ZZ'+sigma I, the shared-unit covariance model (T5/T6, equation (4), p. 569). -/
def sharedCov (N : ℕ) (τ σ : ℝ) : Matrix (Dyad N) (Dyad N) ℝ :=
  τ • ((endpointZ1 N + endpointZ2 N) * (endpointZ1 N + endpointZ2 N).transpose) + σ • 1

/-- t1 Z_1 Z_1'+t2 Z_2 Z_2'+sigma I, the fitted comparison's covariance family (T5/T6, P018-E008). -/
def twoRoleCov (N : ℕ) (t1 t2 σ : ℝ) : Matrix (Dyad N) (Dyad N) ℝ :=
  t1 • (endpointZ1 N * (endpointZ1 N).transpose) +
    t2 • (endpointZ2 N * (endpointZ2 N).transpose) + σ • 1


/-- The explicit 28 dyads for the T7 N=8 sign witness. -/
def eightMembers : Fin 28 → Finset (Fin 8) :=
  ![{0,1},{0,2},{0,3},{0,4},{0,5},{0,6},{0,7},
    {1,2},{1,3},{1,4},{1,5},{1,6},{1,7},
    {2,3},{2,4},{2,5},{2,6},{2,7},
    {3,4},{3,5},{3,6},{3,7},{4,5},{4,6},{4,7},{5,6},{5,7},{6,7}]

/-- Unit Z signs in the explicit T7 N=8 degenerate-inference witness (P018-E002). -/
def degeneracyZ : Fin 8 → ℝ := ![1,1,-1,-1,1,1,-1,-1]
/-- Unit W signs in the explicit T7 N=8 degenerate-inference witness (P018-E002). -/
def degeneracyW : Fin 8 → ℝ := ![1,-1,1,-1,1,-1,1,-1]
/-- X_ij=(1,1+Z_i Z_j) in the explicit T7 witness (P018-E002). -/
def degeneracyX : Fin 28 → Vec 2 := fun d => ![1, 1+∏ i ∈ eightMembers d, degeneracyZ i]
/-- Y_ij=W_i+W_j in the explicit T7 witness (P018-E002). -/
def degeneracyY : Fin 28 → ℝ := fun d => ∑ i ∈ eightMembers d, degeneracyW i

/-- The iid two-sign unit model in T7 (P018-E002, inference claims on pp. 565,567,571). -/
def signPairKernel : Kernel (Bool × Bool) 2 :=
  ⟨fairLaw.prod fairLaw, fun u v => ![1,1+signValue u.1*signValue v.1],
    fun u v => signValue u.2+signValue v.2⟩


/-- Exact N=8 sample with a negative slope-variance estimate in the two-sign iid model (T7(c)).
Its rank and OLS fit are explicitly checked, not assumed. -/
theorem degenerate_numeric_certificate :
    sampleGram degeneracyX = !![28,24;24,48] ∧
    (sampleGram degeneracyX).det = 768 ∧ sampleOLS degeneracyX degeneracyY = 0 ∧
    sampleVariance eightMembers degeneracyX degeneracyY = !![3/8,-1/48;-1/48,-13/288] ∧
    (sampleVariance eightMembers degeneracyX degeneracyY) 1 1 < 0 := by
  have hs : ∀ d : Fin 28, (eightMembers d).card = 2 := by decide
  have hi : Function.Injective eightMembers := by decide
  have hg : sampleGram degeneracyX = !![28,24;24,48] := by
    norm_num [sampleGram,outer, Matrix.of_apply,degeneracyX,degeneracyZ,eightMembers,
      Fin.sum_univ_succ,funext_iff, ← Matrix.ext_iff,Fin.forall_fin_succ]
  have hgInv : (sampleGram degeneracyX)⁻¹ = (1/768 : ℝ) • !![48,-24;-24,28] := by
    apply Matrix.inv_eq_left_inv
    rw [hg]
    norm_num [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, dotProduct,Fin.sum_univ_succ,Matrix.one_apply,
      funext_iff, ← Matrix.ext_iff,Fin.forall_fin_succ]
  have hb : sampleOLS degeneracyX degeneracyY = 0 := by
    have hz : (∑ d, score (degeneracyX d) (degeneracyY d)) = 0 := by
      norm_num [score,degeneracyX,degeneracyY,degeneracyZ,degeneracyW,
        eightMembers,Fin.sum_univ_succ,funext_iff,Fin.forall_fin_succ]
    simp [sampleOLS,hz]
  have he : ∀ d, fittedResidual degeneracyX degeneracyY d = degeneracyY d := by
    intro d
    simp [fittedResidual,hb,dot]
  have hv : sampleVariance eightMembers degeneracyX degeneracyY = !![3/8,-1/48;-1/48,-13/288] := by
    simp only [sampleVariance,hgInv,he]
    rw [overlap_meat_identity eightMembers hs hi]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sandwich,outer, Matrix.of_apply,unitScore,dyadMeat,score,degeneracyX,degeneracyY,
      degeneracyZ,degeneracyW,eightMembers,Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, dotProduct,Fin.sum_univ_succ,
      funext_iff, ← Matrix.ext_iff,Fin.forall_fin_succ]
  refine ⟨hg, ?_,hb,hv,?_⟩
  · rw [hg]; norm_num [Matrix.det_fin_two]
  · rw [hv]; norm_num


/-- Conditional heterogeneity population producing the full-rank T17 sample
with positive leading covariance (T17(d), P018-N003). -/
def finiteUnitLaw : Measure (Fin 4 × Bool) :=
  (PMF.uniformOfFintype (Fin 4 × Bool)).toMeasure

/-- The conditional heterogeneity H(T_i,T_j) of T17(d) (P018-N003, p. 567). -/
def heterogeneityTable : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,1,-1,0;1,0,0,-1;-1,0,0,1;0,-1,1,0]

/-- The bounded iid-unit population containing the T17 negative sample (P018-N003, p. 567). -/
def finiteNegativeKernel : Kernel (Fin 4 × Bool) 2 :=
  ⟨finiteUnitLaw,
    fun u v => ![1, |(u.1.val : ℝ)-(v.1.val : ℝ)|],
    fun u v => |(u.1.val : ℝ)-(v.1.val : ℝ)| + heterogeneityTable u.1 v.1 + signValue u.2 + signValue v.2⟩


/-- Corrected notation for term B equals the sparse conditional double sum
term by term (T21(ii), equation (2) p. 566 and equation (6) p. 573).
This equality does not assert that the printed conditional expression is
Var(S); that is the separate, false printed claim T26. -/
theorem expectation_placement_correction {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) :
    (∑ d : Dyad N, (conditionalTerm K d d + ∑ f ∈ neighbors d, conditionalTerm K d f)) =
      printedSigma K N := by
  classical
  unfold printedSigma
  apply Finset.sum_congr rfl
  intro d hd
  have hself : overlap d d := by
    simp only [overlap,inter_self]
    exact Finset.card_pos.mp (by rw [members_card]; omega)
  have he (f : Dyad N) : (if overlap d f then conditionalTerm K d f else 0) =
      (if f=d then conditionalTerm K d d else 0) +
      (if f ≠ d ∧ overlap d f then conditionalTerm K d f else 0) := by
    by_cases hfd : f=d
    · subst f; simp [hself]
    · by_cases hov : overlap d f <;> simp [hfd,hov]
  rw [show (∑ f : Dyad N, if overlap d f then conditionalTerm K d f else 0) =
      ∑ f : Dyad N, ((if f=d then conditionalTerm K d d else 0) +
        (if f ≠ d ∧ overlap d f then conditionalTerm K d f else 0)) from
        Finset.sum_congr rfl (fun f _ => he f)]
  have hn : (∑ f ∈ neighbors d, conditionalTerm K d f) =
      ∑ f : Dyad N, if f ≠ d ∧ overlap d f then conditionalTerm K d f else 0 := by
    unfold neighbors overlap
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro f hf
    split_ifs <;> rfl
  rw [hn, Finset.sum_add_distrib]
  ext a b
  simp only [Matrix.add_apply,Matrix.sum_apply,matrix_ite_apply,Matrix.zero_apply,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]


/-- Independent normal simulation variables (equation (4), p. 569,
correcting u_dt to nu_dt). Three disjoint index families encode all mutual
independence: unit covariates, unit effects, and observation shocks. -/
abbrev SimulationIndex (N T : ℕ) := Fin N ⊕ (Fin N ⊕ (Dyad N × Fin T))
/-- Independent standard normals X_i, alpha_i, nu_dt (corrected equation (4), p. 569; T22). -/
def simulationLaw (N T : ℕ) : Measure (SimulationIndex N T → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)
/-- "X_i" unit covariate in equation (4), p. 569. -/
def simulationX {N T : ℕ} (ω : SimulationIndex N T → ℝ) (i : Fin N) : ℝ := ω (Sum.inl i)
/-- "epsilon_dt = alpha_i+alpha_j+nu_dt" (equation (4), p. 569; corrected T22). -/
def simulationError {N T : ℕ} (ω : SimulationIndex N T → ℝ) (d : Dyad N) (t : Fin T) : ℝ :=
  (∑ i ∈ members d, ω (Sum.inr (Sum.inl i))) + ω (Sum.inr (Sum.inr (d,t)))


/-- Positive integer type and category label for the rare ill-conditioned
population (T19, P018-N004). `m` is M-1; label is C-1. -/
structure RareUnit where
  m : ℕ
  label : Fin (m+1)
  A : Bool
  B : Bool
  deriving DecidableEq
instance : MeasurableSpace RareUnit := ⊤

/-- M has P(M=m)=2^(-m), conditional labels are uniform on 1,...,m,
and independent A,B are fair signs (T19, P018-N004). This explicit countable
sum has the intended mass; probability normalization is stated in the witness. -/
def rareLaw : Measure RareUnit :=
  Measure.sum (fun m : ℕ =>
    ENNReal.ofReal ((2 : ℝ)^(-(m+1 : ℤ))/((m+1 : ℝ)*4)) •
      (∑ c : Fin (m+1), ∑ a : Bool, ∑ b : Bool, Measure.dirac (RareUnit.mk m c a b)))

/-- delta_m=1/(m^2 2^(m^2+2)) in the T19 rare ill-conditioning witness (P018-N004). -/
def rareDelta (m : ℕ) : ℝ := 1 / ((m : ℝ)^2 * (2 : ℝ)^(m*m+2))
/-- Same M, distinct category event in the T19 rare witness (P018-N004). -/
def rareSmall (u v : RareUnit) : Prop := u.m=v.m ∧ u.label.val ≠ v.label.val
instance (u v : RareUnit) : Decidable (rareSmall u v) := inferInstanceAs (Decidable (u.m=v.m ∧ u.label.val ≠ v.label.val))
/-- s_ij=delta_m on the small event, and one otherwise (T19, P018-N004). -/
def rareS (u v : RareUnit) : ℝ := if rareSmall u v then rareDelta (u.m+1) else 1
/-- a_ij=(A_i+A_j) times the small-event indicator (T19, P018-N004). -/
def rareA (u v : RareUnit) : ℝ := if rareSmall u v then signValue u.A+signValue v.A else 0

/-- The two bounded records X_ij,plus/minus and Y_ij,plus/minus in T19 (P018-N004). -/
def rareRepeated : RepeatedKernel RareUnit 2 :=
  ⟨rareLaw, fun _ _ => 2,
    fun _ _ t u v => ![1,1+(if t.val=0 then rareS u v else -rareS u v)],
    fun _ _ t u v => signValue u.B+signValue v.B+(if t.val=0 then rareA u v else -rareA u v)⟩


/-- q=E[s_12^2] and H=sum_m 2^(-3m)(1-1/m)^2 delta_m^2, from the
rare-model limit calculation (T19(f), P018-N004). -/
def rareQ : ℝ := ∫ uv, (rareS uv.1 uv.2)^2 ∂ rareLaw.prod rareLaw

/-- H=sum_m 2^(-3m)(1-1/m)^2 delta_m^2 in T19(f) (P018-N004). -/
def rareH : ℝ := ∑' m : ℕ, (2 : ℝ)^(-3*(m+1 : ℤ)) *
  (1-1/(m+1 : ℝ))^2 * (rareDelta (m+1))^2

/-- v=4H/q^2, the positive slope variance limit in T19(f) (P018-N004). -/
def rareLimitSlopeVariance : ℝ := 4*rareH/rareQ^2


/-- The nonlinear uniform witness's regressors, response and residual have
exact bounded ranges (T1(a), eq. (2) counterexample). -/
theorem nonlinear_bounds (z t : ℝ) (hz : -1 ≤ z ∧ z ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1) :
    0 ≤ 2+z+t ∧ 2+z+t ≤ 4 ∧ 0 ≤ (z+t)^2 ∧ (z+t)^2 ≤ 4 ∧
    -(2/3 : ℝ) ≤ (z+t)^2-2/3 ∧ (z+t)^2-2/3 ≤ 10/3 := by
  have h1 : -2 ≤ z+t := by linarith
  have h2 : z+t ≤ 2 := by linarith
  have hsq : (z+t)^2 ≤ 4 := by nlinarith
  have hnon := sq_nonneg (z+t)
  constructor
  · linarith
  constructor
  · linarith
  exact ⟨hnon, hsq, by linarith, by linarith⟩

/-- Exact residual substitution bound in the replacement for Appendix B
(T4(L5)): errors shifted by at most c have product error <=2 C_e c+c^2. -/
theorem residual_substitution_bound (a b u v Ce c : ℝ) (hCe : 0 ≤ Ce) (hc : 0 ≤ c)
    (ha : |a| ≤ Ce) (hb : |b| ≤ Ce) (hu : |u| ≤ c) (hv : |v| ≤ c) :
    |(a-u)*(b-v)-a*b| ≤ 2*Ce*c+c^2 := by
  have hav : |a*v| ≤ Ce*c := by
    rw [abs_mul]; exact mul_le_mul ha hv (abs_nonneg _) hCe
  have hbu : |b*u| ≤ Ce*c := by
    rw [abs_mul]; exact mul_le_mul hb hu (abs_nonneg _) hCe
  have huv : |u*v| ≤ c*c := by
    rw [abs_mul]; exact mul_le_mul hu hv (abs_nonneg _) hc
  have hid : (a-u)*(b-v)-a*b = -(a*v) - b*u + u*v := by ring
  rw [hid]
  have ht := abs_add_le (-(a*v)-b*u) (u*v)
  have ht2 := abs_sub (-(a*v)) (b*u)
  simp only [abs_neg] at ht2
  nlinarith

/-- The OLS score identity for a fixed full-rank finite sample
(T26(F1), Appendix A p. 573; T8(F4)). -/
theorem ols_score_identity {E : Type*} [Fintype E] {k : ℕ}
    (X : E → Vec k) (Y : E → ℝ) (β : Vec k) (hG : IsUnit (sampleGram X).det) :
    sampleOLS X Y - β = (sampleGram X)⁻¹.mulVec
      (∑ d, score (X d) (Y d-dot (X d) β)) := by
  have hnormal : (∑ d, score (X d) (dot (X d) β)) = (sampleGram X).mulVec β := by
    ext a
    simp only [score, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, sampleGram, Matrix.mulVec, dotProduct,
      dot, Matrix.sum_apply, Finset.sum_apply, outer, Matrix.of_apply]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hr : (∑ d, score (X d) (Y d-dot (X d) β)) =
      (∑ d, score (X d) (Y d)) - (sampleGram X).mulVec β := by
    rw [← hnormal]
    ext a
    simp [score, sub_mul, Finset.sum_sub_distrib]
  rw [hr, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]
  rfl

/-- The sparse covariance expansion is exact if disjoint scores are
uncorrelated. Uncentred moments require mean-zero individual scores.
This is the finite identity used by T2(ii), T12(iii), and T26(F3). -/
theorem variance_sparse_identity {Ω V E : Type*} [MeasurableSpace Ω]
    [Fintype E] [DecidableEq V] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : E → Finset V) {k : ℕ} (q : E → Ω → Vec k)
    (hL2 : ∀ d a, MemLp (fun ω => q d ω a) 2 μ)
    (hzero : ∀ d, meanVec μ (q d) = 0)
    (hdisjoint : ∀ d f, ¬(s d ∩ s f).Nonempty → covMat μ (q d) (q f) = 0) :
    varMat μ (fun ω => ∑ d, q d ω) =
      ∑ d, ∑ f, if (s d ∩ s f).Nonempty then
        meanMat μ (fun ω => outer (q d ω) (q f ω)) else 0 := by
  rw [variance_sum_identity μ q hL2]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hov : (s d ∩ s f).Nonempty
  · simp only [hov, if_true]
    ext a b
    have hz1 := congrFun (hzero d) a
    have hz2 := congrFun (hzero f) b
    simp only [meanVec, Pi.zero_apply] at hz1 hz2
    simp only [covMat, meanMat, outer, Matrix.of_apply]
    rw [ProbabilityTheory.covariance_eq_sub (hL2 d a) (hL2 f b), hz1, hz2]
    simp
  · simp only [hov, if_false]
    exact hdisjoint d f hov

/-- Intercept-only OLS fit in the exact N=4 sign witness, for arbitrary
unit values: beta-hat=(1/2)sum U_i (T3(a)). -/
theorem intercept4_fit (u : Fin 4 → ℝ) :
    let X : Fin 6 → Vec 1 := fun _ => ![1]
    let Y : Fin 6 → ℝ := fun d => ∑ i ∈ sixMembers d, u i
    sampleOLS X Y = ![(∑ i, u i)/2] ∧
    (∀ d, fittedResidual X Y d = signResidual4 u d) := by
  dsimp only
  have hg : sampleGram (fun _ : Fin 6 => (![1] : Vec 1)) = !![6] := by
    norm_num [sampleGram, outer, Matrix.of_apply, Matrix.mul_apply, Matrix.one_apply,
      Matrix.ofNat_apply,Matrix.natCast_apply,
      Fin.sum_univ_succ, funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]
  have hi : (sampleGram (fun _ : Fin 6 => (![1] : Vec 1)))⁻¹ = !![(1/6 : ℝ)] := by
    apply Matrix.inv_eq_left_inv
    rw [hg]
    norm_num [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.one_apply,
      funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]
  have hb : sampleOLS (fun _ : Fin 6 => (![1] : Vec 1))
      (fun d => ∑ i ∈ sixMembers d, u i) = ![(∑ i, u i)/2] := by
    rw [sampleOLS, hi]
    ext a
    fin_cases a
    simp [score, Matrix.mulVec, dotProduct, sixMembers, Fin.sum_univ_succ]
    ring
  refine ⟨hb, ?_⟩
  intro d
  simp [fittedResidual, hb, dot, signResidual4, Fin.sum_univ_succ]

/-- N=8 fitted residuals for the intercept sign model (T3(g)). -/
def signResidual8 (u : Fin 8 → ℝ) (i j : Fin 8) : ℝ := u i+u j-(∑ l,u l)/4

/-- Covariance on the 256 equiprobable N=8 iid sign samples (T3(g), P018-E006). -/
def fairCov8 (f g : (Fin 8 → ℝ) → ℝ) : ℝ :=
  fairAverage 8 (fun u => f u*g u)-fairAverage 8 f*fairAverage 8 g

/-- Products of fitted residuals on disjoint unit sets have covariance 7/16
at N=8, versus zero for population residuals. Another fitted covariance is
-1/16, contradicting the printed positivity language (T3(g), p. 574). -/
theorem fitted_products_counterexample :
    fairCov8 (fun u => signResidual8 u 0 1*signResidual8 u 0 2)
      (fun u => signResidual8 u 3 4*signResidual8 u 3 5) = 7/16 ∧
    fairCov8 (fun u => (u 0+u 1)*(u 0+u 2)) (fun u => (u 3+u 4)*(u 3+u 5)) = 0 ∧
    fairCov8 (fun u => signResidual8 u 0 1*signResidual8 u 0 2)
      (fun u => signResidual8 u 0 3*signResidual8 u 0 4) = -1/16 := by
  norm_num [fairCov8, fairAverage, signResidual8, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_succ']


/-- Repeated bread printed as E[X_d X'_d] can be singular even for an
excellent coefficient design, and the weighted scalar left bread changes
both coordinates of the covariance (T11(e),(f), pp. 568,576). -/
theorem printed_bread_numeric_certificate :
    (Matrix.det (!![1,1;1,1] : Mat 2)) = 0 ∧
    (∑ t : Fin 2, (1 : ℝ)^2) = 2 ∧
    (4/(2 : ℝ)^2) = 1 ∧ (1 : ℝ) ≠ 4 ∧
    (3/5 : ℝ) * 2 * 2 = 12/5 ∧ (12/5 : ℝ) ≠ 4 := by
  norm_num [Matrix.det_fin_two, Fin.sum_univ_succ]


/-- Standard normal quantile used by the corrected confidence interval
(T8(iii)). It is the lower quantile of the genuine N(0,1) measure. -/
def normalQuantile (p : ℝ) : ℝ := sInf {z : ℝ | p ≤ ((gaussianReal 0 1) (Set.Iic z)).toReal}


/-- Concrete probability-only example showing that stochastic convergence
of inverse factors gives no convergence of moments (T3(h), p. 574 correction).
The two-point law has mass 1/N at N and the remaining mass at one. -/
def inverseSpikeLaw (N : ℕ) : Measure ℝ :=
  ENNReal.ofReal ((N : ℝ)⁻¹) • Measure.dirac (N : ℝ) +
    ENNReal.ofReal (1-(N : ℝ)⁻¹) • Measure.dirac 1


/-- Pareto t^(-2) unit law on [1,infinity), and bounded regressors
(1,exp(-t_i)+exp(-t_j)) for the inverse-Gram moment witness (T3(i)). -/
def paretoUnitLaw : Measure ℝ := volume.withDensity (fun t =>
  if 1 ≤ t then ENNReal.ofReal ((t⁻¹)^2) else 0)
/-- X_ij=(1,exp(-T_i)+exp(-T_j)), Y_ij=0 in T3(i) (P018-E006, inverse-moment defect). -/
def inverseKernel : Kernel ℝ 2 :=
  ⟨paretoUnitLaw, fun u v => ![1,Real.exp (-u)+Real.exp (-v)], fun _ _ => 0⟩

/-- A bounded dyadic design can have infinite inverse moment at every N>=3
(T3(i)). Norm here is the finite-dimensional Euclidean operator norm,
represented by the induced action on unit Euclidean vectors. -/
def euclideanSq {k : ℕ} (x : Vec k) : ℝ := ∑ a, (x a)^2

/-- Euclidean operator norm of inverse Q_N, used in T3(i) (P018-E006). -/
def matrixOperatorNorm {k : ℕ} (M : Mat k) : ℝ :=
  sSup {r : ℝ | ∃ x : Vec k, euclideanSq x ≤ 1 ∧ r=Real.sqrt (euclideanSq (M.mulVec x))}


/-- Covariance of a fixed finite linear map is A Var(q) A' (T12(ii),
T20(i), and equation (1), p. 566). L2 is explicit so the finite sum
identities concern actual finite covariance integrals. -/
theorem covariance_linear_map {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ) (q : Ω → Vec k)
    (hq : ∀ a, MemLp (fun ω => q ω a) 2 μ) :
    varMat μ (fun ω => A.mulVec (q ω)) = A * varMat μ q * A.transpose := by
  ext i j
  simp only [varMat, covMat, Matrix.mulVec, dotProduct]
  rw [ProbabilityTheory.covariance_fun_sum_fun_sum
    (fun a => (hq a).const_mul (A i a)) (fun b => (hq b).const_mul (A j b))]
  simp only [ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_const_mul_right, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [covMat]
  ring

/-- Common multiplication of scores multiplies their covariance by a^2
(T10(C3), T12(ii)). This follows from the actual covariance definition and
does not replace the random design with a surrogate matrix. -/
theorem covariance_score_scale {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (q : Ω → Vec k) (a : ℝ) :
    varMat μ (fun ω => a • q ω) = (a^2) • varMat μ q := by
  ext i j
  simp only [varMat, covMat, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_const_mul_right]
  ring

/-- Entrywise expectations commute with a deterministic scalar (T10(C3),
T12(i), pp. 568,575--576). The integral is the same unit-design expectation. -/
theorem meanMat_scale {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (G : Ω → Mat k) (a : ℝ) :
    meanMat μ (fun ω => a • G ω) = a • meanMat μ G := by
  ext i j
  simp [meanMat, integral_const_mul]

/-- Vector expectations commute with a deterministic scalar (T10(C3),
T12(i), pp. 568,575--576). -/
theorem meanVec_scale {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (q : Ω → Vec k) (a : ℝ) :
    meanVec μ (fun ω => a • q ω) = a • meanVec μ q := by
  ext i
  simp [meanVec, integral_const_mul]

/-- Covariance of a shared-unit random-effect model Za+nu, under independent
finite-L2 random vectors with the stated covariance matrices (T6(ii), T5(a)). -/
theorem shared_random_effect_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m N : ℕ}
    (Z : Matrix (Fin m) (Fin N) ℝ) (a : Ω → Vec N) (ν : Ω → Vec m)
    (ha : ∀ i, MemLp (fun ω => a ω i) 2 μ) (hν : ∀ d, MemLp (fun ω => ν ω d) 2 μ)
    (hind : IndepFun a ν μ) (τ σ : ℝ)
    (hCa : varMat μ a = τ • 1) (hCν : varMat μ ν = σ • 1) :
    varMat μ (fun ω => Z.mulVec (a ω)+ν ω) = τ • (Z*Z.transpose) + σ • 1 := by
  have hl (d : Fin m) : MemLp (fun ω => Z.mulVec (a ω) d) 2 μ := by
    simpa [Matrix.mulVec, dotProduct] using
      memLp_finsetSum (univ : Finset (Fin N)) (fun i _ => (ha i).const_mul (Z d i))
  have cross (d f : Fin m) : ProbabilityTheory.covariance
      (fun ω => Z.mulVec (a ω) d) (fun ω => ν ω f) μ = 0 := by
    simp only [Matrix.mulVec, dotProduct]
    rw [ProbabilityTheory.covariance_fun_sum_left
      (fun i => (ha i).const_mul (Z d i)) (hν f)]
    simp only [ProbabilityTheory.covariance_const_mul_left]
    apply Finset.sum_eq_zero
    intro i hi
    have hind' : IndepFun (fun ω => a ω i) (fun ω => ν ω f) μ :=
      hind.comp (measurable_pi_apply i) (measurable_pi_apply f)
    rw [hind'.covariance_eq_zero (ha i) (hν f), mul_zero]
  have hv := covariance_linear_map μ Z a ha
  have he : varMat μ (fun ω => Z.mulVec (a ω)+ν ω) =
      varMat μ (fun ω => Z.mulVec (a ω)) + varMat μ ν := by
    ext d f
    simp only [varMat, covMat, Pi.add_apply, Matrix.add_apply]
    change ProbabilityTheory.covariance
      ((fun ω => Z.mulVec (a ω) d) + (fun ω => ν ω d))
      ((fun ω => Z.mulVec (a ω) f) + (fun ω => ν ω f)) μ = _
    rw [ProbabilityTheory.covariance_add_left (hl d) (hν d) ((hl f).add (hν f)),
      ProbabilityTheory.covariance_add_right (hl d) (hl f) (hν f),
      ProbabilityTheory.covariance_add_right (hν d) (hl f) (hν f)]
    rw [cross d f, ProbabilityTheory.covariance_comm (fun ω => ν ω d), cross f d]
    ring
  rw [he, hv, hCa, hCν]
  simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]


/-- Repeated sign data with fixed but unbounded lengths 2^(i+j) (T9(e)). -/
def concentratedRepeated : RepeatedKernel Bool 1 :=
  ⟨fairLaw, fun _ d => 2^((firstUnit d).val+(secondUnit d).val+2),
    fun _ _ _ _ _ => ![1], fun _ _ _ u v => signValue u+signValue v⟩


/-- Inverse of a rescaled nonsingular coefficient Gram, used by the exact
common-weight-rescaling calculation (T10(C3)). -/
theorem matrix_inverse_scale {k : ℕ} (G : Mat k) (hG : IsUnit G.det) (a : ℝ) (ha : a ≠ 0) :
    (a • G)⁻¹ = a⁻¹ • G⁻¹ := by
  apply Matrix.inv_eq_left_inv
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_inv_cancel₀ ha, one_smul, Matrix.nonsing_inv_mul G hG]


/-- Common nonzero scaling preserves the totalized nonsingular matrix
inverse rule even on singular samples (T10(C3), p. 575). This extends the
rank-valid matrix_inverse_scale lemma, without adding statistical assumptions. -/
theorem matrix_inverse_scale_total {k : ℕ} (G : Mat k) (a : ℝ) (ha : a ≠ 0) :
    (a • G)⁻¹ = a⁻¹ • G⁻¹ := by
  by_cases hG : IsUnit G.det
  · exact matrix_inverse_scale G hG a ha
  · have hz : G.det = 0 := by simpa [isUnit_iff_ne_zero] using hG
    have hs : ¬IsUnit (a • G).det := by simp [Matrix.det_smul, hz]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hG,
      Matrix.nonsing_inv_apply_not_isUnit _ hs, smul_zero]

/-- A common multiplier on all scores multiplies the meat by its square
(T10(C3), eq. (7)). -/
theorem meat_scale {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (q : E → Vec k) (a : ℝ) :
    meat s (fun d => a • q d) = (a^2) • meat s q := by
  classical
  ext i j
  simp only [meat, matrix_ite_apply, outer, Matrix.of_apply, Matrix.sum_apply, Finset.sum_apply,
    Matrix.smul_apply, Matrix.zero_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro f hf
  split_ifs <;> ring

/-- WLS and equation (7)'s fitted sandwich are exactly invariant under
common positive rescaling on every nonsingular sample (T10(C3)). -/
theorem weighted_sample_scale_invariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (w : Dyad N → ℝ) (ω : Fin N → U)
    (hG : IsUnit (weightedGram K w ω).det) (a : ℝ) (ha : a ≠ 0) :
    weightedOLS K (fun d => a*w d) ω = weightedOLS K w ω ∧
    weightedVariance K (fun d => a*w d) ω = weightedVariance K w ω := by
  have hg : weightedGram K (fun d => a*w d) ω = a • weightedGram K w ω := by
    simp [weightedGram, Finset.smul_sum, mul_smul]
  have hi : (weightedGram K (fun d => a*w d) ω)⁻¹ = a⁻¹ • (weightedGram K w ω)⁻¹ := by
    rw [hg, matrix_inverse_scale _ hG a ha]
  have hn : (∑ d, score (design K ω d) (a*w d*response K ω d)) =
      a • (∑ d, score (design K ω d) (w d*response K ω d)) := by
    ext b
    simp [score, Finset.mul_sum, mul_assoc]
  have hb : weightedOLS K (fun d => a*w d) ω = weightedOLS K w ω := by
    simp only [weightedOLS, hi, hn, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
    rw [mul_inv_cancel₀ ha, one_smul]
  refine ⟨hb, ?_⟩
  simp only [weightedVariance, hi, hb]
  have hs : (fun d => score (design K ω d)
      (a*w d*(response K ω d-dot (design K ω d) (weightedOLS K w ω)))) =
      fun d => a • score (design K ω d)
        (w d*(response K ω d-dot (design K ω d) (weightedOLS K w ω))) := by
    ext d b
    simp [score, mul_assoc]
  rw [hs, meat_scale]
  exact sandwich_scale_invariance a ha _ _


/-- Exact scale invariance (T10(C3), Appendix D pp. 575--576): multiplying
every weighted record by a common positive a leaves WLS, its fitted dyadic
covariance and the corrected population target unchanged. Applies also to
directed records. No unweighted population rank assumption is needed. -/
theorem weighted_scale_invariance {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ)
    (a : ℝ) (ha : 0 < a) (ω : Fin N → U) :
    recordWeightedOLS R (fun d t => a*w d t) ω = recordWeightedOLS R w ω ∧
    recordWeightedVariance R (fun d t => a*w d t) ω = recordWeightedVariance R w ω ∧
    recordWeightedTarget R (fun d t => a*w d t) = recordWeightedTarget R w := by
  have ha0 : a ≠ 0 := ha.ne'
  have hg : recordWeightedGram R (fun d t => a*w d t) =
      fun ω => a • recordWeightedGram R w ω := by
    funext ω
    simp [recordWeightedGram, Finset.smul_sum, mul_smul]
  have hn : recordWeightedXY R (fun d t => a*w d t) =
      fun ω => a • recordWeightedXY R w ω := by
    funext ω
    ext b
    simp [recordWeightedXY, score, Finset.mul_sum, mul_assoc]
  have hb : recordWeightedOLS R (fun d t => a*w d t) ω = recordWeightedOLS R w ω := by
    simp only [recordWeightedOLS, hg, hn, matrix_inverse_scale_total _ a ha0,
      Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
    rw [mul_inv_cancel₀ ha0, one_smul]
  have hpop : recordWeightedBeta R (fun d t => a*w d t) = recordWeightedBeta R w := by
    simp only [recordWeightedBeta, hg, hn, meanMat_scale, meanVec_scale,
      matrix_inverse_scale_total _ a ha0, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
    rw [mul_inv_cancel₀ ha0, one_smul]
  have hs (β : Vec k) (u : Fin N → U) :
      recordWeightedBlockScore R (fun d t => a*w d t) β u =
        fun d => a • recordWeightedBlockScore R w β u d := by
    funext d
    ext b
    simp [recordWeightedBlockScore, score, Finset.mul_sum, mul_assoc]
  have hH : recordWeightedH R (fun d t => a*w d t) = a • recordWeightedH R w := by
    simp only [recordWeightedH, hg, meanMat_scale, smul_smul]
    congr 1
    ring
  refine ⟨hb, ?_, ?_⟩
  · simp only [recordWeightedVariance, hg, hb, hs,
      matrix_inverse_scale_total _ a ha0, meat_scale]
    exact sandwich_scale_invariance a ha0 _ _
  · simp only [recordWeightedTarget, hH, hpop, hs,
      matrix_inverse_scale_total _ a ha0]
    have hsum : (fun u => ∑ d : Dyad N,
        a • recordWeightedBlockScore R w (recordWeightedBeta R w) u d) =
        fun u => a • (∑ d : Dyad N, recordWeightedBlockScore R w (recordWeightedBeta R w) u d) := by
      funext u
      rw [Finset.smul_sum]
    rw [hsum, covariance_score_scale, sandwich_scale_invariance a ha0]


/-- The corrected standard-error recipe has an honest domain, symmetric
score sandwich structure, and contraction/event bounds (T18(i)--(iv), p. 567).
The sampling convergence implications use these inequalities entrywise. -/
theorem standard_error_correction {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (s : E → Finset V)
    (hs : ∀ d, (s d).card = 2) (hi : Function.Injective s)
    {k : ℕ} (q : E → Vec k) (P : Mat k) (hP : P.transpose = P) :
    meat s q = (∑ i, outer (unitScore s q i) (unitScore s q i)) - dyadMeat q ∧
    (sandwich P (meat s q)).transpose = sandwich P (meat s q) ∧
    (∀ v : ℝ, (∃ se, standardError v = some se) ↔ 0 ≤ v) ∧
    (∀ N : ℝ, 0 ≤ N → ∀ v V : ℝ, 0 ≤ V → |N*max v 0-V| ≤ |N*v-V|) ∧
    (∀ N : ℝ, 0 ≤ N → ∀ v V : ℝ, 0 < V → v < 0 → V ≤ |N*v-V|) := by
  exact ⟨overlap_meat_identity s hs hi q, sandwich_symmetric P (meat s q) hP (meat_symmetric s q),
    standard_error_domain, scaled_truncation, negative_implies_deviation⟩

/-- Truncation keeps N-scaled consistency for nonnegative targets, as an
actual probability-limit theorem (T18(ii)). -/
theorem truncation_keeps_consistency {Ω : ℕ → Type*} [∀ N : ℕ, MeasurableSpace (Ω N)]
    (μ : ∀ N : ℕ, Measure (Ω N)) (hμ : ∀ N : ℕ, IsProbabilityMeasure (μ N))
    (v : ∀ N : ℕ, Ω N → ℝ) (V : ℕ → ℝ) (hV : ∀ N : ℕ, 0 ≤ V N)
    (hconv : inProbability μ (fun N ω => (N : ℝ)*v N ω-V N)) :
    inProbability μ (fun N ω => (N : ℝ)*max (v N ω) 0-V N) := by
  intro ε hε
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ (hconv ε hε)
  intro N
  letI := hμ N
  apply ENNReal.toReal_mono (measure_ne_top (μ N) _)
  apply measure_mono
  intro ω hω
  have hineq := scaled_truncation (N : ℝ) (Nat.cast_nonneg N) (v N ω) (V N) (hV N)
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs] at hω ⊢
  exact hω.trans hineq


/-- Complete fitted logistic counterexample to the literal cross-dyad
formula (T13(a)--(d), Appendix E p. 576): binary outcomes, nonsingular
bread, unique fitted parameter zero, and two different computed covariances. -/
theorem logistic_counterexample :
    (∀ d, logitY d=0 ∨ logitY d=1) ∧
    (∀ β : Vec 2, (∑ d,logLikelihood (logitX d) (logitY d) β) ≤
      ∑ d,logLikelihood (logitX d) (logitY d) 0) ∧
    (∀ β : Vec 2, (∑ d,logLikelihood (logitX d) (logitY d) β) =
      (∑ d,logLikelihood (logitX d) (logitY d) 0) → β=0) ∧
    (logisticBread logitX 0).det = 35/4 ∧
    sandwich (logisticBread logitX 0)⁻¹ (printedLogisticMeat sixMembers logitX logitR) =
      !![8/5,-2/5;-2/5,6/35] ∧
    logisticVariance sixMembers logitX logitY 0 = !![38/25,-64/175;-64/175,192/1225] ∧
    sandwich (logisticBread logitX 0)⁻¹ (printedLogisticMeat sixMembers logitX logitR) ≠
      logisticVariance sixMembers logitX logitY 0 := by
  rcases logistic_numeric_certificate with ⟨hscore,hmean,hdet,hleft,hprinted,hmeat,hVp,hVc,hdiff⟩
  rcases logistic_witness_is_MLE with ⟨hmax,hunique,hr⟩
  have hb : logisticBread logitX 0 = logitH := by
    norm_num [logisticBread,expit,dot,logitX,logitH,outer, Matrix.of_apply,Fin.sum_univ_succ,
      funext_iff, ← Matrix.ext_iff,Fin.forall_fin_succ]
  have hi : (logisticBread logitX 0)⁻¹ = logitHinv := by
    rw [hb]
    exact Matrix.inv_eq_left_inv hleft
  have hp : sandwich (logisticBread logitX 0)⁻¹
      (printedLogisticMeat sixMembers logitX logitR) = logitHinv := by
    rw [hi,hprinted,hVp]
  have hc : logisticVariance sixMembers logitX logitY 0 =
      (!![38/25,-64/175;-64/175,192/1225] : Mat 2) := by
    unfold logisticVariance
    simp_rw [hr]
    rw [hi,hmeat,hVc]
  refine ⟨?_,hmax,hunique,?_,?_,hc,?_⟩
  · intro d
    fin_cases d <;> norm_num [logitY]
  · rw [hb]; exact hdet
  · exact hp
  · rw [hp,hc]
    intro he
    have := congrArg (fun M : Mat 2 => M 0 0) he
    norm_num [logitHinv] at this

/-- Both Gram terms in the incidence representation are positive
semidefinite, although their difference need not be (T18(i)). -/
theorem outer_positive_semidefinite {k : ℕ} (x : Vec k) : (outer x x).PosSemidef := by
  convert Matrix.posSemidef_vecMulVec_self_star x using 1
  ext i j
  simp [outer, Matrix.of_apply,Matrix.vecMulVec]

/-- The unit-cluster and dyad-diagonal meats are positive semidefinite
(T18(i), correction to the standard-error recipe after Proposition 1). -/
theorem score_gram_terms_psd {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (s : E → Finset V) {k : ℕ} (q : E → Vec k) :
    (∑ i, outer (unitScore s q i) (unitScore s q i)).PosSemidef ∧ (dyadMeat q).PosSemidef := by
  constructor
  · exact Matrix.posSemidef_sum univ (fun i _ => outer_positive_semidefinite _)
  · exact Matrix.posSemidef_sum univ (fun d _ => outer_positive_semidefinite _)


/-- The unrestricted ordered non-incident index has two orientations per
unordered dyad; self-dyads are excluded (T15(a), pp. 568,575). -/
def orderedNonincidentMeat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (T : E → ℕ)
    (q : (d : E) → Fin (T d) → Vec k) (i : V) : Mat k :=
  ∑ _orientation : Fin 2, nonincidentMeat s T q i

/-- Literal ordered non-incident reading of Sigma_C,i (T15, Proposition 2, p. 568 and Appendix C, p. 575). -/
def orderedClusterMeat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (T : E → ℕ)
    (q : (d : E) → Fin (T d) → Vec k) (i : V) : Mat k :=
  outer (unitScore s (fun d => ∑ t,q d t) i) (unitScore s (fun d => ∑ t,q d t) i) +
    orderedNonincidentMeat s T q i

/-- General factor-two defect of the ordered reading, and its extra
(N-2) Sigma_0 contribution (T15(a), Proposition 2 and Appendix C). -/
theorem ordered_index_general {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (s : E → Finset V)
    (hs : ∀ d, (s d).card = 2) (hi : Function.Injective s)
    {k : ℕ} (T : E → ℕ) (q : (d : E) → Fin (T d) → Vec k) :
    (∀ i, orderedNonincidentMeat s T q i = (2 : ℝ) • nonincidentMeat s T q i) ∧
    (∑ i, orderedNonincidentMeat s T q i) =
      (2*((Fintype.card V : ℝ)-2)) • individualMeat T q ∧
    (∑ i, orderedClusterMeat s T q i) - dyadMeat (fun d => ∑ t,q d t) -
      ((Fintype.card V : ℝ)-2) • individualMeat T q =
        meat s (fun d => ∑ t,q d t)+((Fintype.card V : ℝ)-2) • individualMeat T q := by
  have hd : ∀ i, orderedNonincidentMeat s T q i =
      nonincidentMeat s T q i+nonincidentMeat s T q i := by
    intro i
    simp only [orderedNonincidentMeat,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  have hsum := nonincident_sum s hs T q
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [hd,two_smul]
  · simp_rw [hd,Finset.sum_add_distrib]
    rw [hsum]
    simp [add_smul,two_mul]
  · have hcorrect := (proposition2_corrected s hs hi T q (1 : Mat k)).1
    have he : (∑ i, orderedClusterMeat s T q i) =
        (∑ i, clusterMeat s T q i) + ∑ i, nonincidentMeat s T q i := by
      simp only [orderedClusterMeat,hd,clusterMeat,Finset.sum_add_distrib]
      abel
    rw [he,hsum,hcorrect]
    abel

/-- If N-scaled consistency has a fixed positive target, negative variance
estimates have probability tending to zero (T18(iii), p. 567 correction). -/
theorem negative_diagonals_vanish {Ω : ℕ → Type*} [∀ N : ℕ, MeasurableSpace (Ω N)]
    (μ : ∀ N : ℕ, Measure (Ω N)) (hμ : ∀ N : ℕ, IsProbabilityMeasure (μ N))
    (v : ∀ N : ℕ, Ω N → ℝ) (V : ℝ) (hV : 0 < V)
    (hconv : inProbability μ (fun N ω => (N : ℝ)*v N ω-V)) :
    Tendsto (fun N : ℕ => (μ N {ω | v N ω<0}).toReal) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ (hconv V hV)
  intro N
  letI := hμ N
  apply ENNReal.toReal_mono (measure_ne_top (μ N) _)
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq,Real.norm_eq_abs] at hω ⊢
  exact negative_implies_deviation (N : ℝ) (Nat.cast_nonneg N) (v N ω) V hV hω


/-- The finite coefficient in T4(L2),(L5) is at most four for N>=2
(replacement for Appendix B, pp. 573--574). -/
theorem normalized_overlap_coefficient (N : ℕ) (hN : 2 ≤ N) :
    (N : ℝ)/(Dreal N)^2 * (Dreal N*(2*(N : ℝ)-3)) =
      2*(2*(N : ℝ)-3)/((N : ℝ)-1) ∧
    0 ≤ 2*(2*(N : ℝ)-3)/((N : ℝ)-1) ∧
    2*(2*(N : ℝ)-3)/((N : ℝ)-1) ≤ 4 := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
  have hp1 : 0 < (N : ℝ)-1 := by linarith
  have hp2 : 0 ≤ 2*(N : ℝ)-3 := by linarith
  refine ⟨?_,?_,?_⟩
  · unfold Dreal
    field_simp
    <;> ring
  · positivity
  · apply (div_le_iff₀ (by linarith : 0 < (N : ℝ)-1)).mpr
    linarith

/-- The same-data generic score second moment has the usual PSD Gram
structure when all score coordinates have finite second moments (T23(v),
Appendix E, p. 576). Both factors use the same data argument. -/
theorem generic_score_meat_psd {Ω Θ : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ψ : Ω → Θ → Vec k) (θ : Θ)
    (hL2 : ∀ a, MemLp (fun ω => ψ ω θ a) 2 μ) :
    (genericScoreMeat μ ψ θ).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext a b
    simp [Matrix.IsHermitian, Matrix.conjTranspose_apply, genericScoreMeat,
      meanMat, outer, mul_comm]
  · intro x
    have hi (a b : Fin k) : Integrable
        (fun ω => x a * (ψ ω θ a * ψ ω θ b * x b)) μ :=
      ((hL2 a).integrable_mul (hL2 b)).mul_const (x b) |>.const_mul (x a)
    have hsum : Integrable
        (fun ω => ∑ a : Fin k, ∑ b : Fin k, x a * (ψ ω θ a * ψ ω θ b * x b)) μ :=
      integrable_finset_sum univ (fun a _ => integrable_finset_sum univ (fun b _ => hi a b))
    have he : star x ⬝ᵥ ((genericScoreMeat μ ψ θ).mulVec x) =
        ∫ ω, ∑ a : Fin k, ∑ b : Fin k, x a * (ψ ω θ a * ψ ω θ b * x b) ∂ μ := by
      simp only [genericScoreMeat, meanMat, Matrix.mulVec, dotProduct,
        Pi.star_apply, star_trivial, outer, Finset.mul_sum]
      rw [integral_finsetSum univ
        (fun a _ => integrable_finset_sum univ (fun b _ => hi a b))]
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_finsetSum univ (fun b _ => hi a b)]
      simp [integral_const_mul, integral_mul_const]
    rw [he]
    apply integral_nonneg
    intro ω
    have heq : (∑ a : Fin k, ∑ b : Fin k, x a * (ψ ω θ a * ψ ω θ b * x b)) =
        (dot x (ψ ω θ))^2 := by
      simp only [dot, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    change 0 ≤ ∑ a : Fin k, ∑ b : Fin k, x a * (ψ ω θ a * ψ ω θ b * x b)
    rw [heq]
    exact sq_nonneg _


/-- Exact normalized sample sandwich identity in the replacement proof
(T4(L6), Appendix B, pp. 573--574), on each nonsingular sample. -/
theorem normalized_sample_sandwich {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (ω : Fin N → U) (hN : 2 ≤ N)
    (hG : IsUnit (sampleGram (design K ω)).det) :
    (N : ℝ) • sampleVariance members (design K ω) (response K ω) =
      sandwich (((Dreal N)⁻¹ • sampleGram (design K ω))⁻¹)
        (scaledMeat K (fun w => fittedResidual (design K w) (response K w)) ω) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hD : Dreal N ≠ 0 := by
    unfold Dreal
    exact ne_of_gt (div_pos (mul_pos (by linarith) (by linarith)) (by norm_num))
  rw [matrix_inverse_scale _ hG _ (inv_ne_zero hD),inv_inv]
  simp only [sampleVariance,scaledMeat,sandwich,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have hc : Dreal N*((N : ℝ)/(Dreal N)^2*Dreal N) = (N : ℝ) := by
    field_simp [hD]
  rw [hc]


/-- The corrected repeated/weighted targets reduce to equation (1) for
one record per dyad and unit weights (T12(iv),(v), pp. 568,575--576). -/
def singleRecord {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : RepeatedKernel U k :=
  ⟨K.μ, fun _ _ => 1, fun _ _ _ u v => K.X u v, fun _ _ _ u v => K.Y u v⟩


/-- Equivalent normalizations of the corrected repeated target (T12(v),
p. 568 correction): observation-normalized and dyad-normalized Gram matrices
cancel their respective prefactors. Only nonzero counts and rank at this N
are needed; there is no common-kernel, symmetry or all-size rank requirement. -/
theorem repeated_target_normalization {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hN : 2 ≤ N) (hL : repeatedL R N ≠ 0)
    (hG : (meanMat (repeatedLaw R N) (repeatedGram R)).det ≠ 0) :
    repeatedTarget R N = ((N : ℝ)/(Dreal N)^2) •
      sandwich ((Dreal N)⁻¹ • meanMat (repeatedLaw R N) (repeatedGram R))⁻¹
        (varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N,
          repeatedBlockScore R (repeatedBeta R N) ω d)) := by
  have hreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
  have hD : Dreal N ≠ 0 := by
    unfold Dreal
    exact div_ne_zero (mul_ne_zero hn0 hn1) (by norm_num)
  have hunit : IsUnit (meanMat (repeatedLaw R N) (repeatedGram R)).det := isUnit_iff_ne_zero.mpr hG
  unfold repeatedTarget repeatedH
  rw [matrix_inverse_scale _ hunit _ (inv_ne_zero hL),
    matrix_inverse_scale _ hunit _ (inv_ne_zero hD)]
  simp only [inv_inv, sandwich, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  field_simp [hL, hD] <;> ring


/-- C_i, the distinct incident-dyad cross terms in Appendix C (p. 575),
with block scores sum_t X_dt e_dt (corrected T16). -/
def crossUnitMeat {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (s : E → Finset V) {k : ℕ} (q : E → Vec k) (i : V) : Mat k :=
  ∑ d, ∑ f, if d ≠ f ∧ i ∈ s d ∧ i ∈ s f then outer (q d) (q f) else 0

/-- D_i, the incident-dyad diagonal terms in Appendix C (p. 575;
corrected T16). These are block-score outer products, not record diagonals. -/
def incidentDiagonalMeat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (q : E → Vec k) (i : V) : Mat k :=
  ∑ d, if i ∈ s d then outer (q d) (q d) else 0

/-- All five corrected finite steps of Appendix C (T16, p. 575), for
arbitrary real record scores on two-element dyads. -/
theorem appendixC_corrected_steps {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (s : E → Finset V)
    (hs : ∀ d, (s d).card = 2) (hi : Function.Injective s)
    {k : ℕ} (T : E → ℕ) (q : (d : E) → Fin (T d) → Vec k) :
    let b := fun d => ∑ t,q d t
    meat s b-dyadMeat b = (∑ i,crossUnitMeat s b i) ∧
    (∀ i, clusterMeat s T q i =
      crossUnitMeat s b i+incidentDiagonalMeat s b i+nonincidentMeat s T q i) ∧
    (∑ i,incidentDiagonalMeat s b i) = (2 : ℝ) • dyadMeat b ∧
    (∑ i,nonincidentMeat s T q i) = ((Fintype.card V : ℝ)-2) • individualMeat T q ∧
    meat s b = dyadMeat b+(∑ i,crossUnitMeat s b i) := by
  classical
  dsimp only
  let b : E → Vec k := fun d => ∑ t, q d t
  have hg (i : V) : outer (unitScore s b i) (unitScore s b i) =
      crossUnitMeat s b i + incidentDiagonalMeat s b i := by
    ext a c
    simp only [outer,Matrix.of_apply,unitScore,crossUnitMeat,incidentDiagonalMeat,
      Matrix.add_apply,Matrix.sum_apply,Finset.sum_apply,matrix_ite_apply,Matrix.zero_apply]
    simp_rw [Finset.sum_mul,Finset.mul_sum]
    have hsplit (d f : E) :
        (if i ∈ s d then b d else 0) a*(if i ∈ s f then b f else 0) c =
          (if d ≠ f ∧ i ∈ s d ∧ i ∈ s f then b d a*b f c else 0) +
            (if f=d then (if i ∈ s d then b d a*b d c else 0) else 0) := by
      by_cases hfd : f=d
      · subst f
        by_cases hmem : i ∈ s d <;> simp [hmem]
      · by_cases hd : i ∈ s d <;> by_cases hf : i ∈ s f <;>
          simp [hfd,Ne.symm hfd,hd,hf]
    simp_rw [hsplit,Finset.sum_add_distrib]
    first | rfl | simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have hdiag : (∑ i,incidentDiagonalMeat s b i) = (2 : ℝ) • dyadMeat b := by
    ext a c
    simp only [incidentDiagonalMeat,dyadMeat,Matrix.sum_apply,Matrix.smul_apply,
      smul_eq_mul,matrix_ite_apply,Matrix.zero_apply]
    rw [Finset.sum_comm]
    have ht (d : E) : (∑ i : V, if i ∈ s d then outer (b d) (b d) a c else 0) =
        2 * outer (b d) (b d) a c := by
      simp [← Finset.sum_filter,hs d]
    simp_rw [ht]
    rw [Finset.mul_sum]
  have hm : meat s b = dyadMeat b + (∑ i,crossUnitMeat s b i) := by
    rw [overlap_meat_identity s hs hi b]
    simp_rw [hg,Finset.sum_add_distrib]
    rw [hdiag,two_smul]
    abel
  refine ⟨?_,?_,hdiag,nonincident_sum s hs T q,hm⟩
  · rw [hm]
    abel
  · intro i
    change outer (unitScore s b i) (unitScore s b i) + nonincidentMeat s T q i =
      crossUnitMeat s b i + incidentDiagonalMeat s b i + nonincidentMeat s T q i
    rw [hg]

/-- Exact incidence-matrix version of the variance-meat structure (T18(i),
p. 567 correction). W=B'B-I is the equal-or-overlapping dyad indicator. -/
theorem incidence_meat_structure {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (s : E → Finset V)
    (hs : ∀ d, (s d).card = 2) (hi : Function.Injective s)
    {k : ℕ} (q : E → Vec k) :
    let B : Matrix V E ℝ := Matrix.of (fun i d => if i ∈ s d then 1 else 0)
    let S : Matrix E (Fin k) ℝ := Matrix.of (fun d a => q d a)
    (∀ d f, (B.transpose*B-(1 : Matrix E E ℝ)) d f = (if (s d ∩ s f).Nonempty then 1 else 0)) ∧
    meat s q = S.transpose*(B.transpose*B-(1 : Matrix E E ℝ))*S ∧
    meat s q = (B*S).transpose*(B*S)-S.transpose*S := by
  let B : Matrix V E ℝ := Matrix.of (fun i d => if i ∈ s d then 1 else 0)
  let S : Matrix E (Fin k) ℝ := Matrix.of (fun d a => q d a)
  change (∀ d f, (B.transpose*B-(1 : Matrix E E ℝ)) d f = (if (s d ∩ s f).Nonempty then 1 else 0)) ∧
    meat s q = S.transpose*(B.transpose*B-(1 : Matrix E E ℝ))*S ∧
    meat s q = (B*S).transpose*(B*S)-S.transpose*S
  have hcount (d f : E) : (B.transpose*B) d f = ((s d ∩ s f).card : ℝ) := by
    simp only [B,Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply]
    simp_rw [ite_mul,one_mul,zero_mul]
    simp_rw [← ite_and]
    simp [← Finset.mem_inter,← Finset.sum_filter,Finset.inter_comm]
  have hW : ∀ d f, (B.transpose*B-(1 : Matrix E E ℝ)) d f = (if (s d ∩ s f).Nonempty then 1 else 0) := by
    intro d f
    rw [Matrix.sub_apply,hcount,Matrix.one_apply,intersection_count s hs hi d f]
    split_ifs <;> ring
  have hBS (i : V) (a : Fin k) : (B*S) i a = unitScore s q i a := by
    simp [B,S,Matrix.mul_apply,unitScore,ite_mul,Matrix.of_apply,ite_apply,Pi.zero_apply,Finset.sum_apply]
  have hG : (B*S).transpose*(B*S) = ∑ i,outer (unitScore s q i) (unitScore s q i) := by
    ext a b
    simp only [Matrix.mul_apply,Matrix.transpose_apply,hBS,Matrix.sum_apply,outer, Matrix.of_apply]
  have hD : S.transpose*S = dyadMeat q := by
    ext a b
    simp only [S,Matrix.mul_apply,Matrix.transpose_apply,dyadMeat,Matrix.sum_apply,outer, Matrix.of_apply]
  have hm : meat s q = (B*S).transpose*(B*S)-S.transpose*S := by
    rw [overlap_meat_identity s hs hi q,← hG,← hD]
  refine ⟨hW,?_,hm⟩
  rw [hm]
  simp only [Matrix.transpose_mul,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.mul_assoc]


/-- The exact nine displayed D/H ratios and their worst-case rounded upper
bounds in row order (T24(i),(ii), Table 1, p. 572). -/
theorem table_exact_ratios :
    tableSE.map (fun r => r.2.2/r.1) =
      [265/69,7/2,3,24749/10734,4,5/2,51/13,172/39,840/211] ∧
    tableSE.map (fun r => (r.2.2+1/2000)/(r.1-1/2000)) =
      [531/137,47/13,31/9,49499/21467,17/3,53/21,205/51,689/155,1681/421] := by
  norm_num [tableSE]


/-- Equivalent positive-exponential form of expit, used to differentiate
Appendix E's corrected scalar predictor (T23(i), p. 576). -/
theorem expit_positive_form (t : ℝ) : expit t = Real.exp t/(1+Real.exp t) := by
  have he : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hd : 1+Real.exp t ≠ 0 := by positivity
  unfold expit
  rw [Real.exp_neg]
  field_simp [he,hd] <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- Derivative expit'(t)=p(1-p), the logistic score Jacobian factor
(T23(iii), Appendix E, p. 576). -/
theorem expit_hasDerivAt (t : ℝ) :
    HasDerivAt expit (expit t*(1-expit t)) t := by
  have hd : 1+Real.exp t ≠ 0 := by positivity
  have hf : expit = fun u => Real.exp u/(1+Real.exp u) := funext expit_positive_form
  rw [hf]
  convert (Real.hasDerivAt_exp t).fun_div
    ((hasDerivAt_const t (1 : ℝ)).fun_add (Real.hasDerivAt_exp t)) hd using 1 <;>
    simp only [Pi.add_apply] <;> field_simp [hd] <;> ring

/-- A coordinate partial derivative of x'beta is x_a
(T23(ii), corrected Appendix E scalar predictor, p. 576). -/
theorem predictor_partial_derivative {k : ℕ} (x β : Vec k) (a : Fin k) :
    HasDerivAt (fun t => dot x (Function.update β a t)) (x a) (β a) := by
  have h (b : Fin k) : HasDerivAt (fun t => x b*Function.update β a t b)
      (if b=a then x b else 0) (β a) := by
    by_cases hb : b=a
    · subst b
      simpa using (hasDerivAt_id (β a)).const_mul (x a)
    · simpa [hb,Function.update_of_ne hb] using hasDerivAt_const (β a) (x b*β b)
  simpa [dot] using (HasDerivAt.fun_sum (u := (univ : Finset (Fin k))) (fun b _ => h b))

set_option backward.isDefEq.respectTransparency false in
/-- Scalar logistic log-likelihood derivative is y-expit(t)
(T23(ii), Appendix E, p. 576), for every real response y. -/
theorem scalar_logLikelihood_derivative (y t : ℝ) :
    HasDerivAt (fun u => y*u-Real.log (1+Real.exp u)) (y-expit t) t := by
  have hd : 1+Real.exp t ≠ 0 := by positivity
  simpa only [expit_positive_form,zero_add,mul_one,Pi.add_apply,Pi.sub_apply,id_eq] using
    ((hasDerivAt_id t).const_mul y).fun_sub
      (((hasDerivAt_const t (1 : ℝ)).fun_add (Real.hasDerivAt_exp t)).log hd)

set_option backward.isDefEq.respectTransparency false in
/-- Corrected predictor, gradient, Hessian and same-observation score product
(T23(i)--(v), Appendix E, p. 576). Derivatives are coordinate partials of
these smooth functions, so gradient/Hessian entries have their usual meaning. -/
theorem logistic_formula_correction {k : ℕ} (x : Vec k) (y : ℝ) (β : Vec k) :
    (0 < expit (dot x β) ∧ expit (dot x β) < 1) ∧
    (∀ a, HasDerivAt (fun t => logLikelihood x y (Function.update β a t))
      (logisticScore x y β a) (β a)) ∧
    logisticNegativeJacobian x y β =
      (expit (dot x β)*(1-expit (dot x β))) • outer x x ∧
    (logisticNegativeJacobian x y β).PosSemidef ∧
    outer (logisticScore x y β) (logisticScore x y β) =
      ((y-expit (dot x β))^2) • outer x x := by
  have hgradient (a : Fin k) : HasDerivAt
      (fun t => logLikelihood x y (Function.update β a t)) (logisticScore x y β a) (β a) := by
    have h := (scalar_logLikelihood_derivative y (dot x (Function.update β a (β a)))).comp
      (β a) (predictor_partial_derivative x β a)
    simpa only [logLikelihood,logisticScore,score,Pi.smul_apply,smul_eq_mul,
      Function.update_eq_self,Function.comp_def] using h
  have hj : logisticNegativeJacobian x y β =
      (expit (dot x β)*(1-expit (dot x β))) • outer x x := by
    ext a b
    have hdot := predictor_partial_derivative x β b
    have hexp := (expit_hasDerivAt (dot x (Function.update β b (β b)))).comp (β b) hdot
    have h := ((hasDerivAt_const (β b) y).sub hexp).mul_const (x a)
    have hpsi : HasDerivAt (fun t => logisticScore x y (Function.update β b t) a)
        (-(expit (dot x β)*(1-expit (dot x β))*x b)*x a) (β b) := by
      simpa only [logisticScore,score,Pi.smul_apply,smul_eq_mul,Function.update_eq_self,
        zero_sub,Pi.sub_apply,Function.comp_def] using h
    simp only [logisticNegativeJacobian,Matrix.smul_apply,smul_eq_mul,outer, Matrix.of_apply,hpsi.deriv]
    ring
  refine ⟨expit_bounds _,hgradient,hj,?_,?_⟩
  · rw [hj]
    exact (outer_positive_semidefinite x).smul
      (mul_nonneg (expit_bounds _).1.le (sub_nonneg.mpr (expit_bounds _).2.le))
  · simpa only [logisticScore,pow_two] using score_product x x (y-expit (dot x β)) (y-expit (dot x β))


/-- Summing the corrected one-observation logistic Jacobian and score
outer products gives X'MX and the diagonal score meat (T23(v), p. 576). -/
theorem logistic_summed_formulas {E : Type*} [Fintype E] {k : ℕ}
    (X : E → Vec k) (Y : E → ℝ) (β : Vec k) :
    (∑ d, logisticNegativeJacobian (X d) (Y d) β) = logisticBread X β ∧
    (∑ d, outer (logisticScore (X d) (Y d) β) (logisticScore (X d) (Y d) β)) =
      ∑ d, ((Y d-expit (dot (X d) β))^2) • outer (X d) (X d) := by
  constructor
  · unfold logisticBread
    apply Finset.sum_congr rfl
    intro d hd
    exact (logistic_formula_correction (X d) (Y d) β).2.2.1
  · apply Finset.sum_congr rfl
    intro d hd
    simpa only [logisticScore,pow_two] using score_product (X d) (X d)
      (Y d-expit (dot (X d) β)) (Y d-expit (dot (X d) β))


/-- D=binom(N,2) is the cardinality of the unordered non-self dyads
(p. 566; finite count used in T4 and T21). -/
theorem number_of_dyads (N : ℕ) : Fintype.card (Dyad N) = N.choose 2 := by
  simp [Dyad,dyads,Finset.card_powersetCard]

/-- A real symmetric two-by-two matrix with positive leading entry and
determinant is positive definite, used to certify the T1/T13 matrices. -/
theorem positive_definite_two (a b c : ℝ) (ha : 0 < a) (hd : 0 < a*c-b^2) :
    (!![a,b;b,c] : Mat 2).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · simp [Matrix.IsHermitian,funext_iff, ← Matrix.ext_iff,Fin.forall_fin_succ]
  · intro x hx
    have hq : 0 < a*(x 0)^2+2*b*x 0*x 1+c*(x 1)^2 := by
      by_cases hv : x 1=0
      · have hu : x 0 ≠ 0 := by
          intro hu
          apply hx
          ext i
          fin_cases i <;> simp [hu,hv]
        simpa [hv] using mul_pos ha (sq_pos_of_ne_zero hu)
      · have he : a*(a*(x 0)^2+2*b*x 0*x 1+c*(x 1)^2) =
            (a*x 0+b*x 1)^2+(a*c-b^2)*(x 1)^2 := by ring
        have hp : 0 < a*(a*(x 0)^2+2*b*x 0*x 1+c*(x 1)^2) := by
          rw [he]
          exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hd (sq_pos_of_ne_zero hv))
        exact (mul_pos_iff_of_pos_left ha).mp hp
    convert hq using 1 <;>
      simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,pow_two,mul_add,add_mul] <;> ring

/-- The rational matrices Gamma and V_* in the nonlinear uniform witness
are positive definite (T1(c),(d)). This does not identify their probability
moments. -/
theorem nonlinear_matrices_positive : nonlinearGamma.PosDef ∧ nonlinearVstar.PosDef := by
  constructor
  · exact positive_definite_two _ _ _ (by norm_num) (by norm_num)
  · exact positive_definite_two _ _ _ (by norm_num) (by norm_num)

/-- Both covariance matrices in the T13 logistic witness are positive
definite, despite disagreeing (T13(d), Appendix E, p. 576). -/
theorem logistic_covariances_positive :
    logitHinv.PosDef ∧ (!![38/25,-64/175;-64/175,192/1225] : Mat 2).PosDef := by
  constructor
  · exact positive_definite_two _ _ _ (by norm_num) (by norm_num)
  · exact positive_definite_two _ _ _ (by norm_num) (by norm_num)


/-- A symmetric bread preserves PSD Gram terms under P M P
(T18(i), the corrected variance-estimator structure, p. 567). -/
theorem sandwich_positive_semidefinite {k : ℕ} (P M : Mat k)
    (hP : P.transpose=P) (hM : M.PosSemidef) : (sandwich P M).PosSemidef := by
  have hp : P.conjTranspose=P := by
    ext i j
    have h := congrArg (fun A : Mat k => A i j) hP
    simpa only [Matrix.conjTranspose_apply,Matrix.transpose_apply,star_trivial] using h
  simpa only [sandwich,hp] using hM.mul_mul_conjTranspose_same P

/-- The equation (3) sandwich is a difference of two PSD matrices when
its bread is symmetric (T18(i), p. 567); the difference may have negative
entries even with full-rank OLS, as the finite certificate demonstrates. -/
theorem sandwich_difference_of_grams {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (s : E → Finset V)
    (hs : ∀ d, (s d).card=2) (hi : Function.Injective s)
    {k : ℕ} (q : E → Vec k) (P : Mat k) (hP : P.transpose=P) :
    sandwich P (meat s q) =
      sandwich P (∑ i,outer (unitScore s q i) (unitScore s q i))-sandwich P (dyadMeat q) ∧
    (sandwich P (∑ i,outer (unitScore s q i) (unitScore s q i))).PosSemidef ∧
    (sandwich P (dyadMeat q)).PosSemidef := by
  refine ⟨?_,sandwich_positive_semidefinite _ _ hP (score_gram_terms_psd s q).1,
    sandwich_positive_semidefinite _ _ hP (score_gram_terms_psd s q).2⟩
  rw [overlap_meat_identity s hs hi q]
  simp only [sandwich,Matrix.mul_sub,Matrix.sub_mul]

end AronowAudit.P018

