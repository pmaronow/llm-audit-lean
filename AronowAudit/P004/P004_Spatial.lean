import Mathlib.Tactic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Convex.Hull

/-!
P004: Wang, Samii, Chang and Aronow (2025), pp. 744–768, and Supplement A.
All randomness below is the assignment design.
-/

namespace AronowAudit.P004

open scoped BigOperators Matrix Classical
open MeasureTheory Filter
noncomputable section

set_option maxHeartbeats 1000000

/-- “The ordered vector ... Z ≡ (Z₁,...,Z_N)” (p. 747): Boolean assignments. -/
abbrev Assignment (N : ℕ) := Fin N → Bool

/-- The numeric indicator of treatment, eq. (13), p. 754. -/
def bit (a : Bool) : ℝ := if a then 1 else 0

/-- C1/C6: independent, possibly unequal Bernoulli coins (pp. 751, 758). -/
def coin (p : ℝ) (a : Bool) : ℝ := if a then p else 1 - p

/-- “The experimental design ... a probability distribution” (p. 747).
This is its product probability at the complete assignment z. -/
def designWeight {N : ℕ} (p : Fin N → ℝ) (z : Assignment N) : ℝ :=
  ∏ i, coin (p i) (z i)

/-- “The only source of stochastic variation is from Z” (p. 748).
Expectation over all 2^N assignments, with their actual product weights. -/
def expect {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) : ℝ :=
  ∑ z, designWeight p z * X z

/-- Design probability of an event; Sections 5 and 6.3, pp. 754–758. -/
def prob {N : ℕ} (p : Fin N → ℝ) (A : Assignment N → Prop) : ℝ :=
  expect p (fun z => if A z then 1 else 0)

/-- Design covariance; Supplement A pp. 2–5. -/
def cov {N : ℕ} (p : Fin N → ℝ) (X Y : Assignment N → ℝ) : ℝ :=
  expect p (fun z => X z * Y z) - expect p X * expect p Y

/-- Design variance; Supplement A pp. 2–5. -/
def variance {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) : ℝ := cov p X X

/-- “μᵢ(Y(z);Ω_d)” (eqs. (2)–(3), p. 747), realized circle averages tabulated
at a fixed band. SpatialPopulation below supplies the spatial realization. -/
abbrev CircleTable (N : ℕ) := Fin N → Assignment N → ℝ

/-- “μᵢ(z;d,η)=E_{Z_{−i}}[μᵢ(Y(z,Z_{−i});d)]” (eq. (5), p. 749).
Under independent Bernoulli coins with 0 < pⱼ < 1, this equals
E[μᵢ(Y;d) | Zᵢ=a]. The expression is defined for arbitrary real weights; some
algebraic identities below need weaker assumptions and do not assert a
conditional-probability interpretation. -/
def marginal {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (i : Fin N)
    (a : Bool) : ℝ :=
  expect p (fun z => if z i = a then R i z else 0) / coin (p i) a

/-- E[X | Zᵢ=a,Zⱼ=b] for distinct i,j; Supplement A p. 1. -/
def pairMarginal {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ)
    (i j : Fin N) (a b : Bool) : ℝ :=
  expect p (fun z => if z i = a ∧ z j = b then X z else 0) /
    (coin (p i) a * coin (p j) b)

/-- “τᵢ(d;η)=μᵢ(1;d,η)−μᵢ(0;d,η)” (eq. (8), p. 750). -/
def nodeEffect {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (i : Fin N) : ℝ :=
  marginal p R i true - marginal p R i false

/-- “AME(d;η)=1/N ∑ᵢ τᵢ(d;η)” (eq. (9), p. 750). -/
def ame {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) : ℝ :=
  (∑ i, nodeEffect p R i) / N

/-- Population arm means μ̄ᵃ, Supplement A p. 4. -/
def barMu {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (a : Bool) : ℝ :=
  (∑ i, marginal p R i a) / N

/-- “τ̂_HT(d)=∑ᵢZᵢμᵢ/(Np)−∑ᵢ(1−Zᵢ)μᵢ/(N(1−p))” (eq. (13), p. 754);
the heterogeneous version has the corrected
control weight, p. 759 and target T11. -/
def ht {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (z : Assignment N) : ℝ :=
  (∑ i, (bit (z i) * R i z / p i - (1 - bit (z i)) * R i z / (1 - p i))) / N

/-- The observational HT estimator as misprinted on p. 759. -/
def printedObsHT {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (z : Assignment N) : ℝ :=
  (∑ i, (bit (z i) * R i z / p i - (1 - bit (z i)) * R i z / p i)) / N

/-- “N₁=∑ᵢZᵢ and N₀=N−N₁” (p. 754, n corrected to N). -/
def armCount {N : ℕ} (z : Assignment N) (a : Bool) : ℝ :=
  ∑ i, if z i = a then (1 : ℝ) else 0

/-- Arm sample mean, Supplement A p. 7. Empty arms have mean zero,
as in Supplement A p. 9, footnote 2; Lean's real division has this value. -/
def armMean {N : ℕ} (R : CircleTable N) (z : Assignment N) (a : Bool) : ℝ :=
  (∑ i, if z i = a then R i z else 0) / armCount z a

/-- Hajek estimator, eq. (16), p. 754. -/
def hajek {N : ℕ} (R : CircleTable N) (z : Assignment N) : ℝ :=
  armMean R z true - armMean R z false

/-- Class τ̂(μ₁,μ₀;d), eq. (27), Supplement A p. 11, also (56), p. 26. -/
def augmented {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (z : Assignment N) : ℝ :=
  (∑ i, (g i true - g i false + bit (z i) * (R i z - g i true) / p i -
    (1 - bit (z i)) * (R i z - g i false) / (1 - p i))) / N

/-- Lemma A.3 corrected: the control denominator is N(1−p), T18. -/
def linearHajek {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) : Assignment N → ℝ :=
  augmented p R (fun _ a => barMu p R a)

/-- OLS residuals, p. 755, eq. (19). -/
def residual {N : ℕ} (R : CircleTable N) (z : Assignment N) (i : Fin N) : ℝ :=
  R i z - armMean R z (z i)

/-- Indicator (10), p. 752: j affects μᵢ, with diagonal included by definition. -/
def interferes {N : ℕ} (R : CircleTable N) (i j : Fin N) : Prop :=
  i = j ∨ ∃ z z' : Assignment N,
    (∀ k, k ≠ j → z k = z' k) ∧ R i z ≠ R i z'

/-- Shared interference indicator (11), p. 752. -/
def sharesSource {N : ℕ} (R : CircleTable N) (i j : Fin N) : Prop :=
  ∃ l, interferes R i l ∧ interferes R j l

/-- B_N(i;d)={j:dᵢⱼ≤h(d)}, eq. (12), p. 753. -/
def ball {N : ℕ} (dist : Fin N → Fin N → ℝ) (i : Fin N) (r : ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun j => dist i j ≤ r)

/-- cᵢ(d)=|B_N(i;d)| and c_N(d)=maxᵢ cᵢ(d), p. 753. -/
def maxDegree {N : ℕ} (B : Fin N → Finset (Fin N)) : ℕ :=
  Finset.univ.sup (fun i => (B i).card)

/-- C3 at a fixed band, p. 752: no shared source beyond the cutoff. -/
def LocalAt {N : ℕ} (R : CircleTable N) (dist : Fin N → Fin N → ℝ) (h : ℝ) : Prop :=
  ∀ i j, h < dist i j → ¬ sharesSource R i j

/-- “Each node i ... can be either a point or a collection of points”
(p. 747), with “potential outcomes at any point x ... for each value of z”.
Nondegenerate shell average (2) on a general metric space.
The same ζ is reused at every node; it need not be area measure. -/
structure SpatialPopulation (N : ℕ) (X : Type*) [MetricSpace X] [MeasurableSpace X] where
  node : Fin N → Set X
  node_nonempty : ∀ i, (node i).Nonempty
  zeta : Measure X
  outcome : X → Assignment N → ℝ
  bands : ℝ → Set ℝ

/-- dᵢ(x), the distance to an intervention node, p. 747. Metric.infDist
represents the printed minimum when attained (in particular for compact nodes). -/
def nodeDistance {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i : Fin N) (x : X) : ℝ := Metric.infDist x (P.node i)

/-- dᵢⱼ, the distance between intervention nodes, p. 752 fn. 3. The
infimum equals the printed minimum whenever the minimum is attained. -/
def nodeSeparation {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i j : Fin N) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ P.node i, ∃ y ∈ P.node j, dist x y = r}

/-- The region {x:dᵢ(x)∈Ω_d} in eq. (2), p. 747. -/
def region {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i : Fin N) (d : ℝ) : Set X :=
  {x | nodeDistance P i x ∈ P.bands d}

/-- “μᵢ(Y(z);Ω_d)=∫_{dᵢ(x)∈Ω_d}Yₓ(z)dζ / ∫_{dᵢ(x)∈Ω_d}dζ”
(eq. (2), p. 747), with the actual numerator and finite denominator. -/
def circleAverage {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (d : ℝ) : CircleTable N :=
  fun i z => (∫ x in region P i d, P.outcome x z ∂P.zeta) /
    (P.zeta (region P i d)).toReal

/-- Regularity implicit in “average” (2): measurable regions, positive finite
mass, and integrable potential outcomes. This excludes zero-measure circles. -/
def WellDefined {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (d : ℝ) : Prop :=
  ∀ i, MeasurableSet (region P i d) ∧ 0 < P.zeta (region P i d) ∧
    P.zeta (region P i d) < ⊤ ∧ ∀ z, IntegrableOn (fun x => P.outcome x z) (region P i d) P.zeta

/-- Convergence in probability, with the sample-size-specific design law. -/
def InProb (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun N => prob (p N) (fun z => ε < |U N z|)) atTop (nhds 0)

/-- U_N=O_p(r_N) as N tends to infinity, using eventual tightness bounds. -/
def BigOp (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) (r : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N in atTop, prob (p N) (fun z => C * |r N| < |U N z|) < ε

/-- Convergence of U_N/r_N to zero in probability. This expresses U_N=o_p(r_N)
when r_N is eventually nonzero. At zero rate values, Lean division returns zero
and imposes no condition on U_N. -/
def LittleOp (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) (r : ℕ → ℝ) : Prop :=
  InProb p (fun N z => U N z / r N)

/-- N(0,1), p. 754, using Mathlib's genuine Gaussian measure. -/
def normalCDF (x : ℝ) : ℝ := (ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal

/-- Standard normal quantile, pp. 755–756: inverse of the actual Gaussian CDF. -/
def normalQuantile (a : ℝ) : ℝ := sInf {x : ℝ | a ≤ normalCDF x}

/-- Convergence in distribution to N(0,1): CDF convergence at every real x,
all of which are continuity points of the Gaussian law. -/
def NormalLimit (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) : Prop :=
  ∀ x : ℝ, Tendsto (fun N => prob (p N) (fun z => U N z ≤ x)) atTop (nhds (normalCDF x))

/-- “Uniformly bounded below for all large N” in Propositions 2–4 (p. 754). -/
def Nondegenerate (V : ℕ → ℝ) : Prop :=
  ∃ v : ℝ, 0 < v ∧ ∀ᶠ N : ℕ in atTop, v ≤ (N : ℝ) * V N

/-- liminf coverage ≥1−α; corrected statements T2, T8 and T28. -/
def LiminfAtLeast (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, a-ε ≤ u N

/-- “liminf ... Prob ... ≥1−α”, corrected coverage in T2, T8 and T28;
expressed using the explicit eventual lower-bound predicate. -/
def Conservative (coverage : ℕ → ℝ) (α : ℝ) : Prop :=
  LiminfAtLeast coverage (1-α)

/-- The stronger printed “lim ... ≥1−α”, p. 755: existence is retained. -/
def PrintedCoverage (coverage : ℕ → ℝ) (α : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto coverage atTop (nhds L) ∧ 1 - α ≤ L

/- Finite design identities. -/

/-- Product Bernoulli weights sum to one; C1/C6, pp. 751 and 758. -/
theorem design_normalized {N : ℕ} (p : Fin N → ℝ) :
    (∑ z : Assignment N, designWeight p z) = 1 := by
  simp only [designWeight]
  rw [← Fintype.prod_sum]
  simp [coin, Fintype.sum_bool]

/-- Finite design expectation is linear in subtraction; the expectation
operator used throughout Supplement A, pp. 1–5. -/
theorem expect_sub {N : ℕ} (p : Fin N → ℝ) (X Y : Assignment N → ℝ) :
    expect p (fun z => X z-Y z) = expect p X-expect p Y := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

/-- Finite design expectation is linear in addition; Supplement A p. 1. -/
theorem expect_add {N : ℕ} (p : Fin N → ℝ) (X Y : Assignment N → ℝ) :
    expect p (fun z => X z+Y z) = expect p X+expect p Y := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

/-- Finite expectation commutes with fixed finite sums (Supplement A p. 1). -/
theorem expect_sum {N : ℕ} {A : Type*} [Fintype A] (p : Fin N → ℝ)
    (X : A → Assignment N → ℝ) :
    expect p (fun z => ∑ a, X a z) = ∑ a, expect p (X a) := by
  unfold expect
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- Division by a fixed scalar commutes with finite expectation;
the normalizing factors in eq. (13), p. 754. -/
theorem expect_div {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) (c : ℝ) :
    expect p (fun z => X z/c) = expect p X/c := by
  simp only [expect, ← mul_div_assoc, Finset.sum_div]

/-- A fixed potential-outcome constant has its own expectation (p. 748). -/
theorem expect_const {N : ℕ} (p : Fin N → ℝ) (c : ℝ) :
    expect p (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, design_normalized, one_mul]

/-- A fixed scalar commutes with finite design expectation (Supplement A p. 1). -/
theorem expect_mul {N : ℕ} (p : Fin N → ℝ) (c : ℝ) (X : Assignment N → ℝ) :
    expect p (fun z => c*X z) = c*expect p X := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Lemma A.1, Supplement A p. 1: E[Zᵢμᵢ]=pᵢμᵢ(1),
and its control analogue. No interference restriction is used. -/
theorem bernoulli_selection {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (i : Fin N) (a : Bool) (hp : coin (p i) a ≠ 0) :
    expect p (fun z => if z i = a then R i z else 0) = coin (p i) a * marginal p R i a := by
  unfold marginal
  field_simp

/-- Proposition 1, eq. (14), p. 754, and corrected observational HT (T11a):
under independent Bernoulli assignment, HT is exactly unbiased for AME. -/
theorem ht_unbiased {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (hp : ∀ i, 0 < p i ∧ p i < 1) : expect p (ht p R) = ame p R := by
  have hx : ∀ z, ht p R z =
      (∑ i, ((if z i = true then R i z else 0)/p i -
        (if z i = false then R i z else 0)/(1-p i)))/N := by
    intro z
    unfold ht
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases h : z i <;> simp [bit, h]
  rw [funext hx, expect_div, expect_sum]
  simp_rw [expect_sub, expect_div]
  rfl

/-- Joining the forced own treatment to the vector Z_{−i} in eq. (5),
p. 749. This auxiliary representation enumerates all other assignments. -/
def joinAssignment {N : ℕ} (i : Fin N) (a : Bool)
    (u : {j : Fin N // j ≠ i} → Bool) : Assignment N :=
  fun j => if h : j = i then a else u ⟨j,h⟩

/-- A complete assignment is exactly its own coordinate and all other
coordinates, eq. (5) p. 749; no assignments are removed from the design. -/
def splitAssignment {N : ℕ} (i : Fin N) :
    Assignment N ≃ Bool × ({j : Fin N // j ≠ i} → Bool) where
  toFun z := (z i, fun j => z j)
  invFun au := joinAssignment i au.1 au.2
  left_inv z := by
    funext j
    by_cases h : j = i
    · subst j; simp [joinAssignment]
    · simp [joinAssignment, h]
  right_inv au := by
    rcases au with ⟨a,u⟩
    apply Prod.ext
    · simp [joinAssignment]
    · funext j; simp [joinAssignment, j.property]

/-- C1/C6's product law factors into the own coin and the probability
of the other coordinates, as used in Supplement A Lemma A.1. -/
theorem join_design_weight {N : ℕ} (p : Fin N → ℝ) (i : Fin N) (a : Bool)
    (u : {j : Fin N // j ≠ i} → Bool) :
    designWeight p (joinAssignment i a u) =
      coin (p i) a * ∏ j : {j : Fin N // j ≠ i}, coin (p j) (u j) := by
  unfold designWeight
  rw [← Finset.mul_prod_erase Finset.univ (fun j => coin (p j) (joinAssignment i a u j))
    (Finset.mem_univ i)]
  rw [Finset.prod_subtype (p := fun j : Fin N => j ≠ i) (F := inferInstance)
    (Finset.univ.erase i) (by intro j; simp) (fun j => coin (p j) (joinAssignment i a u j))]
  rw [show joinAssignment i a u i = a by simp [joinAssignment]]
  apply congrArg (fun t : ℝ => coin (p i) a*t)
  apply Finset.prod_congr rfl
  intro j _
  simp [joinAssignment, j.property]

/-- Exact finite marginalization by the product design, eq. (5) p. 749:
expectation is the sum over the own treatment and the unchanged other law. -/
theorem expect_split {N : ℕ} (p : Fin N → ℝ) (i : Fin N) (X : Assignment N → ℝ) :
    expect p X = ∑ a : Bool, coin (p i) a *
      ∑ u : {j : Fin N // j ≠ i} → Bool,
        (∏ j : {j : Fin N // j ≠ i}, coin (p j) (u j))*X (joinAssignment i a u) := by
  unfold expect
  rw [← (splitAssignment i).symm.sum_comp (fun z => designWeight p z*X z), Fintype.sum_prod_type]
  change (∑ a : Bool, ∑ u : {j : Fin N // j ≠ i} → Bool,
    designWeight p (joinAssignment i a u)*X (joinAssignment i a u)) = _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [join_design_weight]
  ring

/-- T39, eq. (5) is indeed marginalization over Z_{−i}, not a changed
estimand: the conditional finite sum equals forced-coordinate expectation. -/
theorem marginal_is_marginalization {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (i : Fin N) (a : Bool) (hp : ∀ j, 0 < p j ∧ p j < 1) :
    marginal p R i a = expect p (fun z => R i (Function.update z i a)) := by
  have hj : ∀ b u, joinAssignment i b u i = b := by intro b u; simp [joinAssignment]
  have hu : ∀ b u, Function.update (joinAssignment i b u) i a = joinAssignment i a u := by
    intro b u
    funext j
    by_cases h : j = i
    · subst j; simp [joinAssignment]
    · simp [joinAssignment, h]
  have hpi : p i ≠ 0 := ne_of_gt (hp i).1
  have hqi : 1-p i ≠ 0 := ne_of_gt (sub_pos.mpr (hp i).2)
  unfold marginal
  rw [expect_split p i, expect_split p i]
  simp_rw [hj, hu]
  cases a <;> simp [Fintype.sum_bool, coin, hpi, hqi]
    <;> ring

/-- Lemma A.1 C1.1, Supplement A p. 1, for every function f and every
positive integer k: E[Zᵢᵏ f(Z)]=pᵢ E[f(1,Z_{−i})]. -/
theorem bernoulli_positive_power {N : ℕ} (p : Fin N → ℝ)
    (f : Assignment N → ℝ) (i : Fin N) (k : ℕ) (hk : 0 < k)
    (hp : ∀ j, 0 < p j ∧ p j < 1) :
    expect p (fun z => (bit (z i))^k*f z) =
      p i*expect p (fun z => f (Function.update z i true)) := by
  have hx : (fun z => (bit (z i))^k*f z) =
      fun z => if z i = true then f z else 0 := by
    funext z
    cases h : z i <;> simp [bit, h, Nat.ne_of_gt hk]
  rw [hx]
  rw [bernoulli_selection p (fun _ z => f z) i true (by simpa [coin] using ne_of_gt (hp i).1),
    marginal_is_marginalization p (fun _ z => f z) i true hp]
  simp [coin]

/-- Lemma A.1 C1.2, Supplement A p. 1, for distinct i,j and positive k,l:
E[ZᵢᵏZⱼˡ f(Z)]=pᵢpⱼ E[f(1ᵢ,1ⱼ,Z_{−(i,j)})]. -/
theorem bernoulli_pair_positive_powers {N : ℕ} (p : Fin N → ℝ)
    (f : Assignment N → ℝ) (i j : Fin N) (hij : i ≠ j)
    (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (hp : ∀ a, 0 < p a ∧ p a < 1) :
    expect p (fun z => (bit (z i))^k*(bit (z j))^l*f z) =
      p i*p j*expect p (fun z => f (Function.update (Function.update z j true) i true)) := by
  have hx : (fun z => (bit (z i))^k*(bit (z j))^l*f z) =
      fun z => (bit (z i))^k*((bit (z j))^l*f z) := by
    funext z
    ring
  rw [hx, bernoulli_positive_power p _ i k hk hp]
  have hu : (fun z => (bit (Function.update z i true j))^l*f (Function.update z i true)) =
      fun z => (bit (z j))^l*f (Function.update z i true) := by
    funext z
    simp [hij, hij.symm]
  rw [hu, bernoulli_positive_power p (fun z => f (Function.update z i true)) j l hl hp]
  exact (mul_assoc _ _ _).symm

/-- T6(c), pp. 763–764: multiplying a statistic by c>0 preserves
every comparison in its two-sided randomization p-value. -/
theorem randomization_scaling (c s t : ℝ) (hc : 0 < c) :
    |c * s| ≥ |c * t| ↔ |s| ≥ |t| := by
  simp only [abs_mul, abs_of_pos hc]
  exact mul_le_mul_iff_right₀ hc

/-- T2(b), corrected score residuals: their arm contrast is δ, and
their inverse-probability sum is L; exact at every node. -/
theorem corrected_fits (p δ L : ℝ) (hp : p ≠ 0) (hq : 1 - p ≠ 0) :
    let f1 := p * δ + p * (1-p) * L
    let f0 := -(1-p) * δ + p * (1-p) * L
    f1 - f0 = δ ∧ f1 / p + f0 / (1-p) = L := by
  dsimp
  constructor
  · ring
  · field_simp
    <;> ring

/-- T2(b), exact augmentation identity: corrected residuals subtract
(Zᵢ−pᵢ)Lᵢ from the true-propensity HT summand, for each assignment. -/
theorem corrected_score_identity (z : Bool) (p μ δ L : ℝ)
    (hp : p ≠ 0) (hq : 1-p ≠ 0) :
    let f1 := p * δ + p * (1-p) * L
    let f0 := -(1-p) * δ + p * (1-p) * L
    δ + bit z * (μ-f1)/p - (1-bit z)*(μ-f0)/(1-p) =
      bit z * μ/p - (1-bit z)*μ/(1-p) - (bit z-p)*L := by
  dsimp
  cases z <;> simp only [bit, Bool.false_eq_true, if_false, if_true]
  all_goals field_simp; ring

/- Corrected observational objects, defined once. -/

/-- Euclidean dot product of two finite real vectors. -/
def dot {k : ℕ} (u v : Fin k → ℝ) : ℝ := ∑ j, u j * v j
/-- “p(Oᵢ|θ)=exp(Oᵢ′θ)/(1+exp(Oᵢ′θ))”, Supplement A p. 14;
the scalar logistic function applied to Oᵢ′θ. -/
def logistic (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t)

/-- Supplement A.6 “C 1”: fixed dimension, bounded fixed confounders,
fixed compact parameter space, positive Gram bound, and the actual constrained MLE.
The interior condition is supplied separately in corrected theorems. -/
def LogisticConditions {k : ℕ} (O : ∀ N, Fin N → Fin k → ℝ)
    (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ) : Prop :=
  IsCompact Θ ∧ θ₀ ∈ Θ ∧
  (∃ U : ℝ, ∀ N i j, |O N i j| ≤ U) ∧
  (∃ c : ℝ, 0 < c ∧ ∀ᶠ N in atTop, ∀ v : Fin k → ℝ,
    c * (∑ j, (v j)^2) ≤ (∑ i, (dot (O N i) v)^2) / N) ∧
  (∀ N z, θhat N z ∈ Θ ∧ ∀ θ ∈ Θ,
    (∑ i, (bit (z i) * dot (O N i) θ - Real.log (1 + Real.exp (dot (O N i) θ)))) ≤
    (∑ i, (bit (z i) * dot (O N i) (θhat N z) -
      Real.log (1 + Real.exp (dot (O N i) (θhat N z))))))

/-- pᵢ=p(Oᵢ|θ₀), C6 and Supplement A p. 14. -/
def propensities {N k : ℕ} (O : Fin N → Fin k → ℝ) (θ : Fin k → ℝ) : Fin N → ℝ :=
  fun i => logistic (dot (O i) θ)

/-- H_N=N⁻¹∑pᵢ(1−pᵢ)OᵢOᵢ', Supplement A p. 14. -/
def information {N k : ℕ} (p : Fin N → ℝ) (O : Fin N → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun a b => (∑ i, p i * (1-p i) * O i a * O i b) / N

/-- β_{a,N}, population projections in Supplement A p. 14. -/
def beta {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (a : Bool) : Fin k → ℝ :=
  (information p O)⁻¹ *ᵥ (fun j =>
    (∑ i, marginal p R i a * p i * (1-p i) * O i j) / N)

/-- Corrected D_N and γ_N=H_N⁻¹D_N, T2. -/
def scoreGamma {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) : Fin k → ℝ :=
  (information p O)⁻¹ *ᵥ (fun j =>
    (∑ i, ((1-p i)*marginal p R i true + p i*marginal p R i false)*O i j) / N)

/-- Printed residual fits Oᵢ'β_{a,N}, Supplement A pp. 14–15. -/
def printedFits {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (i : Fin N) (a : Bool) : ℝ := dot (O i) (beta p R O a)

/-- Corrected fits fᵢ₁=pᵢδᵢ+pᵢ(1−pᵢ)Lᵢ and
fᵢ₀=−(1−pᵢ)δᵢ+pᵢ(1−pᵢ)Lᵢ, T2. -/
def scoreFits {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (i : Fin N) (a : Bool) : ℝ :=
  let δ := printedFits p R O i true - printedFits p R O i false
  let L := dot (O i) (scoreGamma p R O)
  if a then p i * δ + p i * (1-p i) * L
  else -(1-p i) * δ + p i * (1-p i) * L

/-- Tᵢ, raw residual inverse-propensity contrast (T2, T4, T22). -/
def residualContrast {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i : Fin N) (z : Assignment N) : ℝ :=
  bit (z i) * (R i z - g i true) / p i -
  (1-bit (z i)) * (R i z - g i false) / (1-p i)

/-- Mean residual effect hᵢ=τᵢ−(gᵢ₁−gᵢ₀), T2/T22. -/
def residualEffect {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i : Fin N) : ℝ :=
  nodeEffect p R i - (g i true - g i false)

/-- The mean of a deterministic-fit residual contrast is its marginalized
residual effect, Supplement A pp. 5, 15; T2, T21, T22 and T25. -/
theorem residualContrast_mean {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i : Fin N) (hp : ∀ j, 0 < p j ∧ p j < 1) :
    expect p (residualContrast p R g i) = residualEffect p R g i := by
  have hm : ∀ a, marginal p (fun j z => R j z-g j a) i a =
      marginal p R i a-g i a := by
    intro a
    rw [marginal_is_marginalization p _ i a hp,
      marginal_is_marginalization p R i a hp]
    rw [expect_sub, expect_const]
  have hx : residualContrast p R g i = fun z =>
      (if z i = true then R i z-g i true else 0)/p i -
        (if z i = false then R i z-g i false else 0)/(1-p i) := by
    funext z
    cases h : z i <;> simp [residualContrast, bit, h]
  rw [hx, expect_sub, expect_div, expect_div]
  change marginal p (fun j z => R j z-g j true) i true -
    marginal p (fun j z => R j z-g j false) i false = residualEffect p R g i
  rw [hm, hm]
  unfold residualEffect nodeEffect
  ring

/-- The two marginalized population arm means differ by AME,
eqs. (8)–(9), p. 750, and Supplement A p. 4. -/
theorem barMu_difference {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) :
    barMu p R true-barMu p R false = ame p R := by
  unfold barMu ame nodeEffect
  rw [← sub_div, ← Finset.sum_sub_distrib]

/-- The deterministic augmented estimator remains unbiased for AME,
the class in Supplement A eq. (27), p. 11, and T2's corrected score fits. -/
theorem augmented_unbiased {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) :
    expect p (augmented p R g) = ame p R := by
  have hx : augmented p R g = fun z =>
      (∑ i, ((g i true-g i false)+residualContrast p R g i z))/N := by
    funext z
    unfold augmented residualContrast
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hx, expect_div, expect_sum]
  simp_rw [expect_add, expect_const, residualContrast_mean p R g _ hp]
  unfold ame residualEffect
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Signed two-arm product, lines (4)–(5), Lemma A.4, Supplement A p. 5. -/
def armSign (a : Bool) : ℝ := if a then 1 else -1

/-- Uncentered local second-moment variance limit, with both pair signs,
the correct j index and control denominator (T2c, T22, T33b). -/
def secondMomentBound {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  ((∑ i, (marginal p (fun i z => (R i z - g i true)^2) i true / p i +
    marginal p (fun i z => (R i z - g i false)^2) i false / (1-p i))) +
    ∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool,
      armSign a * armSign b * pairMarginal p
        (fun z => (R i z - g i a)*(R j z - g j b)) i j a b) / (N : ℝ)^2

/-- Intended homophily Q, Supplement A p. 14, with Oⱼ in the second fit.
For constant arm fits this is the article's C5. -/
def homophilyQ {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ B i, residualEffect p R g i * residualEffect p R g j) / N

/-- Literal “C 2” in Supplement A.6 uses i instead of j (T23). -/
def printedHomophilyQ {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ B i, residualEffect p R g i *
    (nodeEffect p R j - (g i true - g i false))) / N

/-- Oracle HAC W_H, T2(d), using local products of the corrected Tᵢ. -/
def oracleHAC {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : Assignment N) : ℝ :=
  (∑ i, ∑ j ∈ B i, residualContrast p R g i z * residualContrast p R g j z) / (N : ℝ)^2

/-- Corrected raw-residual SAH, T4, also oracle W_S of T2(d).
Each selected residual is inverse-propensity weighted once. -/
def rawSAH {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : Assignment N) : ℝ :=
  (∑ i, (B i).card * (bit (z i) * (R i z-g i true)^2 / (p i)^2 +
    (1-bit (z i)) * (R i z-g i false)^2 / (1-p i)^2)) / (N : ℝ)^2

/-- The printed, already weighted observational ε̂ᵢ, Supplement A p. 15,
with its undefined Oⱼ read as Oᵢ (T23). -/
def weightedEpsilon {N : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (z : Assignment N) (i : Fin N) : ℝ :=
  armCount z true / N * bit (z i) / phat i * (R i z-g i true) +
  armCount z false / N * (1-bit (z i)) / (1-phat i) * (R i z-g i false)

/-- Printed observational SAH, Supplement A p. 15: propensity weights
are applied to ε̂ᵢ a second time (T3/T36). -/
def printedSAH {N : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : Assignment N) : ℝ :=
  (∑ i, (B i).card * (bit (z i) * (weightedEpsilon phat R g z i)^2 / (phat i)^2 +
    (1-bit (z i)) * (weightedEpsilon phat R g z i)^2 / (1-phat i)^2)) / (N : ℝ)^2

/-- The scalar oracle SAH limit, corrected Proposition 2, Supplement A p. 9. -/
def sahLimit {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  (∑ i, (B i).card * (marginal p (fun i z => (R i z-g i true)^2) i true / p i +
    marginal p (fun i z => (R i z-g i false)^2) i false / (1-p i))) / (N : ℝ)^2

/-- X∈ℝ^{N×2} has rows (1,Zᵢ), eq. (19), p. 755. -/
def designMatrix {N : ℕ} (z : Assignment N) : Matrix (Fin N) (Fin 2) ℝ :=
  fun i a => if a = 0 then 1 else bit (z i)

/-- λᵢ=Zᵢ/N₁−(1−Zᵢ)/N₀, corrected A.7, T24. -/
def lambda {N : ℕ} (z : Assignment N) (i : Fin N) : ℝ :=
  bit (z i) / armCount z true - (1-bit (z i)) / armCount z false

/-- Corrected residual maker M=I−X(X'X)⁻¹X', Supplement A p. 17. -/
def residualMaker {N : ℕ} (z : Assignment N) : Matrix (Fin N) (Fin N) ℝ :=
  let X := designMatrix z
  1 - X * (X.transpose * X)⁻¹ * X.transpose

/-- Eq. (21), p. 756, using the actual N×N kernel and N residuals. -/
def sandwich {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let X := designMatrix z
  let A := (X.transpose * X)⁻¹
  A * (X.transpose * Matrix.of (fun i j => e i * e j * Q i j) * X) * A

/-- Scalar treatment entry e'D_λQD_λe, T7/T8/T24/T29. -/
def kernelVariance {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, lambda z i * lambda z j * e i * e j * Q i j

/-- The actual matrix “(N₁N₀/N) MD_λQD_λM” inside the traces
defining μ and ν, Supplement A p. 17 (T7/T8/T24). -/
def adjustmentMatrix {N : ℕ} (z : Assignment N)
    (Q : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (armCount z true * armCount z false / N) •
    (residualMaker z * Matrix.of (fun i j => lambda z i * lambda z j * Q i j) * residualMaker z)
/-- “μ=Trace(...)”, Supplement A p. 17, the trace of the actual
corrected adjustment matrix (T7, T8 and T24). -/
def adjustmentMu {N : ℕ} (z : Assignment N) (Q : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  Matrix.trace (adjustmentMatrix z Q)
/-- “ν=2Trace(...)”, Supplement A p. 17: twice the trace of the
square of the corrected adjustment matrix; empirical df=2μ²/ν. -/
def adjustmentNu {N : ℕ} (z : Assignment N) (Q : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  2 * Matrix.trace (adjustmentMatrix z Q * adjustmentMatrix z Q)

/-- Eigenvalue truncation K^PD=∑max(λᵢ,0)vᵢvᵢ', eq. (22), p. 756. -/
def spectralKernel {N : ℕ} (values : Fin N → ℝ)
    (vectors : Matrix (Fin N) (Fin N) ℝ) (trim : Bool) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ k, (if trim then max (values k) 0 else values k) * vectors i k * vectors j k

/-- Positive semidefinite order, p. 756: x'Qx≥0 for every real x. -/
def PSD {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ i j, Q i j = Q j i) ∧ ∀ x : Fin N → ℝ, 0 ≤ ∑ i, ∑ j, x i * Q i j * x j

/-- Safe cap V_PD/min(μ_PD,1), with raw PD when μ_PD≤0 (T8). -/
def cappedVariance (V μ : ℝ) : ℝ := if 0 < μ then V / min μ 1 else V

/-- T8(a), the numerical cap cannot reduce a nonnegative raw PD variance. -/
theorem capped_variance_ge (V μ : ℝ) (hV : 0 ≤ V) : V ≤ cappedVariance V μ := by
  unfold cappedVariance
  split_ifs with h
  · have hm : 0 < min μ 1 := lt_min h (by norm_num)
    apply (le_div_iff₀ hm).2
    exact mul_le_of_le_one_right hV (min_le_right _ _)
  · exact le_rfl


/-- C6's Bernoulli probabilities make every full-assignment weight nonnegative. -/
theorem design_weight_nonneg {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (z : Assignment N) : 0 ≤ designWeight p z := by
  apply Finset.prod_nonneg
  intro i _
  unfold coin
  split_ifs <;> have := hp i <;> linarith


/-- Expectations preserve pointwise order under C6, p. 758. -/
theorem expect_mono {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (X Y : Assignment N → ℝ) (h : ∀ z, X z ≤ Y z) : expect p X ≤ expect p Y := by
  apply Finset.sum_le_sum
  intro z _
  exact mul_le_mul_of_nonneg_left (h z) (design_weight_nonneg p hp z)


/-- Covariance is the expectation of centered products, Supplement A p. 9. -/
theorem cov_centered {N : ℕ} (p : Fin N → ℝ) (X Y : Assignment N → ℝ) :
    cov p X Y = expect p (fun z => (X z-expect p X)*(Y z-expect p Y)) := by
  have he : (fun z => (X z-expect p X)*(Y z-expect p Y)) =
      (fun z => X z*Y z-expect p Y*X z-expect p X*Y z+expect p X*expect p Y) := by
    funext z; ring
  rw [he, expect_add, expect_sub, expect_sub, expect_mul, expect_mul, expect_const]
  unfold cov
  ring


/-- Variance is nonnegative over the actual randomization law. -/
theorem variance_nonneg {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (X : Assignment N → ℝ) : 0 ≤ variance p X := by
  rw [variance, cov_centered]
  have h := expect_mono p hp (fun _ => 0) (fun z => (X z-expect p X)*(X z-expect p X))
    (fun z => mul_self_nonneg _)
  simpa [expect_const] using h


/-- Young's covariance bound used in the SAH derivation, Supplement A p. 9. -/
theorem cov_young {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (X Y : Assignment N → ℝ) : 2*cov p X Y ≤ variance p X+variance p Y := by
  have h := expect_mono p hp
    (fun z => 2*((X z-expect p X)*(Y z-expect p Y)))
    (fun z => (X z-expect p X)^2+(Y z-expect p Y)^2)
    (fun z => by nlinarith [sq_nonneg (X z-expect p X-(Y z-expect p Y))])
  rw [expect_mul, expect_add, ← cov_centered] at h
  simpa only [variance, pow_two, ← cov_centered] using h


/-- The second moment bounds variance, the diagonal step in the SAH proof. -/
theorem variance_le_second {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) :
    variance p X ≤ expect p (fun z => (X z)^2) := by
  unfold variance cov
  simp only [pow_two]
  nlinarith [sq_nonneg (expect p X)]


/-- Exact variance expansion for finite sums, Supplement A pp. 2–5. -/
theorem variance_sum {N : ℕ} {A : Type*} [Fintype A]
    (p : Fin N → ℝ) (X : A → Assignment N → ℝ) :
    variance p (fun z => ∑ i, X i z) = ∑ i, ∑ j, cov p (X i) (X j) := by
  unfold variance cov
  simp only [Finset.sum_mul, Finset.mul_sum, expect_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => expect p (fun z => X j z*X i z)),
    Finset.sum_comm (f := fun i j => expect p (X j)*expect p (X i))]


/-- A deterministic denominator scales design variance by its square. -/
theorem variance_div {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) (c : ℝ) :
    variance p (fun z => X z/c) = variance p X/c^2 := by
  have he : (fun z => X z/c*(X z/c)) = (fun z => (X z*X z)/c^2) := by
    funext z
    simp only [div_eq_mul_inv, inv_pow]
    ring
  unfold variance cov
  rw [he, expect_div, expect_div]
  simp only [div_eq_mul_inv, inv_pow]
  ring


/-- Symmetric neighbor sums count each node's variance by its degree, eq. (20). -/
theorem symmetric_neighbor_sum {A : Type*} [Fintype A] [DecidableEq A]
    (B : A → Finset A) (v : A → ℝ) (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j) :
    (∑ i, ∑ j ∈ B i, (v i+v j)) = 2*(∑ i, (B i).card*v i) := by
  have hc : (∑ i, ∑ j ∈ B i, v j) = ∑ i, (B i).card*v i := by
    have hr : ∀ i, (∑ j ∈ B i, v j) = ∑ j, if j ∈ B i then v j else 0 := by
      intro i
      rw [← Finset.sum_filter]
      simp
    simp_rw [hr]
    rw [Finset.sum_comm]
    simp_rw [hsymm]
    simp [← Finset.sum_filter]
  simp only [Finset.sum_add_distrib]
  rw [hc]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring


/-- T4(b): zero covariance outside a symmetric neighborhood gives the finite degree bound. -/
theorem finite_covariance_degree_bound {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (T : Fin N → Assignment N → ℝ)
    (B : Fin N → Finset (Fin N)) (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (houtside : ∀ i j, j ∉ B i → cov p (T i) (T j) = 0) :
    variance p (fun z => (∑ i, T i z)/N) ≤
      (∑ i, (B i).card*expect p (fun z => (T i z)^2))/(N : ℝ)^2 := by
  rw [variance_div, variance_sum]
  have hlocal : (∑ i, ∑ j, cov p (T i) (T j)) = ∑ i, ∑ j ∈ B i, cov p (T i) (T j) := by
    apply Finset.sum_congr rfl
    intro i _
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => houtside i j hj)
  rw [hlocal]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hy : 2*(∑ i, ∑ j ∈ B i, cov p (T i) (T j)) ≤
      ∑ i, ∑ j ∈ B i, (variance p (T i)+variance p (T j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact cov_young p hp (T i) (T j)
  rw [symmetric_neighbor_sum B (fun i => variance p (T i)) hsymm] at hy
  have hd : (∑ i, (B i).card*variance p (T i)) ≤
      ∑ i, (B i).card*expect p (fun z => (T i z)^2) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (variance_le_second p (T i)) (by positivity)
  linarith

/-- Selected-arm square moment, the diagonal term in corrected T4(b). -/
theorem residual_square_moment {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i : Fin N) (hp : 0 < p i ∧ p i < 1) :
    expect p (fun z => (residualContrast p R g i z)^2) =
      marginal p (fun i z => (R i z-g i true)^2) i true/p i +
      marginal p (fun i z => (R i z-g i false)^2) i false/(1-p i) := by
  have he : (fun z => (residualContrast p R g i z)^2) = (fun z =>
      (if z i = true then (R i z-g i true)^2 else 0)/(p i)^2 +
      (if z i = false then (R i z-g i false)^2 else 0)/(1-p i)^2) := by
    funext z
    cases h : z i <;> simp [residualContrast, bit, h, div_pow]
  rw [he, expect_add, expect_div, expect_div]
  simp only [marginal, coin, Bool.false_eq_true, if_false, if_true]
  field_simp


/-- Raw SAH is the degree-weighted sum of squared residual contrasts, T4. -/
theorem raw_sah_squares {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : Assignment N) :
    rawSAH p R B g z = (∑ i, (B i).card*(residualContrast p R g i z)^2)/(N : ℝ)^2 := by
  unfold rawSAH
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases h : z i <;> simp [residualContrast, bit, h, div_pow]


/-- T4(b), exact SAH bound for arbitrary deterministic arm fits;
only zero covariance outside the closed symmetric neighborhoods is assumed. -/
theorem raw_sah_bound {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ)
    (hN : 0 < N) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (hself : ∀ i, i ∈ B i) (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (houtside : ∀ i j, j ∉ B i →
      cov p (residualContrast p R g i) (residualContrast p R g j) = 0) :
    variance p (fun z => (∑ i, residualContrast p R g i z) / N) ≤ sahLimit p R B g ∧
    sahLimit p R B g = expect p (rawSAH p R B g) := by
  have hm : (∑ i, (B i).card*expect p (fun z => (residualContrast p R g i z)^2))/(N : ℝ)^2 =
      sahLimit p R B g := by
    simp_rw [residual_square_moment p R g _ (hp _)]
    rfl
  constructor
  · rw [← hm]
    exact finite_covariance_degree_bound p hp (residualContrast p R g) B hsymm houtside
  · rw [← hm]
    have he : rawSAH p R B g = fun z => (∑ i, (B i).card*(residualContrast p R g i z)^2)/(N : ℝ)^2 := by
      funext z
      exact raw_sah_squares p R B g z
    rw [he, expect_div, expect_sum]
    simp_rw [expect_mul]


/-- T4(a), corrected observational SAH uses N₁²,N₀² when ε̂ is already weighted;
the printed expression has fourth powers of fitted propensities. -/
theorem sah_weighting_identity {N : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : Assignment N)
    (hN : 0 < N) (h1 : 0 < armCount z true) (h0 : 0 < armCount z false)
    (hp : ∀ i, 0 < phat i ∧ phat i < 1) :
    rawSAH phat R B g z =
      (∑ i, bit (z i) * (B i).card * (weightedEpsilon phat R g z i)^2) / (armCount z true)^2 +
      (∑ i, (1-bit (z i)) * (B i).card * (weightedEpsilon phat R g z i)^2) / (armCount z false)^2 ∧
    printedSAH phat R B g z =
      (∑ i, (B i).card * ((armCount z true / N)^2 * bit (z i) * (R i z-g i true)^2 / (phat i)^4 +
        (armCount z false / N)^2 * (1-bit (z i)) * (R i z-g i false)^2 / (1-phat i)^4)) / (N : ℝ)^2 := by
  have hn : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  have h1n : armCount z true ≠ 0 := ne_of_gt h1
  have h0n : armCount z false ≠ 0 := ne_of_gt h0
  have he : ∀ i,
      ((B i).card * (bit (z i) * (R i z-g i true)^2 / (phat i)^2 +
        (1-bit (z i)) * (R i z-g i false)^2 / (1-phat i)^2))/(N : ℝ)^2 =
      bit (z i)*(B i).card*(weightedEpsilon phat R g z i)^2/(armCount z true)^2 +
        (1-bit (z i))*(B i).card*(weightedEpsilon phat R g z i)^2/(armCount z false)^2 := by
    intro i
    have hpi : phat i ≠ 0 := ne_of_gt (hp i).1
    have hqi : 1-phat i ≠ 0 := ne_of_gt (sub_pos.mpr (hp i).2)
    cases hi : z i <;> simp [weightedEpsilon, bit, hi]
      <;> field_simp [hn, h1n, h0n, hpi, hqi] <;> ring
  constructor
  · unfold rawSAH
    rw [Finset.sum_div]
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
  · unfold printedSAH
    apply congrArg (fun s : ℝ => s/(N : ℝ)^2)
    apply Finset.sum_congr rfl
    intro i _
    have hpi : phat i ≠ 0 := ne_of_gt (hp i).1
    have hqi : 1-phat i ≠ 0 := ne_of_gt (sub_pos.mpr (hp i).2)
    cases hi : z i <;>
      simp only [weightedEpsilon, bit, hi, Bool.false_eq_true, if_false, if_true,
        mul_zero, zero_mul, mul_one, one_mul, sub_zero, sub_self, zero_add, add_zero,
        zero_div, div_eq_mul_inv, ← inv_pow] <;> ring

/-- T2(b), the corrected first-order form is exactly true HT minus the
logistic score correction, and has expectation AME. -/
theorem corrected_ipw_finite {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) :
    (∀ z, augmented p R (scoreFits p R O) z = ht p R z -
      (∑ i, (bit (z i)-p i)*dot (O i) (scoreGamma p R O)) / N) ∧
    (∀ i, expect p (residualContrast p R (scoreFits p R O) i) =
      residualEffect p R (printedFits p R O) i) ∧
    expect p (augmented p R (scoreFits p R O)) = ame p R := by
  have hg : ∀ i, scoreFits p R O i true-scoreFits p R O i false =
      printedFits p R O i true-printedFits p R O i false := by
    intro i
    simp only [scoreFits, Bool.false_eq_true, if_false, if_true]
    ring
  refine ⟨?_, ?_, augmented_unbiased p R (scoreFits p R O) hp⟩
  · intro z
    have hi : ∀ i, scoreFits p R O i true-scoreFits p R O i false +
        bit (z i)*(R i z-scoreFits p R O i true)/p i -
          (1-bit (z i))*(R i z-scoreFits p R O i false)/(1-p i) =
        (bit (z i)*R i z/p i-(1-bit (z i))*R i z/(1-p i)) -
          (bit (z i)-p i)*dot (O i) (scoreGamma p R O) := by
      intro i
      rw [hg i]
      exact corrected_score_identity (z i) (p i) (R i z)
        (printedFits p R O i true-printedFits p R O i false)
        (dot (O i) (scoreGamma p R O)) (ne_of_gt (hp i).1)
        (ne_of_gt (sub_pos.mpr (hp i).2))
    unfold augmented ht
    simp_rw [hi]
    rw [Finset.sum_sub_distrib, sub_div]
  · intro i
    rw [residualContrast_mean p R (scoreFits p R O) i hp]
    unfold residualEffect
    rw [hg i]


/- Spatial aggregation, randomization, and finite identities. -/

/-- Finite-measure version of eq. (2) (p. 747 permits discrete outcome points). -/
def finiteAverage {A : Type*} [Fintype A] (mass : A → ℝ) (Y : A → ℝ) : ℝ :=
  (∑ x, mass x * Y x) / (∑ x, mass x)


/-- T6(b), every normalized positive-mass average lies between the
minimum and maximum bin effects. Equal masses give the arithmetic mean. -/
theorem weighted_effect_bounds {m : ℕ} (a τ : Fin m → ℝ)
    (hm : 0 < m) (ha : ∀ k, 0 < a k) :
    (∀ lo hi : ℝ, (∀ k, lo ≤ τ k ∧ τ k ≤ hi) →
      lo ≤ finiteAverage a τ ∧ finiteAverage a τ ≤ hi) ∧
    (∀ c : ℝ, (∀ k, a k = c) → finiteAverage a τ = (∑ k, τ k) / m) := by
  have hs : 0 < ∑ k, a k :=
    Finset.sum_pos (fun k _ => ha k) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  constructor
  · intro lo hi hτ
    unfold finiteAverage
    constructor
    · apply (le_div_iff₀ hs).mpr
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      nlinarith [(hτ k).1, ha k]
    · apply (div_le_iff₀ hs).mpr
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      nlinarith [(hτ k).2, ha k]
  · intro c hc
    have hcpos : 0 < c := by rw [← hc ⟨0, hm⟩]; exact ha ⟨0, hm⟩
    have hmreal : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
    unfold finiteAverage
    simp_rw [hc]
    rw [← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt hcpos, hmreal]
    <;> ring

/-- T5 witness B: bin masses (π cancels) are 1,3,5,7,9,11.
Three weighted binary atoms per bin realize q₀=(.1,...,.1) and
q₁=(.02,.1092,...,.1092). No assignment can change another node's outcome. -/
def areaWitnessMass (j : Fin 6) (x : Fin 3) : ℝ :=
  (2*(j : ℝ)+1) * (if j = 0 then (![1/50, 2/25, 9/10] : Fin 3 → ℝ) x
    else (![1/10, 23/2500, 2227/2500] : Fin 3 → ℝ) x)
/-- Binary atom outcomes realizing q₀=.1 and q₁=.02 or .1092,
T5 case B; the support has three atoms per bin. -/
def areaWitnessOutcome (j : Fin 6) (a : Bool) (x : Fin 3) : ℝ :=
  if j = 0 then if a then (if x = 0 then 1 else 0)
    else (if x = 0 ∨ x = 1 then 1 else 0)
  else if a then (if x = 0 ∨ x = 1 then 1 else 0)
    else (if x = 0 then 1 else 0)
/-- Circle-bin averages of the binary atoms with their actual masses,
T5 case B, eq. (2), p. 747. -/
def areaWitnessTable (j : Fin 6) : CircleTable 2 :=
  fun i z => finiteAverage (areaWitnessMass j) (areaWitnessOutcome j (z i))
/-- The explicit treated/control assignment z=(1,0), T5 case B. -/
def areaWitnessAssignment : Assignment 2 := ![true, false]

/-- Explicit enumeration of the four assignments for finite witness checks;
these are all assignments, with no conditioning on a favorable event. -/
theorem assignment_two_univ : (Finset.univ : Finset (Assignment 2)) =
    {![false,false], ![false,true], ![true,false], ![true,true]} := by decide

/-- T5, a concrete binary-outcome counterexample: with independent half
coins and realized assignment (1,0), the six-bin sum is −.034 while
the whole-region area effect is +121/18000. The atom masses are positive,
outcomes binary, and the bins partition the finite spatial measure. -/
theorem finite_area_sum_certificate :
    (∀ j x, 0 < areaWitnessMass j x) ∧
    (∀ j a x, areaWitnessOutcome j a x = 0 ∨ areaWitnessOutcome j a x = 1) ∧
    (∑ j : Fin 6, hajek (areaWitnessTable j) areaWitnessAssignment) = -(17/500 : ℝ) ∧
    (∑ j : Fin 6, ame (fun _ => 1/2) (areaWitnessTable j)) = -(17/500 : ℝ) ∧
    (∑ j : Fin 6, (2*(j : ℝ)+1)/36 * ame (fun _ => 1/2) (areaWitnessTable j)) = (121/18000 : ℝ) ∧
    (0 : ℝ) < 121/18000 ∧ -(17/500 : ℝ) ≠ 121/18000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x
    fin_cases j <;> fin_cases x <;> norm_num [areaWitnessMass]
  · intro j a x
    fin_cases j <;> cases a <;> fin_cases x <;> norm_num [areaWitnessOutcome]
  · norm_num [hajek, armMean, armCount, areaWitnessTable, finiteAverage,
      areaWitnessMass, areaWitnessOutcome, areaWitnessAssignment, Fin.sum_univ_succ]
  · norm_num [ame, nodeEffect, marginal, expect, designWeight, coin,
      assignment_two_univ, areaWitnessTable, finiteAverage, areaWitnessMass,
      areaWitnessOutcome, Fin.sum_univ_succ]
  · norm_num [ame, nodeEffect, marginal, expect, designWeight, coin,
      assignment_two_univ, areaWitnessTable, finiteAverage, areaWitnessMass,
      areaWitnessOutcome, Fin.sum_univ_succ]
  · norm_num
  · norm_num

/-- T5 finite calculation, keeping the actual binary atom averages and
the observed Hajek contrast; this calculation is separate from design marginalization. -/
theorem area_witness_realized :
    (∑ j : Fin 6, hajek (areaWitnessTable j) areaWitnessAssignment) = -(17/500 : ℝ) ∧
    (∑ j : Fin 6, (2*(j : ℝ)+1)/36 * hajek (areaWitnessTable j) areaWitnessAssignment) =
      (121/18000 : ℝ) := by
  norm_num [hajek, armMean, armCount, areaWitnessTable, finiteAverage,
    areaWitnessMass, areaWitnessOutcome, areaWitnessAssignment, Fin.sum_univ_succ]




/-- Marginalized point effect τᵢₓ, eq. (7), p. 750. -/
def pointEffect {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (p : Fin N → ℝ) (i : Fin N) (x : A) : ℝ :=
  marginal p (fun _ z => P.outcome x z) i true -
    marginal p (fun _ z => P.outcome x z) i false


/-- Positive supported-shell masses induced by a finite spatial measure,
T15(b): shells with zero mass are excluded by the sum's actual filter. -/
def supportedShellMass {A : Type*} [Fintype A] {m N : ℕ}
    (mass : A → ℝ) (shell : Fin N → A → Fin m) (i : Fin N) (k : Fin m) : ℝ :=
  ∑ x, if shell i x = k then mass x else 0

/-- A partition into shells preserves the spatial numerator, p. 757 correction. -/
theorem shell_partition_sum {A : Type*} [Fintype A] {m : ℕ}
    (shell : A → Fin m) (v : A → ℝ) :
    (∑ k : Fin m, ∑ x, if shell x = k then v x else 0) = ∑ x, v x := by
  rw [Finset.sum_comm]
  simp


/-- An empty shell contributes zero mass and zero outcome integral, p. 757. -/
theorem shell_zero_numerator {A : Type*} [Fintype A] {m : ℕ}
    (mass v : A → ℝ) (shell : A → Fin m) (k : Fin m)
    (ha : ∀ x, 0 ≤ mass x) (hz : (∑ x, if shell x = k then mass x else 0) = 0) :
    (∑ x, if shell x = k then mass x*v x else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  by_cases h : shell x = k
  · have hle := Finset.single_le_sum (fun y (_ : y ∈ (Finset.univ : Finset A)) =>
      show 0 ≤ (if shell y = k then mass y else 0) by split_ifs; exact ha y; exact le_rfl)
      (Finset.mem_univ x)
    rw [if_pos h, hz] at hle
    simp [h, le_antisymm hle (ha x)]
  · simp [h]


/-- T15(b–c), shell aggregation on each node's actual support, allowing empty shells. -/
theorem shell_mass_identity {A : Type*} [Fintype A] {m N : ℕ}
    (mass : A → ℝ) (shell : Fin N → A → Fin m) (δ : Fin N → A → ℝ)
    (ha : ∀ x, 0 ≤ mass x) (hpos : 0 < ∑ x, mass x) :
    (∀ i, finiteAverage mass (δ i) =
      ∑ k ∈ Finset.univ.filter (fun k => 0 < supportedShellMass mass shell i k),
        supportedShellMass mass shell i k/(∑ x, mass x) *
          ((∑ x, if shell i x = k then mass x*δ i x else 0)/supportedShellMass mass shell i k)) ∧
    (∀ w : Fin m → ℝ,
      (∀ i k, supportedShellMass mass shell i k/(∑ x, mass x) = w k) →
      (∑ i, finiteAverage mass (δ i))/N = ∑ k, w k *
        ((∑ i, (∑ x, if shell i x = k then mass x*δ i x else 0)/
          supportedShellMass mass shell i k)/N)) := by
  have hnonneg : ∀ i k, 0 ≤ supportedShellMass mass shell i k := by
    intro i k
    apply Finset.sum_nonneg
    intro x _
    split_ifs; exact ha x; exact le_rfl
  have hcancel : ∀ i k,
      supportedShellMass mass shell i k/(∑ x, mass x) *
        ((∑ x, if shell i x = k then mass x*δ i x else 0)/supportedShellMass mass shell i k) =
        (∑ x, if shell i x = k then mass x*δ i x else 0)/(∑ x, mass x) := by
    intro i k
    by_cases h : supportedShellMass mass shell i k = 0
    · have hz := shell_zero_numerator mass (δ i) (shell i) k ha h
      simp [h, hz]
    · field_simp
  have hfull : ∀ i, finiteAverage mass (δ i) = ∑ k,
      supportedShellMass mass shell i k/(∑ x, mass x) *
        ((∑ x, if shell i x = k then mass x*δ i x else 0)/supportedShellMass mass shell i k) := by
    intro i
    simp_rw [hcancel]
    rw [← Finset.sum_div, shell_partition_sum]
    rfl
  constructor
  · intro i
    rw [hfull, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : 0 < supportedShellMass mass shell i k
    · simp [h]
    · have hz : supportedShellMass mass shell i k = 0 := le_antisymm (le_of_not_gt h) (hnonneg i k)
      simp [h, hz]
  · intro w hw
    simp_rw [hfull, hw]
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.mul_sum, mul_div_assoc]


/-- T14 witness 2, the actual three-atom spatial distance pattern is
(4,5,5) at node 1 and (5,4,4) at node 2; effects are (0,1,1) and (−1,0,0).
The two circle AMEs vanish while the disk/donut AME is 1/6. -/
def shellWitnessDistance (i : Fin 2) (x : Fin 3) : ℝ :=
  if i = 0 then (if x = 0 then 4 else 5) else (if x = 0 then 5 else 4)
/-- The effects at the three atoms are (0,1,1) for node 0 and
(−1,0,0) for node 1, T14. -/
def shellWitnessEffect (i : Fin 2) (x : Fin 3) : ℝ :=
  if i = 0 then (if x = 0 then 0 else 1) else (if x = 0 then -1 else 0)
/-- “Yₓ(z)=1+∑ᵢzᵢgᵢ(x)” in the T14 three-atom witness;
it is a fixed full potential-outcome schedule. -/
def shellWitnessOutcome (x : Fin 3) (z : Assignment 2) : ℝ :=
  1 + ∑ i, bit (z i) * shellWitnessEffect i x
/-- The finite distance-table shell averages with equal atom masses,
T14, eq. (2), p. 747. -/
def shellWitnessTable (band : ℝ → Prop) : CircleTable 2 :=
  fun i z => (∑ x : Fin 3, if band (shellWitnessDistance i x) then shellWitnessOutcome x z else 0) /
    (∑ x : Fin 3, if band (shellWitnessDistance i x) then (1 : ℝ) else 0)

/-- T14, no common radial smoothing recovers the band AME in the
finite three-atom, two-node construction (p. 757). -/
theorem finite_shell_certificate :
    ame (fun _ => 1/2) (shellWitnessTable (fun r => r = 4)) = 0 ∧
    ame (fun _ => 1/2) (shellWitnessTable (fun r => r = 5)) = 0 ∧
    ame (fun _ => 1/2) (shellWitnessTable (fun r => 4 ≤ r ∧ r ≤ 5)) = (1/6 : ℝ) ∧
    ∀ w4 w5 : ℝ,
      w4 * ame (fun _ => 1/2) (shellWitnessTable (fun r => r = 4)) +
      w5 * ame (fun _ => 1/2) (shellWitnessTable (fun r => r = 5)) ≠
        ame (fun _ => 1/2) (shellWitnessTable (fun r => 4 ≤ r ∧ r ≤ 5)) := by
  norm_num [ame, nodeEffect, marginal, expect, designWeight, coin, bit,
    assignment_two_univ, shellWitnessTable, shellWitnessDistance, shellWitnessOutcome,
    shellWitnessEffect, Fin.sum_univ_succ]

/-- T13, draw 0 is the observed assignment, and draws 1,...,P are
i.i.d. from the same finite design. Arbitrary fixed-outcome statistics
are allowed, so no no-ties restriction enters. -/
def mcDrawWeight {N : ℕ} (p : Fin N → ℝ) {P : ℕ}
    (draws : Fin (P+1) → Assignment N) : ℝ := ∏ r, designWeight p (draws r)
/-- “B ... |T(d)|” comparisons, Section 6.3, p. 758: counts the
P resamples whose absolute statistic is at least the absolute observed statistic. -/
def mcExceedances {N P : ℕ} (T : Assignment N → ℝ)
    (draws : Fin (P+1) → Assignment N) : ℕ :=
  (Finset.univ.filter (fun r : Fin (P+1) => r ≠ 0 ∧ |T (draws 0)| ≤ |T (draws r)|)).card
/-- The corrected “(1+B)/(P+1)” finite-resample p-value,
T13; ties are included in B. -/
def mcPlusPvalue {N P : ℕ} (T : Assignment N → ℝ)
    (draws : Fin (P+1) → Assignment N) : ℝ := (1 + mcExceedances T draws : ℝ) / (P+1)


/-- T13(c), the plus-one correction changes B/P by at most 1/(P+1). -/
theorem mc_plus_one_identity (P B : ℕ) (hP : 0 < P) (hB : B ≤ P) :
    (1+(B : ℝ))/(P+1) - (B : ℝ)/P = (1-(B : ℝ)/P)/(P+1) ∧
    0 ≤ (1+(B : ℝ))/(P+1) - (B : ℝ)/P ∧
    (1+(B : ℝ))/(P+1) - (B : ℝ)/P ≤ 1/(P+1) := by
  have hp : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  have hbp : (B : ℝ) ≤ P := Nat.cast_le.mpr hB
  have hpp : (0 : ℝ) < P+1 := by positivity
  have he : (1+(B : ℝ))/(P+1) - (B : ℝ)/P = (1-(B : ℝ)/P)/(P+1) := by
    field_simp
    <;> ring
  rw [he]
  refine ⟨rfl, div_nonneg ?_ (le_of_lt hpp), ?_⟩
  · exact sub_nonneg.mpr ((div_le_one hp).mpr hbp)
  · apply div_le_div_of_nonneg_right _ (le_of_lt hpp)
    have : 0 ≤ (B : ℝ)/P := by positivity
    linarith

/-- T12A: a negative observed signed statistic makes the printed
absolute-resample comparison true for every draw; it never rejects at α<1. -/
theorem negative_observed_comparison (observed resampled : ℝ) (h : observed < 0) :
    observed ≤ |resampled| := le_trans (le_of_lt h) (abs_nonneg _)

/-- T12B, the exact eight-node sharp-null rejection probability,
P=100, α=1/20. The rank m is uniform on 1,...,128. -/
def eightNodeMCNumerator : ℕ :=
  ∑ m ∈ Finset.range 128, ∑ b ∈ Finset.range 6,
    Nat.choose 100 b * (m+1)^b * (128-(m+1))^(100-b)
/-- The exact rational rejection sum for P=100 and α=1/20, T12B. -/
def eightNodeMCSize : ℝ :=
  (eightNodeMCNumerator : ℝ) / (128 : ℝ)^101

set_option maxRecDepth 10000 in
/-- T12B, the binomial-rank calculation exceeds 1/20.
This is the numerical component of the sharp-null rejection calculation. -/
theorem mc_size_counterexample : eightNodeMCSize > (1/20 : ℝ) := by
  have hn : (128 : ℕ)^101 < 20*eightNodeMCNumerator := by
    unfold eightNodeMCNumerator
    simp_rw [Nat.choose_eq_descFactorial_div_factorial]
    decide
  have hr : (128 : ℝ)^101 < 20*(eightNodeMCNumerator : ℝ) := by exact_mod_cast hn
  unfold eightNodeMCSize
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 128^101)).mpr
  nlinarith

/-- T23(b), symmetry of normal critical values makes the printed
absolute-value event equivalent to the usual two-sided event. -/
theorem symmetric_critical_event (a t : ℝ) (ha : 0 ≤ a) :
    (-a ≤ |t| ∧ |t| ≤ a) ↔ |t| ≤ a := by
  constructor
  · exact And.right
  · intro h
    exact ⟨le_trans (neg_nonpos.mpr ha) (abs_nonneg t), h⟩

/-- T34(a,c), the missing absolute value in eqs. (127)–(129),
and the ratio identity in eq. (124), are exact scalar identities. -/
theorem denominator_absolute_identity (N N1 p S : ℝ)
    (hN : N ≠ 0) (h1 : N1 ≠ 0) (hp : p ≠ 0) :
    |N * ((N*S)/N1^2 - (N*S)/(N^2*p^2))| = |N^2/N1^2 - 1/p^2| * |S| ∧
    |N^2/N1^2 - 1/p^2| = |((N1/N-p)*(N1/N+p))/(p^2*(N1/N)^2)| := by
  constructor
  · rw [← abs_mul]
    congr 1
    field_simp
    <;> ring
  · rw [← abs_neg]
    congr 1
    field_simp
    <;> ring

/-- T34, explicit arithmetic in the N=8, N₁=5, p=1/2, S=−1/4 witness:
the corrected left side is +9/25 and the printed right side is −9/25. -/
theorem missing_absolute_witness :
    |(8 : ℝ)^2/5^2 - 1/(1/2 : ℝ)^2| * |(-1/4 : ℝ)| = 9/25 ∧
    ((8 : ℝ)^2/5^2 - 1/(1/2 : ℝ)^2) * |(-1/4 : ℝ)| = -9/25 ∧
    ¬ (9/25 : ℝ) ≤ -9/25 := by norm_num

/-- T25, centered NED summand, eq. (57), Supplement A p. 26:
the centering is τᵢ/N, not τᵢ. -/
def centeredSummand {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (μ1 μ0 : ℝ) (i : Fin N) (z : Assignment N) : ℝ :=
  (μ1-μ0 + residualContrast p R (fun _ a => if a then μ1 else μ0) i z - nodeEffect p R i) / N

/-- T25(a–c), corrected zero mean and exact sum decomposition, and the
mean of the misprinted summand. Every fixed N identity is retained. -/
theorem centered_summand_identity {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (μ1 μ0 : ℝ) (hN : 0 < N) (hp : ∀ i, 0 < p i ∧ p i < 1) :
    (∀ i, expect p (centeredSummand p R μ1 μ0 i) = 0) ∧
    (∀ z, (∑ i, centeredSummand p R μ1 μ0 i z) =
      augmented p R (fun _ a => if a then μ1 else μ0) z - ame p R) ∧
    (∀ i, expect p (fun z => centeredSummand p R μ1 μ0 i z +
      ((1 : ℝ)/N-1)*nodeEffect p R i) = ((1 : ℝ)/N-1)*nodeEffect p R i) := by
  have hm : ∀ i, expect p (centeredSummand p R μ1 μ0 i) = 0 := by
    intro i
    unfold centeredSummand
    rw [expect_div, expect_sub, expect_add, expect_const,
      residualContrast_mean p R (fun _ a => if a then μ1 else μ0) i hp, expect_const]
    simp [residualEffect]
  refine ⟨hm, ?_, ?_⟩
  · intro z
    unfold centeredSummand
    rw [← Finset.sum_div, Finset.sum_sub_distrib, sub_div]
    unfold ame
    congr 1
    unfold augmented residualContrast
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Bool.false_eq_true, if_false, if_true]
    ring
  · intro i
    rw [expect_add, hm i, expect_const, zero_add]

/-- T30(2), corrected member of the estimator class is (μ̄₁,μ̄₀).
It is exactly the corrected linearized Hajek estimator for every assignment. -/
theorem linear_hajek_class_identity {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) :
    linearHajek p R = augmented p R (fun _ a => barMu p R a) := rfl

/-- T21(a), corrected node variance; means are squared, not second moments. -/
theorem node_variance_identity {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i : Fin N) (hp : ∀ j, 0 < p j ∧ p j < 1) :
    variance p (residualContrast p R g i) =
      marginal p (fun j z => (R j z-g j true)^2) i true / p i +
      marginal p (fun j z => (R j z-g j false)^2) i false / (1-p i) -
      (residualEffect p R g i)^2 := by
  have hx : (fun z => residualContrast p R g i z*residualContrast p R g i z) =
      fun z => (if z i = true then (R i z-g i true)^2 else 0)/(p i)^2 +
        (if z i = false then (R i z-g i false)^2 else 0)/(1-p i)^2 := by
    funext z
    have hp0 : p i ≠ 0 := ne_of_gt (hp i).1
    have hq0 : 1-p i ≠ 0 := ne_of_gt (sub_pos.mpr (hp i).2)
    cases h : z i <;> simp [residualContrast, bit, h]
      <;> field_simp [hp0, hq0] <;> ring
  unfold variance cov
  rw [residualContrast_mean p R g i hp, hx, expect_add, expect_div, expect_div]
  simp only [marginal, coin, Bool.false_eq_true, if_false, if_true, div_div, pow_two]


/- Sequences and the standing spatial assumptions. -/

variable {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]

/-- The sample-size-indexed S_N, X_N and fixed potential outcomes of
Section 4, p. 751; outcome spaces and measures may vary with N. -/
abbrev PopulationSequence (Space : ℕ → Type*) [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] := ∀ N, SpatialPopulation N (Space N)

/-- “A distance metric γ that satisfies positivity and the triangle inequality”
(Appendix C, Supplement A p. 25). The node separations used by all NED
balls must themselves be a metric; infimum distances between arbitrary
polygon sets alone do not ensure this standing assumption. -/
def MetricNodeDistances (P : PopulationSequence Space) : Prop :=
  ∀ N, (∀ i j, 0 ≤ nodeSeparation (P N) i j) ∧
    (∀ i j, nodeSeparation (P N) i j = 0 ↔ i = j) ∧
    (∀ i j, nodeSeparation (P N) i j = nodeSeparation (P N) j i) ∧
    (∀ i j k, nodeSeparation (P N) i k ≤
      nodeSeparation (P N) i j + nodeSeparation (P N) j k)

/-- C2–C4 uniformly in sample size, pp. 751–753. C2 is imposed on
the raw outcomes, C3 on the actual circle-average interference relation,
and C4 on every fixed-radius spatial neighborhood. -/
def SpatialLocalConditions (P : PopulationSequence Space) : Prop :=
  (∃ b : ℝ, 0 < b ∧ ∀ᶠ N in atTop, ∀ x z, |(P N).outcome x z| < b) ∧
  (∃ h : ℝ → ℝ, (∀ d, 0 ≤ d → 0 ≤ h d) ∧
    ∀ d, 0 ≤ d → ∀ᶠ N in atTop,
      LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) (h d)) ∧
  (∃ c : ℝ → ℝ, ∀ r, 0 ≤ r → ∀ᶠ N in atTop, ∀ i,
    ((ball (nodeSeparation (P N)) i r).card : ℝ) ≤ c r)

/-- C6 overlap: one fixed ε∈(0,1/2), independent assignments already
encoded in designWeight, and ε<pᵢ<1−ε, p. 758. -/
def Overlap (p : ∀ N, Fin N → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < 1/2 ∧ ∀ N i, ε < p N i ∧ p N i < 1-ε

/-- The sequence of circle tables from the spatial integral. -/
def circleSequence (P : PopulationSequence Space) (d : ℝ) (N : ℕ) : CircleTable N :=
  circleAverage (P N) d

/-- The chosen valid C3 cutoff and associated B_N(i;d), eq. (12), p. 753. -/
def spatialNeighborhoods (P : PopulationSequence Space) (h : ℝ) (N : ℕ) : Fin N → Finset (Fin N) :=
  fun i => ball (nodeSeparation (P N)) i h

/-- β̂_a of Supplement A p. 15 footnote 9, using the entire observed sample. -/
def fittedBeta {N k : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (a : Bool) (z : Assignment N) : Fin k → ℝ :=
  (information phat O)⁻¹ *ᵥ (fun j =>
    (∑ i, (if z i = a then R i z * coin (phat i) (!a) * O i j else 0)) / N)

/-- γ̂=Ĥ⁻¹D̂, corrected T2(e). -/
def fittedGamma {N k : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (z : Assignment N) : Fin k → ℝ :=
  (information phat O)⁻¹ *ᵥ (fun j =>
    (∑ i, (bit (z i)*R i z*(1-phat i)/phat i +
      (1-bit (z i))*R i z*phat i/(1-phat i))*O i j) / N)

/-- Plug-in f̂_ia, T2(e), uses fitted β_a and the corrected fitted score γ. -/
def fittedScoreFits {N k : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (z : Assignment N) (i : Fin N) (a : Bool) : ℝ :=
  let δ := dot (O i) (fittedBeta phat R O true z) - dot (O i) (fittedBeta phat R O false z)
  let L := dot (O i) (fittedGamma phat R O z)
  if a then phat i*δ + phat i*(1-phat i)*L
    else -(1-phat i)*δ + phat i*(1-phat i)*L

/-- Fitted IPW point estimator, Supplement A p. 14: the original
estimator is preserved, and only the inferential expansion is corrected. -/
def fittedIPW {N k : ℕ} (R : CircleTable N) (O : Fin N → Fin k → ℝ)
    (θhat : Assignment N → Fin k → ℝ) (z : Assignment N) : ℝ :=
  ht (propensities O (θhat z)) R z


/-- Score g_N=N⁻¹∑(Zᵢ−pᵢ)Oᵢ, Lemma A.6, Supplement A p. 14. -/
def logisticScore {N k : ℕ} (p : Fin N → ℝ) (O : Fin N → Fin k → ℝ)
    (z : Assignment N) : Fin k → ℝ := fun j => (∑ i, (bit (z i)-p i)*O i j) / N


/-- Uniform kernel I(x∈[0,1]), p. 755 footnote 12. -/
def uniformKernel (t : ℝ) : ℝ := if 0 ≤ t ∧ t ≤ 1 then 1 else 0

/-- Kernel matrix K(dᵢⱼ/b), eq. (21), p. 756. -/
def distanceKernel {N : ℕ} (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (b : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => K (D i j/b)


/- Geometry and regression corrections. -/

/-- Source effects have range d̄, as in the sufficient-condition paragraph,
p. 752: changing Z_l changes no outcome farther than d̄ from node l. -/
def FiniteSourceRange {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (dbar : ℝ) : Prop :=
  ∀ l x z z', (∀ k, k ≠ l → z k = z' k) → dbar < nodeDistance P l x →
    P.outcome x z = P.outcome x z'


/-- T17(a), the triangle-inequality chain used in the geometric proof.
The middle source node contributes its diameter D. -/
theorem diameter_chain {A : Type*} [MetricSpace A] (a x u v y b : A)
    (d dbar D : ℝ) (hax : dist a x ≤ d) (hxu : dist x u ≤ dbar)
    (huv : dist u v ≤ D) (hvy : dist v y ≤ dbar) (hyb : dist y b ≤ d) :
    dist a b ≤ 2*dbar+2*d+D := by
  have h1 := dist_triangle a x b
  have h2 := dist_triangle x u b
  have h3 := dist_triangle u v b
  have h4 := dist_triangle v y b
  linarith

/-- A closed polygonal region is a finite union of filled triangles;
this permits nonconvex polygons as well as convex ones, p. 753. -/
def Polygonal (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ m : ℕ, ∃ v : Fin m → Fin 3 → EuclideanSpace ℝ (Fin 2),
    A = ⋃ i, convexHull ℝ (Set.range (v i))


/-- Euclidean rectangles used in T16. -/
def rectangle (a b c d : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ d}

/-- T16A actual spatial construction: A=[0,1]², B=[10,11]×[0,1],
C=[0,11]×[2,3], area measure and Y_x(z)=Z_C on A∪B. -/
def rectangleWitness : SpatialPopulation 3 (EuclideanSpace ℝ (Fin 2)) where
  node := ![rectangle 0 1 0 1, rectangle 10 11 0 1, rectangle 0 11 2 3]
  node_nonempty := by
    intro i
    fin_cases i
    · exact ⟨WithLp.toLp 2 ![0,0], by norm_num [rectangle]⟩
    · exact ⟨WithLp.toLp 2 ![10,0], by norm_num [rectangle]⟩
    · exact ⟨WithLp.toLp 2 ![0,2], by norm_num [rectangle]⟩
  zeta := volume
  outcome := fun x z => if x ∈ rectangle 0 1 0 1 ∪ rectangle 10 11 0 1 then bit (z 2) else 0
  bands := fun d => {d}


/-- T16B thin rectangles of area one cluster next to a unit square;
the index n controls both their number and their aspect ratio. -/
def thinPolygon (n : ℕ) (i : Fin (n+1)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  if i = 0 then rectangle 0 1 0 1
  else rectangle 2 (2+n) (2*((i : ℝ)-1)/n) ((2*((i : ℝ)-1)+1)/n)


/- Dependency graphs and the near-epoch-dependence extension. -/

/-- A genuine dependency graph: families with no cross edge are independent,
not merely pairwise uncorrelated; corrected Lemma A.5, T20. -/
def DependencyGraph {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) (V : Fin N → Ω → ℝ) (B : Fin N → Finset (Fin N)) : Prop :=
  (∀ i, i ∈ B i) ∧ (∀ i j, j ∈ B i ↔ i ∈ B j) ∧
  ∀ I J : Finset (Fin N), (∀ i ∈ I, ∀ j ∈ J, j ∉ B i) →
    ProbabilityTheory.IndepFun (fun ω (i : I) => V i ω) (fun ω (j : J) => V j ω) μ

/-- T19 witness 1: only the first summand is a Rademacher sign.
The ambient independent Bernoulli space makes every hypothesis explicit. -/
def loneRademacher (N : ℕ) (i : Fin N) (z : Assignment N) : ℝ :=
  if i.val = 0 then 2*bit (z i)-1 else 0

/-- Finite-space dependency graph, the same full family independence
as T20, expressed through event probabilities over the actual design. -/
def FiniteDependencyGraph {N : ℕ} (p : Fin N → ℝ) (V : CircleTable N)
    (B : Fin N → Finset (Fin N)) : Prop :=
  (∀ i, i ∈ B i) ∧ (∀ i j, j ∈ B i ↔ i ∈ B j) ∧
  ∀ I J : Finset (Fin N), (∀ i ∈ I, ∀ j ∈ J, j ∉ B i) →
    ∀ A : (I → ℝ) → Prop, ∀ C : (J → ℝ) → Prop,
      prob p (fun z => A (fun i => V i z) ∧ C (fun j => V j z)) =
        prob p (fun z => A (fun i => V i z)) * prob p (fun z => C (fun j => V j z))


/-- E[X|σ(Z_j:j∈J)] evaluated at z, finite weighted conditional
expectation; Appendix C p. 25. Overlap guarantees positive conditioning mass. -/
def conditionOn {N : ℕ} (p : Fin N → ℝ) (J : Finset (Fin N))
    (U : Assignment N → ℝ) (z : Assignment N) : ℝ :=
  expect p (fun z' => if ∀ j ∈ J, z' j = z j then U z' else 0) /
    (∏ j ∈ J, coin (p j) (z j))

/-- ||X||₂=(E|X|²)^(1/2), Definition 1, Supplement A p. 25. -/
def l2Norm {N : ℕ} (p : Fin N → ℝ) (U : Assignment N → ℝ) : ℝ :=
  Real.sqrt (expect p (fun z => (U z)^2))

/-- Uniform L₂-NED of size −4, Appendix C “C 3”, p. 26.
The error is against the actual local conditional expectation, and ψ
decays at a rate strictly faster than s⁻⁴. -/
def NEDConditions (P : PopulationSequence Space) (p d : ℝ) : Prop :=
  ∃ ψ : ℝ → ℝ, ∃ g : ∀ N, Fin N → ℝ, ∃ G : ℝ,
    (∀ s, 0 ≤ s → 0 ≤ ψ s) ∧ AntitoneOn ψ (Set.Ici 0) ∧
    Tendsto ψ atTop (nhds 0) ∧
    (∃ exponent : ℝ, 4 < exponent ∧ ∃ C S : ℝ, 0 < S ∧
      ∀ s, S ≤ s → ψ s ≤ C * s^(-exponent)) ∧
    (∀ N i, 0 < g N i ∧ g N i ≤ G) ∧
    (∀ N i s, 0 ≤ s → l2Norm (fun _ => p)
      (fun z => circleAverage (P N) d i z -
        conditionOn (fun _ => p) (ball (nodeSeparation (P N)) i s) (circleAverage (P N) d i) z) ≤ g N i*ψ s)

/-- Appendix C “C 4”, with the nonvacuous reading:
the quadratic count bound is C_b(1+s²), including the centre at s=0. -/
def QuadraticSpacing (P : PopulationSequence Space) : Prop :=
  ∃ Cb : ℝ, 0 < Cb ∧ ∀ᶠ N in atTop, ∀ i s, 0 ≤ s →
    ((ball (nodeSeparation (P N)) i s).card : ℝ) ≤ Cb*(1+s^2)

/-- C2 on raw outcomes, p. 751, uniformly in large sample sizes. -/
def BoundedOutcomes (P : PopulationSequence Space) : Prop :=
  ∃ b : ℝ, 0 < b ∧ ∀ᶠ N in atTop, ∀ x z, |(P N).outcome x z| < b

/-- Appendix C “C 5”, p. 32: unit value at zero, vanishing for t>1,
boundedness on nonnegative arguments, and local Lipschitz control to the right of zero. -/
def KernelConditions (K : ℝ → ℝ) : Prop :=
  K 0 = 1 ∧ (∀ t, 1 < t → K t = 0) ∧
  (∃ Kmax : ℝ, ∀ t, 0 ≤ t → |K t| < Kmax) ∧
  ∃ ε C : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < C ∧ ∀ t, 0 ≤ t → t < ε → |K t-1| ≤ C*|t|

/-- Appendix C “C 6”, eq. (122), p. 34, on the actual centered effects. -/
def kernelHomophily (P : PopulationSequence Space) (p d : ℝ)
    (K : ℝ → ℝ) (bandwidth : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ i, ∑ j, K (nodeSeparation (P N) i j / bandwidth N) *
    (nodeEffect (fun _ => p) (circleAverage (P N) d) i-ame (fun _ => p) (circleAverage (P N) d)) *
    (nodeEffect (fun _ => p) (circleAverage (P N) d) j-ame (fun _ => p) (circleAverage (P N) d))) / N

/-- ε̂_{i,N}, eq. (102), Appendix C p. 32, has the factor 1/N. -/
def nedEpsilon {N : ℕ} (p : ℝ) (R : CircleTable N) (μ1 μ0 : ℝ)
    (i : Fin N) (z : Assignment N) : ℝ :=
  residualContrast (fun _ => p) R (fun _ a => if a then μ1 else μ0) i z / N

/-- v̂_{i,N}, eq. (107), Appendix C p. 33, is random; its expectation
v_{i,N} is a different object (T29(3)). -/
def nedVRow {N : ℕ} (p : ℝ) (R : CircleTable N) (D : Fin N → Fin N → ℝ)
    (K : ℝ → ℝ) (b μ1 μ0 : ℝ) (i : Fin N) (z : Assignment N) : ℝ :=
  ∑ j ∈ ball D i b, nedEpsilon p R μ1 μ0 i z * nedEpsilon p R μ1 μ0 j z * K (D i j/b)

/-- V̂₁ uses observed arm means; V̂₂ uses deterministic marginalized
means, eqs. (117)–(121), Appendix C p. 34. -/
def nedV1 {N : ℕ} (p : ℝ) (R : CircleTable N) (D : Fin N → Fin N → ℝ)
    (K : ℝ → ℝ) (b : ℝ) (z : Assignment N) : ℝ :=
  ∑ i, nedVRow p R D K b (armMean R z true) (armMean R z false) i z
/-- “V̂₂(d;b_N)” uses the deterministic μ̄¹ and μ̄⁰,
eqs. (117)–(121), Appendix C p. 34. -/
def nedV2 {N : ℕ} (p : ℝ) (R : CircleTable N) (D : Fin N → Fin N → ℝ)
    (K : ℝ → ℝ) (b : ℝ) (z : Assignment N) : ℝ :=
  ∑ i, nedVRow p R D K b (barMu (fun _ => p) R true) (barMu (fun _ => p) R false) i z


/-- Tail envelope in corrected Lemma C.10, T26: the sum is OUTSIDE
the expanding ball, not inside it (Appendix C p. 35). -/
def tailEnvelope (P : PopulationSequence Space) (φ : ℝ → ℝ) (r : ℕ → ℝ) (N : ℕ) : ℝ :=
  sSup (Set.range (fun i : Fin N => ∑ j ∈ (ball (nodeSeparation (P N)) i (r N))ᶜ,
    φ (nodeSeparation (P N) i j)))


/-- T29(5), eqs. (146)–(148) need the factor 1/N² in the mean products. -/
theorem ned_epsilon_means {N : ℕ} (p : ℝ) (R : CircleTable N)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hN : 0 < N) (hp : 0 < p ∧ p < 1) :
    let ε := nedEpsilon p R (barMu (fun _ => p) R true) (barMu (fun _ => p) R false)
    (∀ i, expect (fun _ => p) (ε i) = (nodeEffect (fun _ => p) R i-ame (fun _ => p) R)/N) ∧
    (∑ i, ∑ j, Q i j * (expect (fun _ => p) (fun z => ε i z*ε j z)-cov (fun _ => p) (ε i) (ε j))) =
      (∑ i, ∑ j, Q i j*(nodeEffect (fun _ => p) R i-ame (fun _ => p) R)*
        (nodeEffect (fun _ => p) R j-ame (fun _ => p) R))/(N : ℝ)^2 := by
  let ε := nedEpsilon p R (barMu (fun _ => p) R true) (barMu (fun _ => p) R false)
  change (∀ i, expect (fun _ => p) (ε i) =
      (nodeEffect (fun _ => p) R i-ame (fun _ => p) R)/N) ∧ _
  have hm : ∀ i, expect (fun _ => p) (ε i) =
      (nodeEffect (fun _ => p) R i-ame (fun _ => p) R)/N := by
    intro i
    change expect (fun _ => p) (fun z =>
      residualContrast (fun _ => p) R (fun _ a => if a then
        barMu (fun _ => p) R true else barMu (fun _ => p) R false) i z / N) = _
    rw [expect_div, residualContrast_mean (fun _ => p) R _ i (fun _ => hp)]
    simp only [residualEffect, Bool.false_eq_true, if_false, if_true]
    rw [barMu_difference]
  refine ⟨hm, ?_⟩
  unfold cov
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  change Q i j * (expect (fun _ => p) (fun z => ε i z*ε j z) -
      (expect (fun _ => p) (fun z => ε i z*ε j z) -
        expect (fun _ => p) (ε i)*expect (fun _ => p) (ε j))) =
      Q i j*(nodeEffect (fun _ => p) R i-ame (fun _ => p) R)*
        (nodeEffect (fun _ => p) R j-ame (fun _ => p) R)/(N : ℝ)^2
  rw [hm i, hm j]
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

/- Explicit finding witnesses and printed statements. -/

/-- Euclidean coordinates for the explicit spatial witnesses;
Section 2 p. 747: “x=(x₁,x₂)”. -/
def planePoint (a b : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![a,b]

/-- Counting-measure spatial realization of any finite table at distance
zero. Nodes and outcome points lie on the actual Euclidean plane’s x-axis
(Section 2, p. 747). -/
def linePopulation {N : ℕ} (R : CircleTable N) : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => {planePoint (10*(i : ℝ)) 0}
  node_nonempty := fun _ => Set.singleton_nonempty _
  zeta := ∑ i : Fin N, Measure.dirac (planePoint (10*(i : ℝ)) 0)
  outcome := fun x z => ∑ i : Fin N, if x = planePoint (10*(i : ℝ)) 0 then R i z else 0
  bands := fun d => Set.Icc 0 d

/-- Fixed noninterfering outcomes (1,21/20,1) by type, T1,
realizing the potential-outcome schedule of Section 2, p. 747. -/
def threeTypeTable (N : ℕ) : CircleTable N := fun i _ => if i.val % 3 = 1 then 21/20 else 1
/-- The true logistic coefficient vector (0,log 2), T1;
the three types have propensities 1/3,1/2,2/3. -/
def threeTypeTheta : Fin 2 → ℝ := ![0, Real.log 2]
/-- The fixed compact square [−2,2]² containing the truth in
its interior, T1 and Supplement A, p. 14. -/
def threeTypeParameterSet : Set (Fin 2 → ℝ) := {θ | ∀ j, -2 ≤ θ j ∧ θ j ≤ 2}
/-- Counting-measure point-node realization of the three-type
fixed outcome table, T1; all nodes lie on the Euclidean plane’s x-axis. -/
def threeTypePopulation (N : ℕ) : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) := linePopulation (threeTypeTable N)


/-- T1, exact three-type score coefficients and N-scaled variances.
This verifies the constants, separately from the MLE remainder. -/
theorem ipw_witness_variance_constants :
    let w : Fin 3 → ℝ := ![2/9,1/4,2/9]
    let a : Fin 3 → ℝ := ![27/250,-24/125,27/250]
    let b : Fin 3 → ℝ := ![-81/1000,16/125,-81/1000]
    (∑ t, w t*(a t)^2)/3 = (3/625 : ℝ) ∧
    (∑ t, w t*(b t)^2)/3 = (1753/750000 : ℝ) ∧
    (∑ t, w t*(a t-b t)^2)/3 = (10369/750000 : ℝ) ∧
    (0 : ℝ) < 10369/750000 := by
  norm_num [Fin.sum_univ_succ]

/-- T3 active-group witness: two H nodes per eight, with signs
+1,−1; six L nodes have zero outcome. O consists of the two group indicators. -/
def activeGroup (N : ℕ) (i : Fin N) : Prop := i.val % 8 < 2
/-- Two group-indicator regressors, H=(1,0) and L=(0,1), T3
and Supplement A, p. 14. -/
def activeO (N : ℕ) (i : Fin N) : Fin 2 → ℝ :=
  if activeGroup N i then ![1,0] else ![0,1]
/-- Two signed active outcomes per eight nodes, aᵢZᵢ with aᵢ=±1;
other outcomes are zero, T3. -/
def activeTable (N : ℕ) : CircleTable N :=
  fun i z => (if i.val % 8 = 0 then 1 else if i.val % 8 = 1 then -1 else 0) * bit (z i)
/-- The true group coefficients (0,−log 9), giving p_H=1/2 and
p_L=1/10, T3. -/
def activeTheta : Fin 2 → ℝ := ![0, -Real.log 9]
/-- The fixed compact coefficient square [−log 19,log 19]²,
T3 and Supplement A, p. 14. -/
def activeParameterSet : Set (Fin 2 → ℝ) := {θ | ∀ j, -Real.log 19 ≤ θ j ∧ θ j ≤ Real.log 19}
/-- Counting-measure point-node realization of the actual
active-group outcome table, T3; eq. (2), p. 747. -/
def activePopulation (N : ℕ) : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) := linePopulation (activeTable N)


/-- T4(c), exact finite values at N=32, and corrected limit 1/2
versus true N-scaled variance 1/4. The arithmetic comparisons are exact. -/
theorem sah_witness_constants :
    (493725989/38038425600 : ℝ) > 18239/1505280 ∧
    (412940740700292467/161486810505216000000 : ℝ) < 18239/1505280 ∧
    ((1/5 : ℝ)^2*(1/8)/(1/2 : ℝ)^4)/(1/4 : ℝ) = 8/25 ∧
    (1/8 : ℝ)/(1/2 : ℝ)^2 = 1/2 ∧ (1/4 : ℝ) ≤ 1/2 := by norm_num

/-- Boundary constrained logistic MLE of T9, including S=0 and S=N.
At q≤1/2 it is exactly zero; at q≥logistic(1) it is exactly one. -/
def boundaryMLE {N : ℕ} (z : Assignment N) : ℝ :=
  let q := armCount z true / N
  if q ≤ 1/2 then 0 else if logistic 1 ≤ q then 1 else Real.log (q/(1-q))


/-- Printed (37)–(40), T35: the pair term is unsigned. Both the j residual
in the pair term and the second marginal-mean factor use the i-indexed fit. -/
def printedVarianceFormula {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  ((∑ i, (marginal p (fun i z => (R i z-g i true)^2) i true/p i +
      marginal p (fun i z => (R i z-g i false)^2) i false/(1-p i) - (residualEffect p R g i)^2)) +
    (∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool,
      pairMarginal p (fun z => (R i z-g i a)*(R j z-g i b)) i j a b) -
    (∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool, armSign a*armSign b *
      (marginal p R i a-g i a)*(marginal p R j b-g i b))) / (N : ℝ)^2


/- Remaining target clauses and finite bases. -/

/-- Sharp null in Section 6.3, p. 758 and corrected footnote 22:
Y_x(z)=Y_x(0-vector) for all outcome points and every complete assignment. -/
def SharpNull {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) : Prop :=
  ∀ x z, P.outcome x z = P.outcome x (fun _ => false)

/-- T11(b), the expectation of the observational HT as misprinted:
control means are weighted by (1−pᵢ)/pᵢ. Its bias vanishes exactly under
the stated scalar cancellation, not under general C6. -/
theorem printed_obs_ht_expectation {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (hN : 0 < N) (hp : ∀ i, 0 < p i ∧ p i < 1) :
    expect p (printedObsHT p R) =
      (∑ i, (marginal p R i true-(1-p i)/p i*marginal p R i false)) / N ∧
    (expect p (printedObsHT p R) = ame p R ↔
      (∑ i, (1-2*p i)/p i*marginal p R i false) / N = 0) := by
  have hx : ∀ z, printedObsHT p R z =
      (∑ i, ((if z i = true then R i z else 0)/p i -
        (if z i = false then R i z else 0)/p i))/N := by
    intro z
    unfold printedObsHT
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases h : z i <;> simp [bit, h]
  have he : expect p (printedObsHT p R) =
      (∑ i, (marginal p R i true-(1-p i)/p i*marginal p R i false))/N := by
    rw [funext hx, expect_div, expect_sum]
    simp_rw [expect_sub, expect_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hpi : p i ≠ 0 := ne_of_gt (hp i).1
    have hqi : 1-p i ≠ 0 := ne_of_gt (sub_pos.mpr (hp i).2)
    rw [bernoulli_selection p R i true (by simpa [coin] using hpi),
      bernoulli_selection p R i false (by simpa [coin] using hqi)]
    simp only [coin, Bool.false_eq_true, ite_true, ite_false]
    field_simp
  have hs :
      (∑ i, (marginal p R i true-(1-p i)/p i*marginal p R i false)) =
      (∑ i, nodeEffect p R i) - (∑ i, (1-2*p i)/p i*marginal p R i false) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold nodeEffect
    have hpi : p i ≠ 0 := ne_of_gt (hp i).1
    field_simp
    <;> ring
  refine ⟨he, ?_⟩
  rw [he, hs, sub_div]
  unfold ame
  constructor <;> intro h <;> linarith


/-- T29(4), corrected cross-arm prefactors N²p(1−p), in the exact
product difference underlying eqs. (133)–(136), Appendix C pp. 36–37. -/
theorem epsilon_product_difference (z w : Bool) (N p yi yj h1 h0 b1 b0 : ℝ)
    (hN : N ≠ 0) (hp : p ≠ 0) (hq : 1-p ≠ 0) :
    let E := fun a y c1 c0 => bit a*(y-c1)/(N*p)-(1-bit a)*(y-c0)/(N*(1-p))
    E z yi h1 h0 * E w yj h1 h0 - E z yi b1 b0 * E w yj b1 b0 =
      bit z*bit w/(N^2*p^2)*(-yi*(h1-b1)-yj*(h1-b1)+h1^2-b1^2) +
      (1-bit z)*(1-bit w)/(N^2*(1-p)^2)*(-yi*(h0-b0)-yj*(h0-b0)+h0^2-b0^2) -
      (1-bit z)*bit w/(N^2*p*(1-p))*(-yi*(h1-b1)-yj*(h0-b0)+h0*h1-b0*b1) -
      bit z*(1-bit w)/(N^2*p*(1-p))*(-yi*(h0-b0)-yj*(h1-b1)+h0*h1-b0*b1) := by
  dsimp
  field_simp
  <;> ring


/-- T27 sparse own-treatment outcomes: only node 1 has Y=1/4+3Z₁/4. -/
def sparseTable (N : ℕ) : CircleTable N :=
  fun i z => if i.val = 0 then 1/4+3/4*bit (z i) else 0
/-- Point nodes at (i+1)N² on the x-axis with counting measure and
the sparse first-node outcome, T27. -/
def sparsePopulation (N : ℕ) : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => {planePoint (((i : ℝ)+1)*N^2) 0}
  node_nonempty := fun _ => Set.singleton_nonempty _
  zeta := ∑ i : Fin N, Measure.dirac (planePoint (((i : ℝ)+1)*N^2) 0)
  outcome := fun x z => ∑ i : Fin N, if x = planePoint (((i : ℝ)+1)*N^2) 0 then sparseTable N i z else 0
  bands := fun d => Set.Icc 0 d
/-- “b_N=⌊N^(1/12)⌋”, the bandwidth of the T27 sparse counterexample;
it diverges and is o(N^(1/6)). -/
def sparseBandwidth (N : ℕ) : ℝ := (⌊(N : ℝ)^(1/12 : ℝ)⌋₊ : ℝ)


/-- T40: arbitrary marginal law of other assignments, represented by a
probability on full vectors whose unused own coordinate is overwritten.
This allows every law on Z_{−i}, including non-Bernoulli designs. -/
def marginalLawEffect {N : ℕ} (w : Fin N → Assignment N → ℝ)
    (Y : Assignment N → ℝ) (i : Fin N) : ℝ :=
  (∑ z, w i z * Y (Function.update z i true)) -
    (∑ z, w i z * Y (Function.update z i false))

/-- T40, the pointwise additive potential-outcome contrast is gᵢ(x)
for every assignment to other nodes; eqs. (23)–(24), pp. 756–757. -/
theorem additive_potential_shift {N : ℕ} (g : Fin N → ℝ) (f : ℝ)
    (z : Assignment N) (i : Fin N) :
    ((∑ j, bit (Function.update z i true j)*g j)+f) -
      ((∑ j, bit (Function.update z i false j)*g j)+f) = g i := by
  have he :
      ((∑ j, bit (Function.update z i true j)*g j)+f) -
      ((∑ j, bit (Function.update z i false j)*g j)+f) =
      ∑ j, (bit (Function.update z i true j)*g j-bit (Function.update z i false j)*g j) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ = ∑ j : Fin N, if j = i then g i else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i
      · subst j
        simp [bit]
      · simp [Function.update_of_ne h, h]
    _ = g i := by simp

/-- T40 finite basis: a constant pointwise treatment contrast has the
same contrast under any normalized marginal law (eq. (24), p. 757). -/
theorem marginal_law_shift {N : ℕ} (w : Fin N → Assignment N → ℝ)
    (Y : Assignment N → ℝ) (i : Fin N) (δ : ℝ) (hw : (∑ z, w i z) = 1)
    (hshift : ∀ z, Y (Function.update z i true)-Y (Function.update z i false) = δ) :
    marginalLawEffect w Y i = δ := by
  unfold marginalLawEffect
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ z, w i z*δ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← mul_sub, hshift]
    _ = δ := by rw [← Finset.sum_mul, hw, one_mul]

/-- T40, full structural interpretation on finite weighted outcome points:
for EVERY marginal assignment law, τᵢₓ=gᵢ(x), τᵢ is the spatial average
of gᵢ, and AME is the node mean of those averages. No constant-p assumption. -/
theorem additive_design_invariance {N : ℕ} {A : Type*} [Fintype A]
    (w : Fin N → Assignment N → ℝ) (hw : ∀ i, (∑ z, w i z) = 1)
    (hwpos : ∀ i z, 0 ≤ w i z) (mass : A → ℝ) (band : Fin N → A → Prop)
    (ha : ∀ x, 0 ≤ mass x) (hpos : ∀ i, 0 < ∑ x, if band i x then mass x else 0)
    (g : Fin N → A → ℝ) (f : A → ℝ) :
    let Y := fun x z => (∑ j, bit (z j)*g j x)+f x
    let R := fun i z => (∑ x, if band i x then mass x*Y x z else 0) /
      (∑ x, if band i x then mass x else 0)
    (∀ i x, marginalLawEffect w (Y x) i = g i x) ∧
    (∀ i, marginalLawEffect w (R i) i =
      (∑ x, if band i x then mass x*g i x else 0)/(∑ x, if band i x then mass x else 0)) ∧
    (∑ i, marginalLawEffect w (R i) i)/N =
      (∑ i, (∑ x, if band i x then mass x*g i x else 0)/(∑ x, if band i x then mass x else 0))/N := by
  dsimp only
  have hpoint : ∀ i x, marginalLawEffect w
      (fun z => (∑ j, bit (z j)*g j x)+f x) i = g i x := by
    intro i x
    apply marginal_law_shift w _ i (g i x) (hw i)
    intro z
    exact additive_potential_shift (fun j => g j x) (f x) z i
  have hcircle : ∀ i, marginalLawEffect w
      (fun z => (∑ x, if band i x then mass x*((∑ j, bit (z j)*g j x)+f x) else 0) /
        (∑ x, if band i x then mass x else 0)) i =
      (∑ x, if band i x then mass x*g i x else 0)/(∑ x, if band i x then mass x else 0) := by
    intro i
    apply marginal_law_shift w _ i _ (hw i)
    intro z
    rw [← sub_div, ← Finset.sum_sub_distrib]
    apply congrArg (fun t : ℝ => t/(∑ x, if band i x then mass x else 0))
    apply Finset.sum_congr rfl
    intro x _
    by_cases hb : band i x
    · simp only [hb, ite_true, ← mul_sub]
      rw [additive_potential_shift]
    · simp [hb]
  refine ⟨hpoint, hcircle, ?_⟩
  simp_rw [hcircle]

/- Positive-semidefinite adjustment and coverage. -/

/-- Uniform-distance kernel also at zero cutoff: exactly I(dᵢⱼ≤h).
This avoids changing the h=0 singleton neighborhood by totalized 0/0. -/
def uniformDistanceKernel {N : ℕ} (D : Fin N → Fin N → ℝ) (h : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => if D i j ≤ h then 1 else 0)

/-- Actual Student-t density and CDF, for positive degrees of freedom;
Supplement A.7 quantiles in T7/T38. No arbitrary critical-value proxy is used. -/
def studentDensity (ν x : ℝ) : ℝ :=
  Real.Gamma ((ν+1)/2)/(Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2)) *
    (1+x^2/ν)^(-(ν+1)/2)
/-- The integral CDF of the actual Student-t density used for the
empirical-degree-of-freedom quantiles, Supplement A p. 17 (T7, T38). -/
def studentCDF (ν x : ℝ) : ℝ := ∫ t in Set.Iic x, studentDensity ν t
/-- The generalized inverse of the actual Student-t CDF,
the t critical value used in Supplement A p. 17 (T7, T38). -/
def studentQuantile (ν α : ℝ) : ℝ := sInf {x : ℝ | α ≤ studentCDF ν x}

/-- T7, exact five-node star kernel and its genuine spectral trim;
the negative eigenvector is (2,−1,−1,−1,−1) with eigenvalue −1. -/
def starKernel : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of (fun i j => if i = j ∨ i = 0 ∨ j = 0 then 1 else 0)
/-- “v=(2,−1,−1,−1,−1)”, eigenvector for the star kernel’s
negative eigenvalue −1, T7. -/
def starNegativeVector : Fin 5 → ℝ := ![2,-1,-1,-1,-1]
/-- “K^PD=K+vv′/8”, the genuine spectral trim of the five-node
star kernel, T7; cf. eq. (22), p. 756. -/
def starPD : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of (fun i j => starKernel i j+starNegativeVector i*starNegativeVector j/8)
/-- “Y=(0,1,1,−1,−1)”, fixed sharp-null outcomes on each star, T7. -/
def starY : Fin 5 → ℝ := ![0,1,1,-1,-1]
/-- Block-diagonal repetitions of the actual five-node star kernel
or its spectral trim, T7. -/
def starBlockKernel (m : ℕ) (pd : Bool) : Matrix (Fin (5*m)) (Fin (5*m)) ℝ :=
  Matrix.of (fun i j => if i.val/5 = j.val/5 then
    (if pd then starPD else starKernel) ⟨i.val%5, Nat.mod_lt _ (by omega)⟩
      ⟨j.val%5, Nat.mod_lt _ (by omega)⟩ else 0)
/-- Assignment-invariant outcome tables repeating the star’s
fixed vector (0,1,1,−1,−1), T7. -/
def starBlockTable (m : ℕ) : CircleTable (5*m) :=
  fun i _ => starY ⟨i.val%5, Nat.mod_lt _ (by omega)⟩
/-- The explicit twenty-node treated/control assignment of
T7’s finite variance-order reversal. -/
def starAssignment20 : Assignment 20 :=
  ![true,true,false,true,false, false,true,false,true,false,
    true,true,false,true,false, false,true,false,true,false]

/-- Five-node stars at (10b,0), (10b+1,0), (10b,1), (10b−1,0),
(10b,−1), the Euclidean layout of T7. Partial final stars extend to all N. -/
def starPoint {N : ℕ} (i : Fin N) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (![10*((i.val/5 : ℕ) : ℝ) +
    (if i.val%5 = 1 then 1 else if i.val%5 = 3 then -1 else 0),
    if i.val%5 = 2 then 1 else if i.val%5 = 4 then -1 else 0] : Fin 2 → ℝ)
/-- Actual point-node spatial realization with counting measure of
the repeated star outcomes, T7 and Section 2, p. 747. -/
def starPopulation (N : ℕ) : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => {starPoint i}
  node_nonempty := fun _ => Set.singleton_nonempty _
  zeta := ∑ i : Fin N, Measure.dirac (starPoint i)
  outcome := fun x _ => ∑ i : Fin N, if x = starPoint i then
    starY ⟨i.val%5, Nat.mod_lt _ (by omega)⟩ else 0
  bands := fun d => Set.Icc 0 d





/-- T7 exact adjustment arithmetic, separately from the spatial matrix
and asymptotic calculations. -/
theorem adjusted_pd_constants :
    ((4/25 : ℝ)/(101/100)) = 16/101 ∧ ((4/25 : ℝ)/(41/50)) = 8/41 ∧
    (16/101 : ℝ) < 8/41 ∧ ((18/5 : ℝ)/(6/5))/(16/5) = 15/16 ∧ (15/16 : ℝ) < 1 := by norm_num


/- Finite lemmas for the asymptotic statements. -/


/-- T18/T42 finite ratio identity underlying the Hajek linearization,
Supplement A p. 4: on two nonempty arms the centered ratio is B₁/C₁−B₀/C₀. -/
theorem hajek_ratio_identity {N : ℕ} (p : ℝ) (R : CircleTable N) (z : Assignment N)
    (hN : 0 < N) (hp : 0 < p ∧ p < 1)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false) :
    let B1 := (∑ i, bit (z i)*(R i z-barMu (fun _ => p) R true))/(N*p)
    let B0 := (∑ i, (1-bit (z i))*(R i z-barMu (fun _ => p) R false))/(N*(1-p))
    let C1 := armCount z true/(N*p)
    let C0 := armCount z false/(N*(1-p))
    hajek R z-ame (fun _ => p) R = B1/C1-B0/C0 ∧
    linearHajek (fun _ => p) R z-ame (fun _ => p) R = B1-B0 := by
  dsimp only
  have hn : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
  have hpp : p ≠ 0 := ne_of_gt hp.1
  have hq : 1-p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
  have hc1 : armCount z true ≠ 0 := ne_of_gt h1
  have hc0 : armCount z false ≠ 0 := ne_of_gt h0
  have hb1 : (∑ i, bit (z i)*(R i z-barMu (fun _ => p) R true)) =
      armCount z true*(armMean R z true-barMu (fun _ => p) R true) := by
    have he : (fun i => bit (z i)*(R i z-barMu (fun _ => p) R true)) =
        fun i => (if z i = true then R i z else 0)-(if z i = true then barMu (fun _ => p) R true else 0) := by
      funext i
      cases h : z i <;> simp [bit,h]
    rw [he, Finset.sum_sub_distrib]
    have hf : (∑ i, if z i = true then barMu (fun _ => p) R true else 0) =
        armCount z true*barMu (fun _ => p) R true := by
      unfold armCount
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [hf]
    unfold armMean
    field_simp
  have hb0 : (∑ i, (1-bit (z i))*(R i z-barMu (fun _ => p) R false)) =
      armCount z false*(armMean R z false-barMu (fun _ => p) R false) := by
    have he : (fun i => (1-bit (z i))*(R i z-barMu (fun _ => p) R false)) =
        fun i => (if z i = false then R i z else 0)-(if z i = false then barMu (fun _ => p) R false else 0) := by
      funext i
      cases h : z i <;> simp [bit,h]
    rw [he, Finset.sum_sub_distrib]
    have hf : (∑ i, if z i = false then barMu (fun _ => p) R false else 0) =
        armCount z false*barMu (fun _ => p) R false := by
      unfold armCount
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [hf]
    unfold armMean
    field_simp
  constructor
  · rw [hb1,hb0, ← barMu_difference]
    unfold hajek
    field_simp
    ring
  · unfold linearHajek augmented
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
      nsmul_eq_mul,Finset.card_univ,Fintype.card_fin,← Finset.sum_div]
    rw [← barMu_difference]
    field_simp
    ring


/-- Under C1, a selected off-diagonal product has the signed conditional
arm expansion in corrected Lemma C.6, Supplement A p. 30. -/
theorem residual_pair_moment {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i j : Fin N) (hij : i ≠ j)
    (hp : ∀ k, 0 < p k ∧ p k < 1) :
    expect p (fun z => residualContrast p R g i z*residualContrast p R g j z) =
      ∑ a : Bool, ∑ b : Bool, armSign a*armSign b*pairMarginal p
        (fun z => (R i z-g i a)*(R j z-g j b)) i j a b := by
  have he : (fun z => residualContrast p R g i z*residualContrast p R g j z) =
      fun z => ∑ a : Bool, ∑ b : Bool, (armSign a*armSign b)*
        ((if z i = a ∧ z j = b then (R i z-g i a)*(R j z-g j b) else 0)/
          (coin (p i) a*coin (p j) b)) := by
    have hpi : p i ≠ 0 := ne_of_gt (hp i).1
    have hpj : p j ≠ 0 := ne_of_gt (hp j).1
    have hqi : 1-p i ≠ 0 := ne_of_gt (sub_pos.mpr (hp i).2)
    have hqj : 1-p j ≠ 0 := ne_of_gt (sub_pos.mpr (hp j).2)
    funext z
    cases hi : z i <;> cases hj : z j <;>
      simp [residualContrast, bit, armSign, coin, Fintype.sum_bool, hi, hj]
      <;> field_simp [hpi,hpj,hqi,hqj] <;> ring
  rw [he, expect_sum]
  simp_rw [expect_sum, expect_mul, expect_div]
  rfl


/-- The centered linearized Hájek summands have total mean zero,
the cancellation used in Lemma C.6, Supplement A p. 30. -/
theorem linear_hajek_total_mean {N : ℕ} (p : ℝ) (R : CircleTable N)
    (hN : 0 < N) (hp : 0 < p ∧ p < 1) :
    (∑ i, expect (fun _ => p) (residualContrast (fun _ => p) R (fun _ a => barMu (fun _ => p) R a) i)) = 0 := by
  simp_rw [residualContrast_mean (fun _ => p) R _ _ (fun _ => hp)]
  unfold residualEffect nodeEffect barMu
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hn : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
  field_simp
  ring


/-- T44 finite Lemma C.6 (Appendix C p. 30): under C1 alone, the
variance equals the uncentered diagonal and ALL off-diagonal arm products.
The product-of-means terms cancel because ∑(τᵢ−AME)=0. -/
theorem ned_exact_linear_variance {N : ℕ} (p : ℝ) (R : CircleTable N)
    (hN : 0 < N) (hp : 0 < p ∧ p < 1) :
    variance (fun _ => p) (linearHajek (fun _ => p) R) =
      secondMomentBound (fun _ => p) R (fun _ => Finset.univ) (fun _ a => barMu (fun _ => p) R a) := by
  let g : Fin N → Bool → ℝ := fun _ a => barMu (fun _ => p) R a
  let T := residualContrast (fun _ => p) R g
  have hm : (∑ i, expect (fun _ => p) (T i)) = 0 := linear_hajek_total_mean p R hN hp
  have he : linearHajek (fun _ => p) R = fun z =>
      (∑ i, T i z)/N + ame (fun _ => p) R := by
    funext z
    unfold linearHajek augmented
    have hrow : (∑ i, (g i true-g i false+bit (z i)*(R i z-g i true)/p -
        (1-bit (z i))*(R i z-g i false)/(1-p))) = ∑ i, ((g i true-g i false)+T i z) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [T, residualContrast]
      ring
    rw [hrow, Finset.sum_add_distrib, add_div]
    simp only [g, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    have hn : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
    rw [mul_div_cancel_left₀ _ hn, barMu_difference]
    ring
  have hvconst : ∀ X : Assignment N → ℝ, ∀ c : ℝ,
      variance (fun _ => p) (fun z => X z+c) = variance (fun _ => p) X := by
    intro X c
    have heprod : (fun z => (X z+c)*(X z+c)) =
        fun z => X z*X z+2*c*X z+c*c := by funext z; ring
    unfold variance cov
    rw [heprod, expect_add, expect_add, expect_mul, expect_const, expect_add, expect_const]
    ring
  rw [he, hvconst, variance_div, variance_sum]
  have hc : (∑ i, ∑ j, cov (fun _ => p) (T i) (T j)) =
      ∑ i, ∑ j, expect (fun _ => p) (fun z => T i z*T j z) := by
    unfold cov
    simp only [Finset.sum_sub_distrib]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, hm]
    simp
  rw [hc]
  unfold secondMomentBound
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [show expect (fun _ => p) (fun z => T i z*T i z) =
      marginal (fun _ => p) (fun i z => (R i z-g i true)^2) i true/p +
      marginal (fun _ => p) (fun i z => (R i z-g i false)^2) i false/(1-p) by
        simpa only [pow_two] using residual_square_moment (fun _ => p) R g i hp]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact residual_pair_moment (fun _ => p) R g i j (Finset.ne_of_mem_erase hj).symm (fun _ => hp)


/-- T6(a), marginalized node effects obey the same actual bin-mass
aggregation as realized averages. Node-specific bin masses are retained. -/
theorem marginal_bin_average {N m : ℕ} (p : Fin N → ℝ)
    (R : Fin m → CircleTable N) (a : Fin N → Fin m → ℝ) (i : Fin N) (arm : Bool) :
    marginal p (fun i z => finiteAverage (a i) (fun k => R k i z)) i arm =
      finiteAverage (a i) (fun k => marginal p (R k) i arm) := by
  have hx : ∀ z,
      (if z i = arm then finiteAverage (a i) (fun k => R k i z) else 0) =
      (∑ k, a i k*(if z i = arm then R k i z else 0))/(∑ k, a i k) := by
    intro z
    by_cases h : z i = arm
    · simp [h, finiteAverage]
    · simp [h]
  unfold marginal
  simp_rw [hx]
  rw [expect_div, expect_sum]
  simp_rw [expect_mul]
  unfold finiteAverage
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- T6(a), the marginalized whole-region effect is the actual mass
average of bin effects, and AME is the mean of those node-specific averages. -/
theorem bin_effect_aggregation {N m : ℕ} (p : Fin N → ℝ)
    (R : Fin m → CircleTable N) (a : Fin N → Fin m → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (ha : ∀ i k, 0 < a i k) :
    let combined := fun i z => finiteAverage (a i) (fun k => R k i z)
    (∀ i, nodeEffect p combined i = finiteAverage (a i) (fun k => nodeEffect p (R k) i)) ∧
    ame p combined = (∑ i, finiteAverage (a i) (fun k => nodeEffect p (R k) i))/N := by
  dsimp only
  have hn : ∀ i, nodeEffect p (fun i z => finiteAverage (a i) (fun k => R k i z)) i =
      finiteAverage (a i) (fun k => nodeEffect p (R k) i) := by
    intro i
    unfold nodeEffect
    rw [marginal_bin_average, marginal_bin_average]
    unfold finiteAverage
    rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact (mul_sub _ _ _).symm
  refine ⟨hn, ?_⟩
  unfold ame
  simp_rw [hn]

/-- T40, eqs. (23)–(25), for the paper's general spatial measure and
EVERY marginal design law. This keeps the integral in (25), in addition
to the separately proved finite-outcome version. -/
theorem additive_spatial_design_invariance {N : ℕ} {A : Type*}
    [MetricSpace A] [MeasurableSpace A] (P : SpatialPopulation N A) (d : ℝ)
    (w : Fin N → Assignment N → ℝ) (hw : ∀ i, (∑ z, w i z) = 1)
    (hwpos : ∀ i z, 0 ≤ w i z) (g : Fin N → A → ℝ) (f : A → ℝ)
    (hY : ∀ x z, P.outcome x z = (∑ j, bit (z j)*g j x)+f x)
    (hWD : WellDefined P d) :
    (∀ i x, marginalLawEffect w (P.outcome x) i = g i x) ∧
    (∀ i, marginalLawEffect w (circleAverage P d i) i =
      (∫ x in region P i d, g i x ∂P.zeta)/(P.zeta (region P i d)).toReal) ∧
    (∑ i, marginalLawEffect w (circleAverage P d i) i)/N =
      (∑ i, (∫ x in region P i d, g i x ∂P.zeta)/(P.zeta (region P i d)).toReal)/N := by
  have hshift : ∀ i z x,
      P.outcome x (Function.update z i true)-P.outcome x (Function.update z i false) = g i x := by
    intro i z x
    rw [hY, hY]
    exact additive_potential_shift (fun j => g j x) (f x) z i
  have hpoint : ∀ i x, marginalLawEffect w (P.outcome x) i = g i x := by
    intro i x
    apply marginal_law_shift w _ i _ (hw i)
    intro z
    exact hshift i z x
  have hcircle : ∀ i, marginalLawEffect w (circleAverage P d i) i =
      (∫ x in region P i d, g i x ∂P.zeta)/(P.zeta (region P i d)).toReal := by
    intro i
    apply marginal_law_shift w _ i _ (hw i)
    intro z
    unfold circleAverage
    rw [← sub_div, ← integral_sub ((hWD i).2.2.2 _) ((hWD i).2.2.2 _)]
    simp_rw [hshift]
  refine ⟨hpoint, hcircle, ?_⟩
  simp_rw [hcircle]


/-- Literal unsigned second-moment upper bound in printed Proposition 4,
Supplement A p. 16. The j residual deliberately retains the printed i fit. -/
def printedSecondMomentBound {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  ((∑ i, (marginal p (fun i z => (R i z-g i true)^2) i true/p i +
      marginal p (fun i z => (R i z-g i false)^2) i false/(1-p i))) +
    ∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool,
      pairMarginal p (fun z => (R i z-g i a)*(R j z-g i b)) i j a b)/(N : ℝ)^2


/-- T15(b–c) with node-dependent supported radii, including empty shells.
This retains the correction's R_i(D), rather than requiring every node
to have positive mass at every named radius. -/
theorem supported_shell_identity {A : Type*} [Fintype A] {m N : ℕ}
    (mass : A → ℝ) (shell : Fin N → A → Fin m) (δ : Fin N → A → ℝ)
    (ha : ∀ x, 0 ≤ mass x) (hpos : 0 < ∑ x, mass x) :
    (∀ i, finiteAverage mass (δ i) =
      ∑ k ∈ Finset.univ.filter (fun k => 0 < supportedShellMass mass shell i k),
        supportedShellMass mass shell i k/(∑ x, mass x) *
          ((∑ x, if shell i x = k then mass x*δ i x else 0)/supportedShellMass mass shell i k)) ∧
    (∀ w : Fin m → ℝ,
      (∀ i k, supportedShellMass mass shell i k/(∑ x, mass x) = w k) →
      (∑ i, finiteAverage mass (δ i))/N = ∑ k, w k *
        ((∑ i, (∑ x, if shell i x = k then mass x*δ i x else 0)/
          supportedShellMass mass shell i k)/N)) := by
  exact shell_mass_identity mass shell δ ha hpos

/-- T14 witness 2 uses intervention points (0,0),(3,0) and outcome
atoms (0,4),(3,4),(3,−4), with the paper's ordinary Euclidean distance. -/
def shellNodePoint (i : Fin 2) : EuclideanSpace ℝ (Fin 2) :=
  planePoint (3*(i : ℝ)) 0
/-- The three Euclidean outcome points (0,4),(3,4),(3,−4), T14. -/
def shellAtomPoint (x : Fin 3) : EuclideanSpace ℝ (Fin 2) :=
  if x = 0 then planePoint 0 4 else if x = 1 then planePoint 3 4 else planePoint 3 (-4)
/-- Two point nodes (0,0),(3,0), counting measure on the three
outcome atoms and the fixed additive outcome schedule, T14. -/
def shellSpatialPopulation (D : Set ℝ) : SpatialPopulation 2 (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => {shellNodePoint i}
  node_nonempty := fun _ => Set.singleton_nonempty _
  zeta := ∑ x : Fin 3, Measure.dirac (shellAtomPoint x)
  outcome := fun y z => 1 + ∑ x : Fin 3,
    if y = shellAtomPoint x then shellWitnessOutcome x z-1 else 0
  bands := fun _ => D

/-- Euclidean distances of the T14 witness equal its printed 3-4-5 table. -/
theorem shell_atom_distances (i : Fin 2) (x : Fin 3) :
    nodeDistance (shellSpatialPopulation {4}) i (shellAtomPoint x) = shellWitnessDistance i x := by
  simp only [nodeDistance, shellSpatialPopulation, Metric.infDist_singleton]
  fin_cases i <;> fin_cases x <;>
    norm_num [shellNodePoint, shellAtomPoint, shellWitnessDistance, planePoint,
      EuclideanSpace.dist_eq, Fin.sum_univ_succ]


/-- The three support points in T14 are distinct Euclidean points. -/
theorem shell_atom_injective : Function.Injective shellAtomPoint := by
  intro x y h
  have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
  have h1 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) h
  fin_cases x <;> fin_cases y <;> norm_num [shellAtomPoint, planePoint] at *


/-- The fixed spatial field gives exactly the tabulated potential outcome at each atom. -/
theorem shell_outcome_at_atom (x : Fin 3) (z : Assignment 2) :
    (shellSpatialPopulation {4}).outcome (shellAtomPoint x) z = shellWitnessOutcome x z := by
  change 1+(∑ y : Fin 3, if shellAtomPoint x = shellAtomPoint y then shellWitnessOutcome y z-1 else 0) = _
  simp only [shell_atom_injective.eq_iff]
  simp


/-- The spatial average in T14 equals its distance table for every measurable band. -/
theorem shell_spatial_table (D : Set ℝ) (hD : MeasurableSet D) :
    circleAverage (shellSpatialPopulation D) 0 = shellWitnessTable (fun r => r ∈ D) := by
  funext i z
  have hs : MeasurableSet (region (shellSpatialPopulation D) i 0) := by
    simp only [region, nodeDistance, shellSpatialPopulation, Metric.infDist_singleton]
    exact hD.preimage (measurable_id.dist measurable_const)
  have hatom : ∀ x : Fin 3, shellAtomPoint x ∈ region (shellSpatialPopulation D) i 0 ↔
      shellWitnessDistance i x ∈ D := by
    intro x
    change nodeDistance (shellSpatialPopulation D) i (shellAtomPoint x) ∈ D ↔ _
    have he : nodeDistance (shellSpatialPopulation D) i (shellAtomPoint x) =
      nodeDistance (shellSpatialPopulation {4}) i (shellAtomPoint x) := rfl
    rw [he, shell_atom_distances]
  have hout : ∀ x : Fin 3, (shellSpatialPopulation D).outcome (shellAtomPoint x) z = shellWitnessOutcome x z := by
    intro x
    exact shell_outcome_at_atom x z
  have hi : ∀ x : Fin 3, Integrable (fun y => (shellSpatialPopulation D).outcome y z)
      ((Measure.dirac (shellAtomPoint x)).restrict (region (shellSpatialPopulation D) i 0)) := by
    intro x
    exact (integrable_dirac (by simp)).restrict
  have hr : ((∑ x : Fin 3, Measure.dirac (shellAtomPoint x)).restrict (region (shellSpatialPopulation D) i 0)) =
      ∑ x : Fin 3, (Measure.dirac (shellAtomPoint x)).restrict (region (shellSpatialPopulation D) i 0) := by
    simpa only [Measure.restrictₗ_apply] using map_sum (Measure.restrictₗ (region (shellSpatialPopulation D) i 0))
      (fun x : Fin 3 => Measure.dirac (shellAtomPoint x)) Finset.univ
  have hnum : (∫ y in region (shellSpatialPopulation D) i 0, (shellSpatialPopulation D).outcome y z
      ∂(shellSpatialPopulation D).zeta) =
      ∑ x : Fin 3, if shellWitnessDistance i x ∈ D then shellWitnessOutcome x z else 0 := by
    change (∫ y, (shellSpatialPopulation D).outcome y z
      ∂(∑ x : Fin 3, Measure.dirac (shellAtomPoint x)).restrict (region (shellSpatialPopulation D) i 0)) = _
    rw [hr, integral_finsetSum_measure (fun x _ => hi x)]
    simp_rw [setIntegral_dirac, hatom, hout]
  have hmass : (shellSpatialPopulation D).zeta (region (shellSpatialPopulation D) i 0) =
      ∑ x : Fin 3, if shellWitnessDistance i x ∈ D then (1 : ENNReal) else 0 := by
    change (∑ x : Fin 3, Measure.dirac (shellAtomPoint x)) (region (shellSpatialPopulation D) i 0) = _
    rw [Measure.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro x _
    rw [Measure.dirac_apply]
    have he : nodeDistance (shellSpatialPopulation D) i (shellAtomPoint x) = shellWitnessDistance i x := shell_atom_distances i x
    simp only [region, Set.mem_setOf_eq]
    change (if nodeDistance (shellSpatialPopulation D) i (shellAtomPoint x) ∈ D then (1 : ENNReal) else 0) = _
    rw [he]
  unfold circleAverage shellWitnessTable
  rw [hnum, hmass, ENNReal.toReal_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  · intro x _
    split_ifs <;> simp


/-- The used Euclidean shells are measurable, as required by the average (2). -/
theorem shell_region_measurable (D : Set ℝ) (hD : MeasurableSet D) (i : Fin 2) :
    MeasurableSet (region (shellSpatialPopulation D) i 0) := by
  simp only [region, nodeDistance, shellSpatialPopulation, Metric.infDist_singleton]
  exact hD.preimage (measurable_id.dist measurable_const)


/-- The actual spatial shell mass is the count of supported T14 atoms in that shell. -/
theorem shell_spatial_mass (D : Set ℝ) (i : Fin 2) :
    (shellSpatialPopulation D).zeta (region (shellSpatialPopulation D) i 0) =
      ∑ x : Fin 3, if shellWitnessDistance i x ∈ D then (1 : ENNReal) else 0 := by
  change (∑ x : Fin 3, Measure.dirac (shellAtomPoint x)) (region (shellSpatialPopulation D) i 0) = _
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [Measure.dirac_apply]
  have he : nodeDistance (shellSpatialPopulation D) i (shellAtomPoint x) =
    shellWitnessDistance i x := shell_atom_distances i x
  simp only [region, Set.mem_setOf_eq]
  change (if nodeDistance (shellSpatialPopulation D) i (shellAtomPoint x) ∈ D then (1 : ENNReal) else 0) = _
  rw [he]


/-- A band containing a supported atom at each node gives a positive finite, integrable average. -/
theorem shell_wellDefined (D : Set ℝ) (hD : MeasurableSet D)
    (hhit : ∀ i : Fin 2, ∃ x : Fin 3, shellWitnessDistance i x ∈ D) :
    WellDefined (shellSpatialPopulation D) 0 := by
  intro i
  refine ⟨shell_region_measurable D hD i, ?_, ?_, ?_⟩
  · rw [shell_spatial_mass]
    obtain ⟨x,hx⟩ := hhit i
    have hle := Finset.single_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (Fin 3))) =>
      show 0 ≤ (if shellWitnessDistance i y ∈ D then (1 : ENNReal) else 0) from zero_le)
      (Finset.mem_univ x)
    rw [if_pos hx] at hle
    exact lt_of_lt_of_le (by norm_num) hle
  · rw [shell_spatial_mass]
    simp only [Fin.sum_univ_succ]
    split_ifs <;> norm_num
  · intro z
    have hi : Integrable (fun y => (shellSpatialPopulation D).outcome y z)
        (∑ x : Fin 3, Measure.dirac (shellAtomPoint x)) := by
      rw [integrable_finsetSum_measure]
      intro x _
      exact integrable_dirac (by simp)
    exact hi.integrableOn


/-- All potential outcomes of T14's spatial field obey the strict C2 bound b=3. -/
theorem shell_outcome_bound : ∀ y z, |(shellSpatialPopulation {4}).outcome y z| < 3 := by
  intro y z
  by_cases h : ∃ x : Fin 3, y = shellAtomPoint x
  · obtain ⟨x,rfl⟩ := h
    rw [shell_outcome_at_atom]
    fin_cases x <;> cases h0 : z 0 <;> cases h1 : z 1 <;>
      norm_num [shellWitnessOutcome, shellWitnessEffect, bit, Fin.sum_univ_two, h0, h1]
  · have hn : ∀ x : Fin 3, y ≠ shellAtomPoint x := by
      intro x hx
      exact h ⟨x,hx⟩
    change |1+(∑ x : Fin 3, if y = shellAtomPoint x then shellWitnessOutcome x z-1 else 0)| < 3
    simp [hn]


/-- T14, full Euclidean spatial counterexample. Every used shell has
positive mass. The disk and donut have AME 1/6 although all common
weighted combinations of their radius-4 and radius-5 AMEs vanish.
The finite distance-table computation is proved separately. -/
theorem spatial_shell_counterexample :
    WellDefined (shellSpatialPopulation {4}) 0 ∧
    WellDefined (shellSpatialPopulation {5}) 0 ∧
    WellDefined (shellSpatialPopulation (Set.Icc 4 5)) 0 ∧
    WellDefined (shellSpatialPopulation (Set.Icc 0 5)) 0 ∧
    (∀ x z, |(shellSpatialPopulation {4}).outcome x z| < 3) ∧
    ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {4}) 0) = 0 ∧
    ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {5}) 0) = 0 ∧
    ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation (Set.Icc 4 5)) 0) = 1/6 ∧
    ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation (Set.Icc 0 5)) 0) = 1/6 ∧
    (∀ w4 w5 : ℝ,
      w4*ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {4}) 0) +
      w5*ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {5}) 0) ≠
        ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation (Set.Icc 4 5)) 0)) := by
  have h4hit : ∀ i : Fin 2, ∃ x : Fin 3, shellWitnessDistance i x ∈ ({4} : Set ℝ) := by
    intro i
    fin_cases i
    · exact ⟨0, by norm_num [shellWitnessDistance]⟩
    · exact ⟨1, by norm_num [shellWitnessDistance]⟩
  have h5hit : ∀ i : Fin 2, ∃ x : Fin 3, shellWitnessDistance i x ∈ ({5} : Set ℝ) := by
    intro i
    fin_cases i
    · exact ⟨1, by norm_num [shellWitnessDistance]⟩
    · exact ⟨0, by norm_num [shellWitnessDistance]⟩
  have hbandhit : ∀ i : Fin 2, ∃ x : Fin 3, shellWitnessDistance i x ∈ Set.Icc 4 5 := by
    intro i
    obtain ⟨x,hx⟩ := h4hit i
    simp only [Set.mem_singleton_iff] at hx
    exact ⟨x, by rw [hx]; norm_num⟩
  have hdiskhit : ∀ i : Fin 2, ∃ x : Fin 3, shellWitnessDistance i x ∈ Set.Icc 0 5 := by
    intro i
    obtain ⟨x,hx⟩ := h4hit i
    simp only [Set.mem_singleton_iff] at hx
    exact ⟨x, by rw [hx]; norm_num⟩
  have htable : shellWitnessTable (fun r => r ∈ Set.Icc 0 5) = shellWitnessTable (fun r => r ∈ Set.Icc 4 5) := by
    have he : ∀ i x, (shellWitnessDistance i x ∈ Set.Icc 0 5) ↔
        shellWitnessDistance i x ∈ Set.Icc 4 5 := by
      intro i x
      fin_cases i <;> fin_cases x <;> norm_num [shellWitnessDistance]
    unfold shellWitnessTable
    simp_rw [he]
    funext i z
    congr 1
    all_goals
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : shellWitnessDistance i x ∈ Set.Icc 4 5 <;> simp [hx]
  obtain ⟨h4,h5,hband,hw⟩ := finite_shell_certificate
  refine ⟨shell_wellDefined {4} (measurableSet_singleton 4) h4hit,
    shell_wellDefined {5} (measurableSet_singleton 5) h5hit,
    shell_wellDefined _ measurableSet_Icc hbandhit,
    shell_wellDefined _ measurableSet_Icc hdiskhit, shell_outcome_bound, ?_, ?_, ?_, ?_, ?_⟩
  · rw [shell_spatial_table _ (measurableSet_singleton 4)]
    simpa only [Set.mem_singleton_iff] using h4
  · rw [shell_spatial_table _ (measurableSet_singleton 5)]
    simpa only [Set.mem_singleton_iff] using h5
  · rw [shell_spatial_table _ measurableSet_Icc]
    exact hband
  · rw [shell_spatial_table _ measurableSet_Icc, htable]
    exact hband
  · simp_rw [shell_spatial_table {4} (measurableSet_singleton 4),
      shell_spatial_table {5} (measurableSet_singleton 5),
      shell_spatial_table (Set.Icc 4 5) measurableSet_Icc]
    exact hw


/-- T14: the complete Euclidean three-atom disk/donut counterexample
to the uniform/common-kernel interpretation after (26), p. 757.
Includes well-defined averages and the actual spatial-integral contrasts. -/
theorem shell_counterexample :
    WellDefined (shellSpatialPopulation {4}) 0 ∧
    WellDefined (shellSpatialPopulation {5}) 0 ∧
    WellDefined (shellSpatialPopulation (Set.Icc 4 5)) 0 ∧
    WellDefined (shellSpatialPopulation (Set.Icc 0 5)) 0 ∧
    (∀ x z, |(shellSpatialPopulation {4}).outcome x z| < 3) ∧
    ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {4}) 0) = 0 ∧
    ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {5}) 0) = 0 ∧
    ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation (Set.Icc 4 5)) 0) = 1/6 ∧
    ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation (Set.Icc 0 5)) 0) = 1/6 ∧
    (∀ w4 w5 : ℝ,
      w4*ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {4}) 0) +
      w5*ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation {5}) 0) ≠
        ame (fun _ => 1/2) (circleAverage (shellSpatialPopulation (Set.Icc 4 5)) 0)) := by
  exact spatial_shell_counterexample

/-- T5 case B: normalized angular coordinate about a disk’s center,
giving binary outcomes 1{θ/(2π)<q_j(z_i)}. -/
def angularFraction (c x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  let θ := Complex.arg ((x 0-c 0 : ℝ) + (x 1-c 1 : ℝ)*Complex.I)
  (if θ < 0 then θ+2*Real.pi else θ)/(2*Real.pi)
/-- Disk centers (0,0),(100,0) in the actual Euclidean plane, T5 case B. -/
def areaBinaryCenter (i : Fin 2) : EuclideanSpace ℝ (Fin 2) := planePoint (100*(i : ℝ)) 0
/-- The binary angular-sector shares q₀=.1, q₁=.02 in the node
and .1092 outside it, T5 case B. -/
def areaBinaryShare (c x : EuclideanSpace ℝ (Fin 2)) (a : Bool) : ℝ :=
  if a then (if dist x c ≤ 1 then 1/50 else 273/2500) else 1/10
/-- Actual radius-one disk nodes with planar area measure and
binary angular-sector outcomes, T5 case B; eq. (2), p. 747. -/
def areaBinaryPopulation : SpatialPopulation 2 (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => Metric.closedBall (areaBinaryCenter i) 1
  node_nonempty := fun i => ⟨areaBinaryCenter i, Metric.mem_closedBall_self (by norm_num)⟩
  zeta := volume
  outcome := fun x z =>
    if dist x (areaBinaryCenter 0) ≤ 6 then
      (if angularFraction (areaBinaryCenter 0) x < areaBinaryShare (areaBinaryCenter 0) x (z 0) then 1 else 0)
    else if dist x (areaBinaryCenter 1) ≤ 6 then
      (if angularFraction (areaBinaryCenter 1) x < areaBinaryShare (areaBinaryCenter 1) x (z 1) then 1 else 0)
    else 0
  bands := fun d => if d = 0 then {0} else if d = 6 then Set.Icc 0 5 else Set.Ioc (d-1) d


/-- T12: fixed outcomes under the sharp null at eight nodes. Node i+1
has y_i=2^i/128 for every assignment, exactly the stated witness. -/
def eightNodeNullTable : CircleTable 8 := fun i _ => (2 : ℝ)^i.val/128
/-- Eight Euclidean point nodes at (3(i+1),0) for zero-based i, T12B. -/
def eightNodeNullPoint (i : Fin 8) : EuclideanSpace ℝ (Fin 2) := planePoint (3*((i : ℝ)+1)) 0
/-- Eight point nodes with counting measure and fixed
sharp-null outcomes 2^i/128 for zero-based i, T12B. -/
def eightNodeNullPopulation : SpatialPopulation 8 (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => {eightNodeNullPoint i}
  node_nonempty := fun _ => Set.singleton_nonempty _
  zeta := ∑ i : Fin 8, Measure.dirac (eightNodeNullPoint i)
  outcome := fun x z => ∑ i : Fin 8, if x = eightNodeNullPoint i then eightNodeNullTable i z else 0
  bands := fun d => Set.Icc 0 d
/-- The explicit all-control observed assignment, T12A;
it has positive probability under independent half coins. -/
def eightNodeObserved : Assignment 8 := fun _ => false
/-- The explicit seven-treated resampled assignment, T12A;
it has positive probability under independent half coins. -/
def eightNodeResampled : Assignment 8 := fun i => decide (i.val < 7)
/-- The observed all-control vector and the stipulated resample
vectors for the missing-absolute-value witness, T12A. -/
def eightNodeMCDraws : Fin 101 → Assignment 8 :=
  fun r => if r = 0 then eightNodeObserved else eightNodeResampled


/-- T16A/T17(b): the rectangle construction with arbitrary separation
L≥2, keeping the effect radius exactly 2. This parametrization shows why
no universal cutoff can follow from the effect radius alone. -/
def polygonRangeFamily (L : ℝ) (hL : 2 ≤ L) :
    SpatialPopulation 3 (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => if i = 0 then rectangle 0 1 0 1
    else if i = 1 then rectangle L (L+1) 0 1 else rectangle 0 (L+1) 2 3
  node_nonempty := by
    intro i
    fin_cases i
    · exact ⟨planePoint 0 0, by norm_num [rectangle, planePoint]⟩
    · exact ⟨planePoint (L+1) 0, by norm_num [rectangle, planePoint] <;> linarith⟩
    · exact ⟨planePoint 0 2, by norm_num [rectangle, planePoint] <;> linarith⟩
  zeta := volume
  outcome := fun x z => if x ∈ rectangle 0 1 0 1 ∪ rectangle L (L+1) 0 1 then bit (z 2) else 0
  bands := fun d => Set.Icc 0 d


end
end AronowAudit.P004

