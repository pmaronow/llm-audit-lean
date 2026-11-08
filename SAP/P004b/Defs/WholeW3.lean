import Mathlib
import SAP.P004b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

/-- The five independent terms of (114)--(120), with generic arm denominators. -/
def wholeHacFive {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) (A B : ℝ) : ℝ :=
  (∑ i, bit (z i) * e i ^ 2) / A ^ 2 +
  (∑ i, (1-bit (z i)) * e i ^ 2) / B ^ 2 +
  (∑ i, ∑ j ∈ Finset.univ.erase i, bit (z i)*bit (z j)*e i*e j*Q i j) / A ^ 2 -
  2*(∑ i, ∑ j ∈ Finset.univ.erase i, (1-bit (z i))*bit (z j)*e i*e j*Q i j) / (A*B) +
  (∑ i, ∑ j ∈ Finset.univ.erase i, (1-bit (z i))*(1-bit (z j))*e i*e j*Q i j) / B ^ 2

/-- V1 defined by the independent five-term display, rather than by its row identity. -/
def wholeV1Five {N : ℕ} (p : ℝ) (R : CircleTable N)
    (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (b : ℝ) (z : Assignment N) : ℝ :=
  wholeHacFive z (residual R z) (distanceKernel D K b) (N*p) (N*(1-p))

/-- Coverage requires two nonempty arms and a strictly positive variance. The
quotient is used only on this event; invalid intervals do not count as coverage. -/
def wholeCovered {N : ℕ} (p : ℝ) (R : CircleTable N)
    (Q : Matrix (Fin N) (Fin N) ℝ) (lo hi : ℝ) (z : Assignment N) : Prop :=
  ValidInterval R Q z ∧
  lo ≤ (hajek R z-ame (fun _ => p) R)/Real.sqrt (kernelVariance z (residual R z) Q) ∧
  (hajek R z-ame (fun _ => p) R)/Real.sqrt (kernelVariance z (residual R z) Q) ≤ hi

/-- A finite extension at N=0, which never enters the positive-size witness facts. -/
def wholeFirst {N : ℕ} (z : Assignment N) : Bool :=
  if h : 0 < N then z ⟨0, h⟩ else false

def wholeSparseQ {N : ℕ} (z : Assignment N) : ℝ := armCount z (wholeFirst z)
def wholeSparseR (N : ℕ) : CircleTable N := circleAverage (sparsePopulation N) 1
def wholeSparseQmat (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  distanceKernel (nodeSeparation (sparsePopulation N)) uniformKernel (sparseBandwidth N)
def wholeSparseHac (N : ℕ) (z : Assignment N) : ℝ :=
  kernelVariance z (residual (wholeSparseR N) z) (wholeSparseQmat N)
def wholeSparseV1 (N : ℕ) (z : Assignment N) : ℝ :=
  wholeV1Five (1/2) (wholeSparseR N) (nodeSeparation (sparsePopulation N)) uniformKernel
    (sparseBandwidth N) z
def wholeSparseV2 (N : ℕ) : Assignment N → ℝ :=
  nedV2 (1/2) (wholeSparseR N) (nodeSeparation (sparsePopulation N)) uniformKernel (sparseBandwidth N)
def wholeSparseT (N : ℕ) (z : Assignment N) : ℝ :=
  (hajek (wholeSparseR N) z-ame (fun _ => 1/2) (wholeSparseR N))/Real.sqrt (wholeSparseHac N z)

/-- Conditional probabilities given the first coin. For positive N its mass is 1/2. -/
def wholeSparseCond (N : ℕ) (a : Bool) (E : Assignment N → Prop) : ℝ :=
  2 * prob (fun _ => 1/2) (fun z => wholeFirst z = a ∧ E z)

/-- Counting-measure disk formula; every nonnegative-radius disk has positive finite mass. -/
def WholeSparseDisks : Prop :=
  ∀ N (hN : 0 < N), ∀ d : ℝ, 0 ≤ d →
    WellDefined (sparsePopulation N) d ∧
    ∀ i z, circleAverage (sparsePopulation N) d i z =
      if nodeSeparation (sparsePopulation N) i ⟨0, hN⟩ ≤ d then
        (1/4+3/4*bit (wholeFirst z)) /
          ((ball (nodeSeparation (sparsePopulation N)) i d).card : ℝ)
      else 0

/-- Explicit admissible NED coefficients: the compactly supported step at
each distance, and the identically zero coefficient at d=1. -/
def WholeSparseNED : Prop :=
  (∀ d : ℝ, 0 ≤ d → NEDConditions sparsePopulation (1/2) d) ∧
  (∀ d : ℝ, 0 ≤ d → ∀ N (i : Fin N) s, 0 ≤ s →
    l2Norm (fun _ => 1/2) (fun z => circleAverage (sparsePopulation N) d i z -
      conditionOn (fun _ => 1/2) (ball (nodeSeparation (sparsePopulation N)) i s)
        (circleAverage (sparsePopulation N) d i) z) ≤ if s ≤ d then 1 else 0) ∧
  (∀ N (i : Fin N) s, 0 ≤ s →
    l2Norm (fun _ => 1/2) (fun z => circleAverage (sparsePopulation N) 1 i z -
      conditionOn (fun _ => 1/2) (ball (nodeSeparation (sparsePopulation N)) i s)
        (circleAverage (sparsePopulation N) 1 i) z) = 0)

def WholeSparseExactMoments : Prop :=
  ∀ N : ℕ, 3 ≤ N →
    kernelHomophily sparsePopulation (1/2) 1 uniformKernel sparseBandwidth N =
      9*((N : ℝ)-1)/(16*(N : ℝ)^2) ∧
    variance (fun _ => 1/2) (linearHajek (fun _ => 1/2) (wholeSparseR N)) =
      25*((N : ℝ)-1)/(16*(N : ℝ)^3)

def WholeSparseCountLaw : Prop :=
  ∀ N : ℕ, 3 ≤ N →
    (∀ a : Bool, ∀ k : ℕ, k ≤ N-1 →
      wholeSparseCond N a (fun z => wholeSparseQ z = (k+1 : ℕ)) =
        (Nat.choose (N-1) k : ℝ) / (2 : ℝ)^(N-1)) ∧
    prob (fun _ : Fin N => 1/2) (fun z => ¬ (2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ)-1)) =
      4/(2 : ℝ)^N ∧
    (∀ a : Bool,
      2*expect (fun _ : Fin N => 1/2) (fun z => if wholeFirst z = a then wholeSparseQ z/N else 0) =
        1/2+1/(2*(N : ℝ)) ∧
      2*expect (fun _ : Fin N => 1/2) (fun z => if wholeFirst z = a then
        (wholeSparseQ z/N-(1/2+1/(2*(N : ℝ))))^2 else 0) =
        ((N : ℝ)-1)/(4*(N : ℝ)^2))

def WholeSparseCountLimit : Prop :=
  ∀ a : Bool, ∀ ε : ℝ, 0 < ε →
    Tendsto (fun N => wholeSparseCond N a (fun z => ε < |wholeSparseQ z/N-1/2|))
      atTop (nhds 0)

def WholeSparseFinite : Prop :=
  ∀ N : ℕ, 3 ≤ N → ∀ z : Assignment N,
    2 ≤ wholeSparseQ z → wholeSparseQ z ≤ (N : ℝ)-1 →
    ValidInterval (wholeSparseR N) (wholeSparseQmat N) z ∧
    hajek (wholeSparseR N) z =
      (if wholeFirst z then 1/wholeSparseQ z else -1/(4*wholeSparseQ z)) ∧
    wholeSparseHac N z =
      (if wholeFirst z then (wholeSparseQ z-1)/(wholeSparseQ z)^3
        else (wholeSparseQ z-1)/(16*(wholeSparseQ z)^3)) ∧
    wholeSparseT N z =
      (if wholeFirst z then (1-3*wholeSparseQ z/(4*N))*Real.sqrt (wholeSparseQ z/(wholeSparseQ z-1))
        else -(1+3*wholeSparseQ z/N)*Real.sqrt (wholeSparseQ z/(wholeSparseQ z-1)))

def WholeSparseStatisticLimit : Prop :=
  ∀ a : Bool, ∀ ε : ℝ, 0 < ε →
    Tendsto (fun N => wholeSparseCond N a
      (fun z => ε < |wholeSparseT N z-(if a then 5/8 else -5/2)|)) atTop (nhds 0)

def WholeSparseVarianceBounds : Prop :=
  ∀ N : ℕ, 3 ≤ N →
    (∀ z, 0 ≤ wholeSparseV1 N z ∧ wholeSparseV1 N z ≤ 4/(N : ℝ)^2) ∧
    (∀ z, 0 ≤ wholeSparseV2 N z ∧ wholeSparseV2 N z ≤ 16/(N : ℝ)^2) ∧
    expect (fun _ => 1/2) (wholeSparseV2 N) = 17*((N : ℝ)-1)/(8*(N : ℝ)^3)

def WholeSparseRates : Prop :=
  Asymptotics.IsBigO atTop
    (fun N => sSup (Set.range (fun z : Assignment N => |wholeSparseV2 N z|)))
    (fun N => (N : ℝ)^(-2 : ℤ)) ∧
  BigOp (fun _ _ => 1/2) wholeSparseHac (fun N => (N : ℝ)^(-2 : ℤ)) ∧
  InProb (fun _ _ => 1/2) (fun N z => N*(wholeSparseHac N z-wholeSparseV1 N z)) ∧
  InProb (fun _ _ => 1/2) (fun N z => N*(wholeSparseV1 N z-wholeSparseV2 N z)) ∧
  InProb (fun _ _ => 1/2) (fun N z => N*(wholeSparseV2 N z-expect (fun _ => 1/2) (wholeSparseV2 N)))

/-- P004-T27; Supplement A p. 35 (Proposition 6(v)); compare Proposition 5,
p. 29; assumptions on pp. 26, 27, 32, 34.
Under the reading of Proposition 6(v) with uniform spacing bound C_b(1+s^2),
the sparse Bernoulli witness is a counterexample to its coverage assertion:
it satisfies the NED, kernel, bandwidth and homophily assumptions, but its valid
Wald intervals have coverage tending to one half, both at nominal 95 percent
and with critical values plus/minus two.
The statement includes the all-distance NED assertion, exact variance,
conditional binomial count law, exceptional probability, estimator and
studentized formulas, conditional limits, and the variance rates and bias.
-/
def T27WholeStatement : Prop :=
  T27Statement ∧
  WholeSparseDisks ∧
  WholeSparseNED ∧
  MetricNodeDistances sparsePopulation ∧
  (∀ N : ℕ, 3 ≤ N →
    (∀ x z, |(sparsePopulation N).outcome x z| < 2) ∧
    (∀ i s, 0 ≤ s → ((ball (nodeSeparation (sparsePopulation N)) i s).card : ℝ) ≤ 3*(1+s^2)) ∧
    (∀ i, nodeEffect (fun _ => 1/2) (wholeSparseR N) i = if i.val = 0 then 3/4 else 0) ∧
    ame (fun _ => 1/2) (wholeSparseR N) = 3/(4*(N : ℝ)) ∧
    (∀ i j, wholeSparseQmat N i j = if i = j then 1 else 0) ∧
    sparseBandwidth N / (N : ℝ)^(1/6 : ℝ) ≤ (N : ℝ)^(-1/12 : ℝ)) ∧
  WholeSparseExactMoments ∧ WholeSparseCountLaw ∧ WholeSparseCountLimit ∧
  WholeSparseFinite ∧ WholeSparseStatisticLimit ∧
  (5/8 : ℝ) < normalQuantile (39/40) ∧ normalQuantile (39/40) < 5/2 ∧
  Tendsto (fun N => prob (fun _ => 1/2)
    (wholeCovered (1/2) (wholeSparseR N) (wholeSparseQmat N) (-2) 2)) atTop (nhds (1/2)) ∧
  Tendsto (fun N => prob (fun _ => 1/2)
    (wholeCovered (1/2) (wholeSparseR N) (wholeSparseQmat N)
      (normalQuantile (1/40)) (normalQuantile (39/40)))) atTop (nhds (1/2)) ∧
  (1/2 : ℝ) < 19/20 ∧ WholeSparseVarianceBounds ∧ WholeSparseRates ∧
  (∀ N : ℕ, 3 ≤ N → (N : ℝ) *
    (expect (fun _ => 1/2) (wholeSparseV2 N) -
      variance (fun _ => 1/2) (linearHajek (fun _ => 1/2) (wholeSparseR N))) =
        9*((N : ℝ)-1)/(16*(N : ℝ)^2) ∧
      0 ≤ (N : ℝ)*(expect (fun _ => 1/2) (wholeSparseV2 N) -
        variance (fun _ => 1/2) (linearHajek (fun _ => 1/2) (wholeSparseR N))))

/-- P004-T28; Supplement A p. 35 (Proposition 6); proof pp. 35--39.
Under the corrected uniform quadratic spacing condition and the stated NED,
kernel, bandwidth and homophily assumptions, the independent five-term V1 is
the random row sum, all three raw scaled approximation errors vanish in
probability, and the asymptotic bias is nonnegative. With the claimed variance
lower bound, defined Wald intervals have conservative liminf coverage for
every alpha in (0,1). Gaussian quantile existence is a conclusion.
-/
def T28WholeStatement : Prop :=
  ∀ {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)],
  ∀ (P : PopulationSequence Space) (p d : ℝ) (K : ℝ → ℝ) (bandwidth : ℕ → ℝ),
    (0 < p ∧ p < 1) → 0 ≤ d → BoundedOutcomes P →
    (∀ N, WellDefined (P N) d) → NEDConditions P p d → MetricNodeDistances P →
    QuadraticSpacing P → KernelConditions K → (∀ N, 0 < bandwidth N) →
    Tendsto bandwidth atTop atTop →
    Asymptotics.IsLittleO atTop bandwidth (fun N => (N : ℝ)^(1/6 : ℝ)) →
    LiminfAtLeast (kernelHomophily P p d K bandwidth) 0 →
    let R := circleSequence P d
    let D := fun N => nodeSeparation (P N)
    let Vhac := fun N z => kernelVariance z (residual (R N) z) (distanceKernel (D N) K (bandwidth N))
    let V1 := fun N => wholeV1Five p (R N) (D N) K (bandwidth N)
    let V2 := fun N => nedV2 p (R N) (D N) K (bandwidth N)
    (∀ N z, ValidArms z → V1 N z = nedV1 p (R N) (D N) K (bandwidth N) z) ∧
    (∀ N z, V2 N z = ∑ i, nedVRow p (R N) (D N) K (bandwidth N)
      (barMu (fun _ => p) (R N) true) (barMu (fun _ => p) (R N) false) i z) ∧
    InProb (fun _ _ => p) (fun N z => N*(Vhac N z-V1 N z)) ∧
    InProb (fun _ _ => p) (fun N z => N*(V1 N z-V2 N z)) ∧
    InProb (fun _ _ => p) (fun N z => N*(V2 N z-expect (fun _ => p) (V2 N))) ∧
    LiminfAtLeast (fun N => (N : ℝ)*(expect (fun _ => p) (V2 N)-
      variance (fun _ => p) (linearHajek (fun _ => p) (R N)))) 0 ∧
    (Nondegenerate (fun N => variance (fun _ => p) (linearHajek (fun _ => p) (R N))) →
      ∀ α : ℝ, 0 < α → α < 1 →
      FiniteQuantile (α/2) ∧ FiniteQuantile (1-α/2) ∧
      Conservative (fun N => prob (fun _ => p)
        (wholeCovered p (R N) (distanceKernel (D N) K (bandwidth N))
          (normalQuantile (α/2)) (normalQuantile (1-α/2)))) α)

/-- The interaction correction obtained by conditioning on a second treated node.
Outside any valid interference neighborhood its summands are zero. -/
def wholeDelta {N : ℕ} (p : ℝ) (R : CircleTable N) : ℝ :=
  (∑ i, ∑ j ∈ Finset.univ.erase i,
    (pairMarginal (fun _ => p) (R i) i j true true -
      pairMarginal (fun _ => p) (R i) i j false true - nodeEffect (fun _ => p) R i)) / N

def wholeCountFluctuation {N : ℕ} (p : ℝ) (z : Assignment N) : ℝ := armCount z true/N-p
def wholeOptimalCoefficient {N : ℕ} (p : ℝ) (R : CircleTable N) : ℝ :=
  barMu (fun _ => p) R true/p + barMu (fun _ => p) R false/(1-p) + wholeDelta p R/(1-p)
def wholeVarianceConstant {N : ℕ} (p : ℝ) (R : CircleTable N) : ℝ :=
  variance (fun _ => p) (ht (fun _ => p) R) -
    p*(1-p)*(wholeOptimalCoefficient p R)^2/N

def WholeCountCovariance : Prop :=
  ∀ N : ℕ, 0 < N → ∀ p : ℝ, (0 < p ∧ p < 1) → ∀ R : CircleTable N,
    expect (fun _ => p) (wholeCountFluctuation (N := N) p) = 0 ∧
    variance (fun _ => p) (wholeCountFluctuation (N := N) p) = p*(1-p)/N ∧
    cov (fun _ => p) (ht (fun _ => p) R) (wholeCountFluctuation (N := N) p) =
      ((1-p)*barMu (fun _ => p) R true+p*barMu (fun _ => p) R false+p*wholeDelta p R)/N

def WholeVarianceSquare : Prop :=
  ∀ N : ℕ, 0 < N → ∀ p : ℝ, (0 < p ∧ p < 1) → ∀ R : CircleTable N,
    0 ≤ wholeVarianceConstant p R ∧
    (∀ c1 c0 : ℝ, variance (fun _ => p) (augmented (fun _ => p) R (fun _ a => if a then c1 else c0)) =
      p*(1-p)/N*(c1/p+c0/(1-p)-wholeOptimalCoefficient p R)^2+wholeVarianceConstant p R) ∧
    variance (fun _ => p) (linearHajek (fun _ => p) R) =
      wholeVarianceConstant p R+p*(wholeDelta p R)^2/(N*(1-p)) ∧
    (∀ ε : ℝ, 0 ≤ ε → |wholeDelta p R| ≤ ε →
      0 ≤ variance (fun _ => p) (linearHajek (fun _ => p) R)-wholeVarianceConstant p R ∧
      variance (fun _ => p) (linearHajek (fun _ => p) R)-wholeVarianceConstant p R ≤
        p*ε^2/(N*(1-p))) ∧
    (wholeDelta p R = 0 → variance (fun _ => p) (linearHajek (fun _ => p) R) = wholeVarianceConstant p R)

/-- P004-T30; p. 751 (PDF p. 8), end of Section 3; Supplement A p. 13,
eq. (33), with eq. (32) on p. 12.
Complete randomization gives uniform conditional remainder laws with N1-1
and N1 treated nodes, positive conditioning events, and disjoint supports.
Under Bernoulli assignment the two remainder laws coincide. The corrected
arm centers give the explicit linearized Hajek estimator and the same variance;
the wrong equal-center fit agrees identically exactly when the centers agree.
The approximation in (33) has the exact nonnegative quadratic remainder in
the interaction correction Delta, with the constant independent of both fits.
-/
def T30WholeStatement : Prop :=
  (∀ N n1 : ℕ, 1 ≤ n1 → n1 ≤ N-1 → ∀ i : Fin N,
    0 < (completeSupport N n1).card ∧
    Disjoint (remainderSupport n1 i false) (remainderSupport n1 i true) ∧
    ∀ a : Bool,
      0 < ((completeSupport N n1).filter (fun z => z i = a)).card ∧
      0 < (remainderSupport n1 i a).card ∧
      0 < (((completeSupport N n1).filter (fun z => z i = a)).card : ℝ) /
        ((completeSupport N n1).card : ℝ) ∧
      ∀ u : {j : Fin N // j ≠ i} → Bool,
        (((completeSupport N n1).filter (fun z => z i = a ∧
          ∀ j : {j : Fin N // j ≠ i}, z j = u j)).card : ℝ) /
          (((completeSupport N n1).filter (fun z => z i = a)).card : ℝ) =
        if u ∈ remainderSupport n1 i a then 1/((remainderSupport n1 i a).card : ℝ) else 0) ∧
  (∀ N : ℕ, ∀ p : Fin N → ℝ, (∀ j, 0 < p j ∧ p j < 1) → ∀ i : Fin N,
    (∀ a : Bool, 0 < prob p (fun z => z i = a) ∧
      ∀ u : {j : Fin N // j ≠ i} → Bool,
        prob p (fun z => z i = a ∧ ∀ j : {j : Fin N // j ≠ i}, z j = u j) /
          prob p (fun z => z i = a) = ∏ j : {j : Fin N // j ≠ i}, coin (p j) (u j)) ∧
    (∀ u : {j : Fin N // j ≠ i} → Bool,
      prob p (fun z => z i = false ∧ ∀ j : {j : Fin N // j ≠ i}, z j = u j) /
        prob p (fun z => z i = false) =
      prob p (fun z => z i = true ∧ ∀ j : {j : Fin N // j ≠ i}, z j = u j) /
        prob p (fun z => z i = true)) ∧
    ∀ (R : CircleTable N) (a : Bool),
      marginal p R i a = expect p (fun z => R i (Function.update z i a))) ∧
  (∀ N : ℕ, 0 < N → ∀ p : ℝ, (0 < p ∧ p < 1) → ∀ R : CircleTable N,
    linearHajek (fun _ => p) R = linearFormula (fun _ => p) R ∧
    linearHajek (fun _ => p) R = augmented (fun _ => p) R (fun _ a => barMu (fun _ => p) R a) ∧
    variance (fun _ => p) (linearFormula (fun _ => p) R) =
      variance (fun _ => p) (augmented (fun _ => p) R (fun _ a => barMu (fun _ => p) R a)) ∧
    (∀ z, augmented (fun _ => p) R (fun _ _ => barMu (fun _ => p) R true) z -
      linearHajek (fun _ => p) R z =
        (barMu (fun _ => p) R true-barMu (fun _ => p) R false) *
          (armCount z false/(N*(1-p))-1)) ∧
    ((augmented (fun _ => p) R (fun _ _ => barMu (fun _ => p) R true) =
      linearHajek (fun _ => p) R) ↔ barMu (fun _ => p) R true = barMu (fun _ => p) R false)) ∧
  WholeVarianceSquare

end
end SAP.P004b
