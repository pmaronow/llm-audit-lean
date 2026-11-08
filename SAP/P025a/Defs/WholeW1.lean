import Mathlib
import SAP.P025a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- Original-scale upper threshold vector: the cut counts the prefix. -/
def wholeUpperWeights {n : ℕ} (α β : ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => if i.val < k then 1 / β else 1 / α

/-- The original-scale lower threshold vector. -/
def wholeLowerWeights {n : ℕ} (α β : ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => if i.val < k then 1 / α else 1 / β

/-- Affine interpolation, with the parameter restricted to [0,1] in certificates. -/
def wholeSegment {ι : Type*} (u v : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i => (1 - t) * u i + t * v i

/-- The actual finite law of the two-unit witness, expressed as a PMF. -/
def wholeTwoPMF : PMF (Fin 2) :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (twoProbability ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => by norm_num [twoProbability])]
    norm_num [twoProbability, Fin.sum_univ_two])

/-- A single probability space for all independent Brewer replicates. -/
def wholeTwoPathLaw : Measure (ℕ → Fin 2) :=
  Measure.infinitePi (fun _ : ℕ => wholeTwoPMF.toMeasure)

/-- The sampled units of the tagged population `Fin h × Fin 2`. -/
def wholeTwoPooledSample (h : ℕ) (ω : ℕ → Fin 2) : Finset (Fin h × Fin 2) :=
  Finset.univ.filter (fun ri => ri.2 ∈ twoSample (ω ri.1.val))

/-- Independent copies have the specified one-step law and are pooled by unit tags. -/
def wholeTwoReplication : Prop :=
  IsProbabilityMeasure wholeTwoPathLaw ∧
  (∀ ω, wholeTwoPMF ω = ENNReal.ofReal (twoProbability ω)) ∧
  iIndepFun (fun r : ℕ => fun ω : ℕ → Fin 2 => ω r) wholeTwoPathLaw ∧
  (∀ r : ℕ, wholeTwoPathLaw.map (fun ω : ℕ → Fin 2 => ω r) =
    wholeTwoPMF.toMeasure) ∧
  iIndepFun (fun r : ℕ => fun ω : ℕ → Fin 2 => twoSample (ω r)) wholeTwoPathLaw ∧
  (∀ h : ℕ, Fintype.card (Fin h × Fin 2) = h * 2) ∧
  (∀ (h : ℕ) (ω : ℕ → Fin 2) (ri : Fin h × Fin 2),
    ri ∈ wholeTwoPooledSample h ω ↔ ri.2 ∈ twoSample (ω ri.1.val)) ∧
  (∀ h : ℕ, 0 < h →
    (∑ ri : Fin h × Fin 2, binaryTwo ri.2) / (h * 2 : ℕ) = (1/2 : ℝ)) ∧
  (∀ (h : ℕ), 0 < h → ∀ ω, (wholeTwoPooledSample h ω).Nonempty)

/-- The two inclusion indicators are independent, including their zero events. -/
def wholeTwoIndependentInclusions : Prop :=
  ∀ b c : Bool,
    (∑ ω : Fin 2, twoProbability ω *
      (if decide ((0 : Fin 2) ∈ twoSample ω) = b ∧
          decide ((1 : Fin 2) ∈ twoSample ω) = c then 1 else 0)) =
    (∑ ω : Fin 2, twoProbability ω *
      (if decide ((0 : Fin 2) ∈ twoSample ω) = b then 1 else 0)) *
    (∑ ω : Fin 2, twoProbability ω *
      (if decide ((1 : Fin 2) ∈ twoSample ω) = c then 1 else 0))

/-- Residual certificates for the unweighted numerical witness. -/
def wholeSampleTwoResiduals : Prop :=
  ∀ u v : ℝ, 1 ≤ u → u ≤ 2 → 1 ≤ v → v ≤ 2 →
    0 < u + v ∧
    v/(u+v) - 1/3 = ((2-u) + 2*(v-1))/(3*(u+v)) ∧
    2/3 - v/(u+v) = (2*(u-1) + (2-v))/(3*(u+v)) ∧
    0 ≤ ((2-u) + 2*(v-1))/(3*(u+v)) ∧
    0 ≤ (2*(u-1) + (2-v))/(3*(u+v))

/-- Residual certificates for the class-total numerical witness. -/
def wholeClassTwoResiduals : Prop :=
  ∀ u v : ℝ, 1 ≤ u → u ≤ 2 → 1 ≤ v → v ≤ 2 →
    0 < u/2 + v ∧
    v/(u/2+v) - 1/2 = ((2-u) + 2*(v-1))/(2*(u+2*v)) ∧
    4/5 - v/(u/2+v) = (4*(u-1) + 2*(2-v))/(5*(u+2*v)) ∧
    0 ≤ ((2-u) + 2*(v-1))/(2*(u+2*v)) ∧
    0 ≤ (4*(u-1) + 2*(2-v))/(5*(u+2*v))

/-- Zero-cut diagnosis on the original probability box, for sample or class masses. -/
def wholeZeroDiagnosis {n : ℕ} (hn : 0 < n) (y a : Fin n → ℝ) (α β : ℝ) : Prop :=
  let γ := β/α
  let m := (∑ i, a i * y i) / (∑ i, a i)
  printedLowerCut y a γ ⟨0,hn⟩ ∧
  wholeLowerWeights (n:=n) α β 0 = (fun _ => 1/β) ∧
  weightBox α β (wholeLowerWeights (n:=n) α β 0) ∧
  lowerValue y a γ 0 = m ∧
  ratio y a (wholeLowerWeights α β 0) = m ∧
  y ⟨0,hn⟩ ≤ m ∧
  (1 < γ → (∃ i, y ⟨0,hn⟩ < y i) →
    weightBox α β (wholeLowerWeights (n:=n) α β 1) ∧
    ratio y a (wholeLowerWeights α β 1) < m ∧
    ¬ IsLeast (attainable y a α β) m)

/-- P025-T1; p. 236 (PDF p. 2).
The realizable two-unit sample refutes the printed lower rule: its true range is
[1/3,2/3], with the displayed residual certificates and independent inclusion
indicators. For every sorted nonempty sample the printed rule stops at zero;
the sample-mean residual and exact one-coordinate change explain its strict
nonoptimality whenever the bound ratio exceeds one and the outcomes vary. -/
def T1WholeStatement : Prop :=
  T1Statement ∧ wholeSampleTwoResiduals ∧ wholeTwoIndependentInclusions ∧
  (normBox 2 (![2,1] : Fin 2 → ℝ) ∧
    ratio binaryTwo (fun _ => 1) ![2,1] = 1/3 ∧
    normBox 2 (![1,2] : Fin 2 → ℝ) ∧
    ratio binaryTwo (fun _ => 1) ![1,2] = 2/3) ∧
  (∀ {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ), Monotone y →
    ∀ γ : ℝ, 1 ≤ γ →
      populationMean y - y ⟨0,hn⟩ = (∑ i, (y i - y ⟨0,hn⟩)) / n ∧
      0 ≤ (∑ i, (y i - y ⟨0,hn⟩)) / n ∧
      lowerValue y (fun _ => 1) γ 1 - populationMean y =
        (γ-1)*(y ⟨0,hn⟩ - populationMean y) / ((n : ℝ) + (γ-1))) ∧
  (∀ {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ), Monotone y →
    ∀ α β : ℝ, 0 < α → α ≤ β → β ≤ 1 →
      wholeZeroDiagnosis hn y (fun _ => 1) α β ∧
      ratio y (fun _ => 1) (wholeLowerWeights α β 1) - populationMean y =
        ((β/α)-1)*(y ⟨0,hn⟩ - populationMean y) / ((n : ℝ) + ((β/α)-1)))

/-- Singleton outcome classes, actual totals, and true class weights of the witness. -/
def wholeTwoClasses : Prop :=
  (∀ j : Fin 2, Finset.univ.filter (fun i : Fin 2 => binaryTwo i = binaryTwo j) = {j}) ∧
  (∀ j : Fin 2, designClassTotal twoSample twoProbability id j = twoPi j) ∧
  (∀ j : Fin 2,
    ((Finset.univ.filter (fun i : Fin 2 => binaryTwo i = binaryTwo j)).card : ℝ) /
      designClassTotal twoSample twoProbability id j = (![2,1] : Fin 2 → ℝ) j) ∧
  ratio binaryTwo twoPi ![2,1] = populationMean binaryTwo

/-- P025-T2; p. 238 (PDF p. 4), below Table 1; (7), p. 237 (PDF p. 3).
The two-class design, with independent Brewer replication, has singleton
classes, totals (1/2,1), true weights (2,1), and mean 1/2. The printed lower
cut gives 2/3, while the true extrema are 1/2 and 4/5, certified by the two
displayed residuals; the upper first cut is one and Assumption 2 holds.
For all strictly ordered positive class totals the printed rule stops at zero
and is strictly nonoptimal when the bound ratio exceeds one and there are at
least two classes. -/
def T2WholeStatement : Prop :=
  T2Statement ∧ wholeTwoReplication ∧ wholeTwoClasses ∧
  wholeClassTwoResiduals ∧ upperCut binaryTwo twoPi 2 (1 : Fin 2) ∧
  IsLeast (attainable binaryTwo twoPi (1/2) 1) (1/2) ∧
  IsGreatest (attainable binaryTwo twoPi (1/2) 1) (4/5) ∧
  (∀ {J : ℕ} (hJ : 0 < J) (y mass : Fin J → ℝ), StrictMono y →
    (∀ j, 0 < mass j) → ∀ α β : ℝ, 0 < α → α ≤ β → β ≤ 1 →
      wholeZeroDiagnosis hJ y mass α β ∧
      (1 < β/α → 2 ≤ J →
        ¬ IsLeast (attainable y mass α β)
          (ratio y mass (wholeLowerWeights α β 0))))

/-- Feasibility and continuity on the original-scale optimizer segment. -/
def wholeSampleSegment {n : ℕ} (y : Fin n → ℝ) (α β : ℝ)
    (kL kH : Fin n) : Prop :=
  let wL := fun i => (1/β)*lowerWeights (β/α) kL.val i
  let wH := fun i => (1/β)*upperWeights (β/α) kH.val i
  (∀ t ∈ Set.Icc (0 : ℝ) 1,
    weightBox α β (wholeSegment wL wH t) ∧
    0 < ∑ i, wholeSegment wL wH t i) ∧
  ContinuousOn (fun t => ratio y (fun _ => 1) (wholeSegment wL wH t)) (Set.Icc 0 1)

/-- P025-T3; p. 236 (PDF p. 2); Appendix, pp. 239-240 (PDF pp. 5-6).
Both corrected first cuts exist. Their prescribed feasible threshold vectors
attain the global minimum and maximum and the full interval of ratios.
The objective is continuous on their feasible connecting segment, which
attains every intermediate value. Both increment identities and the lower
separator and termwise residual certificate hold, including original-scale
weights, tied outcomes, singleton samples, and equal bounds. -/
def T3WholeStatement : Prop :=
  T3Statement ∧
  (∀ {n : ℕ} (_hn : 0 < n) (y : Fin n → ℝ), Monotone y →
    ∀ α β : ℝ, 0 < α → α ≤ β → β ≤ 1 →
    ∀ kL kH : Fin n, correctedSampleBounds y α β kL kH →
      wholeSampleSegment y α β kL kH ∧
      (∀ w : Fin n → ℝ, weightBox α β w →
        let u := fun i => β * w i
        let m := lowerValue y (fun _ => 1) (β/α) kL.val
        normBox (β/α) u ∧
        ratio y (fun _ => 1) w - m =
          (∑ i, (u i-lowerWeights (β/α) kL.val i)*(y i-m)) / (∑ i, u i) ∧
        (∀ i, 0 ≤ (u i-lowerWeights (β/α) kL.val i)*(y i-m)) ∧
        0 ≤ ratio y (fun _ => 1) w - m))

/-- The four positive-slack terms appearing in the six-unit residual. -/
def wholeTailSlack (w : Fin 4 → ℝ) : ℝ :=
  7*(2-w 0) + (2-w 1) + 5*(w 2-1) + 11*(w 3-1)

/-- P025-T10; p. 237 (PDF p. 3).
The six-unit design realizes the four-class counterexample. Over the whole
real weight box its minimum is 7/6, uniquely at (2,2,1,1), as certified by
the displayed residual equality and its nonnegative slack terms. The
corrected first cut is two, where the printed display gives 1 instead of
7/6; the printed stopping rule gives zero, where that display is undefined. -/
def T10WholeStatement : Prop :=
  T10Statement ∧
  (∀ w : Fin 4 → ℝ, normBox 2 w →
    0 < ∑ i, w i ∧
    ratio fourOutcomes (fun _ => 1) w - 7/6 = wholeTailSlack w / (6*∑ i, w i) ∧
    0 ≤ wholeTailSlack w / (6*∑ i, w i) ∧
    (ratio fourOutcomes (fun _ => 1) w = 7/6 ↔ w = ![2,2,1,1])) ∧
  ((∀ i : Fin 6, (1/2 : ℝ) ≤ designInclusion fourClassSample fourClassProbability i ∧
      designInclusion fourClassSample fourClassProbability i ≤ 1) ∧
    (∀ i : Fin 6, sixTailOutcomes i = fourOutcomes (sixTailClass i)) ∧
    normBox 2 (lowerWeights (n:=4) 2 2) ∧
    IsLeast (attainable fourOutcomes (fun _ => 1) (1/2) 1) (7/6) ∧
    lowerEndpoint fourOutcomes (fun _ => 1) (1/2) 1 = 7/6)

/-- Class sizes determined by a surjective map onto the distinct outcome classes. -/
def wholeClassSize {N J : ℕ} (cls : Fin N → Fin J) (j : Fin J) : ℕ :=
  (Finset.univ.filter (fun i => cls i = j)).card

/-- Actual class totals, as sums of unit inclusion probabilities. -/
def wholeClassMass {N J : ℕ} (cls : Fin N → Fin J) (π : Fin N → ℝ)
    (j : Fin J) : ℝ := ∑ i with cls i = j, π i

/-- The finite-population meaning of the equal-probability branch (B-iv). -/
def wholePopulationBoundary : Prop :=
  ∀ {N J : ℕ}, 0 < N → 0 < J →
    ∀ (z : Fin N → ℝ) (y : Fin J → ℝ) (cls : Fin N → Fin J),
    StrictMono y → Function.Surjective cls → (∀ i, z i = y (cls i)) →
    ∀ (c : ℝ), 0 < c → c ≤ 1 →
    ∀ π : Fin N → ℝ, (∀ i, c ≤ π i ∧ π i ≤ c) →
    let m := wholeClassSize cls
    let mass := wholeClassMass cls π
    (∀ i, π i = c) ∧
    (∀ j, 0 < m j ∧ mass j = c * m j ∧ 0 < mass j ∧ (m j : ℝ)/mass j = 1/c) ∧
    (∑ j, m j) = N ∧
    (∑ j, (m j : ℝ)*y j)/(∑ j, (m j : ℝ)) = populationMean z ∧
    ratio y mass (fun j => (m j : ℝ)/mass j) = populationMean z ∧
    (∀ w : Fin J → ℝ, weightBox c c w ↔ w = fun _ => 1/c) ∧
    attainable y mass c c = {populationMean z} ∧
    IsLeast (attainable y mass c c) (populationMean z) ∧
    IsGreatest (attainable y mass c c) (populationMean z) ∧
    lowerEndpoint y mass c c = populationMean z ∧
    upperEndpoint y mass c c = populationMean z

/-- The original scale, the boundary cut, and the strict first maximum. -/
def wholeSampleProofRepair : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ), Monotone y →
    ∀ α β : ℝ, 0 < α → α ≤ β → β ≤ 1 →
    let γ := β/α
    (∀ k : ℕ, k ≤ n →
      weightBox α β (wholeUpperWeights (n:=n) α β k) ∧
      ratio y (fun _ => 1) (wholeUpperWeights α β k) = upperValue y (fun _ => 1) γ k ∧
      (∑ i : Fin n, upperWeights γ k i) = (k : ℝ) + γ * ((n-k : ℕ) : ℝ) ∧
      0 < (k : ℝ) + γ * ((n-k : ℕ) : ℝ) ∧
      upperValue y (fun _ => 1) γ k =
        ((∑ i with i.val < k, y i) + γ*(∑ i with k ≤ i.val, y i)) /
          ((k : ℝ) + γ * ((n-k : ℕ) : ℝ))) ∧
    (∀ k : Fin n,
      upperValue y (fun _ => 1) γ (k.val+1) - upperValue y (fun _ => 1) γ k.val =
        (1-γ)*(y k-upperValue y (fun _ => 1) γ k.val) /
          ((k.val+1 : ℕ) + γ * ((n-(k.val+1) : ℕ) : ℝ))) ∧
    (γ = 1 → α = β ∧
      (∀ w : Fin n → ℝ, weightBox α β w ↔ w = fun _ => 1/α) ∧
      (∀ k : ℕ, wholeUpperWeights (n:=n) α β k = (fun _ => 1/α) ∧
        upperValue y (fun _ => 1) γ k = populationMean y) ∧
      lowerEndpoint y (fun _ => 1) α β = populationMean y ∧
      upperEndpoint y (fun _ => 1) α β = populationMean y ∧
      populationMean y ≤ y ⟨n-1, by omega⟩ ∧
      (∃ kH : Fin n,
        IsLeast {k : Fin n | populationMean y ≤ y k} kH ∧
        upperCut y (fun _ => 1) γ kH ∧
        upperValue y (fun _ => 1) γ kH.val = populationMean y) ∧
      IsLeast {k : Fin n | upperValue y (fun _ => 1) γ k.val ≥
        upperValue y (fun _ => 1) γ (k.val+1)} ⟨0,hn⟩) ∧
    (1 < γ → ∃ kH : Fin n, upperCut y (fun _ => 1) γ kH ∧
      IsLeast {k : Fin n | upperValue y (fun _ => 1) γ k.val ≥
        upperValue y (fun _ => 1) γ (k.val+1)} kH ∧
      (∀ j : ℕ, j ≤ n → upperValue y (fun _ => 1) γ j ≤
        upperValue y (fun _ => 1) γ kH.val) ∧
      IsGreatest {v : ℝ | ∃ j : ℕ, j ≤ n ∧ upperValue y (fun _ => 1) γ j = v}
        (upperValue y (fun _ => 1) γ kH.val)) ∧
    (∀ k : Fin n, upperValue y (fun _ => 1) γ k.val ≤ y k →
      upperValue y (fun _ => 1) γ (k.val+1) ≤ y k ∧
      (∀ hk : k.val+1 < n, y k ≤ y ⟨k.val+1,hk⟩))

/-- P025-T11; pp. 239-240 (PDF pp. 5-6); Supplement p. 2.
The repaired proof includes the original-scale threshold formulas and increments.
At equal bounds the sample box is a singleton and both endpoints are the
sample mean; its outcome-test first cut exists, while the first stationary
index is zero. At strict bounds the stationary and outcome-test first cuts
agree and attain the global threshold maximum. The exact two-coordinate
identities give strict improvement only for strict bounds. At equal inclusion
probabilities the actual class totals are probability times class size, and
both class optimization problems attain the finite-population mean. -/
def T11WholeStatement : Prop :=
  T11Statement ∧ wholeSampleProofRepair ∧ wholePopulationBoundary ∧
  (∀ (c₂ p q a b : ℝ), 0 ≤ c₂ → 0 < p → 0 < q → 0 < a → a ≤ b →
    ∀ x ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b, 0 < c₂ + x*p + z*q)

end
end SAP.P025a
