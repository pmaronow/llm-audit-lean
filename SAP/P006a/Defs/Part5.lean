import Mathlib
import SAP.P006a.Defs.Part1
import SAP.P006a.Defs.Part2
import SAP.P006a.Defs.Part3
import SAP.P006a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

universe u v
namespace SAP.P006a
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p


/-- P006-T1: the packaged mathematical assertion. -/
def T1Statement : Prop :=
  ((∀ x, printedAverageRule effectE001 x = binaryRule (0,1) x) ∧
    witnessReward (0,1) = 3/4 ∧ witnessReward (1,1) = 19/20 ∧
    witnessReward (0,1) < witnessReward (1,1) ∧
    (∀ π ∈ binaryPolicies, witnessReward π ≤ witnessReward (17/18,1)) ∧
    (∀ π ∈ binaryPolicies, witnessReward π = witnessReward (17/18,1) ↔ π = (17/18,1)) ∧
    witnessReward (17/18,1) = 1369/1440 ∧
    IsBest binaryPolicies (witnessWelfare) (1,1) ∧
    witnessWelfare (1,1) -
      witnessWelfare (17/18,1) = 1/40 ∧
    witnessWelfare (1,1) -
      witnessWelfare (0,1) = 9/20) ∧
  (∀ π ∈ binaryPolicies, rewardE001ATT π = witnessReward π ∧
    witnessReward π = (9*π.1+10*π.2)*(4-π.1-π.2)/40 ∧
    1369/1440 - witnessReward π =
      (9/40)*(π.1-17/18)^2 + (1-π.2)*(30-19*π.1-10*π.2)/40 ∧
    witnessWelfare π = (9*π.1+10*π.2)/20) ∧
  (finiteConditionalAverage (fun _ : Fin 2 => 1/2) ![9/10,1] ![0,1] = 1 ∧
    witnessReward (0,1) = 3/4 ∧ (3/4 : ℝ) < 1) ∧
  witnessWelfare (1,1) = 19/20 ∧
  witnessWelfare (17/18,1) = 37/40 ∧
  witnessWelfare (0,1) = 1/2


/-- P006-T2: the packaged mathematical assertion. -/
def T2Statement : Prop :=
  (∀ {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C] {n : ℕ}
    (E : Experiment Ω C n) (hD : OutcomeStanding E),
    ((∀ π, Admissible π →
      (E.law π {ω | treatedCount (fun i => E.T π i ω) = 0}).toReal =
        (1 - E.q π)^n ∧
      (E.law π {ω | 0 < treatedCount (fun i => E.T π i ω)}).toReal =
        1 - (1 - E.q π)^n ∧
      E.expectedATO π = E.averageObjective E.μ1 π ∧
      E.averageObjective E.μ1 π =
        (if 0 < E.q π then
          (1 - (1 - E.q π)^n) * (E.A E.μ1 π / E.q π) else 0) ∧
      (0 < E.q π →
        eventMean (E.law π) {ω | 0 < treatedCount (fun i => E.T π i ω)}
          (fun ω => wATO (fun i => E.T π i ω) (E.observed π ω)) =
            E.A E.μ1 π / E.q π)) ∧
      (∀ π, IsBest {π | Admissible π} E.expectedATO π ↔
        IsBest {π | Admissible π} (E.averageObjective E.μ1) π)) ∧
    (Standing E → VectorUnbiased E {π | Admissible π} →
      (∀ π, Admissible π →
        E.expectedATT π = E.averageObjective E.τ π ∧
        E.averageObjective E.τ π =
          (if 0 < E.q π then
            (1 - (1 - E.q π)^n) * (E.A E.τ π / E.q π) else 0) ∧
        (0 < E.q π →
          eventMean (E.law π) {ω | 0 < treatedCount (fun i => E.T π i ω)}
            (fun ω => wATT (E.μhat π ω) (fun i => E.X i ω)
              (fun i => E.T π i ω) (E.observed π ω)) =
                E.A E.τ π / E.q π)) ∧
      (∀ π, IsBest {π | Admissible π} E.expectedATT π ↔
        IsBest {π | Admissible π} (E.averageObjective E.τ) π))) ∧
  (∀ {K : ℕ} (hK : 0 < K) (n : ℕ) (hn : 0 < n)
    (p m : Fin K → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hm : Antitone m),
    (∀ j q, prefixMass p j ≤ q → q ≤ prefixMass p j+p j →
      thresholdRule p j q ∈ finitePolicies ∧
      finiteMass p (thresholdRule p j q) = q ∧
      finiteA p m (thresholdRule p j q) = prefixA p m j + m j*(q-prefixMass p j) ∧
      ∀ π ∈ finitePolicies, finiteMass p π = q →
        finiteA p m π ≤ prefixA p m j + m j*(q-prefixMass p j)) ∧
    (∃ j q, prefixMass p j ≤ q ∧ q ≤ prefixMass p j+p j ∧
      IsBest finitePolicies
        (fun π => emptyFactor n (finiteMass p π) * finiteA p m π)
        (thresholdRule p j q)) ∧
    (if 0 < m ⟨0,hK⟩ then
      IsBest finitePolicies (finiteConditionalAverage p m) (printedAverageRule m) ∧
        finiteConditionalAverage p m (printedAverageRule m) = m ⟨0,hK⟩
    else IsBest finitePolicies (finiteConditionalAverage p m) (fun _ => 0))) ∧
  (∀ {K : ℕ} (p m : Fin K → ℝ)
    (hp : ∀ i, 0 < p i) (j : Fin K) (hmax : ∀ i, m i ≤ m j),
    if 0 < m j then
      IsBest finitePolicies (finiteConditionalAverage p m) (printedAverageRule m) ∧
        finiteConditionalAverage p m (printedAverageRule m) = m j
    else IsBest finitePolicies (finiteConditionalAverage p m) (fun _ => 0)) ∧
  (∀ {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    [Countable C] [MeasurableSingletonClass C] (E : Experiment Ω C 1)
    (hD : OutcomeStanding E),
    (∀ π, Admissible π → E.expectedATO π = E.A E.μ1 π) ∧
    (Standing E → VectorUnbiased E {π | Admissible π} →
      ∀ π, Admissible π → E.expectedATT π = E.A E.τ π))


/-- P006-T3: the packaged mathematical assertion. -/
def T3Statement : Prop :=
  ∀ {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C] {n : ℕ}
    (E : Experiment Ω C n) (hS : Standing E) (PiSet : Set (C → ℝ))
    (hPiSet : ∀ π ∈ PiSet, Admissible π) (hz : (fun _ => 0) ∈ PiSet)
    (hU : VectorUnbiased E PiSet) (b s : C → ℝ)
    (hb : IsBest PiSet E.expectedATT b) (hs : IsBest PiSet E.V s),
    (∀ π ∈ PiSet, E.V π = E.A E.τ π ∧
      E.expectedATT π = emptyFactor n (E.q π)*E.V π ∧
      1 ≤ emptyFactor n (E.q π)) ∧
    E.expectedATT (fun _ => 0) = 0 ∧ E.V (fun _ => 0) = 0 ∧
    0 ≤ E.expectedATT b ∧ 0 ≤ E.V b ∧ regret PiSet E.V b ≤ bestValue PiSet E.V ∧
    regret PiSet E.V b = E.V s - E.V b


/-- P006-T4: the packaged mathematical assertion. -/
def T4Statement : Prop :=
  ((∀ x, fixedEstimatorMean estA x = 0 ∧ fixedEstimatorMean estB x = 0) ∧
    (∀ x, estA x x = 1 ∧ estB x x = -1) ∧
    IsBest binaryPolicies rewardA (0,0) ∧
    (∀ π ∈ binaryPolicies, rewardA π = rewardA (0,0) ↔ π = (0,0)) ∧
    IsBest binaryPolicies welfareA (1,1) ∧
    regret binaryPolicies welfareA (0,0) = 1/2 ∧
    rewardA (1,1) ≠ welfareA (1,1) ∧
    IsBest binaryPolicies rewardB (1,1) ∧
    (∀ π ∈ binaryPolicies, rewardB π = rewardB (1,1) ↔ π = (1,1)) ∧
    IsBest binaryPolicies welfareB (0,0) ∧
    regret binaryPolicies welfareB (1,1) = 1/2 ∧
    bestValue binaryPolicies welfareB = 0) ∧
  (∀ (π : BinaryPolicy), π ∈ binaryPolicies →
    rewardA π = -(π.1+π.2)/4 ∧ welfareA π = (π.1+π.2)/4 ∧
    rewardB π = (π.1+π.2)/4 ∧ welfareB π = -(π.1+π.2)/4) ∧
  (binaryMarginalHeterogeneity (fun _ => 0) (fun _ => 0) = 0 ∧
    2*binaryMarginalHeterogeneity (fun _ => 0) (fun _ => 0) <
      regret binaryPolicies welfareA (0,0)) ∧
  (∀ π ∈ binaryPolicies, oneATT (fun _ => 1/2) estA π = rewardA π ∧
    oneATT (fun _ => -1/2) estB π = rewardB π) ∧
  treatedEstimatorMean estA (1,1) = 1 ∧
  treatedEstimatorMean estB (1,1) = -1 ∧
  (∀ π ∈ binaryPolicies, rewardA π = welfareA π ↔ π = (0,0)) ∧
  bestValue binaryPolicies welfareA = 1/2 ∧
  welfareB (1,1) = -1/2


/-- P006-T5: the packaged mathematical assertion. -/
def T5Statement : Prop :=
  ((∀ x, (∑ xj : Bool, ∑ xk : Bool, (1/4 : ℝ)*sharedEst xj xk x) = 0) ∧
    (∀ xj, (∑ xk : Bool, (1/2 : ℝ)*sharedEst xj xk xj) = 1/2) ∧
    (∀ xk, (∑ xj : Bool, (1/2 : ℝ)*sharedEst xj xk xk) = -1/2) ∧
    IsBest binaryPolicies scoreJ (0,0) ∧ IsBest binaryPolicies scoreK (1,1) ∧
    bestValue binaryPolicies scoreJ = 0 ∧ bestValue binaryPolicies scoreK = 5/8 ∧
    bestValue binaryPolicies scoreJ < bestValue binaryPolicies scoreK ∧
    (1/8 : ℝ) ≤ 1/4) ∧
  (∀ (π : BinaryPolicy), π ∈ binaryPolicies →
    scoreJ π = -(π.1+π.2)/8 ∧ scoreK π = 5*(π.1+π.2)/16) ∧
  (0 : ℝ) < 1/8 ∧ (1/8 : ℝ) < 1/4


/-- P006-T6: the packaged mathematical assertion. -/
def T6Statement : Prop :=
  (∀ {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n)
    (PiSet : Set (C → ℝ)) (hPiSet : ∀ π ∈ PiSet, Admissible π)
    (hS : ∀ π ∈ PiSet, PolicyDesign E π)
    (hR : ∀ π ∈ PiSet, ∀ i, Integrable (fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - E.μ0 (E.X i ω))) (E.law π))
    (hU : TreatedUnbiased E E.μ0 PiSet),
    (∀ π ∈ PiSet, E.expectedTT π = (n : ℝ)*E.meanWelfare π ∧
      E.V π = E.meanWelfare π) ∧
    (∀ π, IsBest PiSet E.expectedTT π ↔ IsBest PiSet E.V π) ∧
    (∀ π, IsBest PiSet E.expectedTT π → regret PiSet E.V π = 0) ∧
    (PiSet = {π | Admissible π} → IsBest PiSet E.expectedTT (positiveRule E.τ))) ∧
  (∀ {Ω C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n)
    (PiSet : Set (C → ℝ))
    (hS : ∀ π ∈ PiSet, PolicyDesign E π)
    (hR : ∀ π ∈ PiSet, ∀ i, Integrable (fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - E.μ0 (E.X i ω))) (E.law π))
    (hU : PointwiseUnbiased E PiSet) (hI : IndependentEstimator E PiSet),
    TreatedUnbiased E E.μ0 PiSet)


/-- P006-T7: the packaged mathematical assertion. -/
def T7Statement : Prop :=
  ∀ {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n)
    (hDesign : Standing ({ E with μhat := fun _ _ _ => 0 } : Experiment Ω C n))
    (g : C → ℝ) (hg : Measurable g) (hpos : ∀ x, 0 < g x)
    (hR : ∀ π, Admissible π → ∀ i, Integrable
      (fun ω => bit (E.T π i ω) *
        (E.μhat π ω (E.X i ω) - E.μ0 (E.X i ω))) (E.law π))
    (hU : TreatedUnbiased E E.μ0 {π | Admissible π})
    (hprod : Integrable (fun x => g x * E.τ x) E.PX)
    (hreward : ∀ π, Admissible π → ∀ i, Integrable
      (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) *
        bit (E.T π i ω) * g (E.X i ω)) (E.law π)),
    (∀ π, Admissible π →
      E.expectedWeightedTT g π = (n : ℝ) * (∫ x, g x * E.τ x * π x ∂E.PX)) ∧
    IsBest {π | Admissible π} (E.expectedWeightedTT g) (positiveRule E.τ) ∧
    (∀ b, IsBest {π | Admissible π} (E.expectedWeightedTT g) b →
      (∀ᵐ x ∂E.PX, (0 < E.τ x → b x = 1) ∧ (E.τ x < 0 → b x = 0)) ∧
      E.V b = (∫ x, E.τ x * positiveRule E.τ x ∂E.PX) ∧
      IsBest {π | Admissible π} E.V b ∧
      regret {π | Admissible π} E.V b = 0)


/-- P006-T8: the packaged mathematical assertion. -/
def T8Statement : Prop :=
  ∀ {Ω X U : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U]
    {n : ℕ} (E : Experiment Ω (X × U) n) (hS : Standing E) (b0 : X → ℝ)
    (hM : MarginalBaseline E b0) (hX : EstimatorUsesOnlyX E)
    (PiSet : Set ((X × U) → ℝ)) (hPiSet : ∀ π ∈ PiSet, Admissible π)
    (hU : TreatedUnbiased E (fun c => b0 c.1) PiSet),
    (∀ π ∈ PiSet,
      normalizedTT E π = (∫ c, π c*(E.μ1 c-b0 c.1) ∂E.PX) ∧
      |normalizedTT E π-E.V π| = |∫ c, π c*(E.μ0 c-b0 c.1) ∂E.PX| ∧
      |normalizedTT E π-E.V π| ≤ marginalHeterogeneity E b0) ∧
    (∀ γ : ℝ, marginalHeterogeneity E b0 ≤ γ → ∀ b s : (X × U) → ℝ,
      IsBest PiSet E.expectedTT b → IsBest PiSet E.V s →
      regret PiSet E.V b = E.V s - E.V b ∧ regret PiSet E.V b ≤ 2*γ)


/-- P006-T9: the packaged mathematical assertion. -/
def T9Statement : Prop :=
  (∀ {n : ℕ} (τhat : Fin n → ℝ) (hn : 0 < n)
    (hk : 0 < (beneficiaries τhat).card),
    beneficiaryMean τhat =
      fittedOptimalUtility τhat * ((n : ℝ)/(beneficiaries τhat).card) ∧
    ((beneficiaries τhat).card < n →
      fittedOptimalUtility τhat < beneficiaryMean τhat)) ∧
  (∀ (vH bH vS bS : ℝ)
    (hHl : 293907/2000000 ≤ vH) (hHu : vH ≤ 293909/2000000)
    (hH : bH = vH*(255/62))
    (hSl : 50371/2000000 ≤ vS) (hSu : vS ≤ 50373/2000000)
    (hS : bS = vS*(7264/1360)),
    14989257/24800000 ≤ bH ∧ bH ≤ 14989359/24800000 ∧ 59/400 < bH ∧
    672601/5000000 ≤ bS ∧ bS ≤ 11434671/85000000 ∧ 51/2000 < bS) ∧
  (∀ (vH rH vS rS : ℝ)
    (hHr : 0 < rH) (hHv : 14694/100000 ≤ vH) (hHrU : rH ≤ 2432/10000)
    (hSr : 0 < rS) (hSv : 2517/100000 ≤ vS) (hSrU : rS ≤ 1873/10000),
    604/1000 < vH/rH ∧ 134/1000 < vS/rS) ∧
  (∀ vH bH vS bS : ℝ,
    293907/2000000 ≤ vH → vH ≤ 293909/2000000 → bH = vH*(255/62) →
    50371/2000000 ≤ vS → vS ≤ 50373/2000000 → bS = vS*(7264/1360) →
    1465/10000 < vH ∧ vH < 1475/10000 ∧
    245/10000 < vS ∧ vS < 255/10000 ∧
    6035/10000 < bH ∧ bH < 6045/10000 ∧
    1345/10000 < bS ∧ bS < 1355/10000)


/-- P006-T10: the packaged mathematical assertion. -/
def T10Statement : Prop :=
  (∀ (B : ℝ) (hB : 0 < B),
    let D : OutcomeLaw Unit := Measure.dirac ((),(1+B,1))
    let PiSet : Set (Unit → ℝ) := {fun _ => 1}
    FiniteOutcomeLaw D ∧
    IsBest PiSet (oneATOExpectation D) (fun _ => 1) ∧
    (∫ z, (1 : ℝ) ∂D) = 1 ∧
    outcomeWelfare D (fun _ => 1) = -B ∧
    regret PiSet (outcomeWelfare D) (fun _ => 1) = 0 ∧
    (∀ V : (Unit → ℝ) → ℝ, regret PiSet V (fun _ => 1) = 0) ∧
    (fun _ : Unit => (0:ℝ)) ∉ PiSet ∧ ¬ (0 ≥ B)) ∧
  (∀ {C : Type*} [MeasurableSpace C]
    (D : OutcomeLaw C) (π : C → ℝ)
    (_hD : FiniteOutcomeLaw D) (_hπ : Admissible π),
    oneATOExpectation D π = ∫ z, π z.1 * z.2.2 ∂D) ∧
  (∀ {C : Type*} [MeasurableSpace C]
    (D D' : OutcomeLaw C) (π : C → ℝ)
    (_hD : FiniteOutcomeLaw D) (_hD' : FiniteOutcomeLaw D') (hπ : Admissible π)
    (hD : Measure.map treatedProjection D = Measure.map treatedProjection D'),
    oneATOExpectation D π = oneATOExpectation D' π) ∧
  NondegenerateReward ({fun _ : Unit => (1 : ℝ)}) oneATOExpectation ∧
  (∀ f : (Unit → ℝ) → ℝ, IsBest ({fun _ : Unit => (1 : ℝ)}) f (fun _ => 1)) ∧
  (∀ B : ℝ, 0 < B →
    bestValue ({fun _ : Unit => (1 : ℝ)})
      (outcomeWelfare (Measure.dirac ((),(1+B,1)))) = -B)


end
end SAP.P006a
