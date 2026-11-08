import SAP.P009c.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009c
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

def T47Statement : Prop :=
  ∀ (S : Study) (k q s : ℝ), RegularSequence S k q s → 4 ≤ q →
    (∀ t, Bernoulli (S.experiment t)) →
    (InProbability S (fun t z => let E := S.experiment t
      size S t / dAvg E * (vBER E z - var E.design (ht E)) -
        (msq E / dAvg E - B1 E - B2 E)) ∧
    ((∀ t, NoInterference (S.experiment t)) →
      InProbability S (fun t z => let E := S.experiment t
        size S t * (vBER E z - var E.design (ht E)) - msq E))) ∧
    (∀ t, 0 ≤ msq (S.experiment t))

def T48Statement : Prop :=
  ∀ (S : Study) (k q s : ℝ), RegularSequence S k q s → 4 ≤ q →
    (∀ t, Bernoulli (S.experiment t)) → Restricted S →
    LittleO (fun t => sdSigmaSq (S.experiment t))
      (fun t => dAvg (S.experiment t) / dRMS (S.experiment t)) →
    Conservative S (fun t => vAVG (S.experiment t))

def T49Statement : Prop :=
  ∀ (S : Study) (k q s : ℝ), RegularSequence S k q s → 4 ≤ q →
    (∀ t, Bernoulli (S.experiment t)) →
    (LittleO (fun t => dMax (S.experiment t))
      (fun t => Real.sqrt (size S t) * Real.sqrt (dAvg (S.experiment t))) ∨
      (Restricted S ∧ PositiveLiminf (fun t => msq (S.experiment t)))) →
    Conservative S (fun t => vMAX (S.experiment t))

def T50Statement : Prop :=
  (∀ (S : Study) (k q s : ℝ), RegularSequence S k q s → 4 ≤ q →
    (∀ t, Bernoulli (S.experiment t)) →
    (LittleO (fun t => lambdaMax (S.experiment t))
      (fun t => Real.sqrt (size S t) * Real.sqrt (dAvg (S.experiment t))) ∨
      (Restricted S ∧ PositiveLiminf (fun t => msq (S.experiment t)))) →
    Conservative S (fun t => vSR (S.experiment t))) ∧
  (∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n),
    dAvg E ≤ lambdaMax E ∧ lambdaMax E ≤ dMax E)

def T51Statement : Prop :=
  (∀ (S : Study) (k α x : ℝ), 0 < k →
    (∀ t i, k⁻¹ ≤ marginal (S.experiment t) i true ∧
      marginal (S.experiment t) i true ≤ 1 - k⁻¹) →
    (∀ t, Bernoulli (S.experiment t)) → 0 < α ∧ α < 1 → 0 ≤ x ∧ x < 1 →
    ∃ y : (t : ℕ) → Fin (S.N t) → Assignment (S.N t) → ℝ,
      let S' : Study := {S with experiment := fun t => {S.experiment t with outcome := y t}}
      (∃ K q s, RegularSequence S' K q s) ∧ Restricted S' ∧
      BigO (fun t => dAvg (S'.experiment t)) (fun t => Real.rpow (size S' t) x) ∧
      (x = 0 → BigO (fun t => dMax (S'.experiment t)) (fun t => Real.sqrt (size S' t))) ∧
      InDistribution S' (fun t z => Real.sqrt (size S' t) / Real.sqrt (dAvg (S'.experiment t)) *
        (ht (S'.experiment t) z - mean (S'.experiment t).design (ht (S'.experiment t))))
        (sharpCDF α)) ∧
  (∀ (α : ℝ) (hα : 0 < α ∧ α < 1),
    mean (sharpLaw α hα) sharpValue = 0 ∧ var (sharpLaw α hα) sharpValue = α ∧
    prob (sharpLaw α hα) (fun i => |sharpValue i| ≥ 1) = α ∧
    prob (sharpLaw α hα) (fun i => |sharpValue i - mean (sharpLaw α hα) sharpValue| ≥
      Real.sqrt (var (sharpLaw α hα) sharpValue / α)) = α)

end
end SAP.P009c
