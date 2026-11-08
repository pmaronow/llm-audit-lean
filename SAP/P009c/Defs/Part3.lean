import SAP.P009c.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009c
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Both ratios in the printed Hájek contrast exist on every supported assignment. -/
def SupportedArms (S : Study) : Prop :=
  ∀ t z, 0 < (S.experiment t).design.mass z → ArmsNonempty (S.experiment t) z

/-- Consistency and the stochastic rate for the HT error. -/
def HTClaims (S : Study) (θ a : ℕ → ℝ) : Prop :=
  InProbability S (fun t z => ht (S.experiment t) z - θ t) ∧
  Op S (fun t z => ht (S.experiment t) z - θ t) a

/-- Consistency and the stochastic rate for Hájek, used only on its supported domain. -/
def HajekClaims (S : Study) (θ a : ℕ → ℝ) : Prop :=
  InProbability S (fun t z => hajek (S.experiment t) z - θ t) ∧
  Op S (fun t z => hajek (S.experiment t) z - θ t) a

def T35Statement : Prop :=
  ∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n),
    (NoInterference E → (∀ z, ateAt E z = ate E) ∧ eate E = ate E) ∧
    eate E = (∑ i, (mean E.design (potential E i true) -
      mean E.design (potential E i false))) / n ∧
    ((∀ i, 0 < marginal E i true ∧ marginal E i true < 1) →
      adse E = (∑ i, (cmean E.design (fun z => z i = true) (potential E i true) -
        cmean E.design (fun z => z i = false) (potential E i false))) / n) ∧
    (Bernoulli E → eate E = adse E)

def T36Statement : Prop :=
  ∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n),
    max (C1 E) (Cinf E ^ 2 / (n : ℝ)) ≤ dAvg E ∧
    dAvg E ≤ C2 E ^ 2 ∧ C2 E ^ 2 ≤ Cinf E ^ 2

def T37Statement : Prop :=
  ∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n) (Q : Law (Assignment n))
    (K : ℝ), BoundedEffects E K →
    |eate E - eate {E with design := Q}| ≤ 2 * K * totalVariation E.design Q

def T38Statement : Prop :=
  ∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n) (K r : ℝ),
    BoundedEffects E K → 1 ≤ r → ∀ z z' : Assignment n,
    |ateAt E z - ateAt E z'| ≤
      2 * K * Real.rpow (n : ℝ) (-1 / r) * conjugateC E r * lrDistance r z z'

def T39Statement : Prop :=
  ∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n) (Q : Law (Assignment n))
    (K r : ℝ), BoundedEffects E K → 1 ≤ r →
    |eate E - eate {E with design := Q}| ≤
      2 * K * Real.rpow (n : ℝ) (-1 / r) * conjugateC E r * wasserstein r E.design Q

def T41Statement : Prop :=
  ∀ (S : Study) (k q s : ℝ),
    RegularSequence S k q s → (∀ t, Bernoulli (S.experiment t)) → Restricted S →
    HTClaims S (fun t => eate (S.experiment t)) (bernoulliRate S)

def T42Statement : Prop :=
  ∀ (S : Study) (k q s : ℝ),
    RegularSequence S k q s → CompleteSequence S → Restricted S →
    LittleO (fun t => C1 (S.experiment t)) (fun t => Real.sqrt (size S t)) →
    EstimatorClaims S (fun t => eate (S.experiment t))
      (fun t => bernoulliRate S t + C1 (S.experiment t) / Real.sqrt (size S t))

def T43Statement : Prop :=
  ∀ (S : Study) (k q s : ℝ), RegularSequence S k q s →
    ((∀ t, Bernoulli (S.experiment t)) ∨ CompleteSequence S) →
    BigO (fun t => dAvg (S.experiment t)) (fun _ => 1) →
    HTClaims S (fun t => eate (S.experiment t)) (fun t => 1 / Real.sqrt (size S t)) ∧
    (CompleteSequence S →
      HajekClaims S (fun t => eate (S.experiment t)) (fun t => 1 / Real.sqrt (size S t)))

def T44Statement : Prop :=
  ∀ (S : Study) (ρ : (t : ℕ) → Pairing (S.N t)) (k q s : ℝ),
    RegularSequence S k q s → (∀ t, Paired (S.experiment t) (ρ t)) → Restricted S →
    LittleO (fun t => eAvg (S.experiment t) (ρ t)) (size S) →
    LittleO (fun t => rSum (S.experiment t) (ρ t)) (size S) →
    EstimatorClaims S (fun t => eate (S.experiment t))
      (fun t => bernoulliRate S t +
        Real.sqrt (eAvg (S.experiment t) (ρ t)) / Real.sqrt (size S t) +
        rSum (S.experiment t) (ρ t) / size S t)

def T45Statement : Prop :=
  ∀ (S : Study) (k : ℝ) (q s : MomentIndex),
    RegularMix S k q s → MaximalMoments S q s → Restricted S →
    LittleO (fun t => alphaExt (S.experiment t) (extExponent q)) (size S) →
    LittleO (fun t => alphaInt (S.experiment t) (intExponent s)) (size S) →
    let θ := fun t => eate (S.experiment t)
    let a := fun t => bernoulliRate S t +
      Real.sqrt (alphaExt (S.experiment t) (extExponent q)) / Real.sqrt (size S t) +
      alphaInt (S.experiment t) (intExponent s) / size S t
    HTClaims S θ a ∧ (SupportedArms S → HajekClaims S θ a)

def T46Statement : Prop :=
  ∀ (S : Study) (k : ℝ) (q s : MomentIndex), RegularMix S k q s →
    (∀ r : MomentIndex, 2 ≤ r →
      (∀ t i, MomentBound (S.experiment t).design ((S.experiment t).outcome i) k r) →
      r ≤ q) → Restricted S →
    LittleO (fun t => alphaExt (S.experiment t) (extExponent q)) (size S) →
    let θ := fun t => adse (S.experiment t)
    let a := fun t => bernoulliRate S t +
      Real.sqrt (alphaExt (S.experiment t) (extExponent q)) / Real.sqrt (size S t)
    HTClaims S θ a ∧ (SupportedArms S → HajekClaims S θ a)

end
end SAP.P009c
