import SAP.P009c.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009c
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

def xi {n : ℕ} (E : Experiment n) (i j : Fin n) (a : Bool) : ℝ :=
  mean E.design (fun z =>
    E.outcome i (Function.update (Function.update z i a) j true) -
    E.outcome i (Function.update (Function.update z i a) j false))

def xiBreve {n : ℕ} (E : Experiment n) (i j : Fin n) : ℝ :=
  (1 - marginal E i true) * xi E i j true + marginal E i true * xi E i j false

def yBreve {n : ℕ} (E : Experiment n) (i : Fin n) : ℝ :=
  (1 - marginal E i true) * cmean E.design (fun z => z i = true) (E.outcome i) +
  marginal E i true * cmean E.design (fun z => z i = false) (E.outcome i)

def B1 {n : ℕ} (E : Experiment n) : ℝ :=
  (∑ i, ∑ j, if j = i then 0 else
    xiBreve E i j * xiBreve E j i +
    2 * yBreve E j * (xi E i j true - xi E i j false)) / ((n : ℝ) * dAvg E)

def B2 {n : ℕ} (E : Experiment n) : ℝ :=
  (∑ i, ∑ j, if j = i then 0 else
    ∑ a : Bool, ∑ b : Bool,
      (1 - 2 * bit a) * (1 - 2 * bit b) *
        ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j)) /
      ((n : ℝ) * dAvg E)

def sigmaSq {n : ℕ} (E : Experiment n) (i : Fin n) : ℝ :=
  var E.design (fun z => (if z i then E.outcome i z else 0) / marginal E i true -
    (if z i then 0 else E.outcome i z) / marginal E i false)

def sdSigmaSq {n : ℕ} (E : Experiment n) : ℝ :=
  Real.sqrt ((∑ i, (sigmaSq E i - (∑ j, sigmaSq E j) / n) ^ 2) / n)

def quadD {n : ℕ} (E : Experiment n) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * d E i j * v j

/-- Maximum Rayleigh value of the symmetric, nonnegative dependence matrix. -/
def lambdaMax {n : ℕ} (E : Experiment n) : ℝ :=
  sSup {r | ∃ v : Fin n → ℝ, (∑ i, v i ^ 2) = 1 ∧ r = quadD E v}

def vAVG {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ := dAvg E * vBER E z

def vMAX {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ := dMax E * vBER E z

def vSR {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ := lambdaMax E * vBER E z

def BoundedEffects {n : ℕ} (E : Experiment n) (K : ℝ) : Prop :=
  ∀ i z, |effect E i z| ≤ K

/-- Total variation on a finite space, one half of the sum of absolute mass differences. -/
def totalVariation {Ω : Type*} [Fintype Ω] (P Q : Law Ω) : ℝ :=
  (∑ ω, |P.mass ω - Q.mass ω|) / 2

def lrDistance {n : ℕ} (r : ℝ) (z z' : Assignment n) : ℝ :=
  Real.rpow (∑ i, Real.rpow |bit (z i) - bit (z' i)| r) (1 / r)

def conjugateC {n : ℕ} (E : Experiment n) (r : ℝ) : ℝ :=
  if r = 1 then Cinf E else Cp E (r / (r - 1))

def Coupling {Ω : Type*} [Fintype Ω] (P Q : Law Ω) (J : Law (Ω × Ω)) : Prop :=
  (∀ x, ∑ y, J.mass (x,y) = P.mass x) ∧
  (∀ y, ∑ x, J.mass (x,y) = Q.mass y)

/-- The paper's infimum of expected L_r ground distance, over probability couplings.
This is a first-order transport cost; product couplings make the cost set nonempty. -/
def wasserstein {n : ℕ} (r : ℝ) (P Q : Law (Assignment n)) : ℝ :=
  sInf {v | ∃ J : Law (Assignment n × Assignment n), Coupling P Q J ∧
    v = mean J (fun zz => lrDistance r zz.1 zz.2)}

/-- A sequence of positive finite populations whose sizes tend to infinity. -/
structure Study where
  N : ℕ → ℕ
  positive : ∀ t, 0 < N t
  grows : Tendsto N atTop atTop
  experiment : (t : ℕ) → Experiment (N t)

def size (S : Study) (t : ℕ) : ℝ := S.N t

def RegularSequence (S : Study) (k q s : ℝ) : Prop :=
  ∀ t, Regular (S.experiment t) k q s

def Restricted (S : Study) : Prop :=
  Tendsto (fun t => dAvg (S.experiment t) / size S t) atTop (nhds 0)

def LittleO (f g : ℕ → ℝ) : Prop := Tendsto (fun t => f t / g t) atTop (nhds 0)

def BigO (f g : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ᶠ t in atTop, |f t| ≤ C * |g t|

/-- Every positive error threshold has a probability tending to zero. -/
def InProbability (S : Study) (X : (t : ℕ) → Assignment (S.N t) → ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun t => prob (S.experiment t).design (fun z => ε < |X t z|))
    atTop (nhds 0)

/-- The paper's stochastic order, with a uniform positive tail cutoff eventually. -/
def Op (S : Study) (X : (t : ℕ) → Assignment (S.N t) → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ K > 0, ∀ᶠ t in atTop,
    prob (S.experiment t).design (fun z => K * a t ≤ |X t z|) ≤ ε

/-- Definition 10: the iterated limit of lower scaled variance-error probabilities,
including existence of the inner limits. -/
def Conservative (S : Study) (Vhat : (t : ℕ) → Assignment (S.N t) → ℝ) : Prop :=
  ∃ L : ℝ → ℝ,
    (∀ ε > 0, Tendsto (fun t => prob (S.experiment t).design (fun z =>
      size S t / dAvg (S.experiment t) *
        (Vhat t z - var (S.experiment t).design (ht (S.experiment t))) ≤ -ε))
      atTop (nhds (L ε))) ∧ Tendsto L (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

def PositiveLiminf (a : ℕ → ℝ) : Prop :=
  ∃ c > 0, ∀ᶠ t in atTop, c ≤ a t

def InDistribution (S : Study) (X : (t : ℕ) → Assignment (S.N t) → ℝ)
    (G : ℝ → ℝ) : Prop :=
  ∀ x, ContinuousAt G x → Tendsto
    (fun t => prob (S.experiment t).design (fun z => X t z ≤ x)) atTop (nhds (G x))

def sharpLaw (α : ℝ) (hα : 0 < α ∧ α < 1) : Law (Fin 3) where
  mass := ![α/2, 1-α, α/2]
  nonneg := by intro i; fin_cases i <;> simp <;> linarith [hα.1, hα.2]
  total := by simp [Fin.sum_univ_succ]; ring

def sharpValue : Fin 3 → ℝ := ![-1,0,1]

def sharpCDF (α x : ℝ) : ℝ :=
  if x < -1 then 0 else if x < 0 then α/2 else if x < 1 then 1-α/2 else 1

abbrev MomentIndex := WithTop ℝ

def MomentBound {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ)
    (k : ℝ) (q : MomentIndex) : Prop :=
  if q = ⊤ then ∀ ω, 0 < P.mass ω → |X ω| ≤ k
  else mean P (fun ω => Real.rpow |X ω| (q.untopD 0)) ≤ Real.rpow k (q.untopD 0)

def RegularMix (S : Study) (k : ℝ) (q s : MomentIndex) : Prop :=
  0 < k ∧ 2 ≤ q ∧ 1 ≤ s ∧
  (∀ t i, k⁻¹ ≤ marginal (S.experiment t) i true ∧
    marginal (S.experiment t) i true ≤ 1-k⁻¹) ∧
  (∀ t i, MomentBound (S.experiment t).design ((S.experiment t).outcome i) k q) ∧
  (∀ t i b, MomentBound (S.experiment t).design (potential (S.experiment t) i b) k s)

def AdmissibleObserved (S : Study) (q : MomentIndex) : Prop :=
  2 ≤ q ∧ ∃ k > 0, ∀ t i,
    MomentBound (S.experiment t).design ((S.experiment t).outcome i) k q

def AdmissiblePotential (S : Study) (s : MomentIndex) : Prop :=
  1 ≤ s ∧ ∃ k > 0, ∀ t i b,
    MomentBound (S.experiment t).design (potential (S.experiment t) i b) k s

/-- Maxima over all admissible bounds, allowing their constants to vary.
T45 explicitly restricts to sequences for which these maxima exist and are attained. -/
def MaximalMoments (S : Study) (q s : MomentIndex) : Prop :=
  AdmissibleObserved S q ∧ (∀ r, AdmissibleObserved S r → r ≤ q) ∧
  AdmissiblePotential S s ∧ (∀ r, AdmissiblePotential S r → r ≤ s)

def extExponent (q : MomentIndex) : ℝ :=
  if q = ⊤ then 1 else (q.untopD 0-2)/(q.untopD 0)

def intExponent (s : MomentIndex) : ℝ :=
  if s = ⊤ then 1 else (s.untopD 0-1)/(s.untopD 0)

def CompleteSequence (S : Study) : Prop :=
  ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∀ t, Complete (S.experiment t) ⌊p*size S t⌋₊

def EstimatorClaims (S : Study) (θ a : ℕ → ℝ) : Prop :=
  InProbability S (fun t z => ht (S.experiment t) z-θ t) ∧
  InProbability S (fun t z => hajek (S.experiment t) z-θ t) ∧
  Op S (fun t z => ht (S.experiment t) z-θ t) a ∧
  Op S (fun t z => hajek (S.experiment t) z-θ t) a

def bernoulliRate (S : Study) (t : ℕ) : ℝ :=
  Real.sqrt (dAvg (S.experiment t)) / Real.sqrt (size S t)
end
end SAP.P009c
