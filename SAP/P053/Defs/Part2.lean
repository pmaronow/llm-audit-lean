import SAP.P053.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Potential outcomes are fixed; complete random assignment is the only randomness. Means and
variances are finite sums, with divisors n-1 and the pooled residual divisor N-2. Regularity
records S5 itself, including moment limits and a raw fourth-moment bound; it contains no
estimator-consistency or central-limit premise. Its arm-size field excludes zero divisors
eventually, which is the domain relevant to all asymptotic assertions. Gaussian probabilities
are finite, and normalCritical is used only for 0 < alpha < 1.
-/

namespace SAP.P053
open Filter
open scoped BigOperators Topology
noncomputable section

structure Population where
  n1 : ℕ
  n0 : ℕ
  Y1 : Fin (n1 + n0) → ℝ
  Y0 : Fin (n1 + n0) → ℝ

abbrev Population.size (P : Population) : ℕ := P.n1 + P.n0

def sampleMean {ι : Type*} [DecidableEq ι] (s : Finset ι) (y : ι → ℝ) : ℝ :=
  (∑ i ∈ s, y i) / (s.card : ℝ)

def centeredSS {ι : Type*} [DecidableEq ι] (s : Finset ι) (y : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (y i - sampleMean s y)^2

def sampleVariance {ι : Type*} [DecidableEq ι] (s : Finset ι) (y : ι → ℝ) : ℝ :=
  centeredSS s y / ((s.card : ℝ) - 1)

def populationMean (P : Population) (y : Fin P.size → ℝ) : ℝ :=
  sampleMean Finset.univ y

def populationVariance (P : Population) (y : Fin P.size → ℝ) : ℝ :=
  sampleVariance Finset.univ y

def averageEffect (P : Population) : ℝ := populationMean P P.Y1 - populationMean P P.Y0

def unitEffects (P : Population) : Fin P.size → ℝ := fun i => P.Y1 i - P.Y0 i

def SharpNull (P : Population) : Prop := ∀ i, P.Y1 i = P.Y0 i

def ConstantEffects (P : Population) : Prop := ∀ i, unitEffects P i = averageEffect P

def observed (P : Population) (z : Finset (Fin P.size)) : Fin P.size → ℝ :=
  fun i => if i ∈ z then P.Y1 i else P.Y0 i

def difference (P : Population) (z : Finset (Fin P.size)) (y : Fin P.size → ℝ) : ℝ :=
  sampleMean z y - sampleMean zᶜ y

def estimate (P : Population) (z : Finset (Fin P.size)) : ℝ := difference P z (observed P z)

def randomizationMean (P : Population) (X : Finset (Fin P.size) → ℝ) : ℝ :=
  (∑ z ∈ support P.n1, X z) / ((support (ι := Fin P.size) P.n1).card : ℝ)

def randomizationVariance (P : Population) (X : Finset (Fin P.size) → ℝ) : ℝ :=
  randomizationMean P (fun z => (X z - randomizationMean P X)^2)

def randomizationProbability (P : Population) (event : Finset (Fin P.size) → Prop) : ℝ := by
  classical
  exact ((support P.n1).filter event).card /
    ((support (ι := Fin P.size) P.n1).card : ℝ)

def residualSS (P : Population) (z : Finset (Fin P.size)) : ℝ :=
  centeredSS z (observed P z) + centeredSS zᶜ (observed P z)

def olsVariance (P : Population) (z : Finset (Fin P.size)) : ℝ :=
  residualSS P z / ((P.size : ℝ) - 2) * (1/(P.n1 : ℝ) + 1/(P.n0 : ℝ))

def neymanVariance (P : Population) (z : Finset (Fin P.size)) : ℝ :=
  sampleVariance z (observed P z) / P.n1 +
    sampleVariance zᶜ (observed P z) / P.n0

def fisherVariance (P : Population) (z : Finset (Fin P.size)) : ℝ :=
  (P.size : ℝ) * populationVariance P (observed P z) / ((P.n1 : ℝ) * P.n0)

structure Regularity (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ) : Prop where
  size_diverges : Tendsto (fun k => (E k).size) atTop atTop
  arm_sizes : ∀ᶠ k in atTop, 2 ≤ (E k).n1 ∧ 2 ≤ (E k).n0
  p_positive : 0 < p
  p_less_one : p < 1
  allocation : Tendsto (fun k => ((E k).n1 : ℝ)/(E k).size) atTop (nhds p)
  variance1 : Tendsto (fun k => populationVariance (E k) (E k).Y1) atTop (nhds v1)
  variance0 : Tendsto (fun k => populationVariance (E k) (E k).Y0) atTop (nhds v0)
  varianceEffect : Tendsto (fun k => populationVariance (E k) (unitEffects (E k))) atTop (nhds vt)
  average_effect : Tendsto (fun k => averageEffect (E k)) atTop (nhds tauInf)
  fourth_moments : ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ,
    (∑ i : Fin ((E k).n1+(E k).n0), (((E k).Y1 i)^4 + ((E k).Y0 i)^4)) /
      ((E k).size : ℝ) ≤ B

def InProbability (E : ℕ → Population)
    (X : (k : ℕ) → Finset (Fin (E k).size) → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun k => randomizationProbability (E k) (fun z => ε < |X k z-c|)) atTop (nhds 0)

def LittleOInvSize (E : ℕ → Population)
    (X : (k : ℕ) → Finset (Fin (E k).size) → ℝ) : Prop :=
  InProbability E (fun k z => ((E k).size : ℝ)*X k z) 0

def neymanLimit (p v1 v0 : ℝ) : ℝ := v1/p + v0/(1-p)

def olsLimit (p v1 v0 : ℝ) : ℝ := v1/(1-p) + v0/p

def standardNormalCDF (t : ℝ) : ℝ :=
  ((ProbabilityTheory.gaussianReal 0 1) (Set.Iic t)).toReal

def normalCritical (α : ℝ) : ℝ := sInf {t : ℝ | 1-α/2 ≤ standardNormalCDF t}

def heterogeneousWitness (k : ℕ) : Population where
  n1 := 2*(k+1)
  n0 := 8*(k+1)
  Y0 := fun i => if i.val < 5*(k+1) then 1 else -1
  Y1 := fun i => 2*(if i.val < 5*(k+1) then 1 else -1)

end
end SAP.P053
