import SAP.P002b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

def augmented {n k} (x : Fin n → Fin k → ℝ) (i : Fin n) : Option (Fin k) → ℝ
  | none => 1
  | some s => x i s

def xCirc {n k} (x : Fin n → Fin k → ℝ) (i : Fin n) : Option (Fin k) → ℝ
  | none => 0
  | some s => x i s

def normSq {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := ∑ j, v j ^ 2

def gram {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n)) :
    Matrix (Option (Fin k)) (Option (Fin k)) ℝ :=
  fun s t => groupMean S fun i => augmented x i s * augmented x i t

def score {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n)) (q : Fin n → ℝ) :
    Option (Fin k) → ℝ := fun s => groupMean S fun i => augmented x i s * q i

def rss {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n))
    (q : Fin n → ℝ) (c : Option (Fin k) → ℝ) : ℝ :=
  ∑ i ∈ S, (q i - dotProduct (augmented x i) c)^2

/-- Full-rank OLS uses the inverse normal equations. On singular arms it uses
a fixed least-squares minimizer, as in the audited declarations; finite real least
squares has such a minimizer. Thus the last branch is unreachable. This convention
fills the paper's unspecified choice on singular arms. -/
def ols {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n)) (q : Fin n → ℝ) :
    Option (Fin k) → ℝ :=
  if (gram x S).det ≠ 0 then (gram x S)⁻¹ *ᵥ score x S q
  else if h : ∃ c, ∀ b, rss x S q c ≤ rss x S q b then Classical.choose h else 0

def psi {n k} (P : CovPopulation n k) (a : Bool) (β : ℝ) :=
  ols P.x Finset.univ (w P.pop a β)

def residual {n k} (P : CovPopulation n k) (a : Bool) (β : ℝ) (i : Fin n) : ℝ :=
  w P.pop a β i - dotProduct (augmented P.x i) (psi P a β)

def fitted {n k} (P : CovPopulation n k) (q : Fin n → ℝ)
    (S : Finset (Fin n)) (a : Bool) := ols P.x (if a then S else Sᶜ) q

def slopeDot {k} (x : Fin k → ℝ) (c : Option (Fin k) → ℝ) : ℝ :=
  ∑ j, x j * c (some j)

def adjustedWith {n k} (P : CovPopulation n k) (q : Fin n → ℝ)
    (S : Finset (Fin n)) (c1 c0 : Option (Fin k) → ℝ) : ℝ :=
  groupMean S (fun i => q i - slopeDot (P.x i) c1) -
  groupMean Sᶜ (fun i => q i - slopeDot (P.x i) c0)

def adjustedTau {n k} (P : CovPopulation n k) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  adjustedWith P q S (fitted P q S true) (fitted P q S false)

/-- Oracle adjustment uses population slopes and observed adjusted responses. -/
def oracleTau {n k} (P : CovPopulation n k) (β : ℝ) (S : Finset (Fin n)) : ℝ :=
  adjustedWith P (observedW P.pop β S) S (psi P true β) (psi P false β)

def oracleStar {n k} (P : CovPopulation n k) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  adjustedWith P q S (ols P.x Finset.univ q) (ols P.x Finset.univ q)

def adjustedSigma2 {n k} (P : CovPopulation n k) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  rss P.x S q (fitted P q S true) / (P.pop.n1 : ℝ)^2 +
  rss P.x Sᶜ q (fitted P q S false) / (controlSize P.pop)^2

def adjustedAR {n k} (P : CovPopulation n k) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ≥0∞ :=
  absStudent (adjustedTau P q S) (adjustedSigma2 P q S)

def adjustedAccepted {n k} (P : CovPopulation n k) (β α : ℝ) (S : Finset (Fin n)) : Prop :=
  adjustedAR P (observedW P.pop β S) S ≤
    quantile P.pop (adjustedAR P (observedW P.pop β S)) α

def adjustedCoverage {n k} (P : CovPopulation n k) (β α : ℝ) : ℝ :=
  probability P.pop (adjustedAccepted P β α)

/-- The adjusted parameter space. The smallest-eigenvalue condition is stated
as the Rayleigh inequality for the covariate second-moment matrix. -/
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

end
end SAP.P002b
