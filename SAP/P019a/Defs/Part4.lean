import SAP.P019a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical
variable {Ω : Type*} [Fintype Ω]

def normalCDF (t : ℝ) : ℝ := ((gaussianReal 0 1) (Set.Iic t)).toReal

/-- Used with an explicit nonempty, bounded-below quantile set. -/
def normalQuantile (u : ℝ) : ℝ := sInf {x : ℝ | u ≤ normalCDF x}

/-- Weak convergence tested against every bounded continuous real function. -/
def WeakLimit {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (P : FiniteLaw Ω) (T : (n : ℕ) → (Fin n → Ω) → E) (Q : Measure E) : Prop :=
  ∀ f : E → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun n => (P.iid n).mean (fun s => f (T n s))) atTop (nhds (∫ x, f x ∂Q))

/-- Explicit value zero when the variance estimate is not positive. -/
def studentized (estimate null varianceEstimate : ℝ) : ℝ :=
  if 0 < varianceEstimate then (estimate - null) / Real.sqrt varianceEstimate else 0

/-- Normal p-value of the completed statistic. -/
def normalPValue (estimate null varianceEstimate : ℝ) : ℝ :=
  2 * normalCDF (-|studentized estimate null varianceEstimate|)

def Study.betaPsi (S : Study Ω) (ω : Ω) : ℝ :=
  bitVal (S.Y ω) / S.law.prob (fun t => S.Y t = true) *
    ((bitVal (S.Z ω)-S.gamma) / (S.gamma*(1-S.gamma))) *
    ((S.W ω : ℝ) - S.law.ce (fun t => (S.W t : ℝ)) (fun t => S.Y t = true))

/-- The entire assignment vector is independent of all latent coordinates,
and its five coordinates have the product of their marginal laws. -/
def jointAssignmentStable (P : FiniteLaw Ω) (S : Fin 5 → Study Ω) : Prop :=
  ∀ (f : (Fin 5 → ℕ) → (Fin 5 → Bool) → (Fin 5 → Bool) → ℝ) (a : Fin 5 → Bool),
    P.mean (fun ω => if ∀ j, (S j).Z ω = a j then
      f (fun j => (S j).W ω) (fun j => (S j).X ω) (fun j => (S j).Y ω) else 0) =
      (∏ j, P.prob (fun ω => (S j).Z ω = a j)) *
        P.mean (fun ω => f (fun j => (S j).W ω) (fun j => (S j).X ω) (fun j => (S j).Y ω))

def latentVectorFibre (S : Fin 5 → Study Ω) (ω t : Ω) : Prop :=
  ∀ j, (S j).W t = (S j).W ω ∧ (S j).X t = (S j).X ω ∧ (S j).Y t = (S j).Y ω

def fisherStatistic (p : Fin 5 → ℝ) : ℝ := -2 * ∑ j, Real.log (p j)

def chiSquareTen : Measure ℝ :=
  (Measure.pi (fun _ : Fin 10 => gaussianReal 0 1)).map (fun x => ∑ j, (x j)^2)

def bitSign (b : Bool) : ℝ := if b then 1 else -1

def prefixSign (ω : Fin 128) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, bitSign (fairBit ω (i+2))

def suffixSign (ω : Fin 128) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.Ico (j+1) 5, bitSign (fairBit ω (i+2))

/-- Lists precede direct questions; each baseline uses earlier assignments. -/
def sequentialStudy (j : Fin 5) : Study (Fin 128) where
  law := uniformFin 128 (by norm_num)
  W := fun ω => if bitSign (fairBit ω 1) * prefixSign ω j.val = 1 then 2 else 1
  X := fun ω => fairBit ω 0
  Y := fun ω => fairBit ω 0 && decide (suffixSign ω j.val = 1)
  Z := fun ω => fairBit ω (j.val+2)
  V := fun ω => (if bitSign (fairBit ω 1) * prefixSign ω j.val = 1 then 2 else 1) +
    (if fairBit ω 0 && fairBit ω (j.val+2) then 1 else 0)

def sequentialPsi (j : Fin 5) (ω : Fin 128) : ℝ :=
  2*bitVal (fairBit ω 0)*bitSign (fairBit ω 1)*
    (if j.val < 4 then prefixSign ω (j.val+1)+prefixSign ω 5 else prefixSign ω 5)

def correlatedNormals (e : Fin 5 → ℝ) (j : Fin 5) : ℝ :=
  if j.val < 4 then (e j + e 4)/Real.sqrt 2 else e 4

def sequentialFisherLimit : Measure ℝ :=
  (Measure.pi (fun _ : Fin 5 => gaussianReal 0 1)).map (fun e =>
    fisherStatistic (fun j => normalPValue (correlatedNormals e j) 0 1))

/-- Used only together with integrability of x and x². -/
def continuousVariance (P : Measure ℝ) : ℝ :=
  (∫ x, x^2 ∂P) - (∫ x, x ∂P)^2

end
end SAP.P019a
