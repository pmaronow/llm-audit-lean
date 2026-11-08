import SAP.P001g.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-! A placebo-null counterexample whose rejection event explicitly requires
nonzero Gram determinants, positive residual risk, and positive residual degrees
of freedom. No singular regression or zero denominator counts as a rejection. -/

def placeboX (i : Fin 12) : ℝ := if i.val/4=0 then -1 else if i.val/4=1 then 0 else 1

def placeboZ (i : Fin 12) : ℝ := if i.val%4 < 2 then -1 else 1

def placeboD (i : Fin 12) : ℝ := if i.val%2=1 then 1 else 0

def placeboW (i : Fin 12) : ℝ := (placeboX i)^2 + placeboZ i/2

def placeboRegressor (i : Fin 12) : Fin 3 → ℝ := ![1,placeboX i,placeboW i]

def placeboFTest_gram {k : ℕ} (R : Fin 12 → Fin k → ℝ)
    (q : Fin 12 → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun a b => ∑ j, q j * R j a * R j b

def placeboFTest_cross {k : ℕ} (R : Fin 12 → Fin k → ℝ)
    (q : Fin 12 → ℝ) : Fin k → ℝ := fun a => ∑ j, q j * R j a * placeboD j

def placeboFTest_coef {k : ℕ} (R : Fin 12 → Fin k → ℝ)
    (q : Fin 12 → ℝ) : Fin k → ℝ :=
  (placeboFTest_gram R q)⁻¹.mulVec (placeboFTest_cross R q)

def placeboFTest_risk {k : ℕ} (R : Fin 12 → Fin k → ℝ)
    (q : Fin 12 → ℝ) : ℝ :=
  ∑ j, q j * (placeboD j - ∑ a, R j a * placeboFTest_coef R q a)^2

def placeboFTest_restricted (j : Fin 12) : Fin 2 → ℝ := ![1, placeboX j]

/-- Normalized empirical cell counts, used only at sample sizes above three. -/
def placeboFrequency {n : ℕ} (s : Fin n → Fin 12) (j : Fin 12) : ℝ :=
  (∑ i : Fin n, if s i = j then (1 : ℝ) else 0) / (n : ℝ)

/-- The two normalized sample Gram matrices are nonsingular and the full
normalized residual sum of squares is strictly positive. -/
def placeboGood {n : ℕ} (s : Fin n → Fin 12) : Prop :=
  3 < n ∧
  (placeboFTest_gram placeboFTest_restricted (placeboFrequency s)).det ≠ 0 ∧
  (placeboFTest_gram placeboRegressor (placeboFrequency s)).det ≠ 0 ∧
  0 < placeboFTest_risk placeboRegressor (placeboFrequency s)

def placeboF {n : ℕ} (s : Fin n → Fin 12) : ℝ :=
  placeboFStatistic (fun i => fun _ : Fin 1 => placeboX (s i))
    (fun i => fun _ : Fin 1 => placeboW (s i)) (fun i => placeboD (s i))

/-- At nominal level one half there is an iid conditional-independence null
with actual reference quantiles and limiting guarded rejection probability one. -/
def T124Statement : Prop :=
  ∃ (μ : Measure (ℕ → Fin 12)) (critical : ℕ → ℝ),
    IsProbabilityMeasure μ ∧
    IID μ (fun i ω => ((fun _ : Fin 1 => placeboX (ω i)),
      (fun _ : Fin 1 => placeboW (ω i)), placeboD (ω i))) ∧
    (∃ hX : Measurable (fun ω : ℕ → Fin 12 => fun _ : Fin 1 => placeboX (ω 0)),
      CI μ (fun ω => fun _ : Fin 1 => placeboX (ω 0)) hX
        (fun ω => fun _ : Fin 1 => placeboW (ω 0)) (fun ω => placeboD (ω 0))) ∧
    (∀ i (ω : ℕ → Fin 12), placeboD (ω i) = 0 ∨ placeboD (ω i) = 1) ∧
    (∀ᵐ ω ∂μ, ∀ᶠ n in atTop, placeboGood (fun i : Fin n => ω i)) ∧
    (∀ n : ℕ, 3 < n → prob (fReference 1 (n - 3)) (Set.Iic (critical n)) = 1 / 2) ∧
    Tendsto (fun n => prob μ {ω | placeboGood (fun i : Fin n => ω i) ∧
      critical n < placeboF (fun i : Fin n => ω i)}) atTop (nhds 1)

end
end SAP.P001g
