import SAP.P002a.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P002a
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
attribute [local instance] Classical.propDecidable

def T12Printed : Prop :=
    let P := signModel 4
    let S : Finset (Fin 8) := {0,1,2,3}
    Theta P 0 (1/2) 1 ∧ late P = 0 ∧ S ∈ assignments P ∧
    designVariance P (rawTau P (observedW P 0 S)) = 1/28 ∧
    (fraction P)^2*(1-fraction P)^2/(8-1) *
      (controlSize P*(P.n1 : ℝ)/8) *
      (armMean (observedW P 0 S) S true-armMean (observedW P 0 S) S false)^2 = 1/14 ∧
    designVariance P (rawTau P (observedW P 0 S)) <
      (fraction P)^2*(1-fraction P)^2/(8-1) *
      (controlSize P*(P.n1 : ℝ)/8) *
      (armMean (observedW P 0 S) S true-armMean (observedW P 0 S) S false)^2

def T12Values : Prop :=
  let P := signModel 4
  let S : Finset (Fin 8) := {0,1,2,3}
  (assignments P).card = 70 ∧
  armMean (observedW P 0 S) S true - armMean (observedW P 0 S) S false = -2 ∧
  (fraction P)^2*(1-fraction P)^2/(8-1) *
    (armMean (observedW P 0 S) S true - armMean (observedW P 0 S) S false)^2 = 1/28

def T12Statement : Prop := T12Printed ∧ T12Values

def T13Statement : Prop :=
  ∀ {n : ℕ} (P : Population n) (h : ValidDesign P)
    (q : Fin n → ℝ) (S : Finset (Fin n)) (hS : S ∈ assignments P)
    (r : ℝ) (hr : 0 < r ∧ r ≤ 1/2)
    (hlo : r*(n : ℝ) ≤ (P.n1 : ℝ)) (hhi : (P.n1 : ℝ) ≤ (1-r)*(n : ℝ)),
  (fraction P)^2*(1-fraction P)^2/((n : ℝ)-1)*(armMean q S true-armMean q S false)^2 ≤
      designVariance P (rawTau P q) ∧
    r^2*(1-r)^2/(n : ℝ)*(armMean q S true-armMean q S false)^2 ≤
      designVariance P (rawTau P q)

def T14Statement : Prop :=
  (∀ m, 2 ≤ m →
      let P := signModel m
      Theta P 0 (1/2) 1 ∧ late P = 0 ∧
      (∀ S ∈ assignments P,
        let q := observedW P 0 S
        designVariance P (rawTau P q) = 1/(4*(((2*m : ℕ) : ℝ)-1)) ∧
        probability P (fun T => |Real.sqrt (rawSigma2 P q T) /
          designVariance P (rawTau P q)-1| ≥ 1/2) = 1 ∧
        (∀ κ : ℝ, 0 < κ → probability P (fun T => |rawSigma2 P q T /
          designVariance P (rawTau P q)-1| ≥ κ) ≤ 2/(((2*m : ℕ) : ℝ)*κ)))) ∧
    Tendsto (fun j =>
      let P := signModel (j+2)
      probability P (fun T => |Real.sqrt (rawSigma2 P (fun i => P.y i false) T) /
        designVariance P (rawTau P (fun i => P.y i false))-1| ≥ 1/2)) atTop (nhds 1)

def T15Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω)
    [IsProbabilityMeasure μ] (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ n, Population (sizes n))
    (Z : ∀ n, Ω → Finset (Fin (sizes n))) (δ r A : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A)
    (hP : ∀ n, Theta (P n) δ r A)
    (hpositive : ∀ n a, 0 < popVar (w (P n) a (late (P n))))
    (hZ : RandomizationSequence P μ Z)
    (sub : ℕ → ℕ) (hsub : StrictMono sub)
    (_hconditional : ∀ n ω, 0 < designVariance (P n)
      (rawTau (P n) (observedW (P n) (late (P n)) (Z n ω)))),
  ∀ᵐ ω ∂μ, ∀ κ : ℝ, 0 < κ → Tendsto (fun j =>
      let N := sub j
      let q := observedW (P N) (late (P N)) (Z N ω)
      probability (P N) (fun S => |rawSigma2 (P N) q S /
        designVariance (P N) (rawTau (P N) q) - 1| ≥ κ)) atTop (nhds 0)

end
end SAP.P002a
