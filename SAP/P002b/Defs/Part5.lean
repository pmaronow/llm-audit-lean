import SAP.P002b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory

/-- The explicit centered four-unit, two-covariate counterexample. -/
def T16Statement : Prop :=
  (∀ s, ∑ i, coordinateExample i s = 0) ∧
  (∀ s, mean (fun i => coordinateExample i s ^ 4) = 1/2) ∧
  (∀ s t, mean (fun i => coordinateExample i s * coordinateExample i t) =
    if s = t then 1/2 else 0) ∧
  maximum (fun i => normSq (augmented coordinateExample i)) = 2 ∧
  1 + (∑ s, maximum (fun i => coordinateExample i s ^ 2)) = 3

/-- The finite corrected bounds and their fixed-dimension order consequence. -/
def T17Statement : Prop :=
  (∀ {n k : ℕ} (x : Fin n → Fin k → ℝ), 0 < n →
    ∀ A : ℝ, 0 ≤ A → (∀ s, mean (fun i => x i s ^ 4) ≤ A) →
    (∀ s, maximum (fun i => |x i s|) ≤ Real.sqrt (Real.sqrt (A * (n : ℝ)))) ∧
    maximum (fun i => normSq (augmented x i)) ≤
      1 + (∑ s, maximum (fun i => x i s ^ 2)) ∧
    1 + (∑ s, maximum (fun i => x i s ^ 2)) ≤
      1 + (k : ℝ) * Real.sqrt (A * (n : ℝ))) ∧
  (∀ (k : ℕ) (A : ℝ), 0 ≤ A →
    ∀ x : ∀ j : ℕ, Fin (j+1) → Fin k → ℝ,
    (∀ j s, mean (fun i => x j i s ^ 4) ≤ A) →
    Asymptotics.IsBigO atTop
      (fun j => maximum (fun i => normSq (augmented (x j) i)))
      (fun j => Real.sqrt ((j+1 : ℕ) : ℝ)))

/-- Both exact corrected differences of feasible and oracle adjustment. -/
def T18Statement : Prop :=
  ∀ {n k : ℕ} (P : CovPopulation n k) (β : ℝ) (S : Finset (Fin n)),
    ValidDesign P.pop → S ∈ assignments P.pop →
    (gram P.x S).det ≠ 0 → (gram P.x Sᶜ).det ≠ 0 →
    (adjustedTau P (observedW P.pop β S) S - oracleTau P β S =
      -groupMean S (fun i => slopeDot (P.x i)
        (fitted P (observedW P.pop β S) S true - psi P true β)) +
       groupMean Sᶜ (fun i => slopeDot (P.x i)
        (fitted P (observedW P.pop β S) S false - psi P false β))) ∧
    (adjustedTau P (observedW P.pop β S) S - oracleTau P β S =
      -groupMean S (fun i => dotProduct (xCirc P.x i)
        ((gram P.x S)⁻¹ *ᵥ score P.x S (residual P true β))) +
       groupMean Sᶜ (fun i => dotProduct (xCirc P.x i)
        ((gram P.x Sᶜ)⁻¹ *ᵥ score P.x Sᶜ (residual P false β))))

/-- The sign-corrected coefficient error and actual residual cross term. -/
def T19Statement : Prop :=
  ∀ {n k : ℕ} (P : CovPopulation n k) (β : ℝ) (S : Finset (Fin n))
    (a : Bool), ValidDesign P.pop → S ∈ assignments P.pop →
    let A := if a then S else Sᶜ
    (gram P.x A).det ≠ 0 →
    (psi P a β - fitted P (observedW P.pop β S) S a =
      -(gram P.x A)⁻¹ *ᵥ score P.x A (residual P a β)) ∧
    (-2 * groupMean A (fun i => residual P a β i *
        dotProduct (augmented P.x i)
          (fitted P (observedW P.pop β S) S a - psi P a β)) =
      -2 * dotProduct (score P.x A (residual P a β))
        ((gram P.x A)⁻¹ *ᵥ score P.x A (residual P a β)))

/-- Oracle centering at the LATE, followed by the well-defined control remainder limit. -/
def T20Statement : Prop :=
  (∀ {n k : ℕ} (P : CovPopulation n k), ValidDesign P.pop →
    MonotoneReceipt P.pop → (compliers P.pop).Nonempty →
    (∀ s, ∑ i, P.x i s = 0) → (gram P.x Finset.univ).det ≠ 0 →
    ∀ S : Finset (Fin n), S ∈ assignments P.pop →
    psi P true (late P.pop) none = mean (w P.pop true (late P.pop)) ∧
    psi P false (late P.pop) none = mean (w P.pop false (late P.pop)) ∧
    mean (w P.pop true (late P.pop)) - mean (w P.pop false (late P.pop)) = 0 ∧
    psi P true (late P.pop) none - psi P false (late P.pop) none = 0 ∧
    oracleTau P (late P.pop) S = groupMean S (residual P true (late P.pop)) -
      groupMean Sᶜ (residual P false (late P.pop))) ∧
  (∀ (sizes : ℕ → ℕ), StrictMono sizes → ∀ (k : ℕ)
    (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ),
    0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
    (0 < r ∧ r ≤ 1/2) → (∀ j, Xi (P j) δ e A B r) →
    (∀ j, 0 < designVariance (P j).pop (oracleTau (P j) (late (P j).pop))) →
    (∀ j S, S ∈ assignments (P j).pop → (gram (P j).x Sᶜ).det ≠ 0) →
    ∀ κ : ℝ, 0 < κ → Tendsto (fun j => probability (P j).pop
      (fun S => κ ≤ |controlRemainder (P j) S|)) atTop (nhds 0))

end
end SAP.P002b
