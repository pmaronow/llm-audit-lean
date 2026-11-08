import SAP.P002b.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory

/-- Existence of a completed Algorithm 2/4 run and correctness of completed runs. -/
def T22Statement : Prop :=
  ∀ (M : ℕ) (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ),
    0 < M → (0 < α ∧ α < 1) → DataGeneratedCoefficients Qf Qg →
    ARRegular Qf → (∀ m, ARRegular (Qg m)) →
    ∀ J : List ℝ, IntersectionList (fun m => arFunction (Qg m)) J → J ≠ [] →
    let f := arFunction Qf
    let g := fun m => arFunction (Qg m)
    (∃ pieces, Algorithm2Run g α J pieces) ∧
    ∀ pieces, Algorithm2Run g α J pieces →
      pieces.length ≤ J.length + 1 ∧
      (pieces.map (fun p => p.right)).Pairwise (· < ·) ∧
      (∀ p ∈ pieces, p.right = ⊤ ∨ ∃ e : ℝ, p.right = (e : EReal) ∧ e ∈ J) ∧
      (∀ β : ℝ, ∃ p ∈ pieces, β ∈ closedInterval p.left p.right) ∧
      (∀ p ∈ pieces, ∀ β ∈ closedInterval p.left p.right,
        p.index ∈ mcIndices g α β) ∧
      (∀ p ∈ pieces, pieceSet f g p = mcSet f g α ∩ closedInterval p.left p.right) ∧
      returnedSet f g pieces = mcSet f g α

/-- Corrected (H.1), including all closed gap endpoints. -/
def T23Statement : Prop :=
  ∀ (M : ℕ) (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ),
    0 < M → (0 < α ∧ α < 1) → DataGeneratedCoefficients Qf Qg →
    ARRegular Qf → (∀ m, ARRegular (Qg m)) →
    ∀ (J : List ℝ) (pieces : List (RecordedPiece M)), J ≠ [] →
    Algorithm1Run (fun m => arFunction (Qg m)) α J pieces →
    let f := arFunction Qf
    let g := fun m => arFunction (Qg m)
    ∀ p ∈ pieces,
      (∀ β ∈ closedInterval p.left p.right,
        p.index ∈ mcIndices g α β ∧ g p.index β = (mcCritical g α β)^2) ∧
      pieceSet f g p = mcSet f g α ∩ closedInterval p.left p.right

/-- Corrected OLS linearity, adjusted contrast, and Wald cancellation. -/
def T24Statement : Prop :=
  ∀ {n k : ℕ} (P : CovPopulation n k) (S : Finset (Fin n))
    (Y D : Fin n → ℝ) (β : ℝ), ValidDesign P.pop → S ∈ assignments P.pop →
    (gram P.x S).det ≠ 0 → (gram P.x Sᶜ).det ≠ 0 →
    (∀ a, fitted P (fun i => Y i - β * D i) S a =
      fitted P Y S a - β • fitted P D S a) ∧
    adjustedTau P (fun i => Y i - β * D i) S =
      adjustedTau P Y S - β * adjustedTau P D S ∧
    (adjustedTau P D S ≠ 0 → adjustedTau P
      (fun i => Y i - (adjustedTau P Y S / adjustedTau P D S) * D i) S = 0)

/-- Baseline recovery, the true LATE, and both finite-sample coverage bounds. -/
def T25Statement : Prop :=
  ∀ {n k : ℕ} (P : CovPopulation n k) (β : ℝ), ValidDesign P.pop →
    MonotoneReceipt P.pop → (compliers P.pop).Nonempty →
    (∀ i, P.pop.y i true = P.pop.y i false + β) →
    (∀ S : Finset (Fin n), observedW P.pop β S = fun i => P.pop.y i false) ∧
    late P.pop = β ∧
    ∀ α : ℝ, (0 < α ∧ α < 1) →
      1-α ≤ coverage P.pop β α ∧ 1-α ≤ adjustedCoverage P β α

/-- Affine contrast, adjusted Wald membership, and IV identities from Remark 4. -/
def T26Statement : Prop :=
  ∀ {n k : ℕ} (P : CovPopulation n k) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)), ValidDesign P.pop → S ∈ assignments P.pop →
    (∀ s, ∑ i, P.x i s = 0) →
    (gram P.x S).det ≠ 0 → (gram P.x Sᶜ).det ≠ 0 →
    (∀ β, adjustedTau P (fun i => Y i - β * D i) S =
      adjustedTau P Y S - β * adjustedTau P D S) ∧
    (adjustedTau P D S ≠ 0 → ∀ α : ℝ, (0 < α ∧ α < 1) →
      adjustedTau P (fun i => Y i - adjustedWald P Y D S * D i) S = 0 ∧
      adjustedAR P (fun i => Y i - adjustedWald P Y D S * D i) S = 0 ∧
      adjustedAR P (fun i => Y i - adjustedWald P Y D S * D i) S ≤
        quantile P.pop (adjustedAR P (fun i => Y i - adjustedWald P Y D S * D i)) α) ∧
    ((ivCross P D S).det ≠ 0 → (instrumentGram P S).det ≠ 0 →
      adjustedTau P D S ≠ 0 →
      adjustedTau P D S * ivCoefficients P Y D S (.inl 0) = adjustedTau P Y S ∧
      ivCoefficients P Y D S (.inl 0) = adjustedWald P Y D S)

/-- All four conclusions of Lemma 1, including either infinite endpoint. -/
def T27Statement : Prop :=
  ∀ (M : ℕ) (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ),
    0 < M → (0 < α ∧ α < 1) → DataGeneratedCoefficients Qf Qg →
    ARRegular Qf → (∀ m, ARRegular (Qg m)) →
    ∀ l u : EReal, l < u →
    (∀ β ∈ openInterval l u, ¬ crossing (fun m => arFunction (Qg m)) β) →
    let g := fun m => arFunction (Qg m)
    (∀ x ∈ openInterval l u, ∀ y ∈ openInterval l u, mcIndices g α x = mcIndices g α y) ∧
    (∀ x ∈ openInterval l u, ∀ a b : ℝ, l = (a : EReal) → u = (b : EReal) →
      mcIndices g α x ⊆ mcIndices g α a ∧ mcIndices g α x ⊆ mcIndices g α b) ∧
    (∀ x ∈ openInterval l u, ∀ b : ℝ, l = ⊥ → u = (b : EReal) →
      mcIndices g α x ⊆ mcIndices g α b) ∧
    (∀ x ∈ openInterval l u, ∀ a : ℝ, u = ⊤ → l = (a : EReal) →
      mcIndices g α x ⊆ mcIndices g α a)

/-- The printed universal nominal-coverage limit in Theorem 1 is false. -/
def T29Statement : Prop :=
  ¬ (∀ δ r A α : ℝ, δ < 1 → (0 < r ∧ r ≤ 1/2) → 0 < A →
    (0 < α ∧ α < 1) → Tendsto (fun n => infCoverageTheta n δ r A α)
      atTop (nhds (ENNReal.ofReal (1-α))))

/-- The printed universal nominal-coverage limit in Theorem 2 is false. -/
def T30Statement : Prop :=
  ¬ (∀ (k : ℕ) (δ e A B r α : ℝ),
    0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
    (0 < r ∧ r ≤ 1/2) → (0 < α ∧ α < 1) →
    Tendsto (fun n => infCoverageXi n k δ e A B r α)
      atTop (nhds (ENNReal.ofReal (1-α))))

end
end SAP.P002b
