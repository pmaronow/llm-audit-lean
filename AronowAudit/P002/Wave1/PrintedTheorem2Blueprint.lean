import AronowAudit.P002.P002_Audit

/-!
# P002-T30: refutation of printed Theorem 2 (main p. 11)

The target is the negation of the universal closure of printed Theorem 2, with its
numerical guards, the nested `infCoverageXi` (ENNReal, empty inner classes `⊤`) and
the ordinary limit to `ofReal (1-α)`.

Witness tuple: `k=1, δ=0, e=1/4, A=4, B=1/2, r=1/4, α=1/2`. Every model of this fixed
class has zero population residuals (B=1/2 moment collapse after OLS centring); on
observed assignments whose two arm Gram matrices are invertible the observed adjusted
AR statistic is `0` and the LATE is accepted; arm rank failure has probability at most
`1548/(n-1)` uniformly over the class; the class is nonempty (centred grid model);
hence the nested infimum is squeezed to `1`, not `1/2`.
-/

namespace AronowAudit.P002.Wave1.PrintedTheorem2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Negation of the universal coverage-limit claim in printed Theorem 2. -/
def Target : Prop :=
  ¬ (∀ (k : ℕ) (δ e A B r α : ℝ),
      0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
      (0 < r ∧ r ≤ 1/2) → (0 < α ∧ α < 1) →
      Tendsto (fun n => infCoverageXi n k δ e A B r α)
        atTop (nhds (ENNReal.ofReal (1-α))))

/-! ## Statements used by the nodes -/

/-- Under Xi with `e > 0` the full population Gram matrix (intercept and covariates) is
invertible: centring plus the Rayleigh bound give `b'Gb ≥ min(1,e)‖b‖²`
(`corrected_augmented_gram`, `gram_quadratic`). -/
def GramInvertible : Prop :=
  ∀ (n k : ℕ) (P : CovPopulation n k) (δ e A B r : ℝ), 0 < e → Xi P δ e A B r →
    (gram P.x Finset.univ).det ≠ 0

/-- Moment collapse: in the fixed class both population residual vectors at the LATE
vanish. -/
def ResidualsVanish : Prop :=
  ∀ (n : ℕ) (P : CovPopulation n 1), Xi P 0 (1/4) 4 (1/2) (1/4) →
    ∀ a i, residual P a (late P.pop) i = 0

/-- Acceptance on the full-rank event: with zero residuals, on an observed assignment
whose two arm Gram matrices are invertible both arm fits recover the population
coefficients, the intercepts coincide, the observed adjusted statistic and its variance
are zero, and the LATE is accepted for every `α`. -/
def FullRankAcceptance : Prop :=
  ∀ (n : ℕ) (P : CovPopulation n 1) (α : ℝ) (O : Finset (Fin n)),
    Xi P 0 (1/4) 4 (1/2) (1/4) →
    (∀ a i, residual P a (late P.pop) i = 0) →
    O ∈ assignments P.pop → (gram P.x O).det ≠ 0 → (gram P.x Oᶜ).det ≠ 0 →
    adjustedAccepted P (late P.pop) α O

/-- Exact without-replacement mean-squared error of both arm sample means, in the P002
expectation operator, using `AronowAudit.P031.sample_mean_squared_error` and
`AronowAudit.P031.expectation_compl`. -/
def SamplingMSE : Prop :=
  ∀ (n : ℕ) (P : Population n) (q : Fin n → ℝ), 2 ≤ P.n1 → 2 ≤ n - P.n1 →
    expectation P (fun S => (groupMean S q - mean q) ^ 2) =
      ((n : ℝ) - P.n1) / ((P.n1 : ℝ) * ((n : ℝ) - 1)) * ((∑ i, (q i - mean q) ^ 2) / n) ∧
    expectation P (fun S => (groupMean Sᶜ q - mean q) ^ 2) =
      (P.n1 : ℝ) / (((n : ℝ) - P.n1) * ((n : ℝ) - 1)) * ((∑ i, (q i - mean q) ^ 2) / n)

/-- Determinant of a one-covariate arm Gram matrix: `v - u²`, with `u, v` the arm means
of `x` and `x²`. -/
def ArmGramDet : Prop :=
  ∀ (n : ℕ) (x : Fin n → Fin 1 → ℝ) (S : Finset (Fin n)), S.Nonempty →
    (gram x S).det = groupMean S (fun i => x i 0 ^ 2) - (groupMean S (fun i => x i 0)) ^ 2

/-- Single-arm rank failure: Chebyshev for `v` and Markov for `u²` give
`Pr(det = 0) ≤ 16 f/Q² + 2 f ≤ 258 f`, with `f = (n-m)/(m(n-1))` for the arm size
`m`, `Q = mean x² ≥ 1/4`, `mean x⁴ ≤ 4`. -/
def SingleArmFailure : Prop :=
  ∀ (n : ℕ) (P : CovPopulation n 1), (∑ i, P.x i 0 = 0) →
    1/4 ≤ mean (fun i => P.x i 0 ^ 2) → mean (fun i => P.x i 0 ^ 4) ≤ 4 →
    2 ≤ P.pop.n1 → 2 ≤ n - P.pop.n1 →
    probability P.pop (fun S => (gram P.x S).det = 0) ≤
      258 * (((n : ℝ) - P.pop.n1) / ((P.pop.n1 : ℝ) * ((n : ℝ) - 1))) ∧
    probability P.pop (fun S => (gram P.x Sᶜ).det = 0) ≤
      258 * ((P.pop.n1 : ℝ) / (((n : ℝ) - P.pop.n1) * ((n : ℝ) - 1)))

/-- Class-uniform rank failure bound `1548/(n-1)` for either observed arm. -/
def ClassFailure : Prop :=
  ∀ (n : ℕ) (P : CovPopulation n 1), 2 ≤ n → Xi P 0 (1/4) 4 (1/2) (1/4) →
    probability P.pop (fun S => (gram P.x S).det = 0 ∨ (gram P.x Sᶜ).det = 0) ≤
      1548 / ((n : ℝ) - 1)

/-- Class-uniform coverage lower bound. -/
def CoverageLowerBound : Prop :=
  ∀ (n : ℕ) (P : CovPopulation n 1) (α : ℝ), 2 ≤ n → Xi P 0 (1/4) 4 (1/2) (1/4) →
    max 0 (1 - 1548 / ((n : ℝ) - 1)) ≤ adjustedCoverage P (late P.pop) α

/-- Nonemptiness: the centred grid model lies in the class for every `n ≥ 2` and every
real `β`, with LATE `β`. -/
def GridInClass : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ β : ℝ,
    Xi (degenerateCovModel n β) 0 (1/4) 4 (1/2) (1/4) ∧ late (degenerateCovModel n β).pop = β

/-- The nested ENNReal infimum of the fixed class tends to one. -/
def InfimumLimitOne : Prop :=
  ∀ α : ℝ, Tendsto (fun n => infCoverageXi n 1 0 (1/4) 4 (1/2) (1/4) α) atTop (nhds 1)

/-- Finite design-probability calculus for the P002 operators: bounds `0 ≤ · ≤ 1`,
monotonicity on the assignment set, union bound, complement (valid design) and Markov. -/
def ProbabilityCalculus : Prop :=
  ∀ (n : ℕ) (P : Population n),
    (∀ E : Finset (Fin n) → Prop, 0 ≤ probability P E ∧ probability P E ≤ 1) ∧
    (∀ (E F : Finset (Fin n) → Prop), (∀ S ∈ assignments P, E S → F S) →
      probability P E ≤ probability P F) ∧
    (∀ (E F : Finset (Fin n) → Prop),
      probability P (fun S => E S ∨ F S) ≤ probability P E + probability P F) ∧
    (ValidDesign P → ∀ E : Finset (Fin n) → Prop,
      probability P (fun S => ¬ E S) = 1 - probability P E) ∧
    (∀ (f : Finset (Fin n) → ℝ) (c : ℝ), 0 < c → (∀ S ∈ assignments P, 0 ≤ f S) →
      probability P (fun S => c ≤ f S) ≤ expectation P f / c)

/-! ## Nodes -/

/-- Node 1 (population Gram invertibility). -/
def N1 : Prop := GramInvertible
/-- Residual centring from the intercept normal equation, followed by moment collapse. -/
def N2 : Prop := GramInvertible → ResidualsVanish
/-- Population Gram invertibility implies acceptance on the full-rank event. -/
def N3 : Prop := GramInvertible → FullRankAcceptance
/-- Exact finite-sampling mean-squared error. -/
def N4 : Prop := SamplingMSE
/-- Node 5 (one-covariate arm Gram determinant). -/
def N5 : Prop := ArmGramDet
/-- Single-arm Chebyshev bound. -/
def N6 : Prop := SamplingMSE → ArmGramDet → ProbabilityCalculus → SingleArmFailure
/-- Node 7 (two-arm union bound and the constant `1548`, including small `n`). -/
def N7 : Prop := ProbabilityCalculus → SingleArmFailure → ClassFailure
/-- Node 8 (coverage lower bound: acceptance contains the full-rank event). -/
def N8 : Prop :=
  ProbabilityCalculus → ResidualsVanish → FullRankAcceptance → ClassFailure →
    CoverageLowerBound
/-- Membership of the centred grid model in the fixed class. -/
def N9 : Prop := GridInClass
/-- Squeeze the nested infimum to one. -/
def N10 : Prop :=
  ProbabilityCalculus → CoverageLowerBound → GridInClass → InfimumLimitOne
/-- Node 11 (finite design-probability calculus). -/
def N11 : Prop := ProbabilityCalculus

/-- The nodes suffice. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7)
    (h8 : N8) (h9 : N9) (h10 : N10) (h11 : N11) : Target := by
  intro h
  have hlim : InfimumLimitOne :=
    h10 h11 (h8 h11 (h2 h1) (h3 h1) (h7 h11 (h6 h4 h5 h11))) h9
  have hprinted := h 1 0 (1/4) 4 (1/2) (1/4) (1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by constructor <;> norm_num)
    (by constructor <;> norm_num)
  have heq := tendsto_nhds_unique (hlim (1/2)) hprinted
  have hlt : ENNReal.ofReal (1 - 1/2) < 1 := ENNReal.ofReal_lt_one.mpr (by norm_num)
  exact (ne_of_lt hlt) heq.symm

end
end AronowAudit.P002.Wave1.PrintedTheorem2
