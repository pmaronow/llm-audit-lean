import AronowAudit.P011.P011_Audit

/-!
# P011-T31: refutation of printed Proposition 1 (path witness)

Printed Proposition 1 asserts `InProbability F (scaledOracle F) (scaledTrue F)` for every `Family` satisfying
`Scaling F c1 c2 c3 c4` (Assumption 2). `Target` is its exact negation.

The witness for P011-T31 is `pathFamily 2`. Index `k`
has `K = k+1` independent blocks `(2+U, -4+3U/5+4V/5, 2+V)` with fair signs `U,V`, `θ = 1`,
true and recruitment graph the disjoint union of paths `1–2–3`, caps `(1,2,1)`. It satisfies
`Scaling (pathFamily 2) 6 2 (29/15) 2`, has `n Var(β̂) = 29/15` exactly, while
`n V̂₁ → -11/15` in probability, so the printed limit fails (at `ε = 1`).

The path statements N1–N11 also support P011-T32, P011-T33 and P011-T35.
The lemmas `scaledTrue_eq`, `scaling_of` and `limit_of` give the scaled variance,
scaling conditions and probability limit.
`PathFiniteCompletion.path_dependency` applies only to the one-block `t = 0` case.
-/

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PropositionOne

open AronowAudit.P011 MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

/-! ## Witness objects -/

/-- The admissible path family `t = 2` (`AronowAudit.P011.pathFamily`). -/
abbrev PF : Family := pathFamily 2

/-- The `K`-block path graph, i.e. `(pathModel 2 K).G`. -/
def pathGraphK (K : ℕ) : Graph (3 * K) := blockGraph (by decide) pathGraph K

/-- `Q̄ = K⁻¹ yᵀ(I+A)y`, the block average of `Q_b = Y_bᵀ B Y_b`. -/
def pathQbar (K : ℕ) (y : Fin (3 * K) → ℝ) : ℝ :=
  quadratic (oracleMatrix (pathGraphK K)) y / K

/-- `L̄ = K⁻¹ 1ᵀ(I+A)y`, the block average of `L_b = 1ᵀ B Y_b`. -/
def pathLbar (K : ℕ) (y : Fin (3 * K) → ℝ) : ℝ :=
  (∑ i, ∑ j, oracleMatrix (pathGraphK K) i j * y j) / K

/-- Block `b` of a vector on `3K` units: coordinates `3b, 3b+1, 3b+2`. -/
def blockVec (K : ℕ) (y : Fin (3 * K) → ℝ) (b : Fin K) : Fin 3 → ℝ := fun r =>
  y ⟨3 * b.val + r.val, by have := b.isLt; have := r.isLt; omega⟩

/-- The source map of `pathModel 2 K`: fair sign coordinates `u b 0 = U_b`, `u b 1 = V_b`. -/
def pathSource (K : ℕ) (u : Fin K → Fin 2 → Bool) : Fin (3 * K) → ℝ := fun i =>
  pathBlock 2 (sign (u (blockIndex (by decide) i) 0)) (sign (u (blockIndex (by decide) i) 1))
    (localIndex (by decide) i)

/-! ## Target -/

/-- **Target (P011-T31).** Negation of printed Proposition 1 (p. 2242). -/
def Target : Prop :=
  ¬ ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
      InProbability F (scaledOracle F) (scaledTrue F)

/-- Explicit path witness to the failure of printed Proposition 1 (P011-T31). -/
def Witness : Prop :=
  Scaling PF 6 2 (29 / 15) 2 ∧ ¬ InProbability PF (scaledOracle PF) (scaledTrue PF)

/-! ## Witness properties -/

/-- Under the uniform law on `Fin K → Fin 2 → Bool`, functions depending
only on disjoint sets of source coordinates are independent. -/
def N1 : Prop :=
  ∀ (K : ℕ) {β γ : Type} [MeasurableSpace β] [MeasurableSpace γ]
    (A B : Finset (Fin K × Fin 2)), Disjoint A B →
    ∀ (f : (Fin K → Fin 2 → Bool) → β) (g : (Fin K → Fin 2 → Bool) → γ),
      (∀ u v, (∀ p ∈ A, u p.1 p.2 = v p.1 p.2) → f u = f v) →
      (∀ u v, (∀ p ∈ B, u p.1 p.2 = v p.1 p.2) → g u = g v) →
      IndepFun f g (PMF.uniformOfFintype (Fin K → Fin 2 → Bool)).toMeasure

/-- Block decompositions of the outcome sum, the oracle quadratic form and
the oracle row-sum functional, together with the block form of `pathSource`. -/
def N2 : Prop :=
  ∀ K : ℕ, (∀ y : Fin (3 * K) → ℝ,
      (∑ i, y i = ∑ b, ∑ r, blockVec K y b r) ∧
      quadratic (oracleMatrix (pathGraphK K)) y =
        ∑ b, quadratic (oracleMatrix pathGraph) (blockVec K y b) ∧
      (∑ i, ∑ j, oracleMatrix (pathGraphK K) i j * y j) =
        ∑ b, ∑ r, ∑ s, oracleMatrix pathGraph r s * blockVec K y b s) ∧
    ∀ (u : Fin K → Fin 2 → Bool) (b : Fin K),
      blockVec K (pathSource K u) b = pathBlock 2 (sign (u b 0)) (sign (u b 1))

/-- The source-coordinate independence property `N1` implies the full
dependency-graph condition for `pathModel 2 K` at every block count. -/
def N3 : Prop := N1 → ∀ K : ℕ, Dependency (pathModel 2 K)

/-- The path family is nested as the number of blocks increases. -/
def N4 : Prop := Nested PF

/-- At every index, `β = 0` and all weighted outcomes have absolute value
at most `6` almost surely. -/
def N5 : Prop :=
  ∀ k : ℕ, beta (PF.model k) = 0 ∧
    ∀ᵐ y ∂(PF.model k).law, ∀ i, |weighted (PF.model k) y i - beta (PF.model k)| ≤ 6

/-- Every vertex in the path family has degree at most `2`. -/
def N6 : Prop := ∀ (k : ℕ) (i : Fin (PF.size k)), (degree (PF.model k).G i : ℝ) ≤ 2

/-- The block decomposition property `N2` implies the exact second moments
`E[β̂²] = 29/(45K)` and `E[(Q̄+11/5)²] = 28836/(625K)`, where `K = k+1`. -/
def N7 : Prop :=
  N2 → ∀ k : ℕ,
    expectation (PF.model k) (fun y => betaHat (PF.model k) y ^ 2) = 29 / (45 * ((k : ℝ) + 1)) ∧
    expectation (PF.model k) (fun y => (pathQbar (k + 1) y + 11 / 5) ^ 2) =
      28836 / (625 * ((k : ℝ) + 1))

/-- Under `N2`, the centered oracle estimator satisfies
`n V̂₁ = (Q̄ − 2H L̄ + 7H²)/3` for every real outcome vector,
where `H` is its average and `n = 3K > 0`. -/
def N8 : Prop :=
  N2 → ∀ K : ℕ, 0 < K → ∀ y : Fin (3 * K) → ℝ,
    ((3 * K : ℕ) : ℝ) * V1 (pathGraphK K) y =
      (pathQbar K y - 2 * average y * pathLbar K y + 7 * average y ^ 2) / 3

/-- Under `N2`, `|L̄| ≤ 61/5` almost surely under each path-family law. -/
def N9 : Prop := N2 → ∀ k : ℕ, ∀ᵐ y ∂(PF.model k).law, |pathLbar (k + 1) y| ≤ 61 / 5

/-- The block decomposition, centering, moment and almost-sure bound
properties `N2`, `N5`, `N7`, `N8` and `N9` imply that the scaled oracle
estimator converges in probability to `−11/15`. -/
def N10 : Prop :=
  N2 → N5 → N7 → N8 → N9 → InProbability PF (scaledOracle PF) (fun _ => -11 / 15)

/-- A statistic converging in probability to a constant cannot also
converge in probability to another constant more than `2` away. -/
def N11 : Prop :=
  ∀ (F : Family) (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (a b : ℝ), 2 < |a - b| →
    InProbability F T (fun _ => a) → ¬ InProbability F T (fun _ => b)

/-! ## Scaled variance, scaling conditions and probability limit -/

/-- `n Var(β̂) = 29/15` at every index, from `β = 0` (N5) and `E β̂² = 29/(45K)` (N7). -/
theorem scaledTrue_eq (h2 : N2) (h5 : N5) (h7 : N7) (k : ℕ) : scaledTrue PF k = 29 / 15 := by
  have hb : expectation (PF.model k) (betaHat (PF.model k)) = 0 := (h5 k).1
  unfold scaledTrue var
  rw [hb]
  simp only [sub_zero]
  rw [(h7 h2 k).1]
  show ((3 * (k + 1) : ℕ) : ℝ) * (29 / (45 * ((k : ℝ) + 1))) = 29 / 15
  have : (k : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- All of `Scaling (pathFamily 2) 6 2 (29/15) 2` (Assumption 2) from the stated witness properties. -/
theorem scaling_of (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7) :
    Scaling PF 6 2 (29 / 15) 2 :=
  ⟨h4, by norm_num, by norm_num, by norm_num, by norm_num, fun k => h3 h1 (k + 1),
    fun k => (h5 k).2, h6,
    tendsto_const_nhds.congr (fun k => (scaledTrue_eq h2 h5 h7 k).symm),
    fun k i => by show |(1 : ℝ)| < 2; norm_num⟩

/-- The probability limit `n V̂₁ → -11/15`. -/
theorem limit_of (h2 : N2) (h5 : N5) (h7 : N7) (h8 : N8) (h9 : N9) (h10 : N10) :
    InProbability PF (scaledOracle PF) (fun _ => -11 / 15) :=
  h10 h2 h5 h7 h8 h9

/-! ## Refutation from the witness -/

/-- The stated properties imply the explicit path witness. -/
theorem assemble_witness (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6)
    (h7 : N7) (h8 : N8) (h9 : N9) (h10 : N10) (h11 : N11) : Witness := by
  refine ⟨scaling_of h1 h2 h3 h4 h5 h6 h7, ?_⟩
  rw [show scaledTrue PF = fun _ => 29 / 15 from funext (scaledTrue_eq h2 h5 h7)]
  exact h11 PF _ (-11 / 15) (29 / 15) (by norm_num [abs_of_neg])
    (limit_of h2 h5 h7 h8 h9 h10)

/-- The stated witness properties imply the refutation of printed Proposition 1. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7)
    (h8 : N8) (h9 : N9) (h10 : N10) (h11 : N11) : Target := by
  intro hall
  have W := assemble_witness h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  exact W.2 (hall PF 6 2 (29 / 15) 2 W.1)

end

end AronowAudit.P011.Wave1.PropositionOne
