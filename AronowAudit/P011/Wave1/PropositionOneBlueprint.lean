import AronowAudit.P011.P011_Audit

/-!
# Blueprint: P011-T31, refutation of printed Proposition 1 (shared path witness)

Wave 1, group P011-P013. The frozen record `AronowAudit.P011.printed_proposition_one`
asserts `InProbability F (scaledOracle F) (scaledTrue F)` for every `Family` satisfying
`Scaling F c1 c2 c3 c4` (Assumption 2). `Target` is its exact negation.

Witness (mapper P011-T31, accepted by both referees): the existing `pathFamily 2`. Index `k`
has `K = k+1` independent blocks `(2+U, -4+3U/5+4V/5, 2+V)` with fair signs `U,V`, `θ = 1`,
true and recruitment graph the disjoint union of paths `1–2–3`, caps `(1,2,1)`. It satisfies
`Scaling (pathFamily 2) 6 2 (29/15) 2`, has `n Var(β̂) = 29/15` exactly, while
`n V̂₁ → -11/15` in probability, so the printed limit fails (at `ε = 1`).

This module owns the path nodes N1–N11 shared with P011-T32 (`CorollaryOneBlueprint`),
P011-T33 (`CorollaryThreeBlueprint`) and P011-T35 (`PackageOLSBlueprint`), and the proved
glue lemmas `scaledTrue_eq`, `scaling_of`, `limit_of`.

Writers: prove `theorem nk_proof : Nk` in `AronowAudit/P011/Wave1/PropositionOne/Nk.lean`.
Do not use the drafts `path_counterexample`, `cycle_counterexample` or the printed
contracts (they are unproved drafts); `PathFiniteCompletion.path_dependency` is only the
one-block `t = 0` case.
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

/-! ## Frozen target -/

/-- **Target (P011-T31).** Exact negation of `printed_proposition_one`
(Proposition 1, p. 2242). -/
def Target : Prop :=
  ¬ ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
      InProbability F (scaledOracle F) (scaledTrue F)

/-- The mapper's explicit witness statement (`printed_proposition_one_refuted` in the map). -/
def Witness : Prop :=
  Scaling PF 6 2 (29 / 15) 2 ∧ ¬ InProbability PF (scaledOracle PF) (scaledTrue PF)

/-! ## Nodes -/

/-- **Node N1** (paper proof T31, "Independent product signs therefore imply independence of
the entire two outcome vectors"; generic): under the uniform law on the sign array
`Fin K → Fin 2 → Bool`, functions depending only on disjoint coordinate sets are
independent. Use `uniform_function_product` (twice, or via `Equiv.curry`), `iIndepFun_pi`,
`iIndepFun.indepFun_finset`, `IndepFun.comp`; every map on this finite discrete space is
measurable. -/
def N1 : Prop :=
  ∀ (K : ℕ) {β γ : Type} [MeasurableSpace β] [MeasurableSpace γ]
    (A B : Finset (Fin K × Fin 2)), Disjoint A B →
    ∀ (f : (Fin K → Fin 2 → Bool) → β) (g : (Fin K → Fin 2 → Bool) → γ),
      (∀ u v, (∀ p ∈ A, u p.1 p.2 = v p.1 p.2) → f u = f v) →
      (∀ u v, (∀ p ∈ B, u p.1 p.2 = v p.1 p.2) → g u = g v) →
      IndepFun f g (PMF.uniformOfFintype (Fin K → Fin 2 → Bool)).toMeasure

/-- **Node N2** (paper proof T31, "For one block write B=I+A_path, S=1'Y, L=1'BY, Q=Y'BY";
block bookkeeping): deterministic block decompositions of `Σy`, `yᵀ(I+A)y` and
`1ᵀ(I+A)y` for the `K`-block path graph, and the block form of the source map. Use
`StarCompletion.blockEquiv`, `block_local`, `block_quot`, `BlockOLSCompletion.local_sum`. -/
def N2 : Prop :=
  ∀ K : ℕ, (∀ y : Fin (3 * K) → ℝ,
      (∑ i, y i = ∑ b, ∑ r, blockVec K y b r) ∧
      quadratic (oracleMatrix (pathGraphK K)) y =
        ∑ b, quadratic (oracleMatrix pathGraph) (blockVec K y b) ∧
      (∑ i, ∑ j, oracleMatrix (pathGraphK K) i j * y j) =
        ∑ b, ∑ r, ∑ s, oracleMatrix pathGraph r s * blockVec K y b s) ∧
    ∀ (u : Fin K → Fin 2 → Bool) (b : Fin K),
      blockVec K (pathSource K u) b = pathBlock 2 (sign (u b 0)) (sign (u b 1))

/-- **Node N3** (paper proof T31, "If two disjoint vertex sets have no connecting path edge,
their source-sign sets are disjoint ... This verifies Dependency"): full vector dependency
for every block count. From N1: the outcome tuples on `S` and `T` are functions of the
disjoint source-coordinate sets (`{(b,0)}` for local 0, `{(b,0),(b,1)}` for local 1,
`{(b,1)}` for local 2; a shared coordinate would force an edge); then push forward along
`pathSource` (`PMF.toMeasure_map`; generalize `PathFiniteCompletion.indep_pushforward` to
tuple-valued maps). -/
def N3 : Prop := N1 → ∀ K : ℕ, Dependency (pathModel 2 K)

/-- **Node N4** (paper proof T31, "Appending a block embeds each previous induced graph as
its first 3K vertices, so Nested holds"): use `Fin.castLE`. -/
def N4 : Prop := Nested PF

/-- **Node N5** (paper proof T31, "The unit means are (2,-4,2) and sum to zero on each block,
so beta=0. Outcomes have absolute value at most 27/5<6"): `β = 0` and the almost-sure
outcome bound with `c₁ = 6`. Use `BlockOLSCompletion.path_coordinate_mean`, `local_sum`;
the a.e. bound from the finite support (`PMF.toMeasure_apply_eq_zero_iff`, `PMF.support_map`
or `ae_map_iff`). -/
def N5 : Prop :=
  ∀ k : ℕ, beta (PF.model k) = 0 ∧
    ∀ᵐ y ∂(PF.model k).law, ∀ i, |weighted (PF.model k) y i - beta (PF.model k)| ≤ 6

/-- **Node N6** (paper proof T31, "Degrees are at most 2"): use `StarCompletion.block_degree`
and the degrees `(1,2,1)` of `pathGraph`. -/
def N6 : Prop := ∀ (k : ℕ) (i : Fin (PF.size k)), (degree (PF.model k).G i : ℝ) ≤ 2

/-- **Node N7** (paper proof T31, "E S=0, E S^2=29/5, E Q=-11/5, Var Q=28836/625 ... Distinct
blocks are independent"; "E H^2=29/(45K)", "E[(Qbar+11/5)^2]=28836/(625K)"): the two exact
second moments. Use N2 to write `β̂` and `Q̄` as block sums of `pathSource`, then
`uniform_integral`, the per-block values of `path_block_moments` at `t = 2`, and
factorization of products of distinct-block functions under the uniform product law
(`uniform_function_product`, `Finset.prod_univ_sum`). -/
def N7 : Prop :=
  N2 → ∀ k : ℕ,
    expectation (PF.model k) (fun y => betaHat (PF.model k) y ^ 2) = 29 / (45 * ((k : ℝ) + 1)) ∧
    expectation (PF.model k) (fun y => (pathQbar (k + 1) y + 11 / 5) ^ 2) =
      28836 / (625 * ((k : ℝ) + 1))

/-- **Node N8** (paper proof T31, "Exact centering of the actual estimator, at the single
sample mean H, gives T=n V1=(Qbar-2H Lbar+7H^2)/3, because 1'B1=7 on one path"): a
deterministic identity for every real vector `y` (symmetry of `I+A`; `1ᵀ(I+A)1 = 7K` from
N2 with `y = 1` and the last conjunct of `path_block_moments`). -/
def N8 : Prop :=
  N2 → ∀ K : ℕ, 0 < K → ∀ y : Fin (3 * K) → ℝ,
    ((3 * K : ℕ) : ℝ) * V1 (pathGraphK K) y =
      (pathQbar K y - 2 * average y * pathLbar K y + 7 * average y ^ 2) / 3

/-- **Node N9** (paper proof T31, "|L|<=61/5"; "Since |Lbar|<=61/5 pointwise"): almost surely
under the law (the bound holds on the finite sign support, not for arbitrary real `y`). Use
N2 (block form of `L̄` and of `pathSource`) and the support argument of N5. -/
def N9 : Prop := N2 → ∀ k : ℕ, ∀ᵐ y ∂(PF.model k).law, |pathLbar (k + 1) y| ≤ 61 / 5

/-- **Node N10** (paper proof T31, "Markov gives P(|H|>a)<=29/(45K a^2) ... The event
|T+11/15|>eta is contained in {|Qbar+11/5|>a} union {|H|>a}"): the scaled oracle tends in
probability to `-11/15`. From N5, N7, N8, N9 (the last three applied to N2): Markov
(`mul_meas_ge_le_integral_of_nonneg`) on `H²` and `(Q̄+11/5)²`, the deterministic bound
`|T+11/15| ≤ |Q̄+11/5|/3 + (122/15)|H| + (7/3)H²` on the a.s. event `|L̄| ≤ 61/5`,
`a = min(1/2, 5η/108)`, `measureReal_union_le`, `squeeze_zero`. Note `weighted y = y`
(`θ = 1`). -/
def N10 : Prop :=
  N2 → N5 → N7 → N8 → N9 → InProbability PF (scaledOracle PF) (fun _ => -11 / 15)

/-- **Node N11** (paper proof T31, "For the actual Proposition 1 conclusion choose epsilon=1";
uniqueness of probability limits): a statistic cannot converge in probability to two
constants more than `2` apart (the `ε = 1` events cover the space; `measureReal_union_le`,
total mass one from `Model.probability`). Generic. -/
def N11 : Prop :=
  ∀ (F : Family) (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (a b : ℝ), 2 < |a - b| →
    InProbability F T (fun _ => a) → ¬ InProbability F T (fun _ => b)

/-! ## Glue (proved here; reused by T32, T33, T35) -/

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

/-- All of `Scaling (pathFamily 2) 6 2 (29/15) 2` (Assumption 2) from the nodes. -/
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

/-! ## Assembly (fully proved) -/

/-- **Assembly of the explicit witness.** -/
theorem assemble_witness (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6)
    (h7 : N7) (h8 : N8) (h9 : N9) (h10 : N10) (h11 : N11) : Witness := by
  refine ⟨scaling_of h1 h2 h3 h4 h5 h6 h7, ?_⟩
  rw [show scaledTrue PF = fun _ => 29 / 15 from funext (scaledTrue_eq h2 h5 h7)]
  exact h11 PF _ (-11 / 15) (29 / 15) (by norm_num [abs_of_neg])
    (limit_of h2 h5 h7 h8 h9 h10)

/-- **Assembly.** The nodes suffice for the refutation. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7)
    (h8 : N8) (h9 : N9) (h10 : N10) (h11 : N11) : Target := by
  intro hall
  have W := assemble_witness h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  exact W.2 (hall PF 6 2 (29 / 15) 2 W.1)

/-- Sanity checks: the witness model at index `k` has `K = k+1` blocks, `θ = 1`, its true
graph is `pathGraphK (k+1)` and its law is the uniform pushforward of `pathSource`. -/
example (k : ℕ) : PF.size k = 3 * (k + 1) := rfl
example (k : ℕ) : (PF.model k).G = pathGraphK (k + 1) := rfl
example (k : ℕ) (i : Fin (PF.size k)) : (PF.model k).theta i = 1 := rfl
example (K : ℕ) : (pathModel 2 K).law = uniformLaw (pathSource K) := rfl

/-- Fidelity check: `Target` is literally the negation of the frozen statement
`AronowAudit.P011.printed_proposition_one` (only its type is read; its unproved draft proof is never used). -/
example : Target = ¬ type_of% @AronowAudit.P011.printed_proposition_one := rfl

end

end AronowAudit.P011.Wave1.PropositionOne
