import AronowAudit.P027.P027_Audit

/-! # Blueprint: refutation of `AronowAudit.P027.aggregation_rationale_reading` (P027-T8)

Dossier group P027, record 13. The frozen contract (source
`AronowAudit/P027/P027_Audit.lean`, `aggregation_rationale_reading`, a `sorry` draft) is
the expressly labelled universal count-of-pairs rationale reading of main p. 237:
for every positive group design, nonempty fibres, outcomes and independently chosen
admissible (Hölder-conjugate) original and grouped exponent arrays, totalling
co-selected units does not increase the actual conservative-estimator bias.
Resolution `refute` (map-P027, accepted by both referees without fixes).

Paper proof (map-P027 report, record 13): `G = Ω = Fin 2`, `D = cluster2`,
`n = (2,1)`, all original outcomes `1`, every exponent `2`. Then
`E[C2] = Var + A + A*` (Propositions 1–2 at exponent 2), with `A_u = A*_u = 4` for
the original units and `A_c = 4`, `A*_c = 5` for the totals `(2,1)`; the biases are
`8` and `9`, so the recorded inequality becomes `9 ≤ 8`.

The frozen target is the negation of the exact recorded contract. The final
declaration (writer) is `AronowAudit.P027.Wave1.aggregation_rationale_counterexample`
in `AronowAudit/P027/Wave1/AggregationRationale.lean`. This refutes only the labelled
universal reading, not the hedged printed tendency (registry P027-N002).
-/

namespace AronowAudit.P027.Wave1.AggregationRationale

set_option autoImplicit false
noncomputable section
open AronowAudit.P027
attribute [local instance] Classical.propDecidable

/-- Frozen target: the negation of the exact recorded contract of
`AronowAudit.P027.aggregation_rationale_reading`, including the section variables
`{Ω : Type} [Fintype Ω]` that the source theorem binds first. -/
def Target : Prop :=
  ¬ (∀ {Ω : Type} [Fintype Ω] {G : Type} [Fintype G] (D : Design G Ω), Positive D →
      ∀ (n : G → ℕ), (∀ g, 0 < n g) →
      ∀ (y : (Σ g, Fin (n g)) → ℝ)
        (a b : (Σ g, Fin (n g)) → (Σ g, Fin (n g)) → ℝ) (ac bc : G → G → ℝ),
      (∀ k l, k ≠ l ∧ joint (liftDesign D n) k l = 0 → (a k l).HolderConjugate (b k l)) →
      (∀ g h, g ≠ h ∧ joint D g h = 0 → (ac g h).HolderConjugate (bc g h)) →
      expect D (conservativeEstimator D (groupTotal n y) ac bc) -
          variance D (htTotal D (groupTotal n y)) ≤
        expect (liftDesign D n) (conservativeEstimator (liftDesign D n) y a b) -
          variance (liftDesign D n) (htTotal (liftDesign D n) y))

/-- Fidelity check: `Target` is literally the negation of the frozen contract. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P027.aggregation_rationale_reading) := Iff.rfl

/-- Witness fibre sizes `n = (2,1)`. -/
def nW : Fin 2 → ℕ := fun g => if g = 0 then 2 else 1

/-- Witness original outcomes, all equal to one. -/
def yW : (Σ g : Fin 2, Fin (nW g)) → ℝ := fun _ => 1

/-- N1 (paper-proof step "the original zero-pair set consists of the four ordered
cross-group member pairs; each contributes 1 to A and (1²+1²)/2 = 1 to quadratic
A*"): for the lifted three-unit design, `A_u = 4` and `A*_u = 4`. -/
def N1 : Prop :=
  biasA (liftDesign cluster2 nW) yW = 4 ∧ quadraticA (liftDesign cluster2 nW) yW = 4

/-- N2 (paper-proof step "at group level the two ordered zero pairs each contribute
2·1 = 2 to A and (2²+1²)/2 = 5/2 to A*"): for the totals `(2,1)` under `cluster2`,
`A_c = 4` and `A*_c = 5`. -/
def N2 : Prop :=
  biasA cluster2 (groupTotal nW yW) = 4 ∧ quadraticA cluster2 (groupTotal nW yW) = 5

/-- The nodes suffice. Instantiate the contract at the witness with all exponents
`2` (`Real.HolderConjugate.two_two`), identify the exponent-2 conservative estimator
with `c2Estimator` (`c2_is_young_two`), expand both expectations with the proved
`c2_expectation` (`Var + A + A*`), and substitute N1 and N2: `9 ≤ 8`. -/
theorem assemble (h1 : N1) (h2 : N2) : Target := by
  intro hcon
  have hpos : Positive cluster2 := aggregation_counterexample_positive.2.1
  have hn : ∀ g, 0 < nW g := by
    intro g; unfold nW; split <;> norm_num
  have h := hcon cluster2 hpos nW hn yW (fun _ _ => 2) (fun _ _ => 2) (fun _ _ => 2)
    (fun _ _ => 2) (fun _ _ _ => Real.HolderConjugate.two_two)
    (fun _ _ _ => Real.HolderConjugate.two_two)
  rw [← c2_is_young_two, ← c2_is_young_two, c2_expectation _ hpos,
    c2_expectation _ (lift_positive _ hpos _)] at h
  obtain ⟨hA1, hQ1⟩ := h1
  obtain ⟨hA2, hQ2⟩ := h2
  rw [hA1, hQ1, hA2, hQ2] at h
  linarith

end
end AronowAudit.P027.Wave1.AggregationRationale
