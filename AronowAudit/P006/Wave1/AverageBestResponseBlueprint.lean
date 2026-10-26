import AronowAudit.P006.Wave1.BinaryExperimentBlueprint

/-!
# P006-T26: counterexample to the printed average-reward best-response claim

Propositions 6–7 as printed (PDF pp. 15–16) assert that the arg-max-only
rules are best responses for the unconditional ATO and ATT rewards.
`Target` is the negation of this claim for sample and covariate types in
universe 0; a universe-polymorphic claim would imply this instance.

The witness is the two-unit experiment `E26`: fair covariates, Bernoulli
treatment, `Y0 = 0`, `Y1 = effectE001 X` and `μhat = 0`. Its actual ATO and
ATT rewards equal `rewardE001 = (9u+10v)(4-u-v)/40`. The printed rule `(0,1)`
earns `3/4`, while treat-all earns `19/20`, as in `T1_average_counterexample`.
`Witness` states this counterexample explicitly and implies `Target`.
-/

set_option autoImplicit false

namespace AronowAudit.P006.Wave1.AverageBestResponse

open AronowAudit.P006 AronowAudit.P006.Wave1.BinaryExperiment MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/-!
## Target
-/

/-- **Target (P006-T26).** The negation of Propositions 6–7 as printed,
for sample and covariate types in universe 0. -/
def Target : Prop :=
  ¬ ∀ {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] [Countable C]
      [MeasurableSingletonClass C] {n : ℕ} (E : Experiment Ω C n),
      Standing E → PointwiseUnbiased E {π | Admissible π} →
      IsBest {π | Admissible π} E.expectedATO (printedAverageRule E.μ1) ∧
      IsBest {π | Admissible π} E.expectedATT (printedAverageRule E.τ)

/-- The two-unit witness experiment. -/
def E26 : Experiment (Fin 2 → Bool × Bool) Bool 2 :=
  binExp 2 (by norm_num) effectE001 (fun _ _ _ => 0)

/-- The explicit counterexample, implying `Target`. -/
def Witness : Prop :=
  ∃ E : Experiment (Fin 2 → Bool × Bool) Bool 2,
    Standing E ∧ PointwiseUnbiased E {π | Admissible π} ∧
    ¬ (IsBest {π | Admissible π} E.expectedATO (printedAverageRule E.μ1) ∧
       IsBest {π | Admissible π} E.expectedATT (printedAverageRule E.τ))

/-! ## Reward identity -/

/-- **Statement S1.** Expanding the integral under νπ⊗νπ over x0,x1,t0,t1
gives twoATO(1/2,effectE001,p)=rewardE001(p). Since μhat=0, the actual ATT
reward equals ATO pointwise. Thus both expected rewards of the witness equal
the finite sum. The calculation uses `BinaryExperiment.S2`,
`realized_rewards_SUTVA` and `wATT_zero`, reindexing `Fin 2 → Bool × Bool`
as two pairs and expanding `twoATO`, with coinMass(1/2,x)=1/2 and
binaryRule(π false,π true)=π. -/
def S1 : Prop :=
  ∀ π : Bool → ℝ, Admissible π →
    E26.expectedATO π = rewardE001 (π false, π true) ∧
    E26.expectedATT π = rewardE001 (π false, π true)

def N1 : Prop := BinaryExperiment.S1 → BinaryExperiment.S2 → S1

/-! ## Assembly -/

/-- Every rule on `Bool` with values in `{0,1}` is admissible. -/
theorem admissible_of_zero_one (π : Bool → ℝ) (h : ∀ x, π x = 0 ∨ π x = 1) : Admissible π := by
  refine ⟨measurable_of_countable π, fun x => ?_⟩
  rcases h x with h | h <;> rw [h] <;> norm_num

/-- **Witness assembly.** -/
theorem assemble_witness (b1 : BinaryExperiment.N1) (b2 : BinaryExperiment.N2)
    (b3 : BinaryExperiment.N3) (b4 : BinaryExperiment.N4) (b5 : BinaryExperiment.N5)
    (h1 : N1) : Witness := by
  have hval : S1 := h1 b1 (b2 b1)
  refine ⟨E26, standing_of b1 b3 b4 b5 2 (by norm_num) effectE001 (fun _ _ _ => 0), ?_, ?_⟩
  · intro π _ x
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp [E26, binExp]
  · rintro ⟨hATO, -⟩
    have hone : Admissible (fun _ : Bool => (1 : ℝ)) :=
      admissible_of_zero_one _ (fun _ => Or.inr rfl)
    have hpr : ∀ x, printedAverageRule effectE001 x = binaryRule (0, 1) x :=
      T1_average_counterexample.1
    have hadm : Admissible (printedAverageRule effectE001) := by
      refine admissible_of_zero_one _ (fun x => ?_)
      rw [hpr x]
      cases x <;> simp [binaryRule]
    have h := hATO.2 _ hone
    change E26.expectedATO (fun _ => 1) ≤ E26.expectedATO (printedAverageRule effectE001) at h
    rw [(hval _ hone).1, (hval _ hadm).1, hpr false, hpr true] at h
    have hlt := T1_average_counterexample.2.2.2.1
    simp only [binaryRule] at h hlt
    norm_num at h hlt
    linarith

/-- **Assembly.** The stated implications suffice for the refutation. -/
theorem assemble (b1 : BinaryExperiment.N1) (b2 : BinaryExperiment.N2)
    (b3 : BinaryExperiment.N3) (b4 : BinaryExperiment.N4) (b5 : BinaryExperiment.N5)
    (h1 : N1) : Target := by
  intro hall
  obtain ⟨E, hS, hU, hneg⟩ := assemble_witness b1 b2 b3 b4 b5 h1
  exact hneg (hall E hS hU)

end

end AronowAudit.P006.Wave1.AverageBestResponse
