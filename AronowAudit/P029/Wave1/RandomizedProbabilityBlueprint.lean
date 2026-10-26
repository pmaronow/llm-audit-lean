import AronowAudit.P029.P029_Audit

/-!
# P029-T25: independent Bernoulli assignment on a probability space

Paper: P029 p. 495 (PDF p. 4), fifth IV assumption: Z randomly assigned, independent of all
fixed potential outcomes, with `0 < P(Z=1) < 1`. The finite signed-weight identity
`randomized_independent` is valid for every real `e`, so it does not by itself certify a
probability experiment. The product law `ν × Bernoulli(e)` for `0 < e < 1` on an arbitrary
measurable unit space has total mass one, independent assignment, and the stated arm
probabilities.
-/

namespace AronowAudit.P029.Wave1.RandomizedProbability

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

universe u v

noncomputable section

/-- Probability, independence, and arm probabilities under Bernoulli assignment. -/
def Target : Prop :=
  ∀ {Ω : Type u} {A : Type v} [MeasurableSpace Ω] [MeasurableSpace A]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (e : ℝ), 0 < e → e < 1 →
    ∀ (v : Ω → A), Measurable v →
      IsProbabilityMeasure (ν.prod (bernoulliMeasure e)) ∧
      IndepFun (fun i : Ω × Bool => v i.1) Prod.snd (ν.prod (bernoulliMeasure e)) ∧
      mP (ν.prod (bernoulliMeasure e)) {i | i.2 = true} = e ∧
      mP (ν.prod (bernoulliMeasure e)) {i | i.2 = false} = 1 - e

/-- For `0 < e < 1`, `bernoulliMeasure e` is a probability measure (`bernoulli_measure_probability`)
with point masses `ofReal e` at `true` and `ofReal (1 - e)` at `false`. -/
def N1 : Prop :=
  ∀ e : ℝ, 0 < e → e < 1 →
    IsProbabilityMeasure (bernoulliMeasure e) ∧
    bernoulliMeasure e {true} = ENNReal.ofReal e ∧
    bernoulliMeasure e {false} = ENNReal.ofReal (1 - e)

/-- For a probability measure `ν`, a probability measure `β` on `Bool`, and measurable `v`, the product law is a
probability measure, `v ∘ fst` is independent of `snd` (`indepFun_prod` with `id`, or the
rectangle formula `Measure.prod_prod`), and the arm masses are the point masses of `β`. -/
def N2 : Prop :=
  ∀ {Ω : Type u} {A : Type v} [MeasurableSpace Ω] [MeasurableSpace A]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (β : Measure Bool) [IsProbabilityMeasure β]
    (v : Ω → A), Measurable v →
      IsProbabilityMeasure (ν.prod β) ∧
      IndepFun (fun i : Ω × Bool => v i.1) Prod.snd (ν.prod β) ∧
      ∀ b : Bool, mP (ν.prod β) {i | i.2 = b} = (β {b}).toReal

/-- The intermediate propositions imply the conclusion. -/
theorem assemble (h1 : N1) (h2 : N2.{u, v}) : Target.{u, v} := by
  intro Ω A _ _ ν _ e he0 he1 v hv
  obtain ⟨hβ, ht, hf⟩ := h1 e he0 he1
  obtain ⟨hp, hind, harm⟩ := h2 ν (bernoulliMeasure e) v hv
  refine ⟨hp, hind, ?_, ?_⟩
  · rw [harm, ht, ENNReal.toReal_ofReal he0.le]
  · rw [harm, hf, ENNReal.toReal_ofReal (by linarith)]

end

end AronowAudit.P029.Wave1.RandomizedProbability
