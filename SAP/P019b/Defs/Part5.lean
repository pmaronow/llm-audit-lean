import SAP.P019b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019b

open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical

def T18Statement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (S : Study Ω), S.standing → ∀ c1 c0 : ℝ,
    Tendsto (fun n : ℕ => (n : ℝ) *
      (S.law.iid n).variance (fun s => S.muHat s c1 c0)) atTop (nhds S.sigmaSq)

def T19Statement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (S : Study Ω), S.standing → ∀ c1 c0 cV : ℝ,
    0 < S.sigmaSq ∧
    RootNTight S c1 c0 ∧
    WeakLimit S.law (fun n s => Real.sqrt n * (S.muHat s c1 c0-S.mu))
      (gaussianReal 0 S.sigmaSq.toNNReal) ∧
    ProbabilityLimit S.law (fun n s => (n : ℝ)*S.muVarianceHat s c1 c0 cV) S.sigmaSq ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      Tendsto (fun n : ℕ => (S.law.iid n).prob (fun s =>
        |S.muHat s c1 c0-S.mu| ≤ normalQuantile (1-α/2) *
          Real.sqrt (S.muVarianceHat s c1 c0 cV))) atTop (nhds (1-α)))

def T20Statement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (S : Study Ω), S.standing → ∀ c1 c0 d1 d0 : ℝ,
    Tendsto (fun n : ℕ => (n : ℝ)*(S.law.iid n).variance
      (fun s => S.muHat s c1 c0)) atTop (nhds S.sigmaSq) ∧
    Tendsto (fun n : ℕ => (n : ℝ)*(S.law.iid n).variance
      (fun s => S.standardHat s d1 d0)) atTop (nhds S.standardSigmaSq) ∧
    S.sigmaSq < S.standardSigmaSq

def T21Statement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (S : Study Ω), S.standing → ∀ c1 c0 cV : ℝ,
    S.beta = 1 ∧
    WeakLimit S.law (fun _ s => (S.betaHat s c1 c0-1) /
      Real.sqrt (S.betaVarianceHat s cV)) (gaussianReal 0 1) ∧
    (∀ u : ℝ, 0 < u → u < 1 →
      Tendsto (fun n : ℕ => (S.law.iid n).prob (fun s =>
        normalPValue (S.betaHat s c1 c0) 1 (S.betaVarianceHat s cV) ≤ u))
          atTop (nhds u))

def T22Statement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (S : Study Ω),
    (S.treatmentIndependent →
      0 < S.law.prob (fun ω => S.Z ω = false) →
      0 < S.law.prob (fun ω => S.Z ω = true) → S.delta = 0) ∧
    (S.treatmentIndependent → S.nondegenerate → ∀ c1 c0 cV : ℝ,
      S.delta = 0 ∧
      WeakLimit S.law (fun _ s => S.deltaHat s c1 c0 /
        Real.sqrt (S.deltaVarianceHat s cV)) (gaussianReal 0 1) ∧
      (∀ u : ℝ, 0 < u → u < 1 →
        Tendsto (fun n : ℕ => (S.law.iid n).prob (fun s =>
          normalPValue (S.deltaHat s c1 c0) 0 (S.deltaVarianceHat s cV) ≤ u))
            atTop (nhds u)))

end
end SAP.P019b
