import AronowAudit.P029.Wave1.FiniteMeasureBlueprint

/-!
# P029-T20: an ordering counterexample with a conditional-unit kernel

Paper: P029 p. 499 (PDF p. 8), the ordering asserted at every profile in Supp(X), stated with
an actual covariate law `μX`, a Markov conditional-unit kernel `κ` and independent Bernoulli
assignment.
Witness: `μX = δ_()`, `κ = Kernel.const Unit ν` with `ν = atomicMeasure
typeMass` (types C, A, N with masses 1/2, 1/4, 1/4), `U = case1Unit`, `e = 1/2`. The population
law is the six-atom law with an inert `Unit` coordinate. At the unique support
profile `()`, typical ignorability holds but `∫ τ dκ() = 1/2 ≠ 1 = E(τ | C)`.
-/

namespace AronowAudit.P029.Wave1.IgnorabilityAllProfiles

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

/-- Negation of the printed implication from typical ignorability to latent
ignorability at every profile in the covariate support (universe-0 instance). -/
def Target : Prop :=
  ¬ (∀ {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
      [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X]
      (μX : Measure X) [IsProbabilityMeasure μX] (κ : Kernel X Ω) [IsMarkovKernel κ]
      (U : Ω → PotentialUnit X) (e : ℝ), 0 < e → e < 1 →
      (∀ x ∈ μX.support, ∀ᵐ ω ∂κ x, (U ω).x = x) →
      IVAssumptions (kernelPopulationLaw μX κ e) (kernelPopulationUnit U) Prod.snd →
      ∀ (x : X), x ∈ μX.support →
      Integrable (fun ω => (U ω).y0) (κ x) →
      Integrable (fun ω => (U ω).y1) (κ x) →
      0 < mP (κ x) {ω | (U ω).complier} →
      typicalAt ((κ x).prod (bernoulliMeasure e)) (liftUnit U) Prod.snd x →
      (∫ ω, (U ω).tau ∂κ x) = mCE (κ x) (fun ω => (U ω).tau) {ω | (U ω).complier})


/-- The three-type unit law `ν = ∑ᵢ ofReal(typeMass i) • δᵢ` (C, A, N = 1/2, 1/4, 1/4). -/
def nu : Measure (Fin 3) := atomicMeasure typeMass

/-- The covariate law `δ_()`. -/
def muX : Measure Unit := Measure.dirac ()

/-- The constant conditional-unit kernel `κ(x) = ν`. -/
def kappa : Kernel Unit (Fin 3) := Kernel.const Unit nu

/-- The counterexample with `κ () = ν`. -/
def Witness : Prop :=
  IsProbabilityMeasure muX ∧ IsMarkovKernel kappa ∧
  (∀ x ∈ muX.support, ∀ᵐ i ∂kappa x, (case1Unit i).x = x) ∧
  IVAssumptions (kernelPopulationLaw muX kappa (1 / 2)) (kernelPopulationUnit case1Unit) Prod.snd ∧
  () ∈ muX.support ∧
  Integrable (fun i => (case1Unit i).y0) (kappa ()) ∧
  Integrable (fun i => (case1Unit i).y1) (kappa ()) ∧
  0 < mP (kappa ()) {i | (case1Unit i).complier} ∧
  typicalAt ((kappa ()).prod (bernoulliMeasure (1 / 2))) (liftUnit case1Unit) Prod.snd () ∧
  (∫ i, (case1Unit i).tau ∂(kappa ())) ≠
    mCE (kappa ()) (fun i => (case1Unit i).tau) {i | (case1Unit i).complier}

/-- The composed population law is the atomic measure of `randomized (typeMass ∘ snd) (1/2)` on
`(Unit × Fin 3) × Bool`, and the profile assignment law `κ() × Bernoulli(1/2)` is the atomic
six-atom law `atomicMeasure sixMass`. Proof: both sides are finite measures on a countable
type with measurable singletons; compare singleton masses (`Measure.ext_of_singleton`,
`Measure.compProd_const`, `Measure.prod_prod`). -/
def N1 : Prop :=
  kernelPopulationLaw muX kappa (1 / 2) =
      atomicMeasure (randomized (fun l : Unit × Fin 3 => typeMass l.2) (1 / 2)) ∧
    (kappa ()).prod (bernoulliMeasure (1 / 2)) = atomicMeasure sixMass

/-- Given `FiniteMeasure.N1`, `FiniteMeasure.N2`, `FiniteMeasure.N3` and `N1`, the witness holds. Global IV: rewrite with `N1` and apply
`FiniteMeasure.N3` to `FIV (randomized (typeMass ∘ snd) (1/2)) (liftUnit (case1Unit ∘ snd)) Prod.snd`,
which is proved exactly like the FIV part of `ignorability_counterexample`
(`randomized_valid`, `randomized_independent`, `norm_num`); note
`kernelPopulationUnit case1Unit = liftUnit (fun l => case1Unit l.2)` definitionally.
Profile facts: rewrite with the second half of `N1` and transfer the six-atom values. -/
def N2 : Prop :=
  FiniteMeasure.N1 → FiniteMeasure.N2 → FiniteMeasure.N3 → N1 → Witness

/-- The intermediate propositions imply the conclusion. -/
theorem assemble (hFM1 : FiniteMeasure.N1) (hFM2 : FiniteMeasure.N2)
    (hFM3 : FiniteMeasure.N3) (h1 : N1) (h2 : N2) : Target := by
  intro h
  obtain ⟨hμ, hκ, hprof, hiv, hsupp, hy0, hy1, hc, hi, hne⟩ := h2 hFM1 hFM2 hFM3 h1
  have := hμ
  have := hκ
  exact hne (h muX kappa case1Unit (1 / 2) (by norm_num) (by norm_num) hprof hiv () hsupp
    hy0 hy1 hc hi)

end

end AronowAudit.P029.Wave1.IgnorabilityAllProfiles
