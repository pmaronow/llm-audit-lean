/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integral transport between independence hypotheses and canonical products

Theorem-agnostic wrappers translating abstract-sample-space independence
hypotheses into integrals over explicit canonical product measures. For an
independent family $X_i : \Omega \to \beta_i$,
$$ \int_\Omega G\bigl((X_i(\omega))_i\bigr)\, d\mu
   \;=\; \int G \, d\Bigl(\bigotimes_i (X_i)_\# \mu\Bigr), $$
with a variant carrying a passenger product factor.
These identities move between "signs on `Ω`" and "signs as a product coordinate".

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.3 (joint law of an independent family;
footnote 7 on enlarging the probability space with independent signs). Pure
plumbing — no numbered theorem.

**Proof formalization notes.** The lemmas wrap
Mathlib bricks: `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map`,
`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`,
`MeasureTheory.MeasurePreserving.prod`, and `MeasureTheory.integral_map`.
Measurability of the integrand is taken as `AEStronglyMeasurable` with respect
to the *pushforward* measure — the natural hypothesis for `integral_map`.

**Bibliographic comments.** The identification of an independent family with
the product of its marginal laws is Kolmogorov's construction (*Grundbegriffe
der Wahrscheinlichkeitsrechnung*, 1933); the "enlarge the space by an
independent auxiliary sequence" device is standard in Banach-space probability
(Ledoux–Talagrand, *Probability in Banach Spaces*, 1991, Ch. 6).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Transport an integral of a function of an independent family to the
product of the marginal laws (HDP §6.3: the joint law of an independent
family is the product of the marginals). -/
theorem integral_eq_integral_pi_map {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {X : (i : ι) → Ω → β i}
    -- LEAN-ONLY: a.e.-measurability of the family; matches
    -- `iIndepFun_iff_map_fun_eq_pi_map`'s hypothesis shape
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    -- USER-INPUT: independent family; HDP §6.3
    (h_indep : iIndepFun X μ)
    {G : ((i : ι) → β i) → ℝ}
    -- LEAN-ONLY: integrand measurability w.r.t. the pushforward; the natural
    -- `integral_map` side condition
    (hG : AEStronglyMeasurable G (Measure.pi fun i => μ.map (X i))) :
    ∫ ω, G (fun i => X i ω) ∂μ = ∫ y, G y ∂(Measure.pi fun i => μ.map (X i)) := by
  have hφ : AEMeasurable (fun ω i => X i ω) μ := AEMeasurable.of_eval h_meas
  have hmap : μ.map (fun ω i => X i ω) = Measure.pi (fun i => μ.map (X i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map h_meas).mp h_indep
  rw [← hmap] at hG ⊢
  exact (integral_map hφ hG).symm

/-- Transport with a passenger product factor: an integral over `μ.prod ρ` of
a function of the independent family in the first coordinate equals the
integral over the canonical product `(⊗ᵢ (Xᵢ)#μ).prod ρ`. -/
theorem integral_prod_eq_integral_pi_prod {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {X : (i : ι) → Ω → β i}
    -- LEAN-ONLY: measurability of the family
    (h_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent family; HDP §6.3
    (h_indep : iIndepFun X μ)
    {γ : Type*} {mγ : MeasurableSpace γ} {ρ : Measure γ} [IsProbabilityMeasure ρ]
    {G : (((i : ι) → β i) × γ) → ℝ}
    -- LEAN-ONLY: integrand measurability w.r.t. the pushforward product
    (hG : AEStronglyMeasurable G ((Measure.pi fun i => μ.map (X i)).prod ρ)) :
    ∫ p, G (fun i => X i p.1, p.2) ∂(μ.prod ρ)
      = ∫ q, G q ∂((Measure.pi fun i => μ.map (X i)).prod ρ) := by
  have hφ : Measurable (fun ω i => X i ω) := Measurable.of_eval h_meas
  have hmapφ : μ.map (fun ω i => X i ω) = Measure.pi (fun i => μ.map (X i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (h_meas i).aemeasurable)).mp h_indep
  have hψ : Measurable (fun p : Ω × γ => (fun i => X i p.1, p.2)) :=
    (Measurable.of_eval (fun i => (h_meas i).comp measurable_fst)).prodMk measurable_snd
  have hmapψ : (μ.prod ρ).map (fun p : Ω × γ => (fun i => X i p.1, p.2))
      = (Measure.pi fun i => μ.map (X i)).prod ρ := by
    rw [show (fun p : Ω × γ => (fun i => X i p.1, p.2))
          = Prod.map (fun ω i => X i ω) id from rfl,
        ← Measure.map_prod_map μ ρ hφ measurable_id, Measure.map_id, hmapφ]
  rw [← hmapψ, integral_map hψ.aemeasurable (by rw [hmapψ]; exact hG)]


end StatLean.ConcentrationInequalities
