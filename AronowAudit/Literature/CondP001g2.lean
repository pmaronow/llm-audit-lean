import AronowAudit.P001.P001_Foundations

/-!
Conditional-independence characterization and a discrete ATE statement
conditional on that characterization. No proofs are supplied.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace AronowAudit.Literature

universe u

/-- Olav Kallenberg, *Foundations of Modern Probability*, 2nd edition,
Springer (2002), Proposition 6.6 (conditional independence, Doob), p. 110.
The sigma-fields below are arbitrary sub-sigma-fields of the ambient probability
space.  The left side is the preceding event-factorization definition of
conditional independence; the right side is equation (8) of the proposition.
All conditional probabilities are represented by conditional expectations of
real indicators.  No standard-Borel or countability assumption is imposed.
Source text: https://djvu.online/file/t4FlvxuKFFZGW (printed p. 110).
Publisher: https://doi.org/10.1007/978-1-4757-4015-8 . -/
noncomputable def Kallenberg2002Prop6_6 : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ),
    @IsProbabilityMeasure Ω mΩ μ →
    ∀ (F G H : MeasurableSpace Ω), F ≤ mΩ → G ≤ mΩ → H ≤ mΩ →
    ((∀ (s t : Set Ω), MeasurableSet[F] s → MeasurableSet[H] t →
      (μ[Set.indicator (s ∩ t) (fun _ => (1 : ℝ)) | G]) =ᵐ[μ]
        (fun ω => (μ[Set.indicator s (fun _ => (1 : ℝ)) | G]) ω *
          (μ[Set.indicator t (fun _ => (1 : ℝ)) | G]) ω)) ↔
     (∀ (t : Set Ω), MeasurableSet[H] t →
       (μ[Set.indicator t (fun _ => (1 : ℝ)) | F ⊔ G]) =ᵐ[μ]
         (μ[Set.indicator t (fun _ => (1 : ℝ)) | G])))

end AronowAudit.Literature

namespace AronowAudit.P001

universe u v


/-- Discrete ATE statement with the general conditional-independence
characterization as a hypothesis. -/
noncomputable def explicit_ignorability_discrete_ate_conditional_statement : Prop :=
  AronowAudit.Literature.Kallenberg2002Prop6_6.{u} →
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1) (hD : Measurable D)
   (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ) (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (p : E → ℝ) (hp : IsCEF μ X D p) (ε : ℝ) (hε : 0 < ε)
   (hpos : ∀ ω,ε < p (X ω) ∧ p (X ω) < 1-ε)
   (hCI : CI μ X hX (fun ω => (Y0 ω,Y1 ω)) D)
   (m0 m1 : E → ℝ)
   (hm0 : IsCEF (μ.restrict {ω | D ω=0}) X (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m0)
   (hm1 : IsCEF (μ.restrict {ω | D ω=1}) X (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m1)
   (hmi0 : Integrable (m0 ∘ X) μ) (hmi1 : Integrable (m1 ∘ X) μ),
    mean μ (fun ω => Y1 ω-Y0 ω)=
   (∑' x : E,m1 x*prob μ {ω | X ω=x})-(∑' x : E,m0 x*prob μ {ω | X ω=x})

end AronowAudit.P001

