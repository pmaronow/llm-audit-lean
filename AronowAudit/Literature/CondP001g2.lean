import AronowAudit.P001.P001_Foundations

/-!
Conditional-statement assessment for cond-P001g2.  No proofs are supplied.
The imported P001 module is used for its definitions, not for held theorem proofs.
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

#print Kallenberg2002Prop6_6
#check @Kallenberg2002Prop6_6

end AronowAudit.Literature

namespace AronowAudit.P001

universe u v

/-- Frozen proposition from P001_Foundations, with only the general literature input added. -/
noncomputable def placebo_linear_cef_correction_conditional_statement : Prop :=
  AronowAudit.Literature.Kallenberg2002Prop6_6.{u} →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
   (hX : Measurable X) (hW : Measurable W) (hD : Measurable D)
   (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (hSupportD : 0 < prob μ {ω | D ω=1} ∧ prob μ {ω | D ω=1} < 1)
   (hX2 : ∀ k,MemLp (fun ω => X ω k) 2 μ) (hW2 : ∀ k,MemLp (fun ω => W ω k) 2 μ)
   (hCI : CI μ X hX W D) (γ : Fin (K+1) → ℝ) (hcef : IsCEF μ X D (linearPredictor γ))
   (hRank : IsUnit (Matrix.det ((fun j k : Fin (K+L+1) => mean μ (fun ω =>
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) j)*
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) k))) : Matrix (Fin (K+L+1)) (Fin (K+L+1)) ℝ))),
   IsCEF μ (fun ω => (X ω,W ω)) D (fun xw => linearPredictor γ xw.1) ∧
   (∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     mean μ (fun ω => (D ω-linearPredictor γ (X ω))^2) ≤
       mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)) ∧
   ∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     (mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)=
       mean μ (fun ω => (D ω-linearPredictor γ (X ω))^2)) ↔
       a=γ 0 ∧ (∀ k,b k=γ k.succ) ∧ (∀ k,c k=0)

/-- Frozen proposition from P001_Foundations, with only the general literature input added. -/
noncomputable def placebo_zero_coefficients_unique_conditional_statement : Prop :=
  AronowAudit.Literature.Kallenberg2002Prop6_6.{u} →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
   (hX : Measurable X) (hW : Measurable W) (hD : Measurable D)
   (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (hX2 : ∀ k,MemLp (fun ω => X ω k) 2 μ) (hW2 : ∀ k,MemLp (fun ω => W ω k) 2 μ)
   (hCI : CI μ X hX W D) (γ : Fin (K+1) → ℝ) (hcef : IsCEF μ X D (linearPredictor γ))
   (hRank : IsUnit (Matrix.det ((fun j k : Fin (K+L+1) => mean μ (fun ω =>
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) j)*
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) k))) : Matrix (Fin (K+L+1)) (Fin (K+L+1)) ℝ))),
   ∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     (mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)=
       mean μ (fun ω => (D ω-linearPredictor γ (X ω))^2)) ↔
       a=γ 0 ∧ (∀ k,b k=γ k.succ) ∧ (∀ k,c k=0)

/-- Frozen discrete ATE proposition, with only the general literature input added. -/
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

set_option pp.universes true in
#check @AronowAudit.P001.placebo_linear_cef_correction_conditional_statement
set_option pp.universes true in
#check @AronowAudit.P001.placebo_zero_coefficients_unique_conditional_statement
set_option pp.universes true in
#check @AronowAudit.P001.explicit_ignorability_discrete_ate_conditional_statement

#print axioms AronowAudit.Literature.Kallenberg2002Prop6_6
#print axioms AronowAudit.P001.placebo_linear_cef_correction_conditional_statement
#print axioms AronowAudit.P001.placebo_zero_coefficients_unique_conditional_statement
#print axioms AronowAudit.P001.explicit_ignorability_discrete_ate_conditional_statement

set_option pp.explicit true in
#print AronowAudit.Literature.Kallenberg2002Prop6_6

-- Inspect only the held declaration type for universe fidelity; never use its proof.
set_option pp.universes true in
#check @AronowAudit.P001.explicit_ignorability_discrete_ate
