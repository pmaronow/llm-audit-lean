import AronowAudit.P001.Wave1.Gap.FidP001

/-!
# P001 printed PDA assertion and counterexample

The PDA assertion includes the joint vector/response PDF; neither the sample
space nor the dimension is fixed. A continuous-CEF counterexample refutes it.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.FidP001Contracts

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

universe u

noncomputable section




/-- P001-T102's printed well-definedness claim: Definition 4.3.7, p. 167 (PDF p. 185),
footnote 13, p. 166 (PDF p. 184), and the well-definedness remark, p. 168 (PDF p. 186).

Conventions: arbitrary measurable probability spaces in universe `u`, every finite real
covariate dimension and every actual coordinate; measurable covariate and response with
finite absolute first moments; continuous joint laws represented by a finite nonnegative
real density on the vector/response product, with a.e. measurability, integrability and
the law-with-density identity. `f` is any covariate PDF in the existing `HasVectorPDF`
sense. "Positive support" means `{x | 0 < f x}`.
CEFs are real extensions satisfying `IsCEF` for the same response and covariate under the
same law; values off covariate support are not prescribed. Differentiability means actual
two-sided differentiability at zero along the selected coordinate path at every
positive-density point. The assertion of well-definedness means existence of one actual
derivative shared by every pair of these CEF versions at the coordinatewise expectation.
No support or differentiability premise at that expectation is supplied by the paper.
No global C¹ assumption, particular law, dimension, derivative value or sample is fixed.
This is the distributional assertion, without the separate sample plug-in formula. -/
def printedContract_P001_T102 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
    (X : Ω → Fin K → ℝ) (Y : Ω → ℝ),
    Measurable X → Measurable Y →
    (∀ j, Integrable (fun ω => X ω j) μ) → Integrable Y μ →
    ∀ (f : (Fin K → ℝ) → ℝ) (q : ((Fin K → ℝ) × ℝ) → ℝ),
    HasVectorPDF (μ.map X) f →
    (AEMeasurable q volume ∧ (∀ z, 0 ≤ q z) ∧ Integrable q volume ∧
      μ.map (fun ω => (X ω, Y ω)) =
        volume.withDensity (fun z => ENNReal.ofReal (q z))) →
    ∀ (m₀ m₁ : (Fin K → ℝ) → ℝ), IsCEF μ X Y m₀ → IsCEF μ X Y m₁ →
    ∀ (k : Fin K),
    (∀ x, 0 < f x →
      DifferentiableAt ℝ (fun t => m₀ (Function.update x k (x k + t))) 0) →
    (∀ x, 0 < f x →
      DifferentiableAt ℝ (fun t => m₁ (Function.update x k (x k + t))) 0) →
    let xbar : Fin K → ℝ := fun j => mean μ (fun ω => X ω j)
    ∃ a : ℝ,
      HasDerivAt (fun t => m₀ (Function.update xbar k (xbar k + t))) a 0 ∧
      HasDerivAt (fun t => m₁ (Function.update xbar k (xbar k + t))) a 0


end
end AronowAudit.P001.Wave1.FidP001Contracts

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

universe u

/-- The continuous-CEF counterexample refutes the full printed PDA
well-definedness assertion. Transporting its joint PDF to the one-coordinate
vector product preserves the paper's joint-density class; lifting its sample
space supplies every universe. -/
theorem printed_pda_continuous_cef_counterexample_printed_negation :
    ¬ FidP001Contracts.printedContract_P001_T102.{u} := by
  classical
  intro H
  obtain ⟨μ, X, Y, f, m₀, m₁, q, hprob, hX, hY, hXi, hYi, hf, hq,
    hcef₀, hcef₁, hm₀, hm₁, _, hderiv⟩ := printed_pda_continuous_cef_counterexample
  haveI : IsProbabilityMeasure μ := hprob

  -- The scalar pair in the certificate is equivalent to the full Fin 1 vector/response pair.
  let e : ((Fin 1 → ℝ) × ℝ) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.funUnique (Fin 1) ℝ).prodCongr (MeasurableEquiv.refl ℝ)
  have hep : MeasurePreserving e volume volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).prod (MeasurePreserving.id volume)
  have hqvi : Integrable (q ∘ e) volume := hep.integrable_comp_of_integrable hq.2.2.1
  have hpair : μ.map (fun ω => (X ω, Y ω)) =
      (μ.map (fun ω => (X ω 0, Y ω))).map e.symm := by
    rw [Measure.map_map (f := fun ω : ℝ × ℝ => (X ω 0, Y ω))
      e.symm.measurable (((measurable_pi_apply 0).comp hX).prodMk hY)]
    congr 1
    funext ω
    apply Prod.ext
    · funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl
    · rfl
  have hqv : AEMeasurable (q ∘ e) volume ∧ (∀ z, 0 ≤ (q ∘ e) z) ∧
      Integrable (q ∘ e) volume ∧
      μ.map (fun ω => (X ω, Y ω)) =
        volume.withDensity (fun z => ENNReal.ofReal ((q ∘ e) z)) := by
    refine ⟨hqvi.aestronglyMeasurable.aemeasurable, fun z => hq.2.1 (e z), hqvi, ?_⟩
    rw [hpair, hq.2.2.2]
    ext A hA
    rw [Measure.map_apply e.symm.measurable hA,
      withDensity_apply _ (e.symm.measurable hA), withDensity_apply _ hA]
    exact (MeasurePreserving.symm e hep).setLIntegral_comp_preimage_emb
      e.symm.measurableEmbedding (fun z => ENNReal.ofReal ((q ∘ e) z)) A

  -- Lift the sample space so the negation holds for the contract at every universe level.
  let l : ULift.{u} (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.ulift
  let ν : Measure (ULift.{u} (ℝ × ℝ)) := μ.map l.symm
  have hl : MeasurePreserving l ν μ := by
    refine ⟨l.measurable, ?_⟩
    dsimp [ν]
    rw [Measure.map_map l.measurable l.symm.measurable, l.self_comp_symm, Measure.map_id]
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have hlaw {E : Type} [MeasurableSpace E] (g : (ℝ × ℝ) → E) (hg : Measurable g) :
      ν.map (g ∘ l) = μ.map g := by
    rw [← Measure.map_map hg l.measurable, hl.map_eq]
  have hcef (m : (Fin 1 → ℝ) → ℝ) (hc : IsCEF μ X Y m) :
      IsCEF ν (X ∘ l) (Y ∘ l) m := by
    refine ⟨hc.1, hl.integrable_comp_of_integrable hc.2.1,
      hl.integrable_comp_of_integrable hc.2.2.1, fun A hA => ?_⟩
    change (∫ ω in l ⁻¹' (X ⁻¹' A), Y (l ω) ∂ν) =
      ∫ ω in l ⁻¹' (X ⁻¹' A), (m ∘ X) (l ω) ∂ν
    rw [hl.setIntegral_preimage_emb l.measurableEmbedding,
      hl.setIntegral_preimage_emb l.measurableEmbedding]
    exact hc.2.2.2 A hA
  have hmean : (fun j => mean ν (fun ω => (X ∘ l) ω j)) =
      (fun j => mean μ (fun ω => X ω j)) := by
    funext j
    exact hl.integral_comp' (fun ω => X ω j)
  have hdiff (m : (Fin 1 → ℝ) → ℝ) (hm : ContDiff ℝ 1 m) :
      ∀ x : Fin 1 → ℝ, 0 < f x →
        DifferentiableAt ℝ (fun t => m (Function.update x 0 (x 0 + t))) 0 := by
    intro x _
    exact (hm.differentiable (by norm_num) _).comp 0
      (((contDiff_update 1 x 0).differentiable (by norm_num) _).comp 0
        (differentiableAt_const (x 0) |>.add differentiableAt_id))
  have hfv : HasVectorPDF (ν.map (X ∘ l)) f := by
    rw [hlaw X hX]
    exact hf
  have hqvl : AEMeasurable (q ∘ e) volume ∧ (∀ z, 0 ≤ (q ∘ e) z) ∧
      Integrable (q ∘ e) volume ∧
      ν.map (fun ω => ((X ∘ l) ω, (Y ∘ l) ω)) =
        volume.withDensity (fun z => ENNReal.ofReal ((q ∘ e) z)) := by
    change AEMeasurable (q ∘ e) volume ∧ (∀ z, 0 ≤ (q ∘ e) z) ∧
      Integrable (q ∘ e) volume ∧
      ν.map ((fun ω => (X ω, Y ω)) ∘ l) = _
    rw [hlaw _ (hX.prodMk hY)]
    exact hqv
  obtain ⟨a, ha₀, ha₁⟩ := @H (ULift.{u} (ℝ × ℝ)) _ ν _ 1 (X ∘ l) (Y ∘ l)
    (hX.comp l.measurable) (hY.comp l.measurable)
    (fun j => hl.integrable_comp_of_integrable (hXi j))
    (hl.integrable_comp_of_integrable hYi) f (q ∘ e) hfv hqvl
    m₀ m₁ (hcef m₀ hcef₀) (hcef m₁ hcef₁) 0 (hdiff m₀ hm₀) (hdiff m₁ hm₁)
  dsimp only at hderiv
  rw [hmean] at ha₀ ha₁
  exact zero_ne_one ((hderiv.1.unique ha₀).trans (ha₁.unique hderiv.2))

end AronowAudit.P001.Wave1

namespace AronowAudit.P001.Wave1.FidP001Contracts

universe u

end AronowAudit.P001.Wave1.FidP001Contracts
