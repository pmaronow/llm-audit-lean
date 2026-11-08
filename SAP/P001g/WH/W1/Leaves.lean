import SAP.P001g.WH.W1.Elementary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g.WH.W1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

universe u v

noncomputable section

/-- Transfer integrability of an X-measurable function from a selected arm to
the population under overlap. For nonnegative bounded truncations of |m(X)|,
the propensity CEF gives E[D f(X)] = E[p(X) f(X)] >= epsilon E[f(X)].
The left side is bounded by the finite arm integral of |m(X)|. Monotone
convergence as the truncation grows gives population integrability.
Alternatively identify the arm covariate law as p times the population law.
Expected size: 120–250 lines. This replaces the retired, different L1. -/
def T117_L1V2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (_hX : Measurable X)
    (D : Ω → ℝ), Measurable D → (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    ∀ p : E → ℝ, IsCEF μ X D p →
    ∀ ε : ℝ, 0 < ε → (∀ᵐ ω ∂μ, ε < p (X ω)) →
    ∀ m : E → ℝ, Measurable m →
      Integrable (m ∘ X) (μ.restrict {ω | D ω = 1}) → Integrable (m ∘ X) μ

/-- An integrable product of an arbitrary covariate-measurable multiplier and
a centered propensity residual has mean zero; the multiplier need not be
integrable. Use isCEF_condExp to get E[p(X)-D | X]=0, then
condExp_mul_of_aestronglyMeasurable_left (which requires the product and the
residual to be integrable), and integral_condExp. Expected size: 60–120 lines.
This replaces the retired, different L2. -/
def T117_L2V2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (_hX : Measurable X)
    (D : Ω → ℝ) (p : E → ℝ), IsCEF μ X D p →
    ∀ H : E → ℝ, Measurable H →
      Integrable (fun ω => H (X ω) * (p (X ω) - D ω)) μ →
      mean μ (fun ω => H (X ω) * (p (X ω) - D ω)) = 0

/-- All missing clauses are elementary integral or finite-sum calculations. -/
theorem T115_assembly : T115WholeStatement := by
  constructor
  · intro Ω _ μ _ Y0 Y1 D h0 h1 hD hi0 hi1 _hb hp
    exact population_chain μ Y0 Y1 D h0 h1 hD hi0 hi1 hp
  · intro n hn y d hb hc1 hc0
    exact empiricalPairs_formula hn y d hb hc1 hc0

/-- Overlap supplies the regression branch's population integrability; the
centered-residual identity handles cancellation in the propensity branch. -/
theorem T117_assembly (h1 : T117_L1V2.{u, 0}) (h2 : T117_L2V2.{u, 0}) : T117WholeStatement.{u} := by
  intro Ω _ K μ _ X hX Y0 Y1 D h0 hY1 hD hi0 hi1 hb hp0 hp1 p hp hpos hCI Y
  have hI : Integrable (fun ω => wholeIPWScore (Y ω) (D ω) (p (X ω))) μ :=
    causal_ipw_integrable μ X hX Y0 Y1 D h0 hY1 hD hi0 hi1 hb p hp hpos hCI
  have hold := SAP.P001g.Bridge.t117 μ X hX Y0 Y1 D h0 hY1 hD hi0 hi1 hb hp0 hp1 p hp hpos hCI
  change Integrable (fun ω => wholeIPWScore (Y ω) (D ω) (p (X ω))) μ ∧ _
  refine ⟨hI, hold.1, ?_⟩
  intro m0 m1 q hm0 hm1 hq hS hcorrect
  rcases hcorrect with ⟨hc0, hc1, hqpos⟩ | hqp
  · obtain ⟨ε, hε, hεp⟩ := hpos
    have him1 : Integrable (m1 ∘ X) μ :=
      h1 μ X hX D hD hb p hp ε hε (hεp.mono fun _ h => h.1) m1 hm1 hc1.2.2.1
    have hpC : IsCEF μ X (fun ω => 1 - D ω) (fun x => 1 - p x) :=
      AronowAudit.P001.Wave1.CausalIpwDr.n2_proof μ X D p hp
    have hbC : ∀ᵐ ω ∂μ, 1 - D ω = 0 ∨ 1 - D ω = 1 :=
      hb.mono fun _ h => by rcases h with h | h <;> simp [h]
    have hevent : {ω | 1 - D ω = 1} = {ω | D ω = 0} := by
      ext ω
      simp only [Set.mem_ofPred_eq, sub_eq_self]
    have him0 : Integrable (m0 ∘ X) μ := by
      apply h1 μ X hX (fun ω => 1 - D ω) (measurable_const.sub hD) hbC
        (fun x => 1 - p x) hpC ε hε (hεp.mono fun _ h => by linarith [h.2]) m0 hm0
      rw [hevent]
      exact hc0.2.2.1
    exact hold.2 m0 m1 q hm0 hm1 hq him0 him1 (Or.inl ⟨hc0, hc1, hqpos⟩)
  · let H : (Fin K → ℝ) → ℝ := fun x => m1 x / p x + m0 x / (1 - p x)
    have hH : Measurable H :=
      (hm1.div hp.1).add (hm0.div (measurable_const.sub hp.1))
    obtain ⟨ε, hε, hεp⟩ := hpos
    have halgebra : (fun ω => wholeAugmentedScore (Y ω) (D ω) (m0 (X ω)) (m1 (X ω)) (q (X ω)) -
        wholeIPWScore (Y ω) (D ω) (p (X ω))) =ᵐ[μ]
        (fun ω => H (X ω) * (p (X ω) - D ω)) := by
      filter_upwards [hqp, hεp] with ω hω hpω
      change q (X ω) = p (X ω) at hω
      have hpn : p (X ω) ≠ 0 := (hε.trans hpω.1).ne'
      have hpc : 1 - p (X ω) ≠ 0 := by linarith [hpω.2]
      rw [hω]
      dsimp [wholeAugmentedScore, wholeIPWScore, H]
      field_simp [hpn, hpc] <;> ring
    have hprod : Integrable (fun ω => H (X ω) * (p (X ω) - D ω)) μ :=
      (hS.sub hI).congr halgebra
    have hz := h2 μ X hX D p hp H hH hprod
    have hz' : mean μ (fun ω => wholeAugmentedScore (Y ω) (D ω) (m0 (X ω)) (m1 (X ω)) (q (X ω))) -
        mean μ (fun ω => wholeIPWScore (Y ω) (D ω) (p (X ω))) = 0 := by
      unfold mean
      rw [← integral_sub hS hI, integral_congr_ae halgebra]
      exact hz
    have hid : mean μ (fun ω => Y1 ω - Y0 ω) =
        mean μ (fun ω => wholeIPWScore (Y ω) (D ω) (p (X ω))) := hold.1
    linarith

/-- The printed random-interval requirement is refuted without any new leaves. -/
theorem T128_assembly : T128WholeStatement := normalInterval_refuted

end
end SAP.P001g.WH.W1
