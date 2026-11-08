import SAP.P001e.Defs.WholeW4
import SAP.P001e.Bridge
import AronowAudit.P001.Wave1.MarSelection.N1
import AronowAudit.P001.Wave1.MarSelection.N2
import AronowAudit.P001.Wave1.MarSelection.N3
import AronowAudit.P001.Wave1.MarSelection.N4
import AronowAudit.P001.Wave1.MarSelection.N5
import AronowAudit.P001.Wave1.CausalIpwDr.N1
import AronowAudit.P001.Wave1.CausalIpwDr.N2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Classical

namespace SAP.P001e.WH.W4

universe u v
noncomputable section

/-- Rank-free OLS normal equations for the intercept and treatment regressor.
Proof route: perturb the intercept by t, then perturb the treatment coefficient
by t. Each residual sum of squares is a polynomial with a global minimum at 0.
Differentiate the finite sum and use `IsLocalMin.hasDerivAt_eq_zero`; its derivatives
are -2 times the displayed sums. No uniqueness, rank, binary-treatment, or
positive-sample-size assumption is needed. Expected proof: under 100 lines. -/
def T93_L1 : Prop :=
  ∀ {n K : ℕ} (Y D : Fin n → ℝ) (X : Fin n → Fin K → ℝ)
    (a b : ℝ) (c : Fin K → ℝ) (hfit : IsPooledOLSW4 Y D X a b c),
    let e := fun i => Y i - (a + ∑ k, X i k * c k) - b * D i
    (∑ i, e i) = 0 ∧ (∑ i, D i * e i) = 0

/-- Restriction of a joint observed CEF to a treatment arm, and lifting its
integrability to the whole covariate distribution under uniform overlap.
First use the joint CEF integral identity on `{d} × A`; on the arm D=d its
composition equals m(d,X), proving the restricted CEF and its integrability.
For the lifting step put ν=map X (μ restricted to D=d), λ=map X μ. The propensity
identity and η<p<1-η give `(ENNReal.ofReal η) • λ ≤ ν`: for each measurable A,
the selected mass of X⁻¹A is the integral of p(X), or 1-p(X), over X⁻¹A.
Transfer integrability along this measure inequality and cancel the positive
finite scalar. Use `integrable_map_measure`, `Integrable.mono_measure`, and
`integrable_smul_measure`. This needs neither causal independence nor moments
of individual covariates. All selection conditions are a.e., including binary D.
Expected proof: 150–300 lines; the restricted measures need not be probability measures. -/
def T93_L2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (D Y : Ω → ℝ) (hX : Measurable X) (hD : Measurable D)
    (hbinary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : IsConditionalMean μ X D p)
    (hpos : ∃ η : ℝ, 0 < η ∧
      ∀ᵐ ω ∂μ, η < p (X ω) ∧ p (X ω) < 1 - η)
    (m : ℝ × E → ℝ)
    (hm : IsConditionalMean μ (fun ω => (D ω, X ω)) Y m)
    (d : ℝ) (hd : d = 0 ∨ d = 1),
    IsConditionalMean (μ.restrict {ω | D ω = d}) X Y (fun x => m (d, x)) ∧
    Integrable (fun ω => m (d, X ω)) μ

/-- Existing selection-transfer proofs applied to each potential outcome.
Unlike the older all-points wrapper, this glue retains a.e. binary treatment
and a.e. overlap throughout. -/
theorem armTransferW4 {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (D Y0 Y1 : Ω → ℝ) (hD : Measurable D)
    (h0 : Measurable Y0) (h1 : Measurable Y1)
    (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ)
    (hbinary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : IsConditionalMean μ X D p)
    (hpos : ∃ η : ℝ, 0 < η ∧
      ∀ᵐ ω ∂μ, η < p (X ω) ∧ p (X ω) < 1 - η)
    (hind : CondIndependent μ X hX (fun ω => (Y0 ω, Y1 ω)) D)
    (m0 m1 : E → ℝ)
    (hm0 : IsConditionalMean (μ.restrict {ω | D ω = 0}) X
      (fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω)) m0)
    (hm1 : IsConditionalMean (μ.restrict {ω | D ω = 1}) X
      (fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω)) m1)
    (hmi0 : Integrable (m0 ∘ X) μ) (hmi1 : Integrable (m1 ∘ X) μ) :
    IsConditionalMean μ X Y0 m0 ∧ IsConditionalMean μ X Y1 m1 := by
  have hU := h0.prodMk h1
  have hbinary0 : ∀ᵐ ω ∂μ, 1 - D ω = 0 ∨ 1 - D ω = 1 := by
    filter_upwards [hbinary] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hind0 := AronowAudit.P001.Wave1.CausalIpwDr.n1_proof
    μ X hX (fun ω => (Y0 ω, Y1 ω)) D hind
  have hp0 := AronowAudit.P001.Wave1.CausalIpwDr.n2_proof μ X D p hp
  obtain ⟨η, hη, hηp⟩ := hpos
  have hpos1 : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω) :=
    ⟨η, hη, hηp.mono (fun _ h => h.1)⟩
  have hpos0 : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < (1 - p (X ω)) := by
    refine ⟨η, hη, ?_⟩
    filter_upwards [hηp] with ω hω
    linarith [hω.2]
  have hobs1 : ∀ᵐ ω ∂μ, D ω = 1 →
      realizedOutcome (Y0 ω) (Y1 ω) (D ω) = Y1 ω :=
    ae_of_all μ (fun ω h => by simp [realizedOutcome, h])
  have hobs0 : ∀ᵐ ω ∂μ, 1 - D ω = 1 →
      realizedOutcome (Y0 ω) (Y1 ω) (D ω) = Y0 ω := by
    apply ae_of_all μ
    intro ω h
    have hd : D ω = 0 := by linarith
    simp [realizedOutcome, hd]
  have hset : {ω | 1 - D ω = 1} = {ω | D ω = 0} := by
    ext ω
    simp only [Set.mem_ofPred_eq, sub_eq_self]
  have hm0' : IsConditionalMean (μ.restrict {ω | 1 - D ω = 1}) X
      (fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω)) m0 := by
    rw [hset]
    exact hm0
  constructor
  · exact AronowAudit.P001.Wave1.MarSelection.n5_proof
      AronowAudit.P001.Wave1.MarSelection.n1_proof
      AronowAudit.P001.Wave1.MarSelection.n4_proof
      AronowAudit.P001.Wave1.MarSelection.n3_proof
      AronowAudit.P001.Wave1.MarSelection.n2_proof
      μ X hX (fun ω => (Y0 ω, Y1 ω)) (fun ω => 1 - D ω)
      (fun z => z.2.1) (fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω))
      (fun x => 1 - p x) m0 hU (measurable_const.sub hD) measurable_snd.fst
      hbinary0 hind0 hp0 hpos0 hi0 hobs0 hm0' hmi0
  · exact AronowAudit.P001.Wave1.MarSelection.n5_proof
      AronowAudit.P001.Wave1.MarSelection.n1_proof
      AronowAudit.P001.Wave1.MarSelection.n4_proof
      AronowAudit.P001.Wave1.MarSelection.n3_proof
      AronowAudit.P001.Wave1.MarSelection.n2_proof
      μ X hX (fun ω => (Y0 ω, Y1 ω)) D
      (fun z => z.2.2) (fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω)) p m1
      hU hD measurable_snd.snd hbinary hind hp hpos1 hi1 hobs1 hm1 hmi1

/-- Conditional-mean subtraction uses only integrable quantities. -/
theorem conditionalMeanSubW4 {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y0 Y1 : Ω → ℝ) (m0 m1 : E → ℝ)
    (h0 : IsConditionalMean μ X Y0 m0) (h1 : IsConditionalMean μ X Y1 m1) :
    IsConditionalMean μ X (fun ω => Y1 ω - Y0 ω) (fun x => m1 x - m0 x) := by
  refine ⟨h1.1.sub h0.1, h1.2.1.sub h0.2.1, h1.2.2.1.sub h0.2.2.1, ?_⟩
  intro A hA
  change (∫ ω in X ⁻¹' A, Y1 ω - Y0 ω ∂μ) =
    ∫ ω in X ⁻¹' A, (m1 ∘ X) ω - (m0 ∘ X) ω ∂μ
  rw [integral_sub h1.2.1.integrableOn h0.2.1.integrableOn,
    integral_sub h1.2.2.1.integrableOn h0.2.2.1.integrableOn,
    h1.2.2.2 A hA, h0.2.2.2 A hA]
  rfl

/-- Assemble the population calculation from the overlap lifting leaf and
proved selection-transfer donors. Version uniqueness gives the explicit
almost-everywhere statement on the covariate law. -/
theorem populationW4 (h2 : T93_L2.{u, 0}) : PopulationLinearCEFW4.{u} := by
  intro Ω _ μ _ K X D Y0 Y1 hX hD h0 h1 hi0 hi1 hbinary p hp hpos hind a b c hcef
  dsimp only
  let Y := fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω)
  let m0 := fun x => pooledPredictionW4 a b c x 0
  let m1 := fun x => pooledPredictionW4 a b c x 1
  let τ := fun ω => Y1 ω - Y0 ω
  obtain ⟨hm0, hmi0⟩ := h2 μ X D Y hX hD hbinary p hp hpos
    (fun dx => pooledPredictionW4 a b c dx.2 dx.1) hcef 0 (Or.inl rfl)
  obtain ⟨hm1, hmi1⟩ := h2 μ X D Y hX hD hbinary p hp hpos
    (fun dx => pooledPredictionW4 a b c dx.2 dx.1) hcef 1 (Or.inr rfl)
  obtain ⟨hc0, hc1⟩ := armTransferW4 μ X hX D Y0 Y1 hD h0 h1 hi0 hi1
    hbinary p hp hpos hind m0 m1 hm0 hm1 hmi0 hmi1
  have hdiff := conditionalMeanSubW4 μ X Y0 Y1 m0 m1 hc0 hc1
  have hcontrast (x : Fin K → ℝ) : m1 x - m0 x = b := by
    dsimp [m0, m1, pooledPredictionW4]
    ring
  have hfun : (fun x => m1 x - m0 x) = (fun _ => b) := funext hcontrast
  have hconst : IsConditionalMean μ X τ (fun _ => b) := hfun ▸ hdiff
  have hce : μ[τ | MeasurableSpace.comap X inferInstance] =ᵐ[μ] (fun _ => b) :=
    (AronowAudit.P001.isCEF_condExp μ X hX τ (fun _ => b) hconst).symm
  refine ⟨hm0, hm1, hc0, hc1, hdiff, hconst, hce, ?_, ?_⟩
  · intro t ht
    have heq : t ∘ X =ᵐ[μ] (fun _ => b) :=
      (AronowAudit.P001.isCEF_condExp μ X hX τ t ht).trans hce
    have hmap : ∀ᵐ x ∂(μ.map X), t x = b :=
      (ae_map_iff hX.aemeasurable (measurableSet_eq_fun ht.1 measurable_const)).mpr heq
    filter_upwards [hmap] with x hx
    exact ⟨hx.trans (hcontrast x).symm, hcontrast x, hx⟩
  · have hmean := hconst.2.2.2 Set.univ MeasurableSet.univ
    simpa [expectation, Set.preimage_univ] using hmean

/-- Finite-sample glue: the existing imputation identity supplies the averages;
filtered residual sums and the two completed-column means are elementary algebra. -/
theorem finiteW4 (h1 : T93_L1) : FiniteImputationW4 := by
  intro n K Y D X hbinary harms a b c hfit
  let g := fun i => a + ∑ k, X i k * c k
  let e := fun i => Y i - g i - b * D i
  let C := ((∑ i ∈ Finset.univ.filter (fun i => D i = 1), e i) -
    ∑ i ∈ Finset.univ.filter (fun i => D i = 0), e i) / (n : ℝ)
  let A := (∑ i, (pooledPredictionW4 a b c (X i) 1 -
    pooledPredictionW4 a b c (X i) 0)) / (n : ℝ)
  let M := ((∑ i ∈ Finset.univ.filter (fun i => D i = 1),
    (Y i - a - (∑ k, X i k * c k))) +
    ∑ i ∈ Finset.univ.filter (fun i => D i = 0),
      (a + b + (∑ k, X i k * c k) - Y i)) / (n : ℝ)
  change 0 < n ∧ (∑ i, e i) = 0 ∧ (∑ i, e i * D i) = 0 ∧ A = b ∧
    (∑ i, pooledPredictionW4 a b c (X i) 1) / (n : ℝ) -
      (∑ i, pooledPredictionW4 a b c (X i) 0) / (n : ℝ) = A ∧
    (∑ i, completedOutcomeW4 Y D X a b c 1 i) / (n : ℝ) -
      (∑ i, completedOutcomeW4 Y D X a b c 0 i) / (n : ℝ) = M ∧
    M = b + C ∧ C = 0 ∧ M = b
  have hn : 0 < n := by
    obtain ⟨i, _⟩ := harms.1
    have := i.isLt
    omega
  obtain ⟨he, heD⟩ := h1 Y D X a b c hfit
  change (∑ i, e i) = 0 at he
  change (∑ i, D i * e i) = 0 at heD
  have heDs : (∑ i, e i * D i) = 0 := by simpa only [mul_comm] using heD
  have hdonor := AronowAudit.P001.pooled_ols_imputation_identity
    hn Y D g b hbinary he heD
  have hsum1 : (∑ i ∈ Finset.univ.filter (fun i => D i = 1), e i) =
      ∑ i, D i * e i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rcases hbinary i with hd | hd <;> simp [hd]
  have hsum0 : (∑ i ∈ Finset.univ.filter (fun i => D i = 0), e i) = 0 := by
    calc
      (∑ i ∈ Finset.univ.filter (fun i => D i = 0), e i) =
          ∑ i, (e i - D i * e i) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        rcases hbinary i with hd | hd <;> simp [hd]
      _ = 0 := by rw [Finset.sum_sub_distrib, he, heD, sub_self]
  have hC : C = 0 := by dsimp [C]; rw [hsum1, heD, hsum0]; simp
  have hA : A = b := by
    calc
      A = (∑ i, ((g i + b) - g i)) / (n : ℝ) := by
        dsimp only [A]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        dsimp [pooledPredictionW4, g]
        ring
      _ = b := hdonor.2
  have hM : M = (∑ i, (D i * (Y i - g i) +
      (1 - D i) * (g i + b - Y i))) / (n : ℝ) := by
    dsimp [M]
    congr 1
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases hbinary i with hd | hd <;> simp [hd, g] <;> ring
  have hMb : M = b := hM.trans hdonor.1
  refine ⟨hn, he, heDs, hA, ?_, ?_, ?_, hC, hMb⟩
  · rw [← sub_div, ← Finset.sum_sub_distrib]
  · rw [← sub_div, ← Finset.sum_sub_distrib, hM]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rcases hbinary i with hd | hd
    all_goals simp [completedOutcomeW4, hd, pooledPredictionW4, g]
    all_goals ring
  · rw [hC, add_zero, hMb]

/-- Every corrected table entry and the exact rational fit are either definitional
or supplied by the already certified six-unit OLS and imputation proofs. -/
theorem correctedExampleW4 : CorrectedExampleW4 := by
  have hfit : IsUnit (exampleDesign.transpose * exampleDesign).det ∧
      leastSquaresCoef exampleDesign exampleY = exampleCoef :=
    AronowAudit.P001.causal_example_ols_fit
  have hagree : partialImputation exampleX1 = exampleCoef 1 ∧
      fullImputation exampleX1 = exampleCoef 1 :=
    AronowAudit.P001.corrected_imputation_table_agreement
  have hcoef : exampleCoef 1 = (6178 / 2437 : ℝ) := by rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, hfit.1, hfit.2, rfl,
    hagree.1.trans hcoef, hagree.2.trans hcoef, ?_, ?_⟩
  · rfl
  · ext i
    fin_cases i <;>
      norm_num [exampleCompletedW4, exampleD, exampleY, exampleX1, exampleX2]
  · ext i
    fin_cases i <;>
      norm_num [exampleCompletedW4, exampleD, exampleY, exampleX1, exampleX2]
  · ext i
    fin_cases i <;> rfl
  · ext i
    fin_cases i <;> rfl
  · norm_num [exampleCompletedW4, exampleD, exampleY, exampleX1, exampleX2,
      examplePrediction, exampleCoef, Fin.sum_univ_succ]
  · norm_num [exampleCompletedW4, exampleD, exampleY, exampleX1, exampleX2,
      examplePrediction, exampleCoef, Fin.sum_univ_succ]

/-- Whole T93: the only unfinished inputs are the two closed mathematical leaves.
All numerical calculations, selection transfer, CEF subtraction, version uniqueness,
expectation, and the connection to completed-column means are proved here. -/
theorem T93_assembly (h1 : T93_L1) (h2 : T93_L2.{u, 0}) : T93WholeStatement_W4.{u} := by
  refine ⟨?_, finiteW4 h1, populationW4 h2, correctedExampleW4⟩
  intro K a b c x
  dsimp [pooledPredictionW4]
  ring

end
end SAP.P001e.WH.W4
