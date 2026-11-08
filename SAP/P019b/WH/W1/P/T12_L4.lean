import SAP.P019b.WH.W1.Leaves
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000
namespace SAP.P019b.WH.W1.P.T12_L4
open scoped BigOperators
open MeasureTheory ProbabilityTheory
noncomputable section
open Classical
/-- The sample obtained by applying the observable code coordinatewise. -/
def codeSample {Ω : Type} {m : ℕ} (e : Ω → Fin m) {n : ℕ}
    (s : Fin n → Ω) : Fin n → Fin m := fun i => e (s i)
/-- The observable tuple after applying the finite code. -/
def encodedObs {Ω : Type} {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (ω : Ω) : ℕ × Bool × Bool × Bool × ℕ :=
  (F.W (e ω), F.X (e ω), F.Y (e ω), F.Z (e ω), F.V (e ω))
/-- The original observable tuple. -/
def wholeObs {Ω : Type} [MeasurableSpace Ω] (S : WholeStudy Ω)
    (ω : Ω) : ℕ × Bool × Bool × Bool × ℕ :=
  (S.W ω, S.X ω, S.Y ω, S.Z ω, S.V ω)
lemma codeSample_measurable {Ω : Type} [MeasurableSpace Ω] {m n : ℕ}
    (e : Ω → Fin m) (he : Measurable e) :
    Measurable (codeSample e : (Fin n → Ω) → (Fin n → Fin m)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact he.comp (measurable_pi_apply i)
lemma encoded_measure {Ω : Type} [MeasurableSpace Ω] (S : WholeStudy Ω)
    {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (he : WholeEncoding S F e) :
    Measure.map e S.law = AronowAudit.P019.Wave1.t19_measure
      (SAP.P019b.Bridge.toLaw F.law) := by
  apply Measure.ext_of_singleton
  intro j
  rw [Measure.map_apply he.1 (measurableSet_singleton j)]
  change S.law {ω | e ω = j} = _
  rw [he.2.1 j, AronowAudit.P019.Wave1.t19_measure_apply,
    SAP.P019b.Bridge.prob_eq]
  simp only [FiniteLaw.prob, FiniteLaw.mean, Set.mem_singleton_iff,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
lemma finite_product_measure {m n : ℕ} (P : FiniteLaw (Fin m)) :
    Measure.pi (fun _ : Fin n => AronowAudit.P019.Wave1.t19_measure
      (SAP.P019b.Bridge.toLaw P)) =
      AronowAudit.P019.Wave1.t19_measure (SAP.P019b.Bridge.toLaw (P.iid n)) := by
  apply Measure.ext_of_singleton
  intro s
  rw [Measure.pi_singleton, AronowAudit.P019.Wave1.t19_measure_apply,
    SAP.P019b.Bridge.prob_eq]
  simp only [FiniteLaw.prob, FiniteLaw.mean, Set.mem_singleton_iff,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    FiniteLaw.iid]
  simp only [AronowAudit.P019.Wave1.t19_measure_apply,
    SAP.P019b.Bridge.prob_eq, FiniteLaw.prob,
    FiniteLaw.mean, Set.mem_singleton_iff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => P.nonneg (s i))).symm
lemma code_sample_law {Ω : Type} [MeasurableSpace Ω] (S : WholeStudy Ω)
    {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (he : WholeEncoding S F e) (n : ℕ) :
    Measure.map (codeSample e) (S.iid n) =
      AronowAudit.P019.Wave1.t19_measure
        (SAP.P019b.Bridge.toLaw (F.law.iid n)) := by
  change Measure.map (codeSample e) (Measure.pi (fun _ : Fin n => S.law)) = _
  change Measure.map (fun s i => e (s i)) (Measure.pi (fun _ : Fin n => S.law)) = _
  rw [Measure.pi_map_pi (f := fun _ : Fin n => e) (fun _ => he.1.aemeasurable)]
  rw [encoded_measure S F e he]
  exact finite_product_measure F.law
lemma sample_cellCount_eq {Ω : Type} [MeasurableSpace Ω] (S : WholeStudy Ω)
    {m n : ℕ} (F : Study (Fin m)) (e : Ω → Fin m) (s : Fin n → Ω)
    (hobs : ∀ i, F.W (e (s i)) = S.W (s i) ∧
      F.X (e (s i)) = S.X (s i) ∧ F.Y (e (s i)) = S.Y (s i) ∧
      F.Z (e (s i)) = S.Z (s i) ∧ F.V (e (s i)) = S.V (s i))
    (z y : Bool) :
    F.cellCount (codeSample e s) z y = S.cellCount s z y := by
  unfold Study.cellCount WholeStudy.cellCount
  apply Finset.sum_congr rfl
  intro i hi
  rcases hobs i with ⟨_, _, hy, hz, _⟩
  simp [codeSample, Study.cell, WholeStudy.cell, hy, hz]
  by_cases hh : S.Z (s i) = z ∧ S.Y (s i) = y <;> simp [hh]
lemma sample_cellMean_eq {Ω : Type} [MeasurableSpace Ω] (S : WholeStudy Ω)
    {m n : ℕ} (F : Study (Fin m)) (e : Ω → Fin m) (s : Fin n → Ω)
    (hobs : ∀ i, F.W (e (s i)) = S.W (s i) ∧
      F.X (e (s i)) = S.X (s i) ∧ F.Y (e (s i)) = S.Y (s i) ∧
      F.Z (e (s i)) = S.Z (s i) ∧ F.V (e (s i)) = S.V (s i))
    (z y : Bool) (c : ℝ) :
    F.cellMean (codeSample e s) z y c = S.cellMean s z y c := by
  have hc := sample_cellCount_eq S F e s hobs z y
  have hsum :
      (∑ i, if F.cell z y (codeSample e s i) then
        (F.V (codeSample e s i) : ℝ) else 0) =
      (∑ i, if S.cell z y (s i) then (S.V (s i) : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rcases hobs i with ⟨_, _, hy, hz, hv⟩
    simp [codeSample, Study.cell, WholeStudy.cell, hy, hz, hv]
    by_cases hh : S.Z (s i) = z ∧ S.Y (s i) = y <;> simp [hh]
  unfold Study.cellMean WholeStudy.cellMean
  rw [hc, hsum]
lemma sample_cellVariance_eq {Ω : Type} [MeasurableSpace Ω]
    (S : WholeStudy Ω) {m n : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (s : Fin n → Ω)
    (hobs : ∀ i, F.W (e (s i)) = S.W (s i) ∧
      F.X (e (s i)) = S.X (s i) ∧ F.Y (e (s i)) = S.Y (s i) ∧
      F.Z (e (s i)) = S.Z (s i) ∧ F.V (e (s i)) = S.V (s i))
    (z y : Bool) :
    F.cellVariance (codeSample e s) z y = S.cellVariance s z y := by
  have hc := sample_cellCount_eq S F e s hobs z y
  have hm := sample_cellMean_eq S F e s hobs z y 0
  have hsum :
      (∑ i, if F.cell z y (codeSample e s i) then
        ((F.V (codeSample e s i) : ℝ) - F.cellMean (codeSample e s) z y 0)^2 else 0) =
      (∑ i, if S.cell z y (s i) then
        ((S.V (s i) : ℝ) - S.cellMean s z y 0)^2 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rcases hobs i with ⟨_, _, hy, hz, hv⟩
    simp [codeSample, Study.cell, WholeStudy.cell, hy, hz, hv, hm]
    by_cases hh : S.Z (s i) = z ∧ S.Y (s i) = y <;> simp [hh]
  unfold Study.cellVariance WholeStudy.cellVariance
  rw [hc, hsum]
lemma sample_statistics_eq {Ω : Type} [MeasurableSpace Ω]
    (S : WholeStudy Ω) {m n : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (s : Fin n → Ω)
    (hobs : ∀ i, F.W (e (s i)) = S.W (s i) ∧
      F.X (e (s i)) = S.X (s i) ∧ F.Y (e (s i)) = S.Y (s i) ∧
      F.Z (e (s i)) = S.Z (s i) ∧ F.V (e (s i)) = S.V (s i))
    (c1 c0 cV : ℝ) :
    (F.betaHat (codeSample e s) c1 c0,
      F.betaVarianceHat (codeSample e s) cV) =
      (S.betaHat s c1 c0, S.betaVarianceHat s cV) := by
  apply Prod.ext
  · unfold Study.betaHat WholeStudy.betaHat
    rw [sample_cellMean_eq S F e s hobs true true c1,
      sample_cellMean_eq S F e s hobs false true c0]
  · have hc1 := sample_cellCount_eq S F e s hobs true true
    have hc0 := sample_cellCount_eq S F e s hobs false true
    have hv1 := sample_cellVariance_eq S F e s hobs true true
    have hv0 := sample_cellVariance_eq S F e s hobs false true
    unfold Study.betaVarianceHat WholeStudy.betaVarianceHat
    rw [hc1, hc0, hv1, hv0]
lemma code_statistics_ae {Ω : Type} [MeasurableSpace Ω]
    (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (he : WholeEncoding S F e) (n : ℕ) (c1 c0 cV : ℝ) :
    (fun s => (S.betaHat s c1 c0, S.betaVarianceHat s cV)) =ᵐ[S.iid n]
      fun s => (F.betaHat (codeSample e s) c1 c0,
        F.betaVarianceHat (codeSample e s) cV) := by
  have hobs : ∀ᵐ ω ∂S.law, encodedObs F e ω = wholeObs S ω := by
    filter_upwards [he.2.2] with ω hω
    rcases hω with ⟨hw, hx, hy, hz, hv⟩
    simp [encodedObs, wholeObs, hw, hx, hy, hz, hv]
  have hobsPi := Measure.ae_eq_pi (μ := fun _ : Fin n => S.law)
    (fun _ => hobs)
  filter_upwards [hobsPi] with s hs
  have hobsSample : ∀ i, F.W (e (s i)) = S.W (s i) ∧
      F.X (e (s i)) = S.X (s i) ∧ F.Y (e (s i)) = S.Y (s i) ∧
      F.Z (e (s i)) = S.Z (s i) ∧ F.V (e (s i)) = S.V (s i) := by
    intro i
    have hi := congrFun hs i
    simpa only [encodedObs, wholeObs, Prod.mk.injEq] using hi
  exact (sample_statistics_eq S F e s hobsSample c1 c0 cV).symm
lemma finite_prob_nonneg {α : Type} [Fintype α] (P : FiniteLaw α)
    (D : α → Prop) : 0 ≤ P.prob D := by
  rw [FiniteLaw.prob, FiniteLaw.mean]
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (P.nonneg a) (by by_cases h : D a <;> simp [h])
lemma code_sample_prob {Ω : Type} [MeasurableSpace Ω]
    (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (he : WholeEncoding S F e) (n : ℕ) (D : (Fin n → Fin m) → Prop) :
    (S.iid n).real {s | D (codeSample e s)} =
      (F.law.iid n).prob D := by
  have hmap := code_sample_law S F e he n
  have h := congrArg (fun μ : Measure (Fin n → Fin m) => μ {t | D t}) hmap
  rw [Measure.map_apply (codeSample_measurable e he.1) (Set.toFinite _).measurableSet,
    AronowAudit.P019.Wave1.t19_measure_apply,
    SAP.P019b.Bridge.prob_eq] at h
  change (S.iid n) {s | D (codeSample e s)} =
    ENNReal.ofReal ((F.law.iid n).prob D) at h
  rw [measureReal_def, h, ENNReal.toReal_ofReal (finite_prob_nonneg _ _)]
lemma code_sample_integral {Ω : Type} [MeasurableSpace Ω]
    (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (he : WholeEncoding S F e) (n : ℕ) (f : (Fin n → Fin m) → ℝ) :
    (∫ s, f (codeSample e s) ∂S.iid n) = (F.law.iid n).mean f := by
  have hmap := code_sample_law S F e he n
  have hf : Integrable f (AronowAudit.P019.Wave1.t19_measure
      (SAP.P019b.Bridge.toLaw (F.law.iid n))) :=
    Integrable.of_finite
  calc
    (∫ s, f (codeSample e s) ∂S.iid n) =
        ∫ t, f t ∂AronowAudit.P019.Wave1.t19_measure
          (SAP.P019b.Bridge.toLaw (F.law.iid n)) := by
      rw [← hmap] at hf
      rw [← hmap]
      exact (integral_map (codeSample_measurable e he.1).aemeasurable
        hf.aestronglyMeasurable).symm
    _ = (SAP.P019b.Bridge.toLaw (F.law.iid n)).mean f :=
      AronowAudit.P019.Wave1.t19_integral _ _
    _ = (F.law.iid n).mean f := SAP.P019b.Bridge.mean_eq _ _
lemma statistics_integrable {Ω : Type} [MeasurableSpace Ω]
    (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (he : WholeEncoding S F e) (n : ℕ) (c1 c0 cV : ℝ)
    (g : ℝ → ℝ → ℝ) :
    Integrable (fun s => g (S.betaHat s c1 c0) (S.betaVarianceHat s cV))
      (S.iid n) := by
  let f : (Fin n → Fin m) → ℝ := fun t =>
    g (F.betaHat t c1 c0) (F.betaVarianceHat t cV)
  have hf : Integrable f (AronowAudit.P019.Wave1.t19_measure
      (SAP.P019b.Bridge.toLaw (F.law.iid n))) :=
    Integrable.of_finite
  have hcomp : Integrable (f ∘ codeSample e) (S.iid n) := by
    rw [← code_sample_law S F e he n] at hf
    exact hf.comp_measurable (codeSample_measurable e he.1)
  have hcongr := (code_statistics_ae S F e he n c1 c0 cV).symm
  have hfun : (f ∘ codeSample e) =ᵐ[S.iid n]
      fun s => g (S.betaHat s c1 c0) (S.betaVarianceHat s cV) := by
    filter_upwards [hcongr] with s hs
    simpa [f, Function.comp_def] using congrArg (fun p : ℝ × ℝ => g p.1 p.2) hs
  exact hcomp.congr hfun
lemma statistics_integral_eq {Ω : Type} [MeasurableSpace Ω]
    (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (he : WholeEncoding S F e) (n : ℕ) (c1 c0 cV : ℝ)
    (g : ℝ → ℝ → ℝ) :
    (∫ s, g (S.betaHat s c1 c0) (S.betaVarianceHat s cV) ∂S.iid n) =
      (F.law.iid n).mean (fun s => g (F.betaHat s c1 c0)
        (F.betaVarianceHat s cV)) := by
  have hstats := code_statistics_ae S F e he n c1 c0 cV
  have hfun : (fun s => g (S.betaHat s c1 c0) (S.betaVarianceHat s cV)) =ᵐ[S.iid n]
      fun s => g (F.betaHat (codeSample e s) c1 c0)
        (F.betaVarianceHat (codeSample e s) cV) := by
    filter_upwards [hstats] with s hs
    exact congrArg (fun p : ℝ × ℝ => g p.1 p.2) hs
  rw [integral_congr_ae hfun]
  exact code_sample_integral S F e he n
    (fun s => g (F.betaHat s c1 c0) (F.betaVarianceHat s cV))
lemma statistics_event_measurable {Ω : Type} [MeasurableSpace Ω]
    (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (he : WholeEncoding S F e) (n : ℕ) (c1 c0 cV : ℝ)
    (D : ℝ → ℝ → Prop) :
    MeasurableSet {s : Fin n → Ω | D (F.betaHat (codeSample e s) c1 c0)
      (F.betaVarianceHat (codeSample e s) cV)} := by
  let A : Set (Fin n → Fin m) := {t | D (F.betaHat t c1 c0)
    (F.betaVarianceHat t cV)}
  change MeasurableSet (codeSample e ⁻¹' A)
  exact (Set.toFinite A).measurableSet.preimage
    (codeSample_measurable e he.1)
lemma statistics_event_ae_eq {Ω : Type} [MeasurableSpace Ω]
    (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (he : WholeEncoding S F e) (n : ℕ) (c1 c0 cV : ℝ)
    (D : ℝ → ℝ → Prop) :
    {s | D (S.betaHat s c1 c0) (S.betaVarianceHat s cV)} =ᵐ[S.iid n]
      {s | D (F.betaHat (codeSample e s) c1 c0)
        (F.betaVarianceHat (codeSample e s) cV)} := by
  filter_upwards [code_statistics_ae S F e he n c1 c0 cV] with s hs
  exact congrArg (fun p : ℝ × ℝ => D p.1 p.2) hs
lemma statistics_probability_eq {Ω : Type} [MeasurableSpace Ω]
    (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (he : WholeEncoding S F e) (n : ℕ) (c1 c0 cV : ℝ)
    (D : ℝ → ℝ → Prop) :
    S.sampleProb n (fun s => D (S.betaHat s c1 c0) (S.betaVarianceHat s cV)) =
      (F.law.iid n).prob
        (fun s => D (F.betaHat s c1 c0) (F.betaVarianceHat s cV)) := by
  have hsets := statistics_event_ae_eq S F e he n c1 c0 cV D
  have hprob := code_sample_prob S F e he n
    (fun s => D (F.betaHat s c1 c0) (F.betaVarianceHat s cV))
  calc
    S.sampleProb n (fun s => D (S.betaHat s c1 c0) (S.betaVarianceHat s cV)) =
        (S.iid n).real {s | D (S.betaHat s c1 c0) (S.betaVarianceHat s cV)} := rfl
    _ = (S.iid n).real {s | D (F.betaHat (codeSample e s) c1 c0)
        (F.betaVarianceHat (codeSample e s) cV)} := measureReal_congr hsets
    _ = (F.law.iid n).prob
        (fun s => D (F.betaHat s c1 c0) (F.betaVarianceHat s cV)) := hprob
lemma statistics_nullMeasurable {Ω : Type} [MeasurableSpace Ω]
    (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m)) (e : Ω → Fin m)
    (he : WholeEncoding S F e) (n : ℕ) (c1 c0 cV : ℝ)
    (D : ℝ → ℝ → Prop) :
    NullMeasurableSet {s | D (S.betaHat s c1 c0) (S.betaVarianceHat s cV)}
      (S.iid n) := by
  have hmeas := statistics_event_measurable S F e he n c1 c0 cV D
  have hsets := statistics_event_ae_eq S F e he n c1 c0 cV D
  exact (hmeas.nullMeasurableSet).congr hsets.symm
end
end SAP.P019b.WH.W1.P.T12_L4
open SAP.P019b.WH.W1.P.T12_L4
theorem SAP.P019b.WH.W1.T12_L4_proof : SAP.P019b.WH.W1.T12_L4 := by
  intro Ω hΩ S m F e he n c1 c0 cV
  constructor
  · intro g
    constructor
    · exact statistics_integrable S F e he n c1 c0 cV g
    · exact statistics_integral_eq S F e he n c1 c0 cV g
  · intro D
    constructor
    · exact statistics_nullMeasurable S F e he n c1 c0 cV D
    · exact statistics_probability_eq S F e he n c1 c0 cV D
