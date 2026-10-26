import AronowAudit.Literature.CondP001cd

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
universe uΩ uE

namespace AronowAudit.P001.Wave1
local instance instDecidableCondP001cdProofs (p : Prop) : Decidable p := Classical.propDecidable p

open AronowAudit.Literature
set_option maxHeartbeats 800000
set_option maxRecDepth 3000

lemma CondP001cd_outer_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℝ) (hm : Measurable Z) (hi : Integrable Z μ) :
    boundedOuterExpectation μ Z = ∫ ω, Z ω ∂μ := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨∫ ω, Z ω ∂μ, ?_⟩
      rintro r ⟨g, hgm, hgi, hg, rfl⟩
      exact integral_mono hi hgi hg
    · exact ⟨Z, hm, hi, fun _ => le_rfl, rfl⟩
  · apply le_csInf
    · exact ⟨_, Z, hm, hi, fun _ => le_rfl, rfl⟩
    · rintro r ⟨g, hgm, hgi, hg, rfl⟩
      exact integral_mono hi hgi hg

lemma CondP001cd_measure_le_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → ℝ)
    (hi : Integrable g μ) (hn : ∀ ω, 0 ≤ g ω) (S : Set Ω)
    (hS : ∀ ω ∈ S, 1 ≤ g ω) : (μ S).toReal ≤ ∫ ω, g ω ∂μ := by
  have h := hi.measure_le_integral (ae_of_all μ hn) hS
  simpa [ENNReal.toReal_ofReal (integral_nonneg hn)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h

lemma CondP001cd_outer_event_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ)
    (hn : ∀ ω, 0 ≤ Z ω) (hb : ∀ ω, Z ω ≤ 1) (S : Set Ω)
    (hS : ∀ ω ∈ S, 1 ≤ Z ω) : (μ S).toReal ≤ boundedOuterExpectation μ Z := by
  apply le_csInf
  · exact ⟨1, (fun _ => 1), measurable_const, integrable_const 1,
      hb, by simp⟩
  · rintro r ⟨g, hgm, hgi, hg, rfl⟩
    exact CondP001cd_measure_le_integral μ g hgi (fun ω => (hn ω).trans (hg ω)) S
      (fun ω hω => (hS ω hω).trans (hg ω))

lemma CondP001cd_outer_event_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ)
    (hn : ∀ ω, 0 ≤ Z ω) (hb : ∀ ω, Z ω ≤ 1) (S : Set Ω)
    (hS : ∀ ω ∉ S, Z ω = 0) : boundedOuterExpectation μ Z ≤ (μ S).toReal := by
  let A := toMeasurable μ S
  have hA : MeasurableSet A := measurableSet_toMeasurable μ S
  have hsub : S ⊆ A := subset_toMeasurable μ S
  have he : (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ) = (μ S).toReal := by
    simp [integral_indicator_const, hA, A, measureReal_def]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨g, hgm, hgi, hg, rfl⟩
    exact integral_nonneg (fun ω => (hn ω).trans (hg ω))
  · refine ⟨A.indicator (fun _ => 1), measurable_const.indicator hA,
      (integrable_const 1).indicator hA, ?_, he⟩
    intro ω
    by_cases hw : ω ∈ A
    · simpa [Set.indicator_of_mem hw] using hb ω
    · have hwS : ω ∉ S := fun h => hw (hsub h)
      simp [Set.indicator_of_notMem hw, hS ω hwS]

/-- A continuous approximation to a lower half-line, with transition on (a,b). -/
def CondP001cd_ramp (a b t : ℝ) : ℝ := min 1 (max 0 ((b - t) / (b - a)))

lemma CondP001cd_ramp_bounds (a b t : ℝ) :
    0 ≤ CondP001cd_ramp a b t ∧ CondP001cd_ramp a b t ≤ 1 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

lemma CondP001cd_ramp_one {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    CondP001cd_ramp a b t = 1 := by
  have h : 1 ≤ (b-t)/(b-a) := (le_div_iff₀ (sub_pos.mpr hab)).2 (by linarith)
  exact min_eq_left ((le_max_right _ _).trans' h)

lemma CondP001cd_ramp_zero {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    CondP001cd_ramp a b t = 0 := by
  have h : (b-t)/(b-a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  simp [CondP001cd_ramp, max_eq_left h]

lemma CondP001cd_outer_CD {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : outerConverges (fun _ : ℕ => μ) Z ν) : CD μ Z ν := by
  intro x hc
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc (prob ν (Set.Iic x) - a) (by linarith)
    let y := x - δ / 2
    have hy : y < x := by dsimp [y]; linarith
    have hay : a < prob ν (Set.Iic y) := by
      have hh := hd (show dist y x < δ by
        rw [Real.dist_eq]
        dsimp [y]
        rw [abs_of_nonpos (by linarith)]
        linarith)
      rw [Real.dist_eq] at hh
      have := (abs_lt.mp hh).1
      linarith
    let f := CondP001cd_ramp y x
    have hf : Continuous f := by
      change Continuous (fun t => min 1 (max 0 ((x - t) / (x - y))))
      fun_prop
    have hfb : ∃ C : ℝ, ∀ t, |f t| ≤ C := ⟨1, fun t => by
      rw [abs_of_nonneg (CondP001cd_ramp_bounds y x t).1]
      exact (CondP001cd_ramp_bounds y x t).2⟩
    have hfi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable 1
      (ae_of_all ν (fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (CondP001cd_ramp_bounds y x t).1]
        exact (CondP001cd_ramp_bounds y x t).2))
    have hlow : prob ν (Set.Iic y) ≤ ∫ t, f t ∂ν :=
      CondP001cd_measure_le_integral ν f hfi
        (fun t => (CondP001cd_ramp_bounds y x t).1) (Set.Iic y)
        (fun t ht => le_of_eq (CondP001cd_ramp_one hy ht).symm)
    have hev := (tendsto_order.1 (h f hf hfb)).1 a (hay.trans_le hlow)
    filter_upwards [hev] with n hn
    exact hn.trans_le (CondP001cd_outer_event_upper μ (fun ω => f (Z n ω))
      (fun ω => (CondP001cd_ramp_bounds y x _).1)
      (fun ω => (CondP001cd_ramp_bounds y x _).2) {ω | Z n ω ≤ x}
      (fun ω hω => CondP001cd_ramp_zero hy (le_of_not_ge hω)))
  · intro b hb
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc (b - prob ν (Set.Iic x)) (by linarith)
    let y := x + δ / 2
    have hy : x < y := by dsimp [y]; linarith
    have hyb : prob ν (Set.Iic y) < b := by
      have hh := hd (show dist y x < δ by
        rw [Real.dist_eq]
        dsimp [y]
        rw [abs_of_nonneg (by linarith)]
        linarith)
      rw [Real.dist_eq] at hh
      have := (abs_lt.mp hh).2
      linarith
    let f := CondP001cd_ramp x y
    have hf : Continuous f := by
      change Continuous (fun t => min 1 (max 0 ((y - t) / (y - x))))
      fun_prop
    have hfb : ∃ C : ℝ, ∀ t, |f t| ≤ C := ⟨1, fun t => by
      rw [abs_of_nonneg (CondP001cd_ramp_bounds x y t).1]
      exact (CondP001cd_ramp_bounds x y t).2⟩
    have hupp : (∫ t, f t ∂ν) ≤ prob ν (Set.Iic y) := by
      have hm := integral_le_measure (μ := ν) (f := f) (s := Set.Iic y)
        (fun t _ => (CondP001cd_ramp_bounds x y t).2)
        (fun t ht => le_of_eq (CondP001cd_ramp_zero hy (le_of_not_ge ht)))
      have hh := ENNReal.toReal_mono (measure_ne_top ν _) hm
      simpa only [AronowAudit.P001.prob, ENNReal.toReal_ofReal
        (integral_nonneg (fun t => show 0 ≤ f t from
          (CondP001cd_ramp_bounds x y t).1))] using hh
    have hev := (tendsto_order.1 (h f hf hfb)).2 b (hupp.trans_lt hyb)
    filter_upwards [hev] with n hn
    exact (CondP001cd_outer_event_lower μ (fun ω => f (Z n ω))
      (fun ω => (CondP001cd_ramp_bounds x y _).1)
      (fun ω => (CondP001cd_ramp_bounds x y _).2) {ω | Z n ω ≤ x}
      (fun ω hω => le_of_eq (CondP001cd_ramp_one hy hω).symm)).trans_lt hn

lemma CondP001cd_weak_outer {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → E)
    (ν : Measure E) (hm : ∀ n, Measurable (Z n)) (h : WeakLimit μ Z ν) :
    outerConverges (fun _ : ℕ => μ) Z ν := by
  intro f hf hb
  have he (n : ℕ) : boundedOuterExpectation μ (fun ω => f (Z n ω)) =
      ∫ ω, f (Z n ω) ∂μ := by
    apply CondP001cd_outer_eq μ _ (hf.measurable.comp (hm n))
    obtain ⟨C, hC⟩ := hb
    exact Integrable.of_bound (hf.measurable.comp (hm n)).aestronglyMeasurable C
      (ae_of_all μ (fun ω => by change |f (Z n ω)| ≤ C; exact hC (Z n ω)))
  simp_rw [he]
  exact h f hf hb

/-- Adjoining the base point preserves the sequential derivative, even if the
original domain does not contain that point. -/
lemma CondP001cd_adjoin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D H : Set E) (T : E → ℝ) (F : E) (L : E →L[ℝ] ℝ)
    (hd : HadamardAt D H T F L) : HadamardAt (D ∪ {F}) H T F L := by
  intro h hh t hs ht ht0 hsh hv
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  by_cases hfreq : ∃ᶠ n in atTop, F + t (ns n) • hs (ns n) ∈ D
  · obtain ⟨ms, hms, hm⟩ := Filter.exists_seq_forall_of_frequently hfreq
    refine ⟨ms, ?_⟩
    exact hd h hh (fun n => t (ns (ms n))) (fun n => hs (ns (ms n)))
      (fun n => ht _) (ht0.comp (hns.comp hms)) (hsh.comp (hns.comp hms)) hm
  · have hev : ∀ᶠ n in atTop, hs (ns n) = 0 := by
      filter_upwards [not_frequently.mp hfreq] with n hn
      have hx : F + t (ns n) • hs (ns n) = F := (hv (ns n)).resolve_left hn
      have hz : t (ns n) • hs (ns n) = 0 := by simpa using hx
      exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt (ht _))
    have hEq : (fun n => hs (ns n)) =ᶠ[atTop] (fun _ => 0) := hev
    have hh0 : h = 0 := tendsto_nhds_unique (hsh.comp hns)
      (tendsto_const_nhds.congr' hEq.symm)
    refine ⟨id, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    simp [hn, hh0]

lemma CondP001cd_delta_outer {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdelta : VanDerVaart1998Delta.{uΩ, uE, 0})
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D H : Set E) (F : E) (T : E → ℝ) (L : E →L[ℝ] ℝ)
    (hd : HadamardAt D H T F L) (Fhat : ℕ → Ω → E)
    (hvalid : ∀ n ω, 0 < n → Fhat n ω ∈ D)
    (ν : Measure E) [IsProbabilityMeasure ν] (htangent : ν Hᶜ = 0)
    (hprocess : outerConverges (fun _ : ℕ => μ)
      (fun n ω => Real.sqrt n • (Fhat n ω - F)) ν) :
    CD μ (fun n ω => Real.sqrt n * (T (Fhat n ω) - T F)) (ν.map L) := by
  have hd' : tangentialHadamard (D ∪ {F}) H T F L.toLinearMap := by
    refine ⟨by simp, L.continuous.continuousOn, ?_⟩
    intro h hh t hs ht ht0 hsh hv
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm, ContinuousLinearMap.coe_coe] using
      CondP001cd_adjoin D H T F L hd h hh t hs ht ht0 hsh hv
  have hp : outerConverges (fun _ : ℕ => μ)
      (fun n ω => Real.sqrt (n+1 : ℕ) • (Fhat (n+1) ω - F)) ν := by
    intro f hf hb
    exact (hprocess f hf hb).comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun n : ℕ => Real.sqrt (n+1 : ℕ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hout := (hdelta E ℝ (fun _ : ℕ => Ω) (fun _ => μ) (fun _ => inferInstance)
    (D ∪ {F}) H F T L.toLinearMap hd' (fun n => Fhat (n+1))
    (fun n ω => Or.inl (hvalid (n+1) ω (Nat.zero_lt_succ n)))
    (fun n => Real.sqrt (n+1 : ℕ)) hr ν inferInstance htangent hp).1
  have hc := CondP001cd_outer_CD μ (fun n ω => Real.sqrt (n+1 : ℕ) *
      (T (Fhat (n+1) ω) - T F)) (ν.map L) hout
  intro x hx
  exact (tendsto_add_atTop_iff_nat 1).1 (hc x hx)

theorem functional_delta_nondegenerate_correction_supporting_conditional :
    AronowAudit.P001.functional_delta_nondegenerate_correction_supporting_conditional_statement := by
  unfold AronowAudit.P001.functional_delta_nondegenerate_correction_supporting_conditional_statement
  intro hdelta Ω E mΩ nE sE mE bE cE μ pμ D H F T L hd Fhat hmeas hvalid νB pν
    htangent hprocess v hv hgauss
  have hm : ∀ n : ℕ, Measurable (fun ω => Real.sqrt n • (Fhat n ω - F)) := by
    intro n
    exact measurable_const.smul ((hmeas n).sub_const F)
  have hp := CondP001cd_weak_outer μ (fun n ω => Real.sqrt n • (Fhat n ω - F))
    νB hm hprocess
  simpa only [hgauss] using
    CondP001cd_delta_outer hdelta μ D H F T L hd Fhat hvalid νB htangent hp

lemma CondP001cd_empirical_probability {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    IsProbabilityMeasure (empirical X n ω) := by
  constructor
  simp [empirical, Measure.smul_apply, hn.ne', ENNReal.inv_mul_cancel]

lemma CondP001cd_cdf_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hm : Measurable X) :
    cdf μ X = cdf (μ.map X) id := by
  funext t
  unfold cdf prob
  change (μ (X ⁻¹' Set.Iic t)).toReal = ((μ.map X) (Set.Iic t)).toReal
  rw [Measure.map_apply hm measurableSet_Iic]

lemma CondP001cd_cdf_domain (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    kolmogorovEmbed (cdf ν id) ∈ cdfDomain := by
  have he : (fun t => kolmogorovEmbed (cdf ν id) t) = ProbabilityTheory.cdf ν := by
    funext t
    rw [kolmogorov_embedding_preserves_cdf_supporting]
    simpa [AronowAudit.P001.cdf, AronowAudit.P001.prob, measureReal_def, Set.Iic_def] using
      (ProbabilityTheory.cdf_eq_real ν t).symm
  change IsRealCDF (fun t => kolmogorovEmbed (cdf ν id) t)
  rw [he]
  exact ⟨fun t => ⟨cdf_nonneg ν t, cdf_le_one ν t⟩, monotone_cdf ν,
    fun t => (ProbabilityTheory.cdf ν).right_continuous t,
    tendsto_cdf_atBot ν, tendsto_cdf_atTop ν⟩

theorem empirical_cdf_delta_nondegenerate_supporting_conditional :
    AronowAudit.P001.empirical_cdf_delta_nondegenerate_supporting_conditional_statement := by
  unfold AronowAudit.P001.empirical_cdf_delta_nondegenerate_supporting_conditional_statement
  intro hdelta Ω mΩ mK bK μ pμ X hiid T H L hd νB pν htangent hprocess v hv hgauss hstat
  have hvalid : ∀ n ω, 0 < n → empiricalCDFElement X n ω ∈ cdfDomain := by
    intro n ω hn
    have instEmpirical : IsProbabilityMeasure (empirical X n ω) :=
      CondP001cd_empirical_probability X hn ω
    exact CondP001cd_cdf_domain (empirical X n ω)
  have hp : outerConverges (fun _ : ℕ => μ) (fun n ω =>
      Real.sqrt n • (empiricalCDFElement X n ω - kolmogorovEmbed (cdf μ (X 0)))) νB := by
    intro f hf hb
    exact (hprocess f hf hb).1
  have hc := CondP001cd_delta_outer hdelta μ cdfDomain H (kolmogorovEmbed (cdf μ (X 0)))
    (fun f => T (fun x => f x)) L hd (empiricalCDFElement X) hvalid νB htangent hp
  rw [hgauss] at hc
  have hbase : (fun x => kolmogorovEmbed (cdf μ (X 0)) x) = cdf μ (X 0) := by
    rw [CondP001cd_cdf_law μ (X 0) (hiid.1 0)]
    exact funext (kolmogorov_embedding_preserves_cdf_supporting (μ.map (X 0)))
  intro x hx
  apply (hc x hx).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have he (ω : Ω) : (fun x => empiricalCDFElement X n ω x) = cdf (empirical X n ω) id := by
    have instEmpirical : IsProbabilityMeasure (empirical X n ω) :=
      CondP001cd_empirical_probability X hn ω
    exact funext (kolmogorov_embedding_preserves_cdf_supporting (empirical X n ω))
  simp only [he, hbase]

end AronowAudit.P001.Wave1
