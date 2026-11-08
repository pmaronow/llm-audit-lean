import SAP.P001e.Defs.WholeW3

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical

namespace SAP.P001e.WH.W3

noncomputable section

/-- Coordinatewise almost-sure constancy implies conditional independence of
the whole cylinder process and any measurable treatment, given a constant
covariate. Start with `ProbabilityTheory.indepFun_const_left` and apply
`ProbabilityTheory.IndepFun.process_congr_left` to the coordinatewise changes.
Measurable coordinates make the process measurable. Convert independence to
the event definition of conditional independence using
`MeasurableSpace.comap_const`, `MeasureTheory.condExp_bot`, indicator integrals,
and `ProbabilityTheory.IndepFun.measure_inter_preimage_eq_mul`. No common null
set over the uncountable coordinate index is needed. Expected: 60--100 lines.
This is a new refutation obligation, distinct from the retired V2 leaves. -/
def T91_L3V2 : Prop :=
  ∀ {Ω I : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : I → Ω → ℝ) (c : I → ℝ) (D : Ω → ℝ),
    (∀ t, Measurable (Y t)) → Measurable D →
    (∀ t, Y t =ᵐ[μ] (fun _ => c t)) →
    CondIndependent μ (fun _ : Ω => ()) measurable_const (fun ω t => Y t ω) D

/-- Assemble the bounded Borel counterexample. Only full cylinder-process
independence is delegated; all regularity, support, observed-law and numerical
counterexample facts are proved here. -/
theorem T91_assembly (h3 : T91_L3V2) : T91WholeStatement := by
  classical
  have : IsProbabilityMeasure T91UniformDoseLaw := ⟨by
    norm_num [T91UniformDoseLaw, Real.volume_Icc]⟩
  have : NullSingletonClass T91UniformDoseLaw := by
    unfold T91UniformDoseLaw
    infer_instance
  have hdiag_ae (t : ℝ) :
      T91DiagonalPotential t =ᵐ[T91UniformDoseLaw] (fun _ => t) := by
    filter_upwards [T91UniformDoseLaw.ae_ne t] with ω hω
    simp [T91DiagonalPotential, hω]
  have hzero_obs : T91ObservedOutcome T91ZeroPotential = (fun _ => 0) := rfl
  have hdiag_obs : T91ObservedOutcome T91DiagonalPotential = (fun _ => 0) := by
    funext ω
    simp [T91ObservedOutcome, T91DiagonalPotential]
  have hregular (Y : ℝ → ℝ → ℝ) (m : ℝ → ℝ)
      (hY : ∀ t, Measurable (Y t))
      (hj : Measurable (fun z : ℝ × ℝ => Y z.1 z.2))
      (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ω, Y t ω ∈ Icc (0 : ℝ) 1)
      (hae : ∀ t, Y t =ᵐ[T91UniformDoseLaw] (fun _ => m t))
      (ho : T91ObservedOutcome Y = (fun _ => 0)) (hm : Continuous m) :
      T91RegularProcess Y m := by
    have hi (t : ℝ) : Integrable (Y t) T91UniformDoseLaw :=
      (integrable_const (m t)).congr (hae t).symm
    refine ⟨(fun t => ⟨hY t, hi t⟩), hj, ?_, hb,
      Measurable.of_eval (fun t => hY t), ?_, ?_, ?_, ?_, hm⟩
    · intro ω
      exact hj.comp (measurable_id.prodMk measurable_const)
    · exact h3 T91UniformDoseLaw
        (fun t : Icc (0 : ℝ) 1 => Y t) (fun t => m t)
        (id : ℝ → ℝ) (fun t => hY t) measurable_id (fun t => hae t)
    · rw [ho]
      exact measurable_const
    · rw [ho]
      exact integrable_const 0
    · intro t
      constructor
      · calc
          expectation T91UniformDoseLaw (Y t) =
              expectation T91UniformDoseLaw (fun _ => m t) := integral_congr_ae (hae t)
          _ = m t := by simp [expectation]
      · refine ⟨measurable_const, hi t, integrable_const (m t), ?_⟩
        intro A _hA
        exact integral_congr_ae (ae_restrict_of_ae (hae t))
  have hA : T91RegularProcess T91ZeroPotential (fun _ => 0) := by
    apply hregular T91ZeroPotential (fun _ => 0) (fun _ => measurable_const) measurable_const
      (fun _ _ _ => by norm_num [T91ZeroPotential])
      (fun _ => Filter.EventuallyEq.rfl) hzero_obs continuous_const
  have hB : T91RegularProcess T91DiagonalPotential (id : ℝ → ℝ) := by
    apply hregular _ _ _ _ _ hdiag_ae hdiag_obs continuous_id
    · intro t
      exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
        measurable_const measurable_const
    · exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_fst)
        measurable_const measurable_fst
    · intro t ht ω
      unfold T91DiagonalPotential
      split_ifs
      · norm_num
      · exact ht
  have hobservedCE (Y : ℝ → ℝ → ℝ)
      (ho : T91ObservedOutcome Y = (fun _ => 0)) :
      IsConditionalMean T91UniformDoseLaw (fun ω => (ω, T91DiscreteCovariate ω))
        (T91ObservedOutcome Y) (fun _ => 0) := by
    rw [ho]
    exact ⟨measurable_const, integrable_const 0, integrable_const 0, fun _ _ => rfl⟩
  have hcellCE : IsConditionalMean
      (T91UniformDoseLaw.restrict {ω | T91DiscreteCovariate ω = ()})
      (id : ℝ → ℝ) (T91ObservedOutcome T91DiagonalPotential) (T91ObservedDoseVersion ()) := by
    simp only [T91DiscreteCovariate, Set.ofPred_true, Measure.restrict_univ, hdiag_obs]
    exact ⟨measurable_const, integrable_const 0, integrable_const 0, fun _ _ => rfl⟩
  have hsupport (d : ℝ) (hd : d ∈ Ioo (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
      0 < probability T91UniformDoseLaw (Metric.ball d ε) := by
    have hp : 0 < volume (Metric.ball d ε ∩ Ioo (0 : ℝ) 1) :=
      IsOpen.measure_pos volume (Metric.isOpen_ball.inter isOpen_Ioo)
        ⟨d, Metric.mem_ball_self hε, hd⟩
    have hl : volume (Metric.ball d ε ∩ Ioo (0 : ℝ) 1) ≤
        T91UniformDoseLaw (Metric.ball d ε) := by
      rw [T91UniformDoseLaw, Measure.restrict_apply Metric.isOpen_ball.measurableSet]
      exact measure_mono (inter_subset_inter_right _ Ioo_subset_Icc_self)
    exact ENNReal.toReal_pos (lt_of_lt_of_le hp hl).ne'
      (measure_ne_top T91UniformDoseLaw _)
  have hmeanB (t : ℝ) : expectation T91UniformDoseLaw (T91DiagonalPotential t) = t := by
    calc
      expectation T91UniformDoseLaw (T91DiagonalPotential t) =
          expectation T91UniformDoseLaw (fun _ => t) := integral_congr_ae (hdiag_ae t)
      _ = t := by simp [expectation]
  have heffectB : expectation T91UniformDoseLaw
      (fun ω => T91DiagonalPotential (3 / 4) ω - T91DiagonalPotential (1 / 4) ω) =
      1 / 2 := by
    unfold expectation
    rw [integral_sub (hB.1 (3 / 4)).2 (hB.1 (1 / 4)).2]
    change expectation T91UniformDoseLaw (T91DiagonalPotential (3 / 4)) -
      expectation T91UniformDoseLaw (T91DiagonalPotential (1 / 4)) = 1 / 2
    rw [hmeanB, hmeanB]
    norm_num
  have hcontrast : T91ObservedContrast = 0 := by
    simp [T91ObservedContrast, T91ObservedDoseVersion]
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    measurable_id, measurable_const, ?_, ?_, ?_, hA, hB, ?_, ?_,
    hobservedCE _ hzero_obs, hobservedCE _ hdiag_obs, hcellCE, continuous_const,
    hsupport, ?_, (hA.1 _).2.sub (hA.1 _).2, (hB.1 _).2.sub (hB.1 _).2,
    ?_, heffectB, hcontrast, ?_, ?_⟩
  · simp [probability, T91DiscreteCovariate]
  · norm_num [T91UniformDoseLaw, Measure.restrict_apply measurableSet_Icc, Real.volume_Icc]
  · exact ae_restrict_mem measurableSet_Icc
  · intro ω
    simp only [hzero_obs, hdiag_obs, and_self]
  · simp only [hzero_obs, hdiag_obs]
  · norm_num [Set.mem_Ioo]
  · simp [expectation, T91ZeroPotential]
  · rw [heffectB, hcontrast]
    norm_num
  · intro hae
    have he : ∀ᵐ t ∂T91UniformDoseLaw, t = 0 := by
      simpa only [Measure.map_id, hmeanB, Filter.EventuallyEq, T91ObservedDoseVersion] using hae
    obtain ⟨t, ht, hnt⟩ := (he.and (T91UniformDoseLaw.ae_ne 0)).exists
    exact hnt ht

end
end SAP.P001e.WH.W3
