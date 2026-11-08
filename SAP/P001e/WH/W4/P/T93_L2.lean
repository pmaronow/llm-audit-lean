import SAP.P001e.WH.W4.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Classical

universe u v
noncomputable section

theorem SAP.P001e.WH.W4.T93_L2_proof : SAP.P001e.WH.W4.T93_L2 := by
  intro Ω E _ _ μ hμ X D Y hX hD hbinary p hp hpos m hm d hd
  let arm : Set Ω := {ω | D ω = d}
  let xset (A : Set E) : Set Ω := X ⁻¹' A
  have harm : MeasurableSet arm := by
    exact (hD (measurableSet_singleton d))
  have hcompMeas : Measurable (fun x : E => m (d, x)) := by
    exact hm.1.comp (measurable_const.prodMk measurable_id)
  have hrestrictedComp :
      Integrable (fun ω => m (d, X ω)) (μ.restrict arm) := by
    have hbase : Integrable (fun ω => m (D ω, X ω)) (μ.restrict arm) :=
      hm.2.2.1.mono_measure Measure.restrict_le_self
    have heq : (fun ω => m (d, X ω)) =ᵐ[μ.restrict arm]
        (fun ω => m (D ω, X ω)) := by
      filter_upwards [ae_restrict_mem harm] with ω hω
      simp [arm] at hω
      simp [hω]
    exact hbase.congr heq.symm
  have hrestricted :
      IsConditionalMean (μ.restrict arm) X Y (fun x => m (d, x)) := by
    refine ⟨hcompMeas, hm.2.1.mono_measure Measure.restrict_le_self,
      hrestrictedComp, ?_⟩
    intro A hA
    let B : Set (ℝ × E) := {z | z.1 = d ∧ z.2 ∈ A}
    have hB : MeasurableSet B :=
      (measurableSet_singleton d).prod hA
    have hpre : (fun ω => (D ω, X ω)) ⁻¹' B = arm ∩ xset A := by
      ext ω
      simp [B, arm, xset]
    have hjoint := hm.2.2.2 B hB
    rw [hpre] at hjoint
    have hsetId :
        (∫ ω in xset A, Y ω ∂ μ.restrict arm) =
          ∫ ω in xset A ∩ arm, Y ω ∂ μ := by
      rw [Measure.restrict_restrict (hX hA)]
    have hsetId' (f : Ω → ℝ) :
        (∫ ω in xset A, f ω ∂ μ.restrict arm) =
          ∫ ω in arm ∩ xset A, f ω ∂ μ := by
      rw [Measure.restrict_restrict (hX hA), inter_comm]
    calc
      (∫ ω in xset A, Y ω ∂ μ.restrict arm)
          = ∫ ω in arm ∩ xset A, Y ω ∂ μ := hsetId' Y
      _ = ∫ ω in (fun ω => (D ω, X ω)) ⁻¹' B, Y ω ∂ μ := by
        rw [hpre]
      _ = ∫ ω in arm ∩ xset A, m (D ω, X ω) ∂ μ := hjoint
      _ = ∫ ω in arm ∩ xset A, m (d, X ω) ∂ μ := by
        apply setIntegral_congr_fun (harm.inter (hX hA))
        intro ω hω
        have hDω : D ω = d := hω.1
        exact congrArg (fun z : ℝ => m (z, X ω)) hDω
      _ = ∫ ω in xset A, m (d, X ω) ∂ μ.restrict arm := by
        symm
        exact hsetId' (fun ω => m (d, X ω))

  obtain ⟨η, hη, hηp⟩ := hpos
  let c : ℝ≥0∞ := ENNReal.ofReal η
  let lam : Measure E := μ.map X
  let ν : Measure E := (μ.restrict arm).map X
  have hc0 : c ≠ 0 := by
    exact ne_of_gt (by simpa [c] using ENNReal.ofReal_pos.mpr hη)
  have hcTop : c ≠ ∞ := by simp [c]
  have hdom : c • lam ≤ ν := by
    apply Measure.le_iff.2
    intro A hA
    have hXA : MeasurableSet (xset A) := hX hA
    have hbaseMass :
        (μ.real (xset A)) * η ≤ (μ.real (arm ∩ xset A)) := by
      have hbinRestr : ∀ᵐ ω ∂ μ.restrict (xset A),
          D ω = 0 ∨ D ω = 1 :=
        hbinary.filter_mono (ae_mono Measure.restrict_le_self)
      have hboundP : ∀ᵐ ω ∂ μ.restrict (xset A),
          η ≤ p (X ω) := by
        filter_upwards [hηp.filter_mono (ae_mono Measure.restrict_le_self)] with ω hω
        exact le_of_lt hω.1
      have hboundP0 : ∀ᵐ ω ∂ μ.restrict (xset A),
          η ≤ 1 - p (X ω) := by
        filter_upwards [hηp.filter_mono (ae_mono Measure.restrict_le_self)] with ω hω
        linarith [hω.2]
      have hpIdentity := hp.2.2.2 A hA
      have hbound1 :
          (μ.real (xset A)) * η ≤ ∫ ω in xset A, p (X ω) ∂ μ := by
        have hmconst : Integrable (fun _ : Ω => η) (μ.restrict (xset A)) :=
          integrable_const η
        have hmp : Integrable (fun ω => p (X ω)) (μ.restrict (xset A)) :=
          hp.2.2.1.mono_measure Measure.restrict_le_self
        have hle := integral_mono_ae hmconst hmp hboundP
        simpa [setIntegral_const, smul_eq_mul] using hle
      have hbound0 :
          (μ.real (xset A)) * η ≤ ∫ ω in xset A, (1 - p (X ω)) ∂ μ := by
        have hmconst : Integrable (fun _ : Ω => η) (μ.restrict (xset A)) :=
          integrable_const η
        have hpcomp : Integrable (fun ω => p (X ω)) μ := hp.2.2.1
        have hcomp : Integrable (fun ω => 1 - p (X ω)) μ :=
          (integrable_const (1 : ℝ)).sub hpcomp
        have hmcomp : Integrable (fun ω => 1 - p (X ω)) (μ.restrict (xset A)) :=
          hcomp.mono_measure Measure.restrict_le_self
        have hle := integral_mono_ae hmconst hmcomp hboundP0
        simpa [setIntegral_const, smul_eq_mul] using hle
      rcases hd with hd0 | hd1
      · subst d
        have hselected :
            μ.real (arm ∩ xset A) = ∫ ω in xset A, (1 - D ω) ∂ μ := by
          have hindicator :
              (∫ ω in xset A, (if D ω = 0 then (1 : ℝ) else 0) ∂ μ) =
                μ.real (arm ∩ xset A) := by
            calc
              _ = ∫ ω, (xset A).indicator
                  (fun ω => if D ω = 0 then (1 : ℝ) else 0) ω ∂ μ := by
                    rw [← integral_indicator hXA]
              _ = ∫ ω, (arm ∩ xset A).indicator (fun _ => (1 : ℝ)) ω ∂ μ := by
                    congr 1
                    funext ω
                    by_cases hx : ω ∈ xset A <;> by_cases hdω : D ω = 0 <;>
                      simp [arm, xset, hx, hdω]
              _ = μ.real (arm ∩ xset A) :=
                    integral_indicator_one (μ := μ) (s := arm ∩ xset A)
                      (harm.inter hXA)
          calc
            μ.real (arm ∩ xset A) =
                ∫ ω in xset A, (if D ω = 0 then (1 : ℝ) else 0) ∂ μ :=
                  hindicator.symm
            _ = ∫ ω in xset A, (1 - D ω) ∂ μ := by
              apply integral_congr_ae
              filter_upwards [hbinRestr] with ω hω
              rcases hω with hzero | hone
              · simp [hzero]
              · simp [hone]
        rw [hselected]
        have hcompl :
            (∫ ω in xset A, 1 - D ω ∂ μ) =
              ∫ ω in xset A, 1 - p (X ω) ∂ μ := by
          calc
            _ = (∫ ω in xset A, (1 : ℝ) ∂ μ) -
                ∫ ω in xset A, D ω ∂ μ := by
              rw [integral_sub (integrable_const (1 : ℝ)).integrableOn
                hp.2.1.integrableOn]
            _ = (∫ ω in xset A, (1 : ℝ) ∂ μ) -
                ∫ ω in xset A, p (X ω) ∂ μ := by rw [hpIdentity]
            _ = ∫ ω in xset A, 1 - p (X ω) ∂ μ := by
              symm
              exact integral_sub (integrable_const (1 : ℝ)).integrableOn
                hp.2.2.1.integrableOn
        rw [hcompl]
        exact hbound0
      · subst d
        have hselected :
            μ.real (arm ∩ xset A) = ∫ ω in xset A, D ω ∂ μ := by
          have hindicator :
              (∫ ω in xset A, (if D ω = 1 then (1 : ℝ) else 0) ∂ μ) =
                μ.real (arm ∩ xset A) := by
            calc
              _ = ∫ ω, (xset A).indicator
                  (fun ω => if D ω = 1 then (1 : ℝ) else 0) ω ∂ μ := by
                    rw [← integral_indicator hXA]
              _ = ∫ ω, (arm ∩ xset A).indicator (fun _ => (1 : ℝ)) ω ∂ μ := by
                    congr 1
                    funext ω
                    by_cases hx : ω ∈ xset A <;> by_cases hdω : D ω = 1 <;>
                      simp [arm, xset, hx, hdω]
              _ = μ.real (arm ∩ xset A) :=
                    integral_indicator_one (μ := μ) (s := arm ∩ xset A)
                      (harm.inter hXA)
          calc
            μ.real (arm ∩ xset A) =
                ∫ ω in xset A, (if D ω = 1 then (1 : ℝ) else 0) ∂ μ :=
                  hindicator.symm
            _ = ∫ ω in xset A, D ω ∂ μ := by
              apply integral_congr_ae
              filter_upwards [hbinRestr] with ω hω
              rcases hω with hzero | hone
              · simp [hzero]
              · simp [hone]
        rw [hselected, hpIdentity]
        exact hbound1
    calc
      c * lam A = ENNReal.ofReal ((μ.real (xset A)) * η) := by
        simp [c, lam, xset, Measure.map_apply hX hA,
          measureReal_def, measure_ne_top]
        exact mul_comm _ _
      _ ≤ ENNReal.ofReal (μ.real (arm ∩ xset A)) :=
        ENNReal.ofReal_le_ofReal hbaseMass
      _ = ν A := by
        calc
          ENNReal.ofReal (μ.real (arm ∩ xset A)) = μ (arm ∩ xset A) := by
            simp [measureReal_def, measure_ne_top]
          _ = (μ.restrict arm) (xset A) := by
            rw [Measure.restrict_apply hXA, inter_comm]
          _ = ν A := by
            simp [ν, xset, Measure.map_apply hX hA]

  have hmeanNu : Integrable (fun x => m (d, x)) ν := by
    apply (integrable_map_measure hcompMeas.aestronglyMeasurable
      hX.aemeasurable).mpr
    exact hrestricted.2.2.1
  have hmeanScaled : Integrable (fun x => m (d, x)) (c • lam) :=
    hmeanNu.mono_measure hdom
  have hmeanLambda : Integrable (fun x => m (d, x)) lam :=
    (integrable_smul_measure hc0 hcTop).mp hmeanScaled
  have hpopulation : Integrable (fun ω => m (d, X ω)) μ := by
    exact (integrable_map_measure hcompMeas.aestronglyMeasurable
      hX.aemeasurable).mp hmeanLambda
  exact ⟨hrestricted, hpopulation⟩

end
