import SAP.P015a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015a.WH.W1.P.T8_L2

open MeasureTheory ProbabilityTheory
open scoped Topology

theorem canonical_density_probability
    (ν : Measure ℝ) (f : ℝ → ℝ) (hf : Integrable f ν)
    (hn : (∫ y, f y ∂ν) = 1) (hnonneg : 0 ≤ᵐ[ν] f) :
    IsProbabilityMeasure (ν.withDensity fun y => ENNReal.ofReal (f y)) := by
  apply isProbabilityMeasure_iff.mpr
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hf hnonneg, hn]
  simp

theorem canonical_tilt
    (ν : Measure ℝ) (κ : ℝ → ℝ) (s : ℝ) (carrier : ℝ → ℝ)
    (I support : Set ℝ)
    (hfamily : SAP.P015a.ValidCanonicalFamily ν κ s carrier I support)
    (η t : ℝ) (hη : η ∈ I) (hshift : η + s * t ∈ I) :
    Integrable (fun y : ℝ => Real.exp (t * y))
        (SAP.P015a.canonicalResponseLaw ν κ s carrier η) ∧
      ProbabilityTheory.mgf (fun y : ℝ => y)
          (SAP.P015a.canonicalResponseLaw ν κ s carrier η) t =
        Real.exp ((κ (η + s * t) - κ η) / s) := by
  rcases hfamily with ⟨hs, hI, hsupport, hnull, hnorm⟩
  have hs0 : s ≠ 0 := ne_of_gt hs
  let q : ℝ → ℝ → ℝ := fun a y =>
    Real.exp (SAP.P015a.canonicalContribution κ s y (carrier y) a)
  let w : ℝ → ℝ → ENNReal := fun a y => ENNReal.ofReal (q a y)
  have hηdata := hnorm η hη
  have hshiftdata := hnorm (η + s * t) hshift
  have hqηnn : 0 ≤ᵐ[ν] q η := by
    filter_upwards [] with y
    exact (Real.exp_pos _).le
  have hprob : IsProbabilityMeasure (ν.withDensity (w η)) := by
    apply canonical_density_probability ν (q η) hηdata.1 hηdata.2 hqηnn
  have hwmeas : AEMeasurable (w η) ν := by
    exact hηdata.1.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hwfinite : ∀ᵐ y ∂ν, w η y < (⊤ : ENNReal) := by
    filter_upwards [] with y
    simp [w, q]
  have hpoint : ∀ y : ℝ,
      q η y * Real.exp (t * y) =
        Real.exp ((κ (η + s * t) - κ η) / s) * q (η + s * t) y := by
    intro y
    calc
      q η y * Real.exp (t * y) =
          Real.exp (SAP.P015a.canonicalContribution κ s y (carrier y) η + t * y) := by
            simp [q, Real.exp_add]
      _ = Real.exp ((κ (η + s * t) - κ η) / s +
            SAP.P015a.canonicalContribution κ s y (carrier y) (η + s * t)) := by
            congr 1
            unfold SAP.P015a.canonicalContribution
            field_simp
            ring
      _ = Real.exp ((κ (η + s * t) - κ η) / s) * q (η + s * t) y := by
            rw [Real.exp_add]
  have hprod : Integrable (fun y : ℝ => q η y * Real.exp (t * y)) ν := by
    rw [integrable_congr (Filter.Eventually.of_forall hpoint)]
    have hqshift : Integrable (q (η + s * t)) ν := by
      simpa [q] using hshiftdata.1
    exact hqshift.const_mul
      (Real.exp ((κ (η + s * t) - κ η) / s) : ℝ)
  have htrans :
      Integrable (fun y : ℝ => Real.exp (t * y)) (ν.withDensity (w η)) ↔
        Integrable (fun y : ℝ => (w η y).toReal • Real.exp (t * y)) ν :=
    integrable_withDensity_iff_integrable_smul₀' hwmeas hwfinite
  have htilt : Integrable (fun y : ℝ => Real.exp (t * y)) (ν.withDensity (w η)) := by
    apply htrans.mpr
    simpa only [w, q, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _)),
      smul_eq_mul] using hprod
  have hfun : (fun y : ℝ => (w η y).toReal • Real.exp (t * y)) =
      fun y => Real.exp ((κ (η + s * t) - κ η) / s) * q (η + s * t) y := by
    funext y
    simp only [w, q, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _)), smul_eq_mul]
    exact hpoint y
  have hint :
      (∫ y : ℝ, Real.exp (t * y) ∂ν.withDensity (w η)) =
        Real.exp ((κ (η + s * t) - κ η) / s) := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hwmeas hwfinite]
    rw [integral_congr_ae
      (Filter.Eventually.of_forall (fun y : ℝ => congrFun hfun y)), integral_const_mul]
    have hnormshift : (∫ y, q (η + s * t) y ∂ν) = 1 := by
      simpa [q] using hshiftdata.2
    rw [hnormshift]
    simp
  constructor
  · simpa [SAP.P015a.canonicalResponseLaw, w] using htilt
  · simpa [SAP.P015a.canonicalResponseLaw, w, ProbabilityTheory.mgf] using hint

end SAP.P015a.WH.W1.P.T8_L2

open MeasureTheory ProbabilityTheory

theorem SAP.P015a.WH.W1.T8_L2_proof : SAP.P015a.WH.W1.T8_L2 := by
  intro ν κ s carrier I support hfamily η hη
  rcases hfamily with ⟨hs, hI, hsupport, hnull, hnorm⟩
  have hηdata := hnorm η hη
  have hprob : IsProbabilityMeasure
      (SAP.P015a.canonicalResponseLaw ν κ s carrier η) := by
    unfold SAP.P015a.canonicalResponseLaw
    apply SAP.P015a.WH.W1.P.T8_L2.canonical_density_probability ν
      (fun y => Real.exp (SAP.P015a.canonicalContribution κ s y (carrier y) η))
      hηdata.1 hηdata.2
    filter_upwards [] with y
    exact (Real.exp_pos _).le
  have hcont : Continuous (fun t : ℝ => η + s * t) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hopen : IsOpen {t : ℝ | η + s * t ∈ I} := hI.preimage hcont
  have hsubset : {t : ℝ | η + s * t ∈ I} ⊆
      integrableExpSet (fun y : ℝ => y)
        (SAP.P015a.canonicalResponseLaw ν κ s carrier η) := by
    intro t ht
    have htilt := SAP.P015a.WH.W1.P.T8_L2.canonical_tilt ν κ s carrier I support
      ⟨hs, hI, hsupport, hnull, hnorm⟩ η t hη ht
    simpa [integrableExpSet] using htilt.1
  have hzero : (0 : ℝ) ∈ {t : ℝ | η + s * t ∈ I} := by simp [hη]
  have hinterior : (0 : ℝ) ∈ interior
      (integrableExpSet (fun y : ℝ => y)
        (SAP.P015a.canonicalResponseLaw ν κ s carrier η)) := by
    rw [mem_interior]
    exact ⟨{t : ℝ | η + s * t ∈ I}, hsubset, hopen, hzero⟩
  refine ⟨hprob, hinterior, ?_⟩
  intro t ht
  have htilt := SAP.P015a.WH.W1.P.T8_L2.canonical_tilt ν κ s carrier I support
    ⟨hs, hI, hsupport, hnull, hnorm⟩ η t hη ht
  simpa [SAP.P015a.canonicalResponseLaw] using htilt

