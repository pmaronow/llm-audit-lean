import SAP.P029b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W2.P.T19_L3

open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set


open SAP.P029b.WH.W2

theorem uniformInterval_probability (r : ℝ) (hr : r = 1 ∨ r = 2) :
    IsProbabilityMeasure (uniformIntervalW2 r) := by
  unfold uniformIntervalW2
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · intro h
    rw [Real.volume_Ioo] at h
    rcases hr with hr | hr <;> rw [hr] at h <;> norm_num at h
  · rw [Real.volume_Ioo]
    rcases hr with hr | hr <;> rw [hr] <;> norm_num

theorem coordinate_probability (Λ : Measure ℝ) (hΛ : IsProbabilityMeasure Λ)
    (k : ℕ) (wrong : Bool) (j : SimCoordinateW2 k) :
    IsProbabilityMeasure (simCoordinateLawW2 Λ k wrong j) := by
  cases j with
  | inl c => exact uniformInterval_probability 2 (by norm_num)
  | inr p =>
    rcases p with ⟨i, t⟩
    by_cases h3 : t.val < 3
    · simpa [simCoordinateLawW2, h3] using
        uniformInterval_probability 1 (by norm_num)
    · by_cases h5 : t.val < 5
      · cases wrong
        · simpa [simCoordinateLawW2, h3, h5] using
            (inferInstance : IsProbabilityMeasure (gaussianReal 0 9))
        · simpa [simCoordinateLawW2, h3, h5] using hΛ
      · simpa [simCoordinateLawW2, h3, h5] using
          (inferInstance : IsProbabilityMeasure (gaussianReal 0 1))

end SAP.P029b.WH.W2.P.T19_L3

open SAP.P029b.WH.W2
open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

theorem SAP.P029b.WH.W2.T19_L3_proof : SAP.P029b.WH.W2.T19_L3 := by
  intro Λ hΛ k hB wrong
  letI : ∀ j : SimCoordinateW2 k,
      IsProbabilityMeasure (simCoordinateLawW2 Λ k wrong j) :=
    SAP.P029b.WH.W2.P.T19_L3.coordinate_probability Λ hΛ k wrong
  letI : IsProbabilityMeasure (Measure.pi (simCoordinateLawW2 Λ k wrong)) := inferInstance
  letI : IsProbabilityMeasure (balancedLawW2 k) := hB
  letI : IsProbabilityMeasure (simLawW2 Λ k wrong) := by
    dsimp [simLawW2]
    infer_instance
  have hmargin : ∀ j : SimCoordinateW2 k,
      Measure.map (fun ω : SimSpaceW2 k => ω.1 j)
        (simLawW2 Λ k wrong) = simCoordinateLawW2 Λ k wrong j := by
    intro j
    calc
      Measure.map (fun ω : SimSpaceW2 k => ω.1 j) (simLawW2 Λ k wrong) =
          (Measure.map Prod.fst (simLawW2 Λ k wrong)).map (fun r : SimCoordinateW2 k → ℝ => r j) := by
        simpa only [Function.comp_def] using
          (Measure.map_map (measurable_pi_apply j) measurable_fst
            (μ := simLawW2 Λ k wrong)).symm
      _ = (Measure.pi (simCoordinateLawW2 Λ k wrong)).map
            (fun r : SimCoordinateW2 k → ℝ => r j) := by
        simp [simLawW2]
      _ = simCoordinateLawW2 Λ k wrong j := by
        rw [Measure.pi_map_eval]
        simp
  have hind : iIndepFun (fun j (ω : SimSpaceW2 k) => ω.1 j)
      (simLawW2 Λ k wrong) := by
    apply (iIndepFun_iff_map_fun_eq_pi_map
      (f := fun j (ω : SimSpaceW2 k) => ω.1 j)
      (μ := simLawW2 Λ k wrong)
      (fun j => (measurable_pi_apply j).comp measurable_fst |>.aemeasurable)).2
    calc
      Measure.map (fun ω : SimSpaceW2 k => fun j => ω.1 j)
          (simLawW2 Λ k wrong) = Measure.pi (simCoordinateLawW2 Λ k wrong) := by
        simp [simLawW2]
      _ = Measure.pi (fun j =>
          Measure.map (fun ω : SimSpaceW2 k => ω.1 j) (simLawW2 Λ k wrong)) := by
        congr 1
        funext j
        exact (hmargin j).symm
  refine ⟨inferInstance, hind, hmargin, ?_, ?_⟩
  · simpa [simLawW2] using
      (indepFun_prod (μ := Measure.pi (simCoordinateLawW2 Λ k wrong))
        (ν := balancedLawW2 k) (X := id) (Y := id)
        measurable_id measurable_id).symm
  · simp [simLawW2]
