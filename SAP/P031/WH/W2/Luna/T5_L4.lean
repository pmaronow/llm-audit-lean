import SAP.P031.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology BoundedContinuousFunction
open Filter Finset MeasureTheory ProbabilityTheory
open SAP.P031 SAP.P031.WH.W2

noncomputable section
namespace SAP.P031.WH.W2.Luna


private def legalAssignmentsW2 (Q : Population) : Finset (Finset (Fin Q.N)) :=
  (Finset.univ : Finset (Fin Q.N)).powersetCard Q.M

private abbrev LegalW2 (Q : Population) := ↥(legalAssignmentsW2 Q)

private def prefixW2 (Q : Population) : Finset (Fin Q.N) :=
  (Finset.univ : Finset (Fin Q.N)).filter (fun i => i.val < Q.M)

private theorem prefix_eq_map (Q : Population) :
    prefixW2 Q = (Finset.univ : Finset (Fin Q.M)).map
      (Fin.castLEEmb (populationSizesW2 Q).2.2.1) := by
  classical
  ext i
  constructor
  · intro hi
    have hlt : i.val < Q.M := (Finset.mem_filter.mp hi).2
    refine Finset.mem_map.mpr ⟨⟨i.val, hlt⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl
  · intro hi
    obtain ⟨j, _, hji⟩ := Finset.mem_map.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hval : i.val = j.val := (congrArg Fin.val hji).symm
    omega

private theorem prefix_card (Q : Population) : (prefixW2 Q).card = Q.M := by
  rw [prefix_eq_map]
  simp

private theorem legal_nonempty (Q : Population) : Nonempty (LegalW2 Q) := by
  classical
  let U := prefixW2 Q
  have hU : U ∈ legalAssignmentsW2 Q := by
    change U ∈ legalAssignmentsW2 Q
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.filter_subset _ _, prefix_card Q⟩
  exact ⟨⟨U, hU⟩⟩

private theorem finiteLaw_integral_expectation (Q : Population) (X : VarianceEstimator)
    [Nonempty (LegalW2 Q)] (f : BoundedContinuousFunction ℝ ℝ) :
    (∫ x, f x ∂(AronowAudit.MapTailB.PermutationArray.finiteLaw
      (fun a : LegalW2 Q => X Q a.val) : Measure ℝ)) =
      expectation Q.M (fun s => f (X Q s)) := by
  classical
  rw [AronowAudit.MapTailB.PermutationArray.integral_finiteLaw _ f.continuous]
  unfold AronowAudit.MapTailB.PermutationArray.average SAP.P031.expectation
  have hsum :
      (∑ a : LegalW2 Q, f (X Q a.val)) =
        ∑ s ∈ legalAssignmentsW2 Q, f (X Q s) := by
    exact Finset.sum_coe_sort (legalAssignmentsW2 Q) (fun s => f (X Q s))
  rw [hsum]
  have hcard : Fintype.card (LegalW2 Q) = (legalAssignmentsW2 Q).card := by
    simp only [LegalW2, Fintype.card_coe]
  rw [hcard]
  simp only [AronowAudit.MapTailB.PermutationArray.average, SAP.P031.expectation]
  field_simp
  unfold legalAssignmentsW2
  <;> ring

private def lawW2 (P : ℕ → Population) (X : VarianceEstimator) (n : ℕ) :
    ProbabilityMeasure ℝ := by
  letI : Nonempty (LegalW2 (P n)) := legal_nonempty (P n)
  exact
  AronowAudit.MapTailB.PermutationArray.finiteLaw
    (fun a : LegalW2 (P n) => X (P n) a.val)

theorem T5_L4_solution : T5_L4 := by
  classical
  intro P X hweak x
  let γ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hLaw : Tendsto (lawW2 P X) atTop (𝓝 γ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hI (n : ℕ) :
        (∫ x, f x ∂(lawW2 P X n : Measure ℝ)) =
          expectation (P n).M (fun s => f (X (P n) s)) := by
      letI : Nonempty (LegalW2 (P n)) := legal_nonempty (P n)
      simpa only [lawW2, ProbabilityMeasure.coe_mk] using
        finiteLaw_integral_expectation (P n) X f
    change Tendsto (fun n => ∫ x, f x ∂(lawW2 P X n : Measure ℝ)) atTop
      (𝓝 (∫ x, f x ∂gaussianReal 0 1))
    simpa only [← hI] using hweak f
  letI : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
  have hfront : (gaussianReal 0 1) (frontier (Set.Iic x)) = 0 := by
    rw [frontier_Iic]
    exact measure_singleton x
  have hmeasure := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hLaw hfront
  have hreal := (ENNReal.continuousAt_toReal (measure_ne_top (gaussianReal 0 1)
      (Set.Iic x))).tendsto.comp hmeasure
  have hevent (n : ℕ) :
      ((lawW2 P X n : Measure ℝ) (Set.Iic x)).toReal =
        eventProbability (P n) (fun s => X (P n) s ≤ x) := by
    -- The finite-law CDF is the cardinality of the same legal assignments
    -- appearing in the original expectation.
    classical
    let Q := P n
    letI : Nonempty (LegalW2 Q) := legal_nonempty Q
    letI : MeasurableSpace (LegalW2 Q) := ⊤
    letI : MeasurableSingletonClass (LegalW2 Q) := ⟨fun _ => trivial⟩
    let W : LegalW2 Q → ℝ := fun a => X Q a.val
    let E : Set (LegalW2 Q) := {a | W a ≤ x}
    have hlaw : ((lawW2 P X n : Measure ℝ) (Set.Iic x)) =
        (Fintype.card E : ENNReal) / Fintype.card (LegalW2 Q) := by
      change ((PMF.uniformOfFintype (LegalW2 Q)).map W).toMeasure (Set.Iic x) = _
      rw [PMF.toMeasure_map_apply (p := PMF.uniformOfFintype (LegalW2 Q))
        (f := W) (s := Set.Iic x) (measurable_of_finite W) measurableSet_Iic]
      rw [PMF.toMeasure_uniformOfFintype_apply (s := W ⁻¹' Set.Iic x)
        (measurableSet_preimage (measurable_of_finite W) measurableSet_Iic)]
      rfl
    have hcount :
        (∑ s ∈ legalAssignmentsW2 Q, if X Q s ≤ x then (1 : ℝ) else 0) =
          (Fintype.card E : ℝ) := by
      calc
        _ = ∑ a : LegalW2 Q, if W a ≤ x then (1 : ℝ) else 0 := by
          symm
          exact Finset.sum_coe_sort (legalAssignmentsW2 Q)
            (fun s => if X Q s ≤ x then (1 : ℝ) else 0)
        _ = _ := by
          change (∑ a ∈ (Finset.univ : Finset (LegalW2 Q)),
            if W a ≤ x then (1 : ℝ) else 0) = _
          rw [Finset.sum_boole]
          norm_cast
          simp [E, Fintype.card_subtype]
    have hcard : Fintype.card (LegalW2 Q) = (legalAssignmentsW2 Q).card := by
      simp only [LegalW2, Fintype.card_coe]
    rw [hlaw]
    change _ = expectation Q.M (fun s => if X Q s ≤ x then (1 : ℝ) else 0)
    unfold SAP.P031.expectation
    dsimp
    unfold legalAssignmentsW2 at hcount hcard ⊢
    rw [hcount]
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
    rw [← hcard]
  have hlimit : ((gaussianReal 0 1) (Set.Iic x)).toReal = normalCDF x := by
    rw [normalCDF, ProbabilityTheory.cdf_eq_real]
    rfl
  rw [← hlimit]
  apply hreal.congr'
  filter_upwards [] with n
  simpa only [Function.comp_apply] using hevent n

example : T5_L4 := T5_L4_solution

#print axioms T5_L4_solution

end SAP.P031.WH.W2.Luna
end
