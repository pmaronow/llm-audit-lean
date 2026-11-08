import SAP.P001e.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology Classical

theorem SAP.P001e.WH.W1.T79_L1_proof : SAP.P001e.WH.W1.T79_L1 := by
  unfold SAP.P001e.WH.W1.T79_L1
  intro Ω _ μ _ K Y X hY hX y x H hH
  let B : Set (Fin K → ℝ) := W1orthant x
  let A : Set Ω := X ⁻¹' B
  let C : Set Ω := Y ⁻¹' Iic y
  let g : Ω → ℝ := fun ω => (condDistrib Y X μ (X ω)).real (Iic y)
  have hB : MeasurableSet B := by
    dsimp [B]
    simpa only [W1orthant, ofPred_forall] using
      (MeasurableSet.iInter (fun k : Fin K =>
        measurableSet_le (measurable_pi_apply k) (measurable_const (a := x k))))
  have hA : MeasurableSet A := hX hB
  have hC : MeasurableSet C := hY measurableSet_Iic
  have hversion : (fun ω => H (X ω)) =ᵐ[μ] g := by
    filter_upwards [ae_of_ae_map hX.aemeasurable hH] with ω hω
    simpa [g, probability, Measure.real_def] using hω
  have hg : Integrable g μ :=
    integrable_toReal_condDistrib hX.aemeasurable measurableSet_Iic
  let f : Ω → ℝ := fun ω => if ω ∈ A then H (X ω) else 0
  let gi : Ω → ℝ := A.indicator g
  have hfg : f =ᵐ[μ] gi := by
    filter_upwards [hversion] with ω hω
    by_cases hωA : ω ∈ A <;> simp [f, gi, hωA, hω]
  have hf : Integrable f μ := (hg.indicator hA).congr hfg.symm
  have hcond := condDistrib_ae_eq_condExp (μ := μ) (s := Iic y) hX hY measurableSet_Iic
  have hce :
      ∫ ω in A, g ω ∂μ =
        ∫ ω in A, (μ⟦C | MeasurableSpace.comap X inferInstance⟧) ω ∂μ := by
    apply setIntegral_congr_ae hA
    filter_upwards [hcond] with ω hω _
    simpa [g, C] using hω
  have hCI : Integrable (C.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hC
  have hce2 :
      ∫ ω in A, (μ⟦C | MeasurableSpace.comap X inferInstance⟧) ω ∂μ =
        ∫ ω in A, C.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ := by
    exact setIntegral_condExp hX.comap_le hCI ⟨B, hB, rfl⟩
  have hset :
      ∫ ω in A, C.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ = μ.real (A ∩ C) := by
    rw [setIntegral_indicator hC, setIntegral_const, smul_eq_mul, mul_one]
  have hEvent : A ∩ C = {ω | Y ω ≤ y ∧ X ω ∈ W1orthant x} := by
    ext ω
    simp [A, B, C, Set.mem_preimage, Set.mem_Iic, and_comm]
  have hIntegral : ∫ ω, f ω ∂μ = μ.real {ω | Y ω ≤ y ∧ X ω ∈ W1orthant x} := by
    calc
      ∫ ω, f ω ∂μ = ∫ ω, gi ω ∂μ := integral_congr_ae hfg
      _ = ∫ ω in A, g ω ∂μ := by simp [gi, integral_indicator hA]
      _ = ∫ ω in A, (μ⟦C | MeasurableSpace.comap X inferInstance⟧) ω ∂μ := hce
      _ = ∫ ω in A, C.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ := hce2
      _ = μ.real (A ∩ C) := hset
      _ = μ.real {ω | Y ω ≤ y ∧ X ω ∈ W1orthant x} := by rw [hEvent]
  have hF : f = (fun ω => if X ω ∈ W1orthant x then H (X ω) else 0) := by
    funext ω
    simp [f, A, B]
  refine ⟨?_, ?_⟩
  · exact hf.congr (Eventually.of_forall fun ω => congrFun hF ω)
  · change probability μ {ω | Y ω ≤ y ∧ X ω ∈ W1orthant x} = ∫ ω, f ω ∂μ
    change μ.real {ω | Y ω ≤ y ∧ X ω ∈ W1orthant x} = ∫ ω, f ω ∂μ
    exact hIntegral.symm
