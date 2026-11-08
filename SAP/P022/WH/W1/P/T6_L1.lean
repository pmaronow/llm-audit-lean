import SAP.P022.WH.W1.Leaves
import AronowAudit.P022.Wave1.Lib.TailA.AtomEndpoints

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T6_L1

open SAP.P022 SAP.P022.WH.W1 Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology ENNReal NNReal
noncomputable section

private abbrev empiricalLaw {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ) :
    ProbabilityMeasure ℝ :=
  AronowAudit.P022.Wave1.TailA.atom_empiricalLaw hN y

private abbrev marginalLaw (H : JointLaw) (t : Bool) : ProbabilityMeasure ℝ :=
  AronowAudit.P022.Wave1.TailA.atom_marginalLaw H t

private theorem empiricalCDF_eq_cdf {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ) :
    empiricalCDF y = fun x => cdf (empiricalLaw hN y : Measure ℝ) x := by
  funext x
  rw [cdf_eq_real]
  calc
    empiricalCDF y x = AronowAudit.P022.empiricalCDF y x := by
      rw [SAP.P022.Bridge.empiricalCDF_eq]
    _ = (empiricalLaw hN y : Measure ℝ).real (Iic x) :=
      (AronowAudit.P022.Wave1.TailA.atom_empirical_Iic hN y x).symm

private theorem lawCDF_eq_cdf (H : JointLaw) (t : Bool) :
    lawCDF H t = fun x => cdf (marginalLaw H t : Measure ℝ) x := by
  funext x
  rw [cdf_eq_real]
  calc
    lawCDF H t x = AronowAudit.P022.lawCDF H t x := by
      rw [SAP.P022.Bridge.lawCDF_eq]
    _ = (marginalLaw H t : Measure ℝ).real (Iic x) :=
      (AronowAudit.P022.Wave1.TailA.atom_marginal_Iic H t x).symm

private theorem cdf_leftLim_eq_measureReal (μ : ProbabilityMeasure ℝ) (x : ℝ) :
    Function.leftLim (fun z => cdf (μ : Measure ℝ) z) x =
      (μ : Measure ℝ).real (Iio x) := by
  have hmono : Monotone (fun z => cdf (μ : Measure ℝ) z) := monotone_cdf _
  have hlim := hmono.tendsto_leftLim x
  have hnonneg : 0 ≤ Function.leftLim (fun z => cdf (μ : Measure ℝ) z) x :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Eventually.of_forall (fun z => cdf_nonneg (μ : Measure ℝ) z))
  have hmeasure := StieltjesFunction.measure_Iio (cdf (μ : Measure ℝ))
    (tendsto_cdf_atBot (μ : Measure ℝ)) x
  rw [ProbabilityTheory.measure_cdf] at hmeasure
  have hreal := congrArg ENNReal.toReal hmeasure
  rw [sub_zero, ENNReal.toReal_ofReal hnonneg] at hreal
  rw [measureReal_def]
  exact hreal.symm

private theorem empirical_leftLim_eq {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ) (x : ℝ) :
    Function.leftLim (empiricalCDF y) x = empiricalLeftCDF y x := by
  have hcdf := empiricalCDF_eq_cdf hN y
  have hleft := cdf_leftLim_eq_measureReal (empiricalLaw hN y) x
  calc
    Function.leftLim (empiricalCDF y) x =
        Function.leftLim (fun z => cdf (empiricalLaw hN y : Measure ℝ) z) x := by
          exact congrArg (fun f : ℝ → ℝ => Function.leftLim f x) hcdf
    _ = (empiricalLaw hN y : Measure ℝ).real (Iio x) := hleft
    _ = AronowAudit.P022.empiricalLeftCDF y x :=
      AronowAudit.P022.Wave1.TailA.atom_empirical_Iio hN y x
    _ = empiricalLeftCDF y x := by rw [SAP.P022.Bridge.empiricalLeftCDF_eq]

private theorem law_leftLim_eq (H : JointLaw) (t : Bool) (x : ℝ) :
    Function.leftLim (lawCDF H t) x = lawLeftCDF H t x := by
  have hcdf := lawCDF_eq_cdf H t
  have hleft := cdf_leftLim_eq_measureReal (marginalLaw H t) x
  calc
    Function.leftLim (lawCDF H t) x =
        Function.leftLim (fun z => cdf (marginalLaw H t : Measure ℝ) z) x := by
          exact congrArg (fun f : ℝ → ℝ => Function.leftLim f x) hcdf
    _ = (marginalLaw H t : Measure ℝ).real (Iio x) := hleft
    _ = AronowAudit.P022.lawLeftCDF H t x :=
      AronowAudit.P022.Wave1.TailA.atom_marginal_Iio H t x
    _ = lawLeftCDF H t x := by rw [SAP.P022.Bridge.lawLeftCDF_eq]

private theorem cdfDistance_point_le (A B : ℝ → ℝ)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ 1) (hB : ∀ x, 0 ≤ B x ∧ B x ≤ 1) (x : ℝ) :
    |A x - B x| ≤ cdfDistance A B := by
  change |A x - B x| ≤ sSup (Set.range (fun z => |A z - B z|))
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro r ⟨z, rfl⟩
    have ha := hA z
    have hb := hB z
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact Set.mem_range_self x

private theorem leftCDF_distance_le (S : ExperimentSequence) (H : JointLaw)
    (t : Bool) (q : ℕ) (x : ℝ) :
    |empiricalLeftCDF (rowOutcomes S t q) x - lawLeftCDF H t x| ≤
      cdfDistance (lawCDF H t) (empiricalCDF (rowOutcomes S t q)) := by
  let y := rowOutcomes S t q
  have hN : 0 < (S.design q).N := by have h := (S.design q).population_min; omega
  have hycdf := empiricalCDF_eq_cdf hN y
  have hfcdf := lawCDF_eq_cdf H t
  have hF : ∀ z, 0 ≤ lawCDF H t z ∧ lawCDF H t z ≤ 1 := by
    intro z
    rw [hfcdf]
    exact ⟨cdf_nonneg _ z, cdf_le_one _ z⟩
  have hG : ∀ z, 0 ≤ empiricalCDF y z ∧ empiricalCDF y z ≤ 1 := by
    intro z
    rw [hycdf]
    exact ⟨cdf_nonneg _ z, cdf_le_one _ z⟩
  have hpt : ∀ z, |lawCDF H t z - empiricalCDF y z| ≤
      cdfDistance (lawCDF H t) (empiricalCDF y) := by
    intro z
    exact cdfDistance_point_le _ _ hF hG z
  let d := cdfDistance (lawCDF H t) (empiricalCDF y)
  have hmonoF : Monotone (lawCDF H t) := by
    rw [hfcdf]
    exact monotone_cdf _
  have hmonoG : Monotone (empiricalCDF y) := by
    rw [hycdf]
    exact monotone_cdf _
  have hupper : Function.leftLim (empiricalCDF y) x ≤ Function.leftLim (lawCDF H t) x + d := by
    apply le_of_tendsto_of_tendsto (hmonoG.tendsto_leftLim x)
      ((hmonoF.tendsto_leftLim x).add_const d)
    filter_upwards [] with z
    have hz := abs_le.mp (hpt z)
    dsimp [d]
    linarith
  have hlower : Function.leftLim (lawCDF H t) x ≤ Function.leftLim (empiricalCDF y) x + d := by
    apply le_of_tendsto_of_tendsto (hmonoF.tendsto_leftLim x)
      ((hmonoG.tendsto_leftLim x).add_const d)
    filter_upwards [] with z
    have hz := abs_le.mp (hpt z)
    dsimp [d]
    linarith
  change |empiricalLeftCDF y x - lawLeftCDF H t x| ≤
    cdfDistance (lawCDF H t) (empiricalCDF y)
  have hu' := hupper
  rw [empirical_leftLim_eq hN y x, law_leftLim_eq H t x] at hu'
  have hl' := hlower
  rw [law_leftLim_eq H t x, empirical_leftLim_eq hN y x] at hl'
  change |empiricalLeftCDF y x - lawLeftCDF H t x| ≤ d
  exact abs_le.mpr ⟨by linarith [hl'], by linarith [hu']⟩

private theorem uniform_cdf_gives_atomLeftConvergence (S : ExperimentSequence)
    (H : JointLaw) (huniform : ∀ t, Tendsto (fun q =>
      cdfDistance (lawCDF H t) (empiricalCDF (rowOutcomes S t q))) atTop (𝓝 0)) :
    AtomLeftConvergence S H := by
  intro t x hx
  have herror : Tendsto (fun q =>
      |empiricalLeftCDF (rowOutcomes S t q) x - lawLeftCDF H t x|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun q => leftCDF_distance_le S H t q x) (huniform t)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using herror

theorem proof : SAP.P022.WH.W1.T6_L1 := by
  unfold SAP.P022.WH.W1.T6_L1 UniversalCDFRates
  refine ⟨?_, ?_, ?_⟩
  · intro η hη
    unfold correctedPartitionInteger
    apply Nat.mul_pos (by decide)
    rw [Nat.ceil_pos]
    exact div_pos (by norm_num) (lt_min hη zero_lt_one)
  · intro a b ha hab
    unfold correctedPartitionInteger
    apply Nat.mul_le_mul_left
    apply Nat.ceil_mono
    have hmin : min a 1 ≤ min b 1 := min_le_min hab le_rfl
    have hposA : 0 < min a 1 := lt_min ha zero_lt_one
    have hposB : 0 < min b 1 := lt_min (lt_of_lt_of_le ha hab) zero_lt_one
    rw [div_le_div_iff₀ hposB hposA]
    nlinarith
  · intro S H θ ρ hcond hcon t η hη
    rcases hcon with ⟨huniform, _⟩
    have hleft := uniform_cdf_gives_atomLeftConvergence S H huniform
    rcases SAP.P022.Bridge.lemma2_corrected_explicit_proof S H θ ρ hcond hleft with
      ⟨hpos, hmono, hconverges, htails⟩
    cases t
    · simpa [marginalTailRate, allocationFraction] using (htails η hη).2
    · simpa [marginalTailRate, allocationFraction] using (htails η hη).1

end
end SAP.P022.WH.W1.P.T6_L1

theorem SAP.P022.WH.W1.T6_L1_proof : SAP.P022.WH.W1.T6_L1 :=
  SAP.P022.WH.W1.P.T6_L1.proof
