import SAP.P009a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped Topology Classical

noncomputable section

theorem SAP.P009a.WH.W3.T7_L2_proof : SAP.P009a.WH.W3.T7_L2 := by
  intro G hcont hG
  let err : ℝ → ℝ := fun x => |SAP.P009a.rademacherCDF x - G x|
  have herr_nonneg (x : ℝ) : 0 ≤ err x := abs_nonneg _
  have hF_bounds (x : ℝ) :
      0 ≤ SAP.P009a.rademacherCDF x ∧
      SAP.P009a.rademacherCDF x ≤ 1 := by
    unfold SAP.P009a.rademacherCDF
    split_ifs <;> norm_num
  have hbounded : BddAbove (Set.range err) := by
    refine ⟨1, ?_⟩
    rintro y ⟨x, rfl⟩
    obtain ⟨hF0, hF1⟩ := hF_bounds x
    obtain ⟨hG0, hG1⟩ := hG x
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hsup_nonempty : (Set.range err).Nonempty :=
    ⟨err 0, ⟨0, rfl⟩⟩
  let d : ℝ := sSup (Set.range err)
  have herr_le (x : ℝ) : err x ≤ d := by
    dsimp [d]
    exact le_csSup hbounded ⟨x, rfl⟩
  have hF_at : SAP.P009a.rademacherCDF (-1) = 1/2 := by
    norm_num [SAP.P009a.rademacherCDF]
  have hleft : 1/2 - G (-1) ≤ d := by
    calc
      1/2 - G (-1) = SAP.P009a.rademacherCDF (-1) - G (-1) := by rw [hF_at]
      _ ≤ err (-1) := le_abs_self _
      _ ≤ d := herr_le (-1)
  have hseq : Tendsto (fun m : ℕ => (-1 : ℝ) - 1 / (m + 1)) atTop (nhds (-1)) := by
    have hzero : Tendsto (fun m : ℕ => (1 : ℝ) / (m + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.sub hzero
  have hvalues : ∀ m : ℕ, G ((-1 : ℝ) - 1 / (m + 1)) ≤ d := by
    intro m
    have hbelow : (-1 : ℝ) - 1 / (m + 1) < -1 := by
      have hpos : (0 : ℝ) < 1 / (m + 1) := by positivity
      linarith
    have hcdf : SAP.P009a.rademacherCDF
        ((-1 : ℝ) - 1 / (m + 1)) = 0 := by
      rw [SAP.P009a.rademacherCDF, if_pos hbelow]
    have herror := herr_le ((-1 : ℝ) - 1 / (m + 1))
    change |SAP.P009a.rademacherCDF ((-1 : ℝ) - 1 / (m + 1)) -
      G ((-1 : ℝ) - 1 / (m + 1))| ≤ d at herror
    rw [hcdf] at herror
    have hGpos := (hG ((-1 : ℝ) - 1 / (m + 1))).1
    rw [abs_of_nonpos (by linarith : (0 : ℝ) -
      G ((-1 : ℝ) - 1 / (m + 1)) ≤ 0)] at herror
    linarith
  have hG_tendsto : Tendsto (fun m : ℕ => G ((-1 : ℝ) - 1 / (m + 1)))
      atTop (nhds (G (-1))) := hcont.tendsto.comp hseq
  have hright : G (-1) ≤ d :=
    le_of_tendsto hG_tendsto (Eventually.of_forall hvalues)
  have hsum : (1/2 - G (-1)) + G (-1) ≤ d + d := add_le_add hleft hright
  have hhalf : (1/2 : ℝ) ≤ d + d := by linarith [hsum]
  have hfinal : (1/4 : ℝ) ≤ d := by linarith
  simpa [SAP.P009a.kolmogorovDistance, d, err] using hfinal
