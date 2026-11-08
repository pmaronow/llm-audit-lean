import SAP.P018b.WH.W1.Leaves
import AronowAudit.P018.Wave1.Gap.TailBRareLimits
import AronowAudit.P018.Wave1.Gap.GP0182B2b

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace SAP.P018b.WH.W1.P.T20_L3

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix.Norms.Elementwise

abbrev U := AronowAudit.P018.RareUnit
abbrev E := U × ℝ

def auxX (u v : E) : Vec 2 :=
  ![1, 1 + (if u.2 < v.2 then AronowAudit.P018.rareS u.1 v.1 else
    if v.2 < u.2 then -AronowAudit.P018.rareS u.1 v.1 else AronowAudit.P018.rareS u.1 v.1)]

def auxY (u v : E) : ℝ :=
  signValue u.1.B + signValue v.1.B +
    (if u.2 < v.2 then AronowAudit.P018.rareA u.1 v.1 else
      if v.2 < u.2 then -AronowAudit.P018.rareA u.1 v.1 else AronowAudit.P018.rareA u.1 v.1)

def auxDir {N : ℕ} (d : Dyad N) (t : Fin 2) : Bool := decide (t.val = 1)

theorem auxDir_injective {N : ℕ} (d : Dyad N) : Function.Injective (auxDir d) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [auxDir] at h ⊢

theorem auxX_reverse (u v : E) : auxX v u =
    ![1, 1 + (if u.2 < v.2 then -AronowAudit.P018.rareS u.1 v.1 else
      if v.2 < u.2 then AronowAudit.P018.rareS u.1 v.1 else AronowAudit.P018.rareS u.1 v.1)] := by
  simp only [auxX]
  rw [AronowAudit.P018.Wave1.tb09_rare_s_symmetric v.1 u.1]
  by_cases h : u.2 < v.2
  · simp [h, lt_asymm h]
  · by_cases h' : v.2 < u.2
    · simp [h, h'] <;> ring
    · have he : u.2 = v.2 := le_antisymm (le_of_not_gt h') (le_of_not_gt h)
      simp [h, h', he]

theorem auxY_reverse (u v : E) : auxY v u =
    signValue u.1.B + signValue v.1.B +
      (if u.2 < v.2 then -AronowAudit.P018.rareA u.1 v.1 else
        if v.2 < u.2 then AronowAudit.P018.rareA u.1 v.1 else AronowAudit.P018.rareA u.1 v.1) := by
  simp only [auxY]
  rw [AronowAudit.P018.Wave1.tb09_rare_a_symmetric v.1 u.1]
  by_cases h : u.2 < v.2
  · simp [h, lt_asymm h] <;> ring
  · by_cases h' : v.2 < u.2
    · simp [h, h'] <;> ring
    · have he : u.2 = v.2 := le_antisymm (le_of_not_gt h') (le_of_not_gt h)
      simp [h, h', he] <;> ring

theorem aux_record_common {N : ℕ} (d : Dyad N) (t : Fin 2) (u v : E) :
    (wholeRareDirected SAP.P018b.WH.W1.rareModel).X N d t u v =
      (if auxDir d t then auxX v u else auxX u v) ∧
    (wholeRareDirected SAP.P018b.WH.W1.rareModel).Y N d t u v =
      (if auxDir d t then auxY v u else auxY u v) := by
  have hs := AronowAudit.P018.Wave1.tb09_rare_s_symmetric
  have ha := AronowAudit.P018.Wave1.tb09_rare_a_symmetric
  have hT : (wholeRareDirected SAP.P018b.WH.W1.rareModel).T N d = 2 := rfl
  let t0 : Fin ((wholeRareDirected SAP.P018b.WH.W1.rareModel).T N d) :=
    ⟨0, by rw [hT]; norm_num⟩
  let t1 : Fin ((wholeRareDirected SAP.P018b.WH.W1.rareModel).T N d) :=
    ⟨1, by rw [hT]; norm_num⟩
  have ht0 : t0.val = 0 := rfl
  have ht1 : t1.val = 1 := rfl
  have hidx0 : t0 = (0 : Fin 2) := by apply Fin.ext; exact ht0
  have hidx1 : t1 = (1 : Fin 2) := by apply Fin.ext; exact ht1
  have hr0 : t0.rev = t1 := by apply Fin.ext; simp [t0, t1, hT, Fin.rev]
  have hr1 : t1.rev = t0 := by apply Fin.ext; simp [t0, t1, hT, Fin.rev]
  have hx0 : (wholeRareDirected SAP.P018b.WH.W1.rareModel).X N d
      t0 u v = auxX u v := by
    by_cases he : u.2 = v.2
    · simp [wholeRareDirected, wholeRareKernel, SAP.P018b.WH.W1.rareModel,
        t0, t1, ht0, ht1, hr0, hr1, hT, auxX, auxY, wholeRareS, wholeRareSmall, AronowAudit.P018.rareS,
        AronowAudit.P018.rareSmall, SAP.P018b.wholeRareDelta, AronowAudit.P018.rareDelta, he]
    · by_cases hlt : u.2 < v.2
      · simp [wholeRareDirected, wholeRareKernel, SAP.P018b.WH.W1.rareModel,
          t0, t1, ht0, ht1, hr0, hr1, hT, auxX, wholeRareS, wholeRareSmall, AronowAudit.P018.rareS,
          AronowAudit.P018.rareSmall, SAP.P018b.wholeRareDelta, AronowAudit.P018.rareDelta, he, hlt]
      · have hgt : v.2 < u.2 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he)
        simp [wholeRareDirected, wholeRareKernel, SAP.P018b.WH.W1.rareModel,
          t0, t1, ht0, ht1, hr0, hr1, hT, auxX, wholeRareS, wholeRareSmall, AronowAudit.P018.rareS,
          AronowAudit.P018.rareSmall, SAP.P018b.wholeRareDelta, AronowAudit.P018.rareDelta,
          AronowAudit.P018.Wave1.TailB_rare_small_symm, he, hlt, hgt]
  have hy0 : (wholeRareDirected SAP.P018b.WH.W1.rareModel).Y N d
      t0 u v = auxY u v := by
    by_cases he : u.2 = v.2
    · simp [wholeRareDirected, wholeRareKernel, SAP.P018b.WH.W1.rareModel,
        t0, t1, ht0, ht1, hr0, hr1, hT, auxY, wholeRareA, wholeRareSmall, AronowAudit.P018.rareA,
        AronowAudit.P018.rareSmall, he, add_comm, add_left_comm, add_assoc] <;> rfl
    · by_cases hlt : u.2 < v.2
      · simp [wholeRareDirected, wholeRareKernel, SAP.P018b.WH.W1.rareModel,
          t0, t1, ht0, ht1, hr0, hr1, hT, auxY, wholeRareA, wholeRareSmall, AronowAudit.P018.rareA,
          AronowAudit.P018.rareSmall, he, hlt, add_comm, add_left_comm, add_assoc] <;> rfl
      · have hgt : v.2 < u.2 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he)
        simp [wholeRareDirected, wholeRareKernel, SAP.P018b.WH.W1.rareModel,
          t0, t1, ht0, ht1, hr0, hr1, hT, auxY, wholeRareA, wholeRareSmall, AronowAudit.P018.rareA,
          AronowAudit.P018.rareSmall, he, hlt, hgt, add_comm, add_left_comm, add_assoc] <;> rfl
  have hx1 : (wholeRareDirected SAP.P018b.WH.W1.rareModel).X N d
      t1 u v = auxX v u := by
    rw [auxX_reverse]
    by_cases he : u.2 = v.2
    · simp [wholeRareDirected, wholeRareKernel, SAP.P018b.WH.W1.rareModel,
        t0, t1, ht0, ht1, hr0, hr1, hT, auxX, wholeRareS, wholeRareSmall, AronowAudit.P018.rareS,
        AronowAudit.P018.rareSmall, SAP.P018b.wholeRareDelta, AronowAudit.P018.rareDelta,
        AronowAudit.P018.Wave1.TailB_rare_small_symm, he, hs]
    · by_cases hlt : u.2 < v.2
      · simp [wholeRareDirected, wholeRareKernel, SAP.P018b.WH.W1.rareModel,
          t0, t1, ht0, ht1, hr0, hr1, hT, auxX, wholeRareS, wholeRareSmall, AronowAudit.P018.rareS,
          AronowAudit.P018.rareSmall, SAP.P018b.wholeRareDelta, AronowAudit.P018.rareDelta,
          AronowAudit.P018.Wave1.TailB_rare_small_symm, he, hlt, hs]
      · have hgt : v.2 < u.2 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he)
        simp [wholeRareDirected, wholeRareKernel, SAP.P018b.WH.W1.rareModel,
          t0, t1, ht0, ht1, hr0, hr1, hT, auxX, wholeRareS, wholeRareSmall, AronowAudit.P018.rareS,
          AronowAudit.P018.rareSmall, SAP.P018b.wholeRareDelta, AronowAudit.P018.rareDelta,
          AronowAudit.P018.Wave1.TailB_rare_small_symm, he, hlt, hgt, hs]
  have hy1 : (wholeRareDirected SAP.P018b.WH.W1.rareModel).Y N d
      t1 u v = auxY v u := by
    rw [auxY_reverse]
    by_cases he : u.2 = v.2
    · simp [wholeRareDirected, wholeRareKernel, SAP.P018b.WH.W1.rareModel,
        t0, t1, ht0, ht1, hr0, hr1, hT, auxY, wholeRareA, wholeRareSmall, AronowAudit.P018.rareA,
        AronowAudit.P018.rareSmall, he, ha, add_comm, add_left_comm, add_assoc] <;> rfl
    · by_cases hlt : u.2 < v.2
      · simp [wholeRareDirected, wholeRareKernel, SAP.P018b.WH.W1.rareModel,
          t0, t1, ht0, ht1, hr0, hr1, hT, auxY, wholeRareA, wholeRareSmall, AronowAudit.P018.rareA,
          AronowAudit.P018.rareSmall, he, hlt, ha, add_comm, add_left_comm, add_assoc] <;> rfl
      · have hgt : v.2 < u.2 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he)
        simp [wholeRareDirected, wholeRareKernel, SAP.P018b.WH.W1.rareModel,
          t0, t1, ht0, ht1, hr0, hr1, hT, auxY, wholeRareA, wholeRareSmall, AronowAudit.P018.rareA,
          AronowAudit.P018.rareSmall, he, hlt, hgt, ha, add_comm, add_left_comm, add_assoc] <;> rfl
  fin_cases t
  · simpa [auxDir, hidx0] using And.intro hx0 hy0
  · simpa [auxDir, hidx1] using And.intro hx1 hy1

theorem auxRareQ : wholeRareQ SAP.P018b.WH.W1.rareModel = AronowAudit.P018.rareQ := rfl

def auxLaw : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

theorem auxLaw_probability : IsProbabilityMeasure auxLaw := by
  refine ⟨?_⟩
  rw [auxLaw, Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

theorem auxX_measurable : Measurable (fun p : E × E => auxX p.1 p.2) := by
  have hpair : Measurable (fun p : E × E => ((p.1.1, p.2.1) : U × U)) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have hs0 : Measurable (fun uv : U × U => AronowAudit.P018.rareS uv.1 uv.2) :=
    measurable_of_countable _
  have hs : Measurable (fun p : E × E => AronowAudit.P018.rareS p.1.1 p.2.1) := hs0.comp hpair
  have hlt : MeasurableSet {p : E × E | p.1.2 < p.2.2} :=
    measurableSet_lt (measurable_snd.comp measurable_fst) (measurable_snd.comp measurable_snd)
  have hgt : MeasurableSet {p : E × E | p.2.2 < p.1.2} :=
    measurableSet_lt (measurable_snd.comp measurable_snd) (measurable_snd.comp measurable_fst)
  have hmid : Measurable (fun p : E × E =>
      if p.2.2 < p.1.2 then -AronowAudit.P018.rareS p.1.1 p.2.1
      else AronowAudit.P018.rareS p.1.1 p.2.1) := Measurable.ite hgt hs.neg hs
  let fs : E × E → ℝ := fun p =>
      if p.1.2 < p.2.2 then AronowAudit.P018.rareS p.1.1 p.2.1
      else if p.2.2 < p.1.2 then -AronowAudit.P018.rareS p.1.1 p.2.1
      else AronowAudit.P018.rareS p.1.1 p.2.1
  have hlast : Measurable fs := Measurable.ite hlt hs hmid
  rw [measurable_pi_iff]
  intro j
  fin_cases j
  · exact measurable_const
  · change Measurable ((fun _ : E × E => (1 : ℝ)) + fs)
    exact measurable_const.add hlast

theorem auxY_measurable : Measurable (fun p : E × E => auxY p.1 p.2) := by
  have hpair : Measurable (fun p : E × E => ((p.1.1, p.2.1) : U × U)) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have hA0 : Measurable (fun uv : U × U => AronowAudit.P018.rareA uv.1 uv.2) :=
    measurable_of_countable _
  have hA : Measurable (fun p : E × E => AronowAudit.P018.rareA p.1.1 p.2.1) := hA0.comp hpair
  have hB0 : Measurable (fun u : U => signValue u.B) := measurable_of_countable _
  have hB₁ : Measurable (fun p : E × E => signValue p.1.1.B) :=
    hB0.comp (measurable_fst.comp measurable_fst)
  have hB₂ : Measurable (fun p : E × E => signValue p.2.1.B) :=
    hB0.comp (measurable_fst.comp measurable_snd)
  have hlt : MeasurableSet {p : E × E | p.1.2 < p.2.2} :=
    measurableSet_lt (measurable_snd.comp measurable_fst) (measurable_snd.comp measurable_snd)
  have hgt : MeasurableSet {p : E × E | p.2.2 < p.1.2} :=
    measurableSet_lt (measurable_snd.comp measurable_snd) (measurable_snd.comp measurable_fst)
  have hmid : Measurable (fun p : E × E =>
      if p.2.2 < p.1.2 then -AronowAudit.P018.rareA p.1.1 p.2.1
      else AronowAudit.P018.rareA p.1.1 p.2.1) := Measurable.ite hgt hA.neg hA
  let fa : E × E → ℝ := fun p =>
      if p.1.2 < p.2.2 then AronowAudit.P018.rareA p.1.1 p.2.1
      else if p.2.2 < p.1.2 then -AronowAudit.P018.rareA p.1.1 p.2.1
      else AronowAudit.P018.rareA p.1.1 p.2.1
  have hlast : Measurable fa := Measurable.ite hlt hA hmid
  change Measurable ((fun p : E × E => signValue p.1.1.B) +
    (fun p : E × E => signValue p.2.1.B) + fa)
  exact (hB₁.add hB₂).add hlast

theorem auxX_norm_bound (u v : E) : ‖auxX u v‖ ≤ 4 := by
  have hs := AronowAudit.P018.Wave1.TailB_rare_s_bounds u.1 v.1
  have hx : 0 ≤ auxX u v 1 ∧ auxX u v 1 ≤ 2 := by
    dsimp [auxX]
    split_ifs <;> constructor <;> linarith
  have hnorm : ‖auxX u v‖ =
      ↑(Finset.univ.sup (fun j : Fin 2 => ‖auxX u v j‖₊)) := rfl
  have hcoord : ∀ j : Fin 2, ‖auxX u v j‖₊ ≤ (4 : NNReal) := by
    intro j
    fin_cases j
    · norm_num [auxX]
    · have hj : ‖auxX u v 1‖ ≤ 4 := by
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg hx.1]
        linarith
      exact_mod_cast hj
  have hsupp : Finset.univ.sup (fun j : Fin 2 => ‖auxX u v j‖₊) ≤ (4 : NNReal) :=
    Finset.sup_le (by intro j hj; exact hcoord j)
  rw [hnorm]
  exact_mod_cast hsupp

theorem auxY_bound (u v : E) : |auxY u v| ≤ 4 := by
  have hb : |signValue u.1.B + signValue v.1.B| ≤ 2 := by
    cases u.1.B <;> cases v.1.B <;> norm_num [signValue]
  have ha := AronowAudit.P018.Wave1.TailB_rare_a_bound u.1 v.1
  have ht : |if u.2 < v.2 then AronowAudit.P018.rareA u.1 v.1 else
      if v.2 < u.2 then -AronowAudit.P018.rareA u.1 v.1 else AronowAudit.P018.rareA u.1 v.1| ≤ 2 := by
    split_ifs <;> simpa only [abs_neg] using ha
  dsimp [auxY]
  exact (abs_add_le _ _).trans (by linarith)

theorem auxDirected_X_bound {N : ℕ} (d : Dyad N) (t : Fin 2) (u v : E) :
    ‖(wholeRareDirected SAP.P018b.WH.W1.rareModel).X N d t u v‖ ≤ 4 := by
  rcases aux_record_common d t u v with ⟨hx, _⟩
  rw [hx]
  by_cases h : auxDir d t <;> simp [h] <;> first | exact auxX_norm_bound _ _ | exact auxX_norm_bound _ _

theorem auxDirected_Y_bound {N : ℕ} (d : Dyad N) (t : Fin 2) (u v : E) :
    |(wholeRareDirected SAP.P018b.WH.W1.rareModel).Y N d t u v| ≤ 4 := by
  rcases aux_record_common d t u v with ⟨_, hy⟩
  rw [hy]
  by_cases h : auxDir d t <;> simp [h] <;> exact auxY_bound _ _

theorem auxDirected_X_measurable {N : ℕ} (d : Dyad N) (t : Fin 2) :
    Measurable (fun p : E × E =>
      (wholeRareDirected SAP.P018b.WH.W1.rareModel).X N d t p.1 p.2) := by
  have hswap : Measurable (fun p : E × E => (p.2, p.1)) := measurable_snd.prodMk measurable_fst
  have hEq : (fun p : E × E =>
      (wholeRareDirected SAP.P018b.WH.W1.rareModel).X N d t p.1 p.2) =
      (if auxDir d t then (fun p => auxX p.2 p.1) else fun p => auxX p.1 p.2) := by
    funext p
    simpa only [ite_apply] using (aux_record_common d t p.1 p.2).1
  rw [hEq]
  by_cases h : auxDir d t = true
  · simpa [h, Function.comp_def] using auxX_measurable.comp hswap
  · simpa [h, Function.comp_def] using auxX_measurable

theorem auxDirected_Y_measurable {N : ℕ} (d : Dyad N) (t : Fin 2) :
    Measurable (fun p : E × E =>
      (wholeRareDirected SAP.P018b.WH.W1.rareModel).Y N d t p.1 p.2) := by
  have hswap : Measurable (fun p : E × E => (p.2, p.1)) := measurable_snd.prodMk measurable_fst
  have hEq : (fun p : E × E =>
      (wholeRareDirected SAP.P018b.WH.W1.rareModel).Y N d t p.1 p.2) =
      (if auxDir d t then (fun p => auxY p.2 p.1) else fun p => auxY p.1 p.2) := by
    funext p
    simpa only [ite_apply] using (aux_record_common d t p.1 p.2).2
  rw [hEq]
  by_cases h : auxDir d t = true
  · simpa [h, Function.comp_def] using auxY_measurable.comp hswap
  · simpa [h, Function.comp_def] using auxY_measurable


theorem aux_structure :
    RepeatedStanding (wholeRareDirected SAP.P018b.WH.W1.rareModel) ∧
    ∃ (X : E → E → Vec 2) (Y : E → E → ℝ)
      (dir : ∀ N, (d : Dyad N) → Fin ((wholeRareDirected SAP.P018b.WH.W1.rareModel).T N d) → Bool),
      (∀ N d, Function.Injective (dir N d)) ∧
      (∀ N d t u v,
        (wholeRareDirected SAP.P018b.WH.W1.rareModel).X N d t u v =
          (if dir N d t then X v u else X u v) ∧
        (wholeRareDirected SAP.P018b.WH.W1.rareModel).Y N d t u v =
          (if dir N d t then Y v u else Y u v)) := by
  classical
  refine ⟨?_, ?_⟩
  ·
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · letI : MeasureTheory.IsProbabilityMeasure AronowAudit.P018.rareLaw :=
        AronowAudit.P018.Wave1.TailB_rare_probability
      letI : MeasureTheory.IsProbabilityMeasure auxLaw := auxLaw_probability
      change MeasureTheory.IsProbabilityMeasure
        (AronowAudit.P018.rareLaw.prod auxLaw)
      infer_instance
    · intro N hN d
      change 0 < 2
      norm_num
    · intro N d t
      exact ⟨auxDirected_X_measurable d t, auxDirected_Y_measurable d t⟩
    · refine ⟨4, by norm_num, ?_⟩
      intro N d t
      filter_upwards [] with uv
      exact ⟨auxDirected_X_bound d t uv.1 uv.2,
        auxDirected_Y_bound d t uv.1 uv.2⟩
    · refine ⟨0, ?_⟩
      intro N d t u v
      rcases aux_record_common d t u v with ⟨hx, _⟩
      rw [hx]
      by_cases h : auxDir d t = true <;> simp [h, auxX]
  · refine ⟨auxX, auxY, (fun N d t => auxDir d t), ?_, ?_⟩
    · intro N d
      exact auxDir_injective d
    · intro N d t u v
      exact aux_record_common d t u v

theorem aux_limit_matrix_posdef :
    (!![2,2;2,2+2*wholeRareQ SAP.P018b.WH.W1.rareModel] : Mat 2).PosDef := by
  rw [show wholeRareQ SAP.P018b.WH.W1.rareModel = AronowAudit.P018.rareQ by rfl]
  have hq : 0 < AronowAudit.P018.rareQ := AronowAudit.P018.Wave1.tb09_rare_Q_pos
  apply AronowAudit.P018.positive_definite_two <;>
    nlinarith

open AronowAudit.P018.Wave1

abbrev R := wholeRareDirected rareModel
abbrev R₀ := wholeRareKernel rareModel
local instance rare_prob : IsProbabilityMeasure AronowAudit.P018.rareLaw := TailB_rare_probability
local instance aux_prob : IsProbabilityMeasure auxLaw := auxLaw_probability
local instance aux_null : NullSingletonClass auxLaw := by
  dsimp [auxLaw]
  infer_instance
local instance directed_prob : IsProbabilityMeasure R.μ := by
  change IsProbabilityMeasure (AronowAudit.P018.rareLaw.prod auxLaw)
  infer_instance
local instance rows_prob (N : ℕ) : IsProbabilityMeasure (repeatedLaw R N) := by
  unfold repeatedLaw
  infer_instance

/-- The two auxiliary labels are unequal almost surely. -/
theorem pair_untied : ∀ᵐ uv ∂ R.μ.prod R.μ, uv.1.2 ≠ uv.2.2 := by
  apply (Measure.ae_prod_iff_ae_ae ((measurableSet_eq_fun
    (measurable_snd.comp measurable_fst) (measurable_snd.comp measurable_snd)).compl)).2
  filter_upwards [] with u
  have hp : MeasurePreserving (Prod.snd : E → ℝ) R.μ auxLaw := by
    change MeasurePreserving Prod.snd (AronowAudit.P018.rareLaw.prod auxLaw) auxLaw
    exact measurePreserving_snd
  filter_upwards [hp.quasiMeasurePreserving.ae (auxLaw.ae_ne u.2)] with v hv
  exact Ne.symm hv

theorem sample_untied (N : ℕ) : ∀ᵐ ω ∂ repeatedLaw R N,
    ∀ d : Dyad N, (ω (firstUnit d)).2 ≠ (ω (secondUnit d)).2 := by
  apply ae_all_iff.mpr
  intro d
  have hp : MeasurePreserving
      (fun ω : Fin N → E => (ω (firstUnit d), ω (secondUnit d)))
      (repeatedLaw R N) (R.μ.prod R.μ) :=
    GP0182B2b_pair_measurePreserving _ (iIndepFun_pi (fun _ => aemeasurable_id))
      (fun i => measurePreserving_eval (fun _ : Fin N => R.μ) i)
      (WeightedConsistency.firstUnit_ne_secondUnit d)
  exact hp.quasiMeasurePreserving.ae pair_untied

theorem project_preserving (N : ℕ) : MeasurePreserving
    (fun ω : Fin N → E => fun i => (ω i).1)
    (repeatedLaw R N) (repeatedLaw R₀ N) := by
  change MeasurePreserving _
    (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw.prod auxLaw))
    (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw))
  exact measurePreserving_pi _ _ (fun _ => measurePreserving_fst)

/-- Off ties, each dyad has exactly the original two records. -/
theorem block_perm {N : ℕ} (d : Dyad N) (u v : E) (h : u.2 ≠ v.2) :
    (∑ t : Fin 2, outer (R.X N d t u v) (R.X N d t u v)) =
      ∑ t : Fin 2, outer (R₀.X N d t u.1 v.1) (R₀.X N d t u.1 v.1) ∧
    (∑ t : Fin 2, score (R.X N d t u v) (R.Y N d t u v)) =
      ∑ t : Fin 2, score (R₀.X N d t u.1 v.1) (R₀.Y N d t u.1 v.1) := by
  by_cases hlt : u.2 < v.2
  · simp [R, wholeRareDirected, h, hlt]
  · simp [R, R₀, wholeRareDirected, wholeRareKernel, h, hlt, Fin.sum_univ_two, Fin.rev, add_comm]

theorem sample_perm (N : ℕ) : ∀ᵐ ω ∂ repeatedLaw R N,
    wholeWeightedGram R (fun _ _ => 1) ω = repeatedGram R₀ (fun i => (ω i).1) ∧
    wholeWeightedXY R (fun _ _ => 1) ω =
      ∑ d : Dyad N, ∑ t, score (repeatedX R₀ (fun i => (ω i).1) d t)
        (repeatedY R₀ (fun i => (ω i).1) d t) := by
  filter_upwards [sample_untied N] with ω hω
  constructor
  · simp only [wholeWeightedGram, repeatedGram, one_smul, repeatedX]
    apply Finset.sum_congr rfl
    intro d hd
    exact (block_perm d _ _ (hω d)).1
  · simp only [wholeWeightedXY, one_mul, repeatedX, repeatedY]
    apply Finset.sum_congr rfl
    intro d hd
    exact (block_perm d _ _ (hω d)).2

theorem expected_gram_transfer (N : ℕ) :
    meanMat (repeatedLaw R N) (wholeWeightedGram R (fun _ _ => 1)) =
      meanMat (repeatedLaw R₀ N) (repeatedGram R₀) := by
  ext a b
  change (∫ ω, wholeWeightedGram R (fun _ _ => 1) ω a b ∂repeatedLaw R N) = _
  calc
    _ = ∫ ω, repeatedGram R₀ (fun i => (ω i).1) a b ∂repeatedLaw R N := by
      apply integral_congr_ae
      filter_upwards [sample_perm N] with ω hω
      exact congrFun (congrFun hω.1 a) b
    _ = _ := GP0182B2b_integral_comp_measurePreserving _ (project_preserving N)
      (fun ω => repeatedGram R₀ ω a b) (measurable_of_countable _)

theorem expected_xy_transfer (N : ℕ) :
    meanVec (repeatedLaw R N) (wholeWeightedXY R (fun _ _ => 1)) =
      meanVec (repeatedLaw R₀ N) (fun ω => ∑ d : Dyad N, ∑ t,
        score (repeatedX R₀ ω d t) (repeatedY R₀ ω d t)) := by
  ext a
  change (∫ ω, wholeWeightedXY R (fun _ _ => 1) ω a ∂repeatedLaw R N) = _
  calc
    _ = ∫ ω, (∑ d : Dyad N, ∑ t, score (repeatedX R₀ (fun i => (ω i).1) d t)
        (repeatedY R₀ (fun i => (ω i).1) d t)) a ∂repeatedLaw R N := by
      apply integral_congr_ae
      filter_upwards [sample_perm N] with ω hω
      exact congrFun hω.2 a
    _ = _ := GP0182B2b_integral_comp_measurePreserving _ (project_preserving N)
      (fun ω => (∑ d : Dyad N, ∑ t, score (repeatedX R₀ ω d t) (repeatedY R₀ ω d t)) a)
      (measurable_of_countable _)

theorem directed_beta (N : ℕ) : wholeWeightedBeta (N := N) R (fun _ _ => 1) = 0 := by
  rw [wholeWeightedBeta, expected_gram_transfer, expected_xy_transfer]
  exact tb09_rare_population_beta N

theorem directed_rank (N : ℕ) (hN : 2 ≤ N) : ∀ᵐ ω ∂ repeatedLaw R N,
    (wholeWeightedGram R (fun _ _ => 1) ω).det ≠ 0 := by
  filter_upwards [sample_perm N] with ω hω
  rw [hω.1]
  exact (TailB_rare_gram_pos hN (fun i => (ω i).1)).ne'

local instance rare_rows_prob (N : ℕ) : IsProbabilityMeasure (repeatedLaw R₀ N) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw))
  infer_instance

theorem rare_S_mean (N : ℕ) :
    (∫ ω, TailB_rare_S ω ∂repeatedLaw R₀ N) = Dreal N * AronowAudit.P018.rareQ := by
  have hi (d : Dyad N) : Integrable
      (fun ω : Fin N → U => (AronowAudit.P018.rareS (ω (firstUnit d)) (ω (secondUnit d)))^2)
      (repeatedLaw R₀ N) :=
    (MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (ae_of_all _ (fun ω => tb09_rare_s2_bound (ω (firstUnit d), ω (secondUnit d)))) :
        MemLp _ 2 _).integrable one_le_two
  have he (d : Dyad N) : (∫ ω : Fin N → U,
      (AronowAudit.P018.rareS (ω (firstUnit d)) (ω (secondUnit d)))^2 ∂repeatedLaw R₀ N) =
      AronowAudit.P018.rareQ :=
    GP0182B2b_kernel_pair_integral _ (iIndepFun_pi (fun _ => aemeasurable_id))
      (fun i => measurePreserving_eval (fun _ : Fin N => AronowAudit.P018.rareLaw) i)
      (K := fun uv => (AronowAudit.P018.rareS uv.1 uv.2)^2)
      (measurable_of_countable _) (WeightedConsistency.firstUnit_ne_secondUnit d)
  change (∫ ω : Fin N → U, ∑ d : Dyad N,
    (AronowAudit.P018.rareS (ω (firstUnit d)) (ω (secondUnit d)))^2 ∂repeatedLaw R₀ N) = _
  simp only [TailB_rare_S, TailB_rare_s, integral_finsetSum _ (fun d _ => hi d), he,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show (Fintype.card (Dyad N) : ℝ) = Dreal N from printed_card_real N]

theorem rare_S_integrable (N : ℕ) : Integrable (TailB_rare_S (N := N)) (repeatedLaw R₀ N) := by
  change Integrable (fun ω : Fin N → U => ∑ d : Dyad N,
    (AronowAudit.P018.rareS (ω (firstUnit d)) (ω (secondUnit d)))^2) _
  apply integrable_finsetSum
  intro d hd
  exact (MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    (ae_of_all _ (fun ω => tb09_rare_s2_bound (ω (firstUnit d), ω (secondUnit d)))) :
      MemLp _ 2 _).integrable one_le_two

theorem rare_expected_gram (N : ℕ) :
    meanMat (repeatedLaw R₀ N) (repeatedGram R₀) =
      !![2*Dreal N, 2*Dreal N; 2*Dreal N, 2*Dreal N+2*(Dreal N*AronowAudit.P018.rareQ)] := by
  have hg (ω : Fin N → U) : repeatedGram R₀ ω =
      !![2*Dreal N, 2*Dreal N; 2*Dreal N, 2*Dreal N+2*TailB_rare_S ω] :=
    TailB_rare_gram ω
  have hi := rare_S_integrable N
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [meanMat, hg, integral_add (integrable_const _) (hi.const_mul 2),
      integral_const_mul, rare_S_mean N]

theorem directed_expected_gram (N : ℕ) (hN : 2 ≤ N) :
    wholeWeightedH (N := N) R (fun _ _ => 1) =
      (!![2,2;2,2+2*wholeRareQ rareModel] : Mat 2) := by
  rw [wholeWeightedH, expected_gram_transfer, rare_expected_gram]
  have hd : Dreal N ≠ 0 := (TailB_rare_D_pos hN).ne'
  have hq : wholeRareQ rareModel = AronowAudit.P018.rareQ := rfl
  ext a b
  fin_cases a <;> fin_cases b <;> simp [hq] <;> field_simp [hd] <;> ring

theorem directed_expected_limit :
    Tendsto (fun N : ℕ => wholeWeightedH (N := N) R (fun _ _ => 1)) atTop
      (𝓝 (!![2,2;2,2+2*wholeRareQ rareModel] : Mat 2)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (directed_expected_gram N hN).symm

end SAP.P018b.WH.W1.P.T20_L3

open SAP.P018b.WH.W1.P.T20_L3

theorem SAP.P018b.WH.W1.T20_L3_proof : SAP.P018b.WH.W1.T20_L3 := by
  exact ⟨aux_structure.1, aux_structure.2, aux_limit_matrix_posdef,
    directed_expected_limit, fun N _ => directed_beta N, directed_rank⟩
