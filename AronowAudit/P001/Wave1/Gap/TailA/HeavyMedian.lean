import AronowAudit.P001.Wave1.Lib.TailA.MedianWeak
import AronowAudit.P001.Wave1.Gap.GP0014B1

/-! Actual upper-median weak limits and the heavy-tail bootstrap variance obstruction. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.Wave1.TailA

open AronowAudit.P001.TailA

local instance instDecidableHeavyMedian (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Both transformed tail components lie outside the open unit interval. -/
theorem heavyMedian_transform_lower (u : ℝ) : 1 ≤ (2 : ℝ)^(1/u^2) := by
  exact Real.one_le_rpow (by norm_num) (div_nonneg (by norm_num) (sq_nonneg u))

/-- The population CDF is affine throughout the open unit interval. -/
theorem heavyMedian_local_cdf (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    cdf heavyBootstrapLaw id x = 1/2+x/4 := by
  have hu : uniformLaw (-1) 1 (Set.Iic x) =
      (1/2 : ℝ≥0∞)*ENNReal.ofReal (x+1) := by
    rw [regular_uniform_symmetric_eq, Measure.smul_apply,
      Measure.restrict_apply measurableSet_Iic]
    have he : Set.Iic x ∩ Set.Icc (-1 : ℝ) 1 = Set.Icc (-1 : ℝ) x := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨hy, hl, _⟩
        exact ⟨hl, hy⟩
      · rintro ⟨hl, hy⟩
        exact ⟨hy, hl, hy.trans hx.2.le⟩
    rw [he, Real.volume_Icc]
    simp only [sub_neg_eq_add, smul_eq_mul]
  have hpositive : (fun u : ℝ => (2 : ℝ)^(1/u^2)) ⁻¹' Set.Iic x = ∅ := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
    exact not_le_of_gt (hx.2.trans_le (heavyMedian_transform_lower u))
  have hnegative : (fun u : ℝ => -((2 : ℝ)^(1/u^2))) ⁻¹' Set.Iic x = Set.univ := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
    linarith [heavyMedian_transform_lower u, hx.1]
  change (heavyBootstrapLaw (Set.Iic x)).toReal = 1/2+x/4
  rw [heavyBootstrapLaw, Measure.add_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply regular_heavy_transform_measurable measurableSet_Iic,
    Measure.map_apply (show Measurable (fun u : ℝ => -((2 : ℝ)^(1/u^2)))
      from regular_heavy_transform_measurable.neg) measurableSet_Iic,
    hpositive, hnegative, measure_empty, regular_uniform_zero_one_mass, hu]
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one,
    ENNReal.toReal_ofReal (by linarith [hx.1] : 0 ≤ x+1)]
  ring

/-- The heavy population has the constant local density one quarter. -/
theorem heavyMedian_local_density :
    heavyBootstrapLaw.restrict (Metric.ball (0 : ℝ) 1) =
      (volume.restrict (Metric.ball (0 : ℝ) 1)).withDensity
        (fun _ => ENNReal.ofReal (1/4 : ℝ)) := by
  have hball : Metric.ball (0 : ℝ) 1 ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    have h : |x| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hx
    exact ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩
  have htails (s : Set ℝ) :
      (fun u : ℝ => (2 : ℝ)^(1/u^2)) ⁻¹' (s ∩ Metric.ball (0 : ℝ) 1) = ∅ ∧
      (fun u : ℝ => -((2 : ℝ)^(1/u^2))) ⁻¹' (s ∩ Metric.ball (0 : ℝ) 1) = ∅ := by
    constructor
    · apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      have hh : |(2 : ℝ)^(1/u^2)| < 1 := by
        simpa [Metric.mem_ball, Real.dist_eq] using hu.2
      linarith [le_abs_self ((2 : ℝ)^(1/u^2)), heavyMedian_transform_lower u]
    · apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      have hh : |(2 : ℝ)^(1/u^2)| < 1 := by
        simpa [Metric.mem_ball, Real.dist_eq] using hu.2
      linarith [le_abs_self ((2 : ℝ)^(1/u^2)), heavyMedian_transform_lower u]
  rw [withDensity_const]
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs, heavyBootstrapLaw,
    Measure.add_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply regular_heavy_transform_measurable (hs.inter measurableSet_ball),
    Measure.map_apply (show Measurable (fun u : ℝ => -((2 : ℝ)^(1/u^2)))
      from regular_heavy_transform_measurable.neg) (hs.inter measurableSet_ball),
    (htails s).1, (htails s).2, measure_empty,
    regular_uniform_symmetric_eq, Measure.smul_apply,
    Measure.restrict_apply (hs.inter measurableSet_ball)]
  have he : (s ∩ Metric.ball (0 : ℝ) 1) ∩ Set.Icc (-1 : ℝ) 1 =
      s ∩ Metric.ball (0 : ℝ) 1 :=
    Set.inter_eq_left.mpr (fun _ hx => hball hx.2)
  rw [he, Measure.smul_apply, Measure.restrict_apply hs]
  simp only [smul_eq_mul, mul_zero, add_zero, ← mul_assoc]
  have hhalf : ENNReal.ofReal (1/2 : ℝ) = (1/2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [show (1/4 : ℝ) = (1/2 : ℝ)*(1/2) by norm_num,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2), hhalf]

/-- The local density and affine CDF give the exact moment-free median inputs. -/
theorem heavyMedian_local_data {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : Measurable (X 0)) (hlaw : μ.map (X 0) = heavyBootstrapLaw) :
    LocalMedianData μ X 0 (fun _ => (1/4 : ℝ)) := by
  have hCDF (x : ℝ) : cdf μ (X 0) x = cdf heavyBootstrapLaw id x := by
    change (μ (X 0 ⁻¹' Set.Iic x)).toReal = (heavyBootstrapLaw (Set.Iic x)).toReal
    rw [← Measure.map_apply hX measurableSet_Iic, hlaw]
  have hmono : Monotone (cdf μ (X 0)) := by
    intro x y hxy
    exact ENNReal.toReal_mono (measure_ne_top μ _)
      (measure_mono (fun ω hω => hω.trans hxy))
  refine ⟨1, by norm_num, ?_, fun _ _ => by norm_num,
    aemeasurable_const, continuousAt_const, by norm_num, ?_, ?_, ?_⟩
  · rw [hlaw]
    exact heavyMedian_local_density
  · rw [hCDF, heavyMedian_local_cdf 0 (by constructor <;> norm_num)]
    norm_num
  · intro x hx
    let y : ℝ := max x (-1/2)
    have hy : y ∈ Set.Ioo (-1 : ℝ) 1 := by
      dsimp [y]
      constructor
      · exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < -1/2) (le_max_right _ _)
      · exact max_lt hx (by norm_num) |>.trans (by norm_num : (0 : ℝ) < 1)
    have hyneg : y < 0 := max_lt hx (by norm_num)
    have hh := hmono (le_max_left x (-1/2))
    rw [hCDF y, heavyMedian_local_cdf y hy] at hh
    linarith
  · intro x hx
    let y : ℝ := min x (1/2)
    have hypos : 0 < y := lt_min hx (by norm_num)
    have hy : y ∈ Set.Ioo (-1 : ℝ) 1 :=
      ⟨lt_trans (by norm_num) hypos,
        lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
    have hh := hmono (min_le_left x (1/2))
    rw [hCDF y, heavyMedian_local_cdf y hy] at hh
    linarith

theorem heavyMedian_bad_sample_deterministic {n : ℕ} (hn : 5 ≤ n) (s : Fin n → ℝ)
    (hhigh : ∃ i, (2 : ℝ)^(n^2) ≤ s i) (hcentral : ∃ j, |s j| ≤ 1) :
    5 < (n : ℝ)*bootVar sampleMedian s := by
  let H : ℝ := (2 : ℝ)^(n^2)
  let N : ℝ := (n : ℝ)^n
  have hn0 : 0 < n := by omega
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hH : (32 : ℝ) ≤ H := by
    have hexp : 5 ≤ n^2 := by nlinarith
    have hh := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hexp
    norm_num only [show (2 : ℝ)^5 = 32 by norm_num] at hh
    exact hh
  have hNpos : 0 < N := pow_pos (Nat.cast_pos.mpr hn0) _
  have hNH : N ≤ H := regular_sample_size_power_bound n
  obtain ⟨i,hi⟩ := hhigh
  obtain ⟨j,hj⟩ := hcentral
  change H ≤ s i at hi
  have hjupper : s j ≤ 1 := (le_abs_self _).trans hj
  have hij : i ≠ j := by
    intro he
    have hh : H ≤ s j := by simpa only [he] using hi
    linarith
  let a : Fin n → Fin n := fun _ => i
  let b : Fin n → Fin n := fun _ => j
  have hab : a ≠ b := by
    intro he
    exact hij (congrFun he ⟨0,hn0⟩)
  have hpair := regular_bootstrap_two_atoms hn0 sampleMedian s a b hab
  have ha : sampleMedian (resample s a) = s i := regular_constant_median hn0 (s i)
  have hb : sampleMedian (resample s b) = s j := regular_constant_median hn0 (s j)
  rw [ha,hb] at hpair
  have hdiff : H-1 ≤ s i-s j := by linarith
  have hsq : (H-1)^2 ≤ (s i-s j)^2 :=
    pow_le_pow_left₀ (by linarith) hdiff 2
  have hHN : H*N ≤ H^2 := by
    have hh := mul_le_mul_of_nonneg_left hNH (show (0 : ℝ) ≤ H by linarith)
    simpa only [pow_two] using hh
  have hsqH : H^2/4 ≤ (H-1)^2 := by nlinarith [sq_nonneg (H-2)]
  have hlower : H/8 ≤ (s i-s j)^2/(2*N) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hNpos)).mpr
    nlinarith
  have hV : H/8 ≤ bootVar sampleMedian s := hlower.trans hpair
  have hscaled := mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg n)
  have hbase := mul_le_mul_of_nonneg_left
    (show (4 : ℝ) ≤ H/8 by linarith) (Nat.cast_nonneg n)
  nlinarith


theorem heavyMedian_bad_sample_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
    (hlaw : μ.map (X 0) = heavyBootstrapLaw) (n : ℕ) (hn : 5 ≤ n) :
    (3/16 : ℝ) ≤ prob μ {ω | 5 < (n : ℝ)*bootVar sampleMedian (firstSample X n ω)} := by
  let H : ℝ := (2 : ℝ)^(n^2)
  let A : Set ℝ := Set.Ici H
  let C : Set ℝ := Set.Icc (-1 : ℝ) 1
  let E : Set Ω := {ω | (∃ i : Fin n, X i ω ∈ A) ∧ (∃ j : Fin n, X j ω ∈ C)}
  let N₁ : Set Ω := {ω | ∀ i : Fin n, X i ω ∉ A}
  let N₂ : Set Ω := {ω | ∀ i : Fin n, X i ω ∉ C}
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hA : MeasurableSet A := measurableSet_Ici
  have hC : MeasurableSet C := measurableSet_Icc
  have hE : MeasurableSet E := by
    have he : E = (⋃ i : Fin n, X i ⁻¹' A) ∩ (⋃ j : Fin n, X j ⁻¹' C) := by
      ext ω
      simp [E]
    rw [he]
    exact (MeasurableSet.iUnion (fun i : Fin n => hA.preimage (hiid.1 i))).inter
      (MeasurableSet.iUnion (fun j : Fin n => hC.preimage (hiid.1 j)))
  have hEA : Eᶜ = N₁ ∪ N₂ := by
    ext ω
    simp only [E,N₁,N₂,Set.mem_compl_iff,Set.mem_setOf_eq,Set.mem_union]
    simp only [not_and_or,not_exists]
  have hq : 1/(4*(n : ℝ)) ≤ prob μ {ω | X 0 ω ∈ A} := by
    have hh := regular_heavy_tail_lower n hn0
    rw [← hlaw, Measure.map_apply (hiid.1 0) measurableSet_Ici] at hh
    have hr := ENNReal.toReal_mono (measure_ne_top μ _) hh
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(4*(n : ℝ)))] at hr
    exact hr
  have hc : (1/2 : ℝ) ≤ prob μ {ω | X 0 ω ∈ C} := by
    have hh := regular_heavy_central_lower
    rw [← hlaw, Measure.map_apply (hiid.1 0) measurableSet_Icc] at hh
    have hr := ENNReal.toReal_mono (measure_ne_top μ _) hh
    norm_num at hr
    exact hr
  have hn₁ : prob μ N₁ ≤ (25/32 : ℝ) := by
    rw [show N₁ = {ω | ∀ i : Fin n, X i ω ∉ A} from rfl,
      regular_iid_none μ X hiid A hA n]
    have hle : 1-prob μ {ω | X 0 ω ∈ A} ≤ 1-1/(4*(n : ℝ)) := by linarith
    have hnon : 0 ≤ 1-prob μ {ω | X 0 ω ∈ A} := sub_nonneg.mpr measureReal_le_one
    exact (pow_le_pow_left₀ hnon hle n).trans (regular_no_high_numeric n hn)
  have hn₂ : prob μ N₂ ≤ (1/32 : ℝ) := by
    rw [show N₂ = {ω | ∀ i : Fin n, X i ω ∉ C} from rfl,
      regular_iid_none μ X hiid C hC n]
    have hle : 1-prob μ {ω | X 0 ω ∈ C} ≤ (1/2 : ℝ) := by linarith
    have hnon : 0 ≤ 1-prob μ {ω | X 0 ω ∈ C} := sub_nonneg.mpr measureReal_le_one
    calc
      _ ≤ (1/2 : ℝ)^n := pow_le_pow_left₀ hnon hle n
      _ ≤ (1/2 : ℝ)^5 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ = 1/32 := by norm_num
  have hcompl := measureReal_add_measureReal_compl (μ := μ) hE
  have hunion : prob μ Eᶜ ≤ prob μ N₁+prob μ N₂ := by
    rw [hEA]
    exact measureReal_union_le _ _
  have hElower : (3/16 : ℝ) ≤ prob μ E := by
    have he : prob μ E+prob μ Eᶜ = 1 := by
      rw [probReal_univ] at hcompl
      exact hcompl
    linarith
  apply hElower.trans
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono
  rintro ω ⟨⟨i,hi⟩,⟨j,hj⟩⟩
  exact heavyMedian_bad_sample_deterministic hn (firstSample X n ω) ⟨i,hi⟩
    ⟨j,abs_le.mpr ⟨hj.1,hj.2⟩⟩


/-- A fixed lower tail probability above five rules out convergence to four. -/
theorem heavyMedian_cp_tail_obstruction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ)
    (hbad : ∀ᶠ k in atTop, (3/16 : ℝ) ≤ prob μ {ω | 5 < Z k ω}) :
    ¬ CP μ Z 4 := by
  intro hcp
  have hsmall := (hcp 1 (by norm_num)).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 3/16 by norm_num))
  have himpossible : ∀ᶠ k : ℕ in atTop, False := by
    filter_upwards [hbad, hsmall] with k hk hsmallk
    have hs : {ω | 5 < Z k ω} ⊆ {ω | (1 : ℝ) ≤ dist (Z k ω) 4} := by
      intro ω hω
      change 5 < Z k ω at hω
      rw [Set.mem_setOf_eq, Real.dist_eq]
      exact (by linarith : (1 : ℝ) ≤ Z k ω-4).trans (le_abs_self _)
    have hp : prob μ {ω | 5 < Z k ω} ≤
        prob μ {ω | (1 : ℝ) ≤ dist (Z k ω) 4} :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hs)
    linarith
  exact himpossible.exists.choose_spec

/-- The actual sample median has both normal weak limits, while its conditional
bootstrap variance fails to converge in probability to the limiting variance. -/
theorem heavy_median_bootstrap_variance_counterexample_final {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (hlaw : μ.map (X 0) = heavyBootstrapLaw) :
    CD μ (fun k ω => Real.sqrt (2*k+1)*sampleMedian (firstSample X (2*k+1) ω))
      (gaussianReal 0 4) ∧
    BootstrapWeakCP μ X (fun k => 2*k+1) (fun {n} => @sampleMedian n)
      (gaussianReal 0 4) ∧
    (∀ n : ℕ, Odd n → 5 ≤ n → (3/16 : ℝ) ≤ prob μ {ω |
      5 < (n : ℝ)*bootVar sampleMedian (firstSample X n ω)}) ∧
    ¬ CP μ (fun k ω => ((2*k+1 : ℕ) : ℝ)*bootVar sampleMedian
      (firstSample X (2*k+1) ω)) 4 := by
  have hlocal := heavyMedian_local_data μ X (hiid.1 0) hlaw
  have hw := local_median_weak μ X hiid 0 (fun _ => (1/4 : ℝ)) hlocal
  have hvar : (⟨1/(4*(1/4 : ℝ)^2), by positivity⟩ : ℝ≥0) = 4 := by
    apply Subtype.ext
    norm_num
  rw [hvar] at hw
  simp only [sub_zero] at hw
  have hodd : Tendsto (fun k : ℕ => 2*k+1) atTop atTop :=
    tendsto_atTop_mono (fun k => by dsimp; omega) tendsto_id
  have hmarginal : CD μ (fun k ω => Real.sqrt (2*k+1)*
      sampleMedian (firstSample X (2*k+1) ω)) (gaussianReal 0 4) := by
    intro x hx
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one] using (hw.1 x hx).comp hodd
  have hbootstrap : BootstrapWeakCP μ X (fun k => 2*k+1)
      (fun {n} => @sampleMedian n) (gaussianReal 0 4) := by
    intro f hf hb ε hε
    exact (hw.2 f hf hb ε hε).comp hodd
  have hbad : ∀ n : ℕ, Odd n → 5 ≤ n → (3/16 : ℝ) ≤ prob μ {ω |
      5 < (n : ℝ)*bootVar sampleMedian (firstSample X n ω)} := by
    intro n _ hn
    exact heavyMedian_bad_sample_probability μ X hiid hlaw n hn
  refine ⟨hmarginal, hbootstrap, hbad, ?_⟩
  apply heavyMedian_cp_tail_obstruction
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with k hk
  exact hbad (2*k+1) ⟨k, by omega⟩ (by omega)

end AronowAudit.P001.Wave1.TailA
