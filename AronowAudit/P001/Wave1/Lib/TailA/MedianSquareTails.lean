import AronowAudit.P001.Wave1.Lib.TailA.MedianTailBounds
import AronowAudit.P001.Wave1.Lib.TailA.MedianMaximum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Square-tail control from a positive-order population moment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
namespace AronowAudit.P001.Wave1.TailA
open AronowAudit.P001.TailA AronowAudit.Literature
local instance instDecidableMedianSquareTails (p : Prop) : Decidable p := Classical.propDecidable p

/-- On good data the local conditional fourth moment is uniformly bounded; distant
resamples contribute only a polynomial maximum times an exponentially small probability.
The endpoint estimate explicitly requires the eventual size threshold. -/
theorem medianSquare_fourth_good {n : ℕ} [NeZero n] (hn : 0 < n)
    (P : Measure ℝ) [IsProbabilityMeasure P] (x : Fin n → ℝ)
    (m a r C B : ℝ) (ha : 0 < a) (hr : 0 < r) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hmax : ∀ i, |x i| ≤ B)
    (hlarge : 2*C ≤ a*r*Real.sqrt n)
    (hdata : Real.sqrt n * CDFDeviation P x ≤ C)
    (hInv : ∀ y : Fin n → ℝ, a * min |sampleMedian y-m| r ≤ CDFDeviation P y) :
    (∫ z, (Real.sqrt n * (sampleMedian (resample x z)-sampleMedian x))^4
      ∂UniformResampling n) ≤
      (8/a^4)*((2*C)^4+8192) +
        64*(n : ℝ)^2*B^4*Real.exp (-((a*r)^2/64)*(n : ℝ)) := by
  let D := fun z : Fin n → Fin n => Real.sqrt n * CDFDeviation
    (StatLean.ComputationalStatistics.empiricalMeasure x) (resample x z)
  let Z := fun z : Fin n → Fin n => Real.sqrt n *
    (sampleMedian (resample x z)-sampleMedian x)
  let q := a*r*Real.sqrt n/2
  let L := 16*(n : ℝ)^2*B^4
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hD0 : ∀ z, 0 ≤ D z := fun z => mul_nonneg hs.le (taila09_cdfDeviation_bounds hn _ _).1
  have hroot (y : Fin n → ℝ) :
      a * (Real.sqrt n * min |sampleMedian y-m| r) ≤
        Real.sqrt n * CDFDeviation P y := by
    convert mul_le_mul_of_nonneg_left (hInv y) hs.le using 1 <;> ring
  have hsmall : |sampleMedian x-m| < r := by
    by_contra hh
    have hx := hroot x
    rw [min_eq_right (le_of_not_gt hh)] at hx
    nlinarith [mul_pos (mul_pos ha hr) hs]
  have hxroot : a * (Real.sqrt n * |sampleMedian x-m|) ≤ C := by
    have hx := (hroot x).trans hdata
    rwa [min_eq_left hsmall.le] at hx
  have htotal (z : Fin n → Fin n) :
      a * (Real.sqrt n * min |sampleMedian (resample x z)-m| r) ≤ C + D z := by
    have ht := mul_le_mul_of_nonneg_left (medianTail_deviation_triangle hn P x (resample x z)) hs.le
    dsimp only [D]
    nlinarith [hroot (resample x z)]
  have hbound (z : Fin n → Fin n) :
      (Z z)^4 ≤ (8/a^4)*((2*C)^4+(D z)^4) +
        (if q ≤ D z then L else 0) := by
    by_cases hlocal : |sampleMedian (resample x z)-m| ≤ r
    · have hy := htotal z
      rw [min_eq_left hlocal] at hy
      have hab : |Z z| ≤ Real.sqrt n * |sampleMedian (resample x z)-m| +
          Real.sqrt n * |sampleMedian x-m| := by
        dsimp [Z]
        rw [abs_mul, abs_of_pos hs, ← mul_add]
        apply mul_le_mul_of_nonneg_left _ hs.le
        convert abs_sub (sampleMedian (resample x z)-m) (sampleMedian x-m) using 1 <;> congr 1 <;> ring
      have hz : |Z z| ≤ (2*C+D z)/a := by
        apply (le_div_iff₀ ha).2
        nlinarith [mul_le_mul_of_nonneg_left hab ha.le]
      have hp := add_pow_le (by positivity : 0 ≤ 2*C) (hD0 z) 4
      have hh : (Z z)^4 ≤ (8/a^4)*((2*C)^4+(D z)^4) := by
        calc
          (Z z)^4 = |Z z|^4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
          _ ≤ ((2*C+D z)/a)^4 := by gcongr
          _ = (1/a^4)*(2*C+D z)^4 := by ring
          _ ≤ (1/a^4)*(8*((2*C)^4+(D z)^4)) := by gcongr; norm_num at hp ⊢; exact hp
          _ = _ := by ring
      have hL0 : 0 ≤ (if q ≤ D z then L else 0) := by
        split_ifs
        · dsimp [L]; positivity
        · exact le_rfl
      linarith
    · have hy := htotal z
      rw [min_eq_right (le_of_not_ge hlocal)] at hy
      have he : q ≤ D z := by dsimp [q]; nlinarith
      rw [if_pos he]
      have hm1 := medianMaximum_median_bound hn x B hmax
      have hm2 := medianMaximum_median_bound hn (resample x z) B (fun i => hmax (z i))
      have hz : |Z z| ≤ 2*Real.sqrt n*B := by
        dsimp [Z]
        rw [abs_mul, abs_of_pos hs]
        have hh := abs_sub (sampleMedian (resample x z)) (sampleMedian x)
        nlinarith [mul_le_mul_of_nonneg_left hh hs.le]
      have hp : (Z z)^4 ≤ L := by
        calc
          (Z z)^4 = |Z z|^4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
          _ ≤ (2*Real.sqrt n*B)^4 := by gcongr
          _ = L := by
            have hs4 : (Real.sqrt (n : ℝ))^4 = (n : ℝ)^2 := by
              rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg n)]
            calc
              _ = 16*(Real.sqrt (n : ℝ))^4*B^4 := by ring
              _ = _ := by rw [hs4]
      have hh : 0 ≤ (8/a^4)*((2*C)^4+(D z)^4) := by positivity
      linarith
  have hI := integral_mono (μ := UniformResampling n)
    (show Integrable (fun z => (Z z)^4) _ from .of_finite)
    (show Integrable (fun z => (8/a^4)*((2*C)^4+(D z)^4)+(if q ≤ D z then L else 0)) _ from .of_finite)
    hbound
  have hD4 : (∫ z, (D z)^4 ∂UniformResampling n) ≤ 8192 := medianTail_resampling_fourth hn x
  have htail : prob (UniformResampling n) {z | q ≤ D z} ≤
      4*Real.exp (-((a*r)^2/64)*(n : ℝ)) := by
    have ht := medianTail_resampling_dkw hn x (d := q) (by dsimp [q]; positivity)
    have he : -(q^2)/16 = -((a*r)^2/64)*(n : ℝ) := by
      dsimp [q]
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
    rw [he] at ht
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top ht).trans_eq (ENNReal.toReal_ofReal (by positivity))
  have hInd : (∫ z, if q ≤ D z then L else 0 ∂UniformResampling n) =
      L * prob (UniformResampling n) {z | q ≤ D z} := by
    change (∫ z, ({z | q ≤ D z} : Set (Fin n → Fin n)).indicator
      (fun _ => L) z ∂UniformResampling n) = _
    rw [integral_indicator_const L (MeasurableSet.of_discrete)]
    simp [prob, Measure.real, mul_comm]
  rw [integral_add (show Integrable _ _ from .of_finite) (show Integrable _ _ from .of_finite),
    integral_const_mul, integral_add (integrable_const _) (show Integrable _ _ from .of_finite),
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul, hInd] at hI
  have hq := mul_le_mul_of_nonneg_left hD4 (by positivity : 0 ≤ 8/a^4)
  have ht := mul_le_mul_of_nonneg_left htail (by dsimp [L]; positivity : 0 ≤ L)
  dsimp only [Z] at hI
  dsimp only [L] at ht
  nlinarith

/-- Conditional truncation of the square is bounded by the fourth moment divided by K². -/
theorem medianSquare_tail_le_fourth {n : ℕ} (x : Fin n → ℝ) (K : ℝ) (hK : 0 < K) :
    bootstrapTestMean sampleMedian x (fun z => if K < |z| then z^2 else 0) ≤
      (∫ a, (Real.sqrt n*(sampleMedian (resample x a)-sampleMedian x))^4
        ∂UniformResampling n) / K^2 := by
  have he := uniform_resampling_mean n (fun a =>
    if K < |Real.sqrt n*(sampleMedian (resample x a)-sampleMedian x)| then
      (Real.sqrt n*(sampleMedian (resample x a)-sampleMedian x))^2 else 0)
  change (∫ a, _ ∂UniformResampling n) =
    bootstrapTestMean sampleMedian x (fun z => if K < |z| then z^2 else 0) at he
  rw [← he, ← integral_div]
  apply integral_mono (show Integrable _ _ from .of_finite) (show Integrable _ _ from .of_finite)
  intro a
  dsimp only
  generalize Real.sqrt n*(sampleMedian (resample x a)-sampleMedian x) = z
  split_ifs with hz
  · apply (le_div_iff₀ (sq_pos_of_pos hK)).2
    have hs : K^2 ≤ z^2 := by nlinarith [sq_abs z, abs_nonneg z]
    have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg z)
    nlinarith
  · positivity

/-- Positive-order moments suffice for conditional uniform integrability of the squared
root-size median. All size restrictions in the endpoint estimate are taken eventually. -/
theorem local_median_square_tails {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : IID μ X) (m : ℝ) (f : ℝ → ℝ) (hlocal : LocalMedianData μ X m f)
    (η : ℝ) (hη : 0 < η) (hmoment : Integrable (fun ω => |X 0 ω|^η) μ) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun K : ℕ => Filter.limsup (fun n => prob μ {ω | ε <
        bootstrapTestMean sampleMedian (firstSample X n ω)
          (fun z => if (K : ℝ) < |z| then z^2 else 0)}) atTop)
      atTop (nhds 0) := by
  let P := μ.map (X 0)
  letI instProbabilityMedianSquareP : IsProbabilityMeasure P :=
    (Measure.isProbabilityMeasure_map_iff (hiid.1 0).aemeasurable).mpr inferInstance
  have hP (t : ℝ) : (P (Set.Iic t)).toReal = cdf μ (X 0) t := by
    rw [show P = μ.map (X 0) from rfl, Measure.map_apply (hiid.1 0) measurableSet_Iic]
    rfl
  have hmed : cdf μ (X 0) m = 1/2 := by
    obtain ⟨δ, hδ, hf, hn, hm, hc, hp, hm', _⟩ := hlocal
    exact hm'
  have hp : 0 < f m := by obtain ⟨δ, hδ, hf, hn, hm, hc, hp, _⟩ := hlocal; exact hp
  obtain ⟨ρ, hρ, hslope⟩ := medianWeak_local_slopes μ X (hiid.1 0) m f hlocal
  let r := ρ/2
  let c := f m/2
  let a := c/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hgap : ∀ u ∈ Set.Icc 0 r,
      c*u ≤ (P (Set.Iic (m+u))).toReal-1/2 ∧
      c*u ≤ 1/2-(P (Set.Iic (m-u))).toReal := by
    intro u hu
    have hu0 := hu.1
    have hu2 := hu.2
    have huρ : u < ρ := by dsimp [r] at hu2; linarith
    have hplus : m+u ∈ Metric.ball m ρ := by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hu.1]
      exact huρ
    have hminus : m-u ∈ Metric.ball m ρ := by
      rw [Metric.mem_ball, Real.dist_eq]
      have he : m-u-m = -u := by ring
      rw [he, abs_neg, abs_of_nonneg hu.1]
      exact huρ
    rw [hP, hP]
    constructor
    · simpa only [hmed, add_sub_cancel_left] using (hslope _ hplus).2 (by linarith)
    · convert (hslope _ hminus).1 (by linarith) using 1 <;> simp only [c, hmed] <;> ring
  have hInv {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) :
      a * min |sampleMedian y-m| r ≤ CDFDeviation P y :=
    medianTail_inverse hn P y m c r hc hr hgap
  obtain ⟨b, hb, hmaxlim⟩ := medianMaximum_polynomial μ X hiid η hη hmoment
  let d := (a*r)^2/64
  have hd : 0 < d := by dsimp [d]; positivity
  have hrem : Tendsto (fun n : ℕ =>
      64*(n : ℝ)^2*((n : ℝ)^b)^4*Real.exp (-d*(n : ℝ))) atTop (nhds 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2+4*b) d hd).comp
      tendsto_natCast_atTop_atTop
    have h64 : Tendsto (fun _ : ℕ => (64 : ℝ)) atTop (nhds 64) := tendsto_const_nhds
    have hh' := h64.mul hh
    simp only [mul_zero] at hh'
    apply hh'.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have he : (n : ℝ)^2*((n : ℝ)^b)^4 = (n : ℝ)^(2+4*b) := by
      rw [← Real.rpow_natCast (n : ℝ) 2,
        ← Real.rpow_natCast ((n : ℝ)^b) 4,
        ← Real.rpow_mul hnR.le, ← Real.rpow_add hnR]
      congr 1
      ring
    dsimp only [Function.comp_def]
    rw [← he]
    ring
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro v hv
    apply Eventually.of_forall
    intro K
    apply hv.trans_le
    apply le_limsup_of_frequently_le
    · exact Frequently.of_forall fun n => ENNReal.toReal_nonneg
    · exact isBoundedUnder_of ⟨1, fun n => measureReal_le_one⟩
  · intro τ hτ
    let C := 16/τ
    have hC : 0 < C := by dsimp [C]; positivity
    let H := (8/a^4)*((2*C)^4+8192)+1
    have hH : 0 < H := by dsimp [H]; positivity
    obtain ⟨K₀, hK₀⟩ := exists_nat_gt (max 1 (H/ε))
    filter_upwards [eventually_ge_atTop K₀] with K hK
    have hKR : (K₀ : ℝ) ≤ K := Nat.cast_le.mpr hK
    have hK1 : 1 < (K : ℝ) := (le_max_left _ _).trans_lt (hK₀.trans_le hKR)
    have hHK : H ≤ ε*(K : ℝ)^2 := by
      have hh : H/ε < (K : ℝ) := (le_max_right _ _).trans_lt (hK₀.trans_le hKR)
      have hh' : H < ε*(K : ℝ) := by simpa only [mul_comm] using (div_lt_iff₀ hε).mp hh
      nlinarith
    apply lt_of_le_of_lt (b := τ/2) _ (by linarith)
    apply limsup_le_of_le
      (isCoboundedUnder_le_of_le atTop (fun _ => ENNReal.toReal_nonneg))
    have hlarge : ∀ᶠ n : ℕ in atTop, 2*C ≤ a*r*Real.sqrt n :=
      ((Tendsto.const_mul_atTop (mul_pos ha hr) Real.tendsto_sqrt_atTop).comp
        tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2*C))
    have hR := (tendsto_order.mp hrem).2 1 (by norm_num)
    have hM := (tendsto_order.mp hmaxlim).2 (τ/4) (by positivity)
    filter_upwards [eventually_gt_atTop 0, hlarge, hR, hM] with n hn hnlarge hnR hnM
    letI instNonzeroMedianSquare : NeZero n := ⟨hn.ne'⟩
    have hCDF := (cdf_deviation_root_n_tail μ hn P
      (fun i : Fin n => X i) (fun i => hiid.1 i)
      (hiid.2.1.precomp Fin.val_injective) (fun i => (hiid.2.2 i).map_eq) C hC).2
    have hsub : {ω | ε < bootstrapTestMean sampleMedian (firstSample X n ω)
        (fun z => if (K : ℝ) < |z| then z^2 else 0)} ⊆
      {ω | C < Real.sqrt n*CDFDeviation P (firstSample X n ω)} ∪
      {ω | ∃ i : Fin n, (n : ℝ)^b < |X i ω|} := by
      intro ω hω
      by_contra hbad
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_exists] at hbad
      have hfourth := medianSquare_fourth_good hn P (firstSample X n ω)
        m a r C ((n : ℝ)^b) ha hr hC.le (Real.rpow_nonneg (Nat.cast_nonneg n) b)
        (fun i => hbad.2 i) hnlarge hbad.1 (hInv hn)
      have hh : (∫ z, (Real.sqrt n*(sampleMedian (resample (firstSample X n ω) z)-
          sampleMedian (firstSample X n ω)))^4 ∂UniformResampling n) ≤ H := by
        dsimp [H]
        exact hfourth.trans (by dsimp [d] at hnR; linarith)
      have ht := (medianSquare_tail_le_fourth (firstSample X n ω) K (by linarith)).trans
        (div_le_div_of_nonneg_right hh (sq_nonneg (K : ℝ)))
      have hfinal : H/(K : ℝ)^2 ≤ ε := (div_le_iff₀ (sq_pos_of_pos (by linarith))).mpr hHK
      exact (not_lt_of_ge (ht.trans hfinal)) hω
    have hu := (measureReal_mono hsub (measure_ne_top μ _)).trans (measureReal_union_le _ _)
    change prob μ _ ≤ _
    change prob μ _ ≤ prob μ _ + prob μ _ at hu
    change prob μ _ < τ/4 at hnM
    have hCC : 4/C = τ/4 := by dsimp [C]; field_simp; norm_num
    rw [hCC] at hCDF
    change prob μ {ω | C < Real.sqrt n*CDFDeviation P (firstSample X n ω)} ≤ τ/4 at hCDF
    linarith only [hu, hCDF, hnM]

end AronowAudit.P001.Wave1.TailA
