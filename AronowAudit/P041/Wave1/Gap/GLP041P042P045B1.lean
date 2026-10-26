import AronowAudit.P041.Wave1.Gap.GP041P042P045B1

/-! P041-T11: normal probability bounds for the three former-senator
rounding rectangles and their printed centres, using Gaussian integrals
and Taylor bounds. -/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace AronowAudit.P041.Wave1

set_option maxRecDepth 10000

/-- Endpoint logarithms certified by the finite atanh series. -/
lemma p041t11_log_former_l :
    (0.370339306132:ℝ) ≤ -Real.log 0.6905 ∧ -Real.log 0.6905 ≤ 0.370339306133 := by
  have hc := neg_log_certificate 0.6905 (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

lemma p041t11_log_former_u :
    (0.368892127877:ℝ) ≤ -Real.log 0.6915 ∧ -Real.log 0.6915 ≤ 0.368892127878 := by
  have hc := neg_log_certificate 0.6915 (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

lemma p041t11_log_living_l :
    (0.255537619125:ℝ) ≤ -Real.log 0.7745 ∧ -Real.log 0.7745 ≤ 0.255537619126 := by
  have hc := neg_log_certificate 0.7745 (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

lemma p041t11_log_living_u :
    (0.254247296365:ℝ) ≤ -Real.log 0.7755 ∧ -Real.log 0.7755 ≤ 0.254247296366 := by
  have hc := neg_log_certificate 0.7755 (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

lemma p041t11_log_deceased_l :
    (0.467606504646:ℝ) ≤ -Real.log 0.6265 ∧ -Real.log 0.6265 ≤ 0.467606504647 := by
  have hc := neg_log_certificate 0.6265 (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

lemma p041t11_log_deceased_u :
    (0.466011607976:ℝ) ≤ -Real.log 0.6275 ∧ -Real.log 0.6275 ≤ 0.466011607977 := by
  have hc := neg_log_certificate 0.6275 (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

lemma p041t11_log_former_c :
    (0.369615455214:ℝ) ≤ -Real.log 0.691 ∧ -Real.log 0.691 ≤ 0.369615455215 := by
  have hc := neg_log_certificate 0.691 (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

lemma p041t11_log_living_c :
    (0.254892249628:ℝ) ≤ -Real.log 0.775 ∧ -Real.log 0.775 ≤ 0.254892249629 := by
  have hc := neg_log_certificate 0.775 (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

lemma p041t11_log_deceased_c :
    (0.466808738349:ℝ) ≤ -Real.log 0.627 ∧ -Real.log 0.627 ≤ 0.466808738350 := by
  have hc := neg_log_certificate 0.627 (by norm_num) (by norm_num) 10
  norm_num [logSeries, Finset.sum_range_succ] at hc
  constructor <;> linarith

/-- Monotone numerator bounds and positive denominators bound a whole rectangle. -/
lemma p041t11_rectangle_stat (l u sl su a b L U h s : ℝ)
    (hl : 0 < l) (hlh : l ≤ h) (hhu : h ≤ u) (hu : u < 1)
    (hsl : 0 < sl) (hls : sl ≤ s) (hsu : s ≤ su)
    (hlog : -1 ≤ Real.log l) (hL : L ≤ -Real.log u) (hU : -Real.log l ≤ U)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hlo : a*su ≤ u*L) (hhi : l*U ≤ b*sl) :
    a ≤ |hazardWald h s| ∧ |hazardWald h s| ≤ b := by
  have hh0 : 0 < h := lt_of_lt_of_le hl hlh
  have hs0 : 0 < s := lt_of_lt_of_le hsl hls
  have hu0 : 0 ≤ u := le_trans hh0.le hhu
  obtain ⟨hnl,hnu⟩ := wald_numerator_above l u h hl hlh hhu hlog
  rw [abs_hazard_wald h s hh0 (lt_of_le_of_lt hhu hu) hs0]
  constructor
  · apply (le_div_iff₀ hs0).mpr
    calc
      a*s ≤ a*su := mul_le_mul_of_nonneg_left hsu ha
      _ ≤ u*L := hlo
      _ ≤ u*(-Real.log u) := mul_le_mul_of_nonneg_left hL hu0
      _ ≤ h*(-Real.log h) := hnl
  · apply (div_le_iff₀ hs0).mpr
    calc
      h*(-Real.log h) ≤ l*(-Real.log l) := hnu
      _ ≤ l*U := mul_le_mul_of_nonneg_left hU hl.le
      _ ≤ b*sl := hhi
      _ ≤ b*s := mul_le_mul_of_nonneg_left hls hb

lemma p041t11_former_rectangle (h s : ℝ)
    (hh : printedInterval 0.691 h) (hs : printedInterval 0.318 s) :
    0.800907084 ≤ |hazardWald h s| ∧ |hazardWald h s| ≤ 0.805415090 := by
  rcases hh with ⟨hlo,hhi⟩
  rcases hs with ⟨slo,shi⟩
  exact p041t11_rectangle_stat 0.6905 0.6915 0.3175 0.3185 0.800907084 0.805415090
    0.368892127877 0.370339306133 h s (by norm_num) (by linarith) (by linarith)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by linarith [p041t11_log_former_l.2]) p041t11_log_former_u.1
    p041t11_log_former_l.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma p041t11_living_rectangle (h s : ℝ)
    (hh : printedInterval 0.775 h) (hs : printedInterval 0.503 s) :
    0.391596381 ≤ |hazardWald h s| ∧ |hazardWald h s| ≤ 0.393858480 := by
  rcases hh with ⟨hlo,hhi⟩
  rcases hs with ⟨slo,shi⟩
  exact p041t11_rectangle_stat 0.7745 0.7755 0.5025 0.5035 0.391596381 0.393858480
    0.254247296365 0.255537619126 h s (by norm_num) (by linarith) (by linarith)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by linarith [p041t11_log_living_l.2]) p041t11_log_living_u.1
    p041t11_log_living_l.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma p041t11_deceased_rectangle (h s : ℝ)
    (hh : printedInterval 0.627 h) (hs : printedInterval 0.406 s) :
    0.719366012 ≤ |hazardWald h s| ∧ |hazardWald h s| ≤ 0.722454933 := by
  rcases hh with ⟨hlo,hhi⟩
  rcases hs with ⟨slo,shi⟩
  exact p041t11_rectangle_stat 0.6265 0.6275 0.4055 0.4065 0.719366012 0.722454933
    0.466011607976 0.467606504647 h s (by norm_num) (by linarith) (by linarith)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by linarith [p041t11_log_deceased_l.2]) p041t11_log_deceased_u.1
    p041t11_log_deceased_l.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma p041t11_former_centre :
    0.803158111 ≤ |hazardWald 0.691 0.318| ∧ |hazardWald 0.691 0.318| ≤ 0.803158112 := by
  rw [abs_hazard_wald 0.691 0.318 (by norm_num) (by norm_num) (by norm_num)]
  have hc := p041t11_log_former_c
  constructor
  · apply (le_div_iff₀ (by norm_num : (0:ℝ) < 0.318)).mpr
    linarith [hc.1]
  · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 0.318)).mpr
    linarith [hc.2]

lemma p041t11_living_centre :
    0.392726627 ≤ |hazardWald 0.775 0.503| ∧ |hazardWald 0.775 0.503| ≤ 0.392726628 := by
  rw [abs_hazard_wald 0.775 0.503 (by norm_num) (by norm_num) (by norm_num)]
  have hc := p041t11_log_living_c
  constructor
  · apply (le_div_iff₀ (by norm_num : (0:ℝ) < 0.503)).mpr
    linarith [hc.1]
  · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 0.503)).mpr
    linarith [hc.2]

lemma p041t11_deceased_centre :
    0.720909061 ≤ |hazardWald 0.627 0.406| ∧ |hazardWald 0.627 0.406| ≤ 0.720909062 := by
  rw [abs_hazard_wald 0.627 0.406 (by norm_num) (by norm_num) (by norm_num)]
  have hc := p041t11_log_deceased_c
  constructor
  · apply (le_div_iff₀ (by norm_num : (0:ℝ) < 0.406)).mpr
    linarith [hc.1]
  · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 0.406)).mpr
    linarith [hc.2]

/-- A rational interval certificate for the actual Gaussian tail.
The hypotheses are finite degree-8/9 Taylor polynomial inequalities. -/
lemma p041t11_tail_interval (a b lo hi x : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hax : a ≤ x) (hxb : x ≤ b)
    (hpa : 0 ≤ normal_intPoly 9 a) (hpb : 0 ≤ normal_intPoly 9 b)
    (hlo : lo ≤ 1 - 2*0.39895*normal_intPoly 8 b)
    (hhi : 1 - 2*0.39894*normal_intPoly 9 a ≤ hi) :
    lo ≤ 2*cdf (gaussianReal 0 1) (-x) ∧ 2*cdf (gaussianReal 0 1) (-x) ≤ hi := by
  have hla := normal_tail_bound 4 a ha hpa
  have hlb := normal_tail_bound 4 b hb hpb
  exact ⟨le_trans hlo (le_trans hlb.1 (normal_tail_antitone hxb)),
    le_trans (normal_tail_antitone hax) (le_trans hla.2 hhi)⟩

lemma p041t11_former_rectangle_p (z : ℝ)
    (hz : 0.800907084 ≤ |z| ∧ |z| ≤ 0.805415090) :
    0.4205 ≤ normalTwoSided z ∧ normalTwoSided z ≤ 0.4232 := by
  exact p041t11_tail_interval 0.800907084 0.805415090 0.4205 0.4232 |z|
    (by norm_num) (by norm_num) hz.1 hz.2
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])

lemma p041t11_living_rectangle_p (z : ℝ)
    (hz : 0.391596381 ≤ |z| ∧ |z| ≤ 0.393858480) :
    0.6936 ≤ normalTwoSided z ∧ normalTwoSided z ≤ 0.6954 := by
  exact p041t11_tail_interval 0.391596381 0.393858480 0.6936 0.6954 |z|
    (by norm_num) (by norm_num) hz.1 hz.2
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])

lemma p041t11_deceased_rectangle_p (z : ℝ)
    (hz : 0.719366012 ≤ |z| ∧ |z| ≤ 0.722454933) :
    0.4700 ≤ normalTwoSided z ∧ normalTwoSided z ≤ 0.4720 := by
  exact p041t11_tail_interval 0.719366012 0.722454933 0.4700 0.4720 |z|
    (by norm_num) (by norm_num) hz.1 hz.2
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])

lemma p041t11_former_centre_p (z : ℝ)
    (hz : 0.803158111 ≤ |z| ∧ |z| ≤ 0.803158112) :
    0.42185 ≤ normalTwoSided z ∧ normalTwoSided z ≤ 0.42195 := by
  exact p041t11_tail_interval 0.803158111 0.803158112 0.42185 0.42195 |z|
    (by norm_num) (by norm_num) hz.1 hz.2
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])

lemma p041t11_living_centre_p (z : ℝ)
    (hz : 0.392726627 ≤ |z| ∧ |z| ≤ 0.392726628) :
    0.69445 ≤ normalTwoSided z ∧ normalTwoSided z ≤ 0.69455 := by
  exact p041t11_tail_interval 0.392726627 0.392726628 0.69445 0.69455 |z|
    (by norm_num) (by norm_num) hz.1 hz.2
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])

lemma p041t11_deceased_centre_p (z : ℝ)
    (hz : 0.720909061 ≤ |z| ∧ |z| ≤ 0.720909062) :
    0.47095 ≤ normalTwoSided z ∧ normalTwoSided z ≤ 0.47105 := by
  exact p041t11_tail_interval 0.720909061 0.720909062 0.47095 0.47105 |z|
    (by norm_num) (by norm_num) hz.1 hz.2
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [normal_intPoly, Finset.sum_range_succ, Nat.factorial])

theorem printed_former_normal_p_enclosures_proof :
    (∀ h s : ℝ, printedInterval 0.691 h → printedInterval 0.318 s →
      0.4205 ≤ normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) ≤ 0.4232) ∧
    (∀ h s : ℝ, printedInterval 0.775 h → printedInterval 0.503 s →
      0.6936 ≤ normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) ≤ 0.6954) ∧
    (∀ h s : ℝ, printedInterval 0.627 h → printedInterval 0.406 s →
      0.4700 ≤ normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) ≤ 0.4720) ∧
    abs (abs (hazardWald 0.691 0.318) - 0.8032) ≤ 0.00005 ∧
    abs (abs (hazardWald 0.775 0.503) - 0.3927) ≤ 0.00005 ∧
    abs (abs (hazardWald 0.627 0.406) - 0.7209) ≤ 0.00005 ∧
    |normalTwoSided (hazardWald 0.691 0.318) - 0.4219| ≤ 0.00005 ∧
    |normalTwoSided (hazardWald 0.775 0.503) - 0.6945| ≤ 0.00005 ∧
    |normalTwoSided (hazardWald 0.627 0.406) - 0.4710| ≤ 0.00005 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h s hh hs
    exact p041t11_former_rectangle_p _ (p041t11_former_rectangle h s hh hs)
  · intro h s hh hs
    exact p041t11_living_rectangle_p _ (p041t11_living_rectangle h s hh hs)
  · intro h s hh hs
    exact p041t11_deceased_rectangle_p _ (p041t11_deceased_rectangle h s hh hs)
  · apply abs_le.mpr
    constructor <;> linarith [p041t11_former_centre.1, p041t11_former_centre.2]
  · apply abs_le.mpr
    constructor <;> linarith [p041t11_living_centre.1, p041t11_living_centre.2]
  · apply abs_le.mpr
    constructor <;> linarith [p041t11_deceased_centre.1, p041t11_deceased_centre.2]
  · obtain ⟨hl,hu⟩ := p041t11_former_centre_p _ p041t11_former_centre
    apply abs_le.mpr
    constructor <;> linarith
  · obtain ⟨hl,hu⟩ := p041t11_living_centre_p _ p041t11_living_centre
    apply abs_le.mpr
    constructor <;> linarith
  · obtain ⟨hl,hu⟩ := p041t11_deceased_centre_p _ p041t11_deceased_centre
    apply abs_le.mpr
    constructor <;> linarith

end AronowAudit.P041.Wave1
