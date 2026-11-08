import SAP.P037a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W1.P.T3_L4

open SAP.P037a.WH.W1
noncomputable section

private def sqrtLo : ℝ := 250662827463100050241 / 100000000000000000000
private def sqrtHi : ℝ := 250662827463100050243 / 100000000000000000000

private theorem sqrt_bounds : sqrtLo < Real.sqrt (2 * Real.pi) ∧
    Real.sqrt (2 * Real.pi) < sqrtHi := by
  have hpiLo := Real.pi_gt_d20
  have hpiHi := Real.pi_lt_d20
  have hlo : sqrtLo ^ 2 < 2 * Real.pi := by
    norm_num [sqrtLo] at hpiLo ⊢
    nlinarith
  have hhi : 2 * Real.pi < sqrtHi ^ 2 := by
    norm_num [sqrtHi] at hpiHi ⊢
    nlinarith
  have hrad : 0 ≤ 2 * Real.pi := by positivity
  have hs : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi := Real.sq_sqrt hrad
  have hloPos : 0 < sqrtLo := by norm_num [sqrtLo]
  have hhiPos : 0 < sqrtHi := by norm_num [sqrtHi]
  have hsPos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  constructor
  · by_contra hn
    have hle : Real.sqrt (2 * Real.pi) ≤ sqrtLo := le_of_not_gt hn
    have hm := mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hsPos.le hloPos.le)
    nlinarith
  · by_contra hn
    have hle : sqrtHi ≤ Real.sqrt (2 * Real.pi) := le_of_not_gt hn
    have hm := mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hhiPos.le hsPos.le)
    nlinarith

private theorem tail_lower (hencl : normalTaylorEnclosure) (z : ℝ) (hz : 0 ≤ z)
    (hg : 0 ≤ gaussianTaylorIntegral 24 z) :
    1 - 2 * gaussianTaylorIntegral 24 z / sqrtLo ≤ wholeNormalTail z := by
  have hs := sqrt_bounds.1
  have hd : 2 * gaussianTaylorIntegral 24 z / Real.sqrt (2 * Real.pi) ≤
      2 * gaussianTaylorIntegral 24 z / sqrtLo :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num [sqrtLo]) hs.le
  have he := hencl z hz
  linarith [he.1]

private theorem tail_upper (hencl : normalTaylorEnclosure) (z : ℝ) (hz : 0 ≤ z)
    (hg : 0 ≤ gaussianTaylorIntegral 25 z) :
    wholeNormalTail z ≤ 1 - 2 * gaussianTaylorIntegral 25 z / sqrtHi := by
  have hs := sqrt_bounds.2
  have hsp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hd : 2 * gaussianTaylorIntegral 25 z / sqrtHi ≤
      2 * gaussianTaylorIntegral 25 z / Real.sqrt (2 * Real.pi) :=
    div_le_div_of_nonneg_left (by positivity) hsp hs.le
  have he := hencl z hz
  linarith [he.2]

private theorem cert_19 :
    0 ≤ gaussianTaylorIntegral 24 (19/10 : ℝ) ∧
    0 ≤ gaussianTaylorIntegral 25 (19/10 : ℝ) ∧
    (5743/100000 - 1/200000 : ℝ) <
      1 - 2 * gaussianTaylorIntegral 24 (19/10 : ℝ) / sqrtLo ∧
    1 - 2 * gaussianTaylorIntegral 25 (19/10 : ℝ) / sqrtHi <
      (5743/100000 + 1/200000 : ℝ) := by
  norm_num [gaussianTaylorIntegral, sqrtLo, sqrtHi]

private theorem cert_2 :
    0 ≤ gaussianTaylorIntegral 24 (2 : ℝ) ∧
    0 ≤ gaussianTaylorIntegral 25 (2 : ℝ) ∧
    (4550/100000 - 1/200000 : ℝ) <
      1 - 2 * gaussianTaylorIntegral 24 (2 : ℝ) / sqrtLo ∧
    1 - 2 * gaussianTaylorIntegral 25 (2 : ℝ) / sqrtHi <
      (4550/100000 + 1/200000 : ℝ) := by
  norm_num [gaussianTaylorIntegral, sqrtLo, sqrtHi]

private theorem cert_57_28 :
    0 ≤ gaussianTaylorIntegral 24 (57/28 : ℝ) ∧
    0 ≤ gaussianTaylorIntegral 25 (57/28 : ℝ) ∧
    (4178/100000 - 1/200000 : ℝ) <
      1 - 2 * gaussianTaylorIntegral 24 (57/28 : ℝ) / sqrtLo ∧
    1 - 2 * gaussianTaylorIntegral 25 (57/28 : ℝ) / sqrtHi <
      (4178/100000 + 1/200000 : ℝ) := by
  norm_num [gaussianTaylorIntegral, sqrtLo, sqrtHi]

private theorem cert_57_34 :
    0 ≤ gaussianTaylorIntegral 24 (57/34 : ℝ) ∧
    0 ≤ gaussianTaylorIntegral 25 (57/34 : ℝ) ∧
    (9365/100000 - 1/200000 : ℝ) <
      1 - 2 * gaussianTaylorIntegral 24 (57/34 : ℝ) / sqrtLo ∧
    1 - 2 * gaussianTaylorIntegral 25 (57/34 : ℝ) / sqrtHi <
      (9365/100000 + 1/200000 : ℝ) := by
  norm_num [gaussianTaylorIntegral, sqrtLo, sqrtHi]

private theorem cert_11_7 :
    0 ≤ gaussianTaylorIntegral 24 (11/7 : ℝ) ∧
    0 ≤ gaussianTaylorIntegral 25 (11/7 : ℝ) ∧
    (11608/100000 - 1/200000 : ℝ) <
      1 - 2 * gaussianTaylorIntegral 24 (11/7 : ℝ) / sqrtLo ∧
    1 - 2 * gaussianTaylorIntegral 25 (11/7 : ℝ) / sqrtHi <
      (11608/100000 + 1/200000 : ℝ) := by
  norm_num [gaussianTaylorIntegral, sqrtLo, sqrtHi]

private theorem cert_13_5 :
    0 ≤ gaussianTaylorIntegral 24 (13/5 : ℝ) ∧
    0 ≤ gaussianTaylorIntegral 25 (13/5 : ℝ) ∧
    (932/100000 - 1/200000 : ℝ) <
      1 - 2 * gaussianTaylorIntegral 24 (13/5 : ℝ) / sqrtLo ∧
    1 - 2 * gaussianTaylorIntegral 25 (13/5 : ℝ) / sqrtHi <
      (932/100000 + 1/200000 : ℝ) := by
  norm_num [gaussianTaylorIntegral, sqrtLo, sqrtHi]

private theorem cert_195996 :
    0 ≤ gaussianTaylorIntegral 24 (195996/100000 : ℝ) ∧
    (1/20 : ℝ) <
      1 - 2 * gaussianTaylorIntegral 24 (195996/100000 : ℝ) / sqrtLo := by
  norm_num [gaussianTaylorIntegral, sqrtLo]

private theorem cert_195997 :
    0 ≤ gaussianTaylorIntegral 25 (195997/100000 : ℝ) ∧
    1 - 2 * gaussianTaylorIntegral 25 (195997/100000 : ℝ) / sqrtHi <
      (1/20 : ℝ) := by
  norm_num [gaussianTaylorIntegral, sqrtHi]

private theorem tail_close (hencl : normalTaylorEnclosure) (z c : ℝ)
    (hz : 0 ≤ z) (hg24 : 0 ≤ gaussianTaylorIntegral 24 z)
    (hg25 : 0 ≤ gaussianTaylorIntegral 25 z)
    (hlo : c - 1/200000 < 1 - 2 * gaussianTaylorIntegral 24 z / sqrtLo)
    (hhi : 1 - 2 * gaussianTaylorIntegral 25 z / sqrtHi < c + 1/200000) :
    |wholeNormalTail z - c| < 1/200000 := by
  have hl := tail_lower hencl z hz hg24
  have hu := tail_upper hencl z hz hg25
  rw [abs_lt]
  constructor <;> linarith

end
end SAP.P037a.WH.W1.P.T3_L4

open SAP.P037a.WH.W1.P.T3_L4

theorem SAP.P037a.WH.W1.T3_L4_proof : SAP.P037a.WH.W1.T3_L4 := by
  intro hencl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc := cert_19
    have hl := tail_lower hencl (19/10 : ℝ) (by norm_num) hc.1
    linarith [hc.2.2.1]
  · have hc := cert_2
    have hu := tail_upper hencl (2 : ℝ) (by norm_num) hc.2.1
    linarith [hc.2.2.2]
  · have hc := cert_195996
    have hl := tail_lower hencl (195996/100000 : ℝ) (by norm_num) hc.1
    linarith [hc.2]
  · have hc := cert_195997
    have hu := tail_upper hencl (195997/100000 : ℝ) (by norm_num) hc.1
    linarith [hc.2]
  · have hc := cert_57_28
    exact tail_close hencl (57/28 : ℝ) (4178/100000 : ℝ) (by norm_num)
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  · have hc := cert_57_34
    exact tail_close hencl (57/34 : ℝ) (9365/100000 : ℝ) (by norm_num)
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  · have hc := cert_2
    exact tail_close hencl (2 : ℝ) (4550/100000 : ℝ) (by norm_num)
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  · have hc := cert_19
    exact tail_close hencl (19/10 : ℝ) (5743/100000 : ℝ) (by norm_num)
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  · have hc := cert_11_7
    exact tail_close hencl (11/7 : ℝ) (11608/100000 : ℝ) (by norm_num)
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  · have hc := cert_13_5
    exact tail_close hencl (13/5 : ℝ) (932/100000 : ℝ) (by norm_num)
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
