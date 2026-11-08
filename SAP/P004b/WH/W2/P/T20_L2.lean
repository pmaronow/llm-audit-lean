import SAP.P004b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2.P.T20_L2

open AronowAudit.P004
open scoped BigOperators Classical

private lemma abs_div_le_of_bound (x d q b : ℝ) (hb : 0 ≤ b)
    (hq : 0 < q) (hd : 0 < d) (hqd : q ≤ d) (hx : |x| ≤ b) :
    |x / d| ≤ b / q := by
  have hmul : |x| * q ≤ b * d := by
    calc
      |x| * q ≤ b * q := mul_le_mul_of_nonneg_right hx hq.le
      _ ≤ b * d := mul_le_mul_of_nonneg_left hqd hb
  have hdiv : |x| / d ≤ b / q := (div_le_div_iff₀ hd hq).2 hmul
  simpa [abs_div, abs_of_pos hd] using hdiv

private lemma raw_ht_bound {N : ℕ} (p b : ℝ) (R : CircleTable N)
    (hp : 0 < p ∧ p < 1) (hb : 0 ≤ b) (hR : ∀ i z, |R i z| ≤ b)
    (i : Fin N) (z : Assignment N) :
    |cltRaw p R false i z| ≤ b / min p (1-p) := by
  have hq : 0 < min p (1-p) := lt_min hp.1 (sub_pos.mpr hp.2)
  have hqp : min p (1-p) ≤ p := min_le_left _ _
  have hq1p : min p (1-p) ≤ 1-p := min_le_right _ _
  by_cases hz : z i = true
  · simpa [cltRaw, residualContrast, bit, hz] using
      (abs_div_le_of_bound (R i z) p (min p (1-p)) b hb hq hp.1 hqp (hR i z))
  · have hz' : z i = false := Bool.eq_false_of_not_eq_true hz
    have hd : 0 < 1-p := sub_pos.mpr hp.2
    simpa [cltRaw, residualContrast, bit, hz'] using
      (abs_div_le_of_bound (R i z) (1-p) (min p (1-p)) b hb hq hd hq1p (hR i z))

private lemma raw_linear_bound {N : ℕ} (p b : ℝ) (R : CircleTable N)
    (hp : 0 < p ∧ p < 1) (hb : 0 ≤ b) (hR : ∀ i z, |R i z| ≤ b)
    (hN : 0 < N) (i : Fin N) (z : Assignment N) :
    |cltRaw p R true i z| ≤ 2*b / min p (1-p) := by
  have hq : 0 < min p (1-p) := lt_min hp.1 (sub_pos.mpr hp.2)
  have hqp : min p (1-p) ≤ p := min_le_left _ _
  have hq1p : min p (1-p) ≤ 1-p := min_le_right _ _
  have hbt : |barMu (fun _ => p) R true| ≤ b :=
    AronowAudit.P004.Wave1.T42_barMu_bound p R hp hN b hR true
  have hbf : |barMu (fun _ => p) R false| ≤ b :=
    AronowAudit.P004.Wave1.T42_barMu_bound p R hp hN b hR false
  have hb2 : 0 ≤ 2*b := by positivity
  by_cases hz : z i = true
  · have hnum : |R i z - barMu (fun _ => p) R true| ≤ 2*b := by
      calc
        |R i z - barMu (fun _ => p) R true| ≤ |R i z| + |barMu (fun _ => p) R true| := abs_sub _ _
        _ ≤ b+b := add_le_add (hR i z) hbt
        _ = 2*b := by ring
    simpa [cltRaw, residualContrast, bit, hz] using
      (abs_div_le_of_bound (R i z - barMu (fun _ => p) R true)
        p (min p (1-p)) (2*b) hb2 hq hp.1 hqp hnum)
  · have hz' : z i = false := Bool.eq_false_of_not_eq_true hz
    have hd : 0 < 1-p := sub_pos.mpr hp.2
    have hnum : |R i z - barMu (fun _ => p) R false| ≤ 2*b := by
      calc
        |R i z - barMu (fun _ => p) R false| ≤ |R i z| + |barMu (fun _ => p) R false| := abs_sub _ _
        _ ≤ b+b := add_le_add (hR i z) hbf
        _ = 2*b := by ring
    simpa [cltRaw, residualContrast, bit, hz'] using
      (abs_div_le_of_bound (R i z - barMu (fun _ => p) R false)
        (1-p) (min p (1-p)) (2*b) hb2 hq hd hq1p hnum)

private lemma raw_bound {N : ℕ} (p b : ℝ) (R : CircleTable N)
    (hp : 0 < p ∧ p < 1) (hb : 0 ≤ b) (hR : ∀ i z, |R i z| ≤ b)
    (hN : 0 < N) (a : Bool) (i : Fin N) (z : Assignment N) :
    |cltRaw p R a i z| ≤ (if a then 2 else 1)*b / min p (1-p) := by
  cases a
  · simpa using raw_ht_bound p b R hp hb hR i z
  · simpa using raw_linear_bound p b R hp hb hR hN i z

end SAP.P004b.WH.W2.P.T20_L2

theorem SAP.P004b.WH.W2.T20_L2_proof : SAP.P004b.WH.W2.T20_L2 := by
  intro N p b R hN hp hb hR a i z
  cases a with
  | false =>
      have hr := SAP.P004b.WH.W2.P.T20_L2.raw_ht_bound p b R hp hb hR i z
      have he := AronowAudit.P004.Wave1.t18_expect_abs_le
        (fun _ : Fin N => p) (fun _ => hp) (cltRaw p R false i) (b / min p (1-p))
        (fun z' => SAP.P004b.WH.W2.P.T20_L2.raw_ht_bound p b R hp hb hR i z')
      change |cltRaw p R false i z - expect (fun _ => p) (cltRaw p R false i)| ≤
        2*b / min p (1-p)
      calc
        |cltRaw p R false i z - expect (fun _ => p) (cltRaw p R false i)| ≤
            |cltRaw p R false i z| + |expect (fun _ => p) (cltRaw p R false i)| := abs_sub _ _
        _ ≤ b / min p (1-p) + b / min p (1-p) := add_le_add hr he
        _ = 2*b / min p (1-p) := by ring
  | true =>
      have hr := SAP.P004b.WH.W2.P.T20_L2.raw_linear_bound p b R hp hb hR hN i z
      have he := AronowAudit.P004.Wave1.t18_expect_abs_le
        (fun _ : Fin N => p) (fun _ => hp) (cltRaw p R true i) (2*b / min p (1-p))
        (fun z' => SAP.P004b.WH.W2.P.T20_L2.raw_linear_bound p b R hp hb hR hN i z')
      change |cltRaw p R true i z - expect (fun _ => p) (cltRaw p R true i)| ≤
        4*b / min p (1-p)
      calc
        |cltRaw p R true i z - expect (fun _ => p) (cltRaw p R true i)| ≤
            |cltRaw p R true i z| + |expect (fun _ => p) (cltRaw p R true i)| := abs_sub _ _
        _ ≤ 2*b / min p (1-p) + 2*b / min p (1-p) := add_le_add hr he
        _ = 4*b / min p (1-p) := by ring
