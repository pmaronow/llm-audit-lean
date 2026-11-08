import SAP.P004a.WH.W1.Leaves
import AronowAudit.P004.Wave1.AreaSum.A1
import AronowAudit.P004.Wave1.AreaSum.A4
import AronowAudit.P004.Wave1.AreaSum.A5
import AronowAudit.P004.Wave1.AreaSum.A6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T5_L4

open MeasureTheory Set
open scoped BigOperators Classical ENNReal
noncomputable section

theorem max_sub_one_bounds (r l u : ℝ) (hl : 0 ≤ l) (hu : 0 ≤ u) :
    (l < max (r - 1) 0 ∧ max (r - 1) 0 ≤ u) ↔
      1 + l < r ∧ r ≤ 1 + u := by
  constructor
  · rintro ⟨hlo, hup⟩
    have hr : 1 < r := by
      by_contra h
      have hr' : r ≤ 1 := le_of_not_gt h
      rw [max_eq_right (by linarith : r - 1 ≤ 0)] at hlo
      linarith
    rw [max_eq_left (by linarith : 0 ≤ r - 1)] at hlo hup
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hlo, hup⟩
    have hr : 1 < r := by linarith
    rw [max_eq_left (by linarith : 0 ≤ r - 1)]
    exact ⟨by linarith, by linarith⟩

theorem refined_disk_region (i : Fin 2) :
    region (w1RefinedArea 0) i 0 = Metric.closedBall (areaBinaryCenter i) 1 := by
  ext x
  change Metric.infDist x (Metric.closedBall (areaBinaryCenter i) 1) ∈ ({0} : Set ℝ) ↔
    dist x (areaBinaryCenter i) ≤ 1
  rw [AronowAudit.P004.Wave1.AreaSum.a1_proof]
  rw [Set.mem_singleton_iff, max_eq_right_iff]
  constructor <;> intro h <;> linarith

theorem refined_annulus_region (j : Fin 11) (hj : j.val ≠ 0) (i : Fin 2) :
    region (w1RefinedArea j) i 0 =
      {x | 1 + (((j : ℝ) - 1) / 2) < dist x (areaBinaryCenter i) ∧
        dist x (areaBinaryCenter i) ≤ 1 + (j : ℝ) / 2} := by
  ext x
  have hjpos : (1 : ℝ) ≤ (j : ℝ) := by
    have hn : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr hj
    exact_mod_cast hn
  have hjfin : j ≠ 0 := by
    intro he
    apply hj
    exact congrArg Fin.val he
  change Metric.infDist x (Metric.closedBall (areaBinaryCenter i) 1) ∈ w1RefinedBand j ↔ _
  simp only [w1RefinedBand, if_neg hjfin, Set.mem_Ioc]
  rw [AronowAudit.P004.Wave1.AreaSum.a1_proof]
  exact max_sub_one_bounds _ _ _ (by positivity) (by positivity)

def oldBinIndex (j : Fin 11) : Fin 6 :=
  ⟨(j.val + 1) / 2, by omega⟩

theorem oldBinIndex_lower (j : Fin 11) :
    (oldBinIndex j : ℝ) ≤ 1 + (((j : ℝ) - 1) / 2) := by
  have hn : 2 * (oldBinIndex j).val ≤ j.val + 1 := by
    dsimp [oldBinIndex]
    omega
  have hr : (2 : ℝ) * (oldBinIndex j : ℝ) ≤ (j : ℝ) + 1 := by
    exact_mod_cast hn
  nlinarith

theorem oldBinIndex_upper (j : Fin 11) :
    1 + (j : ℝ) / 2 ≤ (oldBinIndex j : ℝ) + 1 := by
  have hn : j.val ≤ 2 * (oldBinIndex j).val := by
    dsimp [oldBinIndex]
    omega
  have hr : (j : ℝ) ≤ (2 : ℝ) * (oldBinIndex j : ℝ) := by
    exact_mod_cast hn
  linarith

theorem caseA_share_constant (j : Fin 6) (a : Bool) :
    w1AreaShares 0 j a = w1AreaShares 0 0 a := by
  cases a <;> norm_num [w1AreaShares]

theorem closedBall_volume (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.closedBall c r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [EuclideanSpace.volume_closedBall_fin_two,
    ENNReal.ofReal_mul Real.pi_nonneg, ENNReal.ofReal_pow hr]
  exact mul_comm _ _

theorem annulus_volume (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    volume {x | a < dist x c ∧ dist x c ≤ b} =
      ENNReal.ofReal (Real.pi * (b ^ 2 - a ^ 2)) := by
  have hset : {x | a < dist x c ∧ dist x c ≤ b} =
      Metric.closedBall c b \ Metric.closedBall c a := by
    ext x
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, Set.mem_sdiff, not_le]
    exact and_comm
  have hsub : Metric.closedBall c a ⊆ Metric.closedBall c b :=
    Metric.closedBall_subset_closedBall hab
  have hfinite : volume (Metric.closedBall c a) ≠ ⊤ := by
    rw [closedBall_volume c a ha]
    exact ENNReal.ofReal_ne_top
  rw [hset, measure_sdiff hsub Metric.isClosed_closedBall.measurableSet.nullMeasurableSet hfinite,
    closedBall_volume c b (le_trans ha hab), closedBall_volume c a ha,
    ← ENNReal.ofReal_sub _ (mul_nonneg Real.pi_nonneg (sq_nonneg a))]
  congr 1
  ring

theorem average_sector {P : SpatialPopulation 2 (EuclideanSpace ℝ (Fin 2))}
    (i : Fin 2) (z : Assignment 2) (S : Set (EuclideanSpace ℝ (Fin 2)))
    (c : EuclideanSpace ℝ (Fin 2)) (q area : ℝ)
    (hregion : region P i 0 = S) (hzeta : P.zeta = volume)
    (hmes : MeasurableSet S) (hsector : MeasurableSet {x | angularFraction c x < q})
    (hout : ∀ x, x ∈ S → P.outcome x z =
      ({y | angularFraction c y < q}).indicator (fun _ => (1 : ℝ)) x)
    (hvol : volume S = ENNReal.ofReal area)
    (hsectorvol : volume (S ∩ {x | angularFraction c x < q}) =
      ENNReal.ofReal (q * area)) (hq : 0 ≤ q) (harea : 0 < area) :
    circleAverage P 0 i z = q := by
  have hnum : (∫ x in S, P.outcome x z ∂volume) = q * area := by
    calc
      _ = ∫ x in S, ({y | angularFraction c y < q}).indicator
          (fun _ => (1 : ℝ)) x ∂volume := by
        apply setIntegral_congr_fun hmes
        exact hout
      _ = (volume (S ∩ {x | angularFraction c x < q})).toReal := by
        rw [setIntegral_indicator hsector, setIntegral_const]
        simp only [Measure.real, smul_eq_mul, mul_one]
      _ = q * area := by
        rw [hsectorvol, ENNReal.toReal_ofReal (mul_nonneg hq (le_of_lt harea))]
  change (∫ x in region P i 0, P.outcome x z ∂P.zeta) /
      (P.zeta (region P i 0)).toReal = q
  rw [hregion, hzeta, hnum, hvol,
    ENNReal.toReal_ofReal (le_of_lt harea)]
  apply (div_eq_iff (ne_of_gt harea)).2
  ring

end
end T5_L4
end P
end W1
end WH
end P004a
end SAP

open SAP.P004a.WH.W1.P.T5_L4
open MeasureTheory Set
open scoped BigOperators Classical ENNReal

theorem SAP.P004a.WH.W1.T5_L4_proof : SAP.P004a.WH.W1.T5_L4 := by
  intro hreal j i z
  classical
  rcases hreal with ⟨⟨_, _, hon, _, _, _, hreg, _, _, _, _⟩, _⟩
  let P := w1AreaPopulation (w1AreaShares 0)
  let c := areaBinaryCenter i
  let q := w1AreaShares 0 0 (z i)
  have hq0 : 0 ≤ q := by
    cases hz : z i <;> norm_num [q, w1AreaShares, hz]
  have hqhalf : q ≤ 1 / 2 := by
    cases hz : z i <;> norm_num [q, w1AreaShares, hz]
  have hqpos : 0 < q := by
    cases hz : z i <;> norm_num [q, w1AreaShares, hz]
  have hshare : ∀ k : Fin 6, w1AreaShares 0 k (z i) = q := by
    intro k
    exact (caseA_share_constant k (z i)).trans rfl
  have hzeta (k : Fin 11) : (w1RefinedArea k).zeta = volume := rfl
  by_cases hj : j = 0
  · subst j
    have hregion : region (w1RefinedArea 0) i 0 =
        Metric.closedBall c 1 := by
      simpa [c] using refined_disk_region i
    have hmes : MeasurableSet (Metric.closedBall c 1) := measurableSet_closedBall
    have hsector : MeasurableSet {x | angularFraction c x < q} :=
      measurableSet_lt (AronowAudit.P004.Wave1.AreaSum.angularFraction_measurable c)
        measurable_const
    have hout : ∀ x, x ∈ Metric.closedBall c 1 →
        (w1RefinedArea 0).outcome x z =
          ({y | angularFraction c y < q}).indicator (fun _ => (1 : ℝ)) x := by
      intro x hx
      have hxold : x ∈ region (w1AreaPopulation (w1AreaShares 0)) i ((0 : Fin 6) : ℝ) := by
        rw [hreg i 0]
        simpa [w1AreaBin] using hx
      have ho := hon i 0 x z hxold
      change P.outcome x z = if angularFraction c x < w1AreaShares 0 0 (z i) then 1 else 0 at ho
      rw [show P.outcome x z = (w1RefinedArea 0).outcome x z by rfl] at ho
      rw [show w1AreaShares 0 0 (z i) = q by rfl] at ho
      by_cases ha : angularFraction c x < q <;> simp [Set.indicator, ha, ho]
    have hvol : volume (Metric.closedBall c 1) =
        ENNReal.ofReal (Real.pi * 1 ^ 2) := closedBall_volume c 1 (by norm_num)
    have hsectorvol : volume (Metric.closedBall c 1 ∩ {x | angularFraction c x < q}) =
        ENNReal.ofReal (q * (Real.pi * 1 ^ 2)) := by
      have hh := AronowAudit.P004.Wave1.AreaSum.a5_proof.2 c q hq0 hqhalf
      convert hh using 1 <;> congr 1 <;> ring
    have havg := average_sector (P := w1RefinedArea 0) i z (Metric.closedBall c 1)
      c q (Real.pi * 1 ^ 2) hregion (hzeta 0) hmes hsector hout hvol hsectorvol
      hq0 (by positivity)
    simpa [c, q] using havg
  · have hjval : j.val ≠ 0 := by
      intro h
      apply hj
      exact Fin.ext h
    let k := oldBinIndex j
    let a := 1 + (((j : ℝ) - 1) / 2)
    let b := 1 + (j : ℝ) / 2
    let S : Set (EuclideanSpace ℝ (Fin 2)) :=
      {x | a < dist x c ∧ dist x c ≤ b}
    have hregion : region (w1RefinedArea j) i 0 = S := by
      simpa [S, a, b, c] using refined_annulus_region j hjval i
    have hmes : MeasurableSet S := by
      dsimp [S]
      exact (measurableSet_lt measurable_const (measurable_id.dist measurable_const)).inter
        (measurableSet_le (measurable_id.dist measurable_const) measurable_const)
    have hsector : MeasurableSet {x | angularFraction c x < q} :=
      measurableSet_lt (AronowAudit.P004.Wave1.AreaSum.angularFraction_measurable c)
        measurable_const
    have hkpos : k.val ≠ 0 := by
      dsimp [k, oldBinIndex]
      omega
    have hreg' : region P i (k : ℝ) = w1AreaBin c k.val := by
      simpa [P, c] using hreg i k
    have hout : ∀ x, x ∈ S → (w1RefinedArea j).outcome x z =
        ({y | angularFraction c y < q}).indicator (fun _ => (1 : ℝ)) x := by
      intro x hx
      have hx' : x ∈ region (w1RefinedArea j) i 0 := by simpa [hregion] using hx
      rw [refined_annulus_region j hjval i] at hx'
      rcases hx' with ⟨hxlo, hxhi⟩
      have hxold : x ∈ region P i (k : ℝ) := by
        rw [hreg']
        unfold w1AreaBin
        rw [if_neg hkpos]
        exact ⟨lt_of_le_of_lt (by simpa [k] using oldBinIndex_lower j) hxlo,
          le_trans hxhi (by simpa [k] using oldBinIndex_upper j)⟩
      have ho := hon i k x z hxold
      change P.outcome x z =
        if angularFraction c x < w1AreaShares 0 k (z i) then 1 else 0 at ho
      rw [show P.outcome x z = (w1RefinedArea j).outcome x z by rfl] at ho
      rw [hshare k] at ho
      by_cases ha' : angularFraction c x < q <;> simp [Set.indicator, ha', ho]
    have ha : 0 ≤ a := by
      dsimp [a]
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
        have hn : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr hjval
        exact_mod_cast hn
      linarith
    have hab : a ≤ b := by
      dsimp [a, b]
      linarith
    have harea : 0 < Real.pi * (b ^ 2 - a ^ 2) := by
      have hd : b ^ 2 - a ^ 2 = (2 * (j : ℝ) + 3) / 4 := by
        dsimp [a, b]
        ring
      rw [hd]
      positivity
    have hvol : volume S = ENNReal.ofReal (Real.pi * (b ^ 2 - a ^ 2)) := by
      simpa [S] using annulus_volume c a b ha hab
    have hsectorvol : volume (S ∩ {x | angularFraction c x < q}) =
        ENNReal.ofReal (q * (Real.pi * (b ^ 2 - a ^ 2))) := by
      have hh := AronowAudit.P004.Wave1.AreaSum.a4_proof c a b q ha hab hq0 hqhalf
      convert hh using 1 <;> congr 1 <;> ring
    have havg := average_sector (P := w1RefinedArea j) i z S c q
      (Real.pi * (b ^ 2 - a ^ 2)) hregion (hzeta j) hmes hsector hout hvol hsectorvol
      hq0 harea
    simpa [q] using havg
