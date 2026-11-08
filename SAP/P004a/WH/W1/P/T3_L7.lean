import SAP.P004a.WH.W1.Leaves
import AronowAudit.P004.Wave1.ObservationalCoverage.O12
import AronowAudit.P004.Wave1.DesignLimits.DL9

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P004a.WH.W1.P.T3_L7

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P004
open AronowAudit.P004.Wave1.ObservationalCoverage
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section

theorem inProb_multiples {p : ∀ N, Fin N → ℝ} {U : ∀ N, Assignment N → ℝ}
    (h : AronowAudit.P004.InProb p U) :
    W1InProb (fun r => 8*r) (fun r => p (8*r)) (fun r z => U (8*r) z) := by
  intro ε hε
  exact (h ε hε).comp (SAP.P004a.WH.W1.multiples_tendsto 8 (by omega))

theorem w1_inProb_congr {n : ℕ → ℕ} {p : ∀ k, Fin (n k) → ℝ}
    {U V : ∀ k, Assignment (n k) → ℝ}
    (he : ∀ᶠ k in atTop, ∀ z, U k z = V k z) (hU : W1InProb n p U) :
    W1InProb n p V := by
  intro ε hε
  refine (hU ε hε).congr' ?_
  filter_upwards [he] with k hk
  exact prob_congr _ _ _ (fun z => by rw [hk z])

theorem deterministic_inProb {n : ℕ → ℕ} {p : ∀ k, Fin (n k) → ℝ}
    {a : ℕ → ℝ} (ha : Tendsto a atTop (nhds 0)) :
    W1InProb n p (fun k _ => a k) := by
  intro ε hε
  have hε' : |(0 : ℝ)| < ε := by simpa using hε
  have hsmall : ∀ᶠ k in atTop, |a k| < ε :=
    ha.abs.eventually (eventually_lt_nhds hε')
  have heq : (fun k => prob (p k) (fun _ => ε < |a k|)) =ᶠ[atTop]
      (fun _ : ℕ => (0 : ℝ)) := by
    filter_upwards [hsmall] with k hk
    simp only [prob, not_lt_of_ge hk.le, if_false]
    exact AronowAudit.P004.expect_const (p k) 0
  exact (tendsto_congr' heq).2 tendsto_const_nhds

theorem w1_dl9 {n : ℕ → ℕ} (p : ∀ k, Fin (n k) → ℝ)
    (hp : ∀ k i, 0 < p k i ∧ p k i < 1) {m : ℕ}
    (U : Fin m → ∀ k, Assignment (n k) → ℝ) (c : Fin m → ℝ)
    (F : (Fin m → ℝ) → ℝ) (hF : ContinuousAt F c)
    (hU : ∀ j, W1InProb n p (fun k z => U j k z - c j)) :
    W1InProb n p (fun k z => F (fun j => U j k z) - F c) := by
  classical
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousAt_iff.mp hF) ε hε
  have hhalf : 0 < δ / 2 := by linarith
  have hbad (k : ℕ) (z : Assignment (n k))
      (hz : ε < |F (fun j => U j k z) - F c|) :
      ∃ j, δ / 2 < |U j k z - c j| := by
    by_contra hnone
    have hcoord (j : Fin m) : dist (U j k z) (c j) < δ := by
      have hj : |U j k z - c j| ≤ δ / 2 := by
        apply le_of_not_gt
        intro hj
        exact hnone ⟨j, hj⟩
      rw [Real.dist_eq]
      linarith
    have hvec : dist (fun j => U j k z) c < δ := (dist_pi_lt_iff hδ).mpr hcoord
    have hclose : dist (F (fun j => U j k z)) (F c) < ε := hnear hvec
    rw [Real.dist_eq] at hclose
    linarith
  have hupper (k : ℕ) : prob (p k)
      (fun z => ε < |F (fun j => U j k z) - F c|) ≤
      ∑ j, prob (p k) (fun z => δ / 2 < |U j k z - c j|) :=
    DLbSupport.prob_le_sum (p k) (hp k) _ _ (hbad k)
  have hsum : Tendsto
      (fun k => ∑ j, prob (p k) (fun z => δ / 2 < |U j k z - c j|))
      atTop (nhds (0 : ℝ)) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum (s := Finset.univ)
        (fun j _ => hU j (δ / 2) hhalf))
  exact squeeze_zero (fun k => DLbSupport.prob_nonneg (p k) (hp k) _)
    hupper hsum

def qMap (x : Fin 2 → ℝ) : ℝ := x 0 + x 1
def qPoint : Fin 2 → ℝ := ![1/8, 3/40]

theorem qMap_continuous : ContinuousAt qMap qPoint := by
  exact (continuous_apply 0).continuousAt.add (continuous_apply 1).continuousAt

theorem qMap_value : qMap qPoint = (1/5 : ℝ) := by
  norm_num [qMap, qPoint]

def rMap (x : Fin 4 → ℝ) : ℝ :=
  x 0 - 2 * (x 1 / (x 3 * x 2)) * x 1 +
    x 0 * (x 1 / (x 3 * x 2))^2

def rPoint : Fin 4 → ℝ := ![1/8, 0, 1/2, 1/4]

theorem rMap_continuous : ContinuousAt rMap rPoint := by
  have hx (k : Fin 4) : ContinuousAt (fun x : Fin 4 → ℝ => x k) rPoint :=
    (continuous_apply k).continuousAt
  have hb : ContinuousAt (fun x : Fin 4 → ℝ => x 1 / (x 3 * x 2)) rPoint := by
    apply (hx 1).div ((hx 3).mul (hx 2))
    norm_num [rPoint]
  have hnum : ContinuousAt (fun x : Fin 4 → ℝ =>
      x 0 - 2 * (x 1 / (x 3 * x 2)) * x 1 +
        x 0 * (x 1 / (x 3 * x 2))^2) rPoint := by
    exact ((hx 0).sub ((continuousAt_const.mul hb).mul (hx 1))).add
      ((hx 0).mul (hb.pow 2))
  exact hnum

theorem rMap_value : rMap rPoint = (1/8 : ℝ) := by
  norm_num [rMap, rPoint]

def vMap (x : Fin 2 → ℝ) : ℝ := x 0 / x 1
def vPoint : Fin 2 → ℝ := ![2/25, 1/4]

theorem vMap_continuous : ContinuousAt vMap vPoint := by
  apply (continuous_apply 0).continuousAt.div (continuous_apply 1).continuousAt
  norm_num [vPoint]

theorem vMap_value : vMap vPoint = (8/25 : ℝ) := by
  norm_num [vMap, vPoint]

theorem T3_L7_proof : _root_.SAP.P004a.WH.W1.T3_L7 := by
  intro hf
  let p : ∀ N, Fin N → ℝ := fun N => propensities (activeO N) activeTheta
  obtain ⟨hK, hJ, hS, hph, hH⟩ := o10_proof

  have hnh : AronowAudit.P004.InProb p (fun N _ => nH N / N - 1/4) := by
    apply (dl4_proof p oc_admissible).2.2
    convert hH.sub (tendsto_const_nhds (x := (1/4 : ℝ))) using 1 <;> norm_num

  let UQ : Fin 2 → ∀ N, Assignment N → ℝ :=
    ![fun N z => KAct N z / N, fun N z => JAct N z / N]
  have hUQ : ∀ k, AronowAudit.P004.InProb p (fun N z => UQ k N z - qPoint k) := by
    intro k
    fin_cases k
    · change AronowAudit.P004.InProb p (fun N z => KAct N z / N - 1/8)
      exact hK
    · change AronowAudit.P004.InProb p (fun N z => JAct N z / N - 3/40)
      exact hJ
  have hQmap : AronowAudit.P004.InProb p (fun N z => qMap (fun k => UQ k N z) - 1/5) := by
    simpa only [qMap_value] using
      dl9_proof p oc_admissible UQ qPoint qMap qMap_continuous hUQ
  have hQold : AronowAudit.P004.InProb p (fun N z => armCount z true / N - 1/5) := by
    apply oc_inProb_congr (U := fun N z => qMap (fun k => UQ k N z) - 1/5) _ hQmap
    filter_upwards [eventually_gt_atTop 0] with N hN
    intro z
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hc : armCount z true = KAct N z + JAct N z := oc_armCount_true N z
    change KAct N z / N + JAct N z / N - 1/5 = armCount z true / N - 1/5
    rw [hc]
    field_simp [ne_of_gt hNr]
    <;> ring
  have hQ : W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r))
      (fun r z => armCount z true / (8*r : ℕ) - 1/5) := by
    simpa [p, w1ActiveP] using inProb_multiples hQold

  let UR : Fin 4 → ∀ N, Assignment N → ℝ :=
    ![fun N z => KAct N z / N, fun N z => SAct N z / N,
      fun N z => pHatH N z, fun N _ => nH N / N]
  have hUR : ∀ k, AronowAudit.P004.InProb p (fun N z => UR k N z - rPoint k) := by
    intro k
    fin_cases k
    · change AronowAudit.P004.InProb p (fun N z => KAct N z / N - 1/8)
      exact hK
    · change AronowAudit.P004.InProb p (fun N z => SAct N z / N - 0)
      change AronowAudit.P004.InProb p (fun N z => SAct N z / N - 0) at hS
      exact hS
    · change AronowAudit.P004.InProb p (fun N z => pHatH N z - 1/2)
      exact hph
    · change AronowAudit.P004.InProb p (fun N _ => nH N / N - 1/4)
      exact hnh
  have hRmap : AronowAudit.P004.InProb p (fun N z => rMap (fun k => UR k N z) - 1/8) := by
    simpa only [rMap_value] using
      dl9_proof p oc_admissible UR rPoint rMap rMap_continuous hUR
  have hRold : AronowAudit.P004.InProb p (fun N z => RAct N z / N - 1/8) := by
    apply oc_inProb_congr (U := fun N z => rMap (fun k => UR k N z) - 1/8) _ hRmap
    filter_upwards [eventually_gt_atTop 0] with N hN
    intro z
    have hNp : 0 < N := hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
    have hHpos := oc_nH_pos N hNp
    have hHne : nH N ≠ 0 := ne_of_gt hHpos
    have hphpos : 0 < pHatH N z := by
      have hc := (oc_clip_bounds (KAct N z / nH N)).1
      exact lt_of_lt_of_le (by norm_num) hc
    have hphne : pHatH N z ≠ 0 := ne_of_gt hphpos
    rw [oc_RAct_expansion]
    dsimp [rMap, UR]
    norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
    field_simp [ne_of_gt hNr, hHne, hphne]
    <;> ring
  have hR : W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r))
      (fun r z => w1ActiveR (8*r) z / (8*r : ℕ) - 1/8) := by
    have hseq := inProb_multiples hRold
    have hseq' : W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r))
        (fun r z => RAct (8*r) z / (8*r : ℕ) - 1/8) := by
      simpa [p, w1ActiveP] using hseq
    apply w1_inProb_congr (U := fun r z => RAct (8*r) z / (8*r : ℕ) - 1/8) ?_ hseq'
    filter_upwards with r z
    simp only [w1ActiveR, w1ActiveS, w1ActiveK, w1ActiveNH, w1ActivePH,
      w1Clip, RAct, SAct, KAct, nH, pHatH, clip]
    rfl
  
  have hVold : AronowAudit.P004.InProb p (fun N z => (N : ℝ) *
      printedSAH (propensities (activeO N) (activeMLE N z))
        (circleAverage (activePopulation N) 0) (spatialNeighborhoods activePopulation 0 N)
        (fun i a => dot (activeO N i) (fittedBeta (propensities (activeO N) (activeMLE N z))
          (circleAverage (activePopulation N) 0) (activeO N) a z)) z - 2/25) := o12_proof
  have hVold' : AronowAudit.P004.InProb p (fun N z => (N : ℝ) * w1ActiveVPrinted N z - 2/25) := by
    apply oc_inProb_congr (U := fun N z => (N : ℝ) *
      printedSAH (propensities (activeO N) (activeMLE N z))
        (circleAverage (activePopulation N) 0) (spatialNeighborhoods activePopulation 0 N)
        (fun i a => dot (activeO N i) (fittedBeta (propensities (activeO N) (activeMLE N z))
          (circleAverage (activePopulation N) 0) (activeO N) a z)) z - 2/25) _ hVold
    filter_upwards [eventually_ge_atTop 3] with N hN
    intro z
    have htable : circleAverage (activePopulation N) 0 = activeTable N :=
      AronowAudit.P004.Wave1.LinePopulation.n3_proof (activeTable N)
    have hneigh : spatialNeighborhoods activePopulation 0 N = fun i => {i} := by
      funext i
      exact AronowAudit.P004.Wave1.LinePopulation.line_zero_ball (activeTable N) i
    have hmle : activeMLE N z = w1ActiveMLE N z := by
      simp [activeMLE, w1ActiveMLE, nH, nL, pHatH, pHatL, KAct, JAct, w1ActiveNH,
        w1ActiveNL, w1ActivePH, w1ActivePL, w1ActiveK, w1ActiveJ,
        clip, w1Clip, logit, w1Logit,
        _root_.SAP.P004a.activeGroup, _root_.AronowAudit.P004.activeGroup,
        _root_.SAP.P004a.bit, _root_.AronowAudit.P004.bit]
    rw [htable]
    rw [hneigh, hmle]
    dsimp [w1ActiveVPrinted, w1ActiveFits]
    rfl
  have hV : W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r))
      (fun r z => (8*r : ℕ) * w1ActiveVPrinted (8*r) z - 2/25) := by
    simpa [p, w1ActiveP] using inProb_multiples hVold'

  have hvar : Tendsto (fun r => (8*r : ℕ) *
      variance (w1ActiveP (8*r)) (w1ActiveIPW (8*r))) atTop (nhds (1/4 : ℝ)) :=
    SAP.P004a.WH.W1.active_variance_limit
  have hvar0 : Tendsto (fun r => (8*r : ℕ) *
      variance (w1ActiveP (8*r)) (w1ActiveIPW (8*r)) - 1/4) atTop (nhds 0) := by
    convert hvar.sub (tendsto_const_nhds (x := (1/4 : ℝ))) using 1 <;> norm_num
  let pR : ∀ r, Fin (8*r) → ℝ := fun r => w1ActiveP (8*r)
  have hpR (r : ℕ) (i : Fin (8*r)) : 0 < pR r i ∧ pR r i < 1 :=
    oc_admissible (8*r) i
  have hvarIn : W1InProb (fun r => 8*r) pR
      (fun r _ => (8*r : ℕ) * variance (w1ActiveP (8*r)) (w1ActiveIPW (8*r)) - 1/4) :=
    deterministic_inProb hvar0
  let UV : Fin 2 → ∀ r, Assignment (8*r) → ℝ :=
    ![fun r z => (8*r : ℕ) * w1ActiveVPrinted (8*r) z,
      fun r _ => (8*r : ℕ) * variance (w1ActiveP (8*r)) (w1ActiveIPW (8*r))]
  have hUV : ∀ k, W1InProb (fun r => 8*r) pR
      (fun r z => UV k r z - vPoint k) := by
    intro k
    fin_cases k
    · change W1InProb (fun r => 8*r) pR
        (fun r z => (8*r : ℕ) * w1ActiveVPrinted (8*r) z - 2/25)
      simpa [pR, w1ActiveP] using hV
    · change W1InProb (fun r => 8*r) pR
        (fun r _ => (8*r : ℕ) * variance (w1ActiveP (8*r)) (w1ActiveIPW (8*r)) - 1/4)
      exact hvarIn
  have hVmap : W1InProb (fun r => 8*r) pR
      (fun r z => vMap (fun k => UV k r z) - 8/25) := by
    simpa only [vMap_value] using
      w1_dl9 (n := fun r => 8*r) pR hpR UV vPoint vMap vMap_continuous hUV
  have hRatio : W1InProb (fun r => 8*r) pR
      (fun r z => w1ActiveVPrinted (8*r) z /
        variance (w1ActiveP (8*r)) (w1ActiveIPW (8*r)) - 8/25) := by
    apply w1_inProb_congr (U := fun r z =>
      vMap (fun k => UV k r z) - 8/25) ?_ hVmap
    filter_upwards [eventually_gt_atTop 0] with r hr z
    have hNr : (0 : ℝ) < (8*r : ℕ) := by exact_mod_cast (show 0 < 8*r by omega)
    have hfin := hf r hr
    rcases hfin with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hvpos⟩
    dsimp [vMap, UV]
    norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    field_simp [ne_of_gt hNr, ne_of_gt hvpos]
    <;> ring

  have hzero : Tendsto (fun r => prob (pR r)
      (fun z => w1ActiveVPrinted (8*r) z ≤ 0)) atTop (nhds 0) := by
    have htail := hV (1/25) (by norm_num)
    have hbound (r : ℕ) : prob (pR r)
        (fun z => w1ActiveVPrinted (8*r) z ≤ 0) ≤
        prob (pR r) (fun z => 1/25 < |(8*r : ℕ) * w1ActiveVPrinted (8*r) z - 2/25|) := by
      apply AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_mono
        (pR r) (hpR r) _ _
      intro z hz
      have hN : 0 ≤ ((8*r : ℕ) : ℝ) := by positivity
      have hprod : ((8*r : ℕ) : ℝ) * w1ActiveVPrinted (8*r) z ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hN hz
      have hneg : ((8*r : ℕ) : ℝ) * w1ActiveVPrinted (8*r) z - 2/25 < 0 := by
        calc
          _ ≤ 0 - 2/25 := sub_le_sub_right hprod _
          _ < 0 := by norm_num
      rw [abs_of_neg hneg]
      have hh : (1/25 : ℝ) < 2/25 - ((8*r : ℕ) : ℝ) * w1ActiveVPrinted (8*r) z := by
        nlinarith [hprod]
      convert hh using 1 <;> ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun r => AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_nonneg (pR r) (fun i => hpR r i)
        (fun z => w1ActiveVPrinted (8*r) z ≤ 0)) hbound

  exact ⟨hQ, hR, hV, hRatio, hzero⟩

end

end SAP.P004a.WH.W1.P.T3_L7

theorem _root_.SAP.P004a.WH.W1.T3_L7_proof : _root_.SAP.P004a.WH.W1.T3_L7 := by
  exact SAP.P004a.WH.W1.P.T3_L7.T3_L7_proof
