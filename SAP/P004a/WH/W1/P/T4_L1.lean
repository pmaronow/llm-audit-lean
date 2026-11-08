import SAP.P004a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T4_L1

open AronowAudit.P004
open AronowAudit.P004.Wave1.ObservationalCoverage
open AronowAudit.P004.Wave1.DesignLimits
open Filter
open scoped Classical
noncomputable section
set_option maxHeartbeats 1000000

def point : Fin 4 → ℝ := ![1 / 8, 0, 1 / 2, 1 / 4]

def law (N : ℕ) : Fin N → ℝ := propensities (activeO N) activeTheta

def coords : Fin 4 → ∀ N : ℕ, Assignment N → ℝ :=
  ![fun N z => KAct N z / N,
    fun N z => SAct N z / N,
    fun N z => pHatH N z,
    fun N _ => nH N / N]

def residualMap (x : Fin 4 → ℝ) : ℝ :=
  let b := x 1 / (x 3 * x 2)
  (x 0 - 2 * b * x 1 + x 0 * b^2) / (x 2)^2

theorem residualMap_continuous : ContinuousAt residualMap point := by
  have hx (k : Fin 4) : ContinuousAt (fun x : Fin 4 → ℝ => x k) point :=
    (continuous_apply k).continuousAt
  have hb : ContinuousAt (fun x : Fin 4 → ℝ => x 1 / (x 3 * x 2)) point := by
    apply (hx 1).div ((hx 3).mul (hx 2))
    norm_num [point]
  have hnum : ContinuousAt (fun x : Fin 4 → ℝ =>
      x 0 - 2 * (x 1 / (x 3 * x 2)) * x 1 +
        x 0 * (x 1 / (x 3 * x 2))^2) point := by
    exact ((hx 0).sub (((continuousAt_const).mul hb).mul (hx 1))).add
      ((hx 0).mul (hb.pow 2))
  change ContinuousAt (fun x : Fin 4 → ℝ =>
    (x 0 - 2 * (x 1 / (x 3 * x 2)) * x 1 +
      x 0 * (x 1 / (x 3 * x 2))^2) / (x 2)^2) point
  apply hnum.div ((hx 2).pow 2)
  norm_num [point]

theorem residualMap_point : residualMap point = (1 / 2 : ℝ) := by
  norm_num [residualMap, point]

theorem restrict_inProb {p : ∀ N, Fin N → ℝ}
    {X : ∀ N, Assignment N → ℝ}
    (h : InProb p X) :
    W1InProb (fun r => 8*r) (fun r => p (8*r))
      (fun r z => X (8*r) z) := by
  intro ε hε
  exact (h ε hε).comp (SAP.P004a.WH.W1.multiples_tendsto 8 (by omega))

theorem map_coordinates :
    ∀ k : Fin 4, AronowAudit.P004.InProb law
      (fun N z => coords k N z - point k) := by
  intro k
  have ho := AronowAudit.P004.Wave1.ObservationalCoverage.o10_proof
  rcases ho with ⟨hK, _hJ, hS, hph, hNH⟩
  fin_cases k
  · change AronowAudit.P004.InProb law (fun N z => KAct N z / N - 1 / 8)
    exact hK
  · change AronowAudit.P004.InProb law (fun N z => SAct N z / N - 0)
    exact hS
  · change AronowAudit.P004.InProb law (fun N z => pHatH N z - 1 / 2)
    exact hph
  · have hp : AdmissibleSeq law :=
      AronowAudit.P004.Wave1.ObservationalCoverage.oc_admissible
    have hNH0 : AronowAudit.P004.InProb law (fun N _ => nH N / N - 1 / 4) := by
      apply (AronowAudit.P004.Wave1.DesignLimits.dl4_proof law hp).2.2
      convert hNH.sub (tendsto_const_nhds (x := (1 / 4 : ℝ))) using 1 <;> norm_num
    change AronowAudit.P004.InProb law (fun N _ => nH N / N - 1 / 4)
    exact hNH0

theorem mapped_limit :
    AronowAudit.P004.InProb law
      (fun N z => residualMap (fun k => coords k N z) - 1 / 2) := by
  have hU : ∀ k, AronowAudit.P004.InProb law
      (fun N z => coords k N z - point k) := map_coordinates
  simpa only [residualMap_point] using
    AronowAudit.P004.Wave1.DesignLimits.dl9_proof
      law AronowAudit.P004.Wave1.ObservationalCoverage.oc_admissible
      coords point residualMap residualMap_continuous hU

theorem inProb_congr {n : ℕ → ℕ} {p : ∀ r, Fin (n r) → ℝ}
    {U V : ∀ r, Assignment (n r) → ℝ}
    (h : ∀ᶠ r in atTop, ∀ z, U r z = V r z)
    (hU : W1InProb n p U) : W1InProb n p V := by
  intro ε hε
  refine (hU ε hε).congr' ?_
  filter_upwards [h] with r hr
  exact AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_congr
    (p r) _ _ (fun z => by rw [hr z])

end
end SAP.P004a.WH.W1.P.T4_L1

open AronowAudit.P004
open AronowAudit.P004.Wave1.ObservationalCoverage
open Filter

theorem SAP.P004a.WH.W1.T4_L1_proof : SAP.P004a.WH.W1.T4_L1 := by
  have hm := SAP.P004a.WH.W1.P.T4_L1.restrict_inProb
    (p := SAP.P004a.WH.W1.P.T4_L1.law)
    (X := fun N z => SAP.P004a.WH.W1.P.T4_L1.residualMap
      (fun k => SAP.P004a.WH.W1.P.T4_L1.coords k N z) - 1 / 2)
    SAP.P004a.WH.W1.P.T4_L1.mapped_limit
  have hm' : W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r))
      (fun r z => SAP.P004a.WH.W1.P.T4_L1.residualMap
        (fun k => SAP.P004a.WH.W1.P.T4_L1.coords k (8*r) z) - 1 / 2) := by
    simpa only [SAP.P004a.WH.W1.P.T4_L1.law, w1ActiveP] using hm
  have hraw : W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r))
      (fun r z => (8*r : ℕ) * w1ActiveVRaw (8*r) z - 1 / 2) := by
    apply SAP.P004a.WH.W1.P.T4_L1.inProb_congr
      (U := fun r z => SAP.P004a.WH.W1.P.T4_L1.residualMap
        (fun k => SAP.P004a.WH.W1.P.T4_L1.coords k (8*r) z) - 1 / 2)
    · filter_upwards [eventually_gt_atTop 0] with r hr
      intro z
      let N : ℕ := 8*r
      have hNp : 0 < N := by dsimp [N]; omega
      have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
      have hNH : 0 < nH N :=
        AronowAudit.P004.Wave1.ObservationalCoverage.oc_nH_pos N hNp
      have hph : 0 < pHatH N z :=
        (AronowAudit.P004.Wave1.ObservationalCoverage.pHatH_mem N z).1
      have hform := SAP.P004a.WH.W1.active_raw_formula r hr z
      change w1ActiveVRaw N z = RAct N z / ((N : ℝ)^2 * (pHatH N z)^2) at hform
      have hexp := AronowAudit.P004.Wave1.ObservationalCoverage.oc_RAct_expansion N z
      change RAct N z = KAct N z -
        2 * (SAct N z / (nH N * pHatH N z)) * SAct N z +
        KAct N z * (SAct N z / (nH N * pHatH N z))^2 at hexp
      have hb : SAct N z / (nH N * pHatH N z) =
          (SAct N z / N) / ((nH N / N) * pHatH N z) := by
        field_simp [ne_of_gt hNr, ne_of_gt hNH]
      have hratio : RAct N z / N =
          (KAct N z / N -
            2 * ((SAct N z / N) / ((nH N / N) * pHatH N z)) * (SAct N z / N) +
            (KAct N z / N) * (((SAct N z / N) / ((nH N / N) * pHatH N z))^2)) := by
        rw [hexp, hb]
        field_simp [ne_of_gt hNr, ne_of_gt hNH, ne_of_gt hph]
      have hscale : (N : ℝ) * (RAct N z / ((N : ℝ)^2 * (pHatH N z)^2)) =
          (RAct N z / N) / (pHatH N z)^2 := by
        field_simp [ne_of_gt hNr, ne_of_gt hph]
      change (KAct N z / N -
          2 * ((SAct N z / N) / ((nH N / N) * pHatH N z)) * (SAct N z / N) +
          (KAct N z / N) * (((SAct N z / N) / ((nH N / N) * pHatH N z))^2)) /
            (pHatH N z)^2 - 1 / 2 =
          (N : ℝ) * w1ActiveVRaw N z - 1 / 2
      calc
        (KAct N z / N -
            2 * ((SAct N z / N) / ((nH N / N) * pHatH N z)) * (SAct N z / N) +
            (KAct N z / N) * (((SAct N z / N) / ((nH N / N) * pHatH N z))^2)) /
              (pHatH N z)^2 - 1 / 2 =
            (RAct N z / N) / (pHatH N z)^2 - 1 / 2 := by
              rw [← hratio]
        _ = (N : ℝ) * w1ActiveVRaw N z - 1 / 2 := by
              rw [hform]
              exact congrArg (fun y : ℝ => y - 1/2) hscale.symm
    · exact hm'
  exact hraw
