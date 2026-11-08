import SAP.P004a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P004a.WH.W1.P.T3_L2

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
open AronowAudit.P004.Wave1.ObservationalCoverage

noncomputable section

lemma nH_eight (r : ℕ) : nH (8*r) = (8*r : ℝ)/4 := by
  rw [nH, active_count_formula]
  have hmod : (8*r) % 8 = 0 := by omega
  have hdiv : (8*r) / 8 = r := by omega
  rw [hmod, hdiv]
  norm_num
  ring

lemma nH_eight_eq (r : ℕ) : nH (8*r) = 2*r := by
  rw [nH_eight]
  ring

lemma nL_eight (r : ℕ) : nL (8*r) = 3*(8*r : ℝ)/4 := by
  have hcards (N : ℕ) :
      (Finset.univ.filter (fun i : Fin N => activeGroup N i)).card +
        (Finset.univ.filter (fun i : Fin N => ¬ activeGroup N i)).card = N := by
    let A : Finset (Fin N) := Finset.univ.filter (fun i => activeGroup N i)
    let B : Finset (Fin N) := Finset.univ.filter (fun i => ¬ activeGroup N i)
    have hD : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have hg : activeGroup N i := (Finset.mem_filter.mp hi).2
      have hng : ¬ activeGroup N i := (Finset.mem_filter.mp hj).2
      exact hng hg
    have hU : A ∪ B = Finset.univ := by
      ext i
      by_cases h : activeGroup N i <;> simp [A, B, h]
    have hc := Finset.card_union_of_disjoint hD
    simpa [hU, A, B] using hc.symm
  have hsum (N : ℕ) : nH N + nL N = (N : ℝ) := by
    unfold nH nL
    exact_mod_cast hcards N
  have hsumN := hsum (8*r)
  have hnh : nH (8*r) = (8*r : ℝ)/4 := nH_eight r
  have hnl : nL (8*r) = (8*r : ℝ) - nH (8*r) := by
    calc
      nL (8*r) = (nH (8*r) + nL (8*r)) - nH (8*r) := by ring
      _ = (8*r : ℝ) - nH (8*r) := by rw [hsumN]; norm_cast
  rw [hnl, hnh]
  push_cast
  ring

lemma sAct_eight (r : ℕ) : sAct (8*r) = 0 := by
  rw [sAct_formula]
  have hmod : (8*r) % 8 = 0 := by omega
  simp [hmod]

lemma active_propensity (N : ℕ) :
    w1ActiveP N = fun i => if SAP.P004a.activeGroup N i then 1/2 else 1/10 := by
  change AronowAudit.P004.propensities (AronowAudit.P004.activeO N)
      AronowAudit.P004.activeTheta = _
  funext i
  rw [o4_proof N]
  by_cases h : SAP.P004a.activeGroup N i
  · have hr : AronowAudit.P004.activeGroup N i := by simpa [SAP.P004a.activeGroup, AronowAudit.P004.activeGroup] using h
    simp [h, hr]
  · have hr : ¬ AronowAudit.P004.activeGroup N i := by
      intro hg
      apply h
      simpa [SAP.P004a.activeGroup, AronowAudit.P004.activeGroup] using hg
    simp [h, hr]

lemma activeO_eq (N : ℕ) : SAP.P004a.activeO N = AronowAudit.P004.activeO N := rfl

lemma activeTable_eq (N : ℕ) : SAP.P004a.activeTable N = AronowAudit.P004.activeTable N := rfl

lemma activeP_eq (N : ℕ) :
    w1ActiveP N = AronowAudit.P004.propensities (AronowAudit.P004.activeO N)
      AronowAudit.P004.activeTheta := rfl

lemma propensities_eq {N k : ℕ} (O : Fin N → Fin k → ℝ) (θ : Fin k → ℝ) :
    SAP.P004a.propensities O θ = AronowAudit.P004.propensities O θ := rfl

lemma beta_eq {N k : ℕ} (p : Fin N → ℝ) (R : SAP.P004a.CircleTable N)
    (O : Fin N → Fin k → ℝ) (a : Bool) :
    SAP.P004a.beta p R O a = AronowAudit.P004.beta p R O a := rfl

lemma ame_eq {N : ℕ} (p : Fin N → ℝ) (R : SAP.P004a.CircleTable N) :
    SAP.P004a.ame p R = AronowAudit.P004.ame p R := rfl

lemma expect_eq {N : ℕ} (p : Fin N → ℝ) (X : SAP.P004a.Assignment N → ℝ) :
    SAP.P004a.expect p X = AronowAudit.P004.expect p X := rfl

lemma variance_eq {N : ℕ} (p : Fin N → ℝ) (X : SAP.P004a.Assignment N → ℝ) :
    SAP.P004a.variance p X = AronowAudit.P004.variance p X := rfl

lemma homophily_eq {N : ℕ} (p : Fin N → ℝ) (R : SAP.P004a.CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) :
    SAP.P004a.homophilyQ p R B g = AronowAudit.P004.homophilyQ p R B g := rfl

lemma augmented_eq {N : ℕ} (p : Fin N → ℝ) (R : SAP.P004a.CircleTable N)
    (g : Fin N → Bool → ℝ) (z : SAP.P004a.Assignment N) :
    SAP.P004a.augmented p R g z = AronowAudit.P004.augmented p R g z := rfl

lemma printedFits_eq {N k : ℕ} (p : Fin N → ℝ) (R : SAP.P004a.CircleTable N)
    (O : Fin N → Fin k → ℝ) (i : Fin N) (a : Bool) :
    SAP.P004a.printedFits p R O i a = AronowAudit.P004.printedFits p R O i a := rfl

lemma fittedBeta_eq {N k : ℕ} (p : Fin N → ℝ) (R : SAP.P004a.CircleTable N)
    (O : Fin N → Fin k → ℝ) (a : Bool) (z : SAP.P004a.Assignment N) :
    SAP.P004a.fittedBeta p R O a z = AronowAudit.P004.fittedBeta p R O a z := rfl

lemma fittedIPW_eq {N k : ℕ} (R : SAP.P004a.CircleTable N) (O : Fin N → Fin k → ℝ)
    (θ : SAP.P004a.Assignment N → Fin k → ℝ) (z : SAP.P004a.Assignment N) :
    SAP.P004a.fittedIPW R O θ z = AronowAudit.P004.fittedIPW R O θ z := rfl

lemma printedSAH_eq {N : ℕ} (p : Fin N → ℝ) (R : SAP.P004a.CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : SAP.P004a.Assignment N) :
    SAP.P004a.printedSAH p R B g z = AronowAudit.P004.printedSAH p R B g z := rfl

lemma information_eq {N k : ℕ} (p : Fin N → ℝ) (O : Fin N → Fin k → ℝ) :
    SAP.P004a.information p O = AronowAudit.P004.information p O := rfl

lemma dot_eq {k : ℕ} (u v : Fin k → ℝ) :
    SAP.P004a.dot u v = AronowAudit.P004.dot u v := rfl

lemma bit_eq (a : Bool) : SAP.P004a.bit a = AronowAudit.P004.bit a := rfl

lemma active_propensity_bounds (N : ℕ) (i : Fin N) :
    0 < w1ActiveP N i ∧ w1ActiveP N i < 1 := by
  rw [active_propensity]
  change 0 < (if SAP.P004a.activeGroup N i then (1/2 : ℝ) else 1/10) ∧
    (if SAP.P004a.activeGroup N i then (1/2 : ℝ) else 1/10) < 1
  split_ifs <;> norm_num

lemma activeNH_eq (N : ℕ) : w1ActiveNH N = nH N := by
  unfold w1ActiveNH nH
  congr 1

lemma activeNL_eq (N : ℕ) : w1ActiveNL N = nL N := by
  unfold w1ActiveNL nL
  congr 1

lemma activeK_eq (N : ℕ) (z : Assignment N) : w1ActiveK N z = KAct N z := by
  unfold w1ActiveK KAct
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : SAP.P004a.activeGroup N i
  · have hr : AronowAudit.P004.activeGroup N i := by simpa [SAP.P004a.activeGroup, AronowAudit.P004.activeGroup] using h
    simp [h, hr, SAP.P004a.bit, AronowAudit.P004.bit]
  · have hr : ¬ AronowAudit.P004.activeGroup N i := by
      intro hg
      apply h
      simpa [SAP.P004a.activeGroup, AronowAudit.P004.activeGroup] using hg
    simp [h, hr, SAP.P004a.bit, AronowAudit.P004.bit]

lemma activeJ_eq (N : ℕ) (z : Assignment N) : w1ActiveJ N z = JAct N z := by
  unfold w1ActiveJ JAct
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : SAP.P004a.activeGroup N i
  · have hr : AronowAudit.P004.activeGroup N i := by simpa [SAP.P004a.activeGroup, AronowAudit.P004.activeGroup] using h
    simp [h, hr, SAP.P004a.bit, AronowAudit.P004.bit]
  · have hr : ¬ AronowAudit.P004.activeGroup N i := by
      intro hg
      apply h
      simpa [SAP.P004a.activeGroup, AronowAudit.P004.activeGroup] using hg
    have hb : SAP.P004a.bit (z i) = AronowAudit.P004.bit (z i) := by
      cases z i <;> rfl
    simp [h, hr, hb]

lemma activePH_eq (N : ℕ) (z : Assignment N) : w1ActivePH N z = pHatH N z := by
  unfold w1ActivePH pHatH w1Clip clip
  rw [activeK_eq, activeNH_eq]

lemma activePL_eq (N : ℕ) (z : Assignment N) : w1ActivePL N z = pHatL N z := by
  unfold w1ActivePL pHatL w1Clip clip
  rw [activeJ_eq, activeNL_eq]

lemma active_mle_eq (N : ℕ) (z : Assignment N) : w1ActiveMLE N z = activeMLE N z := by
  have hnh := activeNH_eq N
  have hnl := activeNL_eq N
  have hph := activePH_eq N z
  have hpl := activePL_eq N z
  funext j
  fin_cases j <;> simp [w1ActiveMLE, activeMLE, w1Logit, logit, hnh, hnl, hph, hpl]

lemma active_design_weight_pos {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (z : Assignment N) : 0 < designWeight p z := by
  unfold designWeight
  apply Finset.prod_pos
  intro i hi
  unfold coin
  split_ifs <;> have h := hp i <;> linarith

lemma variance_pos_of_two_values {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (X : Assignment N → ℝ)
    (z₁ z₂ : Assignment N) (hne : X z₁ ≠ X z₂) : 0 < variance p X := by
  have hnonneg := AronowAudit.P004.variance_nonneg p hp X
  by_contra hnot
  have hv0 : variance p X = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hcent : expect p (fun z => (X z - expect p X)^2) = 0 := by
    have hc := AronowAudit.P004.cov_centered p X X
    change AronowAudit.P004.cov p X X = 0 at hv0
    rw [hv0] at hc
    have he : (fun z => (X z - expect p X) * (X z - expect p X)) =
        fun z => (X z - expect p X)^2 := by funext z; ring
    calc
      expect p (fun z => (X z - expect p X)^2) =
          expect p (fun z => (X z - expect p X) * (X z - expect p X)) := by
        congr 1
        funext z
        ring
      _ = 0 := hc.symm
  have hterm (z : Assignment N) :
      designWeight p z * (X z - expect p X)^2 = 0 := by
    have hnonneg (w : Assignment N) :
        0 ≤ designWeight p w * (X w - expect p X)^2 :=
    mul_nonneg (AronowAudit.P004.design_weight_nonneg p hp w) (sq_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun w hw => hnonneg w)).mp (by
      simpa only [expect] using hcent) z (Finset.mem_univ z)
    exact hz
  have hval (z : Assignment N) : X z = expect p X := by
    have hw := active_design_weight_pos p hp z
    have hsq : (X z - expect p X)^2 = 0 := (mul_eq_zero.mp (hterm z)).resolve_left hw.ne'
    nlinarith [hsq]
  exact hne (by rw [hval z₁, hval z₂])

lemma active_sign_eq (N : ℕ) (i : Fin N) : w1ActiveSign N i = activeSign N i := rfl

lemma active_sum_eq (N : ℕ) (z : Assignment N) : w1ActiveS N z = SAct N z := rfl

lemma activeSFun_eq (N : ℕ) : w1ActiveS N = SAct N := by
  funext z
  exact active_sum_eq N z

lemma active_mle_fun_eq (N : ℕ) : w1ActiveMLE N = activeMLE N := by
  funext z
  exact active_mle_eq N z

lemma activeIPW_fun_eq (N : ℕ) : w1ActiveIPW N =
    AronowAudit.P004.fittedIPW (AronowAudit.P004.activeTable N)
      (AronowAudit.P004.activeO N) (activeMLE N) := by
  funext z
  change SAP.P004a.fittedIPW (SAP.P004a.activeTable N) (SAP.P004a.activeO N)
      (w1ActiveMLE N) z = _
  rw [fittedIPW_eq, activeTable_eq, activeO_eq, active_mle_fun_eq]

lemma activeFits_root_eq (N : ℕ) (z : Assignment N) :
    w1ActiveFits N z = fun i a =>
      AronowAudit.P004.dot (AronowAudit.P004.activeO N i)
        (AronowAudit.P004.fittedBeta
        (AronowAudit.P004.propensities (AronowAudit.P004.activeO N) (activeMLE N z))
        (AronowAudit.P004.activeTable N) (AronowAudit.P004.activeO N) a z) := by
  funext i a
  unfold w1ActiveFits
  rw [dot_eq, fittedBeta_eq, propensities_eq, activeO_eq, activeTable_eq,
    active_mle_fun_eq]

lemma activeR_eq (N : ℕ) (z : Assignment N) : w1ActiveR N z = RAct N z := by
  unfold w1ActiveR RAct
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : SAP.P004a.activeGroup N i
  · have hr : AronowAudit.P004.activeGroup N i := by
      simpa [SAP.P004a.activeGroup, AronowAudit.P004.activeGroup] using h
    simp [h, hr, active_sign_eq, active_sum_eq, activeNH_eq, activePH_eq, bit_eq]
  · have hr : ¬ AronowAudit.P004.activeGroup N i := by
      intro hg
      apply h
      simpa [SAP.P004a.activeGroup, AronowAudit.P004.activeGroup] using hg
    simp [h, hr, active_sign_eq, active_sum_eq, activeNH_eq, activePH_eq, bit_eq]


end

end SAP.P004a.WH.W1.P.T3_L2

open SAP.P004a.WH.W1.P.T3_L2
open AronowAudit.P004.Wave1.ObservationalCoverage
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section

theorem SAP.P004a.WH.W1.T3_L2_proof : SAP.P004a.WH.W1.T3_L2 := by
  intro r hr
  dsimp only
  let N : ℕ := 8*r
  have hNpos : 0 < N := by dsimp [N]; omega
  have hN3 : 3 ≤ N := by dsimp [N]; omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNH : nH N = (N : ℝ)/4 := by simpa [N] using nH_eight r
  have hNL : nL N = 3*(N : ℝ)/4 := by simpa [N] using nL_eight r
  have hs : sAct N = 0 := by simpa [N] using sAct_eight r
  have hP : w1ActiveP N = fun i => if SAP.P004a.activeGroup N i then 1/2 else 1/10 := by
    exact active_propensity N
  have hhp (i : Fin N) : 0 < w1ActiveP N i ∧ w1ActiveP N i < 1 :=
    active_propensity_bounds N i
  have hbeta0 (a : Bool) :
      SAP.P004a.beta (w1ActiveP (8*r)) (SAP.P004a.activeTable (8*r))
        (SAP.P004a.activeO (8*r)) a = 0 := by
    have hb := active_population_beta (8*r) hN3 (1/2) (1/10)
      (by norm_num) (by norm_num) a
    rw [sAct_eight r] at hb
    have hbroot : AronowAudit.P004.beta
        (fun i => if AronowAudit.P004.activeGroup (8*r) i then 1/2 else 1/10)
        (AronowAudit.P004.activeTable (8*r)) (AronowAudit.P004.activeO (8*r)) a = 0 := by
      rw [hb]
      funext j
      fin_cases j <;> simp
    rw [beta_eq, activeP_eq, activeTable_eq, activeO_eq, o4_proof (8*r)]
    exact hbroot
  have hmeanRoot : AronowAudit.P004.expect
      (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
        AronowAudit.P004.activeTheta) (SAct (8*r)) = 0 := by
    rw [oc_S_mean, sAct_eight r]
    norm_num
  have hsecondRoot : AronowAudit.P004.expect
      (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
        AronowAudit.P004.activeTheta) (fun z => (SAct (8*r) z)^2) = ((8*r:ℕ):ℝ)/16 := by
    rw [oc_S_second, sAct_eight r, nH_eight r]
    push_cast
    ring
  have hvarRoot : AronowAudit.P004.variance
      (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
        AronowAudit.P004.activeTheta) (SAct (8*r)) = ((8*r:ℕ):ℝ)/16 := by
    unfold AronowAudit.P004.variance AronowAudit.P004.cov
    have hfun : (fun z : Assignment (8*r) => SAct (8*r) z * SAct (8*r) z) =
        fun z => (SAct (8*r) z)^2 := by funext z; ring
    rw [hfun, hsecondRoot, hmeanRoot]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (w1ActiveNH (8*r) = ((8*r : ℕ) : ℝ)/4) ∧
      w1ActiveNL (8*r) = 3*((8*r : ℕ) : ℝ)/4
    constructor
    · rw [activeNH_eq]
      exact hNH
    · rw [activeNL_eq]
      exact hNL
  · intro a b
    have hdiag0 : (∑ i : Fin N, activeO N i 0 * activeO N i 0) = w1ActiveNH N := by
      calc
        _ = ∑ i : Fin N, if SAP.P004a.activeGroup N i then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hg : SAP.P004a.activeGroup N i <;> simp [SAP.P004a.activeO, hg]
        _ = w1ActiveNH N := by
          simpa only [w1ActiveNH] using
            (Finset.sum_boole (fun i : Fin N => SAP.P004a.activeGroup N i) Finset.univ)
    have hdiag1 : (∑ i : Fin N, activeO N i 1 * activeO N i 1) = w1ActiveNL N := by
      calc
        _ = ∑ i : Fin N, if SAP.P004a.activeGroup N i then (0 : ℝ) else 1 := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hg : SAP.P004a.activeGroup N i <;> simp [SAP.P004a.activeO, hg]
        _ = w1ActiveNL N := by
          simpa only [w1ActiveNL, ite_not] using
            (Finset.sum_boole (fun i : Fin N => ¬ SAP.P004a.activeGroup N i) Finset.univ)
    have hcross (a b : Fin 2) (hab : a ≠ b) :
        (∑ i : Fin N, activeO N i a * activeO N i b) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hg : SAP.P004a.activeGroup N i <;> fin_cases a <;> fin_cases b <;>
        simp [SAP.P004a.activeO, hg] at *
    fin_cases a <;> fin_cases b
    · change (∑ i : Fin N, activeO N i 0 * activeO N i 0) / N = (1/4 : ℝ)
      rw [hdiag0, activeNH_eq, hNH]
      field_simp [hNreal.ne', N]
    · change (∑ i : Fin N, activeO N i 0 * activeO N i 1) / N = 0
      rw [hcross 0 1 (by decide)]
      simp
    · change (∑ i : Fin N, activeO N i 1 * activeO N i 0) / N = 0
      rw [hcross 1 0 (by decide)]
      simp
    · change (∑ i : Fin N, activeO N i 1 * activeO N i 1) / N = (3/4 : ℝ)
      rw [hdiag1, activeNL_eq, hNL]
      field_simp [hNreal.ne', N]
  · intro i
    rw [hP]
  · intro a
    exact hbeta0 a
  · have hame := o6_proof.2 (8*r)
    change SAP.P004a.ame (w1ActiveP (8*r)) (SAP.P004a.activeTable (8*r)) = 0
    rw [ame_eq, activeP_eq, activeTable_eq]
    simpa [sAct_eight r] using hame
  · -- Zero population fits leave the signed node effects, and singleton neighborhoods sum their squares.
    have hpRoot (i : Fin (8*r)) :
        0 < AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
          AronowAudit.P004.activeTheta i ∧
        AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
          AronowAudit.P004.activeTheta i < 1 := by
      rw [o4_proof (8*r)]
      by_cases h : AronowAudit.P004.activeGroup (8*r) i <;> simp [h] <;> norm_num
    have hfitRoot (i : Fin (8*r)) (a : Bool) :
        AronowAudit.P004.printedFits
          (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
            AronowAudit.P004.activeTheta)
          (AronowAudit.P004.activeTable (8*r)) (AronowAudit.P004.activeO (8*r)) i a = 0 := by
      have hb : AronowAudit.P004.beta
          (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
            AronowAudit.P004.activeTheta)
          (AronowAudit.P004.activeTable (8*r)) (AronowAudit.P004.activeO (8*r)) a = 0 := by
        simpa only [beta_eq, activeP_eq, activeTable_eq, activeO_eq] using hbeta0 a
      unfold AronowAudit.P004.printedFits
      rw [hb]
      simp [AronowAudit.P004.dot]
    have hres (i : Fin (8*r)) :
        AronowAudit.P004.residualEffect
          (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
            AronowAudit.P004.activeTheta)
          (AronowAudit.P004.activeTable (8*r))
          (fun i a => AronowAudit.P004.printedFits
            (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
              AronowAudit.P004.activeTheta)
            (AronowAudit.P004.activeTable (8*r)) (AronowAudit.P004.activeO (8*r)) i a) i =
        activeSign (8*r) i := by
      unfold AronowAudit.P004.residualEffect AronowAudit.P004.nodeEffect
      rw [active_marginal _ hpRoot i true, active_marginal _ hpRoot i false]
      simp [AronowAudit.P004.bit, hfitRoot]
    change SAP.P004a.homophilyQ (w1ActiveP (8*r)) (SAP.P004a.activeTable (8*r))
      (fun i => {i}) (fun i a => SAP.P004a.printedFits (w1ActiveP (8*r))
        (SAP.P004a.activeTable (8*r)) (SAP.P004a.activeO (8*r)) i a) = 1/4
    rw [homophily_eq, activeP_eq, activeTable_eq]
    have hg : (fun i a => SAP.P004a.printedFits
        (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
          AronowAudit.P004.activeTheta)
        (AronowAudit.P004.activeTable (8*r)) (SAP.P004a.activeO (8*r)) i a) =
      (fun i a => AronowAudit.P004.printedFits
        (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
          AronowAudit.P004.activeTheta)
        (AronowAudit.P004.activeTable (8*r)) (AronowAudit.P004.activeO (8*r)) i a) := by
      funext i a
      rw [printedFits_eq, activeO_eq]
    rw [hg]
    unfold AronowAudit.P004.homophilyQ
    simp_rw [hres]
    simp only [Finset.sum_singleton]
    have hsum : (∑ i : Fin (8*r), activeSign (8*r) i ^ 2) = nH (8*r) :=
      sum_activeSign_sq (8*r)
    have hsumMul : (∑ i : Fin (8*r),
        activeSign (8*r) i * activeSign (8*r) i) = nH (8*r) := by
      calc
        _ = ∑ i : Fin (8*r), activeSign (8*r) i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = nH (8*r) := hsum
    rw [hsumMul, hNH]
    field_simp [hNreal.ne']
    <;> ring
  · intro z
    -- Actual fitted IPW uses the clipped high-group MLE.
    have hi := o6_proof.1 (8*r) hNpos z
    change SAP.P004a.fittedIPW (SAP.P004a.activeTable (8*r))
      (SAP.P004a.activeO (8*r)) (w1ActiveMLE (8*r)) z = _
    rw [fittedIPW_eq, activeTable_eq, activeO_eq, active_mle_fun_eq]
    simpa [active_sum_eq, activePH_eq] using hi
  · intro z
    -- The fitted population coefficients vanish, so the augmented score is 2S/N.
    have hfit (i : Fin (8*r)) (a : Bool) :
        SAP.P004a.printedFits (w1ActiveP (8*r)) (SAP.P004a.activeTable (8*r))
          (SAP.P004a.activeO (8*r)) i a = 0 := by
      unfold SAP.P004a.printedFits
      rw [hbeta0 a]
      simp [SAP.P004a.dot]
    have hfitRoot (i : Fin (8*r)) (a : Bool) :
        AronowAudit.P004.printedFits
          (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
            AronowAudit.P004.activeTheta)
          (AronowAudit.P004.activeTable (8*r)) (AronowAudit.P004.activeO (8*r)) i a = 0 := by
      simpa only [printedFits_eq, activeP_eq, activeTable_eq, activeO_eq] using hfit i a
    have hpval (i : Fin (8*r)) :
        AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
          AronowAudit.P004.activeTheta i =
        if AronowAudit.P004.activeGroup (8*r) i then 1/2 else 1/10 := by
      exact congrFun (o4_proof (8*r)) i
    have hG : (fun i a => AronowAudit.P004.printedFits
        (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
          AronowAudit.P004.activeTheta)
        (AronowAudit.P004.activeTable (8*r)) (AronowAudit.P004.activeO (8*r)) i a) =
      (fun _ _ => (0 : ℝ)) := by
      funext i a
      exact hfitRoot i a
    have hterm (i : Fin (8*r)) :
        AronowAudit.P004.bit (z i) * AronowAudit.P004.activeTable (8*r) i z /
              AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
                AronowAudit.P004.activeTheta i -
          (1-AronowAudit.P004.bit (z i)) * AronowAudit.P004.activeTable (8*r) i z /
              (1-AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
                AronowAudit.P004.activeTheta i) =
        2*activeSign (8*r) i*AronowAudit.P004.bit (z i) := by
      rw [hpval]
      by_cases hg : AronowAudit.P004.activeGroup (8*r) i
      · rw [if_pos hg, activeTable_eq_sign]
        cases hz : z i <;> simp [AronowAudit.P004.bit, hz] <;> ring
      · rw [if_neg hg, activeTable_eq_sign, activeSign_of_not_group i hg]
        cases hz : z i <;> simp [AronowAudit.P004.bit, hz] <;> ring
    change SAP.P004a.augmented (w1ActiveP (8*r)) (SAP.P004a.activeTable (8*r))
      (fun i a => SAP.P004a.printedFits (w1ActiveP (8*r)) (SAP.P004a.activeTable (8*r))
        (SAP.P004a.activeO (8*r)) i a) z = 2*w1ActiveS (8*r) z/(8*r:ℕ)
    rw [augmented_eq, activeP_eq, activeTable_eq]
    rw [activeO_eq]
    change AronowAudit.P004.augmented
      (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r)) AronowAudit.P004.activeTheta)
      (AronowAudit.P004.activeTable (8*r))
      (fun i a => AronowAudit.P004.printedFits
        (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
          AronowAudit.P004.activeTheta)
        (AronowAudit.P004.activeTable (8*r)) (AronowAudit.P004.activeO (8*r)) i a) z = _
    rw [hG]
    unfold AronowAudit.P004.augmented
    simp only [sub_self, add_zero, zero_add, sub_zero]
    have hsum : (∑ i : Fin (8*r),
        (AronowAudit.P004.bit (z i) * AronowAudit.P004.activeTable (8*r) i z /
              AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
                AronowAudit.P004.activeTheta i -
          (1-AronowAudit.P004.bit (z i)) * AronowAudit.P004.activeTable (8*r) i z /
              (1-AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
                AronowAudit.P004.activeTheta i))) = 2*SAct (8*r) z := by
      calc
        _ = ∑ i : Fin (8*r), 2*activeSign (8*r) i*
              AronowAudit.P004.bit (z i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i
        _ = 2*SAct (8*r) z := by
          unfold SAct
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    rw [hsum, active_sum_eq]
  · -- Bernoulli first moment
    change SAP.P004a.expect (w1ActiveP (8*r)) (w1ActiveS (8*r)) = 0
    change AronowAudit.P004.expect
      (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
        AronowAudit.P004.activeTheta) (SAct (8*r)) = 0
    exact hmeanRoot
  · -- Bernoulli variance via the second moment
    change SAP.P004a.variance (w1ActiveP (8*r)) (w1ActiveS (8*r)) = ((8*r:ℕ):ℝ)/16
    change AronowAudit.P004.variance
      (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
        AronowAudit.P004.activeTheta) (SAct (8*r)) = ((8*r:ℕ):ℝ)/16
    exact hvarRoot
  · -- Scaled linearized variance
    change SAP.P004a.variance (w1ActiveP (8*r))
      (fun z => 2*w1ActiveS (8*r) z/(8*r:ℕ)) = 1/(4*(8*r:ℕ))
    change AronowAudit.P004.variance
      (AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r)) AronowAudit.P004.activeTheta)
      (fun z => 2*SAct (8*r) z/(8*r:ℕ)) = _
    have hfun : (fun z : Assignment (8*r) => 2*SAct (8*r) z/(8*r:ℕ)) =
        fun z => SAct (8*r) z/(((8*r:ℕ):ℝ)/2) := by
      funext z
      field_simp [hNreal.ne']
      <;> ring
    rw [hfun, AronowAudit.P004.variance_div, hvarRoot]
    field_simp [hNreal.ne']
    <;> ring
  · intro z
    -- fitted true-arm beta
    have hb := active_fitted_beta (8*r) hN3 z true
    simpa only [fittedBeta_eq, propensities_eq, activeO_eq, activeTable_eq,
      active_mle_fun_eq, active_sum_eq, activeNH_eq, activePH_eq, if_true] using hb
  · intro z
    have hb := active_fitted_beta (8*r) hN3 z false
    have hv : ![if false then SAct (8*r) z / (nH (8*r)*pHatH (8*r) z) else 0, 0] =
        (0 : Fin 2 → ℝ) := by
      ext j
      fin_cases j <;> simp
    rw [hv] at hb
    simpa only [fittedBeta_eq, propensities_eq, activeO_eq, activeTable_eq,
      active_mle_fun_eq] using hb
  · intro z
    have hq := pHatH_mem N z
    have hq' : (1/20 : ℝ) ≤ w1ActivePH N z ∧ w1ActivePH N z ≤ 19/20 := by
      rw [activePH_eq]
      exact clip_bounds (KAct N z / nH N)
    have hprop := active_fitted_propensities hN3 z
    have hinfo : AronowAudit.P004.information
        (AronowAudit.P004.propensities (AronowAudit.P004.activeO N) (activeMLE N z))
        (AronowAudit.P004.activeO N) =
      Matrix.diagonal ![nH N * pHatH N z * (1-pHatH N z) / N,
        nL N * pHatL N z * (1-pHatL N z) / N] := by
      rw [hprop]
      exact active_information N (pHatH N z) (pHatL N z)
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hph := pHatH_mem N z
    have hpl := pHatL_mem N z
    have hdH : nH N * pHatH N z * (1-pHatH N z) / N ≠ 0 :=
      div_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (nH_pos hNpos))
        (ne_of_gt hph.1)) (ne_of_gt (sub_pos.mpr hph.2))) hNr
    have hdL : nL N * pHatL N z * (1-pHatL N z) / N ≠ 0 :=
      div_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (nL_pos hN3))
        (ne_of_gt hpl.1)) (ne_of_gt (sub_pos.mpr hpl.2))) hNr
    have hdet : IsUnit
        (AronowAudit.P004.information
          (AronowAudit.P004.propensities (AronowAudit.P004.activeO N) (activeMLE N z))
          (AronowAudit.P004.activeO N)).det := by
      rw [hinfo, Matrix.det_diagonal]
      apply isUnit_iff_ne_zero.mpr
      simp only [Fin.prod_univ_two]
      exact mul_ne_zero hdH hdL
    have hdetSap : IsUnit
        (SAP.P004a.information
          (SAP.P004a.propensities (SAP.P004a.activeO N) (w1ActiveMLE N z))
          (SAP.P004a.activeO N)).det := by
      simpa only [information_eq, propensities_eq, activeO_eq, active_mle_fun_eq] using hdet
    exact ⟨hq'.1, hq'.2, hdetSap⟩
  · intro z
    -- Exact printed-variance identity from O7.
    have ho7 := o7_proof (8*r) hN3 z
    have hB : (fun i : Fin (8*r) => ({i} : Finset (Fin (8*r)))) =
        AronowAudit.P004.spatialNeighborhoods AronowAudit.P004.activePopulation 0 (8*r) := by
      funext i
      exact (active_zero_neighborhood (8*r) i).symm
    change SAP.P004a.printedSAH
      (SAP.P004a.propensities (SAP.P004a.activeO (8*r)) (w1ActiveMLE (8*r) z))
      (SAP.P004a.activeTable (8*r)) (fun i => {i}) (w1ActiveFits (8*r) z) z = _
    rw [printedSAH_eq, propensities_eq, activeO_eq, activeTable_eq,
      activeFits_root_eq]
    rw [active_mle_fun_eq, hB]
    rw [ho7, activePH_eq, ← activeR_eq]
    rfl
  · -- Positive actual variance: paired assignments have S=±1 and the same clipped count.
    let iPlus : Fin (8*r) := ⟨0, by omega⟩
    let iMinus : Fin (8*r) := ⟨1, by omega⟩
    let zPlus : Assignment (8*r) := fun i => if i = iPlus then true else false
    let zMinus : Assignment (8*r) := fun i => if i = iMinus then true else false
    have hSplus : SAct (8*r) zPlus = 1 := by
      unfold SAct
      rw [Finset.sum_eq_single iPlus]
      · norm_num [zPlus, iPlus, activeSign, AronowAudit.P004.bit]
      · intro j hj hji
        simp [zPlus, hji, AronowAudit.P004.bit]
      · simp
    have hSminus : SAct (8*r) zMinus = -1 := by
      unfold SAct
      rw [Finset.sum_eq_single iMinus]
      · norm_num [zMinus, iMinus, activeSign, AronowAudit.P004.bit]
      · intro j hj hji
        simp [zMinus, hji, AronowAudit.P004.bit]
      · simp
    have hKplus : KAct (8*r) zPlus = 1 := by
      unfold KAct
      rw [Finset.sum_eq_single iPlus]
      · norm_num [zPlus, iPlus, AronowAudit.P004.activeGroup, AronowAudit.P004.bit]
      · intro j hj hji
        simp [zPlus, hji, AronowAudit.P004.bit]
      · simp
    have hKminus : KAct (8*r) zMinus = 1 := by
      unfold KAct
      rw [Finset.sum_eq_single iMinus]
      · norm_num [zMinus, iMinus, AronowAudit.P004.activeGroup, AronowAudit.P004.bit]
      · intro j hj hji
        simp [zMinus, hji, AronowAudit.P004.bit]
      · simp
    have hPHsame : pHatH (8*r) zPlus = pHatH (8*r) zMinus := by
      simp [pHatH, hKplus, hKminus]
    have hIPWplus := o6_proof.1 (8*r) hNpos zPlus
    have hIPWminus := o6_proof.1 (8*r) hNpos zMinus
    have hvalPlus : AronowAudit.P004.fittedIPW
        (AronowAudit.P004.activeTable (8*r)) (AronowAudit.P004.activeO (8*r))
        (activeMLE (8*r)) zPlus = 1 / ((8*r:ℕ) * pHatH (8*r) zPlus) := by
      rw [hSplus] at hIPWplus
      norm_num at hIPWplus ⊢
      exact hIPWplus
    have hvalMinus : AronowAudit.P004.fittedIPW
        (AronowAudit.P004.activeTable (8*r)) (AronowAudit.P004.activeO (8*r))
        (activeMLE (8*r)) zMinus = -1 / ((8*r:ℕ) * pHatH (8*r) zPlus) := by
      rw [hSminus, ← hPHsame] at hIPWminus
      norm_num at hIPWminus ⊢
      exact hIPWminus
    have hden : ((8*r:ℕ):ℝ) * pHatH (8*r) zPlus ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (show 8*r ≠ 0 by omega))
        (ne_of_gt (pHatH_mem (8*r) zPlus).1)
    have hneq : AronowAudit.P004.fittedIPW
        (AronowAudit.P004.activeTable (8*r)) (AronowAudit.P004.activeO (8*r))
        (activeMLE (8*r)) zPlus ≠ AronowAudit.P004.fittedIPW
        (AronowAudit.P004.activeTable (8*r)) (AronowAudit.P004.activeO (8*r))
        (activeMLE (8*r)) zMinus := by
      rw [hvalPlus, hvalMinus]
      intro he
      have hpos : 0 < 1 / (((8*r:ℕ):ℝ) * pHatH (8*r) zPlus) :=
        div_pos (by norm_num) (mul_pos (by exact_mod_cast (show 0 < 8*r by omega))
          (pHatH_mem (8*r) zPlus).1)
      have he' : 1 / (((8*r:ℕ):ℝ) * pHatH (8*r) zPlus) =
          -(1 / (((8*r:ℕ):ℝ) * pHatH (8*r) zPlus)) := by
        simpa only [neg_div] using he
      have hx :
          1 / (((8*r:ℕ):ℝ) * pHatH (8*r) zPlus) +
            1 / (((8*r:ℕ):ℝ) * pHatH (8*r) zPlus) = 0 := by
        calc
          _ = -(1 / (((8*r:ℕ):ℝ) * pHatH (8*r) zPlus)) +
              1 / (((8*r:ℕ):ℝ) * pHatH (8*r) zPlus) := congrArg
                (fun x : ℝ => x + 1 / (((8*r:ℕ):ℝ) * pHatH (8*r) zPlus)) he'
          _ = 0 := by ring
      have hxpos : 0 <
          1 / (((8*r:ℕ):ℝ) * pHatH (8*r) zPlus) +
            1 / (((8*r:ℕ):ℝ) * pHatH (8*r) zPlus) := add_pos hpos hpos
      linarith
    have hpRoot : ∀ i : Fin (8*r),
        0 < AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
          AronowAudit.P004.activeTheta i ∧
        AronowAudit.P004.propensities (AronowAudit.P004.activeO (8*r))
          AronowAudit.P004.activeTheta i < 1 := by
      intro i
      rw [← activeP_eq]
      exact hhp i
    rw [variance_eq, activeP_eq, activeIPW_fun_eq]
    exact variance_pos_of_two_values _ hpRoot _ zPlus zMinus hneq
