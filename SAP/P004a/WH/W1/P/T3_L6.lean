import SAP.P004a.WH.W1.Leaves
import AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T3_L6

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section
set_option maxHeartbeats 1000000

lemma active_mle_eq (N : ℕ) (z : Assignment N) :
    w1ActiveMLE N z = AronowAudit.P004.Wave1.ObservationalCoverage.activeMLE N z := by
  rfl

lemma active_sign_zero_of_not_group (N : ℕ) (i : Fin N)
    (hi : ¬ activeGroup N i) :
    AronowAudit.P004.Wave1.ObservationalCoverage.activeSign N i = 0 := by
  by_cases h0 : i.val % 8 = 0
  · exfalso
    apply hi
    unfold activeGroup
    omega
  · by_cases h1 : i.val % 8 = 1
    · exfalso
      apply hi
      unfold activeGroup
      omega
    · simp [AronowAudit.P004.Wave1.ObservationalCoverage.activeSign, h0, h1]

lemma finite_expansion_identity (hfinite : T3FiniteStatement)
    (r : ℕ) (hr : 0 < r) (z : Assignment (8*r)) :
    fittedIPW (circleAverage (activePopulation (8*r)) 0)
        (activeO (8*r)) (w1ActiveMLE (8*r)) z -
      (ht (w1ActiveP (8*r)) (circleAverage (activePopulation (8*r)) 0) z -
        (∑ i, (bit (z i)-w1ActiveP (8*r) i) *
          dot (activeO (8*r) i)
            (scoreGamma (w1ActiveP (8*r))
              (circleAverage (activePopulation (8*r)) 0)
              (activeO (8*r)))) / (8*r : ℕ)) =
      w1ActiveIPW (8*r) z - 2*w1ActiveS (8*r) z/(8*r : ℕ) := by
  let N := 8*r
  have hF := hfinite r hr
  dsimp only at hF
  rcases hF with ⟨hcounts,hgram,hp,hbeta,hame,hQ,hIPW,haug,hES,hvarS,hvarAug,
    hfitT,hfitF,hclip,hV,hvarPos⟩
  have hpEq : w1ActiveP N = fun i => if activeGroup N i then (1/2 : ℝ) else 1/10 := by
    funext i
    exact hp i
  have hN3 : 3 ≤ N := by dsimp [N]; omega
  have hbetaFun :
      AronowAudit.P004.beta (fun i => if activeGroup N i then (1/2 : ℝ) else 1/10)
        (AronowAudit.P004.activeTable N) (AronowAudit.P004.activeO N) true = 0 := by
    rw [← hpEq]
    exact hbeta true
  have hbetaFormula :=
    AronowAudit.P004.Wave1.ObservationalCoverage.active_population_beta N hN3
      (1/2) (1/10) (by norm_num) (by norm_num) true
  have hratio : (AronowAudit.P004.Wave1.ObservationalCoverage.sAct N) /
      (AronowAudit.P004.Wave1.ObservationalCoverage.nH N) = 0 := by
    have hvec := congrArg (fun v : Fin 2 → ℝ => v 0)
      (hbetaFormula.symm.trans hbetaFun)
    change (AronowAudit.P004.bit true *
      AronowAudit.P004.Wave1.ObservationalCoverage.sAct N /
      AronowAudit.P004.Wave1.ObservationalCoverage.nH N) = 0 at hvec
    simpa only [AronowAudit.P004.bit, if_true, one_mul] using hvec
  have hNHpos : 0 < w1ActiveNH N := by
    rw [hcounts.1]
    positivity
  have hnhne : AronowAudit.P004.Wave1.ObservationalCoverage.nH N ≠ 0 := by
    have hEq : AronowAudit.P004.Wave1.ObservationalCoverage.nH N = w1ActiveNH N := rfl
    rw [hEq]
    exact (ne_of_gt hNHpos)
  have hsAct : AronowAudit.P004.Wave1.ObservationalCoverage.sAct N = 0 := by
    calc
      AronowAudit.P004.Wave1.ObservationalCoverage.sAct N =
          (AronowAudit.P004.Wave1.ObservationalCoverage.sAct N /
            AronowAudit.P004.Wave1.ObservationalCoverage.nH N) *
            AronowAudit.P004.Wave1.ObservationalCoverage.nH N := by
            field_simp [hnhne]
      _ = 0 := by rw [hratio]; ring
  have hMarg (i : Fin N) (a : Bool) :
      AronowAudit.P004.marginal (w1ActiveP N) (AronowAudit.P004.activeTable N) i a =
      AronowAudit.P004.Wave1.ObservationalCoverage.activeSign N i * bit a := by
    have hpp : ∀ i, 0 < w1ActiveP N i ∧ w1ActiveP N i < 1 := by
      intro j
      have hjEq := congrFun hpEq j
      rw [hjEq]
      by_cases hj : activeGroup N j <;> simp [hj] <;> norm_num
    exact AronowAudit.P004.Wave1.ObservationalCoverage.active_marginal
      (w1ActiveP N) hpp i a
  have hrow0 (i : Fin N) :
      ((1-w1ActiveP N i) *
          AronowAudit.P004.marginal (w1ActiveP N) (AronowAudit.P004.activeTable N) i true +
        w1ActiveP N i *
          AronowAudit.P004.marginal (w1ActiveP N) (AronowAudit.P004.activeTable N) i false) *
        AronowAudit.P004.activeO N i 0 = (1/2 : ℝ) *
          AronowAudit.P004.Wave1.ObservationalCoverage.activeSign N i := by
    rw [hMarg i true, hMarg i false]
    by_cases hi : activeGroup N i
    · have hpi : w1ActiveP N i = (1/2 : ℝ) := by rw [hpEq]; simp [hi]
      have hi' : i.val % 8 < 2 := by simpa [activeGroup] using hi
      have hO : AronowAudit.P004.activeO N i 0 = 1 := by
        simp [AronowAudit.P004.activeO, AronowAudit.P004.activeGroup, hi']
      rw [hpi, hO]
      have hbt : bit true = (1 : ℝ) := by simp [bit]
      have hbf : bit false = (0 : ℝ) := by simp [bit]
      rw [hbt, hbf]
      ring
    · have hz := active_sign_zero_of_not_group N i hi
      simp [hi, hz, AronowAudit.P004.activeO, bit]
  have hrow1 (i : Fin N) :
      ((1-w1ActiveP N i) *
          AronowAudit.P004.marginal (w1ActiveP N) (AronowAudit.P004.activeTable N) i true +
        w1ActiveP N i *
          AronowAudit.P004.marginal (w1ActiveP N) (AronowAudit.P004.activeTable N) i false) *
        AronowAudit.P004.activeO N i 1 = 0 := by
    rw [hMarg i true, hMarg i false]
    by_cases hi : activeGroup N i
    · have hi' : i.val % 8 < 2 := by simpa [activeGroup] using hi
      have hO : AronowAudit.P004.activeO N i 1 = 0 := by
        simp [AronowAudit.P004.activeO, AronowAudit.P004.activeGroup, hi']
      rw [hO]
      simp [bit]
    · have hz := active_sign_zero_of_not_group N i hi
      simp [hi, hz, AronowAudit.P004.activeO, bit]
  have hsum0 :
      (∑ i : Fin N,
        ((1-w1ActiveP N i) *
            AronowAudit.P004.marginal (w1ActiveP N) (AronowAudit.P004.activeTable N) i true +
          w1ActiveP N i *
            AronowAudit.P004.marginal (w1ActiveP N) (AronowAudit.P004.activeTable N) i false) *
          AronowAudit.P004.activeO N i 0) = 0 := by
    calc
        _ = ∑ i : Fin N, (1/2 : ℝ) *
            AronowAudit.P004.Wave1.ObservationalCoverage.activeSign N i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hrow0 i
      _ = 0 := by rw [show (∑ i : Fin N, (1/2 : ℝ) *
          AronowAudit.P004.Wave1.ObservationalCoverage.activeSign N i) =
          (1/2 : ℝ) * AronowAudit.P004.Wave1.ObservationalCoverage.sAct N by
            simp [AronowAudit.P004.Wave1.ObservationalCoverage.sAct, Finset.mul_sum], hsAct]
        <;> norm_num
  have hsum1 :
      (∑ i : Fin N,
        ((1-w1ActiveP N i) *
            AronowAudit.P004.marginal (w1ActiveP N) (AronowAudit.P004.activeTable N) i true +
          w1ActiveP N i *
            AronowAudit.P004.marginal (w1ActiveP N) (AronowAudit.P004.activeTable N) i false) *
          AronowAudit.P004.activeO N i 1) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hrow1 i
  have hscoreNum : (fun j : Fin 2 =>
      (∑ i : Fin N,
        ((1-w1ActiveP N i) *
            AronowAudit.P004.marginal (w1ActiveP N) (AronowAudit.P004.activeTable N) i true +
          w1ActiveP N i *
            AronowAudit.P004.marginal (w1ActiveP N) (AronowAudit.P004.activeTable N) i false) *
          AronowAudit.P004.activeO N i j) / N) = 0 := by
    funext j
    fin_cases j
    · simp [hsum0]
    · simp [hsum1]
  have hgamma : AronowAudit.P004.scoreGamma (w1ActiveP N)
      (AronowAudit.P004.activeTable N) (AronowAudit.P004.activeO N) = 0 := by
    unfold AronowAudit.P004.scoreGamma
    rw [hscoreNum]
    simp
  have hgammaSAP : scoreGamma (w1ActiveP N) (activeTable N) (activeO N) = 0 := by
    exact hgamma
  have hfitZero : printedFits (w1ActiveP N) (activeTable N) (activeO N) = fun _ _ => 0 := by
    funext i a
    have hb : beta (w1ActiveP N) (activeTable N) (activeO N) a = 0 := hbeta a
    simp [printedFits, hb, dot]
  have haugHt (z : Assignment N) :
      augmented (w1ActiveP N) (activeTable N)
        (printedFits (w1ActiveP N) (activeTable N) (activeO N)) z =
        ht (w1ActiveP N) (activeTable N) z := by
    rw [hfitZero]
    simp [augmented, ht]
  have hht (z : Assignment N) :
      ht (w1ActiveP N) (activeTable N) z =
        2*w1ActiveS N z/N := by
    have hh := haug z
    rw [haugHt] at hh
    simpa [N] using hh
  have hR : circleAverage (activePopulation N) 0 = activeTable N := by
    calc
      circleAverage (activePopulation N) 0 =
          AronowAudit.P004.circleAverage (Bridge.toPopulation (activePopulation N)) 0 :=
            (Bridge.circleAverage_eq (activePopulation N) 0).symm
      _ = AronowAudit.P004.circleAverage (AronowAudit.P004.activePopulation N) 0 := by
            rw [Bridge.activePopulation_eq]
      _ = AronowAudit.P004.activeTable N :=
            AronowAudit.P004.Wave1.LinePopulation.n3_proof _
      _ = activeTable N := rfl
  have hIPWdef : fittedIPW (activeTable N) (activeO N) (w1ActiveMLE N) z =
      w1ActiveIPW N z := by
    rfl
  change fittedIPW (circleAverage (activePopulation N) 0) (activeO N)
      (w1ActiveMLE N) z -
      (ht (w1ActiveP N) (circleAverage (activePopulation N) 0) z -
        (∑ i, (bit (z i)-w1ActiveP N i) *
          dot (activeO N i)
            (scoreGamma (w1ActiveP N) (circleAverage (activePopulation N) 0)
              (activeO N))) / N) =
      w1ActiveIPW N z - 2*w1ActiveS N z/N
  rw [hR, hgammaSAP, hht]
  simp [dot, hIPWdef]

end
end SAP.P004a.WH.W1.P.T3_L6

open SAP.P004a SAP.P004a.WH.W1
open SAP.P004a.WH.W1.P.T3_L6
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal

/-- Prove the requested order bound using the actual-MLE corrected expansion. -/
theorem SAP.P004a.WH.W1.T3_L6_proof : SAP.P004a.WH.W1.T3_L6 := by
  intro hfinite
  let P : AronowAudit.P004.PopulationSequence
      (fun _ : ℕ => EuclideanSpace ℝ (Fin 2)) :=
    fun N => Bridge.toPopulation (activePopulation N)
  have hPseq : P = fun N => AronowAudit.P004.activePopulation N := by
    funext N
    exact Bridge.activePopulation_eq N
  have hP : AronowAudit.P004.SpatialLocalConditions P := by
    rw [hPseq]
    exact AronowAudit.P004.Wave1.T3_spatial
  have hWD : ∀ᶠ N in atTop, AronowAudit.P004.WellDefined (P N) 0 := by
    rw [hPseq]
    exact Filter.Eventually.of_forall fun N =>
      AronowAudit.P004.Wave1.LinePopulation.n4_proof (AronowAudit.P004.activeTable N) 0 le_rfl
  have hloc : ∀ᶠ N in atTop,
      AronowAudit.P004.LocalAt (AronowAudit.P004.circleAverage (P N) 0)
        (AronowAudit.P004.nodeSeparation (P N)) 0 := by
    rw [hPseq]
    filter_upwards [] with N
    change AronowAudit.P004.LocalAt
      (AronowAudit.P004.circleAverage
        (AronowAudit.P004.linePopulation (AronowAudit.P004.activeTable N)) 0)
      (AronowAudit.P004.nodeSeparation (AronowAudit.P004.activePopulation N)) 0
    rw [AronowAudit.P004.Wave1.LinePopulation.n3_proof]
    exact AronowAudit.P004.Wave1.ObservationalCoverage.o1_proof.2.2 N
  have hlog : AronowAudit.P004.LogisticConditions AronowAudit.P004.activeO
      AronowAudit.P004.activeTheta AronowAudit.P004.activeParameterSet w1ActiveMLE := by
    have hMLEfun : w1ActiveMLE =
        AronowAudit.P004.Wave1.ObservationalCoverage.activeMLE := by
      funext N z
      exact SAP.P004a.WH.W1.P.T3_L6.active_mle_eq N z
    simpa only [AronowAudit.P004.Wave1.ObservationalCoverage.O3, hMLEfun] using
      AronowAudit.P004.Wave1.ObservationalCoverage.o3_proof
  have hinterior : AronowAudit.P004.activeTheta ∈ interior AronowAudit.P004.activeParameterSet :=
    AronowAudit.P004.Wave1.T3_interior
  have hoverlap : AronowAudit.P004.Overlap
      (fun N => AronowAudit.P004.propensities (AronowAudit.P004.activeO N)
        AronowAudit.P004.activeTheta) := AronowAudit.P004.Wave1.T3_overlap
  have hexp : BigOp (fun N => w1ActiveP N)
      (fun N z => fittedIPW (circleAverage (activePopulation N) 0)
          (activeO N) (w1ActiveMLE N) z -
        (ht (w1ActiveP N) (circleAverage (activePopulation N) 0) z -
          (∑ i, (bit (z i)-w1ActiveP N i) *
            dot (activeO N i)
              (scoreGamma (w1ActiveP N) (circleAverage (activePopulation N) 0)
                (activeO N))) / N))
      (fun N => (N : ℝ)⁻¹) := by
    exact AronowAudit.P004.Wave1.T2_ipw_expansion P AronowAudit.P004.activeO
      AronowAudit.P004.activeTheta AronowAudit.P004.activeParameterSet w1ActiveMLE
      0 0 le_rfl hP hWD hloc hlog hinterior hoverlap
  change W1BigOp (fun r => 8*r) (fun r => w1ActiveP (8*r))
    (fun r z => w1ActiveIPW (8*r) z-2*w1ActiveS (8*r) z/(8*r : ℕ))
    (fun r => ((8*r : ℕ) : ℝ)⁻¹)
  intro ε hε
  obtain ⟨C,hC,hE⟩ := hexp ε hε
  refine ⟨C,hC,?_⟩
  filter_upwards [(multiples_tendsto 8 (by norm_num)).eventually hE,
    eventually_gt_atTop 0] with r hN hr
  have hpoint := SAP.P004a.WH.W1.P.T3_L6.finite_expansion_identity hfinite r hr
  simpa only [hpoint] using hN

