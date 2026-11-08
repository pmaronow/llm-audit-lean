import SAP.P004a.WH.W1.Finite
import AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section
set_option maxHeartbeats 1000000

/-- Restricting a limit to positive integer multiples preserves its limit. -/
theorem multiples_tendsto (c : ℕ) (hc : 0 < c) : Tendsto (fun k : ℕ => c*k) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with k hk
  exact hk.trans (by nlinarith)

/-- Instantiate the existing actual-MLE expansion and substitute the exact balanced score
coefficient. The order-N⁻¹ expansion itself needs no new stochastic lemma. -/
theorem three_expansion (θhat : ∀ N, Assignment N → Fin 2 → ℝ)
    (hlog : LogisticConditions threeTypeONat threeTypeTheta threeTypeParameterSet θhat) :
    T1ExpansionStatement θhat := by
  rcases three_spatial with ⟨hP,hi,_hl,_hu,_hb,_hO,hπ,hWD,_hc,hloc,_hB,_hSp⟩
  have he : BigOp w1ThreeP (fun N z => w1ThreeIPW θhat N z -
      (ht (w1ThreeP N) (circleAverage (threeTypePopulation N) 0) z -
        (∑ i, (bit (z i)-w1ThreeP N i)*dot (threeTypeONat N i)
          (scoreGamma (w1ThreeP N) (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)))/N))
        (fun N => (N : ℝ)⁻¹) :=
    AronowAudit.P004.Wave1.T2_ipw_expansion (Bridge.toSequence threeTypePopulation)
      threeTypeONat threeTypeTheta threeTypeParameterSet θhat 0 0 le_rfl hP
      (Eventually.of_forall fun N => hWD N 0 le_rfl)
      (Eventually.of_forall fun N => hloc N 0 le_rfl) hlog hi
      ⟨1/10,by norm_num,by norm_num,hπ⟩
  intro ε hε
  obtain ⟨C,hC,hE⟩ := he ε hε
  refine ⟨C,hC,?_⟩
  filter_upwards [(multiples_tendsto 3 (by omega)).eventually hE, eventually_gt_atTop 0] with K hK hpos
  have ha := (three_linear K hpos).2.1
  simpa only [ha] using hK

/-- The actual fitted-IPW variance limit is a proved second-moment result, not a conclusion
inferred from the Gaussian limit. -/
theorem active_variance_limit :
    Tendsto (fun r => (8*r : ℕ)*variance (w1ActiveP (8*r)) (w1ActiveIPW (8*r)))
      atTop (nhds (1/4 : ℝ)) := by
  have he (N : ℕ) : circleAverage (activePopulation N) 0 = activeTable N :=
    AronowAudit.P004.Wave1.LinePopulation.n3_proof _
  have h : Tendsto (fun (N : ℕ) => (N : ℝ)*variance (w1ActiveP N)
      (fittedIPW (circleAverage (activePopulation N) 0) (activeO N) (w1ActiveMLE N)))
      atTop (nhds (1/4 : ℝ)) := AronowAudit.P004.Wave1.T3_actual_variance_limit
  simp_rw [he] at h
  exact h.comp (multiples_tendsto 8 (by omega))

/-- All finite statistical comparisons for T5 follow from the analytic realization and
four-assignment algebra already supplied by `two_node_effect`. -/
theorem area_cases (hr : ∀ c : Fin 3, W1AreaRealization (w1AreaShares c)) : T5CaseStatement := by
  have htab (c : Fin 3) (j : Fin 6) : circleAverage (w1AreaCase c) j =
      fun i z => w1AreaShares c j (z i) := by
    funext i z
    exact (hr c).2.1 j i z
  have hwhole (c : Fin 3) : circleAverage (w1AreaCase c) 6 =
      fun i z => ∑ j : Fin 6, (2*(j : ℝ)+1)/36*w1AreaShares c j (z i) := by
    funext i z
    exact (hr c).2.2 i z
  have hbin (c : Fin 3) (j : Fin 6) :
      hajek (circleAverage (w1AreaCase c) j) areaWitnessAssignment = w1AreaShares c j true-1/10 ∧
      ame (fun _ => 1/2) (circleAverage (w1AreaCase c) j) = w1AreaShares c j true-1/10 := by
    rw [htab]
    simpa only [w1AreaShares, Bool.false_eq_true, ite_false] using two_node_effect (w1AreaShares c j)
  have hw (c : Fin 3) :
      hajek (circleAverage (w1AreaCase c) 6) areaWitnessAssignment = w1AreaCaseEffect c ∧
      ame (fun _ => 1/2) (circleAverage (w1AreaCase c) 6) = w1AreaCaseEffect c := by
    rw [hwhole]
    have h := two_node_effect (fun a => ∑ j : Fin 6, (2*(j : ℝ)+1)/36*w1AreaShares c j a)
    have hn : (∑ j : Fin 6, (2*(j : ℝ)+1)/36*w1AreaShares c j true) -
        (∑ j : Fin 6, (2*(j : ℝ)+1)/36*w1AreaShares c j false) = w1AreaCaseEffect c := by
      fin_cases c <;> norm_num [w1AreaShares,w1AreaCaseEffect,Fin.sum_univ_succ]
    simpa only [hn] using h
  refine ⟨by norm_num [armCount,areaWitnessAssignment,Fin.sum_univ_two],
    by norm_num [armCount,areaWitnessAssignment,Fin.sum_univ_two], ?_,hr,hbin,?_,by norm_num [w1AreaCaseEffect],?_⟩
  · intro c j a
    fin_cases c <;> fin_cases j <;> cases a <;> norm_num [w1AreaShares]
  · intro c
    refine ⟨?_,?_,(hw c).1,(hw c).2,?_⟩
    · simp_rw [(hbin c _).1]
      fin_cases c <;> norm_num [w1AreaShares,Fin.sum_univ_succ]
    · simp_rw [(hbin c _).2]
      fin_cases c <;> norm_num [w1AreaShares,Fin.sum_univ_succ]
    · fin_cases c <;> norm_num [w1AreaCaseEffect]
  · intro j
    fin_cases j <;> norm_num [w1AreaShares]

/-- The fitted raw SAH formula is direct finite algebra using the existing fitted coefficients. -/
theorem active_raw_formula :
    ∀ r : ℕ, 0 < r → ∀ z : Assignment (8*r),
      w1ActiveVRaw (8*r) z = w1ActiveR (8*r) z/(((8*r : ℕ) : ℝ)^2*(w1ActivePH (8*r) z)^2) := by
  intro r hr z
  let N := 8*r
  have hN : 3 ≤ N := by dsimp [N]; omega
  have hf (i : Fin N) (a : Bool) : w1ActiveFits N z i a =
      if activeGroup N i then (if a then w1ActiveS N z/(w1ActiveNH N*w1ActivePH N z) else 0) else 0 :=
    AronowAudit.P004.Wave1.ObservationalCoverage.active_fitted_fit N hN z i a
  have hp : propensities (activeO N) (w1ActiveMLE N z) =
      fun i => if activeGroup N i then w1ActivePH N z else w1ActivePL N z :=
    AronowAudit.P004.Wave1.ObservationalCoverage.active_fitted_propensities hN z
  change rawSAH (propensities (activeO N) (w1ActiveMLE N z)) (activeTable N)
    (fun i => {i}) (w1ActiveFits N z) z = _
  unfold rawSAH w1ActiveR
  rw [hp,div_mul_eq_div_div,div_right_comm]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [N] at hf ⊢
  by_cases hi : activeGroup (8*r) i
  · cases hz : z i <;> simp [hi,hf,activeTable,w1ActiveSign,bit,hz]
  · have hsign : w1ActiveSign (8*r) i = 0 :=
      AronowAudit.P004.Wave1.ObservationalCoverage.oc_sign_eq_zero N i hi
    have htable : activeTable (8*r) i z = 0 := by change w1ActiveSign (8*r) i*bit (z i) = 0; rw [hsign]; ring
    simp [hi,hf,htable]


end
end SAP.P004a.WH.W1
