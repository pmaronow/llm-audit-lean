import SAP.P004a.WH.W1.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section
set_option maxHeartbeats 1000000

/-- All spatial and overlap guards in T1 are certificates of the fixed witness. -/
theorem three_spatial : T1SpatialStatement := by
  refine ⟨AronowAudit.P004.Wave1.TailBIpw_spatial,
    AronowAudit.P004.Wave1.DecideP004T1_interior, Real.log_pos (by norm_num),
    ?_, ?_, AronowAudit.P004.Wave1.DecideP004T1_bound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hl := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  · intro N x z
    have h : |(threeTypePopulation N).outcome x z| ≤ (21/20 : ℝ) :=
      AronowAudit.P004.Wave1.LinePopulation.n5_proof (threeTypeTable N) (21/20) (by norm_num)
        (fun i _ => by unfold threeTypeTable; split_ifs <;> norm_num) x z
    linarith
  · intro N i
    change 1/10 < propensities (threeTypeONat N) threeTypeTheta i ∧
      propensities (threeTypeONat N) threeTypeTheta i < 1-1/10
    rw [show propensities (threeTypeONat N) threeTypeTheta =
      fun i => AronowAudit.P004.Wave1.DecideP004T1_p (i.val%3) from
      AronowAudit.P004.Wave1.DecideP004T1_propensities N]
    dsimp only
    unfold AronowAudit.P004.Wave1.DecideP004T1_p
    split_ifs <;> norm_num
  · intro N d hd
    exact AronowAudit.P004.Wave1.LinePopulation.n4_proof (threeTypeTable N) d hd
  · intro N
    exact AronowAudit.P004.Wave1.LinePopulation.n3_proof (threeTypeTable N)
  · intro N d _hd i j hij hshare
    have hc (a : Fin N) (z z' : Assignment N) :
        circleAverage (threeTypePopulation N) d a z = circleAverage (threeTypePopulation N) d a z' := rfl
    have hs (a l : Fin N) (h : interferes (circleAverage (threeTypePopulation N) d) a l) : a = l := by
      rcases h with h | ⟨z,z',_,hne⟩
      · exact h
      · exact (hne (hc a z z')).elim
    obtain ⟨l,hil,hjl⟩ := hshare
    have he := (hs i l hil).trans (hs j l hjl).symm
    subst j
    have heq : nodeSeparation (threeTypePopulation N) i i = 0 := by
      change AronowAudit.P004.nodeSeparation (AronowAudit.P004.linePopulation (threeTypeTable N)) i i = 0
      rw [AronowAudit.P004.Wave1.LinePopulation.n1_proof]
      simp
    simp [heq] at hij
  · intro N i
    exact AronowAudit.P004.Wave1.LinePopulation.line_zero_ball (threeTypeTable N) i
  · intro N i r hr
    exact AronowAudit.P004.Wave1.LinePopulation.n6_proof (threeTypeTable N) i r hr

/-- Pointwise coefficient algebra and the independent-sum variance donor prove W3-W4. -/
theorem three_linear : T1LinearStatement := by
  intro K hK
  dsimp only
  let N := 3*K
  have hn : (N : ℝ) ≠ 0 := by dsimp [N]; positivity
  have hc : circleAverage (threeTypePopulation N) 0 = threeTypeTable N :=
    AronowAudit.P004.Wave1.LinePopulation.n3_proof _
  have hp : w1ThreeP N = fun i => AronowAudit.P004.Wave1.DecideP004T1_p (i.val%3) :=
    AronowAudit.P004.Wave1.DecideP004T1_propensities _
  have hprob : ∀ i, 0 < w1ThreeP N i ∧ w1ThreeP N i < 1 := by
    intro i
    rw [hp]
    exact AronowAudit.P004.Wave1.DecideP004T1_prob _
  have hb (z : Assignment N) : w1ThreePrinted N z = w1ThreeLinear w1ThreeB N z := by
    unfold w1ThreePrinted
    rw [hc]
    have hAug : augmented (w1ThreeP N) (threeTypeTable N)
        (printedFits (w1ThreeP N) (threeTypeTable N) (threeTypeONat N)) z =
        (∑ i, AronowAudit.P004.Wave1.DecideP004T1_residual
          (beta (w1ThreeP N) (threeTypeTable N) (threeTypeONat N) true)
          (i.val%3)*(bit (z i)-AronowAudit.P004.Wave1.DecideP004T1_p (i.val%3)))/N :=
      AronowAudit.P004.Wave1.DecideP004T1_augmented N z
    have hbval : beta (w1ThreeP N) (threeTypeTable N) (threeTypeONat N) true = ![509/500,0] :=
      AronowAudit.P004.Wave1.DecideP004T1_beta K hK true
    rw [hAug,hbval]
    unfold w1ThreeLinear
    rw [hp]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have ht : i.val%3 < 3 := Nat.mod_lt _ (by omega)
    interval_cases h : i.val%3 <;>
      norm_num [AronowAudit.P004.Wave1.DecideP004T1_residual,
        AronowAudit.P004.Wave1.DecideP004T1_q,AronowAudit.P004.Wave1.DecideP004T1_o,
        AronowAudit.P004.Wave1.DecideP004T1_p,AronowAudit.P004.dot,
        w1ThreeB,Fin.sum_univ_two,h]
  have ha (z : Assignment N) : ht (w1ThreeP N) (circleAverage (threeTypePopulation N) 0) z -
      (∑ i, (bit (z i)-w1ThreeP N i)*dot (threeTypeONat N i)
        (scoreGamma (w1ThreeP N) (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)))/N =
        w1ThreeLinear w1ThreeA N z := by
    rw [hc]
    have hg : scoreGamma (w1ThreeP N) (threeTypeTable N) (threeTypeONat N) = ![549/125,0] :=
      AronowAudit.P004.Wave1.DecideP004T1_gamma K hK
    rw [hg]
    unfold ht w1ThreeLinear
    rw [←sub_div, ←Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hp]
    have ht : i.val%3 < 3 := Nat.mod_lt _ (by omega)
    interval_cases h : i.val%3 <;> cases hz : z i <;>
      norm_num [threeTypeTable,threeTypeONat,dot,Fin.sum_univ_two,
        AronowAudit.P004.Wave1.DecideP004T1_p,w1ThreeA,bit,h,hz]
  have hv (c : ℕ → ℝ) : (N : ℝ)*variance (w1ThreeP N) (w1ThreeLinear c N) =
      (AronowAudit.P004.Wave1.DecideP004T1_p 0*(1-AronowAudit.P004.Wave1.DecideP004T1_p 0)*(c 0)^2+
       AronowAudit.P004.Wave1.DecideP004T1_p 1*(1-AronowAudit.P004.Wave1.DecideP004T1_p 1)*(c 1)^2+
       AronowAudit.P004.Wave1.DecideP004T1_p 2*(1-AronowAudit.P004.Wave1.DecideP004T1_p 2)*(c 2)^2)/3 := by
    have hvar : variance (w1ThreeP N) (w1ThreeLinear c N) =
        (∑ i, w1ThreeP N i*(1-w1ThreeP N i)*(c (i.val%3))^2)/(N : ℝ)^2 :=
      AronowAudit.P004.Wave1.DecideP004T1_sum_variance (w1ThreeP N) hprob (fun i => c (i.val%3)) N
    rw [hvar]
    rw [show (N : ℝ)*((∑ i, w1ThreeP N i*(1-w1ThreeP N i)*(c (i.val%3))^2)/(N : ℝ)^2) =
      (∑ i, w1ThreeP N i*(1-w1ThreeP N i)*(c (i.val%3))^2)/(N : ℝ) by field_simp]
    rw [hp]
    exact AronowAudit.P004.Wave1.DecideP004T1_cycle_average K hK
      (fun t => AronowAudit.P004.Wave1.DecideP004T1_p t*(1-AronowAudit.P004.Wave1.DecideP004T1_p t)*(c t)^2)
  have hdiff : (fun z => w1ThreeLinear w1ThreeA N z-w1ThreePrinted N z) = w1ThreeLinear w1ThreeD N := by
    funext z
    rw [hb]
    unfold w1ThreeLinear
    rw [←sub_div, ←Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w1ThreeD]
    ring
  refine ⟨hb,ha,?_,?_,?_⟩
  · change (N : ℝ)*variance (w1ThreeP N) (w1ThreeLinear w1ThreeA N) = _
    rw [hv]
    norm_num [w1ThreeA,AronowAudit.P004.Wave1.DecideP004T1_p]
  · have he : w1ThreePrinted N = w1ThreeLinear w1ThreeB N := funext hb
    rw [he]
    change (N : ℝ)*variance (w1ThreeP N) (w1ThreeLinear w1ThreeB N) = _
    rw [hv]
    norm_num [w1ThreeB,AronowAudit.P004.Wave1.DecideP004T1_p]
  · rw [hdiff]
    change (N : ℝ)*variance (w1ThreeP N) (w1ThreeLinear w1ThreeD N) = _
    rw [hv]
    norm_num [w1ThreeD,w1ThreeA,w1ThreeB,AronowAudit.P004.Wave1.DecideP004T1_p]

private theorem three_assignments : (Finset.univ : Finset (Assignment 3)) =
    {![false,false,false],![false,false,true],![false,true,false],![false,true,true],
     ![true,false,false],![true,false,true],![true,true,false],![true,true,true]} := by
  ext z
  simp only [Finset.mem_univ, true_iff]
  have he : z = ![z 0,z 1,z 2] := by funext i; fin_cases i <;> rfl
  rw [he]
  cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;> simp

/-- Exact one-block moments, checked by enumerating the eight Boolean vectors. -/
theorem three_block_moments : expect (w1ThreeP 3) w1OneBlock = 0 ∧
    expect (w1ThreeP 3) (fun z => (w1OneBlock z)^2) = 3*(10369/750000) ∧
    expect (w1ThreeP 3) (fun z => (w1OneBlock z)^4) = 915255049/250000000000 := by
  have hp : w1ThreeP 3 = ![1/3,1/2,2/3] := by
    have h : w1ThreeP 3 = fun i => AronowAudit.P004.Wave1.DecideP004T1_p (i.val%3) :=
      AronowAudit.P004.Wave1.DecideP004T1_propensities 3
    rw [h]
    funext i
    fin_cases i <;> norm_num [AronowAudit.P004.Wave1.DecideP004T1_p]
  unfold expect
  rw [three_assignments]
  norm_num [designWeight,coin,w1OneBlock,w1ThreeD,w1ThreeA,w1ThreeB,hp,bit,Fin.sum_univ_three,Fin.prod_univ_succ]


end
end SAP.P004a.WH.W1
