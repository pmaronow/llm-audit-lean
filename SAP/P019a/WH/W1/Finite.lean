import SAP.P019a.WH.W1.Existing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1
open SAP.P019a SAP.P019a.Bridge Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
open Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

 theorem fairFour : wholeFairBits (uniformFin 16 (by norm_num)) 4
    (fun i ω => fairBit ω i.val) := by
  intro a
  cases h0 : a 0 <;> cases h1 : a 1 <;> cases h2 : a 2 <;> cases h3 : a 3 <;>
    norm_num [FiniteLaw.prob, FiniteLaw.mean, uniformFin, fairBit,
      Fin.sum_univ_succ, Fin.forall_fin_succ, h0, h1, h2, h3]

 theorem fairThree : wholeFairBits (uniformFin 8 (by norm_num)) 3
    (fun i ω => fairBit ω i.val) := by
  intro a
  cases h0 : a 0 <;> cases h1 : a 1 <;> cases h2 : a 2 <;>
    norm_num [FiniteLaw.prob, FiniteLaw.mean, uniformFin, fairBit,
      Fin.sum_univ_succ, Fin.forall_fin_succ, h0, h1, h2]

 theorem t3_population : wholeT3Population := by
  refine ⟨fairFour, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z y; cases z <;> cases y <;>
      norm_num [finiteSampleWitness, wholeCellTable, Study.cell, Study.listMean,
        FiniteLaw.prob, FiniteLaw.ce, FiniteLaw.cv, FiniteLaw.mean,
        uniformFin, fairBit, Fin.sum_univ_succ]
  all_goals try { norm_num [finiteSampleWitness, Study.mu, Study.truthRate, Study.gamma,
    FiniteLaw.prob, FiniteLaw.ce, FiniteLaw.variance, FiniteLaw.mean,
    bitVal, uniformFin, fairBit, Fin.sum_univ_succ] }
  intro y z v
  cases y <;> cases z <;> rcases v with _ | (_ | (_ | v)) <;>
    norm_num [wholeT3Mass, finiteSampleWitness, Study.cell, FiniteLaw.prob,
      FiniteLaw.mean, uniformFin, fairBit, Fin.sum_univ_succ]

 theorem t3_singleton : wholeT3Singleton := by
  let S := finiteSampleWitness
  have hA (s : Fin 1 → Fin 16) : S.sampleA s = 1-bitVal (S.Y (s 0)) := by
    simp [Study.sampleA, Study.ybar]
  have hM (s : Fin 1 → Fin 16) (z : Bool) : S.cellMean s z false 0 =
      singletonMean S z false (s 0) := by
    unfold Study.cellMean Study.cellCount singletonMean
    simp only [Fin.sum_univ_one]
    by_cases hc : S.cell z false (s 0) <;> simp [hc]
  have he (f : Fin 16 → ℝ) : (S.law.iid 1).mean (fun s => f (s 0)) = S.law.mean f :=
    AronowAudit.P019.iid_mean_coordinate (toLaw S.law) 1 0 f
  have havg (g : (Fin 1 → Fin 16) → ℝ) (f : Fin 16 → ℝ)
      (hg : ∀ s, g s = f (s 0)) : (S.law.iid 1).mean g = S.law.mean f := by
    calc
      _ = (S.law.iid 1).mean (fun s => f (s 0)) := congrArg _ (funext hg)
      _ = _ := he f
  refine ⟨(havg _ (fun ω => 1-bitVal (S.Y ω)) hA).trans ?_,
    (havg _ (singletonMean S true false) (fun s => hM s true)).trans ?_,
    (havg _ (fun ω => (1-bitVal (S.Y ω))*singletonMean S true false ω)
      (fun s => congrArg₂ (fun x y : ℝ => x*y) (hA s) (hM s true))).trans ?_,
    (havg _ (singletonMean S false false) (fun s => hM s false)).trans ?_,
    (havg _ (fun ω => (1-bitVal (S.Y ω))*singletonMean S false false ω)
      (fun s => congrArg₂ (fun x y : ℝ => x*y) (hA s) (hM s false))).trans ?_⟩
  all_goals norm_num [S, finiteSampleWitness, singletonMean, Study.cell, FiniteLaw.mean,
    uniformFin, fairBit, bitVal, Fin.sum_univ_succ]

 theorem t5_data : wholeT5Data := by
  refine ⟨fairThree, (by intro ω; rfl), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z y; cases z <;> cases y <;>
      norm_num [distributionWitness, wholeCellTable, Study.cell, Study.listMean,
        FiniteLaw.prob, FiniteLaw.ce, FiniteLaw.cv, FiniteLaw.mean,
        uniformFin, fairBit, Fin.sum_univ_succ]
  all_goals try { norm_num [distributionWitness, Study.mu, Study.truthRate, Study.beta,
    Study.listMean, Study.cell, FiniteLaw.prob, FiniteLaw.ce, FiniteLaw.variance,
    FiniteLaw.mean, bitVal, uniformFin, fairBit, Fin.sum_univ_succ] }
  intro t
  norm_num [distributionWitness, Study.cell, FiniteLaw.prob, FiniteLaw.ce,
    FiniteLaw.mean, uniformFin, fairBit, Fin.sum_univ_succ]
  simp only [show (0 : ℝ) = t ↔ t = 0 from eq_comm,
    show (1 : ℝ) = t ↔ t = 1 from eq_comm,
    show (2 : ℝ) = t ↔ t = 2 from eq_comm,
    show (3 : ℝ) = t ↔ t = 3 from eq_comm]
  split_ifs <;> norm_num

 theorem t5_cdf (t : ℝ) :
    distributionWitness.law.ce (fun ω => if (distributionWitness.V ω : ℝ) ≤ t then 1 else 0)
      (distributionWitness.cell false true) =
    distributionWitness.law.ce (fun ω => if (distributionWitness.V ω : ℝ)-1 ≤ t then 1 else 0)
      (distributionWitness.cell true true) := by
  norm_num [distributionWitness, Study.cell, FiniteLaw.prob, FiniteLaw.ce,
    FiniteLaw.mean, uniformFin, fairBit, Fin.sum_univ_succ]
  split_ifs <;> (try rfl) <;> linarith

 theorem t7_sixteen : wholeT7Sixteen := by
  refine ⟨fairFour, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω; fin_cases ω <;> norm_num [diagnosisWitness, wholeDiagnosisPotential, fairBit]
  all_goals try { norm_num [diagnosisWitness, Study.cell, FiniteLaw.prob,
    FiniteLaw.variance, FiniteLaw.mean, bitVal, uniformFin, fairBit, Fin.sum_univ_succ] }
  · intro z y; cases z <;> cases y <;>
      norm_num [wholeCellTable, diagnosisWitness, Study.cell, Study.listMean,
        FiniteLaw.prob, FiniteLaw.ce, FiniteLaw.cv, FiniteLaw.mean,
        uniformFin, fairBit, Fin.sum_univ_succ]
  · rintro ⟨b,c,x⟩ z
    cases b <;> cases c <;> cases x <;> cases z <;>
      norm_num [diagnosisWitness, wholeIndependent, FiniteLaw.prob, FiniteLaw.mean,
        uniformFin, fairBit, Fin.sum_univ_succ]
  · rintro ⟨w,x⟩ z
    cases x <;> cases z <;> rcases w with _ | (_ | (_ | w)) <;>
      norm_num [diagnosisWitness, wholeIndependent, FiniteLaw.prob, FiniteLaw.mean,
        uniformFin, fairBit, Fin.sum_univ_succ]
  · rintro ⟨a,b⟩ z
    cases a <;> cases b <;> cases z <;>
      norm_num [diagnosisWitness, wholeDiagnosisPotential, wholeIndependent,
        FiniteLaw.prob, FiniteLaw.mean, uniformFin, fairBit, Fin.sum_univ_succ]
  · intro y z
    cases y <;> cases z <;>
      norm_num [diagnosisWitness, wholeIndependent, FiniteLaw.prob, FiniteLaw.mean,
        uniformFin, fairBit, Fin.sum_univ_succ]

 theorem t7_eight : wholeT7Eight := by
  have hcells : wholeCellTable wholeDiagnosisEight (fun _ _ => 1/4)
      (fun z y => if z then (if y then 5/2 else 3/2) else (if y then 1/2 else 3/2))
      (fun _ _ => 1/4) := by
    intro z y; cases z <;> cases y <;>
      norm_num [wholeDiagnosisEight, wholeCellTable, Study.cell, Study.listMean,
        FiniteLaw.prob, FiniteLaw.ce, FiniteLaw.cv, FiniteLaw.mean,
        uniformFin, fairBit, Fin.sum_univ_succ]
  have hvz : wholeDiagnosisEight.law.variance (fun ω => bitVal (wholeDiagnosisEight.Z ω)) = 1/4 := by
    norm_num [wholeDiagnosisEight, FiniteLaw.variance, FiniteLaw.mean,
      uniformFin, fairBit, bitVal, Fin.sum_univ_succ]
  have hvy : wholeDiagnosisEight.law.variance (fun ω => bitVal (wholeDiagnosisEight.Y ω)) = 1/4 := by
    norm_num [wholeDiagnosisEight, FiniteLaw.variance, FiniteLaw.mean,
      uniformFin, fairBit, bitVal, Fin.sum_univ_succ]
  refine ⟨fairThree, ?_, ?_, ?_, ?_, hcells, hvy, hvz, ?_, ?_, ?_⟩
  · intro ω _ _; rfl
  · intro ω _; fin_cases ω <;> norm_num [wholeDiagnosisEight, fairBit, bitVal]
  · refine ⟨?_, ?_, ?_⟩
    · intro z y; obtain ⟨hp, _, _, hv⟩ := hcells z y
      exact ⟨hp, by rw [hv]; norm_num⟩
    · rw [hvz]; norm_num
    · rw [hvy]; norm_num
  · intro ω; fin_cases ω <;> norm_num [wholeDiagnosisEight, fairBit]
  · norm_num [wholeDiagnosisEight, Study.delta, FiniteLaw.ce, FiniteLaw.prob,
      FiniteLaw.mean, uniformFin, fairBit, bitVal, Fin.sum_univ_succ]
  · norm_num [wholeDiagnosisEight, Study.beta, Study.listMean, Study.cell, FiniteLaw.ce,
      FiniteLaw.prob, FiniteLaw.mean, uniformFin, fairBit, Fin.sum_univ_succ]
  · intro hi
    have h := hi (fun w x y => if w = 0 ∧ x = true ∧ y = false then 1 else 0) false
    norm_num [wholeDiagnosisEight, FiniteLaw.prob, FiniteLaw.mean,
      uniformFin, fairBit, Fin.sum_univ_succ] at h

end
end SAP.P019a.WH.W1
