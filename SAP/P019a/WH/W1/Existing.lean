import SAP.P019a.Defs.WholeW1
import SAP.P019a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1
open SAP.P019a SAP.P019a.Bridge Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
open Classical

theorem restrictedT3 : T3Statement := by
  obtain ⟨hs, het, hec, hct, hcc⟩ := AronowAudit.P019.lemma_two_counterexample
  obtain ⟨_, hcount, hmean, hcell⟩ := AronowAudit.P019.conditional_count_counterexample
  obtain ⟨_, hD, hAB, hcross, hv, hrhs, htwo, hzero⟩ :=
    AronowAudit.P019.Wave1.finite_product_counterexample_proof
  refine ⟨hs, ?_, hct, hcc,
    (AronowAudit.P019.regularity_probabilities _ hs.2.2.2).2 false,
    hcount, hmean, hcell, AronowAudit.P019.omitted_binomial_mass,
    hD, ?_, hAB, hcross, hv, hrhs, ?_,
    AronowAudit.P019.realized_count_counterexample.2.1, htwo, hzero⟩
  · intro n z
    have he : finiteSampleWitness.law.prob (fun ω => ¬ finiteSampleWitness.cell z false ω) = 5/8 := by
      cases z
      · exact hec
      · exact het
    have hc := AronowAudit.P019.probability_complement
      (toLaw finiteSampleWitness.law) (finiteSampleWitness.cell z false)
    have hb : 1-finiteSampleWitness.law.prob (finiteSampleWitness.cell z false) = 5/8 :=
      hc.symm.trans he
    have heq : (finiteSampleWitness.law.iid n).prob
        (fun s => finiteSampleWitness.cellCount s z false = 0) = (5/8)^n := by
      rw [← hb]
      exact AronowAudit.P019.empty_cell_probability (toStudy finiteSampleWitness) n z false
    exact ⟨heq, by rw [heq]; positivity⟩
  · have hD' : (finiteSampleWitness.law.iid 4).prob finiteSampleWitness.occupied = 1431/2048 := hD
    rw [hD']; norm_num
  · calc
      _ = (141205/404496 : ℝ) - 75809/202248 := congrArg₂ (fun a b : ℝ => a-b) hv hrhs
      _ = -1157/44944 := by norm_num

theorem restrictedT4.{u} : T4Statement.{u} := by
  intro Ω _ S hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n z
    have hthree := AronowAudit.P019.Wave1.corrected_cell_lemmas_proof
      (toStudy S) hs 3 (by norm_num) 0 0
    have hc : (1-S.law.prob (S.cell z false))^3 =
        (S.law.iid 3).prob (fun s => S.cellCount s z false = 0) := (hthree.2.1 z).1.symm
    have hcube : 0 < (1-S.law.prob (S.cell z false))^3 := by
      rw [hc]; exact (hthree.2.1 z).2
    have hb := (Odd.pow_pos_iff (by decide : Odd 3)).mp hcube
    have heq : (S.law.iid n).prob (fun s => S.cellCount s z false = 0) =
        (1-S.law.prob (S.cell z false))^n :=
      AronowAudit.P019.empty_cell_probability (toStudy S) n z false
    exact ⟨heq, by rw [heq]; exact pow_pos hb n⟩
  · intro n hn c1 c0
    obtain ⟨hD, _, hbin, hpattern, hcov, hcross⟩ :=
      AronowAudit.P019.Wave1.corrected_cell_lemmas_proof (toStudy S) hs n hn c1 c0
    obtain ⟨hA, hB, hK⟩ :=
      AronowAudit.P019.Wave1.corrected_conditional_means_proof (toStudy S) hs n hn c1 c0
    obtain ⟨hmu, hprod, hdiff⟩ :=
      AronowAudit.P019.Wave1.corrected_product_variance_proof (toStudy S) hs n hn c1 c0
    refine ⟨hD, ?_, ?_, hA, hcov, hcross, hmu, hprod, ?_, hdiff⟩
    · intro k hk hpos
      exact ⟨hbin k hk hpos, (hK k hk hpos).1, (hK k hk hpos).2⟩
    · intro s hd hf
      exact ⟨(hpattern s hd hf).1, (hpattern s hd hf).2,
        (hB s hd hf).1, (hB s hd hf).2⟩
    · have hmissing := hdiff
      let P := S.law.iid n
      let A := @Study.sampleA Ω _ S n
      let B := fun s : Fin n → Ω => S.sampleB s c1 c0
      let h := @Study.sampleH Ω _ S n
      let b := S.listMean true false - S.listMean false false - 1
      change P.cv (fun s => A s * B s) S.occupied =
        b^2 * P.cv A S.occupied + P.ce (fun s => A s^2 * h s) S.occupied at hprod
      change P.cv (fun s => A s * B s) S.occupied -
        ((P.ce A S.occupied)^2 * P.cv B S.occupied +
          P.cv A S.occupied * (P.ce B S.occupied)^2 + P.cv A S.occupied * P.cv B S.occupied) =
        P.ccov (fun s => A s^2) h S.occupied at hmissing
      unfold FiniteLaw.ccov at hmissing
      linarith only [hprod, hmissing]
  · have h := AronowAudit.P019.Wave1.corrected_covariance_order_proof (toStudy S) hs
    exact ⟨h.1.comp_tendsto (tendsto_add_atTop_nat 2),
      h.2.comp (tendsto_add_atTop_nat 2)⟩
  · intro n hn
    exact AronowAudit.P019.treatment_count_correction (toStudy S) n hn

theorem restrictedT5 : T5Statement := by
  exact AronowAudit.P019.distribution_sign_counterexample

theorem restrictedT7 : T7Statement := by
  obtain ⟨h1, h2, h4, hδ, hβ, h3⟩ := AronowAudit.P019.diagnosis_counterexample
  refine ⟨h1, h2, h4, hδ, hβ, ?_, h3⟩
  have h : diagnosisWitness.beta = 2 := hβ
  rw [h]; norm_num

theorem restrictedT9 : T9Statement := by
  obtain ⟨hs, hassign, hpsi, hmean, hmatrix⟩ :=
    AronowAudit.P019.Wave1.fisher_sequential_finite_proof
  obtain ⟨_, hnormal, hfisher, hi, hi2, hv, hne⟩ :=
    AronowAudit.P019.Wave1.fisher_reference_counterexample_proof
  refine ⟨hs, hassign, hpsi, hmean, hmatrix, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [studentized_eq, weakLimit_eq, uniformFin_eq, correlatedNormals_eq,
      sequential_betaHat_eq, sequential_betaVarianceHat_eq] using hnormal
  · simpa only [normalPValue_eq, sequentialFisherLimit_eq, weakLimit_eq, uniformFin_eq,
      sequential_betaHat_eq, sequential_betaVarianceHat_eq, fisherStatistic_eq] using hfisher
  · simpa only [sequentialFisherLimit_eq] using hi
  · simpa only [sequentialFisherLimit_eq] using hi2
  · simpa only [sequentialFisherLimit_eq, continuousVariance_eq] using hv
  · simpa only [sequentialFisherLimit_eq, chiSquareTen_eq] using hne

end
end SAP.P019a.WH.W1
