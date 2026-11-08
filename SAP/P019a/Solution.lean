import SAP.P019a.Defs
import SAP.P019a.Bridge
import SAP.P019a.WH.W1.Proofs.T3
import SAP.P019a.WH.W1.Proofs.T4
import SAP.P019a.WH.W1.Proofs.T5
import SAP.P019a.WH.W1.Proofs.T7
import SAP.P019a.WH.W1.Proofs.T9
import SAP.P019a.WH.W2.Proofs.T11

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P019a SAP.P019a.Bridge Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
open Classical

theorem SAP.P019a.T1 : T1Statement := by
  have hp : ceilingBeta printedAffected (1/5) = 3109/3125 :=
    AronowAudit.P019.ceiling_counterexample.2.2.2.2.1
  have hc : ceilingBeta codedAffected (1/5) = 3734/3125 :=
    AronowAudit.P019.ceiling_counterexample.2.2.2.2.2.1
  refine ⟨AronowAudit.P019.binomial_baseline_exact.1,
    AronowAudit.P019.binomial_baseline_exact.2.1,
    AronowAudit.P019.binomial_baseline_exact.2.2, ?_, hp, hc, ?_, ?_,
    AronowAudit.P019.ceiling_counterexample.2.2.2.2.2.2⟩
  · intro w; fin_cases w <;> norm_num [printedAffected, codedAffected, unaffected]
  · rw [hp]; norm_num
  · rw [hc]; norm_num

theorem SAP.P019a.T2 : T2Statement := by
  intro ρ hρ0 hρ1
  obtain ⟨hresponse, hc, hp, hgap, hstrict⟩ := AronowAudit.P019.ceiling_corrected ρ hρ0 hρ1
  have hc' : ceilingBeta codedAffected ρ = 1+(609/625)*ρ := hc
  have hp' : ceilingBeta printedAffected ρ = 1-(16/625)*ρ := hp
  refine ⟨hresponse, AronowAudit.P019.ceiling_response_increments, ?_, hc, ?_, hp,
    hgap, hstrict, ?_, ?_⟩
  · rw [hc']; norm_num [ceilingBaseline]; ring
  · rw [hp']; norm_num [ceilingBaseline]; ring
  · have h : ceilingBeta codedAffected (1/5) = 1+(609/625)*(1/5) :=
      (AronowAudit.P019.ceiling_corrected (1/5) (by norm_num) (by norm_num)).2.1
    norm_num at h
    exact h
  · have h : ceilingBeta printedAffected (1/5) = 1-(16/625)*(1/5) :=
      (AronowAudit.P019.ceiling_corrected (1/5) (by norm_num) (by norm_num)).2.2.1
    norm_num at h
    exact h

theorem SAP.P019a.T3 : SAP.P019a.T3WholeStatement := SAP.P019a.WH.W1.T3_whole

theorem SAP.P019a.T4.{u} : SAP.P019a.T4WholeStatement.{u} := SAP.P019a.WH.W1.T4_whole

theorem SAP.P019a.T5 : SAP.P019a.T5WholeStatement := SAP.P019a.WH.W1.T5_whole

theorem SAP.P019a.T6.{u} : T6Statement.{u} := by
  intro Ω _ S h1 h2 h3 h0 ht
  have hp := AronowAudit.P019.cell_probability (toStudy S) h3 true true
  have hprod : S.law.prob (fun ω => S.Z ω = true) * S.law.prob (fun ω => S.Y ω = true) ≠ 0 :=
    hp.symm ▸ (ne_of_gt ht)
  refine ⟨(mul_ne_zero_iff.mp hprod).2, ?_⟩
  intro t
  have h := AronowAudit.P019.placebo_distribution_corrected
    (toStudy S) h1 h2 h3 (ne_of_gt h0) (ne_of_gt ht) t
  have heq := h.1.trans h.2.symm
  refine ⟨h.1, h.2, heq, ?_⟩
  have heq' : S.law.ce (fun ω => if (S.V ω : ℝ) = t then 1 else 0) (S.cell false true) =
      S.law.ce (fun ω => if (S.V ω : ℝ) - 1 = t then 1 else 0) (S.cell true true) := heq
  simpa only [sub_eq_iff_eq_add] using heq'

theorem SAP.P019a.T7 : SAP.P019a.T7WholeStatement := SAP.P019a.WH.W1.T7_whole

theorem SAP.P019a.T8.{u} : T8Statement.{u} := by
  intro Ω _ S h0 ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2
    exact AronowAudit.P019.beta_baseline_decomposition (toStudy S) h1 h2 h0.ne' ht.ne'
  · intro h1 h2 h3
    have hb : S.beta = 1 :=
      AronowAudit.P019.placebo_one_identity (toStudy S) h1 h2 h3 h0.ne' ht.ne'
    have hd : S.beta = 1 + S.law.ce (fun ω => (S.W ω : ℝ)) (S.cell true true) -
        S.law.ce (fun ω => (S.W ω : ℝ)) (S.cell false true) :=
      AronowAudit.P019.beta_baseline_decomposition (toStudy S) h1 h2 h0.ne' ht.ne'
    exact ⟨by linarith, hb⟩
  · intro hb
    exact AronowAudit.P019.beta_departure_diagnosis (toStudy S) h0.ne' ht.ne' hb
  · intro h1 h2 hb h3
    exact hb (AronowAudit.P019.placebo_one_identity (toStudy S) h1 h2 h3 h0.ne' ht.ne')

theorem SAP.P019a.T9 : SAP.P019a.T9WholeStatement := SAP.P019a.WH.W1.T9_whole

theorem SAP.P019a.T10.{u} : T10Statement.{u} := by
  intro Ω _ P S hsame hs hj
  have hsame' : ∀ j, (toStudy (S j)).law = toLaw P := fun j => congrArg toLaw (hsame j)
  obtain ⟨hb, hcond, hcross, hz, hp, hf⟩ := AronowAudit.P019.Wave1.fisher_corrected_proof
    (toLaw P) (fun j => toStudy (S j)) hsame' hs hj
  refine ⟨hb, ?_, hcross, ?_, ?_, ?_⟩
  · intro j k hjk ω hω
    exact hcond j k hjk ω hω
  · simpa only [studentized_eq, weakLimit_eq, betaHat_eq, betaVarianceHat_eq] using hz
  · simpa only [normalPValue_eq, weakLimit_eq, betaHat_eq, betaVarianceHat_eq] using hp
  · simpa only [normalPValue_eq, weakLimit_eq, betaHat_eq, betaVarianceHat_eq,
      fisherStatistic_eq, chiSquareTen_eq] using hf

theorem SAP.P019a.T11.{u} : SAP.P019a.T11WholeStatement.{u} := SAP.P019a.WH.W2.T11_whole
