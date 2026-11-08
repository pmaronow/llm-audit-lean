import AronowAudit.P026.P026_LogitGeometry
import SAP.P018a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P018a.WH.W1.P.T13_L1

open Finset
open scoped BigOperators

lemma predictor_affine (β γ : Vec 2) (a b : ℝ) (d : Fin 6) :
    dot (logitX d) (a • β + b • γ) =
      a * dot (logitX d) β + b * dot (logitX d) γ := by
  simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Fin.sum_univ_succ]
  ring

lemma predictor_separates (β γ : Vec 2) (hβγ : β ≠ γ) :
    ∃ d : Fin 6, dot (logitX d) β ≠ dot (logitX d) γ := by
  by_contra hn
  push Not at hn
  have h0 := hn 0
  have h1 := hn 1
  norm_num [logitX, dot, Fin.sum_univ_succ] at h0 h1
  have hβ0 : β 0 = γ 0 := h0
  have hβ1 : β 1 = γ 1 := by nlinarith
  apply hβγ
  funext i
  fin_cases i
  · exact hβ0
  · exact hβ1

end SAP.P018a.WH.W1.P.T13_L1

open SAP.P018a
open Finset
open scoped BigOperators

theorem SAP.P018a.WH.W1.T13_L1_proof : SAP.P018a.WH.W1.T13_L1 := by
  refine ⟨convex_univ, ?_⟩
  intro β _ γ _ hβγ a b ha hb hab
  obtain ⟨i, hne⟩ := SAP.P018a.WH.W1.P.T13_L1.predictor_separates β γ hβγ
  have hweak : ∀ d : Fin 6,
      a * logLikelihood (logitX d) (logitY d) β +
        b * logLikelihood (logitX d) (logitY d) γ ≤
      logLikelihood (logitX d) (logitY d) (a • β + b • γ) := by
    intro d
    rw [logLikelihood, logLikelihood, logLikelihood]
    rw [SAP.P018a.WH.W1.P.T13_L1.predictor_affine]
    exact (AronowAudit.P026.LogitCompletion.bernoulliTerm_strictConcave
      (logitY d)).concaveOn.2 (Set.mem_univ _) (Set.mem_univ _) ha.le hb.le hab
  have hstrict :
      a * logLikelihood (logitX i) (logitY i) β +
        b * logLikelihood (logitX i) (logitY i) γ <
      logLikelihood (logitX i) (logitY i) (a • β + b • γ) := by
    rw [logLikelihood, logLikelihood, logLikelihood]
    rw [SAP.P018a.WH.W1.P.T13_L1.predictor_affine]
    exact (AronowAudit.P026.LogitCompletion.bernoulliTerm_strictConcave
      (logitY i)).2 (Set.mem_univ _) (Set.mem_univ _) hne ha hb hab
  have hs := Finset.sum_lt_sum (fun d _ => hweak d)
    ⟨i, Finset.mem_univ _, hstrict⟩
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, smul_eq_mul] using hs

