import SAP.P011a.Defs.WholeW3
import SAP.P011a.WH.W3.Analytic
import SAP.P011a.WH.W3.Finite
import SAP.P011a.WH.W3.Signs
import SAP.P011a.Bridge
import AronowAudit.P011.P011_CorrectedAsymptoticCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W3

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/- There are no unresolved leaves. The finite donors, their row-wise estimates,
and the elementary probability glue below prove both whole statements outright. -/

/-- Assemble all of T4. The two weakened sufficient conditions use the actual
covariance as an admissible witness and the same nonnegative F1 centering. -/
theorem T4_assembly : T4WholeStatement := by
  refine ⟨?_, ?_, ?_, trace_support, (by intro n G; simp [oracleMatrix]), Bridge.CliqueCharacterization_proved,
    Bridge.DataDependentFailure_proved, sign_failure⟩
  · intro F c1 c2 c3 c4 h k M hM
    have hb := h.2.2.2.2.2.1 k
    exact AronowAudit.P011.quadratic_expectation (F.positive k) (Bridge.model (F.model k))
      (AronowAudit.P011.ProbabilityCompletion.weighted_memLp (Bridge.model (F.model k)) c1 hb) M hM
  · intro F c1 c2 c3 c4 K h M hM hK
    have hv := uniform_variance F c1 c2 c3 c4 K h M hM hK
    have he := expansion_from_variance F c1 c2 c3 c4 K h M hM hK hv
    refine ⟨hv, he, ?_⟩
    intro hPSD
    have hp (k : ℕ) : 0 ≤ quadratic (M k) (delta (F.model k)) ∧
        0 ≤ Matrix.trace ((M k - oracleMatrix (F.model k).G)*covariance (F.model k)) :=
      ⟨(hPSD k).1.2 _, AronowAudit.P011.DenseTraceCompletion.trace_psd_covariance
        (Bridge.model (F.model k))
        (AronowAudit.P011.ProbabilityCompletion.weighted_memLp (Bridge.model (F.model k)) c1
          (h.2.2.2.2.2.1 k)) _ (hPSD k).2⟩
    exact ⟨hp, conservative_of_expansion F M he hp⟩
  · intro F c1 c2 c3 c4 K h M hM hK hPSD
    have he := expansion_from_variance F c1 c2 c3 c4 K h M hM hK
      (uniform_variance F c1 c2 c3 c4 K h M hM hK)
    have hp (k : ℕ) : 0 ≤ quadratic (M k) (delta (F.model k)) := (hPSD k).2 _
    have hactual (k : ℕ) : AdmissibleCovariance (F.model k).G (covariance (F.model k)) :=
      ⟨F.model k, rfl, h.2.2.2.2.1 k,
        AronowAudit.P011.ProbabilityCompletion.weighted_memLp (Bridge.model (F.model k)) c1
          (h.2.2.2.2.2.1 k), rfl⟩
    constructor
    · intro htrace
      exact ⟨hp, conservative_of_expansion F M he (fun k => ⟨hp k, htrace k⟩)⟩
    · intro hall
      have htrace (k : ℕ) := hall k (covariance (F.model k)) (hactual k)
      exact ⟨(fun k => ⟨hp k, htrace k⟩),
        conservative_of_expansion F M he (fun k => ⟨hp k, htrace k⟩)⟩

/-- Assemble T5 from the full finite donors and T4. The Young comparison uses
I+D_true, not the possibly unbounded I+D'. Maximization and the minimum are
handled by pointwise domination and a union bound. -/
theorem T5_assembly : T5WholeStatement := by
  refine ⟨Bridge.CorrectedFinite_proved, Bridge.CorrectedMatrix_proved,
    Bridge.CorrectedOptimal_proved, corrected_finite_supplements, ?_⟩
  intro F c1 c2 c3 c4 h hv A hm
  have hc2 : 0 < c2 := h.2.1
  have hDeg : ∀ k i, (degree (F.model k).G i : ℝ) ≤ c2 := h.2.2.2.2.2.2.1
  let MC := fun k => correctedMatrix (F.model k).d (F.model k).G
  let MY := fun k => (1 : Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ) +
    Matrix.diagonal (fun i => (degree (F.model k).G i : ℝ))
  have hCP (k : ℕ) : PSD (MC k) ∧ PSD (MC k - oracleMatrix (F.model k).G) := by
    have hh := Bridge.CorrectedMatrix_proved (F.positive k)
      (F.model k).R (F.model k).G (F.model k).d (hv k) (fun _ => 0)
    exact ⟨hh.1, hh.2.1⟩
  have hYP (k : ℕ) : PSD (MY k) ∧ PSD (MY k - oracleMatrix (F.model k).G) :=
    AronowAudit.P011.CorrectedAsymptoticCompletion.young_true_psd _
  have hCN (k : ℕ) : operatorNorm (MC k) ≤ 1+2*c2 :=
    AronowAudit.P011.SchurSupport.operatorNorm_le_abs_row_sum _ (hCP k).1.1
      (1+2*c2) (by positivity)
      (AronowAudit.P011.CorrectedAsymptoticCompletion.corrected_row_bound
        _ _ _ (hv k) c2 (hDeg k))
  have hYN (k : ℕ) : operatorNorm (MY k) ≤ 1+c2 :=
    AronowAudit.P011.SchurSupport.operatorNorm_le_abs_row_sum _ (hYP k).1.1
      (1+c2) (by positivity)
      (AronowAudit.P011.CorrectedAsymptoticCompletion.young_row_bound _ c2 (hDeg k))
  have hExpansion : WholeDeterministicExpansion := T4_assembly.2.1
  have hC0 := ((hExpansion F c1 c2 c3 c4 (1+2*c2) h MC
    (fun k => (hCP k).1.1) hCN).2.2 hCP).2
  have hC : Conservative F
      (fun k y => V1plus (F.model k).d (F.model k).G (weighted (F.model k) y)) := by
    have he (k : ℕ) (y : Fin (F.size k) → ℝ) :
        V1plus (F.model k).d (F.model k).G (weighted (F.model k) y) =
          varianceForm (MC k) (weighted (F.model k) y) :=
      (Bridge.CorrectedMatrix_proved (F.positive k)
        (F.model k).R (F.model k).G (F.model k).d (hv k) _).2.2.1
    simpa only [he] using hC0
  have hY0 := ((hExpansion F c1 c2 c3 c4 (1+c2) h MY
    (fun k => (hYP k).1.1) hYN).2.2 hYP).2
  have hY : Conservative F (fun k y => VYoung (F.model k).d (weighted (F.model k) y)) :=
    AronowAudit.P011.CorollaryCompletion.conservative_mono (Bridge.family F) _ _ hY0
      (fun k y => AronowAudit.P011.CorrectedAsymptoticCompletion.young_true_le _ _ _ (hv k) _)
  have hdom (k : ℕ) (y : Fin (F.size k) → ℝ) :
      V1plus (F.model k).d (F.model k).G (weighted (F.model k) y) ≤
        V1plus (F.model k).d (A k y) (weighted (F.model k) y) := (hm k y).2 _ (hv k)
  have hSel := AronowAudit.P011.CorollaryCompletion.conservative_mono (Bridge.family F) _ _ hC hdom
  refine ⟨hCN, hdom, hC, hSel, hY,
    AronowAudit.P011.CorrectedAsymptoticCompletion.conservative_min (Bridge.family F) _ _ hSel hY, ?_⟩
  intro hd
  have he (k : ℕ) (y : Fin (F.size k) → ℝ) :
      VYoung (F.model k).d (weighted (F.model k) y) =
        V2prime (F.model k).d (weighted (F.model k) y) := by
    obtain ⟨D, hD⟩ := hd k
    exact AronowAudit.P011.CorrectedAsymptoticCompletion.young_eq_prime_of_constant
      (F.positive k) _ D hD _
  simpa only [he] using hY

end
end SAP.P011a.WH.W3
