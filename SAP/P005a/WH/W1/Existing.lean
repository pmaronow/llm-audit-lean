import SAP.P005a.Defs.WholeW1
import SAP.P005a.Bridge
import AronowAudit.P005.Wave1.Lib.QuadraticSamplingTailC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W1
noncomputable section
open SAP.P005a SAP.P005a.Bridge Finset Filter
open scoped BigOperators Matrix Topology
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

theorem variance_congr {n : ℕ} (m : ℕ) (f g : Finset (Fin n) → ℝ)
    (h : ∀ S ∈ design n m, f S = g S) : variance m f = variance m g :=
  AronowAudit.P005.Wave1.CondP002P005P006_variance_congr m f g h

theorem variance_control {n m : ℕ} (hm : m ≤ n) (f : Finset (Fin n) → ℝ) :
    variance m (fun S => f (control S)) = variance (n-m) f :=
  AronowAudit.P005.Wave1.CondP002P005P006_variance_control hm f

theorem variance_div {n : ℕ} (m : ℕ) (f : Finset (Fin n) → ℝ) (c : ℝ) :
    variance m (fun S => f S/c) = variance m f/c^2 :=
  AronowAudit.P005.Wave1.t4_variance_div m f c

theorem t14_existing : T14Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n d P m S v hn hm hmn hS hinv
    have h := AronowAudit.P005.noninteracted_debiased_expansion
      (toPopulation P) m S v hn hm hmn hS hinv
    have hpre : debiasedATE P m S =
        (mean S P.yT - mean (control S) P.yC -
          dot (xMean P S - xMean P (control S)) ((Lhat P m S)⁻¹ *ᵥ Nhat P m S)) -
        dot (xMean P (control S) - xMean P S) (((Lhat P m S)⁻¹ - 1) *ᵥ Nhat P m S) +
        sampleCov S (leverage P) P.yT / (n - 2 : ℝ) -
        sampleCov (control S) (leverage P) P.yC / (n - 2 : ℝ) := by
      dsimp only [debiasedATE, adjustedATE, biasEstimate, betaHat, nu2]
      ring
    have h1 : debiasedATE P m S =
        mean S P.yT - mean (control S) P.yC -
          dot (xMean P S - xMean P (control S)) (Nhat P m S) +
          sampleCov S (leverage P) P.yT / (n - 2 : ℝ) -
          sampleCov (control S) (leverage P) P.yC / (n - 2 : ℝ) := h.1
    have h2 : debiasedATE P m S =
        mean S (fun i => P.yT i - dot (P.x i) v) -
          mean (control S) (fun i => P.yC i - dot (P.x i) v) -
          dot (xMean P S - xMean P (control S)) (Nhat P m S - v) +
          sampleCov S (leverage P) P.yT / (n - 2 : ℝ) -
          sampleCov (control S) (leverage P) P.yC / (n - 2 : ℝ) := h.2
    exact ⟨h1, h2, hpre, by linarith [h1, hpre], by linarith [h1, h2]⟩
  · intro n d m P hn hm hmn hx S hS
    exact AronowAudit.P005.control_minus_treated_mean_identities
      (toPopulation P) hn hm hmn hx S hS
  · intro n d m P hn hm hmn hP hinv
    exact (AronowAudit.P005.Wave1.noninteracted_exact_decomposition_proof
      (toPopulation P) hn hm hmn hP hinv).2.1
  · intro n d m hn hm hmn
    obtain ⟨F, hF⟩ := AronowAudit.P005.inverse_component_observable n d m hn hm hmn
    refine ⟨F, ?_⟩
    intro P hP S hS hinv
    exact hF (toPopulation P) hP S hS hinv

/-- The same observed array on both potential-outcome slots has the same
assignmentwise inverse correction, without a standardization hypothesis. -/
theorem observable_general (n d m : ℕ) :
    ∃ F : Finset (Fin n) → (Fin n → Fin d → ℝ) → (Fin n → ℝ) → ℝ,
      ∀ (P : Population n d) (S : Finset (Fin n)),
        dot (xMean P (control S)-xMean P S) (nu2 P m S) = F S P.x (observedOutcome P S) := by
  refine ⟨fun S x Y =>
    let Q : Population n d := ⟨x, Y, Y⟩
    dot (xMean Q (control S)-xMean Q S) (nu2 Q m S), ?_⟩
  intro P S
  let Q : Population n d := ⟨P.x, observedOutcome P S, observedOutcome P S⟩
  have ht : mean S (observedOutcome P S) = mean S P.yT := by
    apply AronowAudit.P005.mean_congr
    intro i hi
    simp [observedOutcome, observedResidual, hi]
  have hc : mean (control S) (observedOutcome P S) = mean (control S) P.yC := by
    apply AronowAudit.P005.mean_congr
    intro i hi
    have hnot : i ∉ S := (Finset.mem_sdiff.mp hi).2
    simp [observedOutcome, observedResidual, hnot]
  have htx : ∀ k, mean S (fun i => observedOutcome P S i*P.x i k) =
      mean S (fun i => P.yT i*P.x i k) := by
    intro k
    apply AronowAudit.P005.mean_congr
    intro i hi
    simp [observedOutcome, observedResidual, hi]
  have hcx : ∀ k, mean (control S) (fun i => observedOutcome P S i*P.x i k) =
      mean (control S) (fun i => P.yC i*P.x i k) := by
    intro k
    apply AronowAudit.P005.mean_congr
    intro i hi
    have hnot : i ∉ S := (Finset.mem_sdiff.mp hi).2
    simp [observedOutcome, observedResidual, hnot]
  have hN : Nhat Q m S = Nhat P m S := by
    funext k
    simp only [Nhat, armN, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change pT n m*(mean S (fun i => observedOutcome P S i*P.x i k)-
      mean S (observedOutcome P S)*xMean P S k) +
      pC n m*(mean (control S) (fun i => observedOutcome P S i*P.x i k)-
        mean (control S) (observedOutcome P S)*xMean P (control S) k) = _
    rw [ht, hc, htx k, hcx k]
  have hnu : nu2 Q m S = nu2 P m S := by
    simp only [nu2, hN]
    rfl
  change dot (xMean P (control S)-xMean P S) (nu2 P m S) =
    dot (xMean P (control S)-xMean P S) (nu2 Q m S)
  rw [hnu]

/-- The already-proved finite chain, stated with the SAP arrays. -/
theorem finite_chain {n d m : ℕ} (P : Population n d) (hn : 4 ≤ n)
    (hm : 0 < m) (hmn : m < n) (hP : standardized P) (t : Arm) (K : ℝ)
    (hK : popMean (fun i => (if t = .treated then P.yT i else P.yC i)^2) ≤ K) :
    let y := if t = .treated then P.yT else P.yC
    let u := fun i => leverage P i-(d : ℝ)
    let v := centered y
    popMean (leverage P) = d ∧
    (∀ i, 0 ≤ leverage P i ∧ leverage P i ≤ n*kappa P ∧ |u i| ≤ n*kappa P) ∧
    (d : ℝ) ≤ n*kappa P ∧
    popMean (fun i => u i^2) = popMean (fun i => leverage P i^2)-(d : ℝ)^2 ∧
    popMean (fun i => u i^2) ≤ n*kappa P*d ∧
    popMean (fun i => v i^2) = popMean (fun i => y i^2)-popMean y^2 ∧
    popMean (fun i => v i^2) ≤ K ∧
    popMean (fun i => (u i*v i-popMean (fun j => u j*v j))^2) ≤ popMean (fun i => u i^2*v i^2) ∧
    popMean (fun i => u i^2*v i^2) ≤ (n : ℝ)^2*kappa P^2*K ∧
    variance m (fun S => sampleCov (armSet t S) (leverage P) y) ≤ covarianceBound (armSize n m t) u v ∧
    covarianceBound (armSize n m t) u v ≤ W1LeverageRHS P (armSize n m t) K := by
  cases t with
  | treated =>
    exact AronowAudit.P005.Wave1.corrected_leverage_variance_chain_proof
      (toPopulation P) hn hm hmn hP .treated K hK
  | control =>
    exact AronowAudit.P005.Wave1.corrected_leverage_variance_chain_proof
      (toPopulation P) hn hm hmn hP .control K hK

end
end SAP.P005a.WH.W1
