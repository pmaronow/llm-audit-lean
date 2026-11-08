import SAP.P026a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P026a.WH.W1.P.T6_L1

open Finset
open scoped BigOperators

private theorem block_rank (b : Bool) : w1FullRank (w1BlockDesign b) := by
  intro β h
  cases b with
  | false =>
      have h0 := h ⟨0, by simp [w1BlockUnits]⟩
      have h1 := h ⟨1, by simp [w1BlockUnits]⟩
      have he0 : β 0 + 4 * β 1 = 0 := by
        simpa [w1Predict, w1BlockDesign, paperTableX] using h0
      have he1 : β 0 + 0 * β 1 = 0 := by
        simpa [w1Predict, w1BlockDesign, paperTableX] using h1
      have hb1 : β 1 = 0 := by linarith
      have hb0 : β 0 = 0 := by linarith
      funext j
      fin_cases j <;> simp [hb0, hb1]
  | true =>
      have h6 := h ⟨6, by simp [w1BlockUnits]⟩
      have h7 := h ⟨7, by simp [w1BlockUnits]⟩
      have he6 : β 0 + 4 * β 1 = 0 := by
        simpa [w1Predict, w1BlockDesign, paperTableX] using h6
      have he7 : β 0 + 1 * β 1 = 0 := by
        simpa [w1Predict, w1BlockDesign, paperTableX] using h7
      have hb1 : β 1 = 0 := by linarith
      have hb0 : β 0 = 0 := by linarith
      funext j
      fin_cases j <;> simp [hb0, hb1]

private theorem block_sum_cast (b : Bool) (f : Fin 16 → ℚ) :
    (∑ i : ↥(w1BlockUnits b), (f i : ℝ)) =
      ((∑ i ∈ w1BlockUnits b, f i : ℚ) : ℝ) := by
  calc
    (∑ i : ↥(w1BlockUnits b), (f i : ℝ)) =
        ∑ i ∈ w1BlockUnits b, (f i : ℝ) := by
      exact (Finset.sum_subtype (w1BlockUnits b) (by intro i; rfl)
        (fun i => (f i : ℝ))).symm
    _ = ((∑ i ∈ w1BlockUnits b, f i : ℚ) : ℝ) := by
      rw [Rat.cast_sum]

private theorem block_normal (b : Bool) :
    w1Normal (w1BlockDesign b) (w1BlockY b) (w1BlockCoefficients b) := by
  cases b with
  | false =>
      intro j
      fin_cases j
      · have hrat := AronowAudit.P026.table_linear_fits.1
        have hcast := congrArg (fun q : ℚ => (q : ℝ)) hrat
        have hsum : (∑ i : ↥(w1BlockUnits false),
            ((paperTableY i - (70/93 + paperTableX i/31) : ℚ) : ℝ)) = 0 := by
          rw [block_sum_cast false (fun i => paperTableY i - (70/93 + paperTableX i/31))]
          simpa [w1BlockUnits, paperTableX, paperTableY,
            AronowAudit.P026.tableX, AronowAudit.P026.tableY] using hcast
        simpa [w1Normal, w1Predict, w1BlockDesign, w1BlockY,
          w1BlockCoefficients, Finset.sum_sub_distrib, div_eq_mul_inv] using hsum
      · have hrat := AronowAudit.P026.table_linear_fits.2.1
        have hcast := congrArg (fun q : ℚ => (q : ℝ)) hrat
        have hsum : (∑ i : ↥(w1BlockUnits false),
            ((paperTableX i * (paperTableY i - (70/93 + paperTableX i/31)) : ℚ) : ℝ)) = 0 := by
          rw [block_sum_cast false (fun i => paperTableX i * (paperTableY i - (70/93 + paperTableX i/31)))]
          simpa [w1BlockUnits, paperTableX, paperTableY,
            AronowAudit.P026.tableX, AronowAudit.P026.tableY] using hcast
        simpa [w1Normal, w1Predict, w1BlockDesign, w1BlockY,
          w1BlockCoefficients, div_eq_mul_inv] using hsum
  | true =>
      intro j
      fin_cases j
      · have hrat := AronowAudit.P026.table_linear_fits.2.2.1
        have hcast := congrArg (fun q : ℚ => (q : ℝ)) hrat
        have hsum : (∑ i : ↥(w1BlockUnits true),
            ((paperTableY i - (1/4 + paperTableX i/8) : ℚ) : ℝ)) = 0 := by
          rw [block_sum_cast true (fun i => paperTableY i - (1/4 + paperTableX i/8))]
          simpa [w1BlockUnits, paperTableX, paperTableY,
            AronowAudit.P026.tableX, AronowAudit.P026.tableY] using hcast
        simpa [w1Normal, w1Predict, w1BlockDesign, w1BlockY,
          w1BlockCoefficients, Finset.sum_sub_distrib, div_eq_mul_inv] using hsum
      · have hrat := AronowAudit.P026.table_linear_fits.2.2.2.1
        have hcast := congrArg (fun q : ℚ => (q : ℝ)) hrat
        have hsum : (∑ i : ↥(w1BlockUnits true),
            ((paperTableX i * (paperTableY i - (1/4 + paperTableX i/8)) : ℚ) : ℝ)) = 0 := by
          rw [block_sum_cast true (fun i => paperTableX i * (paperTableY i - (1/4 + paperTableX i/8)))]
          simpa [w1BlockUnits, paperTableX, paperTableY,
            AronowAudit.P026.tableX, AronowAudit.P026.tableY] using hcast
        simpa [w1Normal, w1Predict, w1BlockDesign, w1BlockY,
          w1BlockCoefficients, div_eq_mul_inv] using hsum

end SAP.P026a.WH.W1.P.T6_L1

theorem SAP.P026a.WH.W1.T6_L1_proof : SAP.P026a.WH.W1.T6_L1 := by
  intro b
  exact ⟨SAP.P026a.WH.W1.P.T6_L1.block_rank b,
    SAP.P026a.WH.W1.P.T6_L1.block_normal b⟩
