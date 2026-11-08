import SAP.P005a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P005a
open Finset
open scoped BigOperators Matrix

theorem SAP.P005a.WH.W1.T14_L1_proof : SAP.P005a.WH.W1.T14_L1 := by
  change W1WrongSumFacts
  let P := W1WrongSumPopulation
  have hU : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by
    ext i
    fin_cases i <;> simp
  have hC0 : control ({0} : Finset (Fin 4)) = {1, 2, 3} := by
    ext i
    fin_cases i <;> simp [control, hU]
  have hC1 : control ({1} : Finset (Fin 4)) = {0, 2, 3} := by
    ext i
    fin_cases i <;> simp [control, hU]
  have hC2 : control ({2} : Finset (Fin 4)) = {0, 1, 3} := by
    ext i
    fin_cases i <;> simp [control, hU]
  have hC3 : control ({3} : Finset (Fin 4)) = {0, 1, 2} := by
    ext i
    fin_cases i <;> simp [control, hU]
  have hstd : standardized P := by
    constructor
    · ext k
      fin_cases k
      norm_num [P, W1WrongSumPopulation, standardized, xMean, mean, popMean,
        Fin.sum_univ_succ]
    · ext k l
      fin_cases k <;> fin_cases l <;>
        norm_num [P, W1WrongSumPopulation, standardized, gram, popMean, mean,
          Fin.sum_univ_succ]
  have hregular : noninteractedRegular P 1 := by
    intro S hS
    have hc : S.card = 1 := (Finset.mem_powersetCard.mp hS).2
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    fin_cases i
    · norm_num [P, W1WrongSumPopulation, Lhat, pT, pC, xMean, mean, hC0,
        Fin.sum_univ_succ, Matrix.vecMulVec, Matrix.det_fin_one]
    · norm_num [P, W1WrongSumPopulation, Lhat, pT, pC, xMean, mean, hC1,
        Fin.sum_univ_succ, Matrix.vecMulVec, Matrix.det_fin_one]
    · norm_num [P, W1WrongSumPopulation, Lhat, pT, pC, xMean, mean, hC2,
        Fin.sum_univ_succ, Matrix.vecMulVec, Matrix.det_fin_one]
    · norm_num [P, W1WrongSumPopulation, Lhat, pT, pC, xMean, mean, hC3,
        Fin.sum_univ_succ, Matrix.vecMulVec, Matrix.det_fin_one]
  have hN : N P 1 = 0 := by
    ext k
    fin_cases k
    norm_num [P, W1WrongSumPopulation, N, pT, pC, populationSlope, popMean,
      mean, Fin.sum_univ_succ]
  have hT : ({0} : Finset (Fin 4)) ∈ design 4 1 := by
    simp [design, Finset.mem_powersetCard]
  refine ⟨hstd, hregular, hN, hT, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [P, W1WrongSumPopulation, popMean, mean, Fin.sum_univ_succ]
  · norm_num [P, W1WrongSumPopulation, popMean, mean, Fin.sum_univ_succ]
  · intro k
    fin_cases k
    norm_num [P, W1WrongSumPopulation, popMean, mean, Fin.sum_univ_succ]
  · norm_num [pT]
  · norm_num [pT]
  · rw [hN]
    norm_num [P, W1WrongSumPopulation, mean, hU, dot]
  · rw [hN]
    rw [hC0]
    norm_num [P, W1WrongSumPopulation, mean, xMean, dot, Fin.sum_univ_succ]
