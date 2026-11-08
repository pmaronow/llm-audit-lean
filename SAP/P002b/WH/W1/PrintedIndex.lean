import SAP.P002b.Defs.WholeW1
import SAP.P002b.Bridge
import AronowAudit.P002.Wave1.AlgorithmSupport.N1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace SAP.P002b.WH.W1
noncomputable section
open SAP.P002b SAP.P002b.Bridge
open scoped BigOperators ENNReal Matrix Topology
attribute [local instance] Classical.propDecidable

private abbrev g (m : Fin 2) := arFunction (printedIndexFamily m)

theorem printed_index_regular : ARRegular printedIndexQ0 ∧ ∀ m, ARRegular (printedIndexFamily m) := by
  have h0 : ARRegular printedIndexQ0 := by
    constructor
    · intro β; norm_num [printedIndexQ0]
    · intro β; dsimp [printedIndexQ0]; nlinarith [sq_nonneg (β+5/2)]
  have h1 : ARRegular printedIndexQ1 := by
    constructor
    · intro β; dsimp [printedIndexQ1]; nlinarith [sq_nonneg (β+5/2)]
    · intro β; norm_num [printedIndexQ1]
  refine ⟨h0, ?_⟩
  intro m
  fin_cases m <;> simpa [printedIndexFamily] using (by assumption : ARRegular _)

theorem printed_index_pair_eq (β : ℝ) :
    arFunction printedIndexQ0 β = arFunction printedIndexQ1 β ↔ β = -4 ∨ β = -1 := by
  have hd : (1/64 : ℝ)*β^2 + (5/64)*β + 13/128 ≠ 0 := by
    have H := (printed_index_regular.2 1).1 β
    change 0 < (1/64 : ℝ)*β^2 + (5/64)*β + 13/128 at H
    exact ne_of_gt H
  simp only [arFunction, printedIndexQ0, printedIndexQ1, zero_mul, zero_add]
  rw [div_eq_div_iff (by norm_num) hd]
  constructor
  · intro H
    have hfactor : (β+4)*(β+1)*(4*β^2+20*β+35) = 0 := by nlinarith [H]
    have hpos : 0 < 4*β^2+20*β+35 := by nlinarith [sq_nonneg (β+5/2)]
    have hprod := (mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hpos)
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

theorem printed_index_distinct : g 0 ≠ g 1 := by
  intro h
  have H := congrFun h 0
  norm_num [g, printedIndexFamily, arFunction, printedIndexQ0, printedIndexQ1] at H

theorem printed_index_selected_crossings (m : Fin 2) (β : ℝ) :
    (∃ s, g s ≠ g m ∧ g s β = g m β) ↔ β = -4 ∨ β = -1 := by
  have h01 : g 0 ≠ g 1 := printed_index_distinct
  have h10 : g 1 ≠ g 0 := Ne.symm h01
  have he : g 0 β = g 1 β ↔ β = -4 ∨ β = -1 := printed_index_pair_eq β
  have he' : g 1 β = g 0 β ↔ β = -4 ∨ β = -1 := eq_comm.trans he
  fin_cases m <;> simp [Fin.exists_fin_two, h01, h10, he, he']

theorem printed_index_intersections : IntersectionList g [-4,-1] := by
  constructor
  · norm_num
  · intro β
    constructor
    · intro h
      have hβ : β = -4 ∨ β = -1 := by simpa using h
      obtain ⟨s, hs⟩ := (printed_index_selected_crossings 0 β).mpr hβ
      exact ⟨s, 0, hs⟩
    · rintro ⟨s, m, hne, he⟩
      have hβ := (printed_index_selected_crossings m β).mp ⟨s, hne, he⟩
      simpa using hβ

theorem printed_index_quantile_samples :
    (1 : Fin 2) ∈ mcIndices g (1/2) (-5) ∧
    (0 : Fin 2) ∈ mcIndices g (1/2) (-5/2) ∧
    (1 : Fin 2) ∈ mcIndices g (1/2) 0 := by
  have hn (m : Fin 2) (β : ℝ) : 0 ≤ g m β :=
    div_nonneg ((printed_index_regular.2 m).2 β) ((printed_index_regular.2 m).1 β).le
  have hu : (Finset.univ : Finset (Fin 2)) = {0,1} := by decide
  constructor
  · apply (AronowAudit.P002.quantile_index_rank g (by decide) (1/2) (-5)
      (by constructor <;> norm_num) (fun m => hn m (-5)) 1).mpr
    norm_num [hu, g, printedIndexFamily, arFunction, printedIndexQ0, printedIndexQ1,
      Finset.filter_insert, Finset.filter_singleton, Finset.filter_empty]
    exact ⟨1, by norm_num [g, printedIndexFamily, arFunction, printedIndexQ0, printedIndexQ1]⟩
  · constructor
    · apply (AronowAudit.P002.quantile_index_rank g (by decide) (1/2) (-5/2)
        (by constructor <;> norm_num) (fun m => hn m (-5/2)) 0).mpr
      norm_num [hu, g, printedIndexFamily, arFunction, printedIndexQ0, printedIndexQ1,
        Finset.filter_insert, Finset.filter_singleton, Finset.filter_empty]
      exact ⟨0, by norm_num [g, printedIndexFamily, arFunction, printedIndexQ0, printedIndexQ1]⟩
    · apply (AronowAudit.P002.quantile_index_rank g (by decide) (1/2) 0
        (by constructor <;> norm_num) (fun m => hn m 0) 1).mpr
      norm_num [hu, g, printedIndexFamily, arFunction, printedIndexQ0, printedIndexQ1,
        Finset.filter_insert, Finset.filter_singleton, Finset.filter_empty]
      exact ⟨1, by norm_num [g, printedIndexFamily, arFunction, printedIndexQ0, printedIndexQ1]⟩

theorem printed_index_run : Algorithm2Run g (1/2) [-4,-1] printedIndexPieces := by
  have hfilter : ([-4,-1] : List ℝ).filter
      (fun β : ℝ => (((-4 : ℝ) : EReal) < (β : EReal))) = [-1] := by
    simp only [EReal.coe_lt_coe_iff]
    norm_num
  have hfilterLast : ([-4,-1] : List ℝ).filter
      (fun β : ℝ => (((-1 : ℝ) : EReal) < (β : EReal))) = [] := by
    simp only [EReal.coe_lt_coe_iff]
    norm_num
  have hfirst : Algorithm2Step g (1/2) [-4,-1]
      ⟨⊥, (-4 : ℝ), 1⟩ (some ⟨(-4 : ℝ), (-1 : ℝ), 0⟩) := by
    unfold Algorithm2Step
    simp_rw [printed_index_selected_crossings]
    simp only [EReal.bot_lt_coe, true_and]
    have hc : {β : ℝ | β = -4 ∨ β = -1}.Nonempty := ⟨-4, Or.inl rfl⟩
    rw [ite_eq_left hc]
    constructor
    · refine ⟨-4, ⟨Or.inl rfl, ?_⟩, rfl⟩
      intro β hβ
      rcases hβ with rfl | rfl <;> norm_num
    · simp only [hfilter]
      convert printed_index_quantile_samples.2.1 using 1; norm_num
  have hmiddle : Algorithm2Step g (1/2) [-4,-1]
      ⟨(-4 : ℝ), (-1 : ℝ), 0⟩ (some ⟨(-1 : ℝ), ⊤, 1⟩) := by
    unfold Algorithm2Step
    simp_rw [printed_index_selected_crossings]
    have hc : {β : ℝ | ((-4 : ℝ) : EReal) < (β : EReal) ∧ (β = -4 ∨ β = -1)}.Nonempty := by
      exact ⟨-1, EReal.coe_lt_coe_iff.mpr (by norm_num), Or.inr rfl⟩
    rw [ite_eq_left hc]
    constructor
    · refine ⟨-1, ⟨⟨EReal.coe_lt_coe_iff.mpr (by norm_num), Or.inr rfl⟩, ?_⟩, rfl⟩
      intro β hβ
      rcases hβ.2 with h | rfl
      · subst β; exact (lt_irrefl (((-4 : ℝ) : EReal)) hβ.1).elim
      · exact le_rfl
    · simp only [hfilterLast, EReal.toReal_coe, true_and]
      convert printed_index_quantile_samples.2.2 using 1; norm_num
      intro _
      exact EReal.coe_ne_bot (1 : ℝ)
  have hlast : Algorithm2Step g (1/2) [-4,-1] ⟨(-1 : ℝ), ⊤, 1⟩ none := by
    unfold Algorithm2Step
    simp_rw [printed_index_selected_crossings]
    have hc : ¬ {β : ℝ | ((-1 : ℝ) : EReal) < (β : EReal) ∧ (β = -4 ∨ β = -1)}.Nonempty := by
      rintro ⟨β, hβ, h | h⟩ <;> subst β <;>
        have H := EReal.coe_lt_coe_iff.mp hβ <;> norm_num at H
    rw [ite_eq_right hc]
    simp
  refine ⟨printed_index_intersections, by decide, by simp [printedIndexPieces], ?_, ?_⟩
  · intro p hp
    simp only [printedIndexPieces, List.head?_cons, Option.some.injEq] at hp
    subst p
    refine ⟨rfl, ?_⟩
    convert printed_index_quantile_samples.1 using 1; norm_num
  · intro i
    fin_cases i
    · exact hfirst
    · exact hmiddle
    · exact hlast

theorem printed_index_data :
    printedIndexQ0 = dataCoefficients printedIndexPopulation false printedIndexObserved printedIndexObserved ∧
    ∀ m, printedIndexFamily m = dataCoefficients printedIndexPopulation false
      printedIndexObserved (printedIndexSimulated m) := by
  have hO : printedIndexObservedᶜ = ({2,3} : Finset (Fin 4)) := by decide
  have hU : ({0,2} : Finset (Fin 4))ᶜ = {1,3} := by decide
  have h0 : printedIndexQ0 = dataCoefficients printedIndexPopulation false printedIndexObserved printedIndexObserved := by
    dsimp only [dataCoefficients, rawCoefficients, printedIndexQ0]
    congr 1 <;>
      simp only [rawVarianceCross, rawSigma2, rawTau, armMean, groupMean,
        Bool.false_eq_true, ite_false, ite_true, hO] <;>
      norm_num [rawVarianceCross, rawSigma2, rawTau, armMean, groupMean,
      observedY, observedD, binary, fraction, controlSize, printedIndexPopulation,
      printedIndexObserved, hO, Fin.sum_univ_succ, Finset.filter_insert,
      Finset.filter_singleton, Finset.filter_empty]
  have h1 : printedIndexQ1 = dataCoefficients printedIndexPopulation false printedIndexObserved {0,2} := by
    dsimp only [dataCoefficients, rawCoefficients, printedIndexQ1]
    congr 1 <;> norm_num [rawVarianceCross, rawSigma2, rawTau, armMean, groupMean,
      observedY, observedD, binary, fraction, controlSize, printedIndexPopulation,
      printedIndexObserved, hU, Fin.sum_univ_succ, Finset.filter_insert,
      Finset.filter_singleton, Finset.filter_empty]
  refine ⟨h0, ?_⟩
  intro m
  fin_cases m
  · simpa [printedIndexFamily, printedIndexSimulated] using h0
  · simpa [printedIndexFamily, printedIndexSimulated] using h1

/-- The refutation uses a defined middle printed term; every completion of the
undefined final term still contains its spurious accepted point. -/
theorem printed_index_refutation : T28WholeStatement := by
  have hv : ValidDesign printedIndexPopulation.pop := by norm_num [ValidDesign, printedIndexPopulation]
  have hm : MonotoneReceipt printedIndexPopulation.pop := by simp [MonotoneReceipt, printedIndexPopulation]
  have hc : (compliers printedIndexPopulation.pop).Nonempty := by simp [compliers, printedIndexPopulation]
  have hO : printedIndexObserved ∈ assignments printedIndexPopulation.pop := by decide
  have hT : ∀ m, printedIndexSimulated m ∈ assignments printedIndexPopulation.pop := by
    intro m; fin_cases m <;> decide
  have hdata : DataGeneratedCoefficients printedIndexQ0 printedIndexFamily := by
    exact ⟨4, 0, printedIndexPopulation, false, printedIndexObserved, printedIndexSimulated,
      hv, hm, hc, hO, hT, by simp, printed_index_data.1, printed_index_data.2⟩
  have hshift : (0 : ℝ) ∈ printedStep5DefinedSet (arFunction printedIndexQ0) g printedIndexPieces := by
    refine ⟨⟨(-4 : ℝ), (-1 : ℝ), 0⟩, ⟨(-1 : ℝ), ⊤, 1⟩, ?_, ?_, le_rfl⟩
    · simp [printedIndexPieces]
    · constructor <;> norm_num [closedInterval]
  have hreject : (0 : ℝ) ∉ mcSet (arFunction printedIndexQ0) g (1/2) := by
    have hcrit := (Finset.mem_filter.mp printed_index_quantile_samples.2.2).2
    intro h
    change Real.sqrt (arFunction printedIndexQ0 0) ≤ mcCritical g (1/2) 0 at h
    rw [← hcrit] at h
    have H := (Real.sqrt_le_sqrt_iff (show 0 ≤ g 1 0 by
      norm_num [g, printedIndexFamily, arFunction, printedIndexQ1])).mp h
    norm_num [g, printedIndexFamily, arFunction, printedIndexQ0, printedIndexQ1] at H
  refine ⟨hv, hm, hc, hO, hT, printed_index_data.1, printed_index_data.2, hdata,
    printed_index_regular.1, printed_index_regular.2, printed_index_intersections,
    printed_index_run, ?_, ?_, hshift, hreject, ?_⟩
  · norm_num [arFunction, printedIndexQ0]
  · norm_num [g, printedIndexFamily, arFunction, printedIndexQ1]
  · intro returned hsub heq
    exact hreject (heq ▸ hsub hshift)

end
end SAP.P002b.WH.W1
