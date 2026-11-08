import SAP.P007.Defs.WholeW2
import SAP.P007.Bridge
import AronowAudit.P007.P007_Probability

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P007.WH.W2

open MeasureTheory SAP.P007.Bridge AronowAudit.P007
open scoped BigOperators

universe u

/-- Exact finite-law reduction for any measurable binary array on an arbitrary
probability space. The pushforward's singleton masses give normalized weights;
finite additivity gives all event probabilities, and integral_map followed by
integral_fintype gives the expectations and their integrability. This is short
Mathlib glue, so it is proved here. No independence is assumed, and zero
dimensions work as well. -/
theorem finite_law_realization {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n k : ℕ)
    (M : Ω → Array n k) (hM : Measurable M) :
    ∃ L : Law (Array n k), lawRealizesW2 μ M L := by
  classical
  let ν := μ.map M
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hM.aemeasurable).mpr inferInstance
  have ht : ∑ x : Array n k, ν.real {x} = 1 := by simp
  let L : Law (Array n k) :=
    ⟨fun x => ν.real {x}, fun _ => ENNReal.toReal_nonneg, ht⟩
  refine ⟨L, ?_, ?_⟩
  · intro P
    change (∑ x, if P x then ν.real {x} else 0) = _
    rw [← Finset.sum_filter, sum_measureReal_singleton]
    have hset : (↑(Finset.univ.filter P) : Set (Array n k)) = {x | P x} := by
      ext x
      simp
    rw [hset]
    exact map_measureReal_apply hM (Set.toFinite _).measurableSet
  · intro f
    have hf : Integrable f ν := Integrable.of_finite
    refine ⟨hf.comp_measurable hM, ?_⟩
    rw [← integral_map hM.aemeasurable hf.aestronglyMeasurable, integral_fintype hf]
    rfl

/-- Elementary transfer of prefix probabilities and Assumption 2 along an
exact finite joint distribution; the positive-prefix proviso is unchanged. -/
theorem observation_transfer {Ω : Type u} [MeasurableSpace Ω] {n k : ℕ}
    (μ : Measure Ω) (M : Ω → Array n k) (L : Law (Array n k))
    (hL : lawRealizesW2 μ M L) (q : ℝ) :
    observationBound L q ↔ observationBoundOnW2 μ M q := by
  have hs (i : Fin n) (j : ℕ) : survival L i j = survivalOnW2 μ M i j :=
    hL.1 (fun x => prefixObserved (x i) j)
  simp only [observationBound, observationBoundOnW2, hs]

/-- Independence of all cells determines every atom from its Boolean marginals.
This is a short finite-probability argument, proved here rather than made a leaf. -/
theorem independent_weights {n k : ℕ} (L : Law (Array n k)) (q : ℝ)
    (hi : cellsIndependentW2 L)
    (hm : ∀ i j, probability L (fun x => x i j = false) = q) :
    L.weight = equalWeights n k q := by
  classical
  have htrue (i : Fin n) (j : Fin k) :
      probability L (fun x => x i j = true) = 1 - q := by
    calc
      probability L (fun x => x i j = true) =
          probability L (fun x => ¬ x i j = false) := by
        apply probability_congr (toAudit L)
        intro x
        cases x i j <;> simp
      _ = 1 - probability L (fun x => x i j = false) :=
        probability_compl (toAudit L) _
      _ = 1 - q := by rw [hm i j]
  funext x
  have he : (fun y : Array n k => ∀ i j, y i j = x i j) = (fun y => y = x) := by
    funext y
    exact propext ⟨fun h => funext (fun i => funext (h i)), fun h => by simp [h]⟩
  have hh := hi (fun i j b => b = x i j)
  rw [he] at hh
  have hatom : probability L (fun y => y = x) = L.weight x := by
    unfold probability
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [hy]
    · simp
  rw [hatom] at hh
  rw [hh]
  unfold equalWeights cellWeights
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  cases x i j <;> simp [hm i j, htrue i j]

/-- All cells of the existing product model are mutually independent, with the
prescribed observed marginals. Two applications of the existing product-event
and product-marginal formulas suffice. -/
theorem equal_cells (n k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    cellsIndependentW2 (fromAudit (equalProbabilityLaw n k q hq0 hq1)) ∧
    ∀ i j, probability (fromAudit (equalProbabilityLaw n k q hq0 hq1))
      (fun x => x i j = false) = q := by
  let B := observationBernoulli q hq0 hq1
  let R := independentProduct (fun _ : Fin k => B)
  have hm (i : Fin n) (j : Fin k) (E : Bool → Prop) :
      eventProbability (equalProbabilityLaw n k q hq0 hq1) (fun x => E (x i j)) =
        eventProbability (observationBernoulli q hq0 hq1) E := by
    exact (independentProduct_marginal (fun _ : Fin n => R) i
      (fun r => E (r j))).trans
      (independentProduct_marginal (fun _ : Fin k => B) j E)
  constructor
  · intro E
    change eventProbability (equalProbabilityLaw n k q hq0 hq1)
      (fun x => ∀ i j, E i j (x i j)) = _
    calc
      eventProbability (equalProbabilityLaw n k q hq0 hq1)
          (fun x => ∀ i j, E i j (x i j)) =
          ∏ i, eventProbability R (fun r => ∀ j, E i j (r j)) :=
        independentProduct_events (fun _ : Fin n => R) (fun i r => ∀ j, E i j (r j))
      _ = ∏ i, ∏ j, eventProbability B (E i j) := by
        apply Finset.prod_congr rfl
        intro i _
        exact independentProduct_events (fun _ : Fin k => B) (E i)
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        apply Finset.prod_congr rfl
        intro j _
        exact (hm i j (E i j)).symm
  · intro i j
    exact (hm i j (fun b => b = false)).trans (observationBernoulli_false q hq0 hq1)

/-- Whole corrected claim, with no unproved leaves. Existing expectation and
attainment theorems supply the finite probability inequalities, and the proved
finite-law reduction covers arbitrary underlying probability spaces. The short
independence and endpoint arguments above and below supply the remaining clauses,
including the corrected equality criterion n=1 or q=0. -/
theorem T10_assembly : T10WholeStatement_W2.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Ω _ μ _ n k hn _ M hM q hb
    obtain ⟨L, hL⟩ := finite_law_realization μ n k M hM
    have hbound : observationBound L q := (observation_transfer μ M L hL q).mpr hb
    have hd := expected_deletion_lower_bound (toAudit L) hn hbound
    have hs (i : Fin n) : survival L i k = survivalOnW2 μ M i k :=
      hL.1 (fun x => prefixObserved (x i) k)
    constructor
    · intro i
      refine ⟨(hL.2 (fun x => deletedIndicator x i)).1, ?_, ?_⟩
      · rw [(hL.2 (fun x => deletedIndicator x i)).2]
        exact (expected_removed_row (toAudit L) i).trans
          (congrArg (fun s : ℝ => 1 - s) (hs i))
      · rw [(hL.2 (fun x => deletedIndicator x i)).2]
        exact hd.1 i
    · refine ⟨(hL.2 deletedFraction).1, ?_, ?_⟩
      · rw [(hL.2 deletedFraction).2]
        have hf : expectation L deletedFraction = (∑ i, (1 - survival L i k)) / n :=
          expected_removed_fraction (toAudit L)
        simpa only [hs] using hf
      · rw [(hL.2 deletedFraction).2]
        exact hd.2
  · intro Ω _ μ _ n k hn _ M hM q hq0 hq1 hi hm
    obtain ⟨L, hL⟩ := finite_law_realization μ n k M hM
    have hci : cellsIndependentW2 L := by
      intro E
      simpa only [hL.1] using hi E
    have hcm (i : Fin n) (j : Fin k) : probability L (fun x => x i j = false) = q :=
      (hL.1 _).trans (hm i j)
    let A := equalProbabilityLaw n k q hq0 hq1.le
    have heq : L = fromAudit A := by
      have hw : L.weight = (fromAudit A).weight := independent_weights L q hci hcm
      have hext (J K : Law (Array n k)) (h : J.weight = K.weight) : J = K := by
        cases J
        cases K
        cases h
        rfl
      exact hext L (fromAudit A) hw
    have ha := bestCase_attained n k q hq0 hq1
    have hr : rowIndependent L := by rw [heq]; exact ha.1
    have hb : observationBound L q := by rw [heq]; exact ha.2.1
    refine ⟨?_, (observation_transfer μ M L hL q).mp hb, ?_⟩
    · intro E
      simpa only [hL.1] using hr E
    · rw [(hL.2 deletedFraction).2, heq]
      exact expected_deletion_bound_attained hn q hq0 hq1
  · intro n k hn _ q hq0 hq1
    let L := fromAudit (equalProbabilityLaw n k q hq0 hq1.le)
    have ha := bestCase_attained n k q hq0 hq1
    have hc := equal_cells n k q hq0 hq1.le
    exact ⟨L, rfl, hc.1, ha.1, ha.2.1, hc.2,
      expected_deletion_bound_attained hn q hq0 hq1⟩
  · intro n k hn hk q hq0 hq1
    have hz (hq : q = 0) : fractionBound q k = 1 ∧ lowerBound n q k = 1 := by
      subst q
      simp [fractionBound, lowerBound, zero_pow (Nat.ne_of_gt hk)]
    have hs (hq : 0 < q) (hn2 : 2 ≤ n) :
        0 < fractionBound q k ∧ fractionBound q k < 1 ∧
          lowerBound n q k < fractionBound q k :=
      (fraction_bound_vs_all_bound hn2 hk hq hq1).2.2
    refine ⟨rfl, by simp [lowerBound, fractionBound], hs, ?_, hz⟩
    constructor
    · intro he
      by_cases hn1 : n = 1
      · exact Or.inl hn1
      · right
        by_contra hq
        have hlt := (hs (lt_of_le_of_ne hq0 (Ne.symm hq)) (by omega)).2.2
        exact (ne_of_lt hlt) he
    · rintro (hn1 | hq)
      · simp [hn1, lowerBound, fractionBound]
      · exact (hz hq).2.trans (hz hq).1.symm

end SAP.P007.WH.W2
