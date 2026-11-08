import SAP.P037a.WH.W2.Leaves
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W2.P.T5_L1

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Classical Topology

private def sumLinearMap (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun q := ∑ i, q i
  map_add' q r := by simp [Finset.sum_add_distrib]
  map_smul' c q := by simp [Finset.mul_sum]

private theorem sum_hyperplane_null (m : ℕ) :
    volume {q : Fin m → ℝ | ∑ i, q i = 1} = 0 := by
  classical
  by_cases hm : m = 0
  · subst m
    simp
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let i0 : Fin m := ⟨0, hmpos⟩
    let p : Fin m → ℝ := Pi.single i0 1
    have hp : sumLinearMap m p = 1 := by
      simp [sumLinearMap, p]
    let H : AffineSubspace ℝ (Fin m → ℝ) :=
      AffineSubspace.mk' p (sumLinearMap m).ker
    have hH : (H : Set (Fin m → ℝ)) = {q | ∑ i, q i = 1} := by
      ext q
      change sumLinearMap m (q - p) = 0 ↔ ∑ i, q i = 1
      rw [map_sub, hp]
      change (∑ i, q i) - 1 = 0 ↔ ∑ i, q i = 1
      constructor <;> intro h <;> linarith
    have hstrict : H ≠ ⊤ := by
      intro htop
      have hz : (0 : Fin m → ℝ) ∈ H := by rw [htop]; simp
      change (0 : Fin m → ℝ) ∈ (H : Set (Fin m → ℝ)) at hz
      rw [hH] at hz
      simp at hz
    rw [← hH]
    exact Measure.addHaar_affineSubspace volume H hstrict

private theorem coordinate_hyperplane_null (m : ℕ) (i : Fin m) :
    volume {q : Fin m → ℝ | q i = 0} = 0 := by
  classical
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi_hyperplane (μ := fun _ : Fin m => (volume : Measure ℝ)) i 0

private theorem simplex_restrict_eq (m : ℕ) :
    volume.restrict (closedSimplexW2 m) = volume.restrict (openSimplex m) := by
  classical
  have hbadCoords : volume (⋃ i : Fin m, {q : Fin m → ℝ | q i = 0}) = 0 := by
    rw [measure_iUnion_null]
    intro i
    exact coordinate_hyperplane_null m i
  have hbadSum : volume {q : Fin m → ℝ | ∑ i, q i = 1} = 0 :=
    sum_hyperplane_null m
  have hbad : volume ((⋃ i : Fin m, {q : Fin m → ℝ | q i = 0}) ∪
      {q : Fin m → ℝ | ∑ i, q i = 1}) = 0 :=
    measure_union_null hbadCoords hbadSum
  have hopenClosed : openSimplex m ⊆ closedSimplexW2 m := by
    intro q hq
    change (∀ i, 0 ≤ q i) ∧ ∑ i, q i ≤ 1
    exact ⟨fun i => le_of_lt (hq.1 i), le_of_lt hq.2⟩
  have hdiff : closedSimplexW2 m \ openSimplex m ⊆
      (⋃ i : Fin m, {q : Fin m → ℝ | q i = 0}) ∪
        {q : Fin m → ℝ | ∑ i, q i = 1} := by
    intro q hq
    have hclosed : q ∈ closedSimplexW2 m := hq.1
    have hnotopen : q ∉ openSimplex m := hq.2
    change (∀ i, 0 ≤ q i) ∧ ∑ i, q i ≤ 1 at hclosed
    change ¬ ((∀ i, 0 < q i) ∧ ∑ i, q i < 1) at hnotopen
    rcases (not_and_or.mp hnotopen) with hcoord | hsum
    · rcases not_forall.mp hcoord with ⟨i, hi⟩
      have hzero : q i = 0 := le_antisymm (not_lt.mp hi) (hclosed.1 i)
      exact Or.inl (Set.mem_iUnion.mpr ⟨i, hzero⟩)
    · have hone : ∑ i, q i = 1 := le_antisymm hclosed.2 (not_lt.mp hsum)
      exact Or.inr hone
  have hset : closedSimplexW2 m =ᵐ[volume] openSimplex m := by
    apply ae_eq_set.mpr
    constructor
    · exact measure_mono_null hdiff hbad
    · have : openSimplex m \ closedSimplexW2 m = ∅ := by
        exact sdiff_eq_empty.mpr hopenClosed
      rw [this]
      simp
  exact Measure.restrict_congr_set hset

private theorem closed_simplex_volume (m : ℕ) :
    volume (closedSimplexW2 m) = (m.factorial : ℝ≥0∞)⁻¹ := by
  have hset : closedSimplexW2 m =
      Causalean.Stat.OrderStatistic.spacingSimplex m := by
    ext q
    rfl
  have hscale : Causalean.Stat.OrderStatistic.spacingSimplex m =
      Causalean.Stat.OrderStatistic.scaledSpacingSimplex m 1 := by
    ext q
    simp [Causalean.Stat.OrderStatistic.spacingSimplex,
      Causalean.Stat.OrderStatistic.scaledSpacingSimplex]
  rw [hset, hscale,
    Causalean.Stat.OrderStatistic.scaledSpacingSimplex_volume m 1 (by norm_num)]
  rw [one_pow]
  rw [ENNReal.ofReal_div_of_pos (by positivity : (m.factorial : ℝ) > 0)]
  simp [ENNReal.ofReal_natCast, div_eq_mul_inv]

end SAP.P037a.WH.W2.P.T5_L1

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Classical Topology

theorem SAP.P037a.WH.W2.T5_L1_proof : SAP.P037a.WH.W2.T5_L1 := by
  intro m
  constructor
  · exact SAP.P037a.WH.W2.P.T5_L1.simplex_restrict_eq m
  · have hrestr := SAP.P037a.WH.W2.P.T5_L1.simplex_restrict_eq m
    have hmeasure := congrArg (fun μ : MeasureTheory.Measure (Fin m → ℝ) => μ Set.univ) hrestr
    have hvol : volume (SAP.P037a.closedSimplexW2 m) = volume (SAP.P037a.openSimplex m) := by
      rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ] at hmeasure
      exact hmeasure
    exact hvol.symm.trans (SAP.P037a.WH.W2.P.T5_L1.closed_simplex_volume m)
