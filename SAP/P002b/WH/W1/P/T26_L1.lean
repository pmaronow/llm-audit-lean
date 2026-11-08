import SAP.P002b.WH.W1.Leaves
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b.WH.W1.P.T26_L1

lemma no_cut_strictly_between {cuts : Finset ℝ} {a b z : ℝ}
    (hcell : SAP.P002b.SameOpenCell cuts a b) (hz : z ∈ cuts)
    (haz : a < z) (hzb : z < b) : False := by
  have hiff := hcell.2.2 z hz
  exact (not_lt_of_ge hzb.le) (hiff.mp haz)

lemma exists_root_strictly_between {p : Polynomial ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (ha : Polynomial.eval a p ≠ 0) (hb : Polynomial.eval b p ≠ 0)
    (hsign : (Polynomial.eval a p < 0 ∧ 0 < Polynomial.eval b p) ∨
      (Polynomial.eval b p < 0 ∧ 0 < Polynomial.eval a p)) :
    ∃ z, a < z ∧ z < b ∧ Polynomial.IsRoot p z := by
  let f : ℝ → ℝ := fun t => Polynomial.eval t p
  have hcont : ContinuousOn f (Set.Icc a b) := p.continuous.continuousOn
  have hroot : ∃ z, z ∈ Set.Icc a b ∧ f z = 0 := by
    rcases hsign with hsign | hsign
    · have hzero : (0 : ℝ) ∈ Set.Icc (f a) (f b) :=
        ⟨hsign.1.le, hsign.2.le⟩
      have himage : (0 : ℝ) ∈ f '' Set.Icc a b :=
        (intermediate_value_Icc hab hcont) hzero
      change ∃ z, z ∈ Set.Icc a b ∧ f z = 0 at himage
      rcases himage with ⟨z, hz, heval⟩
      exact ⟨z, hz, heval⟩
    · have hzero : (0 : ℝ) ∈ Set.Icc (f b) (f a) :=
        ⟨hsign.1.le, hsign.2.le⟩
      have himage : (0 : ℝ) ∈ f '' Set.Icc a b :=
        (intermediate_value_Icc' hab hcont) hzero
      change ∃ z, z ∈ Set.Icc a b ∧ f z = 0 at himage
      rcases himage with ⟨z, hz, heval⟩
      exact ⟨z, hz, heval⟩
  obtain ⟨z, hzIcc, hzval⟩ := hroot
  have haz : a < z := by
    rcases eq_or_lt_of_le hzIcc.1 with heq | hlt
    · subst z
      exact (ha hzval).elim
    · exact hlt
  have hzb : z < b := by
    rcases eq_or_lt_of_le hzIcc.2 with heq | hlt
    · subst z
      exact (hb hzval).elim
    · exact hlt
  exact ⟨z, haz, hzb, Polynomial.IsRoot.def.mpr hzval⟩

end SAP.P002b.WH.W1.P.T26_L1

theorem SAP.P002b.WH.W1.T26_L1_proof : SAP.P002b.WH.W1.T26_L1 := by
  intro ι _ p
  classical
  let rootUnion : Set ℝ := ⋃ i : ι, {z | p i ≠ 0 ∧ Polynomial.IsRoot (p i) z}
  have hrootUnionFinite : rootUnion.Finite := by
    dsimp [rootUnion]
    apply Set.finite_iUnion
    intro i
    by_cases hp : p i = 0
    · simp [hp]
    · exact (Polynomial.finite_setOfPred_isRoot hp).subset (by
        intro z hz
        exact hz.2)
  let cuts : Finset ℝ := hrootUnionFinite.toFinset
  have hcuts (z : ℝ) : z ∈ cuts ↔ z ∈ rootUnion := by
    simp [cuts]
  have hroot_cut {i : ι} {z : ℝ} (hp : p i ≠ 0)
      (hz : Polynomial.IsRoot (p i) z) : z ∈ cuts := by
    apply (hcuts z).mpr
    dsimp [rootUnion]
    exact Set.mem_iUnion.mpr ⟨i, ⟨hp, hz⟩⟩
  refine ⟨cuts, ?_⟩
  intro x y hcell i
  have eval_ne {z : ℝ} (hz : z ∉ cuts) (hp : p i ≠ 0) :
      Polynomial.eval z (p i) ≠ 0 := by
    intro heval
    exact hz (hroot_cut hp (Polynomial.IsRoot.def.mpr heval))
  by_cases hp : p i = 0
  · simp [hp]
  · have hxn : Polynomial.eval x (p i) ≠ 0 := eval_ne hcell.1 hp
    have hyn : Polynomial.eval y (p i) ≠ 0 := eval_ne hcell.2.1 hp
    have hzero : (Polynomial.eval x (p i) = 0 ↔ Polynomial.eval y (p i) = 0) := by
      constructor
      · intro hz
        exact (hxn hz).elim
      · intro hz
        exact (hyn hz).elim
    have hcellSym : SAP.P002b.SameOpenCell cuts y x :=
      ⟨hcell.2.1, hcell.1, fun c hc => (hcell.2.2 c hc).symm⟩
    have hneg : (Polynomial.eval x (p i) < 0 ↔ Polynomial.eval y (p i) < 0) := by
      constructor
      · intro hxneg
        by_contra hyNotNeg
        have hypos : 0 < Polynomial.eval y (p i) :=
          lt_of_le_of_ne (le_of_not_gt hyNotNeg) (Ne.symm hyn)
        rcases le_total x y with hxy | hyx
        · obtain ⟨z, haz, hzb, hzroot⟩ :=
          SAP.P002b.WH.W1.P.T26_L1.exists_root_strictly_between
            hxy hxn hyn (Or.inl ⟨hxneg, hypos⟩)
          exact SAP.P002b.WH.W1.P.T26_L1.no_cut_strictly_between
            hcell (hroot_cut hp hzroot) haz hzb
        · obtain ⟨z, haz, hzb, hzroot⟩ :=
          SAP.P002b.WH.W1.P.T26_L1.exists_root_strictly_between
            hyx hyn hxn (Or.inr ⟨hxneg, hypos⟩)
          exact SAP.P002b.WH.W1.P.T26_L1.no_cut_strictly_between
            hcellSym (hroot_cut hp hzroot) haz hzb
      · intro hyneg
        by_contra hxNotNeg
        have hxpos : 0 < Polynomial.eval x (p i) :=
          lt_of_le_of_ne (le_of_not_gt hxNotNeg) (Ne.symm hxn)
        rcases le_total x y with hxy | hyx
        · obtain ⟨z, haz, hzb, hzroot⟩ :=
            SAP.P002b.WH.W1.P.T26_L1.exists_root_strictly_between
              hxy hxn hyn (Or.inr ⟨hyneg, hxpos⟩)
          exact SAP.P002b.WH.W1.P.T26_L1.no_cut_strictly_between
            hcell (hroot_cut hp hzroot) haz hzb
        · obtain ⟨z, haz, hzb, hzroot⟩ :=
            SAP.P002b.WH.W1.P.T26_L1.exists_root_strictly_between
              hyx hyn hxn (Or.inl ⟨hyneg, hxpos⟩)
          exact SAP.P002b.WH.W1.P.T26_L1.no_cut_strictly_between
            hcellSym (hroot_cut hp hzroot) haz hzb
    exact ⟨hneg, hzero⟩
