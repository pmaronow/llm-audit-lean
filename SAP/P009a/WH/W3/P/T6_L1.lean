import SAP.P009a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped Topology Classical

theorem SAP.P009a.WH.W3.T6_L1_proof : SAP.P009a.WH.W3.T6_L1 := by
  intro a hab hnot
  have hupper : IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ) a :=
    Filter.isBoundedUnder_of ⟨1, fun t => (hab t).2⟩
  have hlower : IsBoundedUnder (· ≥ ·) (atTop : Filter ℕ) a :=
    Filter.isBoundedUnder_of ⟨0, fun t => (hab t).1⟩
  have hliminf : (0 : ℝ) ≤ liminf a atTop :=
    le_liminf_of_le hupper.isCoboundedUnder_ge
      (Eventually.of_forall (fun t : ℕ => (hab t).1))
  have hlimsupUpper : limsup a atTop ≤ 1 :=
    limsup_le_of_le hlower.isCoboundedUnder_le
      (Eventually.of_forall (fun t : ℕ => (hab t).2))
  have hlimsupPos : 0 < limsup a atTop := by
    by_contra h
    have hle : limsup a atTop ≤ 0 := le_of_not_gt h
    have htendsto : Tendsto a atTop (nhds 0) :=
      tendsto_of_le_liminf_of_limsup_le hliminf hle hupper hlower
    exact hnot htendsto
  refine ⟨?_, hlimsupPos, hlimsupUpper⟩
  constructor
  · intro ε hε
    exact eventually_lt_add_pos_of_limsup_le hupper le_rfl hε
  · intro ε hε
    have hbelow : limsup a atTop - ε < limsup a atTop := by linarith
    exact frequently_lt_of_lt_limsup hlower.isCoboundedUnder_le hbelow
