import SAP.P001g.Defs
import SAP.P001g.Bridge
import SAP.P001g.WH.W1.Proofs.T115
import SAP.P001g.WH.W1.Proofs.T117
import SAP.P001g.WH.W1.Proofs.T128
import SAP.P001g.WH.W2.Proofs.T121

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

universe u v w z u1 v1

theorem SAP.P001g.T115 : SAP.P001g.T115WholeStatement := SAP.P001g.WH.W1.T115_whole

theorem SAP.P001g.T116 : SAP.P001g.T116Statement.{u, v, w, z, u1, v1} := by
  exact SAP.P001g.Bridge.t116.{u, v, w, z, u1, v1}

theorem SAP.P001g.T117 : SAP.P001g.T117WholeStatement := SAP.P001g.WH.W1.T117_whole

theorem SAP.P001g.T118 : SAP.P001g.T118Statement.{u} := by
  exact SAP.P001g.Bridge.t118.{u}

theorem SAP.P001g.T119 : SAP.P001g.T119Statement := by
  exact SAP.P001g.Bridge.t119

/-- Auxiliary misspecified-model result retained under its existing name.
P001-T120 is omitted from the Challenge: this does not refute its true-model claim. -/
theorem SAP.P001g.T120 : SAP.P001g.T120Statement.{u} := by
  exact SAP.P001g.Bridge.t120.{u}

/-- In a compact two-component, four-outcome mixture with an inactive component, universal full-vector consistency of arbitrary selections among exact likelihood maximizers fails. This refutes the reading allowing tied maximizers; it does not refute the printed assertion under the book's unique-argmax convention. -/
theorem SAP.P001g.T121_tiedAuxiliary : SAP.P001g.T121Statement.{u} := by
  exact SAP.P001g.Bridge.t121.{u}

theorem SAP.P001g.T121 : SAP.P001g.T121WholeStatement.{u} := SAP.P001g.WH.W2.T121_whole

theorem SAP.P001g.T124 : SAP.P001g.T124Statement := by
  exact SAP.P001g.Bridge.t124

theorem SAP.P001g.T125 : SAP.P001g.T125Statement.{u} := by
  exact SAP.P001g.Bridge.t125.{u}

theorem SAP.P001g.T126 : SAP.P001g.T126Statement.{u, v, w} := by
  exact SAP.P001g.Bridge.t126.{u, v, w}

theorem SAP.P001g.T127 : SAP.P001g.T127Statement.{u} := by
  exact SAP.P001g.Bridge.t127.{u}

theorem SAP.P001g.T128 : SAP.P001g.T128Statement.{u} := by
  exact SAP.P001g.Bridge.t128.{u}

theorem SAP.P001g.T129 : SAP.P001g.T129Statement.{u, v} := by
  exact SAP.P001g.Bridge.t129.{u, v}

theorem SAP.P001g.T130 : SAP.P001g.T130Statement.{u} := by
  exact SAP.P001g.Bridge.t130.{u}

