import SAP.P001f.WH.W1.Proofs.T97
import SAP.P001f.WH.W1.Proofs.T101
import SAP.P001f.WH.W1.Proofs.T107
import SAP.P001f.WH.W1.Proofs.T108
import SAP.P001f.WH.W1.Proofs.T111
import SAP.P001f.WH.W2.Proofs.T113
import SAP.P001f.WH.W2.Proofs.T114
import SAP.P001f.Defs
import SAP.P001f.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P001f
universe u v

theorem SAP.P001f.T96 : T96Statement := by
  exact SAP.P001f.Bridge.transportT96

theorem SAP.P001f.T97 : SAP.P001f.T97WholeStatement := SAP.P001f.WH.W1.T97_whole

theorem SAP.P001f.T98 : T98Statement.{u, v} := by
  exact SAP.P001f.Bridge.transportT98

theorem SAP.P001f.T99 : T99Statement := by
  exact SAP.P001f.Bridge.transportT99

theorem SAP.P001f.T100 : T100Statement.{u, v} := by
  exact SAP.P001f.Bridge.transportT100

theorem SAP.P001f.T101 : SAP.P001f.T101WholeStatement := SAP.P001f.WH.W1.T101_whole

theorem SAP.P001f.T102 : T102Statement.{u} := by
  exact SAP.P001f.Bridge.transportT102

theorem SAP.P001f.T103 : T103Statement := by
  exact SAP.P001f.Bridge.transportT103

theorem SAP.P001f.T104 : T104Statement := by
  exact SAP.P001f.Bridge.transportT104

theorem SAP.P001f.T106 : T106Statement.{u} := by
  exact SAP.P001f.Bridge.transportT106

theorem SAP.P001f.T107 : SAP.P001f.T107WholeStatement := SAP.P001f.WH.W1.T107_whole

theorem SAP.P001f.T108 : SAP.P001f.T108WholeStatement := SAP.P001f.WH.W1.T108_whole

theorem SAP.P001f.T109 : T109Statement.{u} := by
  exact SAP.P001f.Bridge.transportT109

theorem SAP.P001f.T110 : T110Statement := by
  exact SAP.P001f.Bridge.transportT110

theorem SAP.P001f.T111 : SAP.P001f.T111WholeStatement := SAP.P001f.WH.W1.T111_whole

theorem SAP.P001f.T112 : T112Statement.{u} := by
  exact SAP.P001f.Bridge.transportT112

theorem SAP.P001f.T113 : SAP.P001f.T113WholeStatement := SAP.P001f.WH.W2.T113_whole

theorem SAP.P001f.T114 : SAP.P001f.T114WholeStatement := SAP.P001f.WH.W2.T114_whole
