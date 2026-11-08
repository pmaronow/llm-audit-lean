import SAP.P037b.WH.W2.Proofs.T22
import SAP.P037b.WH.W1.Proofs.T29
import SAP.P037b.Defs
import SAP.P037b.Bridge
import AronowAudit.P037.P037_Design
import AronowAudit.P037.P037_Inference
import AronowAudit.P037.P037_Network
import AronowAudit.P037.P037_Sample
import AronowAudit.P037.Wave1.Gap.GLP037B2
import AronowAudit.P037.Wave1.Gap.GP037B1
import AronowAudit.P037.Wave1.Gap.GP037B2
import AronowAudit.P037.Wave1.Gap.GP037B3
import AronowAudit.P037.Wave1.Gap.GP037B4

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem SAP.P037b.T18 : SAP.P037b.T18Statement :=
  SAP.P037b.Bridge.T18_correspondence

theorem SAP.P037b.T23 : SAP.P037b.T23Statement :=
  SAP.P037b.Bridge.T23_correspondence

theorem SAP.P037b.T24 : SAP.P037b.T24Statement :=
  SAP.P037b.Bridge.T24_correspondence

theorem SAP.P037b.T19 : SAP.P037b.T19Statement :=
  SAP.P037b.Bridge.T19_correspondence

theorem SAP.P037b.T20 : SAP.P037b.T20Statement :=
  SAP.P037b.Bridge.T20_correspondence

theorem SAP.P037b.T21 : SAP.P037b.T21Statement :=
  SAP.P037b.Bridge.T21_correspondence

theorem SAP.P037b.T22 : SAP.P037b.T22WholeStatement_W2 :=
  SAP.P037b.WH.W2.T22_whole

theorem SAP.P037b.T29 : SAP.P037b.T29WholeStatement :=
  SAP.P037b.WH.W1.T29_whole

theorem SAP.P037b.T30 : SAP.P037b.T30Statement :=
  SAP.P037b.Bridge.T30_correspondence

theorem SAP.P037b.T31 : SAP.P037b.T31Statement :=
  SAP.P037b.Bridge.T31_correspondence

theorem SAP.P037b.T32 : SAP.P037b.T32Statement :=
  SAP.P037b.Bridge.T32_correspondence

theorem SAP.P037b.T25 : SAP.P037b.T25Statement :=
  SAP.P037b.Bridge.T25_correspondence

theorem SAP.P037b.T26 : SAP.P037b.T26Statement :=
  SAP.P037b.Bridge.T26_correspondence
