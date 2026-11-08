import SAP.P011b.Defs
import AronowAudit.P011.Wave1.Gap.GLP011B4
import AronowAudit.P011.Wave1.Gap.GLP011B5
import AronowAudit.P011.Wave1.Gap.Fid2P011
import AronowAudit.P011.Wave1.Checks.FidP011Contracts
import AronowAudit.P011.P011_AuxiliaryCompletion
import AronowAudit.P011.P011_CorrelationCompletion
import AronowAudit.P011.P011_BlockOLSCompletion
import AronowAudit.P011.P011_StarCompletion
import AronowAudit.P011.P011_PathFiniteCompletion
import AronowAudit.P011.P011_FiniteCompletion
import AronowAudit.P011.P011_ThreePointCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b.Bridge

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

/-! Structural adapters preserve every model field and every family field.
All later correspondences reduce to these projections and identical bodies. -/

def toModel {n : ℕ} (m : SAP.P011b.Model n) : AronowAudit.P011.Model n where
  law := m.law
  probability := m.probability
  theta := m.theta
  G := m.G
  R := m.R
  d := m.d

def ofModel {n : ℕ} (m : AronowAudit.P011.Model n) : SAP.P011b.Model n where
  law := m.law
  probability := m.probability
  theta := m.theta
  G := m.G
  R := m.R
  d := m.d

def toFamily (F : SAP.P011b.Family) : AronowAudit.P011.Family where
  size := F.size
  positive := F.positive
  grows := F.grows
  model := fun k => toModel (F.model k)

def ofFamily (F : AronowAudit.P011.Family) : SAP.P011b.Family where
  size := F.size
  positive := F.positive
  grows := F.grows
  model := fun k => ofModel (F.model k)

theorem toModel_ofModel {n : ℕ} (m : AronowAudit.P011.Model n) :
    toModel (ofModel m) = m := rfl

theorem ofModel_toModel {n : ℕ} (m : SAP.P011b.Model n) :
    ofModel (toModel m) = m := rfl

theorem toFamily_ofFamily (F : AronowAudit.P011.Family) :
    toFamily (ofFamily F) = F := rfl

theorem ofFamily_toFamily (F : SAP.P011b.Family) :
    ofFamily (toFamily F) = F := rfl

theorem graph_correspondence (n : ℕ) : SAP.P011b.Graph n = AronowAudit.P011.Graph n := rfl

theorem scaling_correspondence (F : Family) (c1 c2 c3 c4 : ℝ) :
    Scaling F c1 c2 c3 c4 ↔ AronowAudit.P011.Scaling (toFamily F) c1 c2 c3 c4 := Iff.rfl

theorem starModel_correspondence (u : Bool) (K : ℕ) :
    toModel (starModel u K) = AronowAudit.P011.starModel u K := rfl

theorem starFamily_correspondence (u : Bool) :
    toFamily (starFamily u) = AronowAudit.P011.starFamily u := rfl

theorem signModel_correspondence (n : ℕ) :
    toModel (signModel n) = AronowAudit.P011.signModel n := rfl

theorem signFamily_correspondence :
    toFamily signFamily = AronowAudit.P011.signFamily := rfl

theorem printedSignAssertion_correspondence :
    printedSignAssertion ↔ AronowAudit.P011.Wave1.FidP011Contracts.printedContract_P011_T20 := by
  constructor
  · intro h F c1 c2 c3 c4 hs hv hh ε he
    exact h (ofFamily F) c1 c2 c3 c4 hs hv hh ε he
  · intro h F c1 c2 c3 c4 hs hv hh ε he
    exact h (toFamily F) c1 c2 c3 c4 hs hv hh ε he

end
end SAP.P011b.Bridge
