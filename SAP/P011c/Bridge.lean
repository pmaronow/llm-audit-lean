import SAP.P011c.Defs
import AronowAudit.P011.P011_Audit
import AronowAudit.P011.P011_Review

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011c.Bridge

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-- Field-for-field conversion of the independent SAP model data. -/
def toModel {n : ℕ} (m : SAP.P011c.Model n) : AronowAudit.P011.Model n where
  law := m.law
  probability := m.probability
  theta := m.theta
  G := m.G
  R := m.R
  d := m.d

def fromModel {n : ℕ} (m : AronowAudit.P011.Model n) : SAP.P011c.Model n where
  law := m.law
  probability := m.probability
  theta := m.theta
  G := m.G
  R := m.R
  d := m.d

theorem to_from_model {n : ℕ} (m : AronowAudit.P011.Model n) :
    toModel (fromModel m) = m := rfl

theorem from_to_model {n : ℕ} (m : SAP.P011c.Model n) :
    fromModel (toModel m) = m := rfl

/-- Rowwise conversion keeps sample sizes, laws, and all fixed data. -/
def toFamily (F : SAP.P011c.Family) : AronowAudit.P011.Family where
  size := F.size
  positive := F.positive
  grows := F.grows
  model := fun k => toModel (F.model k)

def fromFamily (F : AronowAudit.P011.Family) : SAP.P011c.Family where
  size := F.size
  positive := F.positive
  grows := F.grows
  model := fun k => fromModel (F.model k)

theorem to_from_family (F : AronowAudit.P011.Family) : toFamily (fromFamily F) = F := rfl

theorem from_to_family (F : SAP.P011c.Family) : fromFamily (toFamily F) = F := rfl

theorem graph_eq : SAP.P011c.Graph = AronowAudit.P011.Graph := rfl

theorem adjacency_eq : @SAP.P011c.adjacency = @AronowAudit.P011.adjacency := rfl

theorem degree_eq : @SAP.P011c.degree = @AronowAudit.P011.degree := rfl

theorem compatible_eq : @SAP.P011c.Compatible = @AronowAudit.P011.Compatible := rfl

theorem maximizes_eq : @SAP.P011c.Maximizes = @AronowAudit.P011.Maximizes := rfl

theorem V1_eq : @SAP.P011c.V1 = @AronowAudit.P011.V1 := rfl

theorem V2_eq : @SAP.P011c.V2 = @AronowAudit.P011.V2 := rfl

theorem V2prime_eq : @SAP.P011c.V2prime = @AronowAudit.P011.V2prime := rfl

theorem weighted_eq {n : ℕ} (m : SAP.P011c.Model n) :
    SAP.P011c.weighted m = AronowAudit.P011.weighted (toModel m) := rfl

theorem betaHat_eq {n : ℕ} (m : SAP.P011c.Model n) :
    SAP.P011c.betaHat m = AronowAudit.P011.betaHat (toModel m) := rfl

theorem beta_eq {n : ℕ} (m : SAP.P011c.Model n) :
    SAP.P011c.beta m = AronowAudit.P011.beta (toModel m) := rfl

theorem variance_eq {n : ℕ} (m : SAP.P011c.Model n) (f : (Fin n → ℝ) → ℝ) :
    SAP.P011c.var m f = AronowAudit.P011.var (toModel m) f := rfl

theorem meanModel_iff {n p : ℕ} (m : SAP.P011c.Model n)
    (D : Matrix (Fin n) (Fin p) ℝ) (b : Fin p → ℝ) :
    SAP.P011c.MeanModel m D b ↔ AronowAudit.P011.MeanModel (toModel m) D b := Iff.rfl

theorem scaling_iff (F : SAP.P011c.Family) (c1 c2 c3 c4 : ℝ) :
    SAP.P011c.Scaling F c1 c2 c3 c4 ↔
      AronowAudit.P011.Scaling (toFamily F) c1 c2 c3 c4 := Iff.rfl

theorem valid_iff (F : SAP.P011c.Family) :
    SAP.P011c.Valid F ↔ AronowAudit.P011.Valid (toFamily F) := Iff.rfl

theorem homoskedastic_iff {n : ℕ} (m : SAP.P011c.Model n) :
    SAP.P011c.Homoskedastic m ↔ AronowAudit.P011.Homoskedastic (toModel m) := Iff.rfl

theorem inProbability_iff (F : SAP.P011c.Family)
    (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (a : ℕ → ℝ) :
    SAP.P011c.InProbability F T a ↔ AronowAudit.P011.InProbability (toFamily F) T a :=
  Iff.rfl

theorem conservative_iff (F : SAP.P011c.Family)
    (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) :
    SAP.P011c.Conservative F V ↔ AronowAudit.P011.Conservative (toFamily F) V := Iff.rfl

theorem coverage_eq {n : ℕ} (m : SAP.P011c.Model n)
    (V : (Fin n → ℝ) → ℝ) (α : ℝ) :
    SAP.P011c.coverage m V α = AronowAudit.P011.coverage (toModel m) V α := rfl

theorem printedCoverage_eq {n : ℕ} (m : SAP.P011c.Model n)
    (V : (Fin n → ℝ) → ℝ) (α : ℝ) :
    SAP.P011c.printedCoverage m V α =
      AronowAudit.P011.printedCoverage (toModel m) V α := rfl

theorem standardized_eq {n : ℕ} (m : SAP.P011c.Model n) :
    SAP.P011c.standardized m = AronowAudit.P011.standardized (toModel m) := rfl

theorem capacityMatrix_eq : @SAP.P011c.recruitmentCapacityMatrix =
    @AronowAudit.P011.recruitmentCapacityMatrix := rfl

theorem psd_eq : @SAP.P011c.PSD = @AronowAudit.P011.PSD := rfl

/-- The feasibility row ignores rational weights; empirical profits remain real-valued. -/
def toDegreeProblem {n : ℕ} (forced : Finset (Edge n)) (d : Fin n → ℕ) :
    AronowAudit.P011.DegreeProblem n where
  forced := forced
  cap := d
  weight := fun _ => 0

theorem incidenceFeasible_iff {n : ℕ} (forced : Finset (Edge n)) (d : Fin n → ℕ)
    (S : Finset (Edge n)) :
    IncidenceFeasible forced d S ↔ DegreeFeasible forced d S :=
  AronowAudit.P011.knapsack_encoding (toDegreeProblem forced d) S

/-- Transport the coverage event using the existing everywhere-nonnegative comparison. -/
theorem printedCoverage_iff (F : SAP.P011c.Family)
    (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (hV : ∀ k y, 0 ≤ V k y) :
    PrintedConservativeCoverage F V ↔ ConservativeCoverage F V := by
  have he (k : ℕ) (α : ℝ) :
      printedCoverage (F.model k) (V k) α = coverage (F.model k) (V k) α :=
    AronowAudit.P011.printed_coverage_eq_of_nonnegative (toModel (F.model k))
      (V k) (hV k) α
  constructor <;> intro h α hα hα1 <;> simpa only [he] using h α hα hα1

end
end SAP.P011c.Bridge
