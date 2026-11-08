import SAP.P037a.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.Bridge

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

/-- The adapter changes only the bundled type; every data field is preserved. -/
def toRow {B : ℕ} (r : RetainedRow B) : AronowAudit.P037.RetainedBlockRow B where
  students := r.students
  assignments := r.assignments
  law := fun b => toDesign (r.law b)
  exposed := r.exposed
  y := r.y
  g := r.g
  pi := r.pi
  pi_def := r.pi_def
  pi_pos := r.pi_pos

def toPaired {B : ℕ} (r : RetainedRow B) (s : PairedExposure r) :
    AronowAudit.P037.SecondRowExposure (toRow r) where
  exposed := s.exposed
  y := s.y
  g := s.g
  pi := s.pi
  pi_def := s.pi_def
  pi_pos := s.pi_pos

theorem populationSize_eq {B : ℕ} (r : RetainedRow B) :
    populationSize r = AronowAudit.P037.retainedSize (toRow r) := rfl

theorem blockTotal_eq {B : ℕ} (r : RetainedRow B) :
    blockTotal r = AronowAudit.P037.oracleBlockTotal (toRow r) := rfl

theorem oracleMean_eq {B : ℕ} (r : RetainedRow B) :
    oracleMean r = AronowAudit.P037.oracleRowMean (toRow r) := rfl

theorem potentialMean_eq {B : ℕ} (r : RetainedRow B) :
    potentialMean r = AronowAudit.P037.retainedPotentialMean (toRow r) := rfl

theorem totalBlockVariance_eq {B : ℕ} (r : RetainedRow B) :
    totalBlockVariance r = AronowAudit.P037.rowTotalVariance (toRow r) := rfl

theorem rowProbability_eq {B : ℕ} (r : RetainedRow B) (E : RowAssignment r → Prop) :
    rowProbability r E = AronowAudit.P037.blockRowProbability (toRow r) E := rfl

theorem blockBounds_iff (r : ∀ B, RetainedRow (B+1)) (m : ℕ) (c eta K : ℝ) :
    BlockBounds r m c eta K ↔
      AronowAudit.P037.UniformBlockBounds (fun B => toRow (r B)) m c eta K := Iff.rfl

theorem contrastBlockTotal_eq {B : ℕ} (r : RetainedRow B) (s : PairedExposure r) :
    contrastBlockTotal r s = AronowAudit.P037.oracleContrastBlock (toRow r) (toPaired r s) := rfl

theorem populationContrast_eq {B : ℕ} (r : RetainedRow B) (s : PairedExposure r) :
    populationContrast r s = AronowAudit.P037.retainedContrast (toRow r) (toPaired r s) := rfl

theorem oracleContrast_eq {B : ℕ} (r : RetainedRow B) (s : PairedExposure r) :
    oracleContrast r s = AronowAudit.P037.oracleRowContrast (toRow r) (toPaired r s) := rfl

theorem fittedMean_eq {B q : ℕ} (r : RetainedRow B) (x : Covariates r q)
    (beta : Fin q → ℝ) (p : (b : Fin B) → Fin (r.students b) → ℝ) :
    fittedMean r x beta p = AronowAudit.P037.fittedRowMean (toRow r) x beta p := rfl

theorem fittedCoefficient_eq {B q : ℕ} (r : RetainedRow B) (x : Covariates r q)
    (p : (b : Fin B) → Fin (r.students b) → ℝ) :
    fittedCoefficient r x p = AronowAudit.P037.fittedRowCoefficient (toRow r) x p := rfl

theorem covariateGram_eq {B q : ℕ} (r : RetainedRow B) (x : Covariates r q) :
    covariateGram r x = AronowAudit.P037.populationRowGram (toRow r) x := rfl

theorem covariateRhs_eq {B q : ℕ} (r : RetainedRow B) (x : Covariates r q) :
    covariateRhs r x = AronowAudit.P037.populationRowRhs (toRow r) x := rfl

end SAP.P037a.Bridge
