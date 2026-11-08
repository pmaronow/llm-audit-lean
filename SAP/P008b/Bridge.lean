import SAP.P008b.Defs
import AronowAudit.P008.P008_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b.Bridge

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- Transfer the three finite-law fields without changing any data. -/
def law {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) :
    AronowAudit.P008.FiniteLaw Ω where
  mass := Q.mass
  nonneg := Q.nonneg
  total := Q.total

/-- Transfer the spatial field, node coordinates, measure and potential outcomes. -/
def model {N : ℕ} (P : SpatialModel N) : AronowAudit.P008.SpatialModel N where
  field := P.field
  node := P.node
  node_mem := P.node_mem
  ζ := P.ζ
  Y := P.Y

theorem expect_eq {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f : Ω → ℝ) :
    (law Q).expect f = Q.expect f := rfl

theorem prob_eq {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (P : Ω → Prop) :
    (law Q).prob P = Q.prob P := rfl

theorem covariance_eq {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f g : Ω → ℝ) :
    (law Q).cov f g = Q.cov f g := rfl

theorem variance_eq {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f : Ω → ℝ) :
    (law Q).var f = Q.var f := rfl

theorem uniform_eq (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    law (uniformLaw Ω) = AronowAudit.P008.uniformLaw Ω := rfl

theorem marginal_eq {N : ℕ} (Q : FiniteLaw (Assignment N))
    (f : Assignment N → ℝ) (i : Fin N) (b : Bool) :
    AronowAudit.P008.marginal (law Q) f i b = marginal Q f i b := rfl

theorem circle_eq {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) :
    (model P).circle i d = P.circle i d := rfl

theorem circleMeasure_eq {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) :
    (model P).circleMeasure i d = P.circleMeasure i d := rfl

theorem circleMass_eq {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) :
    (model P).circleMass i d = P.circleMass i d := rfl

theorem average_eq {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) (f : Plane → ℝ) :
    (model P).average i d f = P.average i d f := rfl

theorem circleOutcome_eq {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ)
    (z : Assignment N) : (model P).M i d z = P.M i d z := rfl

theorem marginalOutcome_eq {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (b : Bool) (x : Plane) :
    (model P).marginalY (law Q) i b x = P.marginalY Q i b x := rfl

theorem pointEffect_eq {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (x : Plane) :
    (model P).pointEffect (law Q) i x = P.pointEffect Q i x := rfl

theorem marginalCircle_eq {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (b : Bool) (d : ℝ) :
    (model P).m (law Q) i b d = P.m Q i b d := rfl

theorem nodeEffect_eq {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (d : ℝ) :
    (model P).nodeEffect (law Q) i d = P.nodeEffect Q i d := rfl

theorem amr_eq {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (d : ℝ) :
    (model P).amr (law Q) d = P.amr Q d := rfl

theorem band_eq {N : ℕ} (P : SpatialModel N) (i : Fin N) (d k : ℝ) :
    (model P).band i d k = P.band i d k := rfl

theorem bandAverage_eq {N : ℕ} (P : SpatialModel N) (i : Fin N) (d k : ℝ)
    (f : Plane → ℝ) : (model P).bandAverage i d k f = P.bandAverage i d k f := rfl

theorem sharpNull_eq {N : ℕ} (P : SpatialModel N) :
    (model P).sharpNull ↔ P.sharpNull := Iff.rfl

theorem countMean_eq : @SAP.P008b.countMean = @AronowAudit.P008.countMean := rfl

theorem additiveOutcome_eq : @SAP.P008b.additiveOutcome =
    @AronowAudit.P008.additiveOutcome := rfl

theorem hajek_eq : @SAP.P008b.hajek = @AronowAudit.P008.hajek := rfl

theorem commonBernoulli_eq {N : ℕ} (Q : FiniteLaw (Assignment N)) (p : ℝ) :
    AronowAudit.P008.commonBernoulli (law Q) p ↔ commonBernoulli Q p := Iff.rfl

theorem dependency_eq {N : ℕ} (Q : FiniteLaw (Assignment N))
    (M : Fin N → Assignment N → ℝ) (D : ℕ) :
    AronowAudit.P008.boundedPairDependency (law Q) M D ↔
      boundedPairDependency Q M D := Iff.rfl

theorem finiteAMR_eq {N : ℕ} (Q : FiniteLaw (Assignment N))
    (M : Fin N → Assignment N → ℝ) :
    AronowAudit.P008.finiteAMR (law Q) M = finiteAMR Q M := rfl

theorem completedHajek_eq : @SAP.P008b.completedHajek =
    @AronowAudit.P008.completedHajek := rfl

theorem toyRasterAMR_eq {C : ℕ} (Q : FiniteLaw (Assignment 4))
    (a : ℝ) (base : Fin C → ℝ) (r w : Fin 4 → Fin C → ℝ) :
    AronowAudit.P008.toyRasterAMR (law Q) a base r w =
      toyRasterAMR Q a base r w := rfl

theorem donutGeometry_eq : @SAP.P008b.donutSpatialDistance =
    @AronowAudit.P008.donutSpatialDistance := rfl

theorem donutMeans_eq : @SAP.P008b.donutSpatialMeans =
    @AronowAudit.P008.donutSpatialMeans := rfl

theorem rasterEdge_eq : @SAP.P008b.polygonRasterEdgeM =
    @AronowAudit.P008.polygonRasterEdgeM := rfl

theorem rasterArea_eq : @SAP.P008b.polygonRasterAreaM =
    @AronowAudit.P008.polygonRasterAreaM := rfl

theorem rasterBoundary_eq : @SAP.P008b.rasterBoundary =
    @AronowAudit.P008.rasterBoundary := rfl

theorem lineMean_eq : @SAP.P008b.realLineM = @AronowAudit.P008.realLineM := rfl

end

end SAP.P008b.Bridge
