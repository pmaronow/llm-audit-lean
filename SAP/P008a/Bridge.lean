import SAP.P008a.Defs
import AronowAudit.P008.P008_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008a.Bridge

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

/-- Preserve the mass function and its two probability certificates. -/
def toLaw {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) : AronowAudit.P008.FiniteLaw Ω :=
  ⟨Q.mass, Q.nonneg, Q.total⟩

/-- Preserve the field, nodes, measure, and complete outcome schedule. -/
def toModel {N : ℕ} (P : SpatialModel N) : AronowAudit.P008.SpatialModel N :=
  ⟨P.field, P.node, P.node_mem, P.ζ, P.Y⟩

theorem mass_eq {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) :
    (toLaw Q).mass = Q.mass := rfl

theorem expect_eq {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f : Ω → ℝ) :
    (toLaw Q).expect f = Q.expect f := rfl

theorem prob_eq {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (A : Ω → Prop) :
    (toLaw Q).prob A = Q.prob A := rfl

theorem cov_eq {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f g : Ω → ℝ) :
    (toLaw Q).cov f g = Q.cov f g := rfl

theorem var_eq {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f : Ω → ℝ) :
    (toLaw Q).var f = Q.var f := rfl

theorem uniform_eq (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    toLaw (uniformLaw Ω) = AronowAudit.P008.uniformLaw Ω := rfl

theorem conditional_eq {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (A : Ω → Prop) (hA : 0 < Q.prob A) :
    toLaw (conditionalLaw Q A hA) = AronowAudit.P008.conditionalLaw (toLaw Q) A hA := rfl

theorem tail_eq {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (T : Ω → ℝ) (z : Ω) :
    AronowAudit.P008.tailP (toLaw Q) T z = tailP Q T z := rfl

theorem bernoulli_eq {N : ℕ} (Q : FiniteLaw (Assignment N)) (p : ℝ) :
    AronowAudit.P008.commonBernoulli (toLaw Q) p ↔ commonBernoulli Q p := Iff.rfl

theorem circle_eq {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) :
    (toModel P).circle i d = P.circle i d := rfl

theorem circle_measure_eq {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) :
    (toModel P).circleMeasure i d = P.circleMeasure i d := rfl

theorem circle_mass_eq {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) :
    (toModel P).circleMass i d = P.circleMass i d := rfl

theorem average_eq {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) (f : Plane → ℝ) :
    (toModel P).average i d f = P.average i d f := rfl

theorem circle_outcome_eq {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ)
    (z : Assignment N) : (toModel P).M i d z = P.M i d z := rfl

theorem marginal_eq {N : ℕ} (P : SpatialModel N) (Q : FiniteLaw (Assignment N))
    (i : Fin N) (b : Bool) (d : ℝ) : (toModel P).m (toLaw Q) i b d = P.m Q i b d := rfl

theorem amr_eq {N : ℕ} (P : SpatialModel N) (Q : FiniteLaw (Assignment N)) (d : ℝ) :
    (toModel P).amr (toLaw Q) d = P.amr Q d := rfl

theorem risk_eq {N : ℕ} (P : SpatialModel N) (Q : FiniteLaw (Assignment N)) (b : Bool) (d : ℝ) :
    (toModel P).risk (toLaw Q) b d = P.risk Q b d := rfl

theorem rectangle_eq : toModel validatorRectangleModel = AronowAudit.P008.validatorRectangleModel := rfl

theorem bandwidth_model_eq : toModel bandwidthSpatialModel = AronowAudit.P008.bandwidthSpatialModel := rfl

/-- The finite rational-coordinate circles use the ordinary Euclidean distance. -/
theorem line_distance (x y : ℚ) :
    dist (lineEmbedding x) (lineEmbedding y) = ((|x - y| : ℚ) : ℝ) :=
  AronowAudit.P008.line_embedding_distance x y

end
end SAP.P008a.Bridge
