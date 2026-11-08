import SAP.P020.Defs
import AronowAudit.P020.P020_Design
import AronowAudit.P020.P020_Logistic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P020.Bridge
open SAP.P020
noncomputable section

/-- Preserve the finite support, probabilities, and both validity certificates. -/
def toLaw {Ω : Type*} (L : FiniteLaw Ω) : AronowAudit.P020.FiniteLaw Ω :=
  ⟨L.support, L.weight, L.nonneg, L.total⟩

/-- Preserve cluster counts, sizes, potential totals, and their validity fields. -/
def toPopulation (P : ClusterPopulation) : AronowAudit.P020.ClusterPopulation :=
  ⟨P.M, P.mt, P.mt_pos, P.mt_lt, P.n, P.n_pos, P.y0, P.y1⟩

/-- Preserve individual outcomes and their two aggregation certificates. -/
def toIndividuals {P : ClusterPopulation} (I : IndividualPotentialOutcomes P) :
    AronowAudit.P020.IndividualPotentialOutcomes (toPopulation P) :=
  ⟨I.Y0, I.Y1, I.total0, I.total1⟩

theorem expectation_eq {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) :
    AronowAudit.P020.expectation (toLaw L) T = expectation L T := rfl

theorem variance_eq {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) :
    AronowAudit.P020.designVariance (toLaw L) T = designVariance L T := rfl

theorem mse_eq {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (d : ℝ) :
    AronowAudit.P020.meanSquaredError (toLaw L) T d = meanSquaredError L T d := rfl

theorem clusterLaw_eq (P : ClusterPopulation) :
    AronowAudit.P020.clusterLaw (toPopulation P) = toLaw (clusterLaw P) := rfl

theorem differenceInMeans_eq (P : ClusterPopulation) :
    AronowAudit.P020.differenceInMeans (toPopulation P) = differenceInMeans P := rfl

theorem horvitzThompson_eq (P : ClusterPopulation) :
    AronowAudit.P020.horvitzThompson (toPopulation P) = horvitzThompson P := rfl

theorem desRaj_eq (P : ClusterPopulation) (k : ℝ) :
    AronowAudit.P020.desRaj (toPopulation P) k = desRaj P k := rfl

theorem individualNull_eq {P : ClusterPopulation} (I : IndividualPotentialOutcomes P) :
    AronowAudit.P020.IndividualSharpNull (toIndividuals I) ↔ IndividualSharpNull I := Iff.rfl

theorem affine_eq (P : ClusterPopulation) (b0 b1 : ℝ) :
    AronowAudit.P020.affinePopulation (toPopulation P) b0 b1 =
      toPopulation (affinePopulation P b0 b1) := rfl

theorem replicate_eq (P : ClusterPopulation) (h : ℕ) (hh : 0 < h) :
    AronowAudit.P020.replicateWithin (toPopulation P) h hh =
      toPopulation (replicateWithin P h hh) := rfl

theorem blockLaw_eq {B : ℕ} (P : Fin B → ClusterPopulation) :
    AronowAudit.P020.blockLaw (fun b => toPopulation (P b)) = toLaw (blockLaw P) := rfl

theorem copyLaw_eq (P : ClusterPopulation) (h : ℕ) :
    AronowAudit.P020.copyLaw (toPopulation P) h = toLaw (copyLaw P h) := rfl

theorem efficiency_eq :
    AronowAudit.P020.efficiencyPopulation = toPopulation efficiencyPopulation := rfl

theorem slope_eq :
    AronowAudit.P020.slopePopulation = toPopulation slopePopulation := rfl

theorem subscript_eq :
    AronowAudit.P020.subscriptPopulation = toPopulation subscriptPopulation := rfl

theorem bracket_eq :
    AronowAudit.P020.bracketPopulation = toPopulation bracketPopulation := rfl

theorem logistic_eq : AronowAudit.P020.logistic = logistic := rfl

theorem repairedContrast_eq : AronowAudit.P020.repairedContrast = repairedContrast := rfl

/-- Discarding the zero index is transport of the existing probability limits. -/
theorem consistent_succ {Ω : ℕ → Type*} (L : ∀ h, FiniteLaw (Ω h))
    (T : ∀ h, Ω h → ℝ) (d : ℕ → ℝ) (hc : DesignConsistent L T d) :
    DesignConsistent (fun h => L (h + 1)) (fun h => T (h + 1)) (fun h => d (h + 1)) := by
  intro ε hε
  exact (hc ε hε).comp (Filter.tendsto_add_atTop_nat 1)

/-- The assignment law, estimates and target are unchanged by positive replication. -/
theorem withinReplication_consistency_iff (P : ClusterPopulation) :
    WithinReplicationConsistent P ↔
      DesignConsistent (fun _ : ℕ => clusterLaw P) (fun _ => differenceInMeans P)
        (fun _ => averageTreatmentEffect P) := by
  have hdm (h : ℕ) : differenceInMeans (replicateWithin P (h + 1) (Nat.succ_pos h)) =
      differenceInMeans P := by
    funext s
    exact (AronowAudit.P020.within_replication_invariant (toPopulation P)
      (h + 1) (Nat.succ_pos h) s 0).2.1
  have hate (h : ℕ) : averageTreatmentEffect (replicateWithin P (h + 1) (Nat.succ_pos h)) =
      averageTreatmentEffect P :=
    (AronowAudit.P020.within_replication_invariant (toPopulation P)
      (h + 1) (Nat.succ_pos h) ∅ 0).1
  simp only [WithinReplicationConsistent, DesignConsistent, hdm, hate]
  rfl

end
end SAP.P020.Bridge
