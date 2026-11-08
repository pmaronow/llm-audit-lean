import SAP.P009b.Defs
import AronowAudit.P009.P009_AtomCompletion
import AronowAudit.P009.P009_Audit
import AronowAudit.P009.P009_BernoulliCompletion
import AronowAudit.P009.P009_FullBiasCompletion
import AronowAudit.P009.P009_MinimizerCompletion
import AronowAudit.P009.P009_OneSourceCompletion
import AronowAudit.P009.P009_PairedCompletion
import AronowAudit.P009.P009_PaperDomains
import AronowAudit.P009.Wave1.Gap.GLP0091B4
import AronowAudit.P009.Wave1.Gap.GLP0091B5
import AronowAudit.P009.Wave1.Gap.GP0091B1b
import AronowAudit.P009.Wave1.SimulationVarianceTailC

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Bridge

def toLaw {Ω : Type*} [Fintype Ω] (P : Law Ω) : AronowAudit.P009.Law Ω :=
  ⟨P.mass, P.nonneg, P.total⟩

def toExperiment {n : ℕ} (E : Experiment n) : AronowAudit.P009.Experiment n :=
  ⟨toLaw E.design, E.outcome⟩

def toPairing {n : ℕ} (ρ : Pairing n) : AronowAudit.P009.Pairing n :=
  ⟨ρ.partner, ρ.involution, ρ.no_fixed⟩

def toStudy (S : Study) : AronowAudit.P009.Study :=
  ⟨S.N, S.positive, S.grows, fun t => toExperiment (S.experiment t)⟩

theorem mean_correspondence {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) :
    mean P X = AronowAudit.P009.mean (toLaw P) X := rfl

theorem potential_correspondence {n : ℕ} (E : Experiment n) (i : Fin n)
    (b : Bool) (z : Assignment n) :
    potential E i b z = AronowAudit.P009.potential (toExperiment E) i b z := rfl

theorem to_design {n : ℕ} (E : Experiment n)
    (hDesign : Complete E (n/2) ∨ ∃ ρ : Pairing n, Paired E ρ) :
    AronowAudit.P009.Complete (toExperiment E) (n/2) ∨
      ∃ ρ : AronowAudit.P009.Pairing n, AronowAudit.P009.Paired (toExperiment E) ρ := by
  rcases hDesign with h | ⟨ρ, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨toPairing ρ, h⟩


theorem T18Core_transport (h : type_of% @AronowAudit.P009.Wave1.corrected_hypergeometric_proof) :
    T18CoreStatement := by
  intro n E m hCR i hc
  exact h (toExperiment E) m hCR i hc

theorem T19Core_transport (h : type_of% @AronowAudit.P009.pair_witness_counterexample) :
    T19CoreStatement := by
  exact h

theorem T20Core_transport (h : type_of% @AronowAudit.P009.corrected_pair_dependence) :
    T20CoreStatement := by
  intro n hn E ρ
  exact h hn (toExperiment E) (toPairing ρ)

theorem T22Finite_transport (h : type_of% @AronowAudit.P009.Wave1.corrected_one_source_formulas_proof) :
    T22FiniteStatement := by
  exact h

theorem T22Limit_transport (h : type_of% @AronowAudit.P009.Wave1.corrected_one_source_limit_proof) :
    T22LimitStatement := by
  intro S k q s hReg hQ b hb c hSource hLaw hOutcome
  apply h (toStudy S) k q s hReg hQ b hb c hSource _ hOutcome
  intro t
  exact congrArg toLaw (hLaw t)

theorem T23Core_transport (h : type_of% @AronowAudit.P009.Wave1.simulation_sampling_variance_proof) :
    T23CoreStatement := by
  intro n hn heven P hCR ρ hRank Q hPair _hIntegrable
  exact h hn heven (toLaw P) hCR (fun x => toPairing (ρ x)) hRank
    (fun x => toLaw (Q x)) hPair

theorem T24Core_transport (h : type_of% @AronowAudit.P009.full_interference_bias) :
    T24CoreStatement := by
  intro n hn heven E b hy hDesign
  exact h hn heven (toExperiment E) b hy (to_design E hDesign)

theorem T25Caption_transport (h : type_of% @AronowAudit.P009.absolute_bias_caption) :
    T25CaptionStatement := by
  intro R hR estimates
  have hconstants := (h R hR estimates).2.2
  exact ⟨abs_nonneg _, rfl, hconstants⟩

theorem T25Population_transport (h : type_of% @AronowAudit.P009.absolute_bias_population) :
    T25PopulationStatement := by
  intro n hn heven E b hy hDesign
  exact h hn heven (toExperiment E) b hy (to_design E hDesign)

theorem T26Core_transport (h : type_of% @AronowAudit.P009.PaperDomains.common_assignment_mixing) :
    T26CoreStatement := by
  intro S p hp hNo hCommon
  exact h (toStudy S) p hp hNo hCommon

theorem T27Atoms_transport (h : type_of% @AronowAudit.P009.bernoulli_atom_bounds) :
    T27AtomsStatement := by
  intro n E k q s hReg hBER G a
  exact h (toExperiment E) k q s hReg hBER G a

theorem T27Approximation_transport (h : type_of% @AronowAudit.P009.three_point_atom_approximation.{u}) :
    T27ApproximationStatement.{u} := by
  intro Ω inst P δ α hδ hα
  exact h (toLaw P) δ α hδ hα

end Bridge

end
end SAP.P009b
