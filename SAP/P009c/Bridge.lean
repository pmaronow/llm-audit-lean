import SAP.P009c.Defs
import AronowAudit.P009.P009_TransportCompletion
import AronowAudit.P009.P009_PairedCompletion
import AronowAudit.P009.P009_NormalCompletion
import AronowAudit.P009.Wave1.Gap.DecideP009
import AronowAudit.P009.Wave1.Gap.GP0091B1b
import AronowAudit.P009.Wave1.Gap.GP0091B2b
import AronowAudit.P009.Wave1.Gap.GP0092B1
import AronowAudit.P009.Wave1.Gap.GP0092B2
import AronowAudit.P009.Wave1.Gap.GLP0092B3
import AronowAudit.P009.Wave1.Gap.GLP0092B4
import AronowAudit.P009.Wave1.Gap.GLP0091B9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009c.Bridge
open SAP.P009c Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Preserve the mass function and both probability certificates. -/
def toLaw {Ω : Type*} [Fintype Ω] (P : Law Ω) : AronowAudit.P009.Law Ω :=
  ⟨P.mass, P.nonneg, P.total⟩

def fromLaw {Ω : Type*} [Fintype Ω] (P : AronowAudit.P009.Law Ω) : Law Ω :=
  ⟨P.mass, P.nonneg, P.total⟩

theorem fromLaw_toLaw {Ω : Type*} [Fintype Ω] (P : Law Ω) :
    fromLaw (toLaw P) = P := rfl

theorem toLaw_fromLaw {Ω : Type*} [Fintype Ω] (P : AronowAudit.P009.Law Ω) :
    toLaw (fromLaw P) = P := rfl

/-- No assignment, design mass, or full-cube outcome changes. -/
def toExperiment {n : ℕ} (E : Experiment n) : AronowAudit.P009.Experiment n :=
  ⟨toLaw E.design, E.outcome⟩

def toPairing {n : ℕ} (ρ : Pairing n) : AronowAudit.P009.Pairing n :=
  ⟨ρ.partner, ρ.involution, ρ.no_fixed⟩

/-- Preserve population sizes, their growth, and every experiment. -/
def toStudy (S : Study) : AronowAudit.P009.Study :=
  ⟨S.N, S.positive, S.grows, fun t => toExperiment (S.experiment t)⟩

theorem mean_toLaw {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) :
    AronowAudit.P009.mean (toLaw P) X = mean P X := rfl

theorem prob_toLaw {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω → Prop) :
    AronowAudit.P009.prob (toLaw P) A = prob P A := rfl

theorem eate_toExperiment {n : ℕ} (E : Experiment n) :
    AronowAudit.P009.eate (toExperiment E) = eate E := rfl

theorem interference_toExperiment {n : ℕ} (E : Experiment n) (i j : Fin n) :
    AronowAudit.P009.Interferes (toExperiment E) i j ↔ Interferes E i j := Iff.rfl

theorem marginal_toExperiment {n : ℕ} (E : Experiment n) (i : Fin n) (b : Bool) :
    AronowAudit.P009.marginal (toExperiment E) i b = marginal E i b := rfl

theorem hajek_toExperiment {n : ℕ} (E : Experiment n) (z : Assignment n) :
    AronowAudit.P009.hajek (toExperiment E) z = hajek E z := rfl

theorem paired_toExperiment {n : ℕ} (E : Experiment n) (ρ : Pairing n) :
    AronowAudit.P009.Paired (toExperiment E) (toPairing ρ) ↔ Paired E ρ := Iff.rfl

theorem regular_toStudy (S : Study) (k q s : ℝ) :
    AronowAudit.P009.RegularSequence (toStudy S) k q s ↔ RegularSequence S k q s := Iff.rfl

theorem regularMix_toStudy (S : Study) (k : ℝ) (q s : MomentIndex) :
    AronowAudit.P009.RegularMix (toStudy S) k q s ↔ RegularMix S k q s := Iff.rfl

theorem maximalMoments_toStudy (S : Study) (q s : MomentIndex) :
    AronowAudit.P009.MaximalMoments (toStudy S) q s ↔ MaximalMoments S q s := Iff.rfl

theorem estimatorClaims_toStudy (S : Study) (θ a : ℕ → ℝ) :
    AronowAudit.P009.EstimatorClaims (toStudy S) θ a ↔ EstimatorClaims S θ a := Iff.rfl

theorem conservative_toStudy (S : Study)
    (V : (t : ℕ) → Assignment (S.N t) → ℝ) :
    AronowAudit.P009.Conservative (toStudy S) V ↔ Conservative S V := Iff.rfl

theorem sharpLaw_toLaw (α : ℝ) (hα : 0 < α ∧ α < 1) :
    toLaw (sharpLaw α hα) = AronowAudit.P009.sharpLaw α hα := rfl

/-- The only non-definitional quantity: reindex the same coupling cost set
along the inverse probability-law adapters before applying the same infimum. -/
theorem wasserstein_toLaw {n : ℕ} (r : ℝ) (P Q : Law (Assignment n)) :
    AronowAudit.P009.wasserstein r (toLaw P) (toLaw Q) = wasserstein r P Q := by
  unfold AronowAudit.P009.wasserstein wasserstein
  congr 1
  ext v
  constructor
  · rintro ⟨J, hJ, hv⟩
    exact ⟨fromLaw J, hJ, hv⟩
  · rintro ⟨J, hJ, hv⟩
    exact ⟨toLaw J, hJ, hv⟩

/-- The exported complete-design counts certify the printed ratio's domain. -/
theorem complete_supportedArms (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hCR : CompleteSequence S) : SupportedArms S := by
  obtain ⟨p, _, _, hCR⟩ := hCR
  intro t z hz
  have h := (AronowAudit.P009.Wave1.complete_finite_lemmas_proof (S.positive t)
    (toExperiment (S.experiment t)) _ (hCR t) k q s (hReg t)).2.2.2 z hz
  have hn : (S.N t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (S.positive t))
  exact ⟨fun h0 => hn (h.1.symm.trans h0), fun h0 => hn (h.2.1.symm.trans h0)⟩

/-- The exported paired-design counts certify the printed ratio's domain. -/
theorem paired_supportedArms (S : Study) (ρ : (t : ℕ) → Pairing (S.N t)) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hPair : ∀ t, Paired (S.experiment t) (ρ t)) :
    SupportedArms S := by
  intro t z hz
  have h := (AronowAudit.P009.paired_finite_lemmas (S.positive t)
    (toExperiment (S.experiment t)) (toPairing (ρ t)) (hPair t) k q s
    (hReg t)).2.2.2.2.2 z hz
  have hn : (S.N t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (S.positive t))
  exact ⟨fun h0 => hn (h.1.symm.trans h0), fun h0 => hn (h.2.1.symm.trans h0)⟩

/-- Instantiate the credited finite spectral theorem with the existing fair
design. Structural dependence uses only outcomes, so its bounds do not change. -/
theorem spectral_bounds {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    dAvg E ≤ lambdaMax E ∧ lambdaMax E ≤ dMax E := by
  exact (AronowAudit.P009.Wave1.spectral_inflation_finite_proof hn
    (AronowAudit.P009.fairExperiment n E.outcome)
    (AronowAudit.P009.SparseCompletion.fair_BER n E.outcome)).2.2

end
end SAP.P009c.Bridge
