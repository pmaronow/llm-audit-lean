import SAP.P045b.Defs
import AronowAudit.P045.P045_Spillover
import AronowAudit.P045.P045_ExposureVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SAP.P045b.Bridge
open SAP.P045b Finset
open scoped BigOperators
noncomputable section

/-- Preserve the mass function and its two validity certificates. -/
def toDesign {Ω : Type*} [Fintype Ω] (p : Design Ω) : AronowAudit.P045.Design Ω :=
  ⟨p.mass, p.nonneg, p.total⟩

def fromDesign {Ω : Type*} [Fintype Ω] (p : AronowAudit.P045.Design Ω) : Design Ω :=
  ⟨p.mass, p.nonneg, p.total⟩

def toFiniteDesign {Ω : Type*} [Fintype Ω] (p : Design Ω) :
    AronowAudit.P045.ExposureVariance.FiniteDesign Ω := ⟨p.mass, p.nonneg, p.total⟩

def fromNetwork {n : ℕ} (A : AronowAudit.P045.Network n) : Network n :=
  ⟨A.adj, A.symmetric, A.loopless⟩

theorem toDesign_mass {Ω : Type*} [Fintype Ω] (p : Design Ω) :
    (toDesign p).mass = p.mass := rfl

theorem toFiniteDesign_mass {Ω : Type*} [Fintype Ω] (p : Design Ω) :
    (toFiniteDesign p).mass = p.mass := rfl

@[simp] theorem prob_eq {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (E : Ω → Prop) :
    AronowAudit.P045.prob p E = prob p E := rfl

@[simp] theorem condMean_eq {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (E : Ω → Prop) (X : Ω → ℝ) :
    AronowAudit.P045.condMean p E X = condMean p E X := rfl

@[simp] theorem coMembers_eq {n : ℕ} (i : Fin n) (z : Assignment n) :
    AronowAudit.P045.coMembers i z = coMembers i z := rfl

/-- Lossless single-cell recoding: the distinguished label versus all other labels. -/
theorem conditional_cell {n : ℕ} {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    (p : Design (Assignment n)) (D : Assignment n → Fin n → Δ)
    (y : Fin n → Δ → ℝ) (k : Δ) (hk : ∀ i, 0 < exposureProb p.mass D i k)
    (hc : 0 < prob p.mass (fun z => ∃ i, D z i = k)) :
    condMean p.mass (fun z => ∃ i, D z i = k) (htTotal p.mass D y k) =
      (∑ i, y i k) / prob p.mass (fun z => ∃ i, D z i = k) := by
  classical
  let D' : Assignment n → Fin n → AronowAudit.P045.Exposure :=
    fun z i => if D z i = k then .d11 else .d00
  let y' : Fin n → AronowAudit.P045.Exposure → ℝ := fun i _ => y i k
  have hd (z : Assignment n) (i : Fin n) : D' z i = .d11 ↔ D z i = k := by
    simp [D']
  have hp (i : Fin n) :
      AronowAudit.P045.exposureProb p.mass D' i .d11 = exposureProb p.mass D i k := by
    change prob p.mass (fun z => D' z i = .d11) = prob p.mass (fun z => D z i = k)
    congr 1
    funext z
    exact propext (hd z i)
  have he : (fun z => ∃ i, D' z i = .d11) = (fun z => ∃ i, D z i = k) := by
    funext z
    simp only [hd]
  have ht : AronowAudit.P045.htTotal p.mass D' y' .d11 = htTotal p.mass D y k := by
    funext z
    unfold AronowAudit.P045.htTotal htTotal
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : D z i = k
    · simp [hd, h, hp, AronowAudit.P045.observed, observed, y']
    · simp [hd, h]
  have h := AronowAudit.P045.nonempty_ht_conditional (toDesign p) D' y' .d11
    (fun i => by simpa only [toDesign_mass, hp] using hk i)
    (by simpa only [toDesign_mass, he, prob_eq] using hc)
  simpa only [toDesign_mass, he, ht, y', prob_eq, condMean_eq] using h

theorem T17_glue : T17Statement := by
  classical
  intro n hn Δ _ _ p D y k l _ hk hl
  have hu := AronowAudit.P045.ht_unbiased_headline hn (toDesign p) D y k hk
  refine ⟨?_, hu.1, hu.2 l hl, conditional_cell p D y k hk, ?_, by norm_num⟩
  · intro z hz
    have he := AronowAudit.P045.empty_ht_total (toDesign p) D y k l hk hl z hz
    refine ⟨he.1, he.2, ?_, AronowAudit.P045.empty_hajek p.mass D y k z hz, ?_⟩
    · simp [hz]
    · simp [exposureSampleMean, hz]
  · intro hc hempty hy
    rw [conditional_cell p D y k hk hc]
    have hcpl : prob p.mass (fun z => ∃ i, D z i = k) +
        prob p.mass (fun z => ∀ i, D z i ≠ k) = 1 := by
      unfold prob expect
      rw [← Finset.sum_add_distrib]
      convert p.total using 1
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : ∃ i, D z i = k
      · simp [hz, show ¬(∀ i, D z i ≠ k) by simpa using hz]
      · simp [show ∀ i, D z i ≠ k by simpa using hz]
    intro he
    have hh := (div_eq_iff (ne_of_gt hc)).mp he
    have hmul : (∑ i, y i k) * (1 - prob p.mass (fun z => ∃ i, D z i = k)) = 0 := by
      linarith
    rcases mul_eq_zero.mp hmul with h | h
    · exact hy h
    · linarith

theorem T18_glue : T18Statement := by
  refine ⟨?_, AronowAudit.P045.coordinate_removal_instance⟩
  intro n i
  have h := AronowAudit.P045.coordinate_removal_correct i
  exact ⟨h.1, h.2.1, h.2.2, AronowAudit.P045.reindexed_outcome_unique i⟩

theorem T19_glue : T19Statement := by
  refine ⟨@AronowAudit.P045.fixed_count_peers_correct, ?_, by norm_num⟩
  intro z hz i
  have h := AronowAudit.P045.fixed_count_peers_correct (by norm_num : 2 ≤ 3)
    (2/3) (by norm_num) (by norm_num) (K := 2) (by norm_num) z hz i
  constructor
  · intro hi
    have ht := (h.2.1 hi).1
    norm_num only [coMembers_eq, Nat.cast_ofNat] at ht
    exact ht
  · intro hi
    have ht := h.2.2 hi
    norm_num only [coMembers_eq, Nat.cast_ofNat] at ht
    exact ht

theorem T20_glue : T20Statement := AronowAudit.P045.within_hops_counterexample

theorem T21_glue : T21Statement :=
  ⟨@AronowAudit.P045.epsilon_net_correction,
    AronowAudit.P045.within_hops_counterexample.2⟩

end
end SAP.P045b.Bridge
