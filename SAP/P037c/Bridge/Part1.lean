import SAP.P037c.Defs
import AronowAudit.P037.Wave1.Gap.GLP037B4
import AronowAudit.P037.Wave1.Gap.GP037B4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c.Bridge
open SAP.P037c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- All network functions have the same bodies under the SAP names. -/
theorem nominationStatistic_eq {I : Type*} [Fintype I]
    (E : Finset I) (A : I → I → ℝ) (M z Y : I → ℝ) :
    nominationStatistic E A M z Y = AronowAudit.P037.nominationStatistic E A M z Y := rfl

theorem pairedSupport_eq : pairedSupport = AronowAudit.P037.pairedSupport := rfl
theorem pairedObserved_eq : pairedObserved = AronowAudit.P037.pairedObserved := rfl
theorem partner_eq : partner = AronowAudit.P037.partner := rfl

theorem paired_certificate : PairedTestCertificate := by
  have h := AronowAudit.P037.Wave1.direct_effect_permutation_counterexample_proof
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

theorem own_assignment_only (z z' : Finset (Fin 5 × Bool)) (i : Fin 5 × Bool)
    (h : i∈z ↔ i∈z') : directOnly z i=directOnly z' i :=
  AronowAudit.P037.paired_no_social_influence z z' i h

theorem split_count : (pairedSupport.filter PairSplit).card=32 := by
  calc
    (pairedSupport.filter PairSplit).card =
        (pairedSupport.filter (fun z => ∀ b : Fin 5,
          ((b,false)∈z ↔ (b,true)∉z))).card := by
      congr 1
      apply Finset.filter_congr
      intro z _
      rfl
    _ = 32 := AronowAudit.P037.Wave1.t35r2_split_card

theorem paired_stat_count (z : Finset (Fin 5 × Bool)) (hz : z∈pairedSupport) :
    pairedStatistic z (directOnly pairedObserved)=
      (2*((z ∩ pairedObserved.image partner).card:ℝ)-5)/5 := by
  exact AronowAudit.P037.Wave1.t35r2_stat_card z pairedObserved
    ((AronowAudit.P037.Wave1.t35r2_supported_card _).mp paired_certificate.2.1)

/-- Collapse the one-recipient sums to the pair statistic; both recipient groups have size five. -/
theorem pair_statistic (z : Finset (Fin 5 × Bool)) (hz : z∈pairedSupport)
    (Y : (Fin 5 × Bool) → ℝ) :
    nominationStatistic Finset.univ pairedNomination (fun _ => 1) (directOnly z) Y =
      pairedStatistic z Y := by
  have hcard : z.card=5 := (AronowAudit.P037.Wave1.t35r2_supported_card z).mp hz
  simp [nominationStatistic, pairedNomination, directOnly, pairedStatistic,
    ite_mul, mul_ite, hcard, sub_mul, Finset.sum_sub_distrib]
  ring

theorem sharp_null {Ω I : Type*} [Fintype Ω] [Fintype I] :
    NominationSharpNullStatement Ω I := by
  intro E A M Z p Y z0 α _ _ _ _ _ _ hp ht hsharp hα
  exact AronowAudit.P037.Wave1.sharp_null_permutation_valid_proof p hp ht
    (fun z y => nominationStatistic E A M (Z z) y) Y hsharp z0 α hα

theorem direct_effect {I : Type*} [Fintype I] : NominationDirectEffectStatement I :=
  @AronowAudit.P037.nomination_statistic_direct_effect I _

end SAP.P037c.Bridge
