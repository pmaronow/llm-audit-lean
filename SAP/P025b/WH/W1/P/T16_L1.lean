import SAP.P025b.WH.W1.Leaves
import AronowAudit.P025.P025_Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b.WH.W1.P.T16_L1

open scoped BigOperators

noncomputable section

private theorem quota_mem_iff (N s : ℕ) (t : Finset (Fin N)) :
    t ∈ AronowAudit.P025.quotaDraws N s ↔ t.card = s := by
  simp [AronowAudit.P025.quotaDraws, Finset.mem_powersetCard]

private def quotaLift {N s : ℕ} (f : SAP.P025b.QuotaDraw N s → ℝ)
    (t : Finset (Fin N)) : ℝ :=
  if ht : t.card = s then f ⟨t, ht⟩ else 0

private theorem sum_quota (N s : ℕ) (f : SAP.P025b.QuotaDraw N s → ℝ) :
    (∑ ω, f ω) =
      ∑ t ∈ AronowAudit.P025.quotaDraws N s, quotaLift f t := by
  classical
  letI : Fintype {t : Finset (Fin N) // t.card = s} :=
    SAP.P025b.quotaDrawFintype N s
  have hsum := Finset.sum_subtype
    (F := inferInstance)
    (p := fun t : Finset (Fin N) => t.card = s)
    (AronowAudit.P025.quotaDraws N s)
    (quota_mem_iff N s)
    (quotaLift f)
  calc
    (∑ ω : SAP.P025b.QuotaDraw N s, f ω) =
        ∑ ω : SAP.P025b.QuotaDraw N s, quotaLift f ω.val := by
      change (∑ ω : {t : Finset (Fin N) // t.card = s}, f ω) =
        ∑ ω : {t : Finset (Fin N) // t.card = s}, quotaLift f ω.val
      apply Fintype.sum_congr
      intro ω
      simp only [quotaLift, dif_pos ω.property]
    _ = ∑ t ∈ AronowAudit.P025.quotaDraws N s, quotaLift f t := hsum.symm

end

end SAP.P025b.WH.W1.P.T16_L1

open scoped BigOperators
open SAP.P025b.WH.W1.P.T16_L1 in
theorem SAP.P025b.WH.W1.T16_L1_proof : SAP.P025b.WH.W1.T16_L1 := by
  classical
  intro N s hs hsN
  let q := AronowAudit.P025.quotaDraws N s
  have hmem : ∀ t : Finset (Fin N), t ∈ q ↔ t.card = s := by
    intro t
    exact quota_mem_iff N s t
  have hvalid := AronowAudit.P025.quota_design_valid N s hsN
  have hcard : Fintype.card (SAP.P025b.QuotaDraw N s) = q.card := by
    change Fintype.card {t : Finset (Fin N) // t.card = s} = q.card
    exact Fintype.card_of_subtype q hmem
  have hcardpos : 0 < Fintype.card (SAP.P025b.QuotaDraw N s) := by
    rw [hcard]
    exact Finset.card_pos.mpr hvalid.1
  have hden : (0 : ℝ) < (Fintype.card (SAP.P025b.QuotaDraw N s) : ℝ) := by
    exact_mod_cast hcardpos
  let d : SAP.P025b.FiniteDesign (Fin N) (SAP.P025b.QuotaDraw N s) := {
    sample := fun ω => ω.val
    probability := fun _ => 1 / (Fintype.card (SAP.P025b.QuotaDraw N s) : ℝ)
    nonnegative := by
      intro ω
      exact le_of_lt (one_div_pos.mpr hden)
    total := by
      letI : Fintype {t : Finset (Fin N) // t.card = s} :=
        SAP.P025b.quotaDrawFintype N s
      rw [hcard]
      calc
        (∑ ω, 1 / (q.card : ℝ)) = ∑ t ∈ q, 1 / (q.card : ℝ) := by
          exact (Finset.sum_subtype (F := inferInstance) q hmem
            (fun _ => 1 / (q.card : ℝ))).symm
        _ = 1 := hvalid.2.1
  }
  refine ⟨d, ?_, ?_, ?_⟩
  · intro ω
    rfl
  · intro ω
    rfl
  · intro i
    have hinc : SAP.P025b.inclusion d i = AronowAudit.P025.quotaMarginal N s i := by
      classical
      letI : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a = b)
      unfold SAP.P025b.inclusion SAP.P025b.designExpectation
      rw [sum_quota N s]
      dsimp
      have hquota :
          (∑ t ∈ q, quotaLift (fun ω : SAP.P025b.QuotaDraw N s =>
            d.probability ω * (if i ∈ d.sample ω then 1 else 0)) t) =
          ∑ t ∈ q, (1 / (Fintype.card (SAP.P025b.QuotaDraw N s) : ℝ)) *
            (if i ∈ t then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro t ht
        have htcard : t.card = s := (hmem t).mp ht
        simp [quotaLift, d, htcard]
      change (∑ t ∈ q, quotaLift (fun ω : SAP.P025b.QuotaDraw N s =>
        d.probability ω * (if i ∈ d.sample ω then 1 else 0)) t) = _
      rw [hquota]
      calc
        (∑ t ∈ q, (1 / (Fintype.card (SAP.P025b.QuotaDraw N s) : ℝ)) *
            (if i ∈ t then 1 else 0)) =
            ∑ t ∈ q, if i ∈ t then
              (1 / (Fintype.card (SAP.P025b.QuotaDraw N s) : ℝ)) else 0 := by
          congr 1
          funext t
          split <;> simp
        _ = ∑ t ∈ q with i ∈ t,
            (1 / (Fintype.card (SAP.P025b.QuotaDraw N s) : ℝ)) := by
          rw [← Finset.sum_filter]
        _ = ((q.filter (fun t => i ∈ t)).card : ℝ) *
            (1 / (Fintype.card (SAP.P025b.QuotaDraw N s) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((q.filter (fun t => i ∈ t)).card : ℝ) / (q.card : ℝ) := by
          rw [hcard]
          ring
        _ = AronowAudit.P025.quotaMarginal N s i := by
          rw [AronowAudit.P025.quotaMarginal]
          simp only [q]
          congr 1
          · congr 1
            apply congrArg Finset.card
            ext t
            simp
    rw [hinc, AronowAudit.P025.quota_marginal_eq N s hs hsN i]

