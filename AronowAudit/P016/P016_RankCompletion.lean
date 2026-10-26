import Mathlib

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace AronowAudit.P016.RankCompletion

lemma rank_permutation {N : ℕ} (t : Fin N → ℝ) (ht : Function.Injective t) :
    ∃ e : Equiv.Perm (Fin N), ∀ i,
      (∑ j : Fin N, if t j < t i then (1 : ℕ) else 0) = (e i).val := by
  classical
  let S : Finset ℝ := Finset.univ.image t
  have hc : S.card = N := by
    simpa [S] using Finset.card_image_of_injective Finset.univ ht
  let f : Fin N ≃ S := Equiv.ofBijective
    (fun i => ⟨t i, by simp [S]⟩)
    ⟨fun i j h => ht (congrArg Subtype.val h), by
      rintro ⟨x,hx⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
      exact ⟨i, Subtype.ext hi⟩⟩
  let o : Fin N ≃o S := S.orderIsoOfFin hc
  let e : Equiv.Perm (Fin N) := f.trans o.symm.toEquiv
  have ho (i j : Fin N) : t j < t i ↔ e j < e i := by
    change (f j : ℝ) < (f i : ℝ) ↔ o.symm (f j) < o.symm (f i)
    exact o.symm.lt_iff_lt.symm
  refine ⟨e, fun i => ?_⟩
  simp_rw [ho]
  rw [Equiv.sum_comp e (fun j => if j < e i then (1 : ℕ) else 0)]
  simpa [Finset.sum_boole, Finset.filter_gt_eq_Iio] using Fin.card_Iio (e i)

lemma rank_count_eq_one {N : ℕ} (t : Fin N → ℝ) (ht : Function.Injective t) (k : Fin N) :
    (∑ i : Fin N, if (∑ j : Fin N, if t j < t i then (1 : ℕ) else 0) = k.val
      then (1 : ℝ) else 0) = 1 := by
  classical
  obtain ⟨e,he⟩ := rank_permutation t ht
  simp_rw [he]
  rw [Equiv.sum_comp e (fun j => if j.val = k.val then (1 : ℝ) else 0)]
  simp only [Fin.val_inj]
  simp


def strictRank {N : ℕ} (t : Fin N → ℝ) (i : Fin N) : ℕ :=
  ∑ j, if t j < t i then 1 else 0

lemma strict_rank_perm {N : ℕ} (t : Fin N → ℝ) (π : Equiv.Perm (Fin N)) (i : Fin N) :
    strictRank (fun j => t (π j)) i = strictRank t (π i) := by
  classical
  exact Equiv.sum_comp π (fun j => if t j < t (π i) then (1 : ℕ) else 0)

lemma measurable_strict_rank {N : ℕ} (i : Fin N) :
    Measurable (fun t : Fin N → ℝ => strictRank t i) := by
  classical
  unfold strictRank
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i))
    measurable_const measurable_const

lemma strict_rank_uniform {B : ℕ} (μ : Measure (Fin (B+1) → ℝ)) [IsProbabilityMeasure μ]
    (hex : ∀ π : Equiv.Perm (Fin (B+1)), μ.map (fun t i => t (π i)) = μ)
    (hnt : ∀ᵐ t ∂μ, Function.Injective t) (i0 k : Fin (B+1)) :
    μ.real {t | strictRank t i0 = k.val} = 1/(B+1) := by
  classical
  let E : Fin (B+1) → Set (Fin (B+1) → ℝ) := fun i => {t | strictRank t i = k.val}
  have hmeas : ∀ i, MeasurableSet (E i) := fun i =>
    measurableSet_eq_fun (measurable_strict_rank i) measurable_const
  have hprob : ∀ i, μ.real (E i) = μ.real (E i0) := by
    intro i
    let π : Equiv.Perm (Fin (B+1)) := Equiv.swap i0 i
    have hf : Measurable (fun t : Fin (B+1) → ℝ => fun j => t (π j)) :=
      measurable_pi_iff.mpr (fun j => measurable_pi_apply (π j))
    have hp := map_measureReal_apply (μ := μ) hf (hmeas i0)
    rw [hex π] at hp
    have hevent : (fun t : Fin (B+1) → ℝ => fun j => t (π j)) ⁻¹' E i0 = E i := by
      ext t
      simp only [E,Set.mem_preimage,Set.mem_setOf_eq,strict_rank_perm]
      simp [π]
    rw [hevent] at hp
    exact hp.symm
  have hi : ∀ i, Integrable ((E i).indicator (fun _ => (1 : ℝ))) μ :=
    fun i => (integrable_const (1 : ℝ)).indicator (hmeas i)
  have hpoint : (fun t => ∑ i, (E i).indicator (fun _ => (1 : ℝ)) t) =ᵐ[μ] (fun _ => 1) := by
    filter_upwards [hnt] with t ht
    simpa only [E,Set.indicator,Set.mem_setOf_eq,strictRank] using rank_count_eq_one t ht k
  have hb := integral_congr_ae hpoint
  rw [integral_finsetSum _ (fun i _ => hi i)] at hb
  have hind : ∀ i, (∫ t, (E i).indicator (fun _ => (1 : ℝ)) t ∂μ) = μ.real (E i) :=
    fun i => by simpa using (integral_indicator_const (μ := μ) (1 : ℝ) (hmeas i))
  have hunit : μ.real Set.univ = 1 := by simp [measureReal_def]
  simp only [hind,hprob,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one,integral_const,hunit,one_smul] at hb
  apply (eq_div_iff (by positivity : (B+1 : ℝ) ≠ 0)).mpr
  simpa only [mul_comm,E] using hb


lemma strict_rank_finite_event {B : ℕ} (μ : Measure (Fin (B+1) → ℝ)) [IsProbabilityMeasure μ]
    (hex : ∀ π : Equiv.Perm (Fin (B+1)), μ.map (fun t i => t (π i)) = μ)
    (hnt : ∀ᵐ t ∂μ, Function.Injective t) (i0 : Fin (B+1)) (A : Finset (Fin (B+1))) :
    μ.real {t | ∃ k ∈ A, strictRank t i0 = k.val} = A.card/(B+1) := by
  classical
  have hevent : {t : Fin (B+1) → ℝ | ∃ k ∈ A, strictRank t i0 = k.val} =
      ⋃ k ∈ A, {t | strictRank t i0 = k.val} := by ext t; simp
  rw [hevent, measureReal_biUnion_finset]
  · simp_rw [strict_rank_uniform μ hex hnt i0]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  · intro j hj k hk hjk
    exact Set.disjoint_left.mpr (fun t htj htk => hjk (Fin.ext (htj.symm.trans htk)))
  · intro k hk
    exact measurableSet_eq_fun (measurable_strict_rank i0) measurable_const

end AronowAudit.P016.RankCompletion
