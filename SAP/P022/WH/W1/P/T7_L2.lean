import SAP.P022.WH.W1.Leaves
import AronowAudit.P022.Wave1.SharpBounds
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T7_L2

open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section

def corner (i : ℕ) : ℝ × ℝ :=
  (if i < 2 then 0 else 1, if i % 2 = 0 then 0 else 1)

lemma corner_index (i : ℕ) :
    (cornerWitness.y1 i, cornerWitness.y0 i) = corner (i % 4) := by
  simp only [cornerWitness, corner]
  rw [Nat.mod_mod_of_dvd i (by decide : 2 ∣ 4)]

lemma corner_average (f : ℝ × ℝ → ℝ) :
    (∑ i ∈ Finset.range 4, f (corner i)) / 4 =
      (f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1)) / 4 := by
  norm_num [Finset.sum_range_succ, corner]

lemma sum_cycles (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (4 * n), f (i % 4)) =
      (n : ℝ) * (∑ i ∈ Finset.range 4, f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have he : (∑ i ∈ Finset.range 4, f ((4 * n + i) % 4)) =
        ∑ i ∈ Finset.range 4, f i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
      simp [Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
    rw [he]
    push_cast
    ring

lemma mean_exact (r : ℕ) (f : ℝ × ℝ → ℝ) :
    finiteMean (fun i : Fin (cornerWitness.design (4 * r)).N =>
      f (cornerWitness.y1 i.val, cornerWitness.y0 i.val)) =
      (f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1)) / 4 := by
  simp_rw [corner_index]
  have hN : (cornerWitness.design (4 * r)).N = 4 * (r + 1) := by
    simp [cornerWitness, reciprocalWitness]
    omega
  rw [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    (Fin.sum_univ_eq_sum_range (fun i => f (corner (i % 4)))), hN,
    sum_cycles (fun i => f (corner i)) (r + 1)]
  push_cast
  have hsum : (∑ i ∈ Finset.range 4, f (corner i)) =
      f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1) := by
    have h := corner_average f
    linarith
  rw [hsum]
  have hn : (r + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hn]

lemma marginal_perm (r : ℕ) :
    List.Perm (List.ofFn (rowOutcomes cornerWitness true (4 * r)))
      (List.ofFn (rowOutcomes cornerWitness false (4 * r))) := by
  have hN : (cornerWitness.design (4 * r)).N = (r + 1) * 4 := by
    simp [cornerWitness, reciprocalWitness]
    omega
  let e : Fin (cornerWitness.design (4 * r)).N ≃ Fin (r + 1) × Fin 4 :=
    (finCongr hN).trans finProdFinEquiv.symm
  let σ : Equiv.Perm (Fin (cornerWitness.design (4 * r)).N) :=
    (e.trans (Equiv.prodCongr (Equiv.refl _) (Equiv.swap (1 : Fin 4) 2))).trans e.symm
  have heq : (fun i => rowOutcomes cornerWitness false (4 * r) (σ i)) =
      rowOutcomes cornerWitness true (4 * r) := by
    funext i
    obtain ⟨⟨j, l⟩, rfl⟩ := e.symm.surjective i
    simp only [σ, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodCongr_apply]
    fin_cases l <;>
      norm_num [e, Equiv.symm_trans_apply, rowOutcomes, cornerWitness, finProdFinEquiv,
        Nat.add_mod, Nat.mul_mod, Equiv.swap_apply_def]
  simpa only [Function.comp_def, heq] using
    σ.ofFn_comp_perm (rowOutcomes cornerWitness false (4 * r))

end
end SAP.P022.WH.W1.P.T7_L2

theorem SAP.P022.WH.W1.T7_L2_proof : SAP.P022.WH.W1.T7_L2 := by
  intro r
  let d := cornerWitness.design (4 * r)
  let a := rowOutcomes cornerWitness true (4 * r)
  let b := rowOutcomes cornerWitness false (4 * r)
  haveI : NeZero (cornerWitness.design (4 * r)).N :=
    ⟨by have h := (cornerWitness.design (4 * r)).population_min; omega⟩
  have hμ1 : finiteMean a = 1 / 2 := by
    have h := SAP.P022.WH.W1.P.T7_L2.mean_exact r Prod.fst
    norm_num [a, rowOutcomes] at h ⊢
    exact h
  have hμ0 : finiteMean b = 1 / 2 := by
    have h := SAP.P022.WH.W1.P.T7_L2.mean_exact r Prod.snd
    norm_num [b, rowOutcomes] at h ⊢
    exact h
  have hv1 : finiteVariance a = 1 / 4 := by
    rw [finiteVariance, hμ1]
    have h := SAP.P022.WH.W1.P.T7_L2.mean_exact r (fun p => (p.1 - 1 / 2) ^ 2)
    norm_num [a, rowOutcomes] at h ⊢
    exact h
  have hv0 : finiteVariance b = 1 / 4 := by
    rw [finiteVariance, hμ0]
    have h := SAP.P022.WH.W1.P.T7_L2.mean_exact r (fun p => (p.2 - 1 / 2) ^ 2)
    norm_num [b, rowOutcomes] at h ⊢
    exact h
  have hprod : finiteMean (fun i => a i * b i) = 1 / 4 := by
    have h := SAP.P022.WH.W1.P.T7_L2.mean_exact r (fun p => p.1 * p.2)
    norm_num [a, b, rowOutcomes] at h ⊢
    exact h
  have hcov : finiteCovariance a b = 0 := by
    rw [finiteCovariance, hμ1, hμ0]
    have h := SAP.P022.WH.W1.P.T7_L2.mean_exact r
      (fun p => (p.1 - 1 / 2) * (p.2 - 1 / 2))
    norm_num [a, b, rowOutcomes] at h ⊢
    exact h
  have hsortedA : AronowAudit.P022.sortedValues b = AronowAudit.P022.sortedValues a := by
    have hp :=
      ((AronowAudit.P022.Wave1.SharpBounds.n2_proof b).1.trans
        (SAP.P022.WH.W1.P.T7_L2.marginal_perm r).symm).trans
        (AronowAudit.P022.Wave1.SharpBounds.n2_proof a).1.symm
    have he := hp.eq_of_sortedLE (by
      rw [AronowAudit.P022.Wave1.SharpBounds.sortedValues_ofFn]
      exact List.sortedLE_mergeSort) (by
      rw [AronowAudit.P022.Wave1.SharpBounds.sortedValues_ofFn]
      exact List.sortedLE_mergeSort)
    exact List.ofFn_injective he
  have hsorted : sortedValues b = sortedValues a := by
    simpa only [SAP.P022.Bridge.sortedValues_eq] using hsortedA
  have hintA :
      (∫ u in (0 : ℝ)..1,
        AronowAudit.P022.empiricalQuantile a u * AronowAudit.P022.empiricalQuantile b u) =
        AronowAudit.P022.finiteMean
          (fun i => (AronowAudit.P022.sortedValues a i) ^ 2) := by
    apply AronowAudit.P022.Wave1.SharpBounds.n4_proof
    intro j u hl hu
    rw [(AronowAudit.P022.Wave1.SharpBounds.n3_proof a j u hl hu).1,
      (AronowAudit.P022.Wave1.SharpBounds.n3_proof b j u hl hu).1, hsortedA]
    ring
  have hint :
      (∫ u in (0 : ℝ)..1, empiricalQuantile a u * empiricalQuantile b u) =
        finiteMean (fun i => (sortedValues a i) ^ 2) := by
    simpa only [SAP.P022.Bridge.empiricalQuantile_eq, SAP.P022.Bridge.finiteMean_eq,
      SAP.P022.Bridge.sortedValues_eq] using hintA
  have hraw : finiteMean (fun i => a i ^ 2) = 1 / 2 := by
    have h := SAP.P022.WH.W1.P.T7_L2.mean_exact r (fun p => p.1 ^ 2)
    norm_num [a, rowOutcomes] at h ⊢
    exact h
  have hs : finiteMean (fun i => (sortedValues a i) ^ 2) = 1 / 2 := by
    calc
      finiteMean (fun i => (sortedValues a i) ^ 2) =
          AronowAudit.P022.finiteMean
            (fun i => (AronowAudit.P022.sortedValues a i) ^ 2) := by
        rw [SAP.P022.Bridge.finiteMean_eq, SAP.P022.Bridge.sortedValues_eq]
      _ = AronowAudit.P022.finiteMean (fun i => a i ^ 2) :=
        AronowAudit.P022.Wave1.SharpBounds.n1_proof _ _
          (AronowAudit.P022.Wave1.SharpBounds.n2_proof a).1 (fun x => x ^ 2)
      _ = AronowAudit.P022.finiteMean (fun i => a i ^ 2) := rfl
      _ = 1 / 2 := hraw
  have hsharp : sharpCovariance a b .H = 1 / 4 := by
    have hsharpA : AronowAudit.P022.sharpCovariance a b .H = 1 / 4 := by
      simp only [AronowAudit.P022.sharpCovariance, ite_true]
      rw [hintA]
      rw [AronowAudit.P022.Wave1.SharpBounds.n1_proof _ _
        (AronowAudit.P022.Wave1.SharpBounds.n2_proof a).1 (fun x => x ^ 2)]
      have hμ1A : AronowAudit.P022.finiteMean a = 1 / 2 :=
        (SAP.P022.Bridge.finiteMean_eq a).trans hμ1
      have hμ0A : AronowAudit.P022.finiteMean b = 1 / 2 :=
        (SAP.P022.Bridge.finiteMean_eq b).trans hμ0
      rw [hμ1A, hμ0A]
      have hrawA : AronowAudit.P022.finiteMean (fun i => a i ^ 2) = 1 / 2 :=
        (SAP.P022.Bridge.finiteMean_eq (fun i => a i ^ 2)).trans hraw
      rw [hrawA]
      norm_num
    exact (SAP.P022.Bridge.sharpCovariance_eq a b AronowAudit.P022.BoundSide.H).symm.trans
      hsharpA
  have hm : d.m = 2 * (r + 1) := by
    simp [d, cornerWitness, reciprocalWitness]
    omega
  have hk : d.k = 2 * (r + 1) := by
    simp [d, cornerWitness, reciprocalWitness]
    omega
  simpa only [CornerBalancedMoments, d, a, b] using
    (show d.m = 2 * (r + 1) ∧ d.k = 2 * (r + 1) ∧
      finiteMean a = 1 / 2 ∧ finiteMean b = 1 / 2 ∧
      finiteVariance a = 1 / 4 ∧ finiteVariance b = 1 / 4 ∧
      finiteMean (fun i => a i * b i) = 1 / 4 ∧ finiteCovariance a b = 0 ∧
      (∫ u in (0 : ℝ)..1, empiricalQuantile a u * empiricalQuantile b u) = 1 / 2 ∧
      sharpCovariance a b .H = 1 / 4 from
      ⟨hm, hk, hμ1, hμ0, hv1, hv0, hprod, hcov, by rw [hint, hs], hsharp⟩)
