import AronowAudit.P018.Wave1.WeightedConsistency.M0

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

noncomputable section

theorem members_eq_endpoints {N : ℕ} (d : Dyad N) :
    members d = {firstUnit d, secondUnit d} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact firstUnit_mem d
    · exact secondUnit_mem d
  · simp [members_card, firstUnit_ne_secondUnit]

/-- At most N dyads contain one specified unit. -/
theorem incident_dyad_bound (N : ℕ) (x : Fin N) :
    (∑ d : Dyad N, if x ∈ members d then (1 : ℝ) else 0) ≤ N := by
  let s : Finset (Dyad N) := univ.filter (fun d => x ∈ members d)
  let other (d : Dyad N) : Fin N :=
    if firstUnit d = x then secondUnit d else firstUnit d
  have heq (d : Dyad N) (hd : d ∈ s) : members d = {x, other d} := by
    have hx : x ∈ members d := (mem_filter.mp hd).2
    rw [members_eq_endpoints] at hx ⊢
    simp only [mem_insert, mem_singleton] at hx
    dsimp [other]
    rcases hx with hx | hx
    · simp [hx.symm]
    · by_cases h : firstUnit d = x
      · simp [h, hx.symm]
      · simp [h, hx.symm, pair_comm]
  have hcard : s.card ≤ N := by
    calc
      _ ≤ (univ : Finset (Fin N)).card := Finset.card_le_card_of_injOn other
        (fun _ _ => mem_univ _) (by
          intro d hd f hf hdf
          apply Subtype.ext
          change members d = members f
          rw [heq d hd, heq f hf, hdf])
      _ = N := by simp
  have hc : (∑ d : Dyad N, if x ∈ members d then (1 : ℝ) else 0) = s.card := by
    simp [s, ← Finset.sum_filter]
  rw [hc]
  exact_mod_cast hcard

/-- A row overlap count is controlled by the incidence counts at its members. -/
theorem support_overlap_row_bound {V E : Type*} [Fintype E] [DecidableEq V]
    (σ : E → Finset V) (S : Finset V) (a : ℝ)
    (ha : ∀ x ∈ S, (∑ e, if x ∈ σ e then (1 : ℝ) else 0) ≤ a) :
    (∑ e, if (S ∩ σ e).Nonempty then (1 : ℝ) else 0) ≤ S.card * a := by
  have hi (e : E) : (if (S ∩ σ e).Nonempty then (1 : ℝ) else 0) ≤
      ∑ x ∈ S, if x ∈ σ e then (1 : ℝ) else 0 := by
    have heq : (∑ x ∈ S, if x ∈ σ e then (1 : ℝ) else 0) = (S ∩ σ e).card := by
      rw [← Finset.sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      congr 1
    rw [heq]
    split_ifs with h
    · exact_mod_cast Finset.card_pos.mpr h
    · positivity
  calc
    _ ≤ ∑ e, ∑ x ∈ S, if x ∈ σ e then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun e _ => hi e)
    _ = ∑ x ∈ S, ∑ e, if x ∈ σ e then (1 : ℝ) else 0 := Finset.sum_comm
    _ ≤ ∑ _x ∈ S, a := Finset.sum_le_sum ha
    _ = _ := by simp

theorem dyad_overlap_row_bound (N : ℕ) (d : Dyad N) :
    (∑ f : Dyad N, if overlap d f then (1 : ℝ) else 0) ≤ 2 * N := by
  have hh := support_overlap_row_bound members (members d) (N : ℝ)
    (fun x _ => incident_dyad_bound N x)
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro f hf
    by_cases hov : overlap d f
    · have hov' : (members d ∩ members f).Nonempty := hov
      simp only [hov, hov', ↓reduceIte]
    · have hov' : ¬(members d ∩ members f).Nonempty := hov
      simp only [hov, hov', ↓reduceIte]
  · simp only [members_card, Nat.cast_ofNat]

theorem dyad_card_real_le (N : ℕ) : (Fintype.card (Dyad N) : ℝ) ≤ (N : ℝ) ^ 2 / 2 := by
  rw [number_of_dyads]
  have he := Nat.choose_two_right N
  have hh := Nat.mod_add_div (N * (N - 1)) 2
  have hN : (N * (N - 1) / 2) * 2 ≤ N * (N - 1) := Nat.div_mul_le_self _ _
  have hN' : ((N.choose 2 : ℕ) : ℝ) * 2 ≤ (N : ℝ) * (N - 1 : ℕ) := by
    rw [he]
    exact_mod_cast hN
  have hsub : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  have hnon : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [mul_le_mul_of_nonneg_left hsub hnon]

theorem total_dyad_overlap_bound (N : ℕ) :
    (∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then (1 : ℝ) else 0) ≤ (N : ℝ) ^ 3 := by
  calc
    _ ≤ ∑ _d : Dyad N, 2 * (N : ℝ) :=
      Finset.sum_le_sum (fun d _ => dyad_overlap_row_bound N d)
    _ = (Fintype.card (Dyad N) : ℝ) * (2 * N) := by simp
    _ ≤ ((N : ℝ) ^ 2 / 2) * (2 * N) :=
      mul_le_mul_of_nonneg_right (dyad_card_real_le N) (by positivity)
    _ = (N : ℝ) ^ 3 := by ring

theorem pairSupport_card_le {N : ℕ} (P : Dyad N × Dyad N) : (pairSupport P).card ≤ 3 := by
  unfold pairSupport
  split_ifs with h
  · have hc := Finset.card_union_add_card_inter (members P.1) (members P.2)
    have hp := Finset.card_pos.mpr h
    rw [members_card, members_card] at hc
    omega
  · simp

theorem incident_pair_bound (N : ℕ) (x : Fin N) :
    (∑ P : Dyad N × Dyad N, if x ∈ pairSupport P then (1 : ℝ) else 0) ≤ 4 * (N : ℝ) ^ 2 := by
  have hi (d f : Dyad N) :
      (if x ∈ pairSupport (d, f) then (1 : ℝ) else 0) ≤
        (if x ∈ members d then (if overlap d f then (1 : ℝ) else 0) else 0) +
        (if x ∈ members f then (if overlap f d then (1 : ℝ) else 0) else 0) := by
    have hs : overlap f d ↔ overlap d f := by unfold overlap; rw [inter_comm]
    simp only [pairSupport, hs]
    split_ifs <;> simp_all
  have hsum : (∑ d : Dyad N, ∑ f : Dyad N,
      if x ∈ members d then (if overlap d f then (1 : ℝ) else 0) else 0) ≤ 2 * (N : ℝ)^2 := by
    calc
      _ = ∑ d : Dyad N, if x ∈ members d then
          (∑ f : Dyad N, if overlap d f then (1 : ℝ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        split_ifs <;> simp
      _ ≤ ∑ d : Dyad N, if x ∈ members d then 2 * (N : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro d hd
        split_ifs
        · exact dyad_overlap_row_bound N d
        · rfl
      _ = (∑ d : Dyad N, if x ∈ members d then (1 : ℝ) else 0) * (2 * N) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d hd
        split_ifs <;> simp
      _ ≤ (N : ℝ) * (2 * N) :=
        mul_le_mul_of_nonneg_right (incident_dyad_bound N x) (by positivity)
      _ = _ := by ring
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ d : Dyad N, ∑ f : Dyad N,
        ((if x ∈ members d then (if overlap d f then (1 : ℝ) else 0) else 0) +
        (if x ∈ members f then (if overlap f d then (1 : ℝ) else 0) else 0)) :=
      Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun f _ => hi d f))
    _ = (∑ d : Dyad N, ∑ f : Dyad N,
        if x ∈ members d then (if overlap d f then (1 : ℝ) else 0) else 0) +
        (∑ d : Dyad N, ∑ f : Dyad N,
        if x ∈ members f then (if overlap f d then (1 : ℝ) else 0) else 0) := by
          simp only [Finset.sum_add_distrib]
    _ ≤ 2 * (N : ℝ)^2 + 2 * (N : ℝ)^2 := add_le_add hsum (by
      rw [Finset.sum_comm]
      exact hsum)
    _ = _ := by ring

theorem g4_proof : G4 := by
  intro N
  constructor
  · have hc (d : Dyad N) :
        ((univ.filter (fun f : Dyad N => (members d ∩ members f).Nonempty)).card : ℝ) =
          ∑ f : Dyad N, if overlap d f then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      congr 1
    simpa only [hc] using total_dyad_overlap_bound N
  · have hrow (P : Dyad N × Dyad N) :
        (∑ P' : Dyad N × Dyad N, if (pairSupport P ∩ pairSupport P').Nonempty then (1 : ℝ) else 0) ≤
          if overlap P.1 P.2 then 12 * (N : ℝ)^2 else 0 := by
      by_cases hP : overlap P.1 P.2
      · rw [if_pos hP]
        calc
          _ ≤ (pairSupport P).card * (4 * (N : ℝ)^2) :=
            support_overlap_row_bound pairSupport (pairSupport P) _
              (fun x _ => incident_pair_bound N x)
          _ ≤ 3 * (4 * (N : ℝ)^2) := by
            gcongr
            exact_mod_cast pairSupport_card_le P
          _ = _ := by ring
      · simp [pairSupport, hP]
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun P _ => hrow P)
    have heq : (∑ P : Dyad N × Dyad N, if overlap P.1 P.2 then 12 * (N : ℝ)^2 else 0) =
        (12 * (N : ℝ)^2) * (∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then (1 : ℝ) else 0) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      split_ifs <;> simp
    have ht := mul_le_mul_of_nonneg_left (total_dyad_overlap_bound N)
      (show 0 ≤ 12 * (N : ℝ)^2 by positivity)
    rw [heq] at hsum
    have hh := hsum.trans ht
    convert hh using 1
    · simp only [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_one]
    · ring

end
end AronowAudit.P018.Wave1.WeightedConsistency
