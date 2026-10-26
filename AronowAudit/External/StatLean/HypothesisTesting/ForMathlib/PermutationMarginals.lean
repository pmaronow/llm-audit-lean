/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Prod



/-!
# One- and two-coordinate marginals of a uniform random permutation

A permutation test relabels the pooled data by a uniform random permutation `σ` of the `N`
observations, so every statistic it computes is an average over `Perm (Fin N)` of a function
of finitely many *relabelled coordinates*. The whole first- and second-moment calculus of
such statistics rests on two facts, which is what this file records: under a uniform `σ`,

* a single coordinate is uniform on the `N` items,
  $$ |\mathbf{S}_N|^{-1} \sum_\sigma h(\sigma u) = N^{-1} \sum_l h(l); $$
* a pair of *distinct* coordinates is uniform on the `N(N-1)` ordered pairs of distinct
  items,
  $$ |\mathbf{S}_N|^{-1} \sum_\sigma h(\sigma u, \sigma v)
     = \bigl(N(N-1)\bigr)^{-1} \sum_{l \ne l'} h(l, l') \qquad (u \ne v) . $$

Both are proved by the same two-step argument: all fibres of `σ ↦ σ u` (resp.
`σ ↦ (σ u, σ v)`) have the same cardinality, because left multiplication by a
transposition, `σ ↦ (l l′)σ` (resp. by a permutation `ρ` carrying one output pair to the
other, `σ ↦ ρσ`), maps one fibre bijectively onto another; and the fibres partition the
group, which pins the common cardinality down without ever computing a factorial.

## Main results

* `avg_perm_apply` — the one-coordinate marginal is uniform.
* `avg_perm_apply_pair` — the two-coordinate marginal is uniform on the off-diagonal.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 12 (Extensions of the
CLT to Sums of Dependent Random Variables), §12.2 (Random Sampling Without Replacement from a
Finite Population). (`TSH4 §12.2`.)

**Proof formalization notes.**
* This is the *permutation* model of sampling without replacement: expectations are
  normalized sums over the permutation group.
* No factorial is ever computed: the fibre cardinality `C` is left as an unknown, and the
  partition identity `|Perm α| = N · C` (resp. `N(N-1) · C`) is what cancels it. This keeps
  every statement free of `Nat.factorial` and of the `m > n` edge conventions.

**Bibliographic comments.** The moment computations for sampling without replacement, and
the combinatorial central limit theorem they support, are due to A. Wald and J. Wolfowitz,
"Statistical tests based on permutations of the observations," *Ann. Math. Statist.* **15**
(1944), 358–372, and W. Hoeffding, "A combinatorial central limit theorem," *Ann. Math.
Statist.* **22** (1951), 558–566. The randomization model itself goes back to R. A. Fisher,
*The Design of Experiments*, Oliver & Boyd, 1935, and E. J. G. Pitman, "Significance tests
which may be applied to samples from any populations," *Suppl. J. Roy. Statist. Soc.* **4**
(1937), 119–130.
-/

namespace StatLean.HypothesisTesting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### One coordinate -/

/-- All fibres of `σ ↦ σ u` have the same cardinality: left multiplication by the
transposition `(l l')` carries one onto another. -/
private lemma card_fiber_perm_apply (u l l' : α) :
    (Finset.univ.filter fun σ : Equiv.Perm α => σ u = l).card
      = (Finset.univ.filter fun σ : Equiv.Perm α => σ u = l').card := by
  classical
  refine Finset.card_bij' (fun σ _ => Equiv.swap l l' * σ) (fun σ _ => Equiv.swap l l' * σ)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    simp [hσ, Equiv.swap_apply_left]
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    simp [hσ, Equiv.swap_apply_right]
  · intro σ _
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  · intro σ _
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]

/-- **The one-coordinate marginal of a uniform random permutation is uniform.** -/
theorem avg_perm_apply (u : α) (h : α → ℝ) :
    (Fintype.card (Equiv.Perm α) : ℝ)⁻¹ * ∑ σ : Equiv.Perm α, h (σ u)
      = (Fintype.card α : ℝ)⁻¹ * ∑ l, h l := by
  classical
  set C : ℕ := (Finset.univ.filter fun σ : Equiv.Perm α => σ u = u).card with hC
  have hCpos : 0 < C := by
    rw [hC, Finset.card_pos]
    exact ⟨1, by simp⟩
  have hfib : ∀ l : α, (Finset.univ.filter fun σ : Equiv.Perm α => σ u = l).card = C :=
    fun l => card_fiber_perm_apply u l u
  have hmaps : ∀ σ : Equiv.Perm α, σ ∈ (Finset.univ : Finset (Equiv.Perm α)) →
      σ u ∈ (Finset.univ : Finset α) := fun σ _ => Finset.mem_univ _
  -- the group is the disjoint union of the fibres
  have hcard : Fintype.card (Equiv.Perm α) = Fintype.card α * C := by
    have h1 := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.sum_congr rfl fun l _ => hfib l, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h1
    simpa [Finset.card_univ] using h1
  -- the sum, computed fibrewise
  have hsum : ∑ σ : Equiv.Perm α, h (σ u) = (C : ℝ) * ∑ l, h l := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun σ => h (σ u)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hinner : (∑ σ ∈ Finset.univ.filter fun σ : Equiv.Perm α => σ u = l, h (σ u))
        = ∑ _σ ∈ Finset.univ.filter fun σ : Equiv.Perm α => σ u = l, h l :=
      Finset.sum_congr rfl fun σ hσ => by
        rw [(Finset.mem_filter.1 hσ).2]
    rw [hinner, Finset.sum_const, hfib l, nsmul_eq_mul]
  have hNpos : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨u⟩
  have hCR : (C : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hCpos.ne'
  have hNR : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
  rw [hsum, hcard, Nat.cast_mul]
  field_simp

/-! ### Two distinct coordinates -/

omit [Fintype α] [DecidableEq α] in
/-- Two prescribed values can be realised by a permutation: for `l ≠ l'` and `p ≠ p'` there
is a `ρ` with `ρ l = p` and `ρ l' = p'`. -/
private lemma exists_perm_apply_apply {l l' p p' : α} (hl : l ≠ l') (hp : p ≠ p') :
    ∃ ρ : Equiv.Perm α, ρ l = p ∧ ρ l' = p' := by
  classical
  set q : α := Equiv.swap l p l' with hq
  have hqp : q ≠ p := by
    rw [hq]
    intro hcon
    have h1 : Equiv.swap l p l' = Equiv.swap l p l := by rw [hcon, Equiv.swap_apply_left]
    exact hl ((Equiv.swap l p).injective h1).symm
  refine ⟨Equiv.swap q p' * Equiv.swap l p, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hqp) hp]
  · rw [Equiv.Perm.mul_apply, ← hq, Equiv.swap_apply_left]

/-- All fibres of `σ ↦ (σ u, σ v)` over the off-diagonal have the same cardinality. -/
private lemma card_fiber_perm_apply_pair (u v : α) {l l' p p' : α}
    (hl : l ≠ l') (hp : p ≠ p') :
    (Finset.univ.filter fun σ : Equiv.Perm α => σ u = l ∧ σ v = l').card
      = (Finset.univ.filter fun σ : Equiv.Perm α => σ u = p ∧ σ v = p').card := by
  classical
  obtain ⟨ρ, hρ1, hρ2⟩ := exists_perm_apply_apply hl hp
  refine Finset.card_bij' (fun σ _ => ρ * σ) (fun σ _ => ρ⁻¹ * σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact ⟨by simp [hσ.1, hρ1], by simp [hσ.2, hρ2]⟩
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    refine ⟨?_, ?_⟩
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hσ.1, ← hρ1]
      simp
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hσ.2, ← hρ2]
      simp
  · intro σ _
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  · intro σ _
    rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- **The two-coordinate marginal of a uniform random permutation is uniform on the ordered
pairs of distinct items.** -/
theorem avg_perm_apply_pair {u v : α} (huv : u ≠ v) (h : α → α → ℝ) :
    (Fintype.card (Equiv.Perm α) : ℝ)⁻¹ * ∑ σ : Equiv.Perm α, h (σ u) (σ v)
      = ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))⁻¹ *
        ∑ p ∈ (Finset.univ : Finset α).offDiag, h p.1 p.2 := by
  classical
  have hN2 : 2 ≤ Fintype.card α := Fintype.one_lt_card_iff_nontrivial.2 ⟨⟨u, v, huv⟩⟩
  have hNR : (2 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hN2
  set t : Finset (α × α) := (Finset.univ : Finset α).offDiag with ht
  have htcard : t.card = Fintype.card α * Fintype.card α - Fintype.card α := by
    rw [ht, Finset.offDiag_card, Finset.card_univ]
  have htcardR : (t.card : ℝ) = (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) := by
    rw [htcard, Nat.cast_sub (Nat.le_mul_of_pos_left _ (Fintype.card_pos_iff.2 ⟨u⟩)),
      Nat.cast_mul]
    ring
  have hmem : ∀ p ∈ t, p.1 ≠ p.2 := fun p hp => (Finset.mem_offDiag.1 (ht ▸ hp)).2.2
  have hmaps : ∀ σ : Equiv.Perm α, σ ∈ (Finset.univ : Finset (Equiv.Perm α)) →
      (σ u, σ v) ∈ t := by
    intro σ _
    rw [ht, Finset.mem_offDiag]
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, fun hcon => huv (σ.injective hcon)⟩
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : α × α, p₀ ∈ t := ⟨(u, v), hmaps 1 (Finset.mem_univ _)⟩
  -- the fibrewise sums use the `Prod`-equality form of the fibre
  have hpr : ∀ p : α × α, (Finset.univ.filter fun σ : Equiv.Perm α => (σ u, σ v) = p)
      = (Finset.univ.filter fun σ : Equiv.Perm α => σ u = p.1 ∧ σ v = p.2) := by
    intro p
    refine Finset.filter_congr fun σ _ => ?_
    simp [Prod.ext_iff]
  set C : ℕ := (Finset.univ.filter fun σ : Equiv.Perm α => (σ u, σ v) = p₀).card with hC
  have hfib : ∀ p ∈ t,
      (Finset.univ.filter fun σ : Equiv.Perm α => (σ u, σ v) = p).card = C := by
    intro p hp
    rw [hpr p, hC, hpr p₀]
    exact card_fiber_perm_apply_pair u v (hmem p hp) (hmem p₀ hp₀)
  have hCpos : 0 < C := by
    rw [hC, hpr p₀, Finset.card_pos]
    obtain ⟨ρ, hρ1, hρ2⟩ := exists_perm_apply_apply huv (hmem p₀ hp₀)
    exact ⟨ρ, by simp [hρ1, hρ2]⟩
  have hcard : Fintype.card (Equiv.Perm α) = t.card * C := by
    have h1 := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.sum_congr rfl fun p hp => hfib p hp, Finset.sum_const, nsmul_eq_mul] at h1
    simpa [Finset.card_univ] using h1
  have hsum : ∑ σ : Equiv.Perm α, h (σ u) (σ v) = (C : ℝ) * ∑ p ∈ t, h p.1 p.2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun σ => h (σ u) (σ v)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hinner : (∑ σ ∈ Finset.univ.filter fun σ : Equiv.Perm α => (σ u, σ v) = p,
          h (σ u) (σ v))
        = ∑ _σ ∈ Finset.univ.filter fun σ : Equiv.Perm α => (σ u, σ v) = p, h p.1 p.2 :=
      Finset.sum_congr rfl fun σ hσ => by
        have hσ2 := (Finset.mem_filter.1 hσ).2
        rw [show σ u = p.1 from by rw [← hσ2], show σ v = p.2 from by rw [← hσ2]]
    rw [hinner, Finset.sum_const, hfib p hp, nsmul_eq_mul]
  have hCR : (C : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hCpos.ne'
  have htR : (t.card : ℝ) ≠ 0 := by
    rw [htcardR]
    have : (0 : ℝ) < (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) := by
      apply mul_pos <;> linarith
    exact this.ne'
  rw [hsum, hcard, Nat.cast_mul, htcardR]
  rw [htcardR] at htR
  field_simp




end StatLean.HypothesisTesting
