import AronowAudit.P004.Wave1.ObservationalCoverage.O2
import Mathlib.Topology.Order.Compact

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

private theorem activeO_dot (N : ℕ) (i : Fin N) (v : Fin 2 → ℝ) :
    dot (activeO N i) v = if activeGroup N i then v 0 else v 1 := by
  by_cases hi : activeGroup N i <;>
    simp [dot, activeO, hi, Fin.sum_univ_succ]

/-- Inject two nodes from each complete block.  The offset is 0 for H and 2 for L;
the unfinished block need not be counted. -/
private theorem two_per_block_card_lower (N r : ℕ) (hr : r ≤ 6)
    (P : Fin N → Prop)
    (hP : ∀ i : Fin N, i.val % 8 = r ∨ i.val % 8 = r + 1 → P i) :
    2 * (N / 8) ≤ (Finset.univ.filter P).card := by
  let f : Fin (2 * (N / 8)) → Fin N := fun i =>
    ⟨8 * (i.val / 2) + i.val % 2 + r, by
      have hi := i.isLt
      omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hval := congrArg Fin.val hij
    change 8 * (i.val / 2) + i.val % 2 + r =
      8 * (j.val / 2) + j.val % 2 + r at hval
    apply Fin.ext
    omega
  have hmem : ∀ i : Fin (2 * (N / 8)), f i ∈ Finset.univ.filter P := by
    intro i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hP (f i) ?_⟩
    change (8 * (i.val / 2) + i.val % 2 + r) % 8 = r ∨
      (8 * (i.val / 2) + i.val % 2 + r) % 8 = r + 1
    omega
  have hcard : (Finset.univ : Finset (Fin (2 * (N / 8)))).card ≤
      (Finset.univ.filter P).card := by
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      exact hmem i
    · intro i hi j hj hij
      exact hf hij
  simpa only [Finset.card_univ, Fintype.card_fin] using hcard

private theorem active_group_counts_lower (N : ℕ) (hN : 8 ≤ N) :
    (N : ℝ) / 8 ≤ nH N ∧ (N : ℝ) / 8 ≤ nL N := by
  have hH : 2 * (N / 8) ≤ (Finset.univ.filter (activeGroup N)).card := by
    apply two_per_block_card_lower N 0 (by omega) (activeGroup N)
    intro i hi
    change i.val % 8 < 2
    rcases hi with hi | hi <;> omega
  have hL : 2 * (N / 8) ≤ (Finset.univ.filter (fun i : Fin N => ¬ activeGroup N i)).card := by
    convert two_per_block_card_lower N 2 (by omega) (fun i => ¬ activeGroup N i) ?_
    intro i hi
    change ¬ i.val % 8 < 2
    rcases hi with hi | hi <;> omega
  have hblock : N ≤ 16 * (N / 8) := by omega
  have hHnat : N ≤ 8 * (Finset.univ.filter (activeGroup N)).card := by omega
  have hLnat : N ≤ 8 * (Finset.univ.filter (fun i : Fin N => ¬ activeGroup N i)).card := by
    omega
  have hHreal : (N : ℝ) ≤ 8 * nH N := by
    unfold nH
    exact_mod_cast hHnat
  have hLreal : (N : ℝ) ≤ 8 * nL N := by
    unfold nL
    exact_mod_cast hLnat
  constructor <;> linarith

private theorem active_gram_sum (N : ℕ) (v : Fin 2 → ℝ) :
    (∑ i : Fin N, (dot (activeO N i) v)^2) = nH N * (v 0)^2 + nL N * (v 1)^2 := by
  calc
    (∑ i : Fin N, (dot (activeO N i) v)^2) =
        (∑ i ∈ Finset.univ.filter (activeGroup N), (dot (activeO N i) v)^2) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ activeGroup N i),
          (dot (activeO N i) v)^2) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (activeGroup N)
        (fun i => (dot (activeO N i) v)^2)).symm
    _ = nH N * (v 0)^2 + nL N * (v 1)^2 := by
      congr 1
      · calc
          (∑ i ∈ Finset.univ.filter (activeGroup N), (dot (activeO N i) v)^2) =
              ∑ _i ∈ Finset.univ.filter (activeGroup N), (v 0)^2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [activeO_dot, if_pos (Finset.mem_filter.mp hi).2]
          _ = nH N * (v 0)^2 := by simp [nH, nsmul_eq_mul]
      · calc
          (∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ activeGroup N i),
              (dot (activeO N i) v)^2) =
              ∑ _i ∈ Finset.univ.filter (fun i : Fin N => ¬ activeGroup N i), (v 1)^2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [activeO_dot, if_neg (Finset.mem_filter.mp hi).2]
          _ = nL N * (v 1)^2 := by simp [nL, nsmul_eq_mul]

private theorem group_likelihood_formula {N : ℕ} (G : Finset (Fin N))
    (z : Assignment N) (t : ℝ) :
    (∑ i ∈ G, (bit (z i) * t - Real.log (1 + Real.exp t))) =
      (∑ i ∈ G, bit (z i)) * t - (G.card : ℝ) * Real.log (1 + Real.exp t) := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [Finset.sum_const, nsmul_eq_mul]

/-- An empty group has constant likelihood.  A nonempty group uses precisely O2,
with its observed treated count between zero and its cardinality. -/
private theorem group_likelihood_max {N : ℕ} (G : Finset (Fin N)) (z : Assignment N)
    (θ t : ℝ) (hθl : -Real.log 19 ≤ θ) (hθu : θ ≤ Real.log 19)
    (hselected : (G.card : ℝ) ≠ 0 →
      t = logit (clip ((∑ i ∈ G, bit (z i)) / (G.card : ℝ)))) :
    (∑ i ∈ G, (bit (z i) * θ - Real.log (1 + Real.exp θ))) ≤
      ∑ i ∈ G, (bit (z i) * t - Real.log (1 + Real.exp t)) := by
  by_cases hG : G.card = 0
  · have hGe : G = ∅ := Finset.card_eq_zero.mp hG
    simp only [hGe, Finset.sum_empty, le_refl]
  · have hn : (0 : ℝ) < (G.card : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hG)
    have hbit : ∀ i : Fin N, 0 ≤ bit (z i) ∧ bit (z i) ≤ 1 := by
      intro i
      cases hzi : z i <;> norm_num [bit, hzi]
    have hK : 0 ≤ ∑ i ∈ G, bit (z i) :=
      Finset.sum_nonneg fun i hi => (hbit i).1
    have hKn : (∑ i ∈ G, bit (z i)) ≤ (G.card : ℝ) := by
      calc
        (∑ i ∈ G, bit (z i)) ≤ ∑ _i ∈ G, (1 : ℝ) :=
          Finset.sum_le_sum fun i hi => (hbit i).2
        _ = (G.card : ℝ) := by simp
    rw [group_likelihood_formula G z θ, group_likelihood_formula G z t,
      hselected hn.ne']
    exact o2_proof.2.2 (G.card : ℝ) (∑ i ∈ G, bit (z i)) hn hK hKn θ hθl hθu

private theorem active_likelihood_separates (N : ℕ) (z : Assignment N) (θ : Fin 2 → ℝ) :
    (∑ i, (bit (z i) * dot (activeO N i) θ -
        Real.log (1 + Real.exp (dot (activeO N i) θ)))) =
      (∑ i ∈ Finset.univ.filter (activeGroup N),
        (bit (z i) * θ 0 - Real.log (1 + Real.exp (θ 0)))) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ activeGroup N i),
        (bit (z i) * θ 1 - Real.log (1 + Real.exp (θ 1))) := by
  calc
    _ = (∑ i ∈ Finset.univ.filter (activeGroup N),
          (bit (z i) * dot (activeO N i) θ - Real.log (1 + Real.exp (dot (activeO N i) θ)))) +
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ activeGroup N i),
          (bit (z i) * dot (activeO N i) θ - Real.log (1 + Real.exp (dot (activeO N i) θ))) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (activeGroup N)
        (fun i => bit (z i) * dot (activeO N i) θ -
          Real.log (1 + Real.exp (dot (activeO N i) θ)))).symm
    _ = _ := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [activeO_dot, if_pos (Finset.mem_filter.mp hi).2]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [activeO_dot, if_neg (Finset.mem_filter.mp hi).2]

theorem o3_proof : O3 := by
  have hlog19 : 0 ≤ Real.log 19 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 19)
  have hlog9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 9)
  have hlog_lt : Real.log 9 < Real.log 19 :=
    Real.log_lt_log (by norm_num : (0 : ℝ) < 9) (by norm_num : (9 : ℝ) < 19)
  have htrue : activeTheta ∈ activeParameterSet := by
    intro j
    fin_cases j
    · change -Real.log 19 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ Real.log 19
      constructor <;> linarith
    · change -Real.log 19 ≤ -Real.log 9 ∧ -Real.log 9 ≤ Real.log 19
      constructor <;> linarith
  have hcompact : IsCompact activeParameterSet := by
    have hbox : activeParameterSet =
        Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-Real.log 19) (Real.log 19)) := by
      ext θ
      simp only [activeParameterSet, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]
    rw [hbox]
    exact isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc
  refine ⟨hcompact, htrue, ?_, ?_, ?_⟩
  · refine ⟨1, ?_⟩
    intro N i j
    by_cases hi : activeGroup N i <;> fin_cases j <;> norm_num [activeO, hi]
  · refine ⟨1 / 8, by norm_num, ?_⟩
    filter_upwards [eventually_ge_atTop 8] with N hN
    intro v
    obtain ⟨hH, hL⟩ := active_group_counts_lower N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (by omega : 0 < N)
    rw [active_gram_sum, Fin.sum_univ_two]
    apply (le_div_iff₀ hNpos).2
    calc
      (1 / 8 : ℝ) * ((v 0)^2 + (v 1)^2) * N =
          ((N : ℝ) / 8) * (v 0)^2 + ((N : ℝ) / 8) * (v 1)^2 := by ring
      _ ≤ nH N * (v 0)^2 + nL N * (v 1)^2 :=
        add_le_add (mul_le_mul_of_nonneg_right hH (sq_nonneg (v 0)))
          (mul_le_mul_of_nonneg_right hL (sq_nonneg (v 1)))
  · intro N z
    constructor
    · intro j
      fin_cases j
      · change -Real.log 19 ≤ (if nH N = 0 then 0 else logit (pHatH N z)) ∧
          (if nH N = 0 then 0 else logit (pHatH N z)) ≤ Real.log 19
        by_cases hn : nH N = 0
        · rw [if_pos hn]
          exact htrue 0
        · rw [if_neg hn]
          exact o2_proof.1 (KAct N z / nH N)
      · change -Real.log 19 ≤ (if nL N = 0 then -Real.log 9 else logit (pHatL N z)) ∧
          (if nL N = 0 then -Real.log 9 else logit (pHatL N z)) ≤ Real.log 19
        by_cases hn : nL N = 0
        · rw [if_pos hn]
          exact htrue 1
        · rw [if_neg hn]
          exact o2_proof.1 (JAct N z / nL N)
    · intro θ hθ
      let H : Finset (Fin N) := Finset.univ.filter (activeGroup N)
      let L : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => ¬ activeGroup N i)
      have hK : KAct N z = ∑ i ∈ H, bit (z i) := by
        dsimp only [H]
        simp only [KAct, Finset.sum_filter]
      have hJ : JAct N z = ∑ i ∈ L, bit (z i) := by
        dsimp only [L]
        simp only [JAct, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hg : activeGroup N i <;> simp only [hg, if_true, if_false, not_true_eq_false,
          not_false_eq_true]
      have hfitH : (H.card : ℝ) ≠ 0 → activeMLE N z 0 =
          logit (clip ((∑ i ∈ H, bit (z i)) / (H.card : ℝ))) := by
        intro hH
        have hn : nH N ≠ 0 := hH
        change (if nH N = 0 then 0 else logit (pHatH N z)) = _
        simp only [if_neg hn, pHatH, hK]
        rfl
      have hfitL : (L.card : ℝ) ≠ 0 → activeMLE N z 1 =
          logit (clip ((∑ i ∈ L, bit (z i)) / (L.card : ℝ))) := by
        intro hL
        have hn : nL N ≠ 0 := hL
        change (if nL N = 0 then -Real.log 9 else logit (pHatL N z)) = _
        simp only [if_neg hn, pHatL, hJ]
        rfl
      have hmaxH := group_likelihood_max H z (θ 0) (activeMLE N z 0)
        (hθ 0).1 (hθ 0).2 hfitH
      have hmaxL := group_likelihood_max L z (θ 1) (activeMLE N z 1)
        (hθ 1).1 (hθ 1).2 hfitL
      rw [active_likelihood_separates N z θ,
        active_likelihood_separates N z (activeMLE N z)]
      exact add_le_add hmaxH hmaxL

end
end AronowAudit.P004.Wave1.ObservationalCoverage
