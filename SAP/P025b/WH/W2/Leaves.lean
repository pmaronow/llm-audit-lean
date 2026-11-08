import SAP.P025b.Defs.WholeW2
import SAP.P025b.Bridge
import AronowAudit.P025.P025_Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P025b.WH.W2
open scoped BigOperators

/-- The finite numerator and denominator of any two-level vector have
the printed prefix/tail formulas, including `k = 0`, `k = n`, and `n = 0`.
Split each sum with `Finset.sum_ite`; the prefix has `k` elements and its
complement has `n-k` elements. Alternatively, induct on `k ≤ n`, using
`AronowAudit.P025.threshold_sum_update` and
`AronowAudit.P025.threshold_den_update`, starting with the constant vector.
Only finite-sum algebra and natural-to-real casts are needed. -/
def T19_L1 : Prop :=
  ∀ {n : ℕ} (y : Fin n → ℝ) (l b : ℝ) (k : ℕ), k ≤ n →
    (∑ i : Fin n, (if i.val < k then l else b) * y i) =
      l * t19Prefix y k + b * t19Tail y k ∧
    (∑ i : Fin n, if i.val < k then l else b) =
      l * (k : ℝ) + b * ((n : ℝ) - (k : ℝ))

/-- A nonconstant sorted nonempty real sample has mean strictly above
its first outcome. Choose an outcome different from the first; monotonicity
makes it strictly greater. Apply `Finset.sum_lt_sum` to the constant first
outcome and the sample, then divide by the positive sample size. This is
the strict part of Supplement step (ii); no separation or strict ratio
assumption is needed. -/
def T19_L2 : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ), Monotone y →
    (¬ ∀ i, y i = y ⟨0, hn⟩) → y ⟨0, hn⟩ < populationMean y

/-- Assemble all clauses of Lemma 1 and its Supplement proof. The leaves
provide only finite moment formulas and strict nonconstant averaging;
cut existence, optimality, separation, and residual propagation use the
existing project results. -/
theorem T19_assembly (h1 : T19_L1) (h2 : T19_L2) : T19WholeStatement := by
  intro n hn y hy α β hα hab hb1
  dsimp only
  let γ := β / α
  let FH := upperValue y (fun _ => 1) γ
  let FL := lowerValue y (fun _ => 1) γ
  have hn0 : 0 < n := by omega
  let first : Fin n := ⟨0, hn0⟩
  let : Nonempty (Fin n) := ⟨first⟩
  have hβ : 0 < β := hα.trans_le hab
  have hγ : 1 ≤ γ := (le_div_iff₀ hα).2 (by simpa using hab)
  have hγp : 0 < γ := lt_of_lt_of_le zero_lt_one hγ
  have hscale : (1 / β) * γ = 1 / α := by
    dsimp [γ]
    field_simp
  have hnumH (k : ℕ) (hk : k ≤ n) :
      (∑ i, upperWeights γ k i * y i) = t19Prefix y k + γ * t19Tail y k := by
    simpa only [upperWeights, one_mul] using (h1 y 1 γ k hk).1
  have hnumL (k : ℕ) (hk : k ≤ n) :
      (∑ i, lowerWeights γ k i * y i) = γ * t19Prefix y k + t19Tail y k := by
    simpa only [lowerWeights, one_mul] using (h1 y γ 1 k hk).1
  have hsumH (k : ℕ) (hk : k ≤ n) :
      (∑ i : Fin n, upperWeights γ k i) = t19UpperDen n γ k := by
    simpa only [upperWeights, t19UpperDen, one_mul] using (h1 y 1 γ k hk).2
  have hsumL (k : ℕ) (hk : k ≤ n) :
      (∑ i : Fin n, lowerWeights γ k i) = t19LowerDen n γ k := by
    simpa only [lowerWeights, t19LowerDen, one_mul] using (h1 y γ 1 k hk).2
  have hposH (k : ℕ) : 0 < ∑ i : Fin n, upperWeights γ k i := by
    apply Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    simp only [upperWeights]
    split <;> positivity
  have hposL (k : ℕ) : 0 < ∑ i : Fin n, lowerWeights γ k i := by
    apply Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    simp only [lowerWeights]
    split <;> positivity
  have hDH (k : ℕ) (hk : k ≤ n) : 0 < t19UpperDen n γ k := by
    rw [← hsumH k hk]
    exact hposH k
  have hDL (k : ℕ) (hk : k ≤ n) : 0 < t19LowerDen n γ k := by
    rw [← hsumL k hk]
    exact hposL k
  have hFH (k : ℕ) (hk : k ≤ n) :
      FH k = (t19Prefix y k + γ * t19Tail y k) / t19UpperDen n γ k := by
    dsimp only [FH, upperValue, ratio]
    simp only [one_mul]
    rw [hnumH k hk, hsumH k hk]
  have hFL (k : ℕ) (hk : k ≤ n) :
      FL k = (γ * t19Prefix y k + t19Tail y k) / t19LowerDen n γ k := by
    dsimp only [FL, lowerValue, ratio]
    simp only [one_mul]
    rw [hnumL k hk, hsumL k hk]
  constructor
  · intro k hk
    exact ⟨hDH k hk, hDL k hk, hFH k hk, hFL k hk⟩
  obtain ⟨kL, kH, hL, hH, hwL, hwH, heL, heH, hleast, hgreatest, _, _, _⟩ :=
    AronowAudit.P025.corrected_weighted_bounds hn0 y (fun _ => 1)
      (fun _ => zero_lt_one) hy α β hα hab hb1
  have hphysL (k : ℕ) (i : Fin n) :
      (1 / β) * lowerWeights γ k i = (if i.val < k then 1 / α else 1 / β) := by
    simp only [lowerWeights]
    split <;> simp only [hscale, mul_one]
  have hphysH (k : ℕ) (i : Fin n) :
      (1 / β) * upperWeights γ k i = (if i.val < k then 1 / β else 1 / α) := by
    simp only [upperWeights]
    split <;> simp only [hscale, mul_one]
  have htied (i j : Fin n) (hij : y i = y j) :
      (1 / β) * lowerWeights γ kL.val i = (1 / β) * lowerWeights γ kL.val j ∧
      (1 / β) * upperWeights γ kH.val i = (1 / β) * upperWeights γ kH.val j := by
    obtain ⟨hl, hh⟩ := AronowAudit.P025.tied_outcomes_equal_weights
      hn0 y hy γ hγ kL kH hL hH i j hij
    exact ⟨congrArg (fun v => (1 / β) * v) hl, congrArg (fun v => (1 / β) * v) hh⟩
  refine ⟨kL, kH, hL, hH, ?_, ?_, hwL, hwH, ?_, ?_, htied, ?_, ?_, ?_, ?_, ?_⟩
  · intro jL jH hjL hjH
    exact ⟨hjL.unique hL, hjH.unique hH⟩
  · intro i
    exact ⟨hphysL kL.val i, hphysH kH.val i⟩
  · change IsLeast (AronowAudit.P025.attainable y (fun _ => 1) α β)
      (AronowAudit.P025.ratio y (fun _ => 1)
        (fun i => (1 / β) * AronowAudit.P025.lowerWeights (β / α) kL.val i))
    rw [heL]
    exact hleast
  · change IsGreatest (AronowAudit.P025.attainable y (fun _ => 1) α β)
      (AronowAudit.P025.ratio y (fun _ => 1)
        (fun i => (1 / β) * AronowAudit.P025.upperWeights (β / α) kH.val i))
    rw [heH]
    exact hgreatest
  · intro hstrict i j hij
    have hablt : α < β := by
      have := (lt_div_iff₀ hα).1 hstrict
      simpa using this
    have hne : (1 / β : ℝ) ≠ 1 / α :=
      ne_of_lt (one_div_lt_one_div_of_lt hα hablt)
    have hiff (k : Fin n) (l b : ℝ) (hlb : l ≠ b) :
        ((if i.val < k.val then l else b) = (if j.val < k.val then l else b)) ↔
          k.val ≠ j.val := by
      by_cases hk : k.val = j.val
      · have hi : i.val < k.val := by omega
        have hj : ¬ j.val < k.val := by omega
        simp only [hi, hj, ite_true, ite_false]
        exact iff_of_false hlb (fun h => h hk)
      · have hs : i.val < k.val ↔ j.val < k.val := by omega
        have he : (if i.val < k.val then l else b) = (if j.val < k.val then l else b) := by
          simp only [hs]
        exact iff_of_true he hk
    have hiffL :
        ((1 / β) * lowerWeights γ kL.val i = (1 / β) * lowerWeights γ kL.val j) ↔
          kL.val ≠ j.val := by
      rw [hphysL, hphysL]
      exact hiff kL _ _ hne.symm
    have hiffH :
        ((1 / β) * upperWeights γ kH.val i = (1 / β) * upperWeights γ kH.val j) ↔
          kH.val ≠ j.val := by
      rw [hphysH, hphysH]
      exact hiff kH _ _ hne
    exact ⟨hiffL, hiffH, fun ht => ⟨hiffL.1 (htied i j ht).1, hiffH.1 (htied i j ht).2⟩⟩
  · intro c hc
    have htest : upperValue y (fun _ => 1) γ 0 ≤ y first := by
      apply AronowAudit.P025.ratio_le y (fun _ => 1) (upperWeights γ 0)
        (fun _ => zero_lt_one)
      · intro i
        simpa [upperWeights] using hγp
      · intro i
        rw [hc i, hc first]
    have hk : kH.val = 0 := by
      have hm : kH ≤ first := hH.2 htest
      change kH.val ≤ 0 at hm
      omega
    refine ⟨hk, ?_⟩
    intro i
    rw [hphysH, hk]
    simp
  · intro hnonconstant
    have hzero : FH 0 = populationMean y := by
      have hscaleRatio := AronowAudit.P025.ratio_scale_weights y (fun _ => 1)
        (fun _ => 1) γ hγp.ne'
      change AronowAudit.P025.ratio y (fun _ => 1) (fun _ => γ) =
        AronowAudit.P025.populationMean y
      simpa only [mul_one, AronowAudit.P025.ratio, one_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
        AronowAudit.P025.populationMean] using hscaleRatio
    have hmean : y first < FH 0 := by
      rw [hzero]
      exact h2 hn0 y hy hnonconstant
    refine ⟨hzero, hmean, ?_⟩
    by_contra hnot
    have hk : kH.val = 0 := by omega
    have hfirst : kH = first := Fin.ext hk
    have ht := hH.1
    change FH kH.val ≤ y kH at ht
    rw [hfirst] at ht
    exact (not_le_of_gt hmean) ht
  · intro i j hij hjcut htie
    have hi : i.val < kH.val := by omega
    have hfail : y i < FH i.val := by
      by_contra hnot
      have ht : FH i.val ≤ y i := le_of_not_gt hnot
      have hm := hH.2 ht
      change kH.val ≤ i.val at hm
      omega
    have hs := AronowAudit.P025.threshold_shift hn0 (fun _ => 1) y
      (fun _ => zero_lt_one) 1 γ zero_lt_one hγp i
    simp only [one_mul] at hs
    change FH (i.val + 1) - y i =
      ((∑ z, upperWeights γ i.val z) / (∑ z, upperWeights γ (i.val + 1) z)) *
        (FH i.val - y i) at hs
    rw [← hij, hsumH i.val (by omega), hsumH j.val (by omega)] at hs
    have hpositive : 0 < FH j.val - y i := by
      rw [hs]
      exact mul_pos (div_pos (hDH i.val (by omega)) (hDH j.val (by omega)))
        (sub_pos.2 hfail)
    have hnext : j.val + 1 ≤ kH.val := by
      by_contra hnot
      have heq : j = kH := Fin.ext (by omega)
      have ht := hH.1
      change FH kH.val ≤ y kH at ht
      rw [← heq, ← htie] at ht
      exact (not_le_of_gt (sub_pos.1 hpositive)) ht
    have hu := AronowAudit.P025.threshold_sum_update (fun _ : Fin n => (1 : ℝ)) y 1 γ i
    change (∑ z, 1 * upperWeights γ (i.val + 1) z * y z) =
      (∑ z, 1 * upperWeights γ i.val z * y z) + (1 - γ) * 1 * y i at hu
    simp only [one_mul, mul_one] at hu
    rw [← hij, hnumH j.val (by omega), hnumH i.val (by omega)] at hu
    have hrec : FH j.val =
        ((1 - γ) * y i + t19Prefix y i.val + γ * t19Tail y i.val) /
          t19UpperDen n γ j.val := by
      rw [hFH j.val (by omega), hu]
      congr 1
      ring
    have hdrec : t19UpperDen n γ j.val = t19UpperDen n γ i.val + (1 - γ) := by
      simp only [t19UpperDen, hij, Nat.cast_add, Nat.cast_one]
      ring
    have hbase : ((1 - γ) * y i + t19UpperDen n γ i.val * y i) /
        t19UpperDen n γ j.val = y i := by
      apply (div_eq_iff (hDH j.val (by omega)).ne').2
      rw [hdrec]
      ring
    exact ⟨hfail, hrec, hbase, by rw [hbase]; exact sub_pos.1 hpositive,
      hs, hpositive, by rw [← htie]; exact sub_pos.1 hpositive, hnext⟩
  · intro i j hij hjcut htie
    have hi : i.val < kL.val := by omega
    have hfail : y i < FL i.val := by
      by_contra hnot
      have ht : FL i.val ≤ y i := le_of_not_gt hnot
      have hm := hL.2 ht
      change kL.val ≤ i.val at hm
      omega
    have hs := AronowAudit.P025.threshold_shift hn0 (fun _ => 1) y
      (fun _ => zero_lt_one) γ 1 hγp zero_lt_one i
    simp only [one_mul] at hs
    change FL (i.val + 1) - y i =
      ((∑ z, lowerWeights γ i.val z) / (∑ z, lowerWeights γ (i.val + 1) z)) *
        (FL i.val - y i) at hs
    rw [← hij, hsumL i.val (by omega), hsumL j.val (by omega)] at hs
    have hpositive : 0 < FL j.val - y i := by
      rw [hs]
      exact mul_pos (div_pos (hDL i.val (by omega)) (hDL j.val (by omega)))
        (sub_pos.2 hfail)
    have hnext : j.val + 1 ≤ kL.val := by
      by_contra hnot
      have heq : j = kL := Fin.ext (by omega)
      have ht := hL.1
      change FL kL.val ≤ y kL at ht
      rw [← heq, ← htie] at ht
      exact (not_le_of_gt (sub_pos.1 hpositive)) ht
    refine ⟨hfail, ?_, hpositive, ?_, hnext⟩
    · rw [hs]
      ring
    · rw [← htie]
      exact sub_pos.1 hpositive

end SAP.P025b.WH.W2
