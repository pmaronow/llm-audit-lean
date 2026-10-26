import AronowAudit.P009.Wave1.Gap.GP0092B2

/-! P009-T40: preserve an arbitrary design and its positive limsup density while
constructing bounded outcomes for which both estimators are inconsistent. -/
namespace AronowAudit.P009.Wave1

open scoped BigOperators Topology
open Filter

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

private lemma unrestricted_density_bounds {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    0 ≤ dAvg E / (n : ℝ) ∧ dAvg E / (n : ℝ) ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd (i j : Fin n) : 0 ≤ d E i j ∧ d E i j ≤ 1 := by
    unfold d
    split_ifs <;> norm_num
  have hnon : 0 ≤ dAvg E := by
    apply div_nonneg _ hnR.le
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hd i j).1))
  have hupper : dAvg E ≤ (n : ℝ) := by
    apply (div_le_iff₀ hnR).2
    calc
      _ ≤ ∑ _ : Fin n, ∑ _ : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => (hd i j).2))
      _ = _ := by simp
  exact ⟨div_nonneg hnon hnR.le, (div_le_one hnR).2 hupper⟩

/-- The infimum of eventual upper bounds gives the actual limsup, without
requiring the sequence to attain its limsup infinitely often. -/
private lemma unrestricted_positive_limsup (a : ℕ → ℝ)
    (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1) (hFail : ¬ Tendsto a atTop (nhds 0)) :
    ∃ L, (0 < L ∧ L ≤ 1) ∧ HasLimsup a L := by
  let U : Set ℝ := {b | ∀ᶠ t in atTop, a t ≤ b}
  have hU : U.Nonempty := ⟨1, Eventually.of_forall (fun t => (ha t).2)⟩
  have hlow : ∀ b ∈ U, 0 ≤ b := by
    intro b hb
    obtain ⟨t, ht⟩ := hb.exists
    exact (ha t).1.trans ht
  have hbounded : BddBelow U := ⟨0, hlow⟩
  let L := sInf U
  have hL0 : 0 ≤ L := le_csInf hU hlow
  have hL1 : L ≤ 1 := csInf_le hbounded (Eventually.of_forall (fun t => (ha t).2))
  have hupper : ∀ ε > 0, ∀ᶠ t in atTop, a t < L + ε := by
    intro ε hε
    obtain ⟨b, hb, hbL⟩ := exists_lt_of_csInf_lt hU (show L < L + ε by linarith)
    exact hb.mono (fun t ht => ht.trans_lt hbL)
  have hlower : ∀ ε > 0, ∃ᶠ t in atTop, L - ε < a t := by
    intro ε hε
    by_contra h
    have hb : L - ε ∈ U := by
      change ∀ᶠ t in atTop, a t ≤ L - ε
      simpa only [not_frequently, not_lt] using h
    have := csInf_le hbounded hb
    change L ≤ L - ε at this
    linarith
  have hLpos : 0 < L := by
    by_contra h
    have hzero : L = 0 := le_antisymm (le_of_not_gt h) hL0
    apply hFail
    apply tendsto_order.2
    constructor
    · intro b hb
      exact Eventually.of_forall (fun t => hb.trans_le (ha t).1)
    · intro b hb
      simpa only [hzero, zero_add] using hupper b hb
  exact ⟨L, ⟨hLpos, hL1⟩, hupper, hlower⟩

private lemma unrestricted_hasLimsup_of_tendsto {a : ℕ → ℝ} {L : ℝ}
    (ha : Tendsto a atTop (nhds L)) : HasLimsup a L := by
  constructor
  · intro ε hε
    exact ha.eventually_lt_const (by linarith)
  · intro ε hε
    exact (ha.eventually_const_lt (by linarith : L - ε < L)).frequently

/-- Only marginal overlap is needed from the original design. The reference
experiment has zero outcomes, so it supplies its own moment bounds. -/
private lemma unrestricted_zero_regular {n : ℕ} (E : Experiment n) (k : ℝ)
    (hk : 0 < k)
    (hA : ∀ i, k⁻¹ ≤ marginal E i true ∧ marginal E i true ≤ 1-k⁻¹) :
    Regular ({E with outcome := fun _ _ => 0} : Experiment n) k 2 1 := by
  refine ⟨hk, by norm_num, by norm_num, hA, ?_, ?_⟩
  · intro i
    simp only [Real.rpow_eq_pow, Real.rpow_two, abs_zero, zero_pow (by decide : 2 ≠ 0)]
    rw [mean_const]
    exact sq_nonneg k
  · intro i b
    simp only [potential, Real.rpow_eq_pow, Real.rpow_one, abs_zero]
    rw [mean_const]
    exact hk.le

private lemma unrestricted_mean_le_constant {Ω : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → ℝ) (c : ℝ) (h : ∀ ω, X ω ≤ c) : mean P X ≤ c := by
  calc
    _ ≤ mean P (fun _ => c) := Finset.sum_le_sum
      (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.nonneg ω))
    _ = c := mean_const P c

private lemma unrestricted_bounded_regular {n : ℕ} (E : Experiment n)
    (k K : ℝ) (hk : 0 < k) (hkK : k ≤ K)
    (hA : ∀ i, k⁻¹ ≤ marginal E i true ∧ marginal E i true ≤ 1-k⁻¹)
    (hy : ∀ i z, |E.outcome i z| ≤ K) : Regular E K 2 1 := by
  have hK : 0 < K := hk.trans_le hkK
  have hinv : K⁻¹ ≤ k⁻¹ := inv_anti₀ hk hkK
  refine ⟨hK, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hinv.trans (hA i).1, (hA i).2.trans (by linarith)⟩
  · intro i
    apply unrestricted_mean_le_constant
    intro z
    simp only [Real.rpow_eq_pow, Real.rpow_two]
    exact (sq_le_sq₀ (abs_nonneg _) hK.le).2 (hy i z)
  · intro i b
    apply unrestricted_mean_le_constant
    intro z
    simpa only [Real.rpow_eq_pow, Real.rpow_one, potential] using hy i (Function.update z i b)

private lemma unrestricted_ceiling_ratio_limit (S : Study) (L : ℝ) (hL : 0 < L) :
    Tendsto (fun t => (⌈Real.sqrt L * size S t⌉₊ : ℝ) / size S t)
      atTop (nhds (Real.sqrt L)) := by
  have hN : Tendsto (size S) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr S.grows
  have hi : Tendsto (fun t => 1 / size S t) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hN
  have hu : Tendsto (fun t => Real.sqrt L + 1 / size S t)
      atTop (nhds (Real.sqrt L)) := by
    simpa using tendsto_const_nhds.add hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · apply Eventually.of_forall
    intro t
    have hn : 0 < size S t := by dsimp [size]; exact_mod_cast S.positive t
    exact (le_div_iff₀ hn).2 (Nat.le_ceil _)
  · apply Eventually.of_forall
    intro t
    have hn : 0 < size S t := by dsimp [size]; exact_mod_cast S.positive t
    have hc := Nat.ceil_lt_add_one (mul_nonneg (Real.sqrt_nonneg L) hn.le)
    apply (div_le_iff₀ hn).2
    have he : (Real.sqrt L + 1 / size S t) * size S t =
        Real.sqrt L * size S t + 1 := by field_simp
    rw [he]
    exact hc.le

private lemma unrestricted_density_limit (S : Study) (L : ℝ) (hL : 0 < L) :
    Tendsto (fun t =>
      ((⌈Real.sqrt L * size S t⌉₊ : ℝ)^2 / size S t +
        (size S t - ⌈Real.sqrt L * size S t⌉₊) / size S t) / size S t)
      atTop (nhds L) := by
  have hr := unrestricted_ceiling_ratio_limit S L hL
  have hN : Tendsto (size S) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr S.grows
  have hi : Tendsto (fun t => 1 / size S t) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hN
  have hh := (hr.pow 2).add (((tendsto_const_nhds (x := (1 : ℝ))).sub hr).mul hi)
  have hlim : Tendsto (fun t =>
      ((⌈Real.sqrt L * size S t⌉₊ : ℝ) / size S t)^2 +
        (1 - (⌈Real.sqrt L * size S t⌉₊ : ℝ) / size S t) * (1 / size S t))
      atTop (nhds L) := by
    simpa only [Real.sq_sqrt hL.le, mul_zero, add_zero] using hh
  apply hlim.congr'
  apply Eventually.of_forall
  intro t
  have hn : size S t ≠ 0 := by
    dsimp [size]
    exact_mod_cast (S.positive t).ne'
  field_simp [hn]

private lemma unrestricted_tail_obstruction (S : Study)
    (X : (t : ℕ) → Assignment (S.N t) → ℝ) (ε c : ℝ)
    (hε : 0 < ε) (hc : 0 < c)
    (hbound : ∀ t, c ≤ prob (S.experiment t).design (fun z => ε < |X t z|)) :
    ¬ InProbability S X := by
  intro h
  have he := (h ε hε).eventually_lt_const hc
  obtain ⟨t, ht⟩ := he.exists
  exact (not_lt_of_ge (hbound t)) ht

/-- P009-T40: the same designs and the same positive limsup interference density
admit bounded outcomes with inconsistent HT and Hájek estimators. -/
theorem unrestricted_inconsistency_proof (S : Study) (k : ℝ) (hk : 0 < k)
    (hA : ∀ t i, k⁻¹ ≤ marginal (S.experiment t) i true ∧
      marginal (S.experiment t) i true ≤ 1-k⁻¹) (hFail : ¬ Restricted S) :
    ∃ y : (t : ℕ) → Fin (S.N t) → Assignment (S.N t) → ℝ,
      let S' : Study := {S with experiment := fun t =>
        {S.experiment t with outcome := y t}}
      (∃ K q s, RegularSequence S' K q s) ∧
      (∃ L > 0, HasLimsup (fun t => dAvg (S.experiment t)/size S t) L ∧
        HasLimsup (fun t => dAvg (S'.experiment t)/size S' t) L) ∧
      ¬ InProbability S' (fun t z => ht (S'.experiment t) z-eate (S'.experiment t)) ∧
      ¬ InProbability S' (fun t z => hajek (S'.experiment t) z-eate (S'.experiment t)) := by
  obtain ⟨L, hL, hlim⟩ := unrestricted_positive_limsup
    (fun t => dAvg (S.experiment t) / size S t)
    (fun t => unrestricted_density_bounds (S.positive t) (S.experiment t)) hFail
  let E0 : (t : ℕ) → Experiment (S.N t) := fun t =>
    {S.experiment t with outcome := fun _ _ => 0}
  let M : ℕ → ℕ := fun t => ⌈Real.sqrt L * size S t⌉₊
  let y : (t : ℕ) → Fin (S.N t) → Assignment (S.N t) → ℝ :=
    fun t => p1Outcome (S.positive t) (E0 t) (M t)
  let S' : Study := {S with experiment := fun t => {S.experiment t with outcome := y t}}
  have hfinite (t : ℕ) := construction_p1_proof (S.positive t) (E0 t) k 2 1 L
    (unrestricted_zero_regular (S.experiment t) k hk (hA t)) hL
  have hgraph (t : ℕ) : dAvg (S'.experiment t) =
      (M t : ℝ)^2 / size S t + (size S t - M t) / size S t := (hfinite t).1
  have hbound (t) (i) (z) : |(S'.experiment t).outcome i z| ≤ 1 / Real.sqrt L :=
    (hfinite t).2.2.1 i z
  have hht (t) (z) : k⁻¹ ≤ |ht (S'.experiment t) z - eate (S'.experiment t)| :=
    ((hfinite t).2.2.2.2.1 z).2
  have hhajek (t) : k⁻¹ ≤ prob (S'.experiment t).design
      (fun z => k⁻¹ ≤ |hajek (S'.experiment t) z - eate (S'.experiment t)|) :=
    (hfinite t).2.2.2.2.2
  refine ⟨y, ?_⟩
  change (∃ K q s, RegularSequence S' K q s) ∧ _
  refine ⟨?_, ⟨L, hL.1, hlim, ?_⟩, ?_, ?_⟩
  · refine ⟨max k (1 / Real.sqrt L), 2, 1, fun t => ?_⟩
    apply unrestricted_bounded_regular (S'.experiment t) k _ hk (le_max_left _ _)
    · exact hA t
    · intro i z
      exact (hbound t i z).trans (le_max_right _ _)
  · apply unrestricted_hasLimsup_of_tendsto
    have hh := unrestricted_density_limit S L hL.1
    exact hh.congr (fun t => by rw [show size S' t = size S t from rfl, hgraph])
  · apply unrestricted_tail_obstruction S' _ (k⁻¹ / 2) 1 (by positivity) (by norm_num)
    intro t
    have he : prob (S'.experiment t).design
        (fun z => k⁻¹ / 2 < |ht (S'.experiment t) z - eate (S'.experiment t)|) = 1 := by
      unfold prob
      have hall (z) : k⁻¹ / 2 < |ht (S'.experiment t) z - eate (S'.experiment t)| := by
        have hp : 0 < k⁻¹ := inv_pos.2 hk
        linarith [hht t z]
      simp only [ite_eq_left (hall _)]
      exact mean_const _ 1
    exact he.ge
  · apply unrestricted_tail_obstruction S' _ (k⁻¹ / 2) k⁻¹ (by positivity) (inv_pos.2 hk)
    intro t
    apply (hhajek t).trans
    apply finite_probability_mono
    intro z hz
    have hp : 0 < k⁻¹ := inv_pos.2 hk
    linarith

end
end AronowAudit.P009.Wave1
