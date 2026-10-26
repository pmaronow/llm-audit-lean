import AronowAudit.P009.Wave1.Lib.UniformSpacingBridge

/-! Exact sampling variances for arbitrary adjacent-rank pairing selectors.
Their values agree off the null tie set with a bounded Borel statistic. -/
namespace AronowAudit.P009.Wave1
open MeasureTheory
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem tc01_twice_half (n : ℕ) (heven : Even n) : 2 * (n / 2) = n := by
  rcases heven with ⟨m, hm⟩
  omega

def tc01_lo {n : ℕ} (heven : Even n) (j : Fin (n / 2)) : Fin n :=
  ⟨2 * j.val, by have := tc01_twice_half n heven; have := j.isLt; omega⟩

def tc01_hi {n : ℕ} (heven : Even n) (j : Fin (n / 2)) : Fin n :=
  ⟨2 * j.val + 1, by have := tc01_twice_half n heven; have := j.isLt; omega⟩

/-- Reindex every unit of an arbitrary adjacent-rank pairing by its rank pair. -/
theorem tc01_pair_reindex {n : ℕ} (heven : Even n) (x b : Fin n → ℝ)
    (hx : Function.Injective x) (ρ : Pairing n) (hr : AdjacentRanks x ρ) :
    (∑ i, (b i - b (ρ.partner i))^2) =
      2 * ∑ j : Fin (n / 2),
        (b (Tuple.sort x (tc01_lo heven j)) - b (Tuple.sort x (tc01_hi heven j)))^2 := by
  obtain ⟨σ, hσ, hp⟩ := hr
  have hσeq : σ = Tuple.sort x := by
    apply Equiv.ext
    intro i
    exact hx (congrFun (Tuple.unique_monotone hσ (Tuple.monotone_sort x)) i)
  subst σ
  have hp0 (j : Fin (n / 2)) :
      ρ.partner (Tuple.sort x (tc01_lo heven j)) = Tuple.sort x (tc01_hi heven j) := by
    apply hp
    · simp only [tc01_lo, tc01_hi]
      omega
    · intro h
      have := congrArg Fin.val h
      simp only [tc01_lo, tc01_hi] at this
      omega
  have hp1 (j : Fin (n / 2)) :
      ρ.partner (Tuple.sort x (tc01_hi heven j)) = Tuple.sort x (tc01_lo heven j) := by
    rw [← hp0 j, ρ.involution]
  let e : Fin (n / 2) × Fin 2 ≃ Fin n :=
    finProdFinEquiv.trans (finCongr (by have := tc01_twice_half n heven; omega))
  have he0 (j : Fin (n / 2)) : e (j, 0) = tc01_lo heven j := by
    apply Fin.ext
    simp [e, tc01_lo, finProdFinEquiv]
  have he1 (j : Fin (n / 2)) : e (j, 1) = tc01_hi heven j := by
    apply Fin.ext
    simp [e, tc01_hi, finProdFinEquiv]
    omega
  calc
    _ = ∑ r, (b (Tuple.sort x r) - b (ρ.partner (Tuple.sort x r)))^2 :=
      (Equiv.sum_comp (Tuple.sort x) _).symm
    _ = ∑ j : Fin (n / 2),
        ((b (Tuple.sort x (tc01_lo heven j)) - b (Tuple.sort x (tc01_hi heven j)))^2 +
         (b (Tuple.sort x (tc01_hi heven j)) - b (Tuple.sort x (tc01_lo heven j)))^2) := by
      rw [← e.sum_comp, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.sum_univ_two, he0, he1, hp0, hp1]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- A sampled baseline value at a fixed sorted rank. -/
def tc01_ranked {n : ℕ} (b : (Fin n → ℝ) × (Fin n → ℝ)) (r : Fin n) : ℝ :=
  b.1 (Tuple.sort b.1 r) + b.2 (Tuple.sort b.1 r)

theorem tc01_ranked_measurable {n : ℕ} (r : Fin n) :
    Measurable (fun b : (Fin n → ℝ) × (Fin n → ℝ) => tc01_ranked b r) := by
  have hm : Measurable (fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
      ∑ σ : Equiv.Perm (Fin n),
        if Tuple.sort b.1 = σ then b.1 (σ r) + b.2 (σ r) else 0) := by
    apply Finset.measurable_sum
    intro σ _
    exact Measurable.ite ((t23_sort_region σ).preimage measurable_fst)
      (((measurable_pi_apply (σ r)).comp measurable_fst).add
        ((measurable_pi_apply (σ r)).comp measurable_snd)) measurable_const
  simpa [tc01_ranked] using hm

/-- A Borel expression for the squared baseline difference of two sorted units. -/
def tc01_rank_square {n : ℕ} (r s : Fin n)
    (b : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ := (tc01_ranked b r - tc01_ranked b s)^2

theorem tc01_rank_square_integrable {n : ℕ} (r s : Fin n) :
    Integrable (tc01_rank_square r s) (uniformBaselines n) := by
  haveI := t23_baselines_probability n
  haveI instTC01RankCube3 : IsProbabilityMeasure (t23_cube n 3) :=
    t23_cube_probability n 3 (by norm_num)
  haveI instTC01RankCube7 : IsProbabilityMeasure (t23_cube n 7) :=
    t23_cube_probability n 7 (by norm_num)
  have hm : AEStronglyMeasurable (tc01_rank_square r s) (uniformBaselines n) :=
    (((tc01_ranked_measurable r).sub (tc01_ranked_measurable s)).pow_const 2).aestronglyMeasurable
  apply Integrable.mono' (integrable_const (100 : ℝ)) hm
  rw [t23_baselines_eq]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (t23_cube_ae_bounds n 3 (by norm_num)),
    Measure.quasiMeasurePreserving_snd.ae (t23_cube_ae_bounds n 7 (by norm_num))]
    with b hx he
  have hr0 := hx (Tuple.sort b.1 r)
  have hs0 := hx (Tuple.sort b.1 s)
  have hr1 := he (Tuple.sort b.1 r)
  have hs1 := he (Tuple.sort b.1 s)
  rw [tc01_rank_square, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  dsimp [tc01_ranked]
  have hd0 : 0 ≤ 10 - (b.1 (Tuple.sort b.1 r) + b.2 (Tuple.sort b.1 r) -
      (b.1 (Tuple.sort b.1 s) + b.2 (Tuple.sort b.1 s))) := by linarith
  have hd1 : 0 ≤ 10 + (b.1 (Tuple.sort b.1 r) + b.2 (Tuple.sort b.1 r) -
      (b.1 (Tuple.sort b.1 s) + b.2 (Tuple.sort b.1 s))) := by linarith
  nlinarith [mul_nonneg hd0 hd1]

/-- Integrating independent noise at two distinct labels, with an arbitrary fixed gap. -/
theorem tc01_noise_square {n : ℕ} (d : ℝ) (i j : Fin n) (hij : i ≠ j) :
    Integrable (fun e : Fin n → ℝ => (d + e i - e j)^2) (t23_cube n 7) ∧
    (∫ e, (d + e i - e j)^2 ∂t23_cube n 7) = d^2 + 49 / 6 := by
  haveI := t23_cube_probability n 7 (by norm_num)
  have hi : Integrable (fun e : Fin n → ℝ => e i) (t23_cube n 7) := by
    simpa using t23_cube_integrable_pow n 7 (by norm_num) i 1
  have hj : Integrable (fun e : Fin n → ℝ => e j) (t23_cube n 7) := by
    simpa using t23_cube_integrable_pow n 7 (by norm_num) j 1
  have hii := t23_cube_integrable_pow n 7 (by norm_num) i 2
  have hjj := t23_cube_integrable_pow n 7 (by norm_num) j 2
  have hc := (t23_cube_product 7 (by norm_num) i j).1
  have hl : Integrable (fun e : Fin n → ℝ => (2 * d) * (e i - e j))
      (t23_cube n 7) := (hi.sub' hj).const_mul (2 * d)
  have hq : Integrable (fun e : Fin n → ℝ => e i^2 + e j^2 - 2 * (e i * e j))
      (t23_cube n 7) := (hii.fun_add hjj).sub' (hc.const_mul 2)
  have he (e : Fin n → ℝ) : (d + e i - e j)^2 =
      d^2 + (2 * d) * (e i - e j) + (e i^2 + e j^2 - 2 * (e i * e j)) := by ring
  constructor
  · simpa only [he] using ((integrable_const (d^2)).fun_add hl).fun_add hq
  · simp_rw [he]
    rw [integral_add ((integrable_const _).fun_add hl) hq,
      integral_add (integrable_const _) hl,
      integral_sub (hii.fun_add hjj) (hc.const_mul 2), integral_add hii hjj,
      integral_const_mul, integral_sub hi hj, integral_const_mul]
    have hmean (k : Fin n) : (∫ e, e k ∂t23_cube n 7) = 7 / 2 := by
      simpa [show (1 : ℝ) + 1 = 2 by norm_num] using
        t23_cube_moment n 7 (by norm_num) k 1
    rw [hmean i, hmean j, t23_cube_moment n 7 (by norm_num) i 2,
      t23_cube_moment n 7 (by norm_num) j 2,
      (t23_cube_product 7 (by norm_num) i j).2, if_neg hij]
    simp
    ring

/-- The average of one squared sorted baseline difference separates into its X gap
and the independent noise contribution. -/
theorem tc01_rank_square_average {n : ℕ} (r s : Fin n) (hrs : r ≠ s) :
    (∫ b, tc01_rank_square r s b ∂uniformBaselines n) =
      (∫ x, (x (Tuple.sort x r) - x (Tuple.sort x s))^2 ∂t23_cube n 3) + 49 / 6 := by
  haveI := t23_cube_probability n 3 (by norm_num)
  haveI := t23_cube_probability n 7 (by norm_num)
  have hint := tc01_rank_square_integrable r s
  rw [t23_baselines_eq] at hint ⊢
  rw [integral_prod _ hint]
  have hf (x : Fin n → ℝ) :
      (∫ e, tc01_rank_square r s (x, e) ∂t23_cube n 7) =
        (x (Tuple.sort x r) - x (Tuple.sort x s))^2 + 49 / 6 := by
    have he (e : Fin n → ℝ) : tc01_rank_square r s (x, e) =
        ((x (Tuple.sort x r) - x (Tuple.sort x s)) +
          e (Tuple.sort x r) - e (Tuple.sort x s))^2 := by
      dsimp [tc01_rank_square, tc01_ranked]
      ring
    simp_rw [he]
    exact (tc01_noise_square _ _ _ (fun h => hrs ((Tuple.sort x).injective h))).2
  simp_rw [hf]
  have hg : Integrable
      (fun x : Fin n → ℝ => (x (Tuple.sort x r) - x (Tuple.sort x s))^2)
      (t23_cube n 3) := by
    have hh := hint.integral_prod_left
    simp_rw [hf] at hh
    simpa only [add_sub_cancel_right] using hh.sub' (integrable_const (49 / 6 : ℝ))
  rw [integral_add hg (integrable_const _)]
  simp

/-- The exact contribution of one adjacent sorted baseline pair. -/
theorem tc01_adjacent_square_average {n : ℕ} (heven : Even n) (j : Fin (n / 2)) :
    (∫ b, tc01_rank_square (tc01_lo heven j) (tc01_hi heven j) b
      ∂uniformBaselines n) =
        18 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) + 49 / 6 := by
  have hne : tc01_lo heven j ≠ tc01_hi heven j := by
    intro h
    have := congrArg Fin.val h
    dsimp [tc01_lo, tc01_hi] at this
    omega
  rw [tc01_rank_square_average _ _ hne]
  have hj : 2 * j.val + 1 < n := (tc01_hi heven j).isLt
  have he (x : Fin n → ℝ) :
      (x (Tuple.sort x (tc01_lo heven j)) - x (Tuple.sort x (tc01_hi heven j)))^2 =
        (t23_gap x (2 * j.val) hj)^2 := by
    dsimp [tc01_lo, tc01_hi, t23_gap]
    ring
  simp_rw [he]
  rw [(tc01_uniform_spacing_second_moment n (by omega) 3 (by norm_num) _ hj).2]
  norm_num

/-- Arbitrary selectors are transferred a.e. to a Borel integrable statistic before
any integration or use of Fubini. No measurability of `ρ` or `Q` is required. -/
theorem tc01_paired_sampling_average {n : ℕ} (hn : 0 < n) (heven : Even n)
    (ρ : (Fin n → ℝ) → Pairing n) (hRank : ∀ x, AdjacentRanks x (ρ x))
    (Q : (Fin n → ℝ) → Law (Assignment n))
    (hPair : ∀ x, Paired (⟨Q x, fullOutcome (fun _ => 0)⟩ : Experiment n) (ρ x)) :
    Integrable (fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
      var (Q b.1) (ht (⟨Q b.1, fullOutcome (fun i => b.1 i + b.2 i)⟩ : Experiment n)))
      (uniformBaselines n) ∧
    (∫ b, var (Q b.1) (ht (⟨Q b.1, fullOutcome (fun i => b.1 i + b.2 i)⟩ : Experiment n))
      ∂uniformBaselines n) =
        49 / (3 * (n : ℝ)) + 36 / ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  haveI instTC01PairCube3 : IsProbabilityMeasure (t23_cube n 3) :=
    t23_cube_probability n 3 (by norm_num)
  haveI instTC01PairCube7 : IsProbabilityMeasure (t23_cube n 7) :=
    t23_cube_probability n 7 (by norm_num)
  have hi (j : Fin (n / 2)) :=
    tc01_rank_square_integrable (tc01_lo heven j) (tc01_hi heven j)
  have hcanon := (integrable_finset_sum Finset.univ (fun j _ => hi j)).const_mul
    (4 / (n : ℝ)^2)
  have hae : (fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
      var (Q b.1) (ht (⟨Q b.1, fullOutcome (fun i => b.1 i + b.2 i)⟩ : Experiment n))) =ᵐ[
        uniformBaselines n]
      (fun b => 4 / (n : ℝ)^2 * ∑ j : Fin (n / 2),
        tc01_rank_square (tc01_lo heven j) (tc01_hi heven j) b) := by
    rw [t23_baselines_eq]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (t23_cube_ae_injective n 3 (by norm_num))] with b hb
    rw [t23_paired_baseline_variance hn heven
      (⟨Q b.1, fullOutcome (fun i => b.1 i + b.2 i)⟩ : Experiment n) (ρ b.1)
      (t23_paired_baseline (Q b.1) (ρ b.1) _ (hPair b.1))
      (fun i => b.1 i + b.2 i) rfl,
      tc01_pair_reindex heven b.1 (fun i => b.1 i + b.2 i) hb (ρ b.1) (hRank b.1)]
    simp only [tc01_rank_square, tc01_ranked]
    ring
  refine ⟨hcanon.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_const_mul,
    integral_finset_sum _ (fun j _ => hi j)]
  simp_rw [tc01_adjacent_square_average heven]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) = n := by
    exact_mod_cast tc01_twice_half n heven
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have hh' : ((n / 2 : ℕ) : ℝ) = (n : ℝ) / 2 := by linarith
  rw [hh']
  field_simp
  ring

theorem simulation_sampling_variance_proof {n : ℕ} (hn : 0 < n) (heven : Even n)
    (P : Law (Assignment n))
    (hCR : Complete (⟨P, fullOutcome (fun _ => 0)⟩ : Experiment n) (n/2))
    (ρ : (Fin n → ℝ) → Pairing n) (hRank : ∀ x, AdjacentRanks x (ρ x))
    (Q : (Fin n → ℝ) → Law (Assignment n))
    (hPair : ∀ x, Paired (⟨Q x, fullOutcome (fun _ => 0)⟩ : Experiment n) (ρ x)) :
    let cr := fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
      (⟨P, fullOutcome (fun i => b.1 i+b.2 i)⟩ : Experiment n)
    let pair := fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
      (⟨Q b.1, fullOutcome (fun i => b.1 i+b.2 i)⟩ : Experiment n)
    (∫ b, mean (cr b).design (ht (cr b))-eate (cr b) ∂uniformBaselines n) = -1 ∧
    (∫ b, mean (pair b).design (ht (pair b))-eate (pair b) ∂uniformBaselines n) = -1 ∧
    (∫ b, mean (cr b).design (hajek (cr b))-eate (cr b) ∂uniformBaselines n) = -1 ∧
    (∫ b, mean (pair b).design (hajek (pair b))-eate (pair b) ∂uniformBaselines n) = -1 ∧
    (∫ b, var (cr b).design (ht (cr b)) ∂uniformBaselines n) = 58/(3*(n:ℝ)) ∧
    (∫ b, var (pair b).design (ht (pair b)) ∂uniformBaselines n) =
      49/(3*(n:ℝ))+36/((n:ℝ)*((n:ℝ)+1)*((n:ℝ)+2)) ∧
    (∫ b, var (cr b).design (hajek (cr b)) ∂uniformBaselines n) = 58/(3*(n:ℝ)) ∧
    (∫ b, var (pair b).design (hajek (pair b)) ∂uniformBaselines n) =
      49/(3*(n:ℝ))+36/((n:ℝ)*((n:ℝ)+1)*((n:ℝ)+2)) ∧
    (∫ b, mean (cr b).design (fun z => (ht (cr b) z-eate (cr b))^2)
      ∂uniformBaselines n) = 58/(3*(n:ℝ))+1 ∧
    (∫ b, mean (pair b).design (fun z => (ht (pair b) z-eate (pair b))^2)
      ∂uniformBaselines n) = 49/(3*(n:ℝ))+36/((n:ℝ)*((n:ℝ)+1)*((n:ℝ)+2))+1 ∧
    (∫ b, mean (cr b).design (fun z => (hajek (cr b) z-eate (cr b))^2)
      ∂uniformBaselines n) = 58/(3*(n:ℝ))+1 ∧
    (∫ b, mean (pair b).design (fun z => (hajek (pair b) z-eate (pair b))^2)
      ∂uniformBaselines n) = 49/(3*(n:ℝ))+36/((n:ℝ)*((n:ℝ)+1)*((n:ℝ)+2))+1 ∧
    1/(58/(3*(n:ℝ))) = 3*(n:ℝ)/58  := by
  let cr := fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
    (⟨P, fullOutcome (fun i => b.1 i + b.2 i)⟩ : Experiment n)
  let pair := fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
    (⟨Q b.1, fullOutcome (fun i => b.1 i + b.2 i)⟩ : Experiment n)
  haveI := t23_baselines_probability n
  have h := t23_sampling_without_paired_average hn heven P hCR ρ Q hPair
  have hv := tc01_paired_sampling_average hn heven ρ hRank Q hPair
  have hp (b) := t23_fixed_baseline hn heven (pair b) (fun i => b.1 i + b.2 i) rfl
    (Or.inr ⟨ρ b.1, hPair b.1⟩)
  have hmse : (∫ b, var (Q b.1) (ht (pair b)) + 1 ∂uniformBaselines n) =
      49 / (3 * (n : ℝ)) + 36 / ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) + 1 := by
    rw [integral_add hv.1 (integrable_const 1), hv.2]
    simp
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hv.2,
    h.2.2.2.2.2.1, ?_, h.2.2.2.2.2.2.1, ?_, h.2.2.2.2.2.2.2.1, ?_,
    h.2.2.2.2.2.2.2.2⟩
  · exact (integral_congr_ae (Filter.Eventually.of_forall
      (fun b => (hp b).2.2.1))).trans hv.2
  · exact (integral_congr_ae (Filter.Eventually.of_forall
      (fun b => (hp b).2.2.2.1))).trans hmse
  · exact (integral_congr_ae (Filter.Eventually.of_forall
      (fun b => (hp b).2.2.2.2))).trans hmse

end
end AronowAudit.P009.Wave1
