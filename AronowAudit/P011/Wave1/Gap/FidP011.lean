import AronowAudit.P011.Wave1.Gap.GLP011B6
import AronowAudit.P011.P011_SignCompletion
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset

/-! Faithful one-block path moments and the full fair-sign counterexample. -/
namespace AronowAudit.P011.Wave1
open AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal ProbabilityTheory
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

lemma path_block_moments_finite_mean (t : ℝ) (i : Fin 3) :
    pathMean (fun u v => pathBlock t u v i) = (![t,-2*t,t] : Fin 3 → ℝ) i := by
  fin_cases i <;> norm_num [pathMean,pathBlock] <;> ring

lemma path_block_moments_law_mean (t : ℝ) (i : Fin 3) :
    expectation (pathModel t 1) (fun y => y i) = (![t,-2*t,t] : Fin 3 → ℝ) i := by
  simpa [path_ce_weighted,localIndex,Nat.mod_eq_of_lt i.isLt] using path_ce_mean t 1 i

lemma path_block_moments_law_covariance (t : ℝ) :
    covariance (pathModel t 1) =
      (![![1,3/5,0],![3/5,1,4/5],![0,4/5,1]] : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [path_ce_covariance]
  ext i j
  have hb : blockIndex (by decide) i = blockIndex (by decide) j := Subsingleton.elim _ _
  simp [path_ce_lift,hb,localIndex,Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt,path_ce_C]

theorem path_block_moments_with_covariance
    (t : ℝ) (ht : t = 1 ∨ t = 2) :
    (∀ i : Fin 3,
      pathMean (fun u v => pathBlock t u v i) =
        (![t, -2*t, t] : Fin 3 → ℝ) i) ∧
    (∀ i : Fin 3,
      expectation (pathModel t 1) (fun y => y i) =
        (![t, -2*t, t] : Fin 3 → ℝ) i) ∧
    covariance (pathModel t 1) =
      (![![1, 3/5, 0], ![3/5, 1, 4/5], ![0, 4/5, 1]] :
        Matrix (Fin 3) (Fin 3) ℝ) ∧
    quadratic (oracleMatrix pathGraph) (![t, -2*t, t] : Fin 3 → ℝ) = -2*t^2 ∧
    pathMean (fun u v => ∑ i, pathBlock t u v i) = 0 ∧
    pathMean (fun u v => (∑ i, pathBlock t u v i)^2) = 29/5 ∧
    pathMean (fun u v => quadratic (oracleMatrix pathGraph) (pathBlock t u v)) =
      29/5 - 2*t^2 ∧
    pathMean (fun u v =>
      (quadratic (oracleMatrix pathGraph) (pathBlock t u v) - (29/5 - 2*t^2))^2) =
      8*t^2 + 8836/625 ∧
    pathMean (fun u v => (∑ i, pathBlock t u v i) *
      (∑ i, ∑ j, oracleMatrix pathGraph i j * pathBlock t u v j)) = 14 ∧
    quadratic (oracleMatrix pathGraph) (fun _ => 1) = 7 := by
  rcases ht with rfl | rfl <;>
    exact ⟨path_block_moments_finite_mean _, path_block_moments_law_mean _,
      path_block_moments_law_covariance _, path_block_moments _⟩

noncomputable def signInsideProbability (n : ℕ) (ε : ℝ) : ℝ :=
  probability (signModel n)
    {y | |(n : ℝ)*V2star (signModel n) y -
      (n : ℝ)*var (signModel n) (betaHat (signModel n))| < ε}

lemma printed_sign_full_auxiliary {n : ℕ} (y : Fin n → ℝ) :
    V2star (signModel n) y = V2 (emptyGraph n) y := by
  have hw : weighted (signModel n) y = y := by
    funext i
    exact SignCompletion.weighted_value y i
  rw [auxiliary_empty_identity (signModel n) rfl y]
  change V2 (emptyGraph n) (weighted (signModel n) y) = V2 (emptyGraph n) y
  rw [hw]

lemma printed_sign_full_pointwise {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) :
    (n : ℝ)*V2star (signModel n) y = 1 - (betaHat (signModel n) y)^2 ∧
    |(n : ℝ)*V2star (signModel n) y -
      (n : ℝ)*var (signModel n) (betaHat (signModel n))| =
        (betaHat (signModel n) y)^2 := by
  have hv : (n : ℝ)*V2star (signModel n) y = 1 - (betaHat (signModel n) y)^2 := by
    rw [printed_sign_full_auxiliary,SignCompletion.betaHat_value]
    exact SignCompletion.V2_value hn y hy
  refine ⟨hv,?_⟩
  rw [hv,SignCompletion.scaled_variance hn]
  rw [show 1 - (betaHat (signModel n) y)^2 - 1 =
    -((betaHat (signModel n) y)^2) by ring,abs_neg,abs_of_nonneg (sq_nonneg _)]

lemma printed_sign_full_old_probability (k : ℕ) (ε : ℝ) :
    signInsideProbability (k+1) ε = probability (signFamily.model k)
      {y | |(k+1 : ℝ)*V2 (signFamily.model k).G
        (weighted (signFamily.model k) y)-1| < ε} := by
  unfold signInsideProbability
  simp only [SignCompletion.family_model,SignCompletion.family_size]
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq]
  rw [SignCompletion.scaled_variance (Nat.succ_pos k),
    auxiliary_empty_identity (signModel (k+1)) rfl]
  simp only [Nat.cast_add,Nat.cast_one]

lemma printed_sign_full_limits (ε : ℝ) (hε : 0 < ε) :
    (∀ n : ℕ, 0 < n → 1 - 1/((n : ℝ)*ε) ≤ signInsideProbability n ε) ∧
    Tendsto (fun k => signInsideProbability (k+1) ε) atTop (𝓝 1) := by
  have hold := (AronowAudit.P011.printed_sign_counterexample.2.2.2 ε hε)
  constructor
  · intro n hn
    cases n with
    | zero => omega
    | succ k =>
      simpa only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,
        printed_sign_full_old_probability] using hold.1 k
  · simpa only [printed_sign_full_old_probability] using hold.2

-- Reindex Boolean sign vectors by their sets of positive coordinates.
def printed_sign_full_subsetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun u := univ.filter (fun i => u i = true)
  invFun s i := decide (i ∈ s)
  left_inv u := by
    funext i
    cases h : u i <;> simp [h]
  right_inv s := by
    ext i
    simp

lemma printed_sign_full_subset_average {n : ℕ} (s : Finset (Fin n)) :
    average (fun i => sign ((printed_sign_full_subsetEquiv n).symm s i)) =
      (2*(s.card : ℝ)-(n : ℝ))/(n : ℝ) := by
  unfold average
  congr 1
  have h (i : Fin n) : sign ((printed_sign_full_subsetEquiv n).symm s i) =
      2*(if i ∈ s then (1 : ℝ) else 0)-1 := by
    by_cases hi : i ∈ s <;> norm_num [printed_sign_full_subsetEquiv,sign,hi]
  simp_rw [h]
  rw [sum_sub_distrib,←mul_sum]
  simp

lemma printed_sign_full_average_probability {n : ℕ} (hn : 0 < n) (ε : ℝ) :
    signInsideProbability n ε =
      (∑ u : Fin n → Bool,
        if (average (fun i => sign (u i)))^2 < ε then (1 : ℝ) else 0)/(2 : ℝ)^n := by
  have he : signInsideProbability n ε =
      (signModel n).law.real {y | average y^2 < ε} := by
    apply measureReal_congr
    filter_upwards [DataMatrixCompletion.ae_signs n] with y hy
    rw [(printed_sign_full_pointwise hn y hy).2,SignCompletion.betaHat_value]
  have hs : MeasurableSet {y : Fin n → ℝ | average y^2 < ε} :=
    measurableSet_lt (by unfold average; fun_prop) measurable_const
  rw [he,←integral_indicator_one hs]
  change (∫ y, ({y : Fin n → ℝ | average y^2 < ε}).indicator 1 y
    ∂uniformLaw (fun u : Fin n → Bool => fun i => sign (u i))) = _
  rw [uniform_integral (fun u : Fin n → Bool => fun i => sign (u i))
    (measurable_of_finite _)
    (({y : Fin n → ℝ | average y^2 < ε}).indicator (1 : (Fin n → ℝ) → ℝ))
    (measurable_const.indicator hs)]
  simp only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply,Fintype.card_fun,
    Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]

-- The binomial formula reduces each exact probability to at most n+1 summands.
lemma printed_sign_full_binomial {n : ℕ} (hn : 0 < n) (ε : ℝ) :
    signInsideProbability n ε =
      (∑ r ∈ range (n+1), (n.choose r : ℝ) *
        (if ((2*(r : ℝ)-(n : ℝ))/(n : ℝ))^2 < ε then (1 : ℝ) else 0))/(2 : ℝ)^n := by
  rw [printed_sign_full_average_probability hn ε]
  congr 1
  rw [←(printed_sign_full_subsetEquiv n).symm.sum_comp]
  simp_rw [printed_sign_full_subset_average]
  simpa only [powerset_univ,card_univ,Fintype.card_fin,nsmul_eq_mul] using
    (sum_powerset_apply_card
      (fun r => if ((2*(r : ℝ)-(n : ℝ))/(n : ℝ))^2 < ε then (1 : ℝ) else 0)
      (x := (univ : Finset (Fin n))))

lemma printed_sign_full_probability_two : signInsideProbability 2 (1/2) = 1/2 := by
  rw [printed_sign_full_binomial (by decide)]
  norm_num [sum_range_succ,Nat.choose]

lemma printed_sign_full_probability_four : signInsideProbability 4 (1/2) = 7/8 := by
  rw [printed_sign_full_binomial (by decide)]
  norm_num [sum_range_succ,Nat.choose]

lemma printed_sign_full_probability_sixteen : signInsideProbability 16 (1/2) = 32631/32768 := by
  rw [printed_sign_full_binomial (by decide)]
  norm_num [sum_range_succ,Nat.choose]

theorem printed_sign_counterexample_full :
    Scaling signFamily 1 1 1 2 ∧ Valid signFamily ∧
    (∀ n : ℕ, 0 < n →
      Homoskedastic (signModel n) ∧ beta (signModel n) = 0 ∧
      (n : ℝ)*var (signModel n) (betaHat (signModel n)) = 1 ∧
      expectation (signModel n) (fun y => (betaHat (signModel n) y)^2) = 1/(n : ℝ) ∧
      (∀ y : Fin n → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
        (n : ℝ)*V2star (signModel n) y = 1 - (betaHat (signModel n) y)^2 ∧
        |(n : ℝ)*V2star (signModel n) y -
          (n : ℝ)*var (signModel n) (betaHat (signModel n))| =
            (betaHat (signModel n) y)^2)) ∧
    (∀ ε : ℝ, 0 < ε →
      (∀ n : ℕ, 0 < n →
        1 - 1/((n : ℝ)*ε) ≤
          AronowAudit.P011.Wave1.signInsideProbability n ε) ∧
      Tendsto (fun k => AronowAudit.P011.Wave1.signInsideProbability (k+1) ε)
        atTop (𝓝 1)) ∧
    AronowAudit.P011.Wave1.signInsideProbability 2 (1/2) = 1/2 ∧
    AronowAudit.P011.Wave1.signInsideProbability 4 (1/2) = 7/8 ∧
    AronowAudit.P011.Wave1.signInsideProbability 16 (1/2) = 32631/32768 ∧
    ¬ (∀ ε : ℝ, 0 < ε →
      Tendsto (fun k => AronowAudit.P011.Wave1.signInsideProbability (k+1) ε)
        atTop (𝓝 0)) := by
  refine ⟨SignCompletion.scaling_valid.1,SignCompletion.scaling_valid.2,?_,
    printed_sign_full_limits,printed_sign_full_probability_two,
    printed_sign_full_probability_four,printed_sign_full_probability_sixteen,?_⟩
  · intro n hn
    refine ⟨?_,SignCompletion.beta_zero n,SignCompletion.scaled_variance hn,
      SignCompletion.moment hn,printed_sign_full_pointwise hn⟩
    intro i j
    simp [DataMatrixCompletion.covariance_formula]
  · intro hzero
    have hone := (printed_sign_full_limits (1/2) (by norm_num)).2
    have h := tendsto_nhds_unique hone (hzero (1/2) (by norm_num))
    norm_num at h

end
end AronowAudit.P011.Wave1
