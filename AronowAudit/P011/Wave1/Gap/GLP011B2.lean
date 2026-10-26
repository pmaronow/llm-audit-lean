import AronowAudit.P011.P011_FiniteLawCompletion
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace AronowAudit.P011.Wave1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 700000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

/-! T10: the finite laws and their common infinite prior. -/

lemma uci_sign_abs (u : Bool) : |sign u| = 1 := by cases u <;> norm_num [sign]

lemma uci_ae_uniform {A : Type} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
    (f : A → Fin n → ℝ) {P : (Fin n → ℝ) → Prop}
    (hP : MeasurableSet {y | P y}) (h : ∀ u, P (f u)) :
    ∀ᵐ y ∂uniformLaw f, P y := by
  rw [uniformLaw, ← PMF.toMeasure_map f (PMF.uniformOfFintype A) (measurable_of_finite _)]
  apply (ae_map_iff (measurable_of_finite f).aemeasurable hP).mpr
  exact ae_of_all _ h

lemma uci_average_bound {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (a : ℝ)
    (hx : ∀ i, |x i| ≤ a) : |average x| ≤ a := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [average, abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    |∑ i, x i| ≤ ∑ i, |x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, a := Finset.sum_le_sum (fun i _ => hx i)
    _ = a * n := by simp [mul_comm]

lemma uci_fixed_scaling (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (s : ℕ → Bool) :
    Scaling (fixedMeanFamily a b s) (2*a+b) 1 (b^2) 2 := by
  refine ⟨?_, by positivity, by norm_num, by positivity, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ _ h => Nat.succ_le_succ h, fun _ => ⟨Fin.castSuccEmb, fun _ _ => rfl⟩⟩
  · intro k
    exact uniform_coordinate_dependency Bool (fun i u => a*sign (s i.val)+b*sign u)
      (fun _ => measurable_of_finite _)
  · intro k
    change ∀ᵐ y ∂(fixedMeanModel a b s (k+1)).law,
      ∀ i, |weighted (fixedMeanModel a b s (k+1)) y i-beta (fixedMeanModel a b s (k+1))| ≤ _
    rw [(mixture_finite_moments a b s (k+1) (by omega)).2.1]
    have hm := uci_average_bound (n := k+1) (by omega)
      (fun i => a*sign (s i.val)) a (fun i => by simp [abs_mul, abs_of_pos ha, uci_sign_abs])
    apply uci_ae_uniform _ (by
      simp only [Set.setOf_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le (by unfold weighted; fun_prop) measurable_const)
    intro u i
    simp only [weighted, fixedMeanModel, one_mul]
    calc
      |a*sign (s i.val)+b*sign (u i)-average (fun i : Fin (k+1) => a*sign (s i.val))|
          ≤ |a*sign (s i.val)+b*sign (u i)| + |average (fun i : Fin (k+1) => a*sign (s i.val))| := abs_sub _ _
      _ ≤ (|a*sign (s i.val)|+|b*sign (u i)|)+a := add_le_add (abs_add_le _ _) hm
      _ = 2*a+b := by simp [abs_mul, abs_of_pos ha, abs_of_pos hb, uci_sign_abs]; ring
  · intro k i; simp [fixedMeanFamily, fixedMeanModel, degree, emptyGraph]
  · have he : (fun k => ((fixedMeanFamily a b s).size k : ℝ) *
        var ((fixedMeanFamily a b s).model k) (betaHat ((fixedMeanFamily a b s).model k))) =
        fun _ => b^2 := funext fun k => (mixture_finite_moments a b s (k+1) (by omega)).2.2.1
    rw [he]; exact tendsto_const_nhds
  · intro k i; change |(1 : ℝ)| < 2; norm_num

def uci_pairEquiv (n : ℕ) : ((Fin n → Bool) × (Fin n → Bool)) ≃ (Fin n → Bool × Bool) :=
  { toFun := fun u i => (u.1 i, u.2 i)
    invFun := fun u => (fun i => (u i).1, fun i => (u i).2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma uci_mixture_law (a b : ℝ) (n : ℕ) :
    (mixtureModel a b n).law = uniformLaw
      (fun u : Fin n → Bool × Bool => fun i => a*sign (u i).1+b*sign (u i).2) := by
  let f := fun u : Fin n → Bool × Bool => fun i => a*sign (u i).1+b*sign (u i).2
  change uniformLaw (f ∘ uci_pairEquiv n) = uniformLaw f
  exact NewFiniteCompletion.uniformLaw_equiv (uci_pairEquiv n) f

lemma uci_mixture_scaling (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Scaling (mixtureFamily a b) (a+b) 1 (a^2+b^2) 2 := by
  refine ⟨?_, by positivity, by norm_num, by positivity, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ _ h => Nat.succ_le_succ h, fun _ => ⟨Fin.castSuccEmb, fun _ _ => rfl⟩⟩
  · intro k
    change VariableDependency (mixtureModel a b (k+1)).law (emptyGraph (k+1)) _
    rw [uci_mixture_law]
    exact uniform_coordinate_dependency (Bool × Bool) (fun _ u => a*sign u.1+b*sign u.2)
      (fun _ => measurable_of_finite _)
  · intro k
    change ∀ᵐ y ∂(mixtureModel a b (k+1)).law, ∀ i,
      |weighted (mixtureModel a b (k+1)) y i-beta (mixtureModel a b (k+1))| ≤ _
    rw [(mixture_finite_moments a b (fun _ => false) (k+1) (by omega)).2.2.2.2.1]
    apply uci_ae_uniform _ (by
      simp only [Set.setOf_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le (by unfold weighted; fun_prop) measurable_const)
    intro u i
    simp only [weighted, mixtureModel, one_mul, sub_zero]
    exact (abs_add_le _ _).trans_eq (by simp [abs_mul, abs_of_pos ha, abs_of_pos hb, uci_sign_abs])
  · intro k i; simp [mixtureFamily, mixtureModel, degree, emptyGraph]
  · have he : (fun k => ((mixtureFamily a b).size k : ℝ) *
        var ((mixtureFamily a b).model k) (betaHat ((mixtureFamily a b).model k))) =
        fun _ => a^2+b^2 := funext fun k =>
          (mixture_finite_moments a b (fun _ => false) (k+1) (by omega)).2.2.2.2.2
    rw [he]; exact tendsto_const_nhds
  · intro k i; change |(1 : ℝ)| < 2; norm_num

lemma uci_uniform_apply {A : Type} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
    (f : A → Fin n → ℝ) (E : Set (Fin n → ℝ)) (hE : MeasurableSet E) :
    uniformLaw f E = (Fintype.card A : ℝ≥0∞)⁻¹ * ∑ u, if f u ∈ E then 1 else 0 := by
  rw [uniformLaw, ← PMF.toMeasure_map f (PMF.uniformOfFintype A) (measurable_of_finite _),
    Measure.map_apply (measurable_of_finite _) hE, PMF.toMeasure_apply_fintype]
  simp only [Set.indicator_apply, PMF.uniformOfFintype_apply, Set.mem_preimage]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _; split_ifs <;> simp

lemma uci_measure_identity (a b : ℝ) (n : ℕ) :
    (mixtureModel a b n).law =
      ∑ s : (Fin n → Bool), ((2 : ℝ≥0∞)^n)⁻¹ •
        (fixedMeanModel a b (fun i => if hi : i < n then s ⟨i,hi⟩ else false) n).law := by
  ext E hE
  simp only [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul]
  change uniformLaw _ E = ∑ s : Fin n → Bool, _ * uniformLaw _ E
  rw [uci_uniform_apply _ E hE]
  simp_rw [uci_uniform_apply _ E hE]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Fintype.card_fin,
    Fintype.sum_prod_type, Fin.is_lt, dite_true]
  rw [ENNReal.mul_inv (by simp) (by simp)]
  simp only [mul_assoc, Finset.mul_sum]

def uci_prior : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

instance uci_prior_probability : IsProbabilityMeasure uci_prior := by
  unfold uci_prior; infer_instance

lemma uci_prefix_law (n : ℕ) :
    uci_prior.map (fun s (i : Fin n) => s i.val) =
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure := by
  have hu : (PMF.uniformOfFintype (Fin n → Bool)).toMeasure =
      Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure) := by
    apply Measure.ext_of_singleton
    intro u
    simp [Measure.pi_singleton, PMF.toMeasure_apply_singleton,
      PMF.uniformOfFintype_apply, Fintype.card_fun, ENNReal.inv_pow]
  apply Eq.trans (b := Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)) ?_ hu.symm
  have hi := (iIndepFun_infinitePi (P := fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)
    (X := fun _ (u : Bool) => u) (fun _ => measurable_id)).precomp
      (show Function.Injective (fun i : Fin n => i.val) from Fin.val_injective)
  have he := hi.map_fun_eq_pi_map (fun _ => (measurable_pi_apply _).aemeasurable)
  simpa only [uci_prior, Measure.infinitePi_map_eval] using he

lemma uci_prefix_fixed (a b : ℝ) (s : ℕ → Bool) (n : ℕ) :
    fixedMeanModel a b s n = fixedMeanModel a b
      (fun j => if hj : j < n then s (⟨j,hj⟩ : Fin n).val else false) n := by
  have he : (fun u : Fin n → Bool => fun i => a*sign (s i.val)+b*sign (u i)) =
      (fun u : Fin n → Bool => fun i => a*sign (if hj : i.val < n then s (⟨i.val,hj⟩ : Fin n).val else false)+b*sign (u i)) := by
    funext u i
    simp only [Fin.is_lt, dite_true]
  unfold fixedMeanModel
  simp only [he]

lemma uci_kernel_measurable (a b : ℝ) (n : ℕ) (E : Set (Fin n → ℝ)) :
    Measurable (fun s : ℕ → Bool => probability (fixedMeanModel a b s n) E) := by
  let f := fun v : Fin n → Bool => probability
    (fixedMeanModel a b (fun j => if hj : j < n then v ⟨j,hj⟩ else false) n) E
  have he : (fun s : ℕ → Bool => probability (fixedMeanModel a b s n) E) =
      f ∘ (fun s : ℕ → Bool => fun i : Fin n => s i.val) := by
    funext s
    exact congrArg (fun m : Model n => probability m E) (uci_prefix_fixed a b s n)
  rw [he]
  exact (measurable_of_finite f).comp (measurable_pi_lambda fun i => measurable_pi_apply i.val)

lemma uci_kernel_integral (a b : ℝ) (n : ℕ) (E : Set (Fin n → ℝ)) (hE : MeasurableSet E) :
    (∫ s, probability (fixedMeanModel a b s n) E ∂uci_prior) =
      probability (mixtureModel a b n) E := by
  let f := fun v : Fin n → Bool => probability
    (fixedMeanModel a b (fun j => if hj : j < n then v ⟨j,hj⟩ else false) n) E
  have he : (fun s : ℕ → Bool => probability (fixedMeanModel a b s n) E) =
      fun s => f (fun i => s i.val) := by
    funext s
    exact congrArg (fun m : Model n => probability m E) (uci_prefix_fixed a b s n)
  rw [he, ← integral_map (by fun_prop : Measurable (fun s : ℕ → Bool => fun i : Fin n => s i.val)).aemeasurable
    (measurable_of_finite f).aestronglyMeasurable, uci_prefix_law, PMF.integral_eq_sum]
  rw [probability, uci_measure_identity]
  simp only [Measure.real, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
    PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, Nat.cast_ofNat]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro v _
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    rfl
  · intro v _
    let : IsProbabilityMeasure (fixedMeanModel a b
      (fun i => if hi : i < n then v ⟨i,hi⟩ else false) n).law :=
      (fixedMeanModel a b (fun i => if hi : i < n then v ⟨i,hi⟩ else false) n).probability
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)

lemma uci_consistency_mixes (a b : ℝ)
    (T : ∀ n, (Fin (n+1) → ℝ) → ℝ) (hT : ∀ n, Measurable (T n))
    (h : ∀ s : ℕ → Bool, InProbability (fixedMeanFamily a b s) T (fun _ => b^2)) :
    InProbability (mixtureFamily a b) T (fun _ => b^2) := by
  intro ε hε
  let E := fun k => {y : Fin (k+1) → ℝ | |T k y-b^2| > ε}
  have hE (k) : MeasurableSet (E k) := measurableSet_lt measurable_const (by fun_prop)
  have hc := tendsto_integral_of_dominated_convergence
    (μ := uci_prior) (F := fun k s => probability (fixedMeanModel a b s (k+1)) (E k))
    (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun k => (uci_kernel_measurable a b (k+1) (E k)).aestronglyMeasurable)
    (integrable_const 1) (fun k => ae_of_all _ (fun s => by
      let : IsProbabilityMeasure (fixedMeanModel a b s (k+1)).law :=
        (fixedMeanModel a b s (k+1)).probability
      change ‖(fixedMeanModel a b s (k+1)).law.real (E k)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)) (ae_of_all _ (fun s => h s ε hε))
  change Tendsto (fun k => probability (mixtureModel a b (k+1)) (E k)) atTop (𝓝 0)
  simpa only [uci_kernel_integral a b _ _ (hE _), integral_zero] using hc

lemma uci_incompatible_lower_tail (a b : ℝ) (ha : 0 < a)
    (T : ∀ n, (Fin (n+1) → ℝ) → ℝ)
    (h : InProbability (mixtureFamily a b) T (fun _ => b^2))
    (hl : ∀ ε : ℝ, 0 < ε → Tendsto (fun k => probability (mixtureModel a b (k+1))
      {y | a^2+b^2-T k y > ε}) atTop (𝓝 0)) : False := by
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hs := (h (a^2/4) (by positivity)).add (hl (a^2/2) (by positivity))
  have hbnd (k : ℕ) : 1 ≤ probability (mixtureModel a b (k+1))
      {y | |T k y-b^2| > a^2/4} + probability (mixtureModel a b (k+1))
      {y | a^2+b^2-T k y > a^2/2} := by
    let m := mixtureModel a b (k+1)
    let : IsProbabilityMeasure m.law := m.probability
    have hcover : (Set.univ : Set (Fin (k+1) → ℝ)) ⊆
        {y | |T k y-b^2| > a^2/4} ∪ {y | a^2+b^2-T k y > a^2/2} := by
      intro y _
      by_cases hy : |T k y-b^2| > a^2/4
      · exact Or.inl hy
      · right
        have hh := (abs_le.mp (le_of_not_gt hy)).2
        change a^2+b^2-T k y > a^2/2
        linarith
    calc
      1 = m.law.real Set.univ := probReal_univ.symm
      _ ≤ m.law.real (_ ∪ _) := measureReal_mono hcover
      _ ≤ _ := measureReal_union_le _ _
  have hz : (1 : ℝ) ≤ 0+0 := ge_of_tendsto hs (Eventually.of_forall hbnd)
  norm_num at hz

theorem universal_consistency_impossible_proof (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∀ s : ℕ → Bool, Scaling (fixedMeanFamily a b s) (2*a+b) 1 (b^2) 2) ∧
    Scaling (mixtureFamily a b) (a+b) 1 (a^2+b^2) 2 ∧
    (∀ n, (mixtureModel a b n).law =
      ∑ s : (Fin n → Bool), ((2 : ℝ≥0∞)^n)⁻¹ •
        (fixedMeanModel a b (fun i => if hi : i < n then s ⟨i,hi⟩ else false) n).law) ∧
    ¬ (∃ T : ∀ n, (Fin (n+1) → ℝ) → ℝ,
      (∀ n, Measurable (T n)) ∧
      (∀ s : ℕ → Bool, InProbability (fixedMeanFamily a b s) T (fun _ => b^2)) ∧
      InProbability (mixtureFamily a b) T (fun _ => a^2+b^2)) ∧
    (∀ T : ∀ n, (Fin (n+1) → ℝ) → ℝ, (∀ n, Measurable (T n)) →
      (∀ ε : ℝ, 0 < ε → Tendsto (fun k => probability (mixtureModel a b (k+1))
        {y | a^2+b^2-T k y > ε}) atTop (𝓝 0)) →
      ¬ (∀ s : ℕ → Bool, InProbability (fixedMeanFamily a b s) T (fun _ => b^2))) := by
  refine ⟨uci_fixed_scaling a b ha hb, uci_mixture_scaling a b ha hb,
    uci_measure_identity a b, ?_, ?_⟩
  · rintro ⟨T, hT, hs, hm⟩
    apply uci_incompatible_lower_tail a b ha T (uci_consistency_mixes a b T hT hs)
    intro ε hε
    apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ (hm ε hε)
    apply Eventually.of_forall
    intro k
    let : IsProbabilityMeasure (mixtureModel a b (k+1)).law := (mixtureModel a b (k+1)).probability
    change (mixtureModel a b (k+1)).law.real _ ≤ (mixtureModel a b (k+1)).law.real _
    apply measureReal_mono (μ := (mixtureModel a b (k+1)).law) ?_ (measure_ne_top _ _)
    intro y hy
    change ε < |T k y-(a^2+b^2)|
    exact lt_of_lt_of_le hy (by rw [abs_sub_comm]; exact le_abs_self _)
  · intro T hT hl hs
    exact uci_incompatible_lower_tail a b ha T (uci_consistency_mixes a b T hT hs) hl

/-! T11: parity and deterministic means. -/
def afm_mu (n : ℕ) (i : Fin n) : ℝ := if i.val % 2 = 0 then 2 else 0

lemma afm_sum_mu (n : ℕ) :
    (∑ i : Fin n, afm_mu n i) = 2 * (((n+1)/2 : ℕ) : ℝ) := by
  induction n with
  | zero => simp [afm_mu]
  | succ n ih =>
    simp only [afm_mu, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last] at ih ⊢
    rw [ih]
    by_cases h : n % 2 = 0
    · have he : (n+1+1)/2 = (n+1)/2+1 := by omega
      simp [h, he, Nat.cast_add]
      <;> ring
    · have he : (n+1+1)/2 = (n+1)/2 := by omega
      simp [h, he]

lemma afm_weight_bounds (n : ℕ) (hn : 0 < n) :
    1/2 ≤ alternatingWeight n ∧ alternatingWeight n ≤ 1 ∧
    (n : ℝ)/((n : ℝ)+1) ≤ alternatingWeight n := by
  have hp : 0 < (n+1)/2 := by omega
  have hpn : n ≤ 2*((n+1)/2) := by omega
  have hnp : 2*((n+1)/2) ≤ n+1 := by omega
  have hp2 : (n+1)/2 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (0 : ℝ) < 2 * (((n+1)/2 : ℕ) : ℝ) := by positivity
  have hpnR : (n : ℝ) ≤ 2 * (((n+1)/2 : ℕ) : ℝ) := by exact_mod_cast hpn
  have hnpR : 2 * (((n+1)/2 : ℕ) : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast hnp
  have hp2R : (((n+1)/2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hp2
  dsimp [alternatingWeight]
  refine ⟨(le_div_iff₀ hd).mpr (by linarith),
    (div_le_iff₀ hd).mpr (by linarith), ?_⟩
  exact div_le_div_of_nonneg_left hnR.le hd hnpR


lemma afm_mean (n : ℕ) (i : Fin n) :
    expectation (alternatingModel n) (fun y => weighted (alternatingModel n) y i) =
      alternatingWeight n * afm_mu n i := by
  change (∫ y, alternatingWeight n * y i ∂uniformLaw
    (fun u : Fin n → Bool => fun j => afm_mu n j+sign (u j))) = _
  rw [NewFiniteCompletion.coord_integral Bool
    (fun i b => afm_mu n i + sign b) i (fun x => alternatingWeight n*x) (by fun_prop)]
  simp [Fintype.sum_bool, sign]
  <;> ring

lemma afm_beta (n : ℕ) (hn : 0 < n) : beta (alternatingModel n) = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hp : (((n+1)/2 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < (n+1)/2 := by omega
    positivity
  let : IsProbabilityMeasure (alternatingModel n).law := (alternatingModel n).probability
  have hL2 (i : Fin n) : MemLp (fun y => weighted (alternatingModel n) y i) 2
      (alternatingModel n).law :=
    NewFiniteCompletion.finite_memLp (alternatingOutcome n) _ (by unfold weighted; fun_prop) 2
  unfold beta betaHat average expectation
  rw [integral_div, integral_finsetSum Finset.univ
    (fun i _ => (hL2 i).integrable (by norm_num))]
  change (∑ i, expectation (alternatingModel n)
    (fun y => weighted (alternatingModel n) y i))/(n : ℝ) = 1
  simp_rw [afm_mean]
  rw [← Finset.mul_sum, afm_sum_mu]
  dsimp [alternatingWeight]
  field_simp
  <;> ring


lemma afm_spread (n : ℕ) (hn : 0 < n) :
    meanSpread (alternatingModel n) = 2*alternatingWeight n-1 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hp : (((n+1)/2 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < (n+1)/2 := by omega
    positivity
  have hterm (i : Fin n) : (alternatingWeight n*afm_mu n i-1)^2 =
      (2*alternatingWeight n^2-2*alternatingWeight n)*afm_mu n i+1 := by
    unfold afm_mu
    split_ifs <;> ring
  unfold meanSpread delta
  simp_rw [afm_mean,afm_beta n hn,hterm]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,afm_sum_mu]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  dsimp [alternatingWeight]
  field_simp
  <;> ring


lemma afm_diag (n : ℕ) (i : Fin n) :
    covariance (alternatingModel n) i i = alternatingWeight n^2 := by
  unfold covariance
  rw [afm_mean]
  change (∫ y, (alternatingWeight n*y i-alternatingWeight n*afm_mu n i)*
    (alternatingWeight n*y i-alternatingWeight n*afm_mu n i)
    ∂uniformLaw (fun u : Fin n → Bool => fun j => afm_mu n j+sign (u j))) = _
  rw [NewFiniteCompletion.coord_integral Bool (fun i b => afm_mu n i+sign b) i
    (fun x => (alternatingWeight n*x-alternatingWeight n*afm_mu n i)*
      (alternatingWeight n*x-alternatingWeight n*afm_mu n i)) (by fun_prop)]
  simp [Fintype.sum_bool, sign] <;> ring

lemma afm_meanVariance (n : ℕ) (hn : 0 < n) :
    meanVariance (alternatingModel n) = alternatingWeight n^2 := by
  simp only [meanVariance, afm_diag, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne')

lemma afm_parity (n : ℕ) : 2*((n+1)/2) = n+alternatingParity n := by
  unfold alternatingParity
  omega

lemma afm_weight_relation (n : ℕ) (hn : 0 < n) :
    alternatingWeight n * ((n : ℝ)+(alternatingParity n : ℝ)) = n := by
  have he : (n : ℝ)+(alternatingParity n : ℝ) = 2*((n+1)/2 : ℕ) := by
    exact_mod_cast (afm_parity n).symm
  rw [he]
  unfold alternatingWeight
  have hp : (0 : ℝ) < ((n+1)/2 : ℕ) := by exact_mod_cast (show 0 < (n+1)/2 by omega)
  field_simp

lemma afm_spread_exact (n : ℕ) (hn : 0 < n) :
    meanSpread (alternatingModel n) = alternatingSpread n := by
  rw [afm_spread n hn]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hr := afm_weight_relation n hn
  have hr' : alternatingWeight n*(alternatingParity n : ℝ) = (n : ℝ)*(1-alternatingWeight n) := by nlinarith [hr]
  have hs := congrArg (fun x : ℝ => x^2) hr'
  unfold alternatingSpread
  field_simp
  nlinarith [hs]

lemma afm_delta_sum (n : ℕ) (hn : 0 < n) :
    (∑ i, delta (alternatingModel n) i) = 0 := by
  simp only [delta, afm_mean, afm_beta n hn, Finset.sum_sub_distrib,
    ← Finset.mul_sum, afm_sum_mu, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold alternatingWeight
  have hp : (0 : ℝ) < ((n+1)/2 : ℕ) := by exact_mod_cast (show 0 < (n+1)/2 by omega)
  field_simp
  ring

lemma afm_sign_sq (u : Bool) : sign u^2 = 1 := by cases u <;> norm_num [sign]

lemma afm_sample_identity (n : ℕ) (hn : 0 < n) (u : Fin n → Bool) :
    sampleVariance (weighted (alternatingModel n) (alternatingOutcome n u)) =
      alternatingWeight n^2+meanSpread (alternatingModel n)+
      2*alternatingWeight n*(∑ i, delta (alternatingModel n) i*sign (u i))/(n : ℝ)-
      alternatingWeight n^2*(∑ i, sign (u i))^2/(n : ℝ)^2 := by
  let t := alternatingWeight n
  let d := delta (alternatingModel n)
  let S := ∑ i, sign (u i)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hx (i : Fin n) : weighted (alternatingModel n) (alternatingOutcome n u) i =
      1+d i+t*sign (u i) := by
    dsimp [d, delta]
    rw [afm_mean, afm_beta n hn]
    dsimp [weighted, alternatingModel, alternatingOutcome, afm_mu, t]
    ring
  have hs : average (weighted (alternatingModel n) (alternatingOutcome n u)) = 1+t*S/n := by
    simp only [average, hx, Finset.sum_add_distrib, ← Finset.mul_sum,
      show ∑ i, d i = 0 from afm_delta_sum n hn, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, add_zero]
    dsimp [S]; field_simp <;> ring
  have hc (i : Fin n) : centered (weighted (alternatingModel n) (alternatingOutcome n u)) i =
      d i+t*sign (u i)-t*S/n := by simp only [centered, hx, hs]; ring
  have hterm (i : Fin n) : (d i+t*sign (u i)-t*S/n)^2 =
      d i^2+t^2+2*t*(d i*sign (u i))-
      2*t*S/n*d i-2*t^2*S/n*sign (u i)+(t*S/n)^2 := by
    calc
      _ = d i^2+t^2*(sign (u i))^2+2*t*(d i*sign (u i))-
          2*t*S/n*d i-2*t^2*S/n*sign (u i)+(t*S/n)^2 := by ring
      _ = _ := by rw [afm_sign_sq]; ring
  have hd : ∑ i, d i^2 = n*meanSpread (alternatingModel n) := by
    unfold meanSpread
    dsimp [d]
    field_simp
  unfold sampleVariance
  simp only [hc, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    hd, show ∑ i, d i = 0 from afm_delta_sum n hn, mul_zero, sub_zero]
  change _ = t^2+meanSpread (alternatingModel n)+2*t*(∑ i, d i*sign (u i))/n-t^2*S^2/(n:ℝ)^2
  dsimp [S]
  field_simp
  ring

/-! Normalized finite expectation, with a head-coordinate recurrence. -/

def afm_avg (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ := (∑ u, f u)/(2 : ℝ)^n

lemma afm_avg_const (n : ℕ) (c : ℝ) : afm_avg n (fun _ => c) = c := by
  simp [afm_avg, Fintype.card_fun, Fintype.card_bool]

lemma afm_avg_add (n : ℕ) (f g : (Fin n → Bool) → ℝ) :
    afm_avg n (fun u => f u+g u) = afm_avg n f+afm_avg n g := by
  simp [afm_avg, Finset.sum_add_distrib, add_div]

lemma afm_avg_sub (n : ℕ) (f g : (Fin n → Bool) → ℝ) :
    afm_avg n (fun u => f u-g u) = afm_avg n f-afm_avg n g := by
  simp [afm_avg, Finset.sum_sub_distrib, sub_div]

lemma afm_avg_mul (n : ℕ) (c : ℝ) (f : (Fin n → Bool) → ℝ) :
    afm_avg n (fun u => c*f u) = c*afm_avg n f := by
  simp [afm_avg, ← Finset.mul_sum, mul_div_assoc]

lemma afm_avg_div (n : ℕ) (f : (Fin n → Bool) → ℝ) (c : ℝ) :
    afm_avg n (fun u => f u/c) = afm_avg n f/c := by
  simp only [afm_avg, ← Finset.sum_div]
  ring

def afm_headEquiv (n : ℕ) : (Fin (n+1) → Bool) ≃ Bool × (Fin n → Bool) :=
  { toFun := fun u => (u 0, Fin.tail u)
    invFun := fun p => Fin.cons p.1 p.2
    left_inv := Fin.cons_self_tail
    right_inv := fun p => by simp }

lemma afm_avg_cons (n : ℕ) (f : (Fin (n+1) → Bool) → ℝ) :
    afm_avg (n+1) f = afm_avg n (fun u => f (Fin.cons false u)+f (Fin.cons true u))/2 := by
  have he := Fintype.sum_equiv (afm_headEquiv n) f
    (fun p => f (Fin.cons p.1 p.2)) (fun u => congrArg f (Fin.cons_self_tail u).symm)
  unfold afm_avg
  rw [he]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]
  rw [pow_succ]
  ring

lemma afm_linear_moments (n : ℕ) (c : Fin n → ℝ) :
    afm_avg n (fun u => ∑ i, c i*sign (u i)) = 0 ∧
    afm_avg n (fun u => (∑ i, c i*sign (u i))^2) = ∑ i, c i^2 := by
  induction n with
  | zero => simp [afm_avg]
  | succ n ih =>
    have h := ih (fun i => c i.succ)
    have he (z : Bool) (u : Fin n → Bool) :
        (∑ i : Fin (n+1), c i*sign ((Fin.cons z u : Fin (n+1) → Bool) i)) = c 0*sign z+∑ i, c i.succ*sign (u i) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    constructor
    · rw [afm_avg_cons]
      simp_rw [he]
      have hp (u : Fin n → Bool) :
          (c 0*sign false+∑ i, c i.succ*sign (u i))+
          (c 0*sign true+∑ i, c i.succ*sign (u i)) = 2*(∑ i, c i.succ*sign (u i)) := by
        simp [sign]; ring
      simp_rw [hp]
      rw [afm_avg_mul, h.1]
      ring
    · rw [afm_avg_cons]
      simp_rw [he]
      have hp (u : Fin n → Bool) :
          (c 0*sign false+∑ i, c i.succ*sign (u i))^2+
          (c 0*sign true+∑ i, c i.succ*sign (u i))^2 =
          2*(c 0)^2+2*(∑ i, c i.succ*sign (u i))^2 := by simp [sign]; ring
      simp_rw [hp]
      rw [afm_avg_add, afm_avg_const, afm_avg_mul, h.2, Fin.sum_univ_succ]
      ring

lemma afm_signsum_second (n : ℕ) :
    afm_avg n (fun u => (∑ i, sign (u i))^2) = n := by
  simpa using (afm_linear_moments n (fun _ => 1)).2

lemma afm_signsum_fourth (n : ℕ) :
    afm_avg n (fun u => (∑ i, sign (u i))^4) = 3*(n : ℝ)^2-2*n := by
  induction n with
  | zero => simp [afm_avg]
  | succ n ih =>
    rw [afm_avg_cons]
    have he (z : Bool) (u : Fin n → Bool) :
        (∑ i : Fin (n+1), sign ((Fin.cons z u : Fin (n+1) → Bool) i)) = sign z+∑ i, sign (u i) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    simp_rw [he]
    have hp (u : Fin n → Bool) :
        (sign false+∑ i, sign (u i))^4+(sign true+∑ i, sign (u i))^4 =
        2*(∑ i, sign (u i))^4+12*(∑ i, sign (u i))^2+2 := by simp [sign]; ring
    simp_rw [hp]
    rw [afm_avg_add, afm_avg_add, afm_avg_mul, afm_avg_mul, afm_avg_const,
      afm_signsum_second, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

def afm_flipEquiv (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) :=
  { toFun := fun u i => !(u i)
    invFun := fun u i => !(u i)
    left_inv := fun u => by funext i; simp
    right_inv := fun u => by funext i; simp }

lemma afm_mixed_odd (n : ℕ) (c : Fin n → ℝ) :
    afm_avg n (fun u => (∑ i, c i*sign (u i))*(∑ i, sign (u i))^2) = 0 := by
  have hf (u : Bool) : sign (!u) = -sign u := by cases u <;> norm_num [sign]
  let f := fun u : Fin n → Bool => (∑ i, c i*sign (u i))*(∑ i, sign (u i))^2
  have he : (∑ u, f (afm_flipEquiv n u)) = ∑ u, f u := (afm_flipEquiv n).sum_comp f
  have hh (u : Fin n → Bool) : f (afm_flipEquiv n u) = -f u := by
    simp only [f, afm_flipEquiv, Equiv.coe_fn_mk, hf, mul_neg, Finset.sum_neg_distrib]
    ring
  simp_rw [hh] at he
  rw [Finset.sum_neg_distrib] at he
  have hz : (∑ u, f u) = 0 := by linarith
  exact div_eq_zero_iff.mpr (Or.inl hz)

lemma afm_expectation (n : ℕ) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    expectation (alternatingModel n) f = afm_avg n (fun u => f (alternatingOutcome n u)) := by
  unfold expectation
  rw [show (alternatingModel n).law = uniformLaw (alternatingOutcome n) from rfl,
    uniform_integral _ (measurable_of_finite _) f hf]
  simp only [afm_avg, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

lemma afm_remainder_value (n : ℕ) (hn : 0 < n) (u : Fin n → Bool) :
    varianceRemainder (alternatingModel n) (alternatingOutcome n u) =
      2*alternatingWeight n*(∑ i, delta (alternatingModel n) i*sign (u i))/(n : ℝ)-
      alternatingWeight n^2*(∑ i, sign (u i))^2/(n : ℝ)^2 := by
  rw [varianceRemainder, afm_sample_identity n hn u, afm_meanVariance n hn]
  ring

lemma afm_remainder_moments (n : ℕ) (hn : 0 < n) :
    expectation (alternatingModel n) (varianceRemainder (alternatingModel n)) =
      -alternatingWeight n^2/(n : ℝ) ∧
    expectation (alternatingModel n) (fun y => varianceRemainder (alternatingModel n) y^2) =
      4*alternatingWeight n^2*meanSpread (alternatingModel n)/(n : ℝ)+
      alternatingWeight n^4*(3/(n : ℝ)^2-2/(n : ℝ)^3) := by
  let t := alternatingWeight n
  let d := delta (alternatingModel n)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd : (∑ i, d i^2) = n*meanSpread (alternatingModel n) := by
    unfold meanSpread
    dsimp [d]
    field_simp
  have hR : Measurable (varianceRemainder (alternatingModel n)) := by
    unfold varianceRemainder sampleVariance centered average weighted; fun_prop
  constructor
  · rw [afm_expectation n _ hR]
    simp_rw [afm_remainder_value n hn]
    rw [afm_avg_sub, afm_avg_div, afm_avg_mul, afm_avg_div, afm_avg_mul,
      (afm_linear_moments n d).1, afm_signsum_second]
    field_simp <;> ring
  · rw [afm_expectation n _ (hR.pow_const 2)]
    simp_rw [afm_remainder_value n hn]
    have he (u : Fin n → Bool) :
        (2*t*(∑ i, d i*sign (u i))/(n : ℝ)-t^2*(∑ i, sign (u i))^2/(n : ℝ)^2)^2 =
        4*t^2/(n : ℝ)^2*(∑ i, d i*sign (u i))^2-
        4*t^3/(n : ℝ)^3*((∑ i, d i*sign (u i))*(∑ i, sign (u i))^2)+
        t^4/(n : ℝ)^4*(∑ i, sign (u i))^4 := by ring
    change afm_avg n (fun u => (2*t*(∑ i, d i*sign (u i))/(n : ℝ)-
      t^2*(∑ i, sign (u i))^2/(n : ℝ)^2)^2) = _
    simp_rw [he]
    rw [afm_avg_add, afm_avg_sub, afm_avg_mul, afm_avg_mul, afm_avg_mul,
      (afm_linear_moments n d).2, afm_mixed_odd, afm_signsum_fourth, hd]
    field_simp <;> ring

lemma afm_V2_empty (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) :
    (n : ℝ)*V2 (emptyGraph n) x = sampleVariance x := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [V2, adjacency, emptyGraph]
  field_simp

lemma afm_even_bounds (n : ℕ) (hn : 0 < n) (heven : Even n) :
    alternatingWeight n=1 ∧ meanSpread (alternatingModel n)=1 ∧
      expectation (alternatingModel n) (fun y => ((n : ℝ)*V2 (alternatingModel n).G
        (weighted (alternatingModel n) y)-1-1)^2)=
        4/(n : ℝ)+3/(n : ℝ)^2-2/(n : ℝ)^3 ∧
      1-4*(4/(n : ℝ)+3/(n : ℝ)^2-2/(n : ℝ)^3) ≤
        probability (alternatingModel n) {y | |(n : ℝ)*V2 (alternatingModel n).G
          (weighted (alternatingModel n) y)-1| > 1/2} ∧
      1-4*(4/(n : ℝ)+3/(n : ℝ)^2-2/(n : ℝ)^3) ≤
        probability (alternatingModel n) {y | |(n : ℝ)*V2 (alternatingModel n).G
          (weighted (alternatingModel n) y)-1| < 3/2} := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : alternatingParity n = 0 := by
    rcases heven with ⟨q, hq⟩
    unfold alternatingParity
    omega
  have ht : alternatingWeight n = 1 := by
    have h := afm_weight_relation n hn
    simp only [hp, Nat.cast_zero, add_zero] at h
    exact mul_right_cancel₀ hn0 (by simpa using h)
  have hM : meanSpread (alternatingModel n) = 1 := by
    rw [afm_spread_exact n hn]
    simp [alternatingSpread, ht, hp]
  let m := alternatingModel n
  let R := fun y => (n : ℝ)*V2 m.G (weighted m y)-1-1
  let v : ℝ := 4/(n : ℝ)+3/(n : ℝ)^2-2/(n : ℝ)^3
  let : IsProbabilityMeasure m.law := m.probability
  have he (y : Fin n → ℝ) : R y = varianceRemainder m y := by
    dsimp [R, m]
    rw [show (alternatingModel n).G = emptyGraph n from rfl, afm_V2_empty n hn]
    rw [varianceRemainder, afm_meanVariance n hn, ht, hM]
    norm_num
  have hmoment : expectation m (fun y => R y^2) = v := by
    simp_rw [he]
    rw [(afm_remainder_moments n hn).2, ht, hM]
    dsimp [v]
    ring
  have hR : Measurable R := by
    dsimp [R]
    unfold V2 sampleVariance centered average weighted
    fun_prop
  have hInt : Integrable (fun y => R y^2) m.law := by
    have hLp : MemLp (fun y => R y^2) 1 m.law :=
      NewFiniteCompletion.finite_memLp (alternatingOutcome n) _ (hR.pow_const 2) 1
    exact hLp.integrable (by norm_num)
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := m.law) (ae_of_all _ fun y => sq_nonneg (R y)) hInt (1/4)
  change (1/4)*m.law.real {y | 1/4 ≤ R y^2} ≤ expectation m (fun y => R y^2) at hMarkov
  rw [hmoment] at hMarkov
  have hbad : m.law.real {y | 1/4 ≤ R y^2} ≤ 4*v := by linarith
  have hgood : 1-4*v ≤ m.law.real {y | 1/4 ≤ R y^2}ᶜ := by
    rw [probReal_compl_eq_one_sub (measurableSet_le measurable_const (hR.pow_const 2))]
    linarith
  refine ⟨ht, hM, hmoment, hgood.trans ?_, hgood.trans ?_⟩
  · apply measureReal_mono (μ := m.law) ?_ (measure_ne_top _ _)
    intro y hy
    have hy' : R y^2 < 1/4 := lt_of_not_ge hy
    have hleft : -(1/2 : ℝ) < R y := by nlinarith [sq_nonneg (R y+1/2)]
    change 1/2 < |(n : ℝ)*V2 m.G (weighted m y)-1|
    have heq : (n : ℝ)*V2 m.G (weighted m y)-1 = R y+1 := by dsimp [R]; ring
    rw [heq]
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  · apply measureReal_mono (μ := m.law) ?_ (measure_ne_top _ _)
    intro y hy
    have hy' : R y^2 < 1/4 := lt_of_not_ge hy
    have hl : -(1/2 : ℝ) < R y := by nlinarith [sq_nonneg (R y+1/2)]
    have hu : R y < (1/2 : ℝ) := by nlinarith [sq_nonneg (R y-1/2)]
    change |(n : ℝ)*V2 m.G (weighted m y)-1| < 3/2
    have heq : (n : ℝ)*V2 m.G (weighted m y)-1 = R y+1 := by dsimp [R]; ring
    rw [heq]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem alternating_finite_moments_proof (k : ℕ) :
    let n := k+1
    let m := alternatingModel n
    let t := alternatingWeight n
    1/2 ≤ t ∧ t ≤ 1 ∧ beta m=1 ∧
    (∀ i, covariance m i i=t^2 ∧
      delta m i=t*(if i.val%2=0 then 2 else 0)-1) ∧
    meanSpread m=alternatingSpread n ∧
    (∀ u : Fin n → Bool,
      sampleVariance (weighted m (alternatingOutcome n u)) = t^2+meanSpread m+
        2*t*(∑ i, delta m i*sign (u i))/(n : ℝ)-t^2*(∑ i, sign (u i))^2/(n : ℝ)^2) ∧
    expectation m (varianceRemainder m)=-t^2/(n : ℝ) ∧
    expectation m (fun y => varianceRemainder m y^2) =
      4*t^2*meanSpread m/(n : ℝ)+t^4*(3/(n : ℝ)^2-2/(n : ℝ)^3) ∧
    (Even n → t=1 ∧ meanSpread m=1 ∧
      expectation m (fun y => ((n : ℝ)*V2 m.G (weighted m y)-1-1)^2)=
        4/(n : ℝ)+3/(n : ℝ)^2-2/(n : ℝ)^3 ∧
      1-4*(4/(n : ℝ)+3/(n : ℝ)^2-2/(n : ℝ)^3) ≤
        probability m {y | |(n : ℝ)*V2 m.G (weighted m y)-1| > 1/2} ∧
      1-4*(4/(n : ℝ)+3/(n : ℝ)^2-2/(n : ℝ)^3) ≤
        probability m {y | |(n : ℝ)*V2 m.G (weighted m y)-1| < 3/2}) := by
  dsimp only
  have hn : 0 < k+1 := by omega
  refine ⟨(afm_weight_bounds _ hn).1, (afm_weight_bounds _ hn).2.1, afm_beta _ hn,
    ?_, afm_spread_exact _ hn, afm_sample_identity _ hn,
    (afm_remainder_moments _ hn).1, (afm_remainder_moments _ hn).2, afm_even_bounds _ hn⟩
  intro i
  refine ⟨afm_diag _ i, ?_⟩
  simp only [delta, afm_mean, afm_beta _ hn, afm_mu]

end
end AronowAudit.P011.Wave1
