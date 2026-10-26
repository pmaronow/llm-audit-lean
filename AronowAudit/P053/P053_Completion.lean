import AronowAudit.P053.P053_Audit
import AronowAudit.P053.P053_CausalBridge

/-!
Variance-estimator limits for Aronow and Offer-Westort (2017).

This module proves the estimator algebra and convergence implications from a
shared moment-LLN interface. P053_MomentConsistency proves that interface from
bounded-fourth-moment regularity.
-/

namespace AronowAudit.P053

open scoped BigOperators
open Filter

noncomputable section

attribute [local instance] Classical.propDecidable

theorem randomizationProbability_nonneg (P : Population)
    (A : Finset (Fin P.size) → Prop) : 0 ≤ randomizationProbability P A := by
  classical
  unfold randomizationProbability
  positivity

theorem randomizationProbability_mono (P : Population)
    (A B : Finset (Fin P.size) → Prop)
    (h : ∀ z ∈ support P.n1, A z → B z) :
    randomizationProbability P A ≤ randomizationProbability P B := by
  classical
  unfold randomizationProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hz, ha⟩
    exact Finset.mem_filter.mpr ⟨hz, h z hz ha⟩)

theorem randomizationProbability_or_le (P : Population)
    (A B : Finset (Fin P.size) → Prop) :
    randomizationProbability P (fun z => A z ∨ B z) ≤
      randomizationProbability P A + randomizationProbability P B := by
  classical
  unfold randomizationProbability
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  norm_cast
  calc
    _ ≤ (((support P.n1).filter A) ∪ ((support P.n1).filter B)).card := by
      apply Finset.card_le_card
      intro z hz
      rcases (@Finset.mem_filter _ (fun z => A z ∨ B z)
        (fun z => Classical.propDecidable (A z ∨ B z)) _ z).mp hz with ⟨hz, ha | hb⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, ha⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hb⟩)
    _ ≤ _ := Finset.card_union_le _ _


theorem inProbability_congr_eventually (E : ℕ → Population)
    (X Y : (k : ℕ) → Finset (Fin (E k).size) → ℝ) (c : ℝ)
    (h : ∀ᶠ k in atTop, ∀ z ∈ support (E k).n1, X k z = Y k z)
    (hX : InProbability E X c) : InProbability E Y c := by
  intro ε hε
  apply (hX ε hε).congr'
  filter_upwards [h] with k hk
  classical
  unfold randomizationProbability
  have he : (support (E k).n1).filter (fun z => ε < |X k z-c|) =
      (support (E k).n1).filter (fun z => ε < |Y k z-c|) := by
    apply Finset.filter_congr
    intro z hz
    rw [hk z hz]
  exact congrArg (fun s : Finset (Finset (Fin (E k).size)) =>
    (s.card : ℝ) / ((support (ι := Fin (E k).size) (E k).n1).card : ℝ)) he

theorem inProbability_deterministic (E : ℕ → Population) (a : ℕ → ℝ) (c : ℝ)
    (h : Tendsto a atTop (nhds c)) :
    InProbability E (fun k _ => a k) c := by
  intro ε hε
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) ε hε
  filter_upwards [eventually_ge_atTop N] with k hk
  have hk := hN k hk
  rw [Real.dist_eq] at hk
  have hn : ¬ ε < |a k - c| := not_lt.mpr (le_of_lt hk)
  classical
  simp [randomizationProbability, hn]

theorem inProbability_continuous_pair (E : ℕ → Population)
    (X Y : (k : ℕ) → Finset (Fin (E k).size) → ℝ) (a b : ℝ)
    (hX : InProbability E X a) (hY : InProbability E Y b)
    (f : ℝ × ℝ → ℝ) (hf : ContinuousAt f (a,b)) :
    InProbability E (fun k z => f (X k z, Y k z)) (f (a,b)) := by
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hf ε hε
  have hd : 0 < δ / 2 := by positivity
  have hlim := (hX (δ / 2) hd).add (hY (δ / 2) hd)
  apply squeeze_zero
    (fun k => randomizationProbability_nonneg (E k) _)
    (fun k => ?_) (by simpa using hlim)
  calc
    randomizationProbability (E k)
      (fun z => ε < |f (X k z,Y k z)-f (a,b)|) ≤
        randomizationProbability (E k)
          (fun z => δ / 2 < |X k z-a| ∨ δ / 2 < |Y k z-b|) := by
      apply randomizationProbability_mono
      intro z hz he
      by_contra hn
      push Not at hn
      have hp : dist (X k z,Y k z) (a,b) < δ := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        exact max_lt (by linarith [hn.1]) (by linarith [hn.2])
      have hh := hclose hp
      rw [Real.dist_eq] at hh
      linarith
    _ ≤ _ := randomizationProbability_or_le (E k) _ _

theorem inProbability_add (E : ℕ → Population)
    (X Y : (k : ℕ) → Finset (Fin (E k).size) → ℝ) (a b : ℝ)
    (hX : InProbability E X a) (hY : InProbability E Y b) :
    InProbability E (fun k z => X k z + Y k z) (a+b) :=
  inProbability_continuous_pair E X Y a b hX hY (fun t => t.1+t.2) (by fun_prop)

theorem inProbability_sub (E : ℕ → Population)
    (X Y : (k : ℕ) → Finset (Fin (E k).size) → ℝ) (a b : ℝ)
    (hX : InProbability E X a) (hY : InProbability E Y b) :
    InProbability E (fun k z => X k z - Y k z) (a-b) :=
  inProbability_continuous_pair E X Y a b hX hY (fun t => t.1-t.2) (by fun_prop)

theorem inProbability_mul (E : ℕ → Population)
    (X Y : (k : ℕ) → Finset (Fin (E k).size) → ℝ) (a b : ℝ)
    (hX : InProbability E X a) (hY : InProbability E Y b) :
    InProbability E (fun k z => X k z * Y k z) (a*b) :=
  inProbability_continuous_pair E X Y a b hX hY (fun t => t.1*t.2) (by fun_prop)

theorem inProbability_div (E : ℕ → Population)
    (X Y : (k : ℕ) → Finset (Fin (E k).size) → ℝ) (a b : ℝ)
    (hX : InProbability E X a) (hY : InProbability E Y b) (hb : b ≠ 0) :
    InProbability E (fun k z => X k z / Y k z) (a/b) :=
  inProbability_continuous_pair E X Y a b hX hY (fun t => t.1/t.2)
    (by exact continuousAt_fst.div continuousAt_snd hb)

theorem inProbability_sq (E : ℕ → Population)
    (X : (k : ℕ) → Finset (Fin (E k).size) → ℝ) (a : ℝ)
    (hX : InProbability E X a) :
    InProbability E (fun k z => (X k z)^2) (a^2) := by
  simpa only [pow_two] using inProbability_mul E X X a a hX hX

theorem regularity_allocation_control (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ) :
    Tendsto (fun k => ((E k).n0 : ℝ)/(E k).size) atTop (nhds (1-p)) := by
  apply (tendsto_const_nhds.sub h.allocation).congr'
  filter_upwards [h.arm_sizes] with k hk
  have hN : ((E k).size : ℝ) ≠ 0 := by
    exact_mod_cast (by dsimp [Population.size]; omega : (E k).size ≠ 0)
  simp only [Population.size, Nat.cast_add] at hN ⊢
  field_simp <;> ring

theorem regularity_inverse_size (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ) :
    Tendsto (fun k => 1 / ((E k).size : ℝ)) atTop (nhds 0) := by
  have hN : Tendsto (fun k => ((E k).size : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr h.size_diverges
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hN

/-- A standard SRS moment law of large numbers, exposed as a shared interface.
The theorem `finitePopulationMomentLLN` in P053_MomentConsistency proves this
interface from bounded-fourth-moment regularity.
The hypothesis concerns raw arm sample variances and the difference in means;
it does not assume any Fisher/OLS/Neyman variance-estimator conclusion below.
Under the bounded fourth moments in Regularity, these are the usual
sampling-without-replacement moment consistency results (Li and Ding, 2017,
Proposition 3 and Lemma A.3; https://arxiv.org/abs/1610.04821).
-/
def FinitePopulationMomentLLN : Prop :=
  ∀ (E : ℕ → Population) (p v1 v0 vt τ : ℝ), Regularity E p v1 v0 vt τ →
    InProbability E (fun k z => sampleVariance z (observed (E k) z)) v1 ∧
    InProbability E (fun k z => sampleVariance zᶜ (observed (E k) z)) v0 ∧
    InProbability E (fun k z => estimate (E k) z) τ

/-- Neyman's scaled variance-estimator limit under regularity and convergence
in probability of the two arm sample variances.
All estimator algebra and convergence operations are proved in this module.
-/
theorem neyman_variance_limit_of_arm_consistency
    (E : ℕ → Population) (p v1 v0 vt τ : ℝ) (h : Regularity E p v1 v0 vt τ)
    (h1 : InProbability E (fun k z => sampleVariance z (observed (E k) z)) v1)
    (h0 : InProbability E (fun k z => sampleVariance zᶜ (observed (E k) z)) v0) :
    InProbability E (fun k z => ((E k).size : ℝ)*neymanVariance (E k) z)
      (neymanLimit p v1 v0) := by
  have ha := inProbability_deterministic E _ _ h.allocation
  have hb := inProbability_deterministic E _ _
    (regularity_allocation_control E p v1 v0 vt τ h)
  have hlim := inProbability_add E _ _ _ _
    (inProbability_div E _ _ _ _ h1 ha (ne_of_gt h.p_positive))
    (inProbability_div E _ _ _ _ h0 hb (by linarith [h.p_less_one]))
  apply inProbability_congr_eventually E _ _ _ _ hlim
  filter_upwards [h.arm_sizes] with k hk
  intro z hz
  have hN : ((E k).size : ℝ) ≠ 0 := by
    exact_mod_cast (by dsimp [Population.size]; omega : (E k).size ≠ 0)
  have hA : ((E k).n1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : (E k).n1 ≠ 0)
  have hB : ((E k).n0 : ℝ) ≠ 0 := by exact_mod_cast (by omega : (E k).n0 ≠ 0)
  dsimp [neymanVariance]
  field_simp <;> ring

/-- Universal-LLN specialization of the proved Neyman limit implication. -/
theorem neyman_variance_limit_of_momentLLN (hLLN : FinitePopulationMomentLLN)
    (E : ℕ → Population) (p v1 v0 vt τ : ℝ) (h : Regularity E p v1 v0 vt τ) :
    InProbability E (fun k z => ((E k).size : ℝ)*neymanVariance (E k) z)
      (neymanLimit p v1 v0) :=
  neyman_variance_limit_of_arm_consistency E p v1 v0 vt τ h
    (hLLN E p v1 v0 vt τ h).1 (hLLN E p v1 v0 vt τ h).2.1

/-- Deterministic OLS coefficients, normalized by population size so all
denominators have nonzero limits. -/
def olsCoefficient (E : ℕ → Population) (treatment : Bool) (k : ℕ) : ℝ :=
  let r1 := ((E k).n1 : ℝ)/(E k).size
  let r0 := ((E k).n0 : ℝ)/(E k).size
  let invN := 1/((E k).size : ℝ)
  ((if treatment then r1 else r0)-invN) / ((1-2*invN)*r1*r0)

theorem regularity_ols_coefficients (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ) :
    Tendsto (olsCoefficient E true) atTop (nhds (1/(1-p))) ∧
    Tendsto (olsCoefficient E false) atTop (nhds (1/p)) := by
  have h0 := regularity_allocation_control E p v1 v0 vt τ h
  have hi := regularity_inverse_size E p v1 v0 vt τ h
  have hc : Tendsto (fun k => 1-2*(1/((E k).size : ℝ)))
      atTop (nhds (1-2*(0:ℝ))) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hi)
  have hd := (hc.mul h.allocation).mul h0
  have hp : p ≠ 0 := ne_of_gt h.p_positive
  have hp0 : 1-p ≠ 0 := by linarith [h.p_less_one]
  have hden : (1-2*(0:ℝ))*p*(1-p) ≠ 0 := by simp [hp,hp0]
  constructor
  · have hh := (h.allocation.sub hi).div hd hden
    have he : (p-0)/((1-2*(0:ℝ))*p*(1-p)) = 1/(1-p) := by field_simp; ring
    rw [he] at hh
    apply hh.congr'
    filter_upwards [] with k
    rfl
  · have hh := (h0.sub hi).div hd hden
    have he : ((1-p)-0)/((1-2*(0:ℝ))*p*(1-p)) = 1/p := by field_simp; ring
    rw [he] at hh
    apply hh.congr'
    filter_upwards [] with k
    rfl

/-- The OLS variance limit under regularity and convergence in probability
of the two arm sample variances. -/
theorem ols_variance_limit_of_arm_consistency
    (E : ℕ → Population) (p v1 v0 vt τ : ℝ) (h : Regularity E p v1 v0 vt τ)
    (h1 : InProbability E (fun k z => sampleVariance z (observed (E k) z)) v1)
    (h0 : InProbability E (fun k z => sampleVariance zᶜ (observed (E k) z)) v0) :
    InProbability E (fun k z => ((E k).size : ℝ)*olsVariance (E k) z)
      (olsLimit p v1 v0) := by
  obtain ⟨hc1,hc0⟩ := regularity_ols_coefficients E p v1 v0 vt τ h
  have hlim := inProbability_add E _ _ _ _
    (inProbability_mul E _ _ _ _ (inProbability_deterministic E _ _ hc1) h1)
    (inProbability_mul E _ _ _ _ (inProbability_deterministic E _ _ hc0) h0)
  have he : 1/(1-p)*v1 + 1/p*v0 = olsLimit p v1 v0 := by
    simp only [olsLimit, div_eq_mul_inv]
    ring
  rw [he] at hlim
  apply inProbability_congr_eventually E _ _ _ _ hlim
  filter_upwards [h.arm_sizes] with k hk
  intro z hz
  have hN : ((E k).size : ℝ) ≠ 0 := by
    exact_mod_cast (by dsimp [Population.size]; omega : (E k).size ≠ 0)
  have hA : ((E k).n1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : (E k).n1 ≠ 0)
  have hB : ((E k).n0 : ℝ) ≠ 0 := by exact_mod_cast (by omega : (E k).n0 ≠ 0)
  have hN2 : ((E k).size : ℝ)-2 ≠ 0 := by
    have hn : (4:ℝ) ≤ (E k).size := by
      exact_mod_cast (show 4 ≤ (E k).size by dsimp [Population.size]; omega)
    linarith
  dsimp [olsCoefficient, olsVariance]
  rw [residualSS_sample_variances (E k) hk.1 hk.2 z hz]
  field_simp
  push_cast
  ring

/-- Universal-LLN specialization of the proved OLS limit implication. -/
theorem ols_variance_limit_of_momentLLN (hLLN : FinitePopulationMomentLLN)
    (E : ℕ → Population) (p v1 v0 vt τ : ℝ) (h : Regularity E p v1 v0 vt τ) :
    InProbability E (fun k z => ((E k).size : ℝ)*olsVariance (E k) z)
      (olsLimit p v1 v0) :=
  ols_variance_limit_of_arm_consistency E p v1 v0 vt τ h
    (hLLN E p v1 v0 vt τ h).1 (hLLN E p v1 v0 vt τ h).2.1

/-- The corrected asymptotic Neyman bound, conditional on the single
explicit universal SRS moment theorem rather than any target conclusion. -/
theorem neyman_asymptotic_bound_of_momentLLN (hLLN : FinitePopulationMomentLLN)
    (E : ℕ → Population) (p v1 v0 vt τ : ℝ) (h : Regularity E p v1 v0 vt τ) :
    Tendsto (fun k => ((E k).size : ℝ)*randomizationVariance (E k) (estimate (E k)))
      atTop (nhds (neymanLimit p v1 v0-vt)) ∧
    neymanLimit p v1 v0-vt ≤ neymanLimit p v1 v0 ∧
    InProbability E (fun k z => ((E k).size : ℝ)*neymanVariance (E k) z)
      (neymanLimit p v1 v0) := by
  exact ⟨(actual_variance_limit_bound E p v1 v0 vt τ h).1,
    (actual_variance_limit_bound E p v1 v0 vt τ h).2,
    neyman_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h⟩

theorem regularity_oracle_ols_limit (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ) :
    Tendsto (fun k => ((E k).size : ℝ)*
      (populationVariance (E k) (E k).Y1/(E k).n0 +
       populationVariance (E k) (E k).Y0/(E k).n1)) atTop (nhds (olsLimit p v1 v0)) := by
  have hp : p ≠ 0 := ne_of_gt h.p_positive
  have hp0 : 1-p ≠ 0 := by linarith [h.p_less_one]
  have hh := (h.variance1.div (regularity_allocation_control E p v1 v0 vt τ h) hp0).add
    (h.variance0.div h.allocation hp)
  apply hh.congr'
  filter_upwards [h.arm_sizes] with k hk
  have hN : ((E k).size : ℝ) ≠ 0 := by
    exact_mod_cast (by dsimp [Population.size]; omega : (E k).size ≠ 0)
  have hA : ((E k).n1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : (E k).n1 ≠ 0)
  have hB : ((E k).n0 : ℝ) ≠ 0 := by exact_mod_cast (by omega : (E k).n0 ≠ 0)
  simp only [Pi.div_apply]
  field_simp <;> ring

theorem regularity_oracle_neyman_limit (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ) :
    Tendsto (fun k => ((E k).size : ℝ)*
      (populationVariance (E k) (E k).Y1/(E k).n1 +
       populationVariance (E k) (E k).Y0/(E k).n0)) atTop (nhds (neymanLimit p v1 v0)) := by
  have hp : p ≠ 0 := ne_of_gt h.p_positive
  have hp0 : 1-p ≠ 0 := by linarith [h.p_less_one]
  have hh := (h.variance1.div h.allocation hp).add
    (h.variance0.div (regularity_allocation_control E p v1 v0 vt τ h) hp0)
  apply hh.congr'
  filter_upwards [h.arm_sizes] with k hk
  have hN : ((E k).size : ℝ) ≠ 0 := by
    exact_mod_cast (by dsimp [Population.size]; omega : (E k).size ≠ 0)
  have hA : ((E k).n1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : (E k).n1 ≠ 0)
  have hB : ((E k).n0 : ℝ) ≠ 0 := by exact_mod_cast (by omega : (E k).n0 ≠ 0)
  simp only [Pi.div_apply]
  field_simp <;> ring

theorem fisher_variance_limit_of_momentLLN (hLLN : FinitePopulationMomentLLN)
    (E : ℕ → Population) (p v1 v0 vt τ : ℝ) (h : Regularity E p v1 v0 vt τ) :
    InProbability E (fun k z => ((E k).size : ℝ)*fisherVariance (E k) z)
      (olsLimit p v1 v0+τ^2) := by
  have hOLS := ols_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h
  have hi := regularity_inverse_size E p v1 v0 vt τ h
  have hOLSzero : InProbability E (fun k z => olsVariance (E k) z) 0 := by
    have hz := inProbability_mul E _ _ _ _ (inProbability_deterministic E _ _ hi) hOLS
    simp only [zero_mul] at hz
    apply inProbability_congr_eventually E _ _ _ _ hz
    filter_upwards [h.arm_sizes] with k hk
    intro z hz
    have hN : ((E k).size : ℝ) ≠ 0 := by
      exact_mod_cast (by dsimp [Population.size]; omega : (E k).size ≠ 0)
    field_simp
  have hc : Tendsto (fun k => 1/(1-1/((E k).size : ℝ))) atTop (nhds 1) := by
    have hh : Tendsto (fun k => 1/(1-1/((E k).size : ℝ)))
        atTop (nhds ((1:ℝ)/(1-0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.sub hi)
        (by norm_num : (1:ℝ)-0 ≠ 0)
    simpa only [sub_zero, div_one] using hh
  have hsq := inProbability_sq E _ _ (hLLN E p v1 v0 vt τ h).2.2
  have hlim := inProbability_add E _ _ _ _ hOLS
    (inProbability_mul E _ _ _ _ (inProbability_deterministic E _ _ hc)
      (inProbability_sub E _ _ _ _ hsq hOLSzero))
  simp only [sub_zero, one_mul] at hlim
  apply inProbability_congr_eventually E _ _ _ _ hlim
  filter_upwards [h.arm_sizes] with k hk
  intro z hz
  have hN : ((E k).size : ℝ) ≠ 0 := by
    exact_mod_cast (by dsimp [Population.size]; omega : (E k).size ≠ 0)
  have hN1 : ((E k).size : ℝ)-1 ≠ 0 := by
    have hh : (4:ℝ) ≤ (E k).size := by
      exact_mod_cast (show 4 ≤ (E k).size by dsimp [Population.size]; omega)
    linarith
  have he := (fisher_ols_exact (E k) hk.1 hk.2 z hz).2
  have he' := (eq_div_iff hN1).mp he
  field_simp
  nlinarith [he']

/-- Full Section 2 expansion, conditional on the explicit SRS moment LLN. -/
theorem fisher_ols_asymptotics_of_momentLLN (hLLN : FinitePopulationMomentLLN)
    (E : ℕ → Population) (p v1 v0 vt τ : ℝ) (h : Regularity E p v1 v0 vt τ) :
    LittleOInvSize E (fun k z => fisherVariance (E k) z -
      (populationVariance (E k) (E k).Y1/(E k).n0 +
       populationVariance (E k) (E k).Y0/(E k).n1 + (averageEffect (E k))^2/(E k).size)) ∧
    LittleOInvSize E (fun k z => olsVariance (E k) z -
      (populationVariance (E k) (E k).Y1/(E k).n0 +
       populationVariance (E k) (E k).Y0/(E k).n1)) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*
      (fisherVariance (E k) z-olsVariance (E k) z)-(averageEffect (E k))^2) 0 ∧
    InProbability E (fun k z => ((E k).size : ℝ)*fisherVariance (E k) z)
      (olsLimit p v1 v0+τ^2) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*olsVariance (E k) z) (olsLimit p v1 v0) := by
  have hF := fisher_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h
  have hO := ols_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h
  have hOracle := regularity_oracle_ols_limit E p v1 v0 vt τ h
  have hTau := h.average_effect.pow 2
  have hdet := inProbability_deterministic E _ _ hOracle
  have ht := inProbability_deterministic E _ _ hTau
  refine ⟨?_,?_,?_,hF,hO⟩
  · have hh := inProbability_sub E _ _ _ _ hF (inProbability_add E _ _ _ _ hdet ht)
    simp only [sub_self] at hh
    apply inProbability_congr_eventually E _ _ _ _ hh
    filter_upwards [h.arm_sizes] with k hk
    intro z hz
    have hN : ((E k).size : ℝ) ≠ 0 := by
      exact_mod_cast (by dsimp [Population.size]; omega : (E k).size ≠ 0)
    field_simp <;> ring
  · have hh := inProbability_sub E _ _ _ _ hO hdet
    simp only [sub_self] at hh
    apply inProbability_congr_eventually E _ _ _ _ hh
    filter_upwards [] with k
    intro z hz
    ring

  · have hh := inProbability_sub E _ _ _ _ (inProbability_sub E _ _ _ _ hF hO) ht
    have he : (olsLimit p v1 v0+τ^2-olsLimit p v1 v0)-τ^2 = 0 := by ring
    rw [he] at hh
    apply inProbability_congr_eventually E _ _ _ _ hh
    filter_upwards [] with k
    intro z hz
    ring

theorem local_alternative_equivalence_of_momentLLN (hLLN : FinitePopulationMomentLLN)
    (E : ℕ → Population) (p v1 v0 vt τ : ℝ) (h : Regularity E p v1 v0 vt τ)
    (hl : Tendsto (fun k => averageEffect (E k)) atTop (nhds 0)) :
    LittleOInvSize E (fun k z => fisherVariance (E k) z-olsVariance (E k) z) ∧
    (0 < olsLimit p v1 v0 →
      InProbability E (fun k z => fisherVariance (E k) z/olsVariance (E k) z) 1) := by
  have ht : τ = 0 := tendsto_nhds_unique h.average_effect hl
  have hF := fisher_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h
  simp only [ht, zero_pow (by norm_num : (2:ℕ) ≠ 0), add_zero] at hF
  have hO := ols_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h
  constructor
  · have hh := inProbability_sub E _ _ _ _ hF hO
    simp only [sub_self] at hh
    apply inProbability_congr_eventually E _ _ _ _ hh
    filter_upwards [] with k
    intro z hz
    ring
  · intro hv
    have hh := inProbability_div E _ _ _ _ hF hO (ne_of_gt hv)
    rw [div_self (ne_of_gt hv)] at hh
    apply inProbability_congr_eventually E _ _ _ _ hh
    filter_upwards [h.arm_sizes] with k hk
    intro z hz
    have hN : ((E k).size : ℝ) ≠ 0 := by
      exact_mod_cast (by dsimp [Population.size]; omega : (E k).size ≠ 0)
    exact mul_div_mul_left _ _ hN

theorem constant_effect_asymptotics_of_momentLLN (hLLN : FinitePopulationMomentLLN)
    (E : ℕ → Population) (p v1 v0 vt τ : ℝ) (h : Regularity E p v1 v0 vt τ)
    (hc : ∀ k, ConstantEffects (E k)) :
    LittleOInvSize E (fun k z => olsVariance (E k) z-
      randomizationVariance (E k) (estimate (E k))) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*
      (fisherVariance (E k) z-randomizationVariance (E k) (estimate (E k))) -
      (averageEffect (E k))^2) 0 := by
  obtain ⟨hf,hv,ht,hV,he⟩ := constant_effect_deterministic_limits E p v1 v0 vt τ h hc
  rw [he] at hV
  have hdet := inProbability_deterministic E _ _ hV
  have hO := ols_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h
  have hF := fisher_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h
  constructor
  · have hh := inProbability_sub E _ _ _ _ hO hdet
    simp only [sub_self] at hh
    apply inProbability_congr_eventually E _ _ _ _ hh
    filter_upwards [] with k
    intro z hz
    ring
  · have hh := inProbability_sub E _ _ _ _ (inProbability_sub E _ _ _ _ hF hdet)
      (inProbability_deterministic E _ _ (h.average_effect.pow 2))
    have hh0 : (olsLimit p v1 v0+τ^2-olsLimit p v1 v0)-τ^2 = 0 := by ring
    rw [hh0] at hh
    apply inProbability_congr_eventually E _ _ _ _ hh
    filter_upwards [] with k
    intro z hz
    ring

theorem wald_comparison_asymptotics_of_momentLLN (hLLN : FinitePopulationMomentLLN)
    (E : ℕ → Population) (p v1 v0 vt τ : ℝ) (h : Regularity E p v1 v0 vt τ) :
    LittleOInvSize E (fun k z => neymanVariance (E k) z -
      (populationVariance (E k) (E k).Y1/(E k).n1 +
       populationVariance (E k) (E k).Y0/(E k).n0)) ∧
    LittleOInvSize E (fun k z => olsVariance (E k) z-neymanVariance (E k) z -
      ((populationVariance (E k) (E k).Y1/(E k).n0 +
        populationVariance (E k) (E k).Y0/(E k).n1) -
       (populationVariance (E k) (E k).Y1/(E k).n1 +
        populationVariance (E k) (E k).Y0/(E k).n0))) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*olsVariance (E k) z) (olsLimit p v1 v0) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*neymanVariance (E k) z) (neymanLimit p v1 v0) ∧
    olsLimit p v1 v0-neymanLimit p v1 v0 = ((v1-v0)*(2*p-1))/(p*(1-p)) ∧
    (olsLimit p v1 v0 ≠ neymanLimit p v1 v0 → v1 ≠ v0 ∧ p ≠ 1/2) := by
  have hO := ols_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h
  have hN := neyman_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h
  have hDO := inProbability_deterministic E _ _ (regularity_oracle_ols_limit E p v1 v0 vt τ h)
  have hDN := inProbability_deterministic E _ _ (regularity_oracle_neyman_limit E p v1 v0 vt τ h)
  refine ⟨?_,?_,hO,hN,wald_limit_identity p v1 v0 h.p_positive h.p_less_one,
    unequal_wald_limits_necessary p v1 v0⟩
  · have hh := inProbability_sub E _ _ _ _ hN hDN
    simp only [sub_self] at hh
    apply inProbability_congr_eventually E _ _ _ _ hh
    filter_upwards [] with k
    intro z hz
    ring
  · have hh := inProbability_sub E _ _ _ _ (inProbability_sub E _ _ _ _ hO hN)
      (inProbability_sub E _ _ _ _ hDO hDN)
    simp only [sub_self] at hh
    apply inProbability_congr_eventually E _ _ _ _ hh
    filter_upwards [] with k
    intro z hz
    ring

theorem fisher_neyman_local_comparison_of_momentLLN (hLLN : FinitePopulationMomentLLN)
    (E : ℕ → Population) (p v1 v0 vt τ : ℝ) (h : Regularity E p v1 v0 vt τ)
    (hl : Tendsto (fun k => averageEffect (E k)) atTop (nhds 0)) :
    LittleOInvSize E (fun k z => fisherVariance (E k) z-neymanVariance (E k) z -
      ((populationVariance (E k) (E k).Y1/(E k).n0 +
        populationVariance (E k) (E k).Y0/(E k).n1) -
       (populationVariance (E k) (E k).Y1/(E k).n1 +
        populationVariance (E k) (E k).Y0/(E k).n0))) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*fisherVariance (E k) z) (olsLimit p v1 v0) ∧
    InProbability E (fun k z => ((E k).size : ℝ)*neymanVariance (E k) z) (neymanLimit p v1 v0) := by
  have ht : τ = 0 := tendsto_nhds_unique h.average_effect hl
  have hF := fisher_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h
  simp only [ht, zero_pow (by norm_num : (2:ℕ) ≠ 0), add_zero] at hF
  have hN := neyman_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h
  have hDO := inProbability_deterministic E _ _ (regularity_oracle_ols_limit E p v1 v0 vt τ h)
  have hDN := inProbability_deterministic E _ _ (regularity_oracle_neyman_limit E p v1 v0 vt τ h)
  refine ⟨?_,hF,hN⟩
  have hh := inProbability_sub E _ _ _ _ (inProbability_sub E _ _ _ _ hF hN)
    (inProbability_sub E _ _ _ _ hDO hDN)
  simp only [sub_self] at hh
  apply inProbability_congr_eventually E _ _ _ _ hh
  filter_upwards [] with k
  intro z hz
  ring

theorem constant_effect_limit_agreement_of_momentLLN (hLLN : FinitePopulationMomentLLN)
    (E : ℕ → Population) (p v1 v0 vt τ : ℝ) (h : Regularity E p v1 v0 vt τ)
    (hc : ∀ k, ConstantEffects (E k)) :
    (∀ k, populationVariance (E k) (E k).Y1 = populationVariance (E k) (E k).Y0 ∧
      populationVariance (E k) (unitEffects (E k)) = 0) ∧
    v1=v0 ∧ vt=0 ∧
    Tendsto (fun k => ((E k).size : ℝ)*randomizationVariance (E k) (estimate (E k)))
      atTop (nhds (neymanLimit p v1 v0)) ∧
    neymanLimit p v1 v0 = olsLimit p v1 v0 ∧
    LittleOInvSize E (fun k z => olsVariance (E k) z-neymanVariance (E k) z) := by
  obtain ⟨hf,hv,ht,hV,he⟩ := constant_effect_deterministic_limits E p v1 v0 vt τ h hc
  refine ⟨hf,hv,ht,hV,he,?_⟩
  have hO := ols_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h
  have hN := neyman_variance_limit_of_momentLLN hLLN E p v1 v0 vt τ h
  rw [he] at hN
  have hh := inProbability_sub E _ _ _ _ hO hN
  simp only [sub_self] at hh
  apply inProbability_congr_eventually E _ _ _ _ hh
  filter_upwards [] with k
  intro z hz
  ring

/-- The concrete variance counterexample: the sample
variance limits are supplied by the imported, proved SRS theorem and exact law
bridges, not an assumed asymptotic estimator limit. -/
theorem anticonservative_limit_exists_completed :
    Regularity heterogeneousWitness (1/5) 4 1 1 0 ∧
    (∀ k, averageEffect (heterogeneousWitness k) = 0) ∧
    Tendsto (fun k => ((heterogeneousWitness k).size : ℝ)*
      randomizationVariance (heterogeneousWitness k) (estimate (heterogeneousWitness k)))
        atTop (nhds (81/4)) ∧
    InProbability heterogeneousWitness (fun k z =>
      ((heterogeneousWitness k).size : ℝ)*olsVariance (heterogeneousWitness k) z) 10 ∧
    olsLimit (1/5) 4 1 = 10 ∧ neymanLimit (1/5) 4 1 = 85/4 ∧ (10 : ℝ) < 81/4 := by
  refine ⟨witness_regular,fun k => (heterogeneous_witness_finite k).1,
    witness_actual_scaled_limit.1,?_,?_,?_,?_⟩
  · have hh := ols_variance_limit_of_arm_consistency
      heterogeneousWitness (1/5) 4 1 1 0 witness_regular
      CausalBridge.witness_arm_variance_limits.1 CausalBridge.witness_arm_variance_limits.2
    norm_num [olsLimit] at hh
    simpa only [Population.size, Nat.cast_add] using hh
  · norm_num [olsLimit]
  · norm_num [neymanLimit]
  · norm_num

end
end AronowAudit.P053

