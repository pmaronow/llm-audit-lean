import AronowAudit.P002.Wave1.Theorem2.Reassignment

/-! P002-T5: exact corrected Theorem 2, regression-adjusted uniform coverage. -/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

local instance T2C_normalNullSingleton : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
  ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

lemma T2C_C_cutoffs (α x : ℝ) (hα : 0 < α ∧ α < 1)
    (hx0 : 0 < x) (hx : x < 1-α) :
    ∃ c a b : ℝ, 0 < c ∧ c < a ∧ a < b ∧ x < SH_absNormalCDF c ∧
      SH_absNormalCDF b < 1-α := by
  obtain ⟨c,hc⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (ProbabilityTheory.gaussianReal 0 1) (p := (1+(2*x+(1-α))/3)/2)
    (by linarith) (by linarith)
  obtain ⟨b,hb⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (ProbabilityTheory.gaussianReal 0 1) (p := (1+(x+2*(1-α))/3)/2)
    (by linarith) (by linarith)
  have hc0 : 0 < c := by
    apply AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.lt_iff_lt.mp
    rw [AronowAudit.P053.NormalCompletion.normal_cdf_zero,hc]
    linarith
  have hcb : c < b := by
    apply AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.lt_iff_lt.mp
    rw [hc,hb]
    linarith
  refine ⟨c,(c+b)/2,b,hc0,by linarith,by linarith,?_,?_⟩
  · dsimp [SH_absNormalCDF]
    rw [hc]
    linarith
  · dsimp [SH_absNormalCDF]
    rw [hb]
    linarith

lemma T2C_C_quantile_lower {n} (P : Population n) (hP : ValidDesign P)
    (g : Finset (Fin n) → ℝ≥0∞) (α : ℝ) (hα : 0 < α ∧ α < 1) (a : ℝ≥0∞)
    (ha : probability P (fun S => g S ≤ a) < 1-α) : a < quantile P g α := by
  by_contra hn
  have hq := le_of_not_gt hn
  have hm := T2C_probability_mono P (fun S hS (h : g S ≤ quantile P g α) => h.trans hq)
  have hv := quantile_valid P hP g α hα
  linarith

theorem T2C_positive_coverage (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r α : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hα : 0 < α ∧ α < 1)
    (hP : ∀ j, Xi (P j) δ e A B r) (hH : ∀ j, 0 < T2C_totalH (P j))
    (x : ℝ) (hx0 : 0 < x) (hx : x < 1-α) :
    ∀ᶠ j in atTop, x < adjustedCoverage (P j) (late (P j).pop) α := by
  obtain ⟨c,a,b,hc0,hca,hab,hxc,hb⟩ := T2C_C_cutoffs α x hα hx0 hx
  let c1 : ℝ := (a+c)/2
  let ε : ℝ := (a-c)/2
  let κ : ℝ := (a^2-c1^2)/a^2
  let K := T2C_pooledK k e A (T2C_RK k e A B r)
  have ha0 := hc0.trans hca
  have hc10 : 0 ≤ c1 := by dsimp [c1]; linarith
  have hc1a : c1 < a := by dsimp [c1]; linarith
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hκ : 0 < κ := div_pos (by nlinarith) (sq_pos_of_pos ha0)
  have hK : 0 ≤ K := by dsimp [K, T2C_pooledK, T2C_RK]; positivity
  have hfixed := T2C_fixed_cdf_uniform k e A r K a b (1-α) hk he hA hr hK ha0 hab hb
  have hfixedseq := hsizes.tendsto_atTop.eventually hfixed
  let V := fun j => designVariance (P j).pop (oracleTau (P j) (late (P j).pop))
  let C := fun j => T2C_oracleConservative (P j)
  let O := fun j S => oracleTau (P j) (late (P j).pop) S
  let X := fun j S => adjustedTau (P j) (observedW (P j).pop (late (P j).pop) S) S
  let s := fun j S => adjustedSigma2 (P j) (observedW (P j).pop (late (P j).pop) S) S
  let R := fun j S => |O j S/Real.sqrt (V j)| ≤ c
  let E := fun j S => ε ≤ |(X j S-O j S)/Real.sqrt (V j)|
  let G := fun j S => κ ≤ |s j S/C j-1|
  let F := fun j S => ¬ (0 < T2C_pooledH (P j).x (observedW (P j).pop (late (P j).pop) S) ∧
    mean (fun i => T2C_pooledResidual (P j).x (observedW (P j).pop (late (P j).pop) S) i^4) ≤
      K*(T2C_pooledH (P j).x (observedW (P j).pop (late (P j).pop) S))^2)
  have hR := T2C_oracle_abs_cdf sizes hsizes k P δ e A B r hk hδ he hA hB hr hP hH c hc0.le
  have hE := T2C_observed_numerator_oracle_limit sizes hsizes k P δ e A B r hk hδ he hA hB
    hr hP hH ε hε
  have hG := T2C_observed_sigma_limit sizes hsizes k P δ e A B r he hr.1 hP hH κ hκ
  have hF := T2C_observed_pooled_limit sizes hsizes k P δ e A B r he hr.1 hP hH
  have hlim : Tendsto (fun j => probability (P j).pop (R j)-probability (P j).pop (E j)-
      probability (P j).pop (G j)-probability (P j).pop (F j))
      atTop (nhds (SH_absNormalCDF c)) := by simpa only [sub_zero] using ((hR.sub hE).sub hG).sub hF
  filter_upwards [hfixedseq, (tendsto_order.1 hlim).1 x hxc] with j hj hxj
  apply hxj.trans_le
  have hV : 0 < V j := T2C_oracle_variance_pos (P j) δ e A B r hk hδ he hA hB hr (hP j) (hH j)
  have hVC : V j ≤ C j := T2C_oracle_variance_upper (P j) δ e A B r he (hP j)
  have hC : 0 < C j := hV.trans_le hVC
  have hU : probability (P j).pop (fun S => adjustedAccepted (P j) (late (P j).pop) α S ∨
        (E j S ∨ (G j S ∨ F j S))) ≤
      adjustedCoverage (P j) (late (P j).pop) α+
        (probability (P j).pop (E j)+
          (probability (P j).pop (G j)+probability (P j).pop (F j))) :=
    (T2C_probability_union _ _ _).trans (add_le_add le_rfl
      ((T2C_probability_union _ _ _).trans (add_le_add le_rfl (T2C_probability_union _ _ _))))
  have hinc : probability (P j).pop (R j) ≤ probability (P j).pop (fun S =>
      adjustedAccepted (P j) (late (P j).pop) α S ∨ (E j S ∨ (G j S ∨ F j S))) := by
    apply T2C_probability_mono
    intro S hS hR
    by_cases hE : E j S
    · exact Or.inr (Or.inl hE)
    by_cases hG : G j S
    · exact Or.inr (Or.inr (Or.inl hG))
    by_cases hF : F j S
    · exact Or.inr (Or.inr (Or.inr hF))
    have hpool := not_not.mp hF
    have hcdf := hj (P j) (observedW (P j).pop (late (P j).pop) S) (hP j).1
      (hP j).2.2.2.1 (hP j).2.2.2.2.1 (T2C_Xi_covariates (P j) δ e A B r (hP j))
      hpool.1 hpool.2
    have hq := T2C_C_quantile_lower (P j).pop (hP j).1 _ α hα (ENNReal.ofReal a) hcdf
    have hstd : |X j S/Real.sqrt (V j)| ≤ c1 := by
      have heq : X j S/Real.sqrt (V j) = O j S/Real.sqrt (V j)+
          (X j S-O j S)/Real.sqrt (V j) := by ring
      rw [heq]
      have htri := abs_add_le (O j S/Real.sqrt (V j)) ((X j S-O j S)/Real.sqrt (V j))
      have hsmall : |(X j S-O j S)/Real.sqrt (V j)| < ε := lt_of_not_ge hE
      change |O j S/Real.sqrt (V j)| ≤ c at hR
      dsimp [c1, ε] at *
      linarith
    have hstat := T2C_U_student_lower (X j S) (s j S) (V j) (C j) a c1
      (T2C_sigma_nonneg _ _ _) hV hC hVC ha0 hc10 hc1a hstd (lt_of_not_ge hG)
    exact Or.inl (hstat.trans hq.le)
  have hbound := hinc.trans hU
  change probability (P j).pop (R j)-probability (P j).pop (E j)-
    probability (P j).pop (G j)-probability (P j).pop (F j) ≤
      adjustedCoverage (P j) (late (P j).pop) α
  linarith

lemma T2C_probability_complement {n} (P : Population n) (hP : ValidDesign P)
    (E : Finset (Fin n) → Prop) : probability P E+probability P (fun S => ¬ E S) = 1 := by
  simp only [DecisionLemma12_probability_eq_expectation, ← DecisionLemma12_expectation_add]
  calc
    _ = expectation P (fun _ => (1 : ℝ)) :=
      DecisionLemma12_expectation_congr P (fun S hS => by
        by_cases h : E S <;> simp [h])
    _ = 1 := expectation_const P hP 1

theorem T2C_zero_coverage_seq (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r α : ℝ)
    (he : 0 < e) (hr : 0 < r) (hP : ∀ j, Xi (P j) δ e A B r)
    (hH : ∀ j, T2C_totalH (P j) = 0) (x : ℝ) (hx : x < 1) :
    ∀ᶠ j in atTop, x < adjustedCoverage (P j) (late (P j).pop) α := by
  have hGram := T2C_gram_bad_limit sizes hsizes k P e A r he hr
    (fun j => (hP j).1) (fun j => (hP j).2.2.2.1) (fun j => (hP j).2.2.2.2.1)
    (fun j => T2C_Xi_covariates (P j) δ e A B r (hP j))
  have hlim : Tendsto (fun j => 1-probability (P j).pop
      (fun S => ¬ T2C_gramGood (P j).x e S)) atTop (nhds 1) := by
    simpa only [sub_zero] using
      (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) from tendsto_const_nhds).sub hGram
  filter_upwards [(tendsto_order.1 hlim).1 x hx] with j hj
  have hcomp := T2C_probability_complement (P j).pop (hP j).1 (T2C_gramGood (P j).x e)
  have hcov : probability (P j).pop (T2C_gramGood (P j).x e) ≤
      adjustedCoverage (P j) (late (P j).pop) α :=
    T2C_probability_mono _ (fun S hS hG =>
      T2C_zero_residual_accepted (P j) δ e A B r α he (hP j) (hH j) S hS hG)
  linarith

theorem T2C_uniform_coverage (k : ℕ) (δ e A B r α : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hα : 0 < α ∧ α < 1)
    (x : ℝ) (hx0 : 0 < x) (hx : x < 1-α) :
    ∀ᶠ n in atTop, ∀ P : CovPopulation n k, Xi P δ e A B r →
      x ≤ adjustedCoverage P (late P.pop) α := by
  have hp := T2C_U_uniform_eventual
    (fun n (P : CovPopulation n k) => Xi P δ e A B r ∧ 0 < T2C_totalH P)
    (fun n P => x < adjustedCoverage P (late P.pop) α) (by
      intro sizes hsizes P hP
      exact T2C_positive_coverage sizes hsizes k P δ e A B r α hk hδ he hA hB hr hα
        (fun j => (hP j).1) (fun j => (hP j).2) x hx0 hx)
  have hz := T2C_U_uniform_eventual
    (fun n (P : CovPopulation n k) => Xi P δ e A B r ∧ T2C_totalH P = 0)
    (fun n P => x < adjustedCoverage P (late P.pop) α) (by
      intro sizes hsizes P hP
      exact T2C_zero_coverage_seq sizes hsizes k P δ e A B r α he hr.1
        (fun j => (hP j).1) (fun j => (hP j).2) x (by linarith [hα.1]))
  filter_upwards [hp,hz] with n hp hz P hP
  by_cases hH : 0 < T2C_totalH P
  · exact (hp P ⟨hP,hH⟩).le
  · have hnonneg : 0 ≤ T2C_totalH P :=
      add_nonneg (T2C_residualH_nonneg P true) (T2C_residualH_nonneg P false)
    have hzero : T2C_totalH P = 0 := le_antisymm (le_of_not_gt hH) hnonneg
    exact (hz P ⟨hP,hzero⟩).le

theorem corrected_theorem2_proof (k : ℕ) (δ e A B r α : ℝ) (hk : 0 < k) (hδ : δ < 1)
    (he : 0 < e) (hA : 0 < A) (hB : 0 < B) (hr : 0 < r ∧ r ≤ 1/2)
    (hα : 0 < α ∧ α < 1) :
    ENNReal.ofReal (1-α) ≤ Filter.liminf (fun n => infCoverageXi n k δ e A B r α)
      (atTop ⊓ Filter.principal {n | ∃ P : CovPopulation n k, Xi P δ e A B r}) := by
  apply (le_liminf_iff).mpr
  intro y hy
  have hyn : y ≠ ⊤ := ne_top_of_lt hy
  have hyr : y.toReal < 1-α := (ENNReal.lt_ofReal_iff_toReal_lt hyn).mp hy
  obtain ⟨x,hyx,hx⟩ := exists_between hyr
  have hx0 : 0 < x := ENNReal.toReal_nonneg.trans_lt hyx
  have hu := T2C_uniform_coverage k δ e A B r α hk hδ he hA hB hr hα x hx0 hx
  apply eventually_inf_principal.mpr
  filter_upwards [hu] with n hn hne
  have hbound : ENNReal.ofReal x ≤ infCoverageXi n k δ e A B r α := by
    unfold infCoverageXi
    apply le_iInf
    intro β
    apply le_iInf
    intro P
    apply ENNReal.ofReal_le_ofReal
    simpa only [P.property.2] using hn P.val P.property.1
  exact ((ENNReal.lt_ofReal_iff_toReal_lt hyn).mpr hyx).trans_le hbound

end
end AronowAudit.P002.Wave1
