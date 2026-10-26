import AronowAudit.P002.Wave1.Theorem2.OracleCLT

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

lemma T2C_sigma_nonneg {n k} (P : CovPopulation n k) (q : Fin n → ℝ) (S : Finset (Fin n)) :
    0 ≤ adjustedSigma2 P q S := by
  apply add_nonneg
  all_goals exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _)

lemma T2C_oracle_variance_upper {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) :
    designVariance P.pop (oracleTau P (late P.pop)) ≤ T2C_oracleConservative P := by
  have hx := T2C_Xi_covariates P δ e A B r hP
  have hg := T2C_population_det P.x e A (by have := hP.1.1; omega) he hx
  have h := (oracle_variances_proof P hP.1 (late P.pop) 0 hx.1 hg).1
  rw [h]
  exact sub_le_self _ (div_nonneg (T2C_U_popVar_nonneg hP.1.1 _) (Nat.cast_nonneg _))

lemma T2C_kurtosis_norm {n} (hn : 2 ≤ n) (q : Fin n → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hq0 : mean q = 0) (hq4 : mean (fun i => q i^4) ≤ K*(mean (fun i => q i^2))^2) :
    fourthNorm q ≤ (K+1)*Real.sqrt (popVar q) := by
  have hH := T2C_mean_nonneg (fun i => q i^2) (fun i => sq_nonneg _)
  have h4 := T2C_mean_nonneg (fun i => q i^4) (fun i => by positivity)
  have hV := T2C_U_popVar_nonneg hn q
  have hHV := T2C_second_le_popVar hn q hq0
  have hHV2 := pow_le_pow_left₀ hH hHV 2
  have hcoef : K ≤ (K+1)^4 := by
    nlinarith [sq_nonneg K, (by positivity : 0 ≤ K^3), (by positivity : 0 ≤ K^4)]
  have hpow : mean (fun i => q i^4) ≤ (K+1)^4*(popVar q)^2 := by
    apply hq4.trans
    exact (mul_le_mul_of_nonneg_left hHV2 hK).trans
      (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
  have hroot : (fourthNorm q)^4 = mean (fun i => q i^4) := by
    unfold fourthNorm
    calc
      _ = ((Real.sqrt (Real.sqrt (mean (fun i => q i^4))))^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt h4]
  apply (pow_le_pow_iff_left₀ (show 0 ≤ fourthNorm q from Real.sqrt_nonneg _)
    (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (by decide : 4 ≠ 0)).mp
  rw [hroot, mul_pow, show (Real.sqrt (popVar q))^4 = ((Real.sqrt (popVar q))^2)^2 by ring,
    Real.sq_sqrt hV]
  exact hpow

def T2C_fixedPopulation {n k} (P : CovPopulation n k) (q : Fin n → ℝ) : CovPopulation n k where
  pop := T2C_responsePopulation P.pop (fun _ => q)
  x := P.x

lemma T2C_fixed_late {n k} (P : CovPopulation n k) (q : Fin n → ℝ) :
    late (T2C_fixedPopulation P q).pop = 0 := T2C_response_late _ _ rfl

lemma T2C_fixed_observed {n k} (P : CovPopulation n k) (q : Fin n → ℝ) (S : Finset (Fin n)) :
    observedW (T2C_fixedPopulation P q).pop (late (T2C_fixedPopulation P q).pop) S = q := by
  rw [T2C_fixed_late]
  funext i
  by_cases hi : i ∈ S
  · rw [observedW_treated _ _ _ _ hi]
    exact congrFun (T2C_response_w _ (fun _ => q) true) i
  · rw [observedW_control _ _ _ _ (Finset.mem_compl.mpr hi)]
    exact congrFun (T2C_response_w _ (fun _ => q) false) i

lemma T2C_fixed_residual {n k} (P : CovPopulation n k) (q : Fin n → ℝ) (a : Bool) :
    residual (T2C_fixedPopulation P q) a (late (T2C_fixedPopulation P q).pop) =
      T2C_pooledResidual P.x q := by
  have hw : w (T2C_fixedPopulation P q).pop a 0 = q := T2C_response_w _ _ a
  unfold residual psi
  rw [T2C_fixed_late, hw]
  rfl

lemma T2C_fixed_Xi {n k} (P : CovPopulation n k) (q : Fin n → ℝ) (e A r K : ℝ)
    (he : 0 < e) (hK : 0 ≤ K) (hP : ValidDesign P.pop)
    (hl : r*n ≤ (P.pop.n1 : ℝ)) (hu : (P.pop.n1 : ℝ) ≤ (1-r)*n)
    (hx : T2C_covariates P.x e A)
    (hq4 : mean (fun i => T2C_pooledResidual P.x q i^4) ≤ K*(T2C_pooledH P.x q)^2) :
    Xi (T2C_fixedPopulation P q) 0 e A (K+1) r := by
  have hn : 0 < n := by have := hP.1; omega
  have hg := T2C_population_det P.x e A hn he hx
  have hres0 : mean (T2C_pooledResidual P.x q) = 0 :=
    T2C_residual_centered P.x _ (T2C_population_score_zero P.x q hg)
  have hcomp : compliers (T2C_fixedPopulation P q).pop = Finset.univ := T2C_response_compliers _ _
  refine ⟨hP, ?_, ?_, hl, hu, ?_, ?_, hx.1, hx.2.1, hx.2.2⟩
  · intro i hi
    change (false : Bool) = true at hi
    contradiction
  · rw [hcomp]
    exact Finset.univ_nonempty_iff.mpr ⟨⟨0,hn⟩⟩
  · simp only [T2C_fixed_residual, neg_zero, zero_mul]
    have hself : popCov (T2C_pooledResidual P.x q) (T2C_pooledResidual P.x q) =
        popVar (T2C_pooledResidual P.x q) := by simp only [popCov, popVar, pow_two]
    rw [hself]
    exact T2C_U_popVar_nonneg hP.1 _
  · intro a
    rw [T2C_fixed_residual]
    exact T2C_kurtosis_norm hP.1 _ K hK hres0 hq4

lemma T2C_fixed_totalH {n k} (P : CovPopulation n k) (q : Fin n → ℝ) :
    T2C_totalH (T2C_fixedPopulation P q) = 2*T2C_pooledH P.x q := by
  unfold T2C_totalH T2C_residualH
  simp only [T2C_fixed_residual]
  dsimp only [T2C_pooledH]
  ring

lemma T2C_fixed_variance {n k} (P : CovPopulation n k) (q : Fin n → ℝ) (e A : ℝ)
    (he : 0 < e) (hP : ValidDesign P.pop) (hx : T2C_covariates P.x e A) :
    designVariance (T2C_fixedPopulation P q).pop
        (oracleTau (T2C_fixedPopulation P q) (late (T2C_fixedPopulation P q).pop)) =
      T2C_oracleConservative (T2C_fixedPopulation P q) := by
  have hg := T2C_population_det P.x e A (by have := hP.1; omega) he hx
  have h := (oracle_variances_proof (T2C_fixedPopulation P q) hP
    (late (T2C_fixedPopulation P q).pop) q hx.1 hg).1
  have hz : popVar (fun i => residual (T2C_fixedPopulation P q) true
      (late (T2C_fixedPopulation P q).pop) i-
        residual (T2C_fixedPopulation P q) false (late (T2C_fixedPopulation P q).pop) i) = 0 := by
    simp only [T2C_fixed_residual, sub_self, popVar, mean, Finset.sum_const_zero,
      zero_div, sub_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [hz, zero_div, sub_zero] at h
  exact h

lemma T2C_oracle_variance_pos {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hP : Xi P δ e A B r) (hH : 0 < T2C_totalH P) :
    0 < designVariance P.pop (oracleTau P (late P.pop)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hP.1.1; omega : 0 < n)
  exact (div_pos (mul_pos (mul_pos (sub_pos.mpr (max_lt hδ zero_lt_one)) hr.1) hH) hn).trans_le
    (T2C_observed_variance_lower P δ e A B r hk hδ he hA hB hr hP)

/-- The upper CDF comparison is sufficient for the lower bound on the cutoff. -/
theorem T2C_fixed_cdf_seq (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (q : ∀ j, Fin (sizes j) → ℝ)
    (e A r K a b p : ℝ) (hk : 0 < k) (he : 0 < e) (hA : 0 < A)
    (hr : 0 < r ∧ r ≤ 1/2) (hK : 0 ≤ K) (ha : 0 < a) (hab : a < b)
    (hp : SH_absNormalCDF b < p) (hP : ∀ j, ValidDesign (P j).pop)
    (hl : ∀ j, r*sizes j ≤ ((P j).pop.n1 : ℝ))
    (hu : ∀ j, ((P j).pop.n1 : ℝ) ≤ (1-r)*sizes j)
    (hx : ∀ j, T2C_covariates (P j).x e A)
    (hH : ∀ j, 0 < T2C_pooledH (P j).x (q j))
    (hfour : ∀ j, mean (fun i => T2C_pooledResidual (P j).x (q j) i^4) ≤
      K*(T2C_pooledH (P j).x (q j))^2) :
    ∀ᶠ j in atTop, probability (P j).pop (fun S => adjustedAR (P j) (q j) S ≤ ENNReal.ofReal a) < p := by
  let Q := fun j => T2C_fixedPopulation (P j) (q j)
  have hXi (j) : Xi (Q j) 0 e A (K+1) r :=
    T2C_fixed_Xi (P j) (q j) e A r K he hK (hP j) (hl j) (hu j) (hx j) (hfour j)
  have htotal (j) : 0 < T2C_totalH (Q j) := by
    rw [T2C_fixed_totalH]
    exact mul_pos (by norm_num) (hH j)
  let b0 : ℝ := (a+b)/2
  let ε : ℝ := (b-a)/2
  let κ : ℝ := (b0^2-a^2)/a^2
  have hab0 : a < b0 := by dsimp [b0]; linarith
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hκ : 0 < κ := div_pos (by nlinarith) (sq_pos_of_pos ha)
  let V := fun j => designVariance (Q j).pop (oracleTau (Q j) (late (Q j).pop))
  let X := fun j S => adjustedTau (Q j) (observedW (Q j).pop (late (Q j).pop) S) S
  let O := fun j S => oracleTau (Q j) (late (Q j).pop) S
  let s := fun j S => adjustedSigma2 (Q j) (observedW (Q j).pop (late (Q j).pop) S) S
  let E := fun j S => ε ≤ |(X j S-O j S)/Real.sqrt (V j)|
  let F := fun j S => κ ≤ |s j S/T2C_oracleConservative (Q j)-1|
  let R := fun j S => |O j S/Real.sqrt (V j)| ≤ b
  have hB : 0 < K+1 := by linarith
  have hN := T2C_observed_numerator_oracle_limit sizes hsizes k Q 0 e A (K+1) r hk
    (by norm_num) he hA hB hr hXi htotal ε hε
  have hS := T2C_observed_sigma_limit sizes hsizes k Q 0 e A (K+1) r he hr.1 hXi htotal κ hκ
  have hR := T2C_oracle_abs_cdf sizes hsizes k Q 0 e A (K+1) r hk (by norm_num)
    he hA hB hr hXi htotal b (ha.trans hab).le
  have hlim : Tendsto (fun j => probability (Q j).pop (R j)+
      probability (Q j).pop (E j)+probability (Q j).pop (F j))
      atTop (nhds (SH_absNormalCDF b)) := by simpa using (hR.add hN).add hS
  have hresult : ∀ᶠ j in atTop, probability (Q j).pop (fun S =>
      adjustedAR (Q j) (observedW (Q j).pop (late (Q j).pop) S) S ≤ ENNReal.ofReal a) < p := by
    filter_upwards [(tendsto_order.1 hlim).2 p hp] with j hj
    apply lt_of_le_of_lt _ hj
    have hV : 0 < V j := T2C_oracle_variance_pos (Q j) 0 e A (K+1) r hk (by norm_num)
      he hA hB hr (hXi j) (htotal j)
    calc
      _ ≤ probability (Q j).pop (fun S => R j S ∨ (E j S ∨ F j S)) := by
        apply T2C_probability_mono
        intro S hmem hstat
        by_cases hE : E j S
        · exact Or.inr (Or.inl hE)
        by_cases hF : F j S
        · exact Or.inr (Or.inr hF)
        apply Or.inl
        have hratio : |s j S/V j-1| < κ := by
          rw [show V j = T2C_oracleConservative (Q j) from
            T2C_fixed_variance (P j) (q j) e A he (hP j) (hx j)]
          exact lt_of_not_ge hF
        have hstd := T2C_U_student_upper (X j S) (s j S) (V j) a b0
          (T2C_sigma_nonneg _ _ _) hV ha hab0 hstat hratio
        have heq : O j S/Real.sqrt (V j) = X j S/Real.sqrt (V j)-
            (X j S-O j S)/Real.sqrt (V j) := by ring
        change |O j S/Real.sqrt (V j)| ≤ b
        rw [heq]
        have htri := abs_sub (X j S/Real.sqrt (V j)) ((X j S-O j S)/Real.sqrt (V j))
        have hsmall : |(X j S-O j S)/Real.sqrt (V j)| < ε := lt_of_not_ge hE
        dsimp [b0, ε] at hstd hsmall
        linarith
      _ ≤ probability (Q j).pop (R j)+(probability (Q j).pop (E j)+probability (Q j).pop (F j)) :=
        (T2C_probability_union _ _ _).trans (add_le_add le_rfl (T2C_probability_union _ _ _))
      _ = _ := by ring
  have hobs (j) (S : Finset (Fin (sizes j))) :
      observedW (Q j).pop (late (Q j).pop) S = q j := T2C_fixed_observed _ _ _
  simp_rw [hobs] at hresult
  exact hresult

theorem T2C_fixed_cdf_uniform (k : ℕ) (e A r K a b p : ℝ) (hk : 0 < k)
    (he : 0 < e) (hA : 0 < A) (hr : 0 < r ∧ r ≤ 1/2) (hK : 0 ≤ K)
    (ha : 0 < a) (hab : a < b) (hp : SH_absNormalCDF b < p) :
    ∀ᶠ n in atTop, ∀ (P : CovPopulation n k) (q : Fin n → ℝ), ValidDesign P.pop →
      r*n ≤ (P.pop.n1 : ℝ) → (P.pop.n1 : ℝ) ≤ (1-r)*n → T2C_covariates P.x e A →
      0 < T2C_pooledH P.x q →
      mean (fun i => T2C_pooledResidual P.x q i^4) ≤ K*(T2C_pooledH P.x q)^2 →
      probability P.pop (fun S => adjustedAR P q S ≤ ENNReal.ofReal a) < p := by
  have hu := T2C_U_uniform_eventual
    (X := fun n => CovPopulation n k × (Fin n → ℝ))
    (fun n z => ValidDesign z.1.pop ∧ r*n ≤ (z.1.pop.n1 : ℝ) ∧
      (z.1.pop.n1 : ℝ) ≤ (1-r)*n ∧ T2C_covariates z.1.x e A ∧
      0 < T2C_pooledH z.1.x z.2 ∧
      mean (fun i => T2C_pooledResidual z.1.x z.2 i^4) ≤ K*(T2C_pooledH z.1.x z.2)^2)
    (fun n z => probability z.1.pop (fun S => adjustedAR z.1 z.2 S ≤ ENNReal.ofReal a) < p)
    (by
      intro sizes hsizes z hz
      exact T2C_fixed_cdf_seq sizes hsizes k (fun j => (z j).1) (fun j => (z j).2)
        e A r K a b p hk he hA hr hK ha hab hp
        (fun j => (hz j).1) (fun j => (hz j).2.1) (fun j => (hz j).2.2.1)
        (fun j => (hz j).2.2.2.1) (fun j => (hz j).2.2.2.2.1) (fun j => (hz j).2.2.2.2.2))
  filter_upwards [hu] with n hn P q hP hl hu hx hH hfour
  exact hn (P,q) ⟨hP,hl,hu,hx,hH,hfour⟩

end
end AronowAudit.P002.Wave1
