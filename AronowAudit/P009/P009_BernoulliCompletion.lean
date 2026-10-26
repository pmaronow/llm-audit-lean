import AronowAudit.P009.P009_Audit

/-!
Bernoulli finite identities and asymptotic estimator rates under the P009
assumptions. Product-law block factorization supplies full interference
graph covariance cancellation. Finite second moments control the IPW means and
counts; an explicit ratio bound handles the Hájek empty-arm extension.
-/

namespace AronowAudit.P009.BernoulliCompletion
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

/-- Full-cube noninterference makes changing a nonparent immaterial. -/
theorem outcome_update_of_not_interferes {n : ℕ} (E : Experiment n) (i j : Fin n)
    (h : ¬ Interferes E j i) (z : Assignment n) (b : Bool) :
    E.outcome i (Function.update z j b) = E.outcome i z := by
  by_contra hn
  apply h
  exact Or.inr ⟨Function.update z j b, z,
    fun ℓ hℓ => Function.update_of_ne hℓ b z, hn⟩

/-- Each outcome is a function of precisely its full-cube interference parents. -/
theorem outcome_dependsOn {n : ℕ} (E : Experiment n) (i : Fin n) :
    DependsOn (E.outcome i) {j | Interferes E j i} := by
  intro z z' hagree
  have hh (s : Finset (Fin n)) : E.outcome i (s.piecewise z' z) = E.outcome i z := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hjs ih =>
      rw [Finset.piecewise_insert]
      by_cases hj : Interferes E j i
      · have hz : (s.piecewise z' z) j = z' j := by
          simpa only [Finset.piecewise, hjs, ite_false] using (hagree j hj)
        rw [← hz, Function.update_eq_self]
        exact ih
      · rw [outcome_update_of_not_interferes E i j hj]
        exact ih
  simpa using (hh Finset.univ).symm

theorem arm_dependsOn {n : ℕ} (E : Experiment n) (i : Fin n) (b : Bool) (a : ℕ) :
    DependsOn (armVariable E b a i) {j | Interferes E j i} := by
  intro z z' hagree
  have hi : z i = z' i := hagree i (Or.inl rfl)
  simp only [armVariable, hi, outcome_dependsOn E i hagree]

/-- The Bernoulli mass of each coordinate in either coding. -/
def coordinateMass {n : ℕ} (E : Experiment n) (i : Fin n) (a : Bool) : ℝ :=
  if a then marginal E i true else 1-marginal E i true

theorem coordinateMass_total {n : ℕ} (E : Experiment n) (i : Fin n) :
    ∑ a : Bool, coordinateMass E i a = 1 := by simp [coordinateMass, Fintype.sum_bool]

/-- Product-law factorization for arbitrary functions of disjoint coordinate
blocks. It uses every coordinate jointly, not pairwise independence. -/
theorem mean_product_of_dependsOn {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (s : Set (Fin n)) (f g : Assignment n → ℝ)
    (hf : DependsOn f s) (hg : DependsOn g sᶜ) :
    mean E.design (fun z => f z*g z) = mean E.design f * mean E.design g := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun j => j ∈ s) (fun _ => Bool)
  let qf := fun x : s → Bool => f (e.symm (x, fun _ => false))
  let qg := fun y : ({j : Fin n // j ∉ s} → Bool) => g (e.symm (fun _ => false, y))
  have hfac (x : s → Bool) (y : ({j : Fin n // j ∉ s} → Bool)) :
      E.design.mass (e.symm (x,y)) =
        (∏ j : s, coordinateMass E j (x j))*
        (∏ j : {j : Fin n // j ∉ s}, coordinateMass E j (y j)) := by
    rw [hBER.2, ← Fintype.prod_subtype_mul_prod_subtype (fun j => j ∈ s)]
    congr 1
    · apply Finset.prod_congr rfl
      intro j _
      simp [e, coordinateMass, Equiv.piEquivPiSubtypeProd, j.property]
    · apply Finset.prod_congr rfl
      intro j _
      simp [e, coordinateMass, Equiv.piEquivPiSubtypeProd, j.property]
  have hf' (x : s → Bool) (y : ({j : Fin n // j ∉ s} → Bool)) : f (e.symm (x,y)) = qf x := by
    apply hf
    intro j hj
    simp [e, Equiv.piEquivPiSubtypeProd, hj]
  have hg' (x : s → Bool) (y : ({j : Fin n // j ∉ s} → Bool)) : g (e.symm (x,y)) = qg y := by
    apply hg
    intro j hj
    change j ∉ s at hj
    simp [e, Equiv.piEquivPiSubtypeProd, hj]
  have htx : (∑ x : s → Bool, ∏ j : s, coordinateMass E j (x j)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [coordinateMass_total, Finset.prod_const_one]
  have hty : (∑ y : ({j : Fin n // j ∉ s} → Bool), ∏ j : {j : Fin n // j ∉ s}, coordinateMass E j (y j)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [coordinateMass_total, Finset.prod_const_one]
  have hmf : mean E.design f = ∑ x : s → Bool, (∏ j : s, coordinateMass E j (x j))*qf x := by
    unfold mean
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp_rw [hfac, hf', mul_right_comm _ _ (qf _), ← Finset.mul_sum, hty, mul_one]
  have hmg : mean E.design g = ∑ y : ({j : Fin n // j ∉ s} → Bool), (∏ j : {j : Fin n // j ∉ s}, coordinateMass E j (y j))*qg y := by
    unfold mean
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [hfac, hg', mul_assoc, ← Finset.sum_mul, htx, one_mul]
  unfold mean
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  change (∑ x : s → Bool, ∑ y : ({j : Fin n // j ∉ s} → Bool),
    E.design.mass (e.symm (x,y))*(f (e.symm (x,y))*g (e.symm (x,y)))) = _
  simp_rw [hfac, hf', hg']
  rw [show (∑ z, E.design.mass z*f z) = mean E.design f from rfl,
    show (∑ z, E.design.mass z*g z) = mean E.design g from rfl, hmf, hmg,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring


 theorem covariance_product_formula {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (f g : Ω → ℝ) : cov P f g = mean P (fun z => f z*g z)-mean P f*mean P g := by
  unfold cov
  calc
    _ = mean P (fun z => f z*g z-mean P f*g z-mean P g*f z+mean P f*mean P g) := by
      congr 1
      funext z
      ring
    _ = _ := by
      rw [mean_add, mean_sub, mean_sub, mean_const_mul, mean_const_mul, mean_const]
      ring

 theorem covariance_nonedge {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (i j : Fin n) (hij : ¬ Dependent E i j) (b : Bool) (a : ℕ) :
    cov E.design (armVariable E b a i) (armVariable E b a j) = 0 := by
  have hj : DependsOn (armVariable E b a j) {ℓ | Interferes E ℓ i}ᶜ := by
    apply DependsOn.mono _ (arm_dependsOn E j b a)
    intro ℓ hℓ hi
    exact hij ⟨ℓ, hi, hℓ⟩
  rw [covariance_product_formula, mean_product_of_dependsOn E hBER _ _ _
    (arm_dependsOn E i b a) hj, sub_self]

 theorem covariance_graph_cancellation {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (i j : Fin n) (b : Bool) (a : ℕ) :
    (1-d E i j)*cov E.design (armVariable E b a i) (armVariable E b a j) = 0 := by
  by_cases hij : Dependent E i j
  · simp [d, hij]
  · rw [covariance_nonedge E hBER i j hij b a]
    simp

 theorem regular_marginal_bounds {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) (i : Fin n) (b : Bool) :
    k⁻¹ ≤ marginal E i b ∧ marginal E i b ≤ 1-k⁻¹ ∧
      0 < marginal E i b ∧ (marginal E i b)⁻¹ ≤ k := by
  rcases hReg with ⟨hk,hq,hs,hp,hm,hpot⟩
  have h1 : k⁻¹ ≤ marginal E i b ∧ marginal E i b ≤ 1-k⁻¹ := by
    cases b
    · have ht := hp i
      have he := marginal_partition E i
      constructor <;> linarith
    · exact hp i
  have hp0 := (inv_pos.mpr hk).trans_le h1.1
  exact ⟨h1.1,h1.2,hp0,(inv_le_comm₀ hp0 hk).mpr h1.1⟩

 theorem regular_k_ge_two {n : ℕ} (hn : 0 < n) (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) : 2 ≤ k := by
  have hk := hReg.1
  have hh := hReg.2.2.2.1 ⟨0,hn⟩
  have hki : 0 < k⁻¹ := inv_pos.mpr hk
  have he : k*k⁻¹ = 1 := mul_inv_cancel₀ hk.ne'
  nlinarith [mul_le_mul_of_nonneg_left hh.1 hk.le,
    mul_le_mul_of_nonneg_left hh.2 hk.le]

 theorem variance_div {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) (c : ℝ) :
    var P (fun z => X z/c) = var P X/c^2 := by
  rw [variance_second_moment, variance_second_moment]
  simp_rw [div_pow, mean_div]
  ring

 theorem mean_abs_le {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) :
    |mean P X| ≤ mean P (fun z => |X z|) := by
  unfold mean
  calc
    _ ≤ ∑ z, |P.mass z*X z| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (P.nonneg _)]

 theorem mean_abs_of_moment {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ)
    (k r : ℝ) (hk : 0 < k) (hr : 1 ≤ r)
    (hM : mean P (fun z => Real.rpow |X z| r) ≤ Real.rpow k r) :
    mean P (fun z => |X z|) ≤ k := by
  have hr0 : 0 < r := by linarith
  have hnonneg : 0 ≤ mean P (fun z => Real.rpow |X z| r) := by
    apply Finset.sum_nonneg
    intro z _
    exact mul_nonneg (P.nonneg z) (Real.rpow_nonneg (abs_nonneg _) _)
  calc
    _ ≤ Real.rpow (mean P (fun z => Real.rpow |X z| r)) (1/r) := by
      simpa only [pow_one, Nat.cast_one] using finite_moment_interpolation P X 1 (by omega) r (by simpa using hr)
    _ ≤ Real.rpow (Real.rpow k r) (1/r) :=
      Real.rpow_le_rpow hnonneg hM (by positivity)
    _ = k := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul hk.le, mul_one_div_cancel hr0.ne', Real.rpow_one]

 theorem conditional_potential_eq_observed {n : ℕ} (E : Experiment n) (i : Fin n) (b : Bool) :
    cmean E.design (fun z => z i = b) (potential E i b) =
      cmean E.design (fun z => z i = b) (E.outcome i) := by
  unfold cmean
  congr 1
  apply congrArg (mean E.design)
  funext z
  by_cases hz : z i = b
  · have he : Function.update z i b = z := by
      rw [← hz, Function.update_eq_self]
    simp only [hz, ite_true, potential, he]
  · simp [hz]

 theorem mean_muHat_eq_muBreve {n : ℕ} (E : Experiment n) (b : Bool)
    (hp : ∀ i, 0 < marginal E i b) : mean E.design (muHat E b) = muBreve E b := by
  rw [expected_arm_mean E b hp]
  simp only [muBreve, conditional_potential_eq_observed]

 theorem muBreve_bound {n : ℕ} (hn : 0 < n) (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) (hBER : Bernoulli E) (b : Bool) : |muBreve E b| ≤ k^2 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hk2 := regular_k_ge_two hn E k q s hReg
  have hb (i : Fin n) : |mean E.design (potential E i b)| ≤ k :=
    (mean_abs_le E.design _).trans (mean_abs_of_moment E.design _ k s hReg.1 hReg.2.2.1
      (hReg.2.2.2.2.2 i b))
  unfold muBreve
  simp_rw [conditional_potential_eq_observed, conditional_observed_eq_potential_mean E hBER]
  rw [abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑ i, |mean E.design (potential E i b)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, k := Finset.sum_le_sum (fun i _ => hb i)
    _ ≤ k^2*(n:ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hh : k ≤ k^2 := by nlinarith only [hk2, sq_nonneg (k-1)]
      nlinarith only [mul_le_mul_of_nonneg_right hh hnR.le]

 theorem arm_variance_bound {n : ℕ} (hn : 0 < n) (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) (hBER : Bernoulli E) (b : Bool) :
    var E.design (muHat E b) ≤ k^4*dAvg E/(n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hc (i j : Fin n) : |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤ d E i j*k^2 := by
    by_cases hij : Dependent E i j
    · simpa only [d, hij, if_true, one_mul, show 2*1=2 by norm_num] using
        (corrected_moment_covariance E k q hReg.1 hReg.2.1 hReg.2.2.2.2.1
          1 (by simpa using hReg.2.1) i j b).2.2.2.2.2.2
    · simp only [d, hij, if_false, zero_mul, covariance_nonedge E hBER i j hij b 1, abs_zero, le_refl]
  have he : muHat E b = fun z => (∑ i, (marginal E i b)⁻¹*armVariable E b 1 i z)/(n:ℝ) := by
    funext z
    simp only [muHat, armVariable, pow_one, div_eq_mul_inv]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, variance_div]
  have hw := weighted_variance_absolute E.design (armVariable E b 1)
    (fun i => (marginal E i b)⁻¹) k (fun i =>
      ⟨inv_pos.mpr (regular_marginal_bounds E k q s hReg i b).2.2.1,
        (regular_marginal_bounds E k q s hReg i b).2.2.2⟩)
  calc
    _ ≤ (k^2*(∑ i, ∑ j, |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)|))/(n:ℝ)^2 :=
      div_le_div_of_nonneg_right hw.2 (sq_nonneg _)
    _ ≤ (k^2*(∑ i, ∑ j, d E i j*k^2))/(n:ℝ)^2 := by
      gcongr with i j
      exact hc i j
    _ = _ := by
      simp only [dAvg, degree, ← Finset.sum_mul]
      field_simp


 def countVariable {n : ℕ} (E : Experiment n) (b : Bool) (i : Fin n) (z : Assignment n) : ℝ :=
   (if z i = b then 1 else 0)/marginal E i b

 theorem indicator_mean {n : ℕ} (E : Experiment n) (b : Bool) (i : Fin n) :
    mean E.design (fun z => if z i = b then (1:ℝ) else 0) = marginal E i b := by
  unfold marginal prob
  congr 1
  funext z
  by_cases hz : z i = b <;> simp [hz]

 theorem count_mean {n : ℕ} (E : Experiment n) (b : Bool) (i : Fin n)
    (hp : 0 < marginal E i b) : mean E.design (countVariable E b i) = 1 := by
  unfold countVariable
  rw [mean_div, indicator_mean]
  change marginal E i b/marginal E i b = 1
  exact div_self hp.ne'

 theorem count_variance {n : ℕ} (E : Experiment n) (b : Bool) (i : Fin n)
    (hp : 0 < marginal E i b) : var E.design (countVariable E b i) = (1-marginal E i b)/marginal E i b := by
  have he : (fun z => (countVariable E b i z)^2) =
      (fun z => (if z i = b then (1:ℝ) else 0)/(marginal E i b)^2) := by
    funext z
    by_cases hz : z i = b <;> simp [countVariable, hz, div_pow]
  rw [variance_second_moment, count_mean E b i hp, he, mean_div, indicator_mean]
  change marginal E i b/(marginal E i b)^2-1^2 = _
  field_simp

 theorem count_covariance_ne {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (b : Bool) (i j : Fin n) (hij : i ≠ j) :
    cov E.design (countVariable E b i) (countVariable E b j) = 0 := by
  have hi : DependsOn (countVariable E b i) ({i} : Set (Fin n)) := by
    intro z z' hagree
    have hh := hagree i (Set.mem_singleton i)
    simp [countVariable, hh]
  have hj : DependsOn (countVariable E b j) ({i} : Set (Fin n))ᶜ := by
    intro z z' hagree
    have hh := hagree j (by simpa using hij.symm)
    simp [countVariable, hh]
  rw [covariance_product_formula, mean_product_of_dependsOn E hBER _ _ _ hi hj, sub_self]

 theorem count_variance_sum {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (b : Bool) : var E.design (fun z => nHat E b z/n) =
      (∑ i, (1-marginal E i b)/marginal E i b)/(n:ℝ)^2 := by
  have he : nHat E b = fun z => ∑ i, (1:ℝ)*countVariable E b i z := by
    funext z
    simp only [nHat, countVariable, one_mul]
  rw [he, variance_div]
  have hv := (weighted_variance_absolute E.design (countVariable E b)
    (fun _ => (1:ℝ)) 1 (fun _ => ⟨by norm_num, le_rfl⟩)).1
  rw [hv]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simpa only [one_mul, var] using count_variance E b i (marginal_pos E hBER i b)
  · intro j _ hji
    simp only [one_mul, count_covariance_ne E hBER b i j hji.symm]
  · simp

 theorem count_variance_bound {n : ℕ} (hn : 0 < n) (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) (hBER : Bernoulli E) (b : Bool) :
    var E.design (fun z => nHat E b z/n) ≤ k/(n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  rw [count_variance_sum E hBER b]
  have hi (i : Fin n) : (1-marginal E i b)/marginal E i b ≤ k := by
    have hp := regular_marginal_bounds E k q s hReg i b
    rw [sub_div, div_self hp.2.2.1.ne', one_div]
    linarith only [hp.2.2.2]
  calc
    _ ≤ (∑ _i : Fin n, k)/(n:ℝ)^2 :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => hi i)) (sq_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

 theorem variance_sub_le {Ω : Type*} [Fintype Ω] (P : Law Ω) (X Y : Ω → ℝ) :
    var P (fun z => X z-Y z) ≤ 2*(var P X+var P Y) := by
  unfold var cov
  rw [← mean_add, ← mean_const_mul, mean_sub]
  unfold mean
  apply Finset.sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ (P.nonneg z)
  have hh := sq_nonneg ((X z-mean P X)+(Y z-mean P Y))
  dsimp only [mean] at hh
  dsimp only
  nlinarith only [hh]

 theorem ht_mse_bound {n : ℕ} (hn : 0 < n) (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) (hBER : Bernoulli E) :
    mean E.design (fun z => (ht E z-eate E)^2) ≤ 4*k^4*dAvg E/(n:ℝ) := by
  have he : mean E.design (fun z => (ht E z-eate E)^2) = var E.design (ht E) := by
    unfold var cov
    rw [ht_unbiased E hBER]
    congr 1
    funext z
    ring
  rw [he]
  change var E.design (fun z => muHat E true z-muHat E false z) ≤ _
  have hh := variance_sub_le E.design (muHat E true) (muHat E false)
  have h1 := arm_variance_bound hn E k q s hReg hBER true
  have h0 := arm_variance_bound hn E k q s hReg hBER false
  calc
    _ ≤ 2*(var E.design (muHat E true)+var E.design (muHat E false)) := hh
    _ ≤ 2*(k^4*dAvg E/(n:ℝ)+k^4*dAvg E/(n:ℝ)) := by gcongr
    _ = _ := by ring


 theorem centered_square_mean {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) :
    mean P (fun z => (X z-mean P X)^2) = var P X := by
  unfold var cov
  congr 1
  funext z
  ring

 theorem second_moment_tail {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ)
    (u : ℝ) (hu : 0 < u) :
    prob P (fun z => u ≤ |X z|) ≤ mean P (fun z => (X z)^2)/u^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
  unfold prob mean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : u ≤ |X z|
  · simp only [hz, ite_true, mul_one]
    exact mul_le_mul_of_nonneg_left
      (by nlinarith only [(sq_le_sq₀ hu.le (abs_nonneg _)).mpr hz, sq_abs (X z)])
      (P.nonneg z)
  · simp only [hz, ite_false, mul_zero, zero_mul]
    exact mul_nonneg (P.nonneg z) (sq_nonneg _)

 theorem op_of_second_moment (S : Study) (X : (t : ℕ) → Assignment (S.N t) → ℝ)
    (a : ℕ → ℝ) (C : ℝ) (hC : 0 < C) (ha : ∀ t, 0 < a t)
    (hM : ∀ t, mean (S.experiment t).design (fun z => (X t z)^2) ≤ C*(a t)^2) :
    Op S X a := by
  intro ε hε
  let K := Real.sqrt (C/ε)+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hs : C ≤ ε*K^2 := by
    have hr := Real.sq_sqrt (div_nonneg hC.le hε.le)
    have hsr := Real.sqrt_nonneg (C/ε)
    dsimp [K]
    nlinarith [div_mul_cancel₀ C hε.ne']
  refine ⟨K,hK, Eventually.of_forall (fun t => ?_)⟩
  calc
    _ ≤ mean (S.experiment t).design (fun z => (X t z)^2)/(K*a t)^2 :=
      second_moment_tail _ _ _ (mul_pos hK (ha t))
    _ ≤ (C*(a t)^2)/(K*a t)^2 := div_le_div_of_nonneg_right (hM t) (sq_nonneg _)
    _ = C/K^2 := by field_simp [(ha t).ne', hK.ne']
    _ ≤ ε := (div_le_iff₀ (sq_pos_of_pos hK)).mpr hs

 theorem probability_of_op_zero (S : Study) (X : (t : ℕ) → Assignment (S.N t) → ℝ)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds 0)) (hX : Op S X a) :
    InProbability S X := by
  intro ε hε
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨K,hK,hbound⟩ := hX (η/2) (by positivity)
  have hlim : Tendsto (fun t => K*a t) atTop (nhds 0) := by simpa using ha.const_mul K
  filter_upwards [hbound, hlim.eventually_lt_const hε] with t ht hsmall
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (probability_nonnegative _ _)]
  calc
    _ ≤ prob (S.experiment t).design (fun z => K*a t ≤ |X t z|) :=
      finite_probability_mono _ _ _ (fun z hz => (hsmall.trans hz).le)
    _ ≤ η/2 := ht
    _ < η := by linarith

 theorem bernoulli_rate_pos (S : Study) (t : ℕ) : 0 < bernoulliRate S t := by
  have hn : (0:ℝ) < size S t := by dsimp [size]; exact_mod_cast S.positive t
  have hd : (0:ℝ) < dAvg (S.experiment t) :=
    lt_of_lt_of_le (by norm_num) (average_degree_at_least_one _ (S.positive t))
  unfold bernoulliRate
  exact div_pos (Real.sqrt_pos.mpr hd) (Real.sqrt_pos.mpr hn)

 theorem bernoulli_rate_square (S : Study) (t : ℕ) :
    (bernoulliRate S t)^2 = dAvg (S.experiment t)/size S t := by
  have hn : (0:ℝ) ≤ size S t := by dsimp [size]; positivity
  have hd : (0:ℝ) ≤ dAvg (S.experiment t) :=
    le_trans (by norm_num) (average_degree_at_least_one _ (S.positive t))
  rw [bernoulliRate, div_pow, Real.sq_sqrt hd, Real.sq_sqrt hn]

 theorem bernoulli_rate_zero (S : Study) (h : Restricted S) :
    Tendsto (bernoulliRate S) atTop (nhds 0) := by
  have hh := h.sqrt
  have hd (t : ℕ) : (0:ℝ) ≤ dAvg (S.experiment t) :=
    le_trans (by norm_num) (average_degree_at_least_one _ (S.positive t))
  change Tendsto (fun t => Real.sqrt (dAvg (S.experiment t))/Real.sqrt (size S t)) atTop (nhds 0)
  simpa only [Real.sqrt_div (hd _), Real.sqrt_zero] using hh

 theorem muBreve_difference {n : ℕ} (E : Experiment n) (hBER : Bernoulli E) :
    muBreve E true-muBreve E false = eate E := by
  rw [eate_eq_adse E hBER]
  simp only [muBreve, conditional_potential_eq_observed, adse,
    Finset.sum_sub_distrib, sub_div]

 theorem ratio_error_bound (x y m δ B : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/2)
    (hX : |x-m| ≤ δ) (hY : |y-1| ≤ δ) (hm : |m| ≤ B) :
    0 < y ∧ |x/y-m| ≤ 2*(1+B)*δ := by
  have hB : 0 ≤ B := (abs_nonneg m).trans hm
  have hy : (1/2:ℝ) ≤ y := by have hh := (abs_le.mp hY).1; linarith
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  refine ⟨hy0, ?_⟩
  have he : x/y-m = (x-m-m*(y-1))/y := by field_simp; ring
  rw [he, abs_div, abs_of_pos hy0]
  calc
    _ ≤ (|x-m|+|m| * |y-1|)/y := by
      apply div_le_div_of_nonneg_right _ hy0.le
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul] using abs_sub_le (x-m) 0 (m*(y-1))
    _ ≤ (δ+B*δ)/y := by gcongr
    _ ≤ (δ+B*δ)/(1/2) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hy
    _ = _ := by ring


 theorem hajek_error_bound {n : ℕ} (hn : 0 < n) (E : Experiment n) (k δ : ℝ)
    (hBER : Bernoulli E) (z : Assignment n) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/2)
    (hm : ∀ b, |muBreve E b| ≤ k^2)
    (hX : ∀ b, |muHat E b z-muBreve E b| ≤ δ)
    (hY : ∀ b, |nHat E b z/(n:ℝ)-1| ≤ δ) :
    |hajek E z-eate E| ≤ 4*(1+k^2)*δ := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hr (b : Bool) := ratio_error_bound (muHat E b z) (nHat E b z/(n:ℝ))
    (muBreve E b) δ (k^2) hδ hδ1 (hX b) (hY b) (hm b)
  have hnonzero (b : Bool) : nHat E b z ≠ 0 := by
    intro hz
    have hh := (hr b).1
    rw [hz, zero_div] at hh
    exact (lt_irrefl 0 hh)
  have ha : ArmsNonempty E z := ⟨hnonzero true, hnonzero false⟩
  have he (b : Bool) : (n:ℝ)*muHat E b z/nHat E b z = muHat E b z/(nHat E b z/(n:ℝ)) := by
    field_simp [hnR.ne', hnonzero b]
    <;> ring
  rw [hajek, if_pos ha, he true, he false, ← muBreve_difference E hBER]
  calc
    _ = |(muHat E true z/(nHat E true z/(n:ℝ))-muBreve E true)-
      (muHat E false z/(nHat E false z/(n:ℝ))-muBreve E false)| := by congr 1; ring
    _ ≤ |muHat E true z/(nHat E true z/(n:ℝ))-muBreve E true|+
      |muHat E false z/(nHat E false z/(n:ℝ))-muBreve E false| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
          (muHat E true z/(nHat E true z/(n:ℝ))-muBreve E true) 0
          (muHat E false z/(nHat E false z/(n:ℝ))-muBreve E false)
    _ ≤ 2*(1+k^2)*δ+2*(1+k^2)*δ := add_le_add (hr true).2 (hr false).2
    _ = _ := by ring

 theorem component_second_moments (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hBER : ∀ t, Bernoulli (S.experiment t))
    (t : ℕ) (b : Bool) :
    mean (S.experiment t).design (fun z => (muHat (S.experiment t) b z-muBreve (S.experiment t) b)^2) ≤
      (k^4+k)*(bernoulliRate S t)^2 ∧
    mean (S.experiment t).design (fun z => (nHat (S.experiment t) b z/size S t-1)^2) ≤
      (k^4+k)*(bernoulliRate S t)^2 := by
  have hk := (hReg t).1
  have hn : (0:ℝ) < size S t := by dsimp [size]; exact_mod_cast S.positive t
  have hp := fun i => marginal_pos (S.experiment t) (hBER t) i b
  have hm := mean_muHat_eq_muBreve (S.experiment t) b hp
  have hcount : mean (S.experiment t).design (fun z => nHat (S.experiment t) b z/size S t) = 1 := by
    rw [mean_div, expected_arm_count _ _ hp]
    exact div_self hn.ne'
  constructor
  · rw [← hm, centered_square_mean]
    calc
      _ ≤ k^4*dAvg (S.experiment t)/size S t := arm_variance_bound (S.positive t) _ k q s (hReg t) (hBER t) b
      _ ≤ (k^4+k)*(bernoulliRate S t)^2 := by
        rw [bernoulli_rate_square]
        have hd : (0:ℝ) ≤ dAvg (S.experiment t)/size S t :=
          le_trans (by norm_num) ((bernoulli_rate_square S t) ▸ sq_nonneg (bernoulliRate S t))
        calc
          _ ≤ k^4*dAvg (S.experiment t)/size S t+k*(dAvg (S.experiment t)/size S t) :=
            le_add_of_nonneg_right (mul_nonneg hk.le hd)
          _ = _ := by ring
  · rw [← hcount, centered_square_mean]
    calc
      _ ≤ k/size S t := count_variance_bound (S.positive t) _ k q s (hReg t) (hBER t) b
      _ ≤ k*dAvg (S.experiment t)/size S t := by
        apply div_le_div_of_nonneg_right _ hn.le
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (average_degree_at_least_one _ (S.positive t)) hk.le
      _ ≤ (k^4+k)*(bernoulliRate S t)^2 := by
        rw [bernoulli_rate_square]
        have hd : 0 ≤ dAvg (S.experiment t)/size S t :=
          le_trans (by norm_num) ((bernoulli_rate_square S t) ▸ sq_nonneg (bernoulliRate S t))
        calc
          _ ≤ k*dAvg (S.experiment t)/size S t+k^4*(dAvg (S.experiment t)/size S t) :=
            le_add_of_nonneg_right (mul_nonneg (pow_nonneg hk.le 4) hd)
          _ = _ := by ring

 theorem bernoulli_hajek_op (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hBER : ∀ t, Bernoulli (S.experiment t))
    (hRestricted : Restricted S) :
    Op S (fun t z => hajek (S.experiment t) z-eate (S.experiment t)) (bernoulliRate S) := by
  intro ε hε
  let C := k^4+k
  have hk := (hReg 0).1
  have hC : 0 < C := by dsimp [C]; positivity
  let K := Real.sqrt (4*C/ε)+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hs : C ≤ (ε/4)*K^2 := by
    have hr := Real.sq_sqrt (div_nonneg (by positivity : 0 ≤ 4*C) hε.le)
    have hsr := Real.sqrt_nonneg (4*C/ε)
    dsimp [K]
    nlinarith [div_mul_cancel₀ (4*C) hε.ne']
  have hlarge : 0 < 8*(1+k^2)*K := by positivity
  refine ⟨8*(1+k^2)*K, hlarge, ?_⟩
  have hlim : Tendsto (fun t => K*bernoulliRate S t) atTop (nhds 0) := by
    simpa using (bernoulli_rate_zero S hRestricted).const_mul K
  filter_upwards [hlim.eventually_le_const (by norm_num : (0:ℝ) < 1/2)] with t hδ1
  let δ := K*bernoulliRate S t
  have hδ : 0 < δ := mul_pos hK (bernoulli_rate_pos S t)
  let A := fun b z => δ ≤ |muHat (S.experiment t) b z-muBreve (S.experiment t) b|
  let D := fun b z => δ ≤ |nHat (S.experiment t) b z/size S t-1|
  have hp (X : Assignment (S.N t) → ℝ)
      (hM : mean (S.experiment t).design (fun z => (X z)^2) ≤ C*(bernoulliRate S t)^2) :
      prob (S.experiment t).design (fun z => δ ≤ |X z|) ≤ ε/4 := by
    calc
      _ ≤ mean (S.experiment t).design (fun z => (X z)^2)/δ^2 := second_moment_tail _ _ δ hδ
      _ ≤ (C*(bernoulliRate S t)^2)/(K*bernoulliRate S t)^2 :=
        div_le_div_of_nonneg_right hM (sq_nonneg _)
      _ = C/K^2 := by field_simp [(bernoulli_rate_pos S t).ne', hK.ne']
      _ ≤ ε/4 := (div_le_iff₀ (sq_pos_of_pos hK)).mpr hs
  have hA (b : Bool) : prob (S.experiment t).design (A b) ≤ ε/4 :=
    hp _ (component_second_moments S k q s hReg hBER t b).1
  have hD (b : Bool) : prob (S.experiment t).design (D b) ≤ ε/4 :=
    hp _ (component_second_moments S k q s hReg hBER t b).2
  have hi (z : Assignment (S.N t))
      (hz : (8*(1+k^2)*K)*bernoulliRate S t ≤ |hajek (S.experiment t) z-eate (S.experiment t)|) :
      (A true z ∨ A false z) ∨ (D true z ∨ D false z) := by
    by_contra hn
    have hneg : (¬A true z ∧ ¬A false z) ∧ (¬D true z ∧ ¬D false z) := by tauto
    have hX (b : Bool) : |muHat (S.experiment t) b z-muBreve (S.experiment t) b| ≤ δ := by
      cases b
      · exact (lt_of_not_ge hneg.1.2).le
      · exact (lt_of_not_ge hneg.1.1).le
    have hY (b : Bool) : |nHat (S.experiment t) b z/size S t-1| ≤ δ := by
      cases b
      · exact (lt_of_not_ge hneg.2.2).le
      · exact (lt_of_not_ge hneg.2.1).le
    have hb := hajek_error_bound (S.positive t) (S.experiment t) k δ (hBER t) z hδ.le hδ1
      (fun b => muBreve_bound (S.positive t) _ k q s (hReg t) (hBER t) b) hX hY
    have hh := hz.trans hb
    change (8*(1+k^2)*K)*bernoulliRate S t ≤ 4*(1+k^2)*(K*bernoulliRate S t) at hh
    have hprod : 0 < (1+k^2)*(K*bernoulliRate S t) := mul_pos (by positivity) hδ
    nlinarith only [hh, hprod]
  calc
    _ ≤ prob (S.experiment t).design (fun z => A true z ∨ A false z)+
        prob (S.experiment t).design (fun z => D true z ∨ D false z) := probability_union_bound _ _ _ _ hi
    _ ≤ (prob (S.experiment t).design (A true)+prob (S.experiment t).design (A false))+
        (prob (S.experiment t).design (D true)+prob (S.experiment t).design (D false)) :=
      add_le_add (probability_union_bound _ _ _ _ (fun z hz => hz))
        (probability_union_bound _ _ _ _ (fun z hz => hz))
    _ ≤ ε := by linarith only [hA true, hA false, hD true, hD false]


 theorem restricted_of_bounded_degree (S : Study)
    (hBound : BigO (fun t => dAvg (S.experiment t)) (fun _ => 1)) : Restricted S := by
  obtain ⟨C,hC,hbound⟩ := hBound
  have hN : Tendsto (size S) atTop atTop := by
    change Tendsto (fun t => (S.N t : ℝ)) atTop atTop
    exact tendsto_natCast_atTop_iff.mpr S.grows
  have hlim : Tendsto (fun t => C/size S t) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using hN.inv_tendsto_atTop.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall (fun t => div_nonneg
      (le_trans (by norm_num) (average_degree_at_least_one _ (S.positive t))) (by dsimp [size]; positivity))
  · filter_upwards [hbound] with t ht
    apply div_le_div_of_nonneg_right _ (by dsimp [size]; positivity)
    simpa only [abs_one, mul_one] using (le_abs_self (dAvg (S.experiment t))).trans ht

 theorem op_change_rate (S : Study) (X : (t : ℕ) → Assignment (S.N t) → ℝ)
    (a b : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (hRate : ∀ᶠ t in atTop, a t ≤ C*b t) (hX : Op S X a) : Op S X b := by
  intro ε hε
  obtain ⟨K,hK,hbound⟩ := hX ε hε
  refine ⟨K*C,mul_pos hK hC, ?_⟩
  filter_upwards [hRate,hbound] with t ht hb
  calc
    _ ≤ prob (S.experiment t).design (fun z => K*a t ≤ |X t z|) := by
      apply finite_probability_mono
      intro z hz
      have hh : K*a t ≤ (K*C)*b t := by nlinarith only [mul_le_mul_of_nonneg_left ht hK.le]
      exact hh.trans hz
    _ ≤ ε := hb

 theorem bernoulli_rate_root_n (S : Study)
    (hBound : BigO (fun t => dAvg (S.experiment t)) (fun _ => 1)) :
    ∃ C > 0, ∀ᶠ t in atTop, bernoulliRate S t ≤ C*(1/Real.sqrt (size S t)) := by
  obtain ⟨B,hB,hbound⟩ := hBound
  refine ⟨Real.sqrt B,Real.sqrt_pos.mpr hB, ?_⟩
  filter_upwards [hbound] with t ht
  have hd : dAvg (S.experiment t) ≤ B := by
    simpa only [abs_one,mul_one] using (le_abs_self _).trans ht
  unfold bernoulliRate
  simpa only [mul_one_div] using
    div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hd) (Real.sqrt_nonneg (size S t))


 theorem coordinateMass_eq_marginal {n : ℕ} (E : Experiment n) (i : Fin n) (b : Bool) :
    coordinateMass E i b = marginal E i b := by
  cases b
  · dsimp [coordinateMass]
    linarith [marginal_partition E i]
  · rfl

 theorem probability_fixed_coordinates {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (G : Finset (Fin n)) (a : Assignment n) :
    prob E.design (fun z => ∀ i ∈ G, z i = a i) = ∏ i ∈ G, marginal E i (a i) := by
  classical
  let w := fun i b => if i ∈ G then (if b = a i then coordinateMass E i b else 0)
    else coordinateMass E i b
  have he (z : Assignment n) : E.design.mass z*(@ite ℝ (∀ i ∈ G, z i = a i) (Classical.propDecidable _) 1 0) =
      ∏ i, w i (z i) := by
    rw [hBER.2]
    change (∏ i, coordinateMass E i (z i))*
      (@ite ℝ (∀ i ∈ G, z i = a i) (Classical.propDecidable _) 1 0) = _
    by_cases hz : ∀ i ∈ G, z i = a i
    · rw [if_pos hz, mul_one]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ G <;> simp [w, hi, hz i]
    · rw [if_neg hz, mul_zero]
      push Not at hz
      obtain ⟨i,hi,hzi⟩ := hz
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [w, hi, hzi])
  unfold prob mean
  trans ∑ z : Assignment n, ∏ i, w i (z i)
  · apply Finset.sum_congr rfl
    intro z _
    exact he z
  rw [← Fintype.prod_sum]
  have hw (i : Fin n) : (∑ b : Bool, w i b) = if i ∈ G then marginal E i (a i) else 1 := by
    by_cases hi : i ∈ G
    · cases ha : a i <;> simp [w, hi, ha, Fintype.sum_bool, coordinateMass,
        ← coordinateMass_eq_marginal E i false]
    · simp only [w, hi, ite_false, coordinateMass_total]
  simp_rw [hw]
  rw [← Finset.prod_filter]
  simp

end
end AronowAudit.P009.BernoulliCompletion

namespace AronowAudit.P009
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- T41 finite lemmas, Supplement A pp. 3,7–9: arm unbiasedness, estimated
count unbiasedness, zero non-edge covariance, the corrected variance bounds
and the HT MSE bound that drives Proposition 2's limit argument. -/
theorem bernoulli_finite_lemmas {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hReg : Regular E k q s) (hBER : Bernoulli E) :
    eate E = adse E ∧
    (∀ b, mean E.design (muHat E b) = muBreve E b ∧
      mean E.design (nHat E b) = n ∧ |muBreve E b| ≤ k^2 ∧
      var E.design (muHat E b) ≤ k^4*dAvg E/(n:ℝ) ∧
      var E.design (fun z => nHat E b z/n) =
        (∑ i, (1-marginal E i b)/marginal E i b)/(n:ℝ)^2 ∧
      var E.design (fun z => nHat E b z/n) ≤ k/(n:ℝ)) ∧
    (∀ i j b, (1-d E i j)*cov E.design
      (armVariable E b 1 i) (armVariable E b 1 j) = 0) ∧
    mean E.design (fun z => (ht E z-eate E)^2) ≤ 4*k^4*dAvg E/(n:ℝ) := by
  refine ⟨BernoulliCompletion.eate_eq_adse E hBER, ?_, ?_,
    BernoulliCompletion.ht_mse_bound hn E k q s hReg hBER⟩
  · intro b
    exact ⟨BernoulliCompletion.mean_muHat_eq_muBreve E b
        (fun i => BernoulliCompletion.marginal_pos E hBER i b),
      expected_arm_count E b (fun i => BernoulliCompletion.marginal_pos E hBER i b),
      BernoulliCompletion.muBreve_bound hn E k q s hReg hBER b,
      BernoulliCompletion.arm_variance_bound hn E k q s hReg hBER b,
      BernoulliCompletion.count_variance_sum E hBER b,
      BernoulliCompletion.count_variance_bound hn E k q s hReg hBER b⟩
  · intro i j b
    exact BernoulliCompletion.covariance_graph_cancellation E hBER i j b 1


/-- T41, Proposition 2 (p. 684): Bernoulli HT and Hájek consistency and
the exact printed n^-1/2 sqrt(d_AVG) stochastic rates under Assumptions 1–2. -/
theorem bernoulli_consistency (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hBER : ∀ t, Bernoulli (S.experiment t))
    (hRestricted : Restricted S) :
    EstimatorClaims S (fun t => eate (S.experiment t)) (bernoulliRate S) := by
  have hk := (hReg 0).1
  have hHT : Op S (fun t z => ht (S.experiment t) z-eate (S.experiment t)) (bernoulliRate S) := by
    apply BernoulliCompletion.op_of_second_moment S _ _ (4*k^4) (by positivity)
      (BernoulliCompletion.bernoulli_rate_pos S)
    intro t
    rw [BernoulliCompletion.bernoulli_rate_square]
    convert BernoulliCompletion.ht_mse_bound (S.positive t) _ k q s (hReg t) (hBER t) using 1 <;> simp only [size] <;> ring
  have hH := BernoulliCompletion.bernoulli_hajek_op S k q s hReg hBER hRestricted
  have ha := BernoulliCompletion.bernoulli_rate_zero S hRestricted
  exact ⟨BernoulliCompletion.probability_of_op_zero S _ _ ha hHT,
    BernoulliCompletion.probability_of_op_zero S _ _ ha hH, hHT, hH⟩


/-- The bounded-degree Bernoulli branch of the root-n corollary. -/
theorem bernoulli_root_n_consistency (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hBER : ∀ t, Bernoulli (S.experiment t))
    (hBound : BigO (fun t => dAvg (S.experiment t)) (fun _ => 1)) :
    EstimatorClaims S (fun t => eate (S.experiment t))
      (fun t => 1/Real.sqrt (size S t)) := by
  have hh := bernoulli_consistency S k q s hReg hBER
    (BernoulliCompletion.restricted_of_bounded_degree S hBound)
  obtain ⟨C,hC,hRate⟩ := BernoulliCompletion.bernoulli_rate_root_n S hBound
  exact ⟨hh.1,hh.2.1,
    BernoulliCompletion.op_change_rate S _ _ _ C hC hRate hh.2.2.1,
    BernoulliCompletion.op_change_rate S _ _ _ C hC hRate hh.2.2.2⟩


/-- T27, Bernoulli upper and lower bounds on every b-coordinate assignment
atom. The upper bound, rather than the printed lower bound, tends to zero. -/
theorem bernoulli_atom_bounds {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) (hBER : Bernoulli E) (G : Finset (Fin n))
    (a : Assignment n) :
    k⁻¹ ^ G.card ≤ prob E.design (fun z => ∀ i ∈ G, z i = a i) ∧
    prob E.design (fun z => ∀ i ∈ G, z i = a i) ≤ (1-k⁻¹)^G.card := by
  rw [BernoulliCompletion.probability_fixed_coordinates E hBER G a]
  constructor
  · rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun i _ => (inv_pos.mpr hReg.1).le)
      (fun i _ => (BernoulliCompletion.regular_marginal_bounds E k q s hReg i (a i)).1)
  · rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun i _ => (BernoulliCompletion.marginal_pos E hBER i (a i)).le)
      (fun i _ => (BernoulliCompletion.regular_marginal_bounds E k q s hReg i (a i)).2.1)

end
end AronowAudit.P009
