import SAP.P001a.WH.W3.Endpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Matrix

noncomputable section

universe u

namespace SAP.P001a.WH.W3

open AronowAudit.P001.Wave1.SieveRate
open AronowAudit.P001.Wave1.TailBSieveEscape

/-- Finite-dimensional ridge limits select a least-squares solution, for every design,
including ties, rank deficiency, and `n = 0`. Diagonalize the symmetric positive
semidefinite Gram matrix. The right-hand side is orthogonal to its kernel, so each
positive-eigenvalue coordinate converges after division by `lambda + 1/(r+1)`, and each
zero-eigenvalue coordinate is zero. The limit solves the normal equations; expand the
residual square to prove minimality. Use the finite-dimensional spectral theorem, or
split coefficient space into the kernel and its orthogonal complement. The positive
regularization makes every displayed inverse genuine. Measurability of the resulting
selection is proved below from `measurable_ridge` and pointwise convergence. -/
def T5_L1 : Prop :=
  ∀ n d : ℕ, ∀ z : SieveDataW3 n, ∃ b : Fin (d + 1) → ℝ,
    Tendsto (fun r : ℕ => ridgeCoefficient n d r z) atTop (nhds b) ∧
    ∀ c : Fin (d + 1) → ℝ,
      (∑ i : Fin n, (z.2 i - (coefficientPolynomialW3 b).eval (z.1 i)) ^ 2) ≤
        ∑ i : Fin n, (z.2 i - (coefficientPolynomialW3 c).eval (z.1 i)) ^ 2

/-- Shifted Legendre polynomials are orthogonal to every polynomial of lower degree on
`[0,1]`. Transfer Mathlib's Rodrigues identity to real polynomials. Repeated integration
by parts moves `k` derivatives onto the lower-degree polynomial; the boundary terms
vanish because `x^k(1-x)^k` has zeros of order `k` at both endpoints. The `WithBot` degree
condition includes the zero polynomial when `k = 0`. All integrals are over a compact
interval and have continuous polynomial integrands. -/
def T5_L2 : Prop :=
  ∀ k : ℕ, ∀ p : Polynomial ℝ, p.degree < (k : WithBot ℕ) →
    (∫ x in Set.Icc (0 : ℝ) 1, p.eval x * (shiftedLegendreReal k).eval x) = 0

/-- A polynomial with uniform squared norm at most `1/n` has empirical squared norm at
most two with probability at least one half, simultaneously with distinct design
points. Each of the `n` terms has the stated finite expectation by the coordinate
measure-preserving maps; Markov at two gives the half-probability bound. Independent
atomless uniform coordinates are pairwise distinct almost surely; intersect with that
event. The diagonal-null argument in `SieveRate.n16_proof` is a concrete template.
The guard `0 < n` ensures the displayed reciprocal is an actual sample-size reciprocal. -/
def T5_L3 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ q : Polynomial ℝ,
    (∫ x in Set.Icc (0 : ℝ) 1, (q.eval x) ^ 2) ≤ 1 / (n : ℝ) →
    1 / 2 ≤ prob (unifVec n) (goodDesign n q)

theorem borel_selection (h1 : T5_L1) {Ω : Type*} (X Y : ℕ → Ω → ℝ) (J : ℕ → ℕ) :
    ∃ fit : ℕ → Ω → Polynomial ℝ, BorelSieveLSW3 X Y J fit := by
  classical
  choose b hb using fun n : ℕ => h1 n (J n)
  have hbm (n : ℕ) : Measurable (b n) :=
    measurable_of_tendsto_metrizable (fun r => measurable_ridge n (J n) r)
      (tendsto_pi_nhds.2 fun z => (hb n z).1)
  let fit : ℕ → Ω → Polynomial ℝ := fun n ω => coefficientPolynomialW3
    (b n ((fun i : Fin n => X i ω), (fun i : Fin n => Y i ω)))
  refine ⟨fit, ⟨?_, fun n => ⟨b n, hbm n, fun _ => rfl⟩⟩⟩
  intro n ω
  refine ⟨coefficient_degree _, ?_⟩
  intro p hp
  have hmin := (hb n ((fun i : Fin n => X i ω), (fun i : Fin n => Y i ω))).2
    (fun k : Fin (J n + 1) => p.coeff (k : ℕ))
  rw [← polynomial_of_coefficients p hp] at hmin
  change (∑ i : Fin n, (Y i ω - (fit n ω).eval (X i ω)) ^ 2) ≤
    ∑ i : Fin n, (Y i ω - p.eval (X i ω)) ^ 2 at hmin
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (Y i ω - (fit n ω).eval (X i ω)) ^ 2) n,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => (Y i ω - p.eval (X i ω)) ^ 2) n] at hmin
  exact hmin

/-- The Borel coefficient condition makes the local-risk statistic and its tail events
measurable. No integrability in the sample variable is needed for this parameter integral. -/
theorem measurable_localRisk {Ω : Type*} [MeasurableSpace Ω]
    (X Y : ℕ → Ω → ℝ) (J : ℕ → ℕ) (fit : ℕ → Ω → Polynomial ℝ)
    (hfit : BorelSieveLSW3 X Y J fit) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (δ : ℝ) (n : ℕ) :
    Measurable (localRiskW3 fit δ n) := by
  obtain ⟨b, hb, heq⟩ := hfit.2 n
  have hdata : Measurable (fun ω =>
      ((fun i : Fin n => X i ω), (fun i : Fin n => Y i ω))) :=
    (Measurable.of_eval (fun i : Fin n => hX i)).prodMk
      (Measurable.of_eval (fun i : Fin n => hY i))
  have h := (tb02_meas_region δ (J n)).comp (hb.comp hdata)
  have he : localRiskW3 fit δ n = (fun ω => tb02Region δ
      (coeffPoly (b ((fun i : Fin n => X i ω), (fun i : Fin n => Y i ω))))
      (coeffPoly (b ((fun i : Fin n => X i ω), (fun i : Fin n => Y i ω))))) := by
    funext ω
    simp only [localRiskW3, heq ω, tb02Region, pow_two]
    rfl
  rw [he]
  exact h

theorem legendre_norm (h2 : T5_L2) (k : ℕ) :
    (∫ x in Set.Icc (0 : ℝ) 1, ((shiftedLegendreReal k).eval x) ^ 2) =
      1 / (2 * (k : ℝ) + 1) := by
  rw [orthogonal_endpoint_norm (shiftedLegendreReal k) k (legendre_degree k) (h2 k),
    legendre_at_one]
  have hsign : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
  rw [hsign]

theorem legendre_inner (h2 : T5_L2) (j k : ℕ) :
    (∫ x in Set.Icc (0 : ℝ) 1,
      (shiftedLegendreReal j).eval x * (shiftedLegendreReal k).eval x) =
      if j = k then 1 / (2 * (k : ℝ) + 1) else 0 := by
  by_cases heq : j = k
  · subst j
    simpa [pow_two] using legendre_norm h2 k
  · rw [if_neg heq]
    rcases lt_or_gt_of_ne heq with hlt | hlt
    · apply h2 k (shiftedLegendreReal j)
      have hd := (shiftedLegendreReal j).degree_le_natDegree
      rw [legendre_degree] at hd
      exact hd.trans_lt (by exact_mod_cast hlt)
    · have h := h2 j (shiftedLegendreReal k) (by
        have hd := (shiftedLegendreReal k).degree_le_natDegree
        rw [legendre_degree] at hd
        exact hd.trans_lt (by exact_mod_cast hlt))
      simpa only [mul_comm] using h

theorem odd_sum (m : ℕ) : (∑ k : Fin m, (2 * (k : ℝ) + 1)) = (m : ℝ) ^ 2 := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [hm]
    push_cast
    ring

theorem kernel_properties (h2 : T5_L2) (d : ℕ) :
    (endpointKernel d).natDegree ≤ d ∧ (endpointKernel d).eval 1 = 1 ∧
      (∫ x in Set.Icc (0 : ℝ) 1, ((endpointKernel d).eval x) ^ 2) =
        1 / ((d : ℝ) + 1) ^ 2 := by
  classical
  let a : Fin (d + 1) → ℝ := fun k => (2 * (k : ℝ) + 1) * (-1 : ℝ) ^ (k : ℕ)
  let L : Fin (d + 1) → ℝ → ℝ := fun k x => (shiftedLegendreReal (k : ℕ)).eval x
  let u : ℝ := 1 / ((d : ℝ) + 1) ^ 2
  have hsign (k : Fin (d + 1)) : (-1 : ℝ) ^ (k : ℕ) * (-1 : ℝ) ^ (k : ℕ) = 1 := by
    rw [← mul_pow]
    norm_num
  have ha (k : Fin (d + 1)) : a k * a k / (2 * (k : ℝ) + 1) = 2 * (k : ℝ) + 1 := by
    have hden : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
    dsimp [a]
    field_simp
    nlinarith [hsign k]
  have heval (x : ℝ) : (endpointKernel d).eval x = u * ∑ k : Fin (d + 1), a k * L k x := by
    simp only [endpointKernel, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_finsetSum]
    dsimp [u, a, L]
    push_cast
    rfl
  have hnorm : (∫ x in Set.Icc (0 : ℝ) 1,
      (∑ k : Fin (d + 1), a k * L k x) * ∑ k : Fin (d + 1), a k * L k x) =
      ((d : ℝ) + 1) ^ 2 := by
    simp_rw [Finset.sum_mul_sum]
    have hInt (j k : Fin (d + 1)) :
        Integrable (fun x : ℝ => (a j * L j x) * (a k * L k x))
          (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      ((continuous_const.mul (shiftedLegendreReal (j : ℕ)).continuous).mul
        (continuous_const.mul (shiftedLegendreReal (k : ℕ)).continuous)).integrableOn_Icc
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hInt j k))]
    have hinter (j k : Fin (d + 1)) :
        (∫ x in Set.Icc (0 : ℝ) 1, (a j * L j x) * (a k * L k x)) =
          a j * a k * (if j = k then 1 / (2 * (k : ℝ) + 1) else 0) := by
      have he : (fun x => (a j * L j x) * (a k * L k x)) =
          (fun x => (a j * a k) * (L j x * L k x)) := by funext x; ring
      rw [he, integral_const_mul]
      have horth := legendre_inner h2 (j : ℕ) (k : ℕ)
      simpa only [L, Fin.val_inj] using congrArg (fun z : ℝ => a j * a k * z) horth
    calc
      _ = ∑ j : Fin (d + 1), ∑ k : Fin (d + 1),
          a j * a k * (if j = k then 1 / (2 * (k : ℝ) + 1) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [integral_finsetSum _ (fun k _ => hInt j k)]
        exact Finset.sum_congr rfl fun k _ => hinter j k
      _ = ∑ j : Fin (d + 1), (2 * (j : ℝ) + 1) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [mul_ite, mul_zero, mul_one_div]
        simpa using ha j
      _ = ((d : ℝ) + 1) ^ 2 := by simpa using odd_sum (d + 1)
  refine ⟨?_, ?_, ?_⟩
  · unfold endpointKernel
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((legendre_degree (k : ℕ)).le.trans (Nat.le_of_lt_succ k.isLt))
  · rw [heval]
    have hs : (∑ k : Fin (d + 1), a k * L k 1) = ((d : ℝ) + 1) ^ 2 := by
      calc
        _ = ∑ k : Fin (d + 1), (2 * (k : ℝ) + 1) := by
          apply Finset.sum_congr rfl
          intro k _
          dsimp [a, L]
          rw [legendre_at_one, mul_assoc, hsign k, mul_one]
        _ = _ := by simpa using odd_sum (d + 1)
    rw [hs]
    dsimp [u]
    exact div_mul_cancel₀ 1 (by positivity)
  · have hsquare (x : ℝ) : ((endpointKernel d).eval x) ^ 2 =
        (u * u) * ((∑ k : Fin (d + 1), a k * L k x) *
          ∑ k : Fin (d + 1), a k * L k x) := by rw [heval]; ring
    simp_rw [hsquare]
    rw [integral_const_mul, hnorm]
    dsimp [u]
    field_simp

theorem not_local_consistent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (fit : ℕ → Ω → Polynomial ℝ) (δ : ℝ)
    (hlower : ∀ ε : ℝ, 0 < ε →
      1 / 2 ≤ Filter.liminf (fun t : ℕ =>
        prob μ {ω | ε < localRiskW3 fit δ (t ^ 4) ω}) atTop) :
    ¬ CP μ (localRiskW3 fit δ) 0 := by
  intro hCP
  have hsub (t : ℕ) : {ω | (1 : ℝ) < localRiskW3 fit δ (t ^ 4) ω} ⊆
      {ω | (1 : ℝ) ≤ dist (localRiskW3 fit δ (t ^ 4) ω) 0} := by
    intro ω hω
    change (1 : ℝ) ≤ dist (localRiskW3 fit δ (t ^ 4) ω) 0
    rw [Real.dist_eq, sub_zero]
    exact hω.le.trans (le_abs_self _)
  have hT := (hCP 1 one_pos).comp (tendsto_pow_atTop (n := 4) (by norm_num))
  have hstrict : Tendsto (fun t : ℕ =>
      prob μ {ω | (1 : ℝ) < localRiskW3 fit δ (t ^ 4) ω}) atTop (nhds 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg)
      (fun t => ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hsub t))) hT
  have hbad := hlower 1 one_pos
  rw [hstrict.liminf_eq] at hbad
  norm_num at hbad

theorem endpoint_failure (h2 : T5_L2) (h3 : T5_L3)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : ℕ → Ω → ℝ) (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
    (hlaw : μ.map (fun ω => (X 0 ω, Y 0 ω)) =
      (uniformLaw 0 1).prod (gaussianReal 0 1))
    (fit : ℕ → Ω → Polynomial ℝ) (hfit : BorelSieveLSW3 X Y endpointDegreeW3 fit)
    (t : ℕ) (ht : 2 ≤ t) :
    1 / 4 ≤ prob μ {ω | 1 / 4 < |(fit (t ^ 2) ω).eval 1|} := by
  have hcols : t + 1 ≤ t ^ 2 := by nlinarith
  have htp : 0 < t := by omega
  have htn : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htp
  obtain ⟨hq, hq1, hnorm⟩ := kernel_properties h2 t
  have hsmall : (∫ x in Set.Icc (0 : ℝ) 1, ((endpointKernel t).eval x) ^ 2) ≤
      1 / ((t ^ 2 : ℕ) : ℝ) := by
    rw [hnorm, Nat.cast_pow]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  exact sample_endpoint_tail μ X Y hiid hlaw endpointDegreeW3 fit hfit.1 (t ^ 2) t
    (Nat.sqrt_eq' t) hcols (endpointKernel t) hq hq1
    (h3 (t ^ 2) (pow_pos htp 2) (endpointKernel t) hsmall)

/-- The endpoint bound for an arbitrary finite iid experiment, without any coupling
between different sample sizes. -/
theorem finite_endpoint_failure (h2 : T5_L2) (h3 : T5_L3) : FiniteEndpointBoundW3.{u} := by
  intro t ht Ω _ μ _ Z hZ hlaw b _ hmin
  have hcols : t + 1 ≤ t ^ 2 := by nlinarith
  have htp : 0 < t := by omega
  have htn : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htp
  obtain ⟨hq, hq1, hnorm⟩ := kernel_properties h2 t
  have hsmall : (∫ x in Set.Icc (0 : ℝ) 1, ((endpointKernel t).eval x) ^ 2) ≤
      1 / ((t ^ 2 : ℕ) : ℝ) := by
    rw [hnorm, Nat.cast_pow]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  exact finite_endpoint_tail μ (t ^ 2) t Z hZ hlaw
    (fun ω => coefficientPolynomialW3 (b (Z ω))) (fun _ => coefficient_degree _)
    hmin hcols (endpointKernel t) hq hq1
    (h3 (t ^ 2) (pow_pos htp 2) (endpointKernel t) hsmall)

/-- The three leaves complete the corrected claim. The local-L2 lower limit and degree
rates are the certified donor; existence, the model facts, failure of convergence,
kernel construction, Gaussian endpoint calculation, and Fubini transfer are assembled
explicitly here and in the supporting files. -/
theorem T5_assembly (h1 : T5_L1) (h2 : T5_L2) (h3 : T5_L3) :
    T5WholeStatement_W3.{u} := by
  have hrate : Tendsto (fun n : ℕ =>
      (mainDegreeW3 (n + 1) : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [Function.comp_def, mainDegreeW3, sieveJ, Nat.cast_add, Nat.cast_one] using
      n3_proof.2.1.comp (tendsto_add_atTop_nat 1)
  constructor
  · refine ⟨n3_proof.1, hrate, fun t => Nat.sqrt_eq' t, ?_⟩
    intro Ω _ μ _ X Y hiid hlaw
    refine ⟨model_facts μ X Y hiid hlaw, borel_selection h1 X Y mainDegreeW3,
      ?_, borel_selection h1 X Y endpointDegreeW3, ?_⟩
    · intro fit hfit δ hδ hδ1
      have hc := AronowAudit.P001.Wave1.TailB_sieve_degree_counterexample
        μ X Y hiid hlaw fit hfit.1
      have hlower : ∀ ε : ℝ, 0 < ε →
          1 / 2 ≤ Filter.liminf (fun t : ℕ =>
            prob μ {ω | ε < localRiskW3 fit δ (t ^ 4) ω}) atTop :=
        fun ε hε => hc.2.2 δ hδ hδ1 ε hε
      exact ⟨hlower, not_local_consistent μ fit δ hlower⟩
    · intro fit hfit t ht
      exact endpoint_failure h2 h3 μ X Y hiid hlaw fit hfit t ht
  · exact finite_endpoint_failure h2 h3

end SAP.P001a.WH.W3
