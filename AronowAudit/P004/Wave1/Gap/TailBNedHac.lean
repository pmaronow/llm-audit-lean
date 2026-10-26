import AronowAudit.P004.Wave1.NedHeadline
import AronowAudit.P004.Wave1.NedFarCovariance
import AronowAudit.P004.Wave1.Gap.GP0042B2b

/-! The exact NED HAC correction. The existing headline CLT, finite-conditioning
calculus, and far-row covariance theorem supply the probabilistic inputs. This
module supplies shifted metric shells, supported-pair substitutions, oracle
concentration, covariance smoothing, and liminf Wald coverage. Every kernel
operation is a finite sum, so kernel measurability is unnecessary. -/

universe u

namespace AronowAudit.P004.Wave1

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open NedHeadline DesignLimits
open scoped BigOperators

/-- Shifted tails are summed using containing balls, including the shell just
outside `3b`, where the argument of `ψ` can be arbitrarily close to zero. -/
theorem TailB_Ned_shifted_shell_sum {N : ℕ}
    (D : Fin N → Fin N → ℝ) (i : Fin N) (ψ : ℝ → ℝ) (Cb b A e : ℝ)
    (hCb : 0 < Cb) (hb : 1 ≤ b) (hA : 0 ≤ A) (he : 4 < e)
    (hψ : ∀ t, 0 ≤ t → 0 ≤ ψ t) (hanti : AntitoneOn ψ (Set.Ici 0))
    (henv : ∀ t, 1 ≤ t → ψ t ≤ A * t ^ (-e))
    (hsp : ∀ s, 0 ≤ s → ((ball D i s).card : ℝ) ≤ Cb * (1 + s^2)) :
    (∑ j ∈ Finset.univ.filter (fun j => 3*b < D i j), ψ (D i j/3-b)) ≤
      Cb * b^2 * (37 * ψ 0 + 148 * A / (1 - (2 : ℝ) ^ (2-e))) := by
  classical
  have hb0 : 0 < b := by linarith
  have hq : 0 < 1 - (2 : ℝ) ^ (2-e) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by linarith : 2-e < 0)
    linarith
  let S := Finset.univ.filter (fun j => 3*b < D i j)
  let F := Finset.univ.filter (fun j => 6*b < D i j)
  have hnear : ∑ j ∈ S.filter (fun j => D i j ≤ 6*b), ψ (D i j/3-b) ≤
      37 * Cb * b^2 * ψ 0 := by
    have hsub : S.filter (fun j => D i j ≤ 6*b) ⊆ ball D i (6*b) := by
      intro j hj
      simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and] using
        (Finset.mem_filter.mp hj).2
    have hcard : ((S.filter (fun j => D i j ≤ 6*b)).card : ℝ) ≤ 37*Cb*b^2 := by
      calc
        _ ≤ ((ball D i (6*b)).card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hsub)
        _ ≤ Cb*(1+(6*b)^2) := hsp _ (by positivity)
        _ ≤ 37*Cb*b^2 := by nlinarith [sq_nonneg (b-1)]
    calc
      _ ≤ ∑ _j ∈ S.filter (fun j => D i j ≤ 6*b), ψ 0 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjfar := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
        exact hanti (by simp) (by simp only [Set.mem_Ici]; linarith) (by linarith)
      _ = ((S.filter (fun j => D i j ≤ 6*b)).card : ℝ) * ψ 0 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (hψ 0 le_rfl)
  have hfar : ∑ j ∈ F, ψ (D i j/3-b) ≤
      148*Cb*b^2*A/(1-(2 : ℝ)^(2-e)) := by
    have hh := dy_proof D i Cb (2*b) e A (fun j => ψ (D i j/3-b))
      hCb (by linarith) he hA hsp (by
        intro j hj
        have hd : 6*b < D i j := by linarith
        have ht : 1 ≤ D i j/(6*b) := by
          apply (le_div_iff₀ (by positivity : 0 < 6*b)).mpr
          linarith
        have hshift : D i j/(6*b) ≤ D i j/3-b := by
          apply (div_le_iff₀ (by positivity : 0 < 6*b)).mpr
          have hx : 0 ≤ D i j-6*b := by linarith
          nlinarith [mul_nonneg (by linarith : 0 ≤ b-1) hx]
        refine ⟨hψ _ (by linarith), ?_⟩
        calc
          ψ (D i j/3-b) ≤ ψ (D i j/(6*b)) :=
            hanti (by simp only [Set.mem_Ici]; linarith)
              (by simp only [Set.mem_Ici]; linarith) hshift
          _ ≤ A*(D i j/(6*b))^(-e) := henv _ ht
          _ = A*(D i j/(3*(2*b)))^(-e) := by ring_nf)
    calc
      _ = ∑ j ∈ Finset.univ.filter (fun j => 3*(2*b) < D i j), ψ (D i j/3-b) := by
        congr 1
        ext j
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
        congr 1 <;> ring
      _ ≤ _ := hh.trans_eq (by ring)
  have hsplit : (∑ j ∈ S, ψ (D i j/3-b)) =
      (∑ j ∈ S.filter (fun j => D i j ≤ 6*b), ψ (D i j/3-b)) +
        ∑ j ∈ F, ψ (D i j/3-b) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := S) (p := fun j => D i j ≤ 6*b)]
    congr 1
    congr 1
    ext j
    simp only [S, F, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by linarith, h⟩
  change (∑ j ∈ S, ψ (D i j/3-b)) ≤ _
  rw [hsplit]
  exact (add_le_add hnear hfar).trans_eq (by ring)

/-- A finite supported-pair sum divided by `N` has only the ball-count cost. -/
theorem TailB_Ned_supported_sum_bound {N : ℕ} (hN : 0 < N)
    (D : Fin N → Fin N → ℝ) (b Cb A : ℝ) (hA : 0 ≤ A)
    (hsp : ∀ i, ((ball D i b).card : ℝ) ≤ Cb * (1+b^2))
    (f : Fin N → Fin N → ℝ) (hf : ∀ i j, j ∈ ball D i b → |f i j| ≤ A) :
    |(∑ i, ∑ j ∈ ball D i b, f i j) / (N : ℝ)| ≤ Cb * (1+b^2) * A := by
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_div, abs_of_pos hn, div_le_iff₀ hn]
  calc
    |∑ i, ∑ j ∈ ball D i b, f i j| ≤
        ∑ i, ∑ j ∈ ball D i b, |f i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin N, ((ball D i b).card : ℝ) * A := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ _j ∈ ball D i b, A := Finset.sum_le_sum (hf i)
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _i : Fin N, Cb*(1+b^2)*A :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hsp i) hA
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring


/-- Unnormalized supported quadratic form. -/
def TailB_Ned_form {N : ℕ} (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ)
    (b : ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ ball D i b, x i*x j*K (D i j/b)

theorem TailB_Ned_form_div {N : ℕ} (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ)
    (b c : ℝ) (x : Fin N → ℝ) :
    TailB_Ned_form D K b (fun i => x i/c) = TailB_Ned_form D K b x/c^2 := by
  classical
  simp only [TailB_Ned_form, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem TailB_Ned_rows_form {N : ℕ} (p : ℝ) (R : CircleTable N)
    (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (b μ1 μ0 : ℝ) (z : Assignment N) :
    (∑ i, nedVRow p R D K b μ1 μ0 i z) =
      TailB_Ned_form D K b
        (fun i => residualContrast (fun _ => p) R (fun _ a => if a then μ1 else μ0) i z) /
          (N : ℝ)^2 :=
  TailB_Ned_form_div D K b N _

theorem TailB_Ned_kernel_support {N : ℕ} (D : Fin N → Fin N → ℝ)
    (K : ℝ → ℝ) (b : ℝ) (hb : 0 < b) (hK : ∀ t, 1 < t → K t = 0)
    (f : Fin N → Fin N → ℝ) :
    (∑ i, ∑ j, f i j*K (D i j/b)) =
      ∑ i, ∑ j ∈ ball D i b, f i j*K (D i j/b) := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  simp only [ball, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : D i j ≤ b
  · simp only [hij, if_true]
  · have ht : 1 < D i j/b := (lt_div_iff₀ hb).mpr (by simpa using lt_of_not_ge hij)
    simp only [hij, if_false, hK _ ht, mul_zero]

theorem TailB_Ned_kernel_form {N : ℕ} (R : CircleTable N) (z : Assignment N)
    (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (b : ℝ)
    (hN : 0 < N) (hb : 0 < b) (hK : ∀ t, 1 < t → K t = 0) :
    (N : ℝ)*kernelVariance z (residual R z) (distanceKernel D K b) =
      TailB_Ned_form D K b (fun i => (N : ℝ)*lambda z i*residual R z i)/(N : ℝ) := by
  classical
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold kernelVariance distanceKernel
  rw [TailB_Ned_kernel_support D K b hb hK]
  simp only [TailB_Ned_form, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hn]
  <;> ring

theorem TailB_Ned_arm_second
    {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    {P : PopulationSequence Space} {p d : ℝ} (E : ScoreEnvelope P p d)
    (hp : 0 < p ∧ p < 1) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ᶠ N in atTop, ∀ a,
      expect (fun _ => p) (fun z => (T42_B p (circleAverage (P N) d) a z)^2) ≤ V/N := by
  classical
  let M := 2*E.B*E.L
  let V := |10*E.Cb*M^2+74*E.Cb*M*(E.L*E.G)*E.A/(1-(2 : ℝ)^(2-E.e))|
  refine ⟨V, abs_nonneg _, ?_⟩
  filter_upwards [E.hbound, E.hspacing, eventually_gt_atTop 0] with N hRN hsp hN
  intro a
  let R := circleAverage (P N) d
  let X := armResidual p R a
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (by norm_num) E.hB.le) E.hL.le
  have hμ : |barMu (fun _ => p) R a| ≤ E.B :=
    NedFarCovariance.barMu_abs_le p hp R E.B E.hB.le hRN a
  let α : Fin N → Bool → ℝ := fun _ b => armCoefficient p a b
  let β : Fin N → Bool → ℝ := fun _ b => -armCoefficient p a b*barMu (fun _ => p) R a
  have hX : X = fun i z => α i (z i)*R i z+β i (z i) := by
    rw [show X = armResidual p R a from rfl, armResidual_affine]
    funext i z
    dsimp [α, β]
    ring
  have hLF : LocalFamily p X (nodeSeparation (P N)) E.ψ (E.L*E.G) E.Cb E.A E.e := by
    rw [hX]
    exact E.affine_family hp N hsp α β (fun _ b => E.arm_coefficient hp a b)
  have hXB : ∀ i z, |X i z| ≤ M := by
    intro i z
    have hr : |R i z-barMu (fun _ => p) R a| ≤ 2*E.B :=
      (abs_sub _ _).trans (by linarith [hRN i z])
    have hx : X i z = armCoefficient p a (z i)*(R i z-barMu (fun _ => p) R a) := by
      rw [hX]
      dsimp [α, β]
      ring
    rw [hx, abs_mul]
    exact (mul_le_mul (E.arm_coefficient hp a (z i)) hr (abs_nonneg _) E.hL.le).trans_eq
      (by dsimp [M]; ring)
  have hsum : variance (fun _ => p) (fun z => ∑ i, X i z) ≤ (N : ℝ)*V :=
    (covsum_proof p X _ E.ψ (E.L*E.G) E.Cb E.A E.e M hLF hM hXB).trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) hn.le)
  have hB : T42_B p R a = fun z => (∑ i, X i z)/(N : ℝ) := by
    funext z
    simp only [T42_B, X, armResidual, ← Finset.sum_div]
    ring
  have hm : expect (fun _ => p) (T42_B p R a) = 0 := by
    rw [hB, expect_div, armResidual_sum_mean p R a hN hp, zero_div]
  calc
    _ = variance (fun _ => p) (T42_B p R a) := by
      simp only [variance, cov, hm, zero_mul, sub_zero, pow_two]
      rfl
    _ = variance (fun _ => p) (fun z => ∑ i, X i z)/(N : ℝ)^2 := by
      rw [hB, variance_div]
    _ ≤ ((N : ℝ)*V)/(N : ℝ)^2 := div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = V/N := by field_simp [hn.ne'] <;> ring

/-- The joint arm/count error has a root-`N` second-moment bound. -/
theorem TailB_Ned_errors_moment
    {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    {P : PopulationSequence Space} {p d : ℝ} (E : ScoreEnvelope P p d)
    (hp : 0 < p ∧ p < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N in atTop,
      expect (fun _ => p) (GP0042B2b_errors p (circleAverage (P N) d)) ≤ C/N := by
  obtain ⟨V, hV, hVN⟩ := TailB_Ned_arm_second E hp
  let C := 2*V+(1-p)/p+p/(1-p)
  have hq : 0 < 1-p := sub_pos.mpr hp.2
  have hC : 0 ≤ C := add_nonneg
    (add_nonneg (by positivity) (div_nonneg hq.le hp.1.le)) (div_nonneg hp.1.le hq.le)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hVN, eventually_gt_atTop 0] with N hVN hN
  have h1 := T42_E_moment p hp hN true
  have h0 := T42_E_moment p hp hN false
  simp only [coin, ite_true, Bool.false_eq_true, ite_false, sub_sub_cancel] at h1 h0
  unfold GP0042B2b_errors
  rw [expect_add, expect_add, expect_add, h1, h0]
  calc
    _ ≤ V/N+V/N+(1-p)/p/N+p/(1-p)/N := by linarith [hVN true, hVN false]
    _ = C/N := by dsimp [C]; ring

/-- The bandwidth assumption supplies the sixth-power concentration rate. -/
theorem TailB_Ned_bandwidth_sixth (b : ℕ → ℝ)
    (hrate : Asymptotics.IsLittleO atTop b (fun N => (N : ℝ)^(1/6 : ℝ))) :
    Tendsto (fun N => (b N)^6/(N : ℝ)) atTop (nhds 0) := by
  have h := hrate.tendsto_div_nhds_zero.pow 6
  have he (N : ℕ) : ((N : ℝ)^(1/6 : ℝ))^6 = (N : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    norm_num
  simpa only [div_pow, he, zero_pow (by decide : 6 ≠ 0)] using h

/-- A second-moment error bound remains negligible after the supported-pair
factor `1+b²`. The bad event may include empty treatment arms. -/
theorem TailB_Ned_supported_error_transfer
    (π : ∀ N, Fin N → ℝ) (hπ : AdmissibleSeq π)
    (b : ℕ → ℝ) (hb : ∀ᶠ N in atTop, 1 ≤ b N)
    (hrate : Tendsto (fun N => (b N)^6/(N : ℝ)) atTop (nhds 0))
    (Q U : ∀ N, Assignment N → ℝ) (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hQ : ∀ N z, 0 ≤ Q N z)
    (hmom : ∀ᶠ N in atTop, expect (π N) (Q N) ≤ C/N)
    (hU : ∀ᶠ N in atTop, ∀ z, Q N z ≤ 1/4 →
      |U N z| ≤ A*(1+(b N)^2)*Real.sqrt (Q N z)) : InProb π U := by
  let W : ∀ N, Assignment N → ℝ := fun N z => A*(1+(b N)^2)*Real.sqrt (Q N z)
  have hbad : Tendsto (fun N => prob (π N) (fun z => ¬ Q N z ≤ 1/4)) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => T34_prob_nonneg _ (hπ N) _)
    · filter_upwards [hmom] with N hN
      calc
        _ ≤ expect (π N) (Q N)/(1/4 : ℝ) :=
          T34_markov (π N) (hπ N) _ (Q N) (1/4) (by norm_num) (hQ N)
            (fun z hz => (lt_of_not_ge hz).le)
        _ ≤ (C/N)/(1/4 : ℝ) := div_le_div_of_nonneg_right hN (by norm_num)
        _ = (4*C)/(N : ℝ) := by ring
    · have hi := tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using hi.const_mul (4*C)
  have hW : InProb π W := by
    apply (dl2_proof π hπ W).2
    apply squeeze_zero' (g := fun N => (4*A^2*C)*((b N)^6/(N : ℝ)))
      (Eventually.of_forall fun N => by
        simpa only [expect_const] using expect_mono (π N) (hπ N) (fun _ => 0)
          (fun z => (W N z)^2) (fun z => sq_nonneg _))
    · filter_upwards [hb, hmom, eventually_gt_atTop 0] with N hbN hmN hN
      have hn : (0 : ℝ) < N := by exact_mod_cast hN
      have h2 : 1 ≤ (b N)^2 := one_le_pow₀ hbN
      have h6 : (1+(b N)^2)^2 ≤ 4*(b N)^6 := by
        have h4 : (b N)^4 ≤ (b N)^6 := by
          have hh := mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith : 0 ≤ b N) 4)
          convert hh using 1 <;> ring
        nlinarith [sq_nonneg ((b N)^2-1)]
      have he : expect (π N) (fun z => (W N z)^2) =
          (A*(1+(b N)^2))^2*expect (π N) (Q N) := by
        have hh : (fun z => (W N z)^2) =
            fun z => (A*(1+(b N)^2))^2*Q N z := by
          funext z
          dsimp only [W]
          rw [mul_pow, Real.sq_sqrt (hQ N z)]
        rw [hh, expect_mul]
      rw [he]
      calc
        _ ≤ (A*(1+(b N)^2))^2*(C/N) :=
          mul_le_mul_of_nonneg_left hmN (sq_nonneg _)
        _ ≤ (4*A^2*C)*((b N)^6/(N : ℝ)) := by
          have hh := mul_le_mul_of_nonneg_left h6
            (by positivity : 0 ≤ A^2*(C/(N : ℝ)))
          convert hh using 1 <;> ring
    · simpa only [mul_zero] using hrate.const_mul (4*A^2*C)
  exact dl3_proof π hπ U W (fun N z => Q N z ≤ 1/4) hbad
    (hU.mono fun N hN z hz => (hN z hz).trans (le_abs_self _)) hW

theorem TailB_Ned_scaled_rows {N : ℕ} (p : ℝ) (R : CircleTable N)
    (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (b μ1 μ0 : ℝ) (z : Assignment N)
    (hN : 0 < N) :
    (N : ℝ)*(∑ i, nedVRow p R D K b μ1 μ0 i z) =
      TailB_Ned_form D K b
        (fun i => residualContrast (fun _ => p) R (fun _ a => if a then μ1 else μ0) i z) /
          (N : ℝ) := by
  rw [TailB_Ned_rows_form]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hn]

/-- The observed-denominator and observed-mean substitution, for arbitrary
bounded kernels on a supported set of pairs. -/
theorem TailB_Ned_plugin_bound {N : ℕ} (p : ℝ) (R : CircleTable N)
    (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (b M Cb Lk δ : ℝ)
    (hp : 0 < p ∧ p < 1) (hN : 0 < N) (hb : 0 < b)
    (hM : 0 ≤ M) (hLk : 0 ≤ Lk) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1/2)
    (hR : ∀ i z, |R i z| ≤ M) (hD : ∀ i j, 0 ≤ D i j)
    (hsp : ∀ i, ((ball D i b).card : ℝ) ≤ Cb*(1+b^2))
    (hK : ∀ t, 0 ≤ t → |K t| ≤ Lk) (hsupp : ∀ t, 1 < t → K t = 0)
    (z : Assignment N) (hB : ∀ a, |T42_B p R a z| ≤ δ)
    (hE : ∀ a, |T42_E p a z| ≤ δ) :
    let S := 1/p+1/(1-p)
    let C := 2*M*S
    let L := (4*M+4)*S
    |(N : ℝ)*(kernelVariance z (residual R z) (distanceKernel D K b)-
      nedV2 p R D K b z)| ≤ Cb*(1+b^2)*(Lk*L*(2*C+L)*δ) := by
  classical
  dsimp only
  let S := 1/p+1/(1-p)
  let C := 2*M*S
  let L := (4*M+4)*S
  have hS : 0 ≤ S := add_nonneg (one_div_pos.mpr hp.1).le
    (one_div_pos.mpr (sub_pos.mpr hp.2)).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let x := fun i => (N : ℝ)*lambda z i*residual R z i
  let y := fun i => residualContrast (fun _ => p) R (fun _ a => barMu (fun _ => p) R a) i z
  have hy : ∀ i, |y i| ≤ C := by
    intro i
    have hr : ∀ i z, |R i z-barMu (fun _ => p) R (z i)| ≤ 2*M := by
      intro i z
      exact (abs_sub _ _).trans (by linarith [hR i z, T42_barMu_bound p R hp hN M hR (z i)])
    have ht := CLTCompletion.raw_contrast_abs_le p (2*M)
      (T42_recenter p R) hp (by positivity) hr i z
    have hc : C = 2*M/p+2*M/(1-p) := by dsimp [C, S]; ring
    rw [hc]
    convert ht using 1
    cases hz : z i <;> simp [y, T42_recenter, residualContrast, bit, hz]
  have hxy : ∀ i, |x i-y i| ≤ L*δ :=
    GP0042B2b_scaled_residual p R hp hN M δ hM hδ hδhalf hR z hB hE
  have he : (N : ℝ)*(kernelVariance z (residual R z) (distanceKernel D K b)-
      nedV2 p R D K b z) = (TailB_Ned_form D K b x-TailB_Ned_form D K b y)/(N : ℝ) := by
    rw [mul_sub, TailB_Ned_kernel_form R z D K b hN hb hsupp]
    have hh := TailB_Ned_scaled_rows p R D K b
      (barMu (fun _ => p) R true) (barMu (fun _ => p) R false) z hN
    change (N : ℝ)*nedV2 p R D K b z = _ at hh
    rw [hh, ← sub_div]
    congr 2
  rw [he]
  unfold TailB_Ned_form
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  apply TailB_Ned_supported_sum_bound hN D b Cb (Lk*L*(2*C+L)*δ) (by positivity) hsp
  intro i j _
  rw [← sub_mul, abs_mul]
  calc
    _ ≤ (L*(2*C+L)*δ)*Lk := mul_le_mul
      (GP0042B2b_product_compare x y C L δ hC hL hδ (by linarith) hy hxy i j)
      (hK _ (div_nonneg (hD i j) hb.le)) (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Covariance summation with the actual shifted shell and quadratic ball counts. -/
theorem TailB_Ned_shifted_covariance_sum {N : ℕ} (π : Fin N → ℝ)
    (X : Fin N → Assignment N → ℝ) (D : Fin N → Fin N → ℝ)
    (ψ : ℝ → ℝ) (Cb b A e U F : ℝ)
    (hCb : 0 < Cb) (hb : 1 ≤ b) (hA : 0 ≤ A) (he : 4 < e)
    (hU : 0 ≤ U) (hF : 0 ≤ F)
    (hψ : ∀ t, 0 ≤ t → 0 ≤ ψ t) (hanti : AntitoneOn ψ (Set.Ici 0))
    (henv : ∀ t, 1 ≤ t → ψ t ≤ A*t^(-e))
    (hsp : ∀ i s, 0 ≤ s → ((ball D i s).card : ℝ) ≤ Cb*(1+s^2))
    (hnear : ∀ i j, D i j ≤ 3*b → |cov π (X i) (X j)| ≤ U)
    (hfar : ∀ i j, 3*b < D i j → |cov π (X i) (X j)| ≤ F*ψ (D i j/3-b)) :
    variance π (fun z => ∑ i, X i z) ≤
      (N : ℝ)*(Cb*(1+(3*b)^2)*U+
        F*(Cb*b^2*(37*ψ 0+148*A/(1-(2 : ℝ)^(2-e))))) := by
  classical
  rw [variance_sum]
  have hrow (i : Fin N) : (∑ j, cov π (X i) (X j)) ≤
      Cb*(1+(3*b)^2)*U+F*(Cb*b^2*(37*ψ 0+148*A/(1-(2 : ℝ)^(2-e)))) := by
    have hcompl : (ball D i (3*b))ᶜ = Finset.univ.filter (fun j => 3*b < D i j) := by
      ext j
      simp [ball, not_le]
    calc
      _ ≤ ∑ j, |cov π (X i) (X j)| := Finset.sum_le_sum fun j _ => le_abs_self _
      _ = (∑ j ∈ ball D i (3*b), |cov π (X i) (X j)|) +
          ∑ j ∈ Finset.univ.filter (fun j => 3*b < D i j), |cov π (X i) (X j)| := by
        rw [← hcompl]
        exact (Finset.sum_add_sum_compl _ _).symm
      _ ≤ ((ball D i (3*b)).card : ℝ)*U+
          F*(∑ j ∈ Finset.univ.filter (fun j => 3*b < D i j), ψ (D i j/3-b)) := by
        apply add_le_add
        · calc
            _ ≤ ∑ _j ∈ ball D i (3*b), U := Finset.sum_le_sum
              fun j hj => hnear i j (Finset.mem_filter.mp hj).2
            _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
        · rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun j hj => hfar i j (Finset.mem_filter.mp hj).2
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (hsp i _ (by linarith)) hU)
        (mul_le_mul_of_nonneg_left
          (TailB_Ned_shifted_shell_sum D i ψ Cb b A e hCb hb hA he hψ hanti henv (hsp i)) hF)
  calc
    _ ≤ ∑ _i : Fin N, (Cb*(1+(3*b)^2)*U+
        F*(Cb*b^2*(37*ψ 0+148*A/(1-(2 : ℝ)^(2-e))))) :=
      Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem TailB_Ned_contrast_formula {N : ℕ} (p : ℝ) (R : CircleTable N)
    (f : Bool → ℝ) (i : Fin N) (z : Assignment N) :
    residualContrast (fun _ => p) R (fun _ a => f a) i z =
      armSign (z i)/coin p (z i)*(R i z-f (z i)) := by
  cases hz : z i <;> simp [residualContrast, bit, armSign, coin, hz] <;> ring

theorem TailB_Ned_coefficient_bound (p : ℝ) (hp : 0 < p ∧ p < 1) (a : Bool) :
    |armSign a/coin p a| ≤ 1/p+1/(1-p) := by
  have hq : 0 < 1-p := sub_pos.mpr hp.2
  have hpi : 0 < 1/p := one_div_pos.mpr hp.1
  have hqi : 0 < 1/(1-p) := one_div_pos.mpr hq
  cases a <;> simp only [armSign, coin, Bool.false_eq_true, ite_false, ite_true,
    abs_div, abs_neg, abs_one, abs_of_pos hp.1, abs_of_pos hq] <;> linarith

theorem TailB_Ned_contrast_bound {N : ℕ} (p : ℝ) (R : CircleTable N)
    (f : Bool → ℝ) (M : ℝ) (hp : 0 < p ∧ p < 1) (hM : 0 ≤ M)
    (hR : ∀ i z, |R i z| ≤ M) (hf : ∀ a, |f a| ≤ M) (i : Fin N) (z : Assignment N) :
    |residualContrast (fun _ => p) R (fun _ a => f a) i z| ≤ 2*M*(1/p+1/(1-p)) := by
  rw [TailB_Ned_contrast_formula, abs_mul]
  have hS : 0 ≤ 1/p+1/(1-p) := add_nonneg (one_div_pos.mpr hp.1).le
    (one_div_pos.mpr (sub_pos.mpr hp.2)).le
  have hr : |R i z-f (z i)| ≤ 2*M :=
    (abs_sub _ _).trans (by linarith [hR i z, hf (z i)])
  calc
    _ ≤ (1/p+1/(1-p))*(2*M) :=
      mul_le_mul (TailB_Ned_coefficient_bound p hp (z i)) hr (abs_nonneg _) hS
    _ = _ := by ring

theorem TailB_Ned_arm_mean_error {N : ℕ} (p : ℝ) (R : CircleTable N)
    (hp : 0 < p ∧ p < 1) (hN : 0 < N) (δ : ℝ) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1/2)
    (z : Assignment N) (a : Bool) (hB : |T42_B p R a z| ≤ δ)
    (hE : |T42_E p a z| ≤ δ) :
    |armMean R z a-barMu (fun _ => p) R a| ≤ 2*δ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < coin p a := T42_coin_pos p hp a
  have hcnear : 1/2 ≤ T42_E p a z+1 := by have := (abs_le.mp hE).1; linarith
  have hcpos : 0 < T42_E p a z+1 := by linarith
  have hcnt : 0 < armCount z a := by
    have hh : T42_E p a z+1 = armCount z a/(N*coin p a) := by
      simp only [T42_E, sub_add_cancel]
    rw [hh] at hcpos
    exact (div_pos_iff_of_pos_right (mul_pos hn hc)).mp hcpos
  rw [GP0042B2b_arm_centering p R hp hN z a hcnt, abs_div, abs_of_pos hcpos,
    div_le_iff₀ hcpos]
  nlinarith

/-- The second supported-pair substitution, replacing observed arm means by
their deterministic marginalized means. -/
theorem TailB_Ned_arm_substitution_bound {N : ℕ} (p : ℝ) (R : CircleTable N)
    (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (b M Cb Lk δ : ℝ)
    (hp : 0 < p ∧ p < 1) (hN : 0 < N) (hb : 0 < b)
    (hM : 0 ≤ M) (hLk : 0 ≤ Lk) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1/2)
    (hR : ∀ i z, |R i z| ≤ M) (hD : ∀ i j, 0 ≤ D i j)
    (hsp : ∀ i, ((ball D i b).card : ℝ) ≤ Cb*(1+b^2))
    (hK : ∀ t, 0 ≤ t → |K t| ≤ Lk)
    (z : Assignment N) (hB : ∀ a, |T42_B p R a z| ≤ δ)
    (hE : ∀ a, |T42_E p a z| ≤ δ) :
    let S := 1/p+1/(1-p)
    let C := 2*M*S
    let L := 2*S
    |(N : ℝ)*(nedV1 p R D K b z-nedV2 p R D K b z)| ≤
      Cb*(1+b^2)*(Lk*L*(2*C+L)*δ) := by
  classical
  dsimp only
  let S := 1/p+1/(1-p)
  let C := 2*M*S
  let L := 2*S
  have hS : 0 ≤ S := add_nonneg (one_div_pos.mpr hp.1).le
    (one_div_pos.mpr (sub_pos.mpr hp.2)).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let x := fun i => residualContrast (fun _ => p) R
    (fun _ a => if a then armMean R z true else armMean R z false) i z
  let y := fun i => residualContrast (fun _ => p) R
    (fun _ a => if a then barMu (fun _ => p) R true else barMu (fun _ => p) R false) i z
  have hmeans (a : Bool) : |armMean R z a-barMu (fun _ => p) R a| ≤ 2*δ :=
    TailB_Ned_arm_mean_error p R hp hN δ hδ hδhalf z a (hB a) (hE a)
  have hy : ∀ i, |y i| ≤ C := by
    intro i
    apply TailB_Ned_contrast_bound p R _ M hp hM hR
    intro a
    cases a <;> exact NedFarCovariance.barMu_abs_le p hp R M hM hR _
  have hxy : ∀ i, |x i-y i| ≤ L*δ := by
    intro i
    have he : x i-y i = armSign (z i)/coin p (z i)*
        (barMu (fun _ => p) R (z i)-armMean R z (z i)) := by
      dsimp only [x, y]
      rw [TailB_Ned_contrast_formula, TailB_Ned_contrast_formula]
      cases hz : z i <;> simp only [hz, Bool.false_eq_true, ite_false, ite_true] <;> ring
    rw [he, abs_mul, abs_sub_comm]
    exact (mul_le_mul (TailB_Ned_coefficient_bound p hp (z i)) (hmeans (z i))
      (abs_nonneg _) hS).trans_eq (by dsimp [L]; ring)
  have he : (N : ℝ)*(nedV1 p R D K b z-nedV2 p R D K b z) =
      (TailB_Ned_form D K b x-TailB_Ned_form D K b y)/(N : ℝ) := by
    rw [mul_sub]
    change (N : ℝ)*(∑ i, nedVRow p R D K b _ _ i z)-
      (N : ℝ)*(∑ i, nedVRow p R D K b _ _ i z) = _
    rw [TailB_Ned_scaled_rows p R D K b _ _ z hN,
      TailB_Ned_scaled_rows p R D K b _ _ z hN, ← sub_div]
  rw [he]
  unfold TailB_Ned_form
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  apply TailB_Ned_supported_sum_bound hN D b Cb (Lk*L*(2*C+L)*δ) (by positivity) hsp
  intro i j _
  rw [← sub_mul, abs_mul]
  calc
    _ ≤ (L*(2*C+L)*δ)*Lk := mul_le_mul
      (GP0042B2b_product_compare x y C L δ hC hL hδ (by linarith) hy hxy i j)
      (hK _ (div_nonneg (hD i j) hb.le)) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem TailB_Ned_oracle_row_bound {N : ℕ} (p : ℝ) (R : CircleTable N)
    (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (B Cb L b : ℝ)
    (hN : 0 < N) (hp : 0 < p ∧ p < 1) (hB : 0 ≤ B) (hCb : 0 ≤ Cb)
    (hL : 0 ≤ L) (hb : 1 ≤ b) (hR : ∀ i z, |R i z| ≤ B)
    (hD : ∀ i j, 0 ≤ D i j)
    (hsp : ∀ i, ((ball D i b).card : ℝ) ≤ Cb*(1+b^2))
    (hK : ∀ t, 0 ≤ t → |K t| ≤ L) (i : Fin N) (z : Assignment N) :
    |nedVRow p R D K b (barMu (fun _ => p) R true) (barMu (fun _ => p) R false) i z| ≤
      (2*Cb*L*(2*B/min p (1-p))^2)*b^2/(N : ℝ)^2 := by
  classical
  let A := 2*B/min p (1-p)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 < min p (1-p) := lt_min hp.1 (sub_pos.mpr hp.2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he := (NedFarCovariance.e1_proof p R B B
    (barMu (fun _ => p) R true) (barMu (fun _ => p) R false) hN hp hR
    (NedFarCovariance.barMu_abs_le p hp R B hB hR true)
    (NedFarCovariance.barMu_abs_le p hp R B hB hR false)).1
  have he' (k : Fin N) :
      |nedEpsilon p R (barMu (fun _ => p) R true) (barMu (fun _ => p) R false) k z| ≤ A/N :=
    (he k z).trans_eq (by dsimp [A]; ring)
  have hcard : ((ball D i b).card : ℝ) ≤ 2*Cb*b^2 :=
    (hsp i).trans (by nlinarith [mul_nonneg hCb (sub_nonneg.mpr (one_le_pow₀ hb : 1 ≤ b^2))])
  unfold nedVRow
  calc
    _ ≤ ∑ j ∈ ball D i b, |nedEpsilon p R (barMu (fun _ => p) R true)
        (barMu (fun _ => p) R false) i z*nedEpsilon p R (barMu (fun _ => p) R true)
        (barMu (fun _ => p) R false) j z*K (D i j/b)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ ball D i b, (A/(N : ℝ))^2*L := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      exact (mul_le_mul (mul_le_mul (he' i) (he' j) (abs_nonneg _) (by positivity))
        (hK _ (div_nonneg (hD i j) (by linarith))) (abs_nonneg _)
        (by positivity)).trans_eq (by ring)
    _ = ((ball D i b).card : ℝ)*((A/(N : ℝ))^2*L) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2*Cb*b^2)*((A/(N : ℝ))^2*L) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by dsimp [A]; ring

/-- The centered oracle HAC has second moment `O(b⁶/N)` after multiplication
by `N`; the far covariance theorem retains its original `N⁻⁴` factor. -/
theorem TailB_Ned_oracle_second
    {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    {P : PopulationSequence Space} {p d : ℝ} (hS : Standing P p d)
    (E : ScoreEnvelope P p d) (K : ℝ → ℝ) (b : ℕ → ℝ)
    (hK : KernelConditions K) (hb : ∀ᶠ N in atTop, 1 ≤ b N) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ᶠ N : ℕ in atTop,
      expect (fun _ => p) (fun z => ((N : ℝ)*
        (nedV2 p (circleAverage (P N) d) (nodeSeparation (P N)) K (b N) z-
          expect (fun _ => p) (nedV2 p (circleAverage (P N) d) (nodeSeparation (P N)) K (b N))))^2) ≤
        V*(b N)^6/(N : ℝ) := by
  classical
  obtain ⟨Lk, hLk⟩ := hK.2.2.1
  have hL : 0 ≤ Lk := (abs_nonneg _).trans (hLk 0 le_rfl).le
  obtain ⟨C, hfar⟩ := (ned_far_covariance_under_uniform_spacing P p d K E.ψ b hS.hp
    hS.hb hS.hmetric hS.hspacing hK E.hψ E.hψanti ⟨E.G, E.hned⟩ hS.hWD hb).2
  let H := 2*E.Cb*Lk*(2*E.B/min p (1-p))^2
  let F := 2*|C| * E.Cb
  let S := 37*E.ψ 0+148*E.A/(1-(2 : ℝ)^(2-E.e))
  let V := 10*E.Cb*H^2+F*E.Cb*S
  have hden : 0 < 1-(2 : ℝ)^(2-E.e) := by
    have hh := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by linarith [E.he] : 2-E.e < 0)
    linarith
  have hCb : 0 ≤ E.Cb := E.hCb.le
  have hH : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) E.hCb.le) hL) (sq_nonneg _)
  have hF : 0 ≤ F := by
    dsimp [F]
    exact mul_nonneg (by positivity) E.hCb.le
  have hSS : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg (mul_nonneg (by norm_num) (E.hψ 0 le_rfl))
      (div_nonneg (mul_nonneg (by norm_num) E.hA) hden.le)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  refine ⟨V, hV, ?_⟩
  filter_upwards [hfar, E.hspacing, E.hbound, hb, eventually_gt_atTop 0] with N hf hsp hR hbN hN
  let D := nodeSeparation (P N)
  let R := circleAverage (P N) d
  let X := nedVRow p R D K (b N) (barMu (fun _ => p) R true) (barMu (fun _ => p) R false)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hb0 : 0 < b N := by linarith
  have hcard (i : Fin N) : ((ball D i (b N)).card : ℝ) ≤ 2*E.Cb*(b N)^2 :=
    (hsp i _ hb0.le).trans (by
      nlinarith [mul_nonneg E.hCb.le (sub_nonneg.mpr (one_le_pow₀ hbN : 1 ≤ (b N)^2))])
  have hrow (i : Fin N) (z : Assignment N) : |X i z| ≤ H*(b N)^2/(N : ℝ)^2 :=
    TailB_Ned_oracle_row_bound p R D K E.B E.Cb Lk (b N) hN hS.hp E.hB.le
      E.hCb.le hL hbN hR (E.hmetric N).1 (fun i => hsp i _ hb0.le) (fun t ht => (hLk t ht).le) i z
  rcases FiniteConditioning.fc7_proof (fun _ : Fin N => p) (fun _ => hS.hp) with
    ⟨hnn, _, _, _, _, hsup, _, _, hcov, _⟩
  have hnear (i j : Fin N) (_ : D i j ≤ 3*b N) :
      |cov (fun _ => p) (X i) (X j)| ≤ (H*(b N)^2/(N : ℝ)^2)^2 := by
    exact (hcov (X i) (X j)).trans ((mul_le_mul (hsup _ _ (hrow i))
      (hsup _ _ (hrow j)) (hnn _) (by positivity)).trans_eq (by ring))
  have hfar' (i j : Fin N) (hij : 3*b N < D i j) :
      |cov (fun _ => p) (X i) (X j)| ≤
        (F*(b N)^4/(N : ℝ)^4)*E.ψ (D i j/3-b N) := by
    have ht : 0 ≤ D i j/3-b N := by linarith
    have hψ0 := E.hψ _ ht
    have hlocal (k : Fin N) :
        (∑ l ∈ ball D k (b N), E.ψ (D i j/3-D k l)) ≤
          2*E.Cb*(b N)^2*E.ψ (D i j/3-b N) := by
      calc
        _ ≤ ∑ _l ∈ ball D k (b N), E.ψ (D i j/3-b N) := by
          apply Finset.sum_le_sum
          intro l hl
          have hdl := (Finset.mem_filter.mp hl).2
          exact E.hψanti ht (by change 0 ≤ D i j/3-D k l; linarith) (by linarith)
        _ = ((ball D k (b N)).card : ℝ)*E.ψ (D i j/3-b N) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcard k) hψ0
    have hmax : 0 ≤ max
        (∑ k ∈ ball D i (b N), E.ψ (D i j/3-D i k))
        (∑ l ∈ ball D j (b N), E.ψ (D i j/3-D j l)) := by
      apply le_trans _ (le_max_left _ _)
      apply Finset.sum_nonneg
      intro k hk
      have hdk := (Finset.mem_filter.mp hk).2
      exact E.hψ _ (by linarith)
    calc
      _ ≤ C*(b N)^2/(N : ℝ)^4 * max
          (∑ k ∈ ball D i (b N), E.ψ (D i j/3-D i k))
          (∑ l ∈ ball D j (b N), E.ψ (D i j/3-D j l)) := hf i j hij
      _ ≤ (|C| * (b N)^2/(N : ℝ)^4)*(2*E.Cb*(b N)^2*E.ψ (D i j/3-b N)) := by
        apply mul_le_mul _ (max_le (hlocal i) (hlocal j)) hmax (by positivity)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)) (by positivity)
      _ = _ := by dsimp [F]; ring
  have hv := TailB_Ned_shifted_covariance_sum (fun _ => p) X D E.ψ E.Cb (b N) E.A E.e
    ((H*(b N)^2/(N : ℝ)^2)^2) (F*(b N)^4/(N : ℝ)^4)
    E.hCb hbN E.hA E.he (sq_nonneg _) (by positivity) E.hψ E.hψanti E.henv hsp hnear hfar'
  have he : expect (fun _ => p) (fun z => ((N : ℝ)*
      (nedV2 p R D K (b N) z-expect (fun _ => p) (nedV2 p R D K (b N)) ))^2) =
      (N : ℝ)^2*variance (fun _ => p) (nedV2 p R D K (b N)) := by
    rw [variance, cov_centered, ← expect_mul]
    congr 1
    funext z
    ring
  rw [he]
  calc
    _ ≤ (N : ℝ)^2*((N : ℝ)*(E.Cb*(1+(3*b N)^2)*(H*(b N)^2/(N : ℝ)^2)^2+
        (F*(b N)^4/(N : ℝ)^4)*(E.Cb*(b N)^2*S))) :=
      mul_le_mul_of_nonneg_left hv (sq_nonneg _)
    _ = (E.Cb*H^2*(1+9*(b N)^2)*(b N)^4+F*E.Cb*S*(b N)^6)/(N : ℝ) := by
      field_simp [hn.ne']
      <;> ring
    _ ≤ V*(b N)^6/(N : ℝ) := by
      apply div_le_div_of_nonneg_right _ hn.le
      have hh := mul_le_mul_of_nonneg_left
        (show 1+9*(b N)^2 ≤ 10*(b N)^2 by nlinarith [(one_le_pow₀ hbN : 1 ≤ (b N)^2)])
        (by positivity : 0 ≤ E.Cb*H^2*(b N)^4)
      dsimp only [V]
      nlinarith only [hh]

theorem TailB_Ned_oracle_concentration
    {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    {P : PopulationSequence Space} {p d : ℝ} (hS : Standing P p d)
    (E : ScoreEnvelope P p d) (K : ℝ → ℝ) (b : ℕ → ℝ)
    (hK : KernelConditions K) (hb : ∀ᶠ N in atTop, 1 ≤ b N)
    (hrate : Asymptotics.IsLittleO atTop b (fun N => (N : ℝ)^(1/6 : ℝ))) :
    InProb (fun _ _ => p) (fun N z => (N : ℝ)*
      (nedV2 p (circleAverage (P N) d) (nodeSeparation (P N)) K (b N) z-
        expect (fun _ => p) (nedV2 p (circleAverage (P N) d) (nodeSeparation (P N)) K (b N)))) := by
  obtain ⟨V, hV, hVN⟩ := TailB_Ned_oracle_second hS E K b hK hb
  apply (dl2_proof _ (fun _ _ => hS.hp) _).2
  apply squeeze_zero' (g := fun N => V*((b N)^6/(N : ℝ)))
    (Eventually.of_forall fun N => by
      simpa only [expect_const] using expect_mono (fun _ => p) (fun _ => hS.hp)
        (fun _ => 0) _ (fun z => sq_nonneg _))
  · exact hVN.mono fun N hN => hN.trans_eq (by ring)
  · simpa only [mul_zero] using (TailB_Ned_bandwidth_sixth b hrate).const_mul V

theorem TailB_Ned_substitutions
    {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    {P : PopulationSequence Space} {p d : ℝ} (hS : Standing P p d)
    (E : ScoreEnvelope P p d) (K : ℝ → ℝ) (b : ℕ → ℝ)
    (hK : KernelConditions K) (hbpos : ∀ N, 0 < b N) (hb : ∀ᶠ N in atTop, 1 ≤ b N)
    (hrate : Asymptotics.IsLittleO atTop b (fun N => (N : ℝ)^(1/6 : ℝ))) :
    let R := fun N => circleAverage (P N) d
    let D := fun N => nodeSeparation (P N)
    let H := fun N z => kernelVariance z (residual (R N) z) (distanceKernel (D N) K (b N))
    InProb (fun _ _ => p) (fun N z => (N : ℝ)*(H N z-nedV1 p (R N) (D N) K (b N) z)) ∧
    InProb (fun _ _ => p) (fun N z => (N : ℝ)*
      (nedV1 p (R N) (D N) K (b N) z-nedV2 p (R N) (D N) K (b N) z)) := by
  classical
  dsimp only
  obtain ⟨Cq, hCq, hQ⟩ := TailB_Ned_errors_moment E hS.hp
  obtain ⟨Lk, hLk⟩ := hK.2.2.1
  have hLk0 : 0 ≤ Lk := (abs_nonneg _).trans (hLk 0 le_rfl).le
  let R := fun N => circleAverage (P N) d
  let D := fun N => nodeSeparation (P N)
  let Q := fun N => GP0042B2b_errors p (R N)
  let S := 1/p+1/(1-p)
  let C := 2*E.B*S
  let L0 := (4*E.B+4)*S
  let L1 := 2*S
  let H := fun N z => kernelVariance z (residual (R N) z) (distanceKernel (D N) K (b N))
  have hB0 : 0 ≤ E.B := E.hB.le
  have hCb : 0 ≤ E.Cb := E.hCb.le
  have hS0 : 0 ≤ S := add_nonneg (one_div_pos.mpr hS.hp.1).le
    (one_div_pos.mpr (sub_pos.mpr hS.hp.2)).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL0 : 0 ≤ L0 := by dsimp [L0]; positivity
  have hL1 : 0 ≤ L1 := by dsimp [L1]; positivity
  have hQ0 : ∀ N z, 0 ≤ Q N z := by intro N z; dsimp [Q, GP0042B2b_errors]; positivity
  have hrate6 := TailB_Ned_bandwidth_sixth b hrate
  have hplug : InProb (fun _ _ => p) (fun N z => (N : ℝ)*
      (H N z-nedV2 p (R N) (D N) K (b N) z)) := by
    apply TailB_Ned_supported_error_transfer _ (fun _ _ => hS.hp) b hb hrate6 Q _ Cq
      (E.Cb*(Lk*L0*(2*C+L0))) hCq (by positivity) hQ0 hQ
    filter_upwards [E.hbound, E.hspacing, eventually_gt_atTop 0] with N hRN hsp hN z hz
    let δ := Real.sqrt (Q N z)
    have hδ : 0 ≤ δ := Real.sqrt_nonneg _
    have hδhalf : δ ≤ 1/2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; exact hz⟩
    obtain ⟨hBs, hEs⟩ := GP0042B2b_errors_small p (R N) z δ hδ
      (by dsimp [δ]; rw [Real.sq_sqrt (hQ0 N z)])
    have hh := TailB_Ned_plugin_bound p (R N) (D N) K (b N) E.B E.Cb Lk δ hS.hp hN
      (hbpos N) hB0 hLk0 hδ hδhalf hRN (E.hmetric N).1 (fun i => hsp i _ (hbpos N).le)
      (fun t ht => (hLk t ht).le) hK.2.1 z hBs hEs
    exact hh.trans_eq (by dsimp [C, S, L0, δ]; ring)
  have harm : InProb (fun _ _ => p) (fun N z => (N : ℝ)*
      (nedV1 p (R N) (D N) K (b N) z-nedV2 p (R N) (D N) K (b N) z)) := by
    apply TailB_Ned_supported_error_transfer _ (fun _ _ => hS.hp) b hb hrate6 Q _ Cq
      (E.Cb*(Lk*L1*(2*C+L1))) hCq (by positivity) hQ0 hQ
    filter_upwards [E.hbound, E.hspacing, eventually_gt_atTop 0] with N hRN hsp hN z hz
    let δ := Real.sqrt (Q N z)
    have hδ : 0 ≤ δ := Real.sqrt_nonneg _
    have hδhalf : δ ≤ 1/2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; exact hz⟩
    obtain ⟨hBs, hEs⟩ := GP0042B2b_errors_small p (R N) z δ hδ
      (by dsimp [δ]; rw [Real.sq_sqrt (hQ0 N z)])
    have hh := TailB_Ned_arm_substitution_bound p (R N) (D N) K (b N) E.B E.Cb Lk δ hS.hp hN
      (hbpos N) hB0 hLk0 hδ hδhalf hRN (E.hmetric N).1 (fun i => hsp i _ (hbpos N).le)
      (fun t ht => (hLk t ht).le) z hBs hEs
    exact hh.trans_eq (by dsimp [C, S, L1, δ]; ring)
  refine ⟨?_, harm⟩
  have hneg := (dl4_proof _ (fun _ _ => hS.hp)).2.1 (-1) _ harm
  have hadd := (dl4_proof _ (fun _ _ => hS.hp)).1 _ _ hplug hneg
  convert hadd using 1
  funext N z
  ring

/-- A lower deterministic bias in liminf suffices for the positive-variance
Wald good event; no convergence of coverage probabilities is required. -/
theorem TailB_Ned_liminf_wald (π : ∀ N, Fin N → ℝ) (hπ : AdmissibleSeq π)
    (U W : ∀ N, Assignment N → ℝ) (V E : ℕ → ℝ)
    (hv : Nondegenerate V)
    (hclt : NormalLimit π (fun N z => U N z/Real.sqrt (V N)))
    (hbias : LiminfAtLeast (fun N => (N : ℝ)*(E N-V N)) 0)
    (herr : InProb π (fun N z => (N : ℝ)*(W N z-E N)))
    (α : ℝ) (hα : 0 < α ∧ α < 1) :
    Conservative (fun N => prob (π N) (fun z =>
      normalQuantile (α/2) ≤ U N z/Real.sqrt (W N z) ∧
      U N z/Real.sqrt (W N z) ≤ normalQuantile (1-α/2))) α := by
  obtain ⟨v, hv0, hvN⟩ := hv
  have hV : ∀ᶠ N in atTop, 0 < V N := by
    filter_upwards [hvN, eventually_gt_atTop 0] with N hf hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    exact (pos_of_mul_pos_right (hv0.trans_le hf) hn.le)
  have hshort : ∀ η : ℝ, 0 < η → η < 1 →
      Tendsto (fun N => prob (π N) (fun z => W N z < (1-η)*V N)) atTop (nhds 0) := by
    intro η hη _
    have he : 0 < η*v/2 := by positivity
    apply squeeze_zero' (g := fun N => prob (π N) (fun z => η*v/2 < |(N : ℝ)*(W N z-E N)|))
      (Eventually.of_forall fun N => T34_prob_nonneg _ (hπ N) _)
    · filter_upwards [hvN, hbias (η*v/2) he, eventually_gt_atTop 0] with N hf hb hN
      apply T34_prob_mono _ (hπ N)
      intro z hz
      have hn : (0 : ℝ) < N := by exact_mod_cast hN
      have hh := mul_lt_mul_of_pos_left hz hn
      have hf' := mul_le_mul_of_nonneg_left hf hη.le
      have ha := neg_le_abs ((N : ℝ)*(W N z-E N))
      nlinarith
    · exact herr _ he
  have hc := GP0042B2b_capped_pd_one_sided_wald π hπ U W V hV hclt hshort α hα
  obtain ⟨_, hstrict, _, hneg, hquant, _, _⟩ := DesignLimits.nf_proof
  have hqlow : normalQuantile (α/2) = -normalQuantile (1-α/2) := by
    apply hstrict.injective
    rw [hquant (α/2) (by linarith) (by linarith), hneg,
      hquant (1-α/2) (by linarith) (by linarith)]
    ring
  intro ε hε
  filter_upwards [hc ε hε] with N hN
  apply hN.trans
  apply T34_prob_mono _ (hπ N)
  intro z hz
  have hs : 0 < Real.sqrt (W N z) := Real.sqrt_pos.mpr hz.1
  have ha : |U N z/Real.sqrt (W N z)| ≤ normalQuantile (1-α/2) := by
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact hz.2
  rw [hqlow]
  exact abs_le.mp ha

/-- Public covariance decay interface for a bounded local family. -/
theorem TailB_Ned_local_covariance {N : ℕ} (p : ℝ)
    (X : Fin N → Assignment N → ℝ) (D : Fin N → Fin N → ℝ) (ψ : ℝ → ℝ)
    (Kc Cb A e M : ℝ) (hF : LocalFamily p X D ψ Kc Cb A e)
    (hM : 0 ≤ M) (hX : ∀ i z, |X i z| ≤ M) :
    (∀ i j, |cov (fun _ => p) (X i) (X j)| ≤ M^2) ∧
    (∀ i j, 0 < D i j → |cov (fun _ => p) (X i) (X j)| ≤ 2*M*Kc*ψ (D i j/3)) := by
  classical
  let π : Fin N → ℝ := fun _ => p
  have hp : FiniteConditioning.Admissible π := fun _ => hF.hp
  rcases FiniteConditioning.fc7_proof π hp with
    ⟨hnn, _, _, _, _, hsup, _, _, hcov, _⟩
  have hnorm (i : Fin N) : l2Norm π (X i) ≤ M := hsup _ _ (hX i)
  refine ⟨fun i j => (hcov _ _).trans
    ((mul_le_mul (hnorm i) (hnorm j) (hnn _) hM).trans_eq (by ring)), ?_⟩
  intro i j hij
  let t := D i j/3
  let Q := fun k => conditionOn π (ball D k t) (X k)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hψ := hF.hψ t ht
  have hQnorm (k : Fin N) : l2Norm π (Q k) ≤ M :=
    hsup _ _ (FiniteConditioning.fc5_proof π hp (ball D k t) (X k) M (hX k))
  have herror (k : Fin N) : l2Norm π (fun z => X k z-Q k z) ≤ Kc*ψ t := hF.hNED k t ht
  have hdisj : Disjoint (↑(ball D i t) : Set (Fin N)) (↑(ball D j t) : Set (Fin N)) := by
    apply Set.disjoint_left.mpr
    intro k hki hkj
    have hik : D i k ≤ t := (Finset.mem_filter.mp hki).2
    have hjk : D j k ≤ t := (Finset.mem_filter.mp hkj).2
    have hh := hF.hD.2.2.2 i k j
    rw [hF.hD.2.2.1 k j] at hh
    dsimp [t] at hik hjk
    linarith
  have hdepI : DependsOn (Q i) (↑(ball D i t) : Set (Fin N)) :=
    FiniteConditioning.fc1_proof π _ _
  have hdepJ : DependsOn (Q j) (↑(ball D i t) : Set (Fin N))ᶜ := by
    intro z z' hzz'
    apply FiniteConditioning.fc1_proof π (ball D j t) (X j)
    intro k hk
    exact hzz' k (fun hki => Set.disjoint_left.mp hdisj hki hk)
  have hzero : cov π (Q i) (Q j) = 0 := by
    unfold cov
    rw [GraphCompletion.expect_mul_of_disjoint_depends π _ _ _ hdepI hdepJ, sub_self]
  have hdecomp : cov π (X i) (X j) =
      cov π (fun z => X i z-Q i z) (X j)+cov π (Q i) (fun z => X j z-Q j z) := by
    have hleft : cov π (fun z => X i z-Q i z) (X j) = cov π (X i) (X j)-cov π (Q i) (X j) := by
      simp only [cov, sub_mul, expect_sub]
      ring
    have hright : cov π (Q i) (fun z => X j z-Q j z) = cov π (Q i) (X j)-cov π (Q i) (Q j) := by
      simp only [cov, mul_sub, expect_sub]
      ring
    linarith
  rw [hdecomp]
  calc
    _ ≤ |cov π (fun z => X i z-Q i z) (X j)|+
        |cov π (Q i) (fun z => X j z-Q j z)| := abs_add_le _ _
    _ ≤ (Kc*ψ t)*M+M*(Kc*ψ t) := add_le_add
      ((hcov _ _).trans (mul_le_mul (herror i) (hnorm j) (hnn _) (mul_nonneg hF.hKc hψ)))
      ((hcov _ _).trans (mul_le_mul (hQnorm i) (herror j) (hnn _) hM))
    _ = _ := by dsimp [t]; ring

/-- Uniform covariance tails; the exponent is `2-e`, using the containing
balls of the metric shells. -/
theorem TailB_Ned_covariance_tail {N : ℕ} (p : ℝ)
    (X : Fin N → Assignment N → ℝ) (D : Fin N → Fin N → ℝ) (ψ : ℝ → ℝ)
    (Kc Cb A e M r : ℝ) (hF : LocalFamily p X D ψ Kc Cb A e)
    (hM : 0 ≤ M) (hX : ∀ i z, |X i z| ≤ M) (hr : 1 ≤ r) (i : Fin N) :
    (∑ j ∈ (ball D i (3*r))ᶜ, |cov (fun _ => p) (X i) (X j)|) ≤
      (74*Cb*M*Kc*A/(1-(2 : ℝ)^(2-e)))*r^(2-e) := by
  classical
  have hr0 : 0 < r := by linarith
  have hKc : 0 ≤ Kc := hF.hKc
  have hA : 0 ≤ A := hF.hA
  have hcov := (TailB_Ned_local_covariance p X D ψ Kc Cb A e M hF hM hX).2
  have hh := dy_proof D i Cb r e (2*M*Kc*A*r^(-e))
    (fun j => |cov (fun _ => p) (X i) (X j)|) hF.hCb hr hF.he (by positivity) (hF.hspacing i) (by
      intro j hij
      have hdist : 0 < D i j := by linarith
      have ht : 1 ≤ D i j/3 := by linarith
      have hratio : 0 ≤ D i j/(3*r) := by positivity
      have heq : (D i j/3)^(-e) = r^(-e)*(D i j/(3*r))^(-e) := by
        rw [← Real.mul_rpow hr0.le hratio]
        congr 1
        field_simp [hr0.ne']
      refine ⟨abs_nonneg _, ?_⟩
      calc
        _ ≤ 2*M*Kc*ψ (D i j/3) := hcov i j hdist
        _ ≤ 2*M*Kc*(A*(D i j/3)^(-e)) :=
          mul_le_mul_of_nonneg_left (hF.henv _ ht) (by positivity)
        _ = (2*M*Kc*A*r^(-e))*(D i j/(3*r))^(-e) := by rw [heq]; ring)
  have hset : (ball D i (3*r))ᶜ = Finset.univ.filter (fun j => 3*r < D i j) := by
    ext j
    simp [ball, not_le]
  rw [hset]
  refine hh.trans_eq ?_
  have hp : r^2*r^(-e) = r^(2-e) := by
    rw [← Real.rpow_two, ← Real.rpow_add hr0]
    simp only [sub_eq_add_neg]
  calc
    _ = (74*Cb*M*Kc*A/(1-(2 : ℝ)^(2-e)))*(r^2*r^(-e)) := by ring
    _ = _ := by rw [hp]

theorem TailB_Ned_array_smoothing_bound {N : ℕ} (hN : 0 < N)
    (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (c : Fin N → Fin N → ℝ)
    (b r Cb M Ck Lk ε T : ℝ) (hb : 0 < b) (hr : 0 ≤ r)
    (hM : 0 ≤ M) (hCb : 0 ≤ Cb) (hCk : 0 ≤ Ck) (hLk : 0 ≤ Lk)
    (hD : ∀ i j, 0 ≤ D i j) (hc : ∀ i j, |c i j| ≤ M)
    (hsp : ∀ i, ((ball D i (3*r)).card : ℝ) ≤ Cb*(1+(3*r)^2))
    (hK : ∀ t, 0 ≤ t → |K t| ≤ Lk)
    (hsmall : ∀ t, 0 ≤ t → t < ε → |K t-1| ≤ Ck*|t|)
    (hre : 3*r/b < ε) (htail : ∀ i, ∑ j ∈ (ball D i (3*r))ᶜ, |c i j| ≤ T) :
    |(∑ i, ∑ j, (K (D i j/b)-1)*c i j)/(N : ℝ)| ≤
      M*Ck*Cb*(3*r/b+27*r^3/b)+(Lk+1)*T := by
  classical
  let f := fun i j => (K (D i j/b)-1)*c i j
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hrow (i : Fin N) : (∑ j, |f i j|) ≤
      M*Ck*Cb*(3*r/b+27*r^3/b)+(Lk+1)*T := by
    have hnear (j : Fin N) (hj : j ∈ ball D i (3*r)) :
        |f i j| ≤ (Ck*(3*r/b))*M := by
      have hd : D i j ≤ 3*r := (Finset.mem_filter.mp hj).2
      have ht0 := div_nonneg (hD i j) hb.le
      have ht := div_le_div_of_nonneg_right hd hb.le
      have hk := hsmall (D i j/b) ht0 (ht.trans_lt hre)
      rw [abs_of_nonneg ht0] at hk
      dsimp [f]
      rw [abs_mul]
      exact mul_le_mul (hk.trans (mul_le_mul_of_nonneg_left ht hCk))
        (hc i j) (abs_nonneg _) (by positivity)
    have hfar (j : Fin N) : |f i j| ≤ (Lk+1)*|c i j| := by
      dsimp [f]
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact (abs_sub _ _).trans (by
        simpa only [abs_one] using
          add_le_add (hK _ (div_nonneg (hD i j) hb.le)) (le_refl (1 : ℝ)))
    calc
      _ = (∑ j ∈ ball D i (3*r), |f i j|)+∑ j ∈ (ball D i (3*r))ᶜ, |f i j| :=
        (Finset.sum_add_sum_compl _ _).symm
      _ ≤ ((ball D i (3*r)).card : ℝ)*(Ck*(3*r/b)*M)+
          (Lk+1)*(∑ j ∈ (ball D i (3*r))ᶜ, |c i j|) := by
        apply add_le_add
        · calc
            _ ≤ ∑ _j ∈ ball D i (3*r), Ck*(3*r/b)*M := Finset.sum_le_sum hnear
            _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
        · rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun j _ => hfar j
      _ ≤ (Cb*(1+(3*r)^2))*(Ck*(3*r/b)*M)+(Lk+1)*T :=
        add_le_add (mul_le_mul_of_nonneg_right (hsp i) (by positivity))
          (mul_le_mul_of_nonneg_left (htail i) (by positivity))
      _ = _ := by ring
  rw [abs_div, abs_of_pos hn, div_le_iff₀ hn]
  calc
    _ ≤ ∑ i, ∑ j, |f i j| := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin N, (M*Ck*Cb*(3*r/b+27*r^3/b)+(Lk+1)*T) :=
      Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring

/-- Bounded, locally Lipschitz kernels smooth the covariance sum without
any measurability condition on the kernel. -/
theorem TailB_Ned_covariance_smoothing (p : ℝ)
    (X : ∀ N, Fin N → Assignment N → ℝ) (D : ∀ N, Fin N → Fin N → ℝ)
    (ψ K : ℝ → ℝ) (b : ℕ → ℝ) (Kc Cb A e M : ℝ)
    (hM : 0 ≤ M) (hCb : 0 < Cb) (hKc : 0 ≤ Kc) (hA : 0 ≤ A) (he : 4 < e)
    (hF : ∀ᶠ N in atTop, LocalFamily p (X N) (D N) ψ Kc Cb A e)
    (hX : ∀ᶠ N in atTop, ∀ i z, |X N i z| ≤ M)
    (hK : KernelConditions K) (hb : ∀ N, 0 < b N) (hdiv : Tendsto b atTop atTop) :
    Tendsto (fun N => (∑ i, ∑ j, (K (D N i j/b N)-1)*cov (fun _ => p) (X N i) (X N j))/(N : ℝ))
      atTop (nhds 0) := by
  classical
  obtain ⟨Lk, hLk⟩ := hK.2.2.1
  obtain ⟨ε, Ck, hε, _, hCk, hsmall⟩ := hK.2.2.2
  have hL : 0 ≤ Lk := (abs_nonneg _).trans (hLk 0 le_rfl).le
  let r := fun N => (b N)^(1/6 : ℝ)
  let T := 74*Cb*M*Kc*A/(1-(2 : ℝ)^(2-e))
  have hrpos (N : ℕ) : 0 < r N := Real.rpow_pos_of_pos (hb N) _
  have hrdiv : Tendsto r atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/6)).comp hdiv
  have hid1 (N : ℕ) : r N/b N = (b N)^(-(5/6 : ℝ)) := by
    dsimp [r]
    rw [← Real.rpow_sub_one (hb N).ne']
    norm_num
  have hid3 (N : ℕ) : (r N)^3/b N = (b N)^(-(1/2 : ℝ)) := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (hb N).le, ← Real.rpow_sub_one (hb N).ne']
    norm_num
  have ht1 : Tendsto (fun N => r N/b N) atTop (nhds 0) := by
    simp_rw [hid1]
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5/6)).comp hdiv
  have ht3 : Tendsto (fun N => (r N)^3/b N) atTop (nhds 0) := by
    simp_rw [hid3]
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp hdiv
  have htr : Tendsto (fun N => 3*r N/b N) atTop (nhds 0) := by
    simpa only [mul_div_assoc, mul_zero] using ht1.const_mul 3
  have htail : Tendsto (fun N => (r N)^(2-e)) atTop (nhds 0) := by
    rw [show 2-e = -(e-2) by ring]
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < e-2)).comp hrdiv
  have hbound : ∀ᶠ N in atTop,
      |(∑ i, ∑ j, (K (D N i j/b N)-1)*cov (fun _ => p) (X N i) (X N j))/(N : ℝ)| ≤
        M^2*Ck*Cb*(3*r N/b N+27*(r N)^3/b N)+(Lk+1)*(T*(r N)^(2-e)) := by
    filter_upwards [hF, hX, hrdiv.eventually (eventually_ge_atTop 1),
      htr.eventually (eventually_lt_nhds hε), eventually_gt_atTop 0] with N hFN hXN hrN hre hN
    apply TailB_Ned_array_smoothing_bound hN (D N) K
      (fun i j => cov (fun _ => p) (X N i) (X N j)) (b N) (r N) Cb (M^2) Ck Lk ε
      (T*(r N)^(2-e)) (hb N) (hrpos N).le (sq_nonneg _) hCb.le hCk.le hL hFN.hD.1
      (TailB_Ned_local_covariance p (X N) (D N) ψ Kc Cb A e M hFN hM hXN).1
      (fun i => hFN.hspacing i _ (by positivity)) (fun t ht => (hLk t ht).le) hsmall hre
    exact fun i => TailB_Ned_covariance_tail p (X N) (D N) ψ Kc Cb A e M (r N) hFN hM hXN hrN i
  have hlimit : Tendsto (fun N => M^2*Ck*Cb*(3*r N/b N+27*(r N)^3/b N)+
      (Lk+1)*(T*(r N)^(2-e))) atTop (nhds 0) := by
    simpa only [mul_div_assoc, mul_zero, add_zero] using
      (((ht1.const_mul 3).add (ht3.const_mul 27)).const_mul (M^2*Ck*Cb)).add
        ((htail.const_mul T).const_mul (Lk+1))
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  exact squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) hbound hlimit

theorem TailB_Ned_expect_form {N : ℕ} (π : Fin N → ℝ)
    (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (b : ℝ)
    (X : Fin N → Assignment N → ℝ) :
    expect π (fun z => TailB_Ned_form D K b (fun i => X i z)) =
      ∑ i, ∑ j ∈ ball D i b,
        (cov π (X i) (X j)+expect π (X i)*expect π (X j))*K (D i j/b) := by
  classical
  have hsum (s : Finset (Fin N)) (f : Fin N → Assignment N → ℝ) :
      expect π (fun z => ∑ j ∈ s, f j z) = ∑ j ∈ s, expect π (f j) := by
    unfold expect
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  unfold TailB_Ned_form
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun z => X i z*X j z*K (D i j/b)) =
      fun z => K (D i j/b)*(X i z*X j z) := by funext z; ring
  rw [he, expect_mul]
  unfold cov
  ring

/-- Exact finite covariance-smoothing and centered-effect decomposition. -/
theorem TailB_Ned_bias_identity {N : ℕ} (p : ℝ) (R : CircleTable N)
    (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (b : ℝ)
    (hN : 0 < N) (hp : 0 < p ∧ p < 1) (hb : 0 < b)
    (hsupp : ∀ t, 1 < t → K t = 0) :
    let X := residualContrast (fun _ => p) R (fun _ a => barMu (fun _ => p) R a)
    (N : ℝ)*(expect (fun _ => p) (nedV2 p R D K b)-
      variance (fun _ => p) (linearHajek (fun _ => p) R)) =
      (∑ i, ∑ j, (K (D i j/b)-1)*cov (fun _ => p) (X i) (X j))/(N : ℝ)+
      (∑ i, ∑ j, K (D i j/b)*(nodeEffect (fun _ => p) R i-ame (fun _ => p) R)*
        (nodeEffect (fun _ => p) R j-ame (fun _ => p) R))/(N : ℝ) := by
  classical
  dsimp only
  let π : Fin N → ℝ := fun _ => p
  let g := fun (_ : Fin N) a => barMu π R a
  let X := residualContrast π R g
  let a := fun i => nodeEffect π R i-ame π R
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hg : (fun (_ : Fin N) a => if a then barMu π R true else barMu π R false) = g := by
    funext i a
    cases a <;> rfl
  have hrow : nedV2 p R D K b = fun z => TailB_Ned_form D K b (fun i => X i z)/(N : ℝ)^2 := by
    funext z
    rw [nedV2, TailB_Ned_rows_form]
    rw [hg]
  have hm (i : Fin N) : expect π (X i) = a i := by
    rw [show X i = residualContrast π R g i from rfl, residualContrast_mean π R g i (fun _ => hp)]
    dsimp [residualEffect, g, a]
    rw [barMu_difference]
  have hv : variance π (linearHajek π R) = (∑ i, ∑ j, cov π (X i) (X j))/(N : ℝ)^2 := by
    change variance π (augmented π R g) = _
    rw [GraphCompletion.augmented_variance_reduction, variance_div, variance_sum]
  have hev : expect π (nedV2 p R D K b) =
      (∑ i, ∑ j, (cov π (X i) (X j)+a i*a j)*K (D i j/b))/(N : ℝ)^2 := by
    rw [hrow, expect_div, TailB_Ned_expect_form]
    simp_rw [hm]
    rw [← TailB_Ned_kernel_support D K b hb hsupp]
  have halg : (∑ i, ∑ j, (cov π (X i) (X j)+a i*a j)*K (D i j/b))-
      (∑ i, ∑ j, cov π (X i) (X j)) =
      (∑ i, ∑ j, (K (D i j/b)-1)*cov π (X i) (X j))+
        ∑ i, ∑ j, K (D i j/b)*a i*a j := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (N : ℝ)*(expect π (nedV2 p R D K b)-variance π (linearHajek π R)) = _
  rw [hev, hv]
  calc
    _ = ((∑ i, ∑ j, (cov π (X i) (X j)+a i*a j)*K (D i j/b))-
        (∑ i, ∑ j, cov π (X i) (X j)))/(N : ℝ) := by field_simp [hn] <;> ring
    _ = _ := by rw [halg, add_div]

theorem TailB_Ned_oracle_bias
    {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    {P : PopulationSequence Space} {p d : ℝ} (hS : Standing P p d)
    (E : ScoreEnvelope P p d) (K : ℝ → ℝ) (b : ℕ → ℝ)
    (hK : KernelConditions K) (hb : ∀ N, 0 < b N) (hdiv : Tendsto b atTop atTop)
    (hhom : LiminfAtLeast (kernelHomophily P p d K b) 0) :
    LiminfAtLeast (fun N => (N : ℝ)*
      (expect (fun _ => p) (nedV2 p (circleAverage (P N) d) (nodeSeparation (P N)) K (b N))-
        variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d)))) 0 := by
  classical
  let R := fun N => circleAverage (P N) d
  let D := fun N => nodeSeparation (P N)
  let X := fun N => residualContrast (fun _ => p) (R N) (fun _ a => barMu (fun _ => p) (R N) a)
  let S := 1/p+1/(1-p)
  let M := 2*E.B*S
  have hB : 0 ≤ E.B := E.hB.le
  have hS0 : 0 ≤ S := add_nonneg (one_div_pos.mpr hS.hp.1).le
    (one_div_pos.mpr (sub_pos.mpr hS.hp.2)).le
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hF : ∀ᶠ N in atTop, LocalFamily p (X N) (D N) E.ψ (E.L*E.G) E.Cb E.A E.e := by
    filter_upwards [E.hspacing] with N hsp
    let α : Fin N → Bool → ℝ := fun _ a => bit a/p-(1-bit a)/(1-p)
    let β : Fin N → Bool → ℝ := fun _ a =>
      -bit a*barMu (fun _ => p) (R N) true/p+(1-bit a)*barMu (fun _ => p) (R N) false/(1-p)
    have hx : X N = fun i z => α i (z i)*R N i z+β i (z i) := by
      funext i z
      dsimp [X, α, β, residualContrast]
      ring
    rw [hx]
    exact E.affine_family hS.hp N hsp α β (fun _ a => E.contrast_coefficient hS.hp a)
  have hX : ∀ᶠ N in atTop, ∀ i z, |X N i z| ≤ M := by
    filter_upwards [E.hbound] with N hR i z
    exact TailB_Ned_contrast_bound p (R N) _ E.B hS.hp hB hR
      (fun a => NedFarCovariance.barMu_abs_le p hS.hp (R N) E.B hB hR a) i z
  have hsm := TailB_Ned_covariance_smoothing p X D E.ψ K b (E.L*E.G) E.Cb E.A E.e M
    hM E.hCb (mul_nonneg E.hL.le E.hG) E.hA E.he hF hX hK hb hdiv
  intro ε hε
  filter_upwards [hhom (ε/2) (by linarith),
    (tendsto_order.mp hsm).1 (-ε/2) (by linarith), eventually_gt_atTop 0] with N hh hs hN
  have heq := TailB_Ned_bias_identity p (R N) (D N) K (b N) hN hS.hp (hb N) hK.2.1
  change (N : ℝ)*(expect (fun _ => p) (nedV2 p (R N) (D N) K (b N))-
      variance (fun _ => p) (linearHajek (fun _ => p) (R N))) =
    (∑ i, ∑ j, (K (D N i j/b N)-1)*cov (fun _ => p) (X N i) (X N j))/(N : ℝ)+
      kernelHomophily P p d K b N at heq
  rw [heq]
  linarith

/-- The corrected NED HAC theorem, with all four approximation/bias
clauses and the conservative liminf coverage conclusion. -/
theorem TailB_ned_hac_correction : (∀ {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
      (P : PopulationSequence Space)
      (p d : ℝ)
      (K : ℝ → ℝ)
      (bandwidth : ℕ → ℝ)
      (hp : 0 < p ∧ p < 1)
      (hd : 0 ≤ d)
      (hb : BoundedOutcomes P)
      (hWD : ∀ N, WellDefined (P N) d)
      (hNED : NEDConditions P p d)
      (hmetric : MetricNodeDistances P)
      (hspacing : QuadraticSpacing P)
      (hK : KernelConditions K)
      (hbpos : ∀ N, 0 < bandwidth N)
      (hbdiv : Tendsto bandwidth atTop atTop)
      (hbrate : Asymptotics.IsLittleO atTop bandwidth (fun N => (N : ℝ)^(1/6 : ℝ)))
      (hhom : LiminfAtLeast (kernelHomophily P p d K bandwidth) 0),
      let R := circleSequence P d
    let D := fun N => nodeSeparation (P N)
    let Vhac := fun N z => kernelVariance z (residual (R N) z) (distanceKernel (D N) K (bandwidth N))
    InProb (fun _ _ => p) (fun N z => N*(Vhac N z-nedV1 p (R N) (D N) K (bandwidth N) z)) ∧
    InProb (fun _ _ => p) (fun N z => N*(nedV1 p (R N) (D N) K (bandwidth N) z-
      nedV2 p (R N) (D N) K (bandwidth N) z)) ∧
    InProb (fun _ _ => p) (fun N z => N*(nedV2 p (R N) (D N) K (bandwidth N) z-
      expect (fun _ => p) (nedV2 p (R N) (D N) K (bandwidth N)))) ∧
    LiminfAtLeast (fun N => (N : ℝ)*(expect (fun _ => p) (nedV2 p (R N) (D N) K (bandwidth N))-
      variance (fun _ => p) (linearHajek (fun _ => p) (R N)))) 0 ∧
    (Nondegenerate (fun N => variance (fun _ => p) (linearHajek (fun _ => p) (R N))) →
      ∀ α : ℝ, 0 < α → α < 1 → Conservative (fun N => prob (fun _ => p) (fun z =>
        normalQuantile (α/2) ≤ (hajek (R N) z-ame (fun _ => p) (R N))/Real.sqrt (Vhac N z) ∧
          (hajek (R N) z-ame (fun _ => p) (R N))/Real.sqrt (Vhac N z) ≤ normalQuantile (1-α/2))) α)) := by
  intro Space instMetric instMeas P p d K bandwidth hp hd hb hWD hNED hmetric hspacing hK
    hbpos hbdiv hbrate hhom
  dsimp only
  have hS : Standing P p d := ⟨hp, hd, hb, Eventually.of_forall hWD, hNED, hmetric, hspacing⟩
  obtain ⟨E⟩ := exists_scoreEnvelope P p d hS
  have hband : ∀ᶠ N in atTop, 1 ≤ bandwidth N := hbdiv.eventually (eventually_ge_atTop 1)
  obtain ⟨h1, h2⟩ := TailB_Ned_substitutions hS E K bandwidth hK hbpos hband hbrate
  have h3 := TailB_Ned_oracle_concentration hS E K bandwidth hK hband hbrate
  have h4 := TailB_Ned_oracle_bias hS E K bandwidth hK hbpos hbdiv hhom
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro hv α hα0 hα1
  have hclt := (ned_headline_under_uniform_spacing P p d hp hd hb hS.hWD hNED hmetric hspacing).2.2.2 hv
  apply TailB_Ned_liminf_wald (fun _ _ => p) (fun _ _ => hp) _ _ _ _ hv hclt h4 ?_ α ⟨hα0, hα1⟩
  have ha := (dl4_proof _ (fun _ _ => hp)).1 _ _ h1 h2
  have ht := (dl4_proof _ (fun _ _ => hp)).1 _ _ ha h3
  convert ht using 1
  funext N z
  dsimp only [circleSequence]
  ring

end
end AronowAudit.P004.Wave1
