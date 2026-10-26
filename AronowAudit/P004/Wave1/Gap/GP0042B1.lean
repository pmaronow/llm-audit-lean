import AronowAudit.P004.P004_VarianceComponentsCompletion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.CDF

/-! T26, T34, and T42: tail homophily correction, finite-law concentration,
and the Hájek central limit theorem. -/
namespace AronowAudit.P004.Wave1

open scoped BigOperators Matrix Classical Topology
open MeasureTheory Filter
open CLTCompletion ComponentCompletion
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

variable {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
  [∀ N, MeasurableSpace (Space N)]

lemma T26_center {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (hN : 0 < N) :
    (∑ i, (nodeEffect p R i - ame p R)) = 0 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ame]
  field_simp [hn]
  <;> ring

lemma T26_center_bound {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hN : 0 < N) (M : ℝ)
    (hR : ∀ i z, |R i z| ≤ M) :
    ∀ i, |nodeEffect p R i - ame p R| ≤ 4 * M := by
  have hτ (i : Fin N) : |nodeEffect p R i| ≤ 2 * M := by
    exact (abs_sub _ _).trans (by
      have h1 := marginal_abs_le p hp R M hR i true
      have h0 := marginal_abs_le p hp R M hR i false
      change |marginal p R i true| + |marginal p R i false| ≤ 2*M
      linarith)
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hm : |ame p R| ≤ 2 * M := by
    rw [ame, abs_div, abs_of_pos hn]
    apply (div_le_iff₀ hn).mpr
    calc
      |∑ i, nodeEffect p R i| ≤ ∑ i, |nodeEffect p R i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, 2 * M := Finset.sum_le_sum (fun i _ => hτ i)
      _ = _ := by simp [mul_comm]
  intro i
  exact (abs_sub _ _).trans (by linarith [hτ i])

/-- The kernel bound assumes a nonnegative radius `r` in `hr`. -/
lemma T26_centered_kernel_split {N : ℕ} (hN : 0 < N)
    (D : Fin N → Fin N → ℝ) (a : Fin N → ℝ) (K φ : ℝ → ℝ)
    (b r A C Cb L ε T : ℝ) (hb : 0 < b) (hr : 0 ≤ r)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hCb : 0 ≤ Cb) (hL : 0 ≤ L)
    (hD : ∀ i j, 0 ≤ D i j) (hcenter : ∑ i, a i = 0)
    (ha : ∀ i, |a i| ≤ A) (henv : ∀ i j, |a i| * |a j| ≤ φ (D i j))
    (hcount : ∀ i, ((ball D i r).card : ℝ) ≤ Cb * (1 + r^2))
    (hK : ∀ t, 0 ≤ t → |K t| ≤ L)
    (hnear : ∀ t, 0 ≤ t → t < ε → |K t - 1| ≤ C * |t|)
    (hre : r / b < ε)
    (htail : ∀ i, (∑ j ∈ (ball D i r)ᶜ, φ (D i j)) ≤ T) :
    |(∑ i, ∑ j, K (D i j / b) * a i * a j) / (N : ℝ)| ≤
      A^2*C*Cb*(r/b + r^3/b) + (L+1)*T := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  let F := fun i j => (K (D i j / b)-1)*a i*a j
  have hcancel : (∑ i, ∑ j, K (D i j / b)*a i*a j) = ∑ i, ∑ j, F i j := by
    have hz : (∑ i, ∑ j, a i*a j) = 0 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, hcenter, mul_zero, Finset.sum_const_zero]
    dsimp [F]
    simp_rw [sub_mul, one_mul]
    simp only [Finset.sum_sub_distrib]
    rw [hz, sub_zero]
  have hprod (i j : Fin N) : |a i| * |a j| ≤ A^2 := by
    simpa only [pow_two] using mul_le_mul (ha i) (ha j) (abs_nonneg _) hA
  have hrow (i : Fin N) : (∑ j, |F i j|) ≤
      A^2*C*Cb*(r/b+r^3/b)+(L+1)*T := by
    have hsmall (j : Fin N) (hj : j ∈ ball D i r) :
        |F i j| ≤ (C*(r/b))*A^2 := by
      have hd : D i j ≤ r := (Finset.mem_filter.mp hj).2
      have ht : D i j/b ≤ r/b := div_le_div_of_nonneg_right hd hb.le
      have ht0 := div_nonneg (hD i j) hb.le
      have hk := hnear _ ht0 (ht.trans_lt hre)
      rw [abs_of_nonneg ht0] at hk
      have hk' : |K (D i j/b)-1| ≤ C*(r/b) :=
        hk.trans (mul_le_mul_of_nonneg_left ht hC)
      dsimp [F]
      rw [abs_mul, abs_mul, mul_assoc]
      exact mul_le_mul hk' (hprod i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg hC (div_nonneg hr hb.le))
    have hlarge (j : Fin N) : |F i j| ≤ (L+1)*φ (D i j) := by
      have hk : |K (D i j/b)-1| ≤ L+1 :=
        (abs_sub _ _).trans (by simpa using add_le_add (hK _ (div_nonneg (hD i j) hb.le)) (le_refl (1 : ℝ)))
      dsimp [F]
      rw [abs_mul, abs_mul, mul_assoc]
      exact mul_le_mul hk (henv i j) (by positivity) (by linarith)
    calc
      (∑ j, |F i j|) = (∑ j ∈ ball D i r, |F i j|) +
          ∑ j ∈ (ball D i r)ᶜ, |F i j| :=
        (Finset.sum_add_sum_compl (ball D i r) (fun j => |F i j|)).symm
      _ ≤ (∑ _j ∈ ball D i r, (C*(r/b))*A^2) +
          ∑ j ∈ (ball D i r)ᶜ, (L+1)*φ (D i j) := by
        exact add_le_add (Finset.sum_le_sum hsmall)
          (Finset.sum_le_sum (fun j _ => hlarge j))
      _ = ((ball D i r).card : ℝ) * ((C*(r/b))*A^2) +
          (L+1)*(∑ j ∈ (ball D i r)ᶜ, φ (D i j)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
      _ ≤ (Cb*(1+r^2))*((C*(r/b))*A^2)+(L+1)*T :=
        add_le_add (mul_le_mul_of_nonneg_right (hcount i) (by positivity))
          (mul_le_mul_of_nonneg_left (htail i) (by linarith))
      _ = _ := by ring
  rw [hcancel, abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    |∑ i, ∑ j, F i j| ≤ ∑ i, |∑ j, F i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |F i j| := Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin N, (A^2*C*Cb*(r/b+r^3/b)+(L+1)*T) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = _ := by simp [mul_comm] <;> ring

theorem tail_homophily_correction_proof (P : PopulationSequence Space) (p d : ℝ)
    (K φ : ℝ → ℝ) (bandwidth : ℕ → ℝ) (hp : 0 < p ∧ p < 1)
    (hb : BoundedOutcomes P) (hWD : ∀ N, WellDefined (P N) d)
    (hmetric : MetricNodeDistances P) (hspacing : QuadraticSpacing P) (hK : KernelConditions K)
    (hdiv : Tendsto bandwidth atTop atTop) (hpos : ∀ N, 0 < bandwidth N)
    (hφ : ∀ s, 0 ≤ s → 0 ≤ φ s)
    (henvelope : ∀ᶠ N in atTop, ∀ i j,
      |nodeEffect (fun _ => p) (circleAverage (P N) d) i-ame (fun _ => p) (circleAverage (P N) d)| *
      |nodeEffect (fun _ => p) (circleAverage (P N) d) j-ame (fun _ => p) (circleAverage (P N) d)| ≤
        φ (nodeSeparation (P N) i j))
    (htail : ∀ r : ℕ → ℝ, Tendsto r atTop atTop →
      Tendsto (tailEnvelope P φ r) atTop (nhds 0)) :
    Tendsto (kernelHomophily P p d K bandwidth) atTop (nhds 0) := by
  obtain ⟨M, hM, hbM⟩ := hb
  obtain ⟨Cb, hCb, hspacing⟩ := hspacing
  obtain ⟨L, hL⟩ := hK.2.2.1
  obtain ⟨ε, C, hε, hε1, hC, hnear⟩ := hK.2.2.2
  have hL0 : 0 ≤ L := (abs_nonneg (K 0)).trans (hL 0 le_rfl).le
  let r : ℕ → ℝ := fun N => bandwidth N ^ (1/6 : ℝ)
  have hrpos (N : ℕ) : 0 < r N := Real.rpow_pos_of_pos (hpos N) _
  have hrdiv : Tendsto r atTop atTop := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/6)).comp hdiv
  have hid1 (N : ℕ) : r N / bandwidth N = bandwidth N ^ (-(5/6 : ℝ)) := by
    dsimp [r]
    rw [← Real.rpow_sub_one (hpos N).ne']
    norm_num
  have hid3 (N : ℕ) : (r N)^3 / bandwidth N = bandwidth N ^ (-(1/2 : ℝ)) := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (hpos N).le, ← Real.rpow_sub_one (hpos N).ne']
    norm_num
  have ht1 : Tendsto (fun N => r N / bandwidth N) atTop (nhds 0) := by
    simp_rw [hid1]
    exact (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<5/6)).comp hdiv
  have ht3 : Tendsto (fun N => (r N)^3 / bandwidth N) atTop (nhds 0) := by
    simp_rw [hid3]
    exact (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp hdiv
  have hbound : ∀ᶠ N in atTop, |kernelHomophily P p d K bandwidth N| ≤
      (4*M)^2*C*Cb*(r N/bandwidth N+(r N)^3/bandwidth N) +
        (L+1)*tailEnvelope P φ r N := by
    filter_upwards [eventually_gt_atTop 0, hbM, hspacing, henvelope,
      ht1.eventually (eventually_lt_nhds hε)] with N hN hbN hsN heN hreN
    let a := fun i : Fin N => nodeEffect (fun _ => p) (circleAverage (P N) d) i -
      ame (fun _ => p) (circleAverage (P N) d)
    apply T26_centered_kernel_split hN (nodeSeparation (P N)) a K φ
      (bandwidth N) (r N) (4*M) C Cb L ε (tailEnvelope P φ r N)
      (hpos N) (hrpos N).le (by positivity) hC.le hCb.le hL0
      (hmetric N).1 (T26_center _ _ hN)
    · exact T26_center_bound _ _ (fun _ => hp) hN M
        (circleAverage_abs_le (P N) d M (hWD N) (fun x z => (hbN x z).le))
    · exact heN
    · exact fun i => hsN i (r N) (hrpos N).le
    · exact fun t ht => (hL t ht).le
    · exact hnear
    · exact hreN
    · intro i
      exact le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)
  have htbound : Tendsto (fun N =>
      (4*M)^2*C*Cb*(r N/bandwidth N+(r N)^3/bandwidth N) +
        (L+1)*tailEnvelope P φ r N) atTop (nhds 0) := by
    simpa using ((ht1.add ht3).const_mul ((4*M)^2*C*Cb)).add
      ((htail r hrdiv).const_mul (L+1))
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  exact squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) hbound htbound

/-! ## T34: elementary finite-law concentration. -/
lemma T34_prob_nonneg {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (E : Assignment N → Prop) : 0 ≤ prob p E := by
  unfold prob expect
  exact Finset.sum_nonneg (fun z _ => mul_nonneg (design_weight_nonneg p hp z)
    (by dsimp; split_ifs <;> norm_num))

lemma T34_prob_mono {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (E F : Assignment N → Prop)
    (h : ∀ z, E z → F z) : prob p E ≤ prob p F := by
  apply expect_mono p hp
  intro z
  by_cases he : E z
  · simp only [if_pos he, if_pos (h z he), le_refl]
  · simp only [if_neg he]
    split_ifs <;> norm_num

lemma T34_prob_union {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (E F : Assignment N → Prop) :
    prob p (fun z => E z ∨ F z) ≤ prob p E + prob p F := by
  rw [prob, prob, prob, ← expect_add]
  apply expect_mono p hp
  intro z
  by_cases hE : E z <;> by_cases hF : F z <;> simp [hE, hF]

/-- Markov on any nonnegative majorant, for use on a good event. -/
lemma T34_markov {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (E : Assignment N → Prop)
    (H : Assignment N → ℝ) (t : ℝ) (ht : 0 < t)
    (hH : ∀ z, 0 ≤ H z) (hEH : ∀ z, E z → t ≤ H z) :
    prob p E ≤ expect p H / t := by
  apply (le_div_iff₀ ht).mpr
  have h := expect_mono p hp (fun z => t*(if E z then 1 else 0)) H (fun z => by
    by_cases he : E z
    · simpa only [if_pos he, mul_one] using hEH z he
    · simpa only [if_neg he, mul_zero] using hH z)
  rw [expect_mul] at h
  simpa only [prob, mul_comm] using h

lemma T34_chebyshev {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (X : Assignment N → ℝ)
    (t : ℝ) (ht : 0 < t) :
    prob p (fun z => t < |X z|) ≤ expect p (fun z => (X z)^2) / t^2 := by
  apply T34_markov p hp _ _ (t^2) (sq_pos_of_pos ht) (fun z => sq_nonneg _)
  intro z hz
  nlinarith [sq_abs (X z)]

lemma T34_count_moments {N : ℕ} (p : ℝ) (hp : 0 < p ∧ p < 1) (a : Bool) :
    expect (fun _ : Fin N => p) (fun z => armCount z a) = (N:ℝ)*coin p a ∧
    variance (fun _ : Fin N => p) (fun z => armCount z a) =
      (N:ℝ)*coin p a*(1-coin p a) := by
  let π := fun _ : Fin N => p
  let I := fun (i : Fin N) (z : Assignment N) => if z i = a then (1:ℝ) else 0
  let c := coin p a
  have hI (i : Fin N) : expect π (I i) = c := by
    simpa only [I, c, π, expect_const, mul_one] using
      selected_update π (fun _ => hp) (fun _ => (1:ℝ)) i a
  have hpair (i j : Fin N) (hij : i ≠ j) :
      expect π (fun z => I i z * I j z) = c*c := by
    have he : (fun z => I i z * I j z) = fun z => if z i = a then I j z else 0 := by
      funext z
      dsimp [I]
      split_ifs <;> simp_all
    rw [he, selected_update π (fun _ => hp) (I j) i a]
    have hu : (fun z => I j (Function.update z i a)) = I j := by
      funext z
      simp only [I, Function.update_of_ne hij.symm]
    rw [hu, hI]
  have hdiag (i : Fin N) : cov π (I i) (I i) = c*(1-c) := by
    have he : (fun z => I i z * I i z) = I i := by
      funext z
      dsimp [I]
      split_ifs <;> norm_num
    simp only [cov, he, hI]
    ring
  have hoff (i j : Fin N) (hij : i ≠ j) : cov π (I i) (I j) = 0 := by
    simp only [cov, hpair i j hij, hI, sub_self]
  constructor
  · change expect π (fun z => ∑ i, I i z) = _
    rw [expect_sum]
    simp only [hI, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rfl
  · change variance π (fun z => ∑ i, I i z) = _
    rw [variance_sum]
    have hi (i : Fin N) : (∑ j, cov π (I i) (I j)) = c*(1-c) := by
      rw [Finset.sum_eq_single i]
      · exact hdiag i
      · intro j _ hji
        exact hoff i j hji.symm
      · simp
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [c]
    ring

lemma T34_fraction_moments {N : ℕ} (p : ℝ) (hp : 0 < p ∧ p < 1)
    (hN : 0 < N) (a : Bool) :
    (∀ z : Assignment N, 0 ≤ armCount z a / N ∧ armCount z a / N ≤ 1) ∧
    expect (fun _ : Fin N => p) (fun z => (armCount z a/N-coin p a)^2) =
      coin p a*(1-coin p a)/N := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hcnt := T34_count_moments p hp (N := N) a
  constructor
  · intro z
    have hlo : 0 ≤ armCount z a := Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
    have hhi : armCount z a ≤ (N:ℝ) := by
      calc
        armCount z a ≤ ∑ _i : Fin N, (1:ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs <;> norm_num
        _ = _ := by simp
    exact ⟨div_nonneg hlo hn.le, (div_le_one hn).mpr hhi⟩
  · have hm : expect (fun _ : Fin N => p) (fun z => armCount z a / N) = coin p a := by
      rw [expect_div, hcnt.1]
      field_simp
    have hv := variance_div (fun _ : Fin N => p) (fun z => armCount z a) (N:ℝ)
    rw [hcnt.2] at hv
    have hc := cov_centered (fun _ : Fin N => p)
      (fun z => armCount z a / N) (fun z => armCount z a / N)
    simp only [hm] at hc
    change variance _ _ = _ at hc
    rw [hc] at hv
    simpa only [pow_two] using hv.trans (by field_simp <;> ring)

lemma T34_inverse_square (p q : ℝ) (hp : 0 < p) (hq : p/2 ≤ q) (hq1 : q ≤ 1) :
    |1/q^2-1/p^2| ≤ (4*(1+p)/p^4)*|q-p| := by
  have hq0 : 0 < q := by linarith
  have hd : 0 < q^2*p^2 := mul_pos (sq_pos_of_pos hq0) (sq_pos_of_pos hp)
  have hp4 : 0 < p^4 := pow_pos hp _
  have he : 1/q^2-1/p^2 = -(q-p)*(q+p)/(q^2*p^2) := by
    field_simp [hp.ne', hq0.ne'] <;> ring
  rw [he, abs_div, abs_mul, abs_neg, abs_of_pos (by linarith : 0 < q+p), abs_of_pos hd]
  have hsq : p^2 ≤ 4*q^2 := by nlinarith
  have hden : p^4 ≤ 4*(q^2*p^2) := by
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg p)]
  have hc : (q+p)/(q^2*p^2) ≤ 4*(1+p)/p^4 := by
    apply (div_le_div_iff₀ hd hp4).mpr
    calc
      (q+p)*p^4 ≤ (1+p)*p^4 := mul_le_mul_of_nonneg_right (by linarith) hp4.le
      _ ≤ (1+p)*(4*(q^2*p^2)) := mul_le_mul_of_nonneg_left hden (by linarith)
      _ = _ := by ring
  calc
    |q-p| * (q+p)/(q^2*p^2) = |q-p| * ((q+p)/(q^2*p^2)) := by ring
    _ ≤ |q-p| * (4*(1+p)/p^4) := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    _ = _ := by ring

theorem bernoulli_denominator_rate_proof (p : ℝ) (hp : 0 < p ∧ p < 1) :
    BigOp (fun _ _ => p) (fun N z => |(N : ℝ)^2/(armCount z true)^2-1/p^2|)
      (fun N => (Real.sqrt N)⁻¹) := by
  intro ε hε
  have hp0 : 0 < p := hp.1
  have hq0 : 0 < 1-p := sub_pos.mpr hp.2
  let v := p*(1-p)
  let A := Real.sqrt (v/ε) + 1
  let L := 4*(1+p)/p^4
  have hv : 0 < v := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hsmall : v/A^2 < ε := by
    have hs := Real.sq_sqrt (div_nonneg hv.le hε.le)
    have hnn := Real.sqrt_nonneg (v/ε)
    apply (div_lt_iff₀ (sq_pos_of_pos hA)).mpr
    have hs' : ε*(Real.sqrt (v/ε))^2 = v := by
      rw [hs]
      field_simp [hε.ne']
    have hcross := mul_nonneg hε.le hnn
    dsimp [A]
    nlinarith
  refine ⟨L*A, mul_pos hL hA, ?_⟩
  have ht : Tendsto (fun N : ℕ => A*(Real.sqrt N)⁻¹) atTop (nhds 0) := by
    simpa using (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop.const_mul A
  filter_upwards [eventually_gt_atTop 0, ht.eventually (eventually_lt_nhds (by linarith : 0 < p/2))]
    with N hN htN
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hn
  let t := A*(Real.sqrt N)⁻¹
  have htpos : 0 < t := mul_pos hA (inv_pos.mpr hs)
  have hinc : ∀ z : Assignment N,
      L*A*|(Real.sqrt N)⁻¹| < |(|(N:ℝ)^2/(armCount z true)^2-1/p^2|)| →
      t < |armCount z true/N-p| := by
    intro z hz
    by_contra hbad
    have hqerr : |armCount z true/N-p| ≤ t := le_of_not_gt hbad
    have hq := (T34_fraction_moments p hp hN true).1 z
    have hqlo : p/2 ≤ armCount z true/N := by
      have := (abs_le.mp hqerr).1
      dsimp [t] at this
      linarith
    have hqpos : 0 < armCount z true/N := by linarith
    have hcpos : 0 < armCount z true :=
      (div_pos_iff_of_pos_right hn).mp hqpos
    have he : (N:ℝ)^2/(armCount z true)^2 = 1/(armCount z true/N)^2 := by
      field_simp [hn.ne', hcpos.ne'] <;> ring
    have hi := T34_inverse_square p (armCount z true/N) hp.1 hqlo hq.2
    rw [he, abs_abs, abs_of_pos (inv_pos.mpr hs)] at hz
    have hboundInv : |1/(armCount z true/N)^2-1/p^2| ≤ L*t :=
      hi.trans (mul_le_mul_of_nonneg_left hqerr hL.le)
    have hz' : L*t < |1/(armCount z true/N)^2-1/p^2| := by
      simpa only [t, mul_assoc] using hz
    exact (not_lt_of_ge hboundInv) hz'
  have hprob := (T34_prob_mono (fun _ : Fin N => p) (fun _ => hp) _ _ hinc).trans
    (T34_chebyshev (fun _ : Fin N => p) (fun _ => hp)
      (fun z => armCount z true/N-p) t htpos)
  have hm : expect (fun _ : Fin N => p) (fun z => (armCount z true/N-p)^2) = v/N := by
    simpa [coin, v] using (T34_fraction_moments p hp hN true).2
  rw [hm] at hprob
  have hratio : (v/(N:ℝ))/t^2 = v/A^2 := by
    dsimp [t]
    rw [mul_pow, inv_pow, Real.sq_sqrt hn.le]
    field_simp [hA.ne', hn.ne'] <;> ring
  rw [hratio] at hprob
  exact hprob.trans_lt hsmall

/-! ## T42: deterministic arm recentering, finite moments, and CDF transfer. -/
def T42_recenter {N : ℕ} (p : ℝ) (R : CircleTable N) : CircleTable N :=
  fun i z => R i z - barMu (fun _ => p) R (z i)

def T42_arm_table {N : ℕ} (p : ℝ) (R : CircleTable N) (a : Bool) : CircleTable N :=
  fun i z => if z i = a then R i z - barMu (fun _ => p) R a else 0

def T42_B {N : ℕ} (p : ℝ) (R : CircleTable N) (a : Bool) (z : Assignment N) : ℝ :=
  (∑ i, if z i = a then R i z - barMu (fun _ => p) R a else 0) / (N * coin p a)

def T42_E {N : ℕ} (p : ℝ) (a : Bool) (z : Assignment N) : ℝ :=
  armCount z a / (N * coin p a) - 1

lemma T42_coin_pos (p : ℝ) (hp : 0 < p ∧ p < 1) (a : Bool) : 0 < coin p a := by
  cases a <;> simp [coin] <;> linarith [hp.1, hp.2]

lemma T42_barMu_bound {N : ℕ} (p : ℝ) (R : CircleTable N)
    (hp : 0 < p ∧ p < 1) (hN : 0 < N) (M : ℝ)
    (hR : ∀ i z, |R i z| ≤ M) (a : Bool) : |barMu (fun _ => p) R a| ≤ M := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [barMu, abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    |∑ i, marginal (fun _ => p) R i a| ≤ ∑ i, |marginal (fun _ => p) R i a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, M := Finset.sum_le_sum (fun i _ => marginal_abs_le _ (fun _ => hp) R M hR i a)
    _ = _ := by simp [mul_comm]

lemma T42_transform_interferes {N : ℕ} (R : CircleTable N)
    (f : Fin N → Bool → ℝ → ℝ) (i j : Fin N) :
    interferes (fun i z => f i (z i) (R i z)) i j → interferes R i j := by
  rintro (hij | ⟨z, z', he, hn⟩)
  · exact Or.inl hij
  · by_cases hij : i = j
    · exact Or.inl hij
    · right
      refine ⟨z, z', he, ?_⟩
      intro hr
      apply hn
      dsimp only
      rw [he i hij, hr]

lemma T42_transform_local {N : ℕ} (R : CircleTable N)
    (f : Fin N → Bool → ℝ → ℝ) (D : Fin N → Fin N → ℝ) (h : ℝ)
    (hloc : LocalAt R D h) : LocalAt (fun i z => f i (z i) (R i z)) D h := by
  intro i j hij
  rintro ⟨k, hik, hjk⟩
  exact hloc i j hij ⟨k, T42_transform_interferes R f i k hik,
    T42_transform_interferes R f j k hjk⟩

lemma T42_recenter_identity {N : ℕ} (p : ℝ) (R : CircleTable N) (hN : 0 < N) :
    ht (fun _ => p) (T42_recenter p R) =
      fun z => linearHajek (fun _ => p) R z - ame (fun _ => p) R := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  funext z
  have hsel (i : Fin N) :
      bit (z i)*(R i z-barMu (fun _ => p) R (z i))/p -
        (1-bit (z i))*(R i z-barMu (fun _ => p) R (z i))/(1-p) =
      bit (z i)*(R i z-barMu (fun _ => p) R true)/p -
        (1-bit (z i))*(R i z-barMu (fun _ => p) R false)/(1-p) := by
    cases hz : z i <;> simp [bit, hz]
  simp only [ht, T42_recenter, hsel, linearHajek, augmented,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← barMu_difference]
  field_simp <;> ring

lemma T42_recenter_mean {N : ℕ} (p : ℝ) (R : CircleTable N)
    (hp : 0 < p ∧ p < 1) (hN : 0 < N) :
    ame (fun _ => p) (T42_recenter p R) = 0 := by
  rw [← ht_unbiased _ _ (fun _ => hp), T42_recenter_identity p R hN,
    expect_sub, expect_const]
  change expect (fun _ => p) (augmented (fun _ => p) R
    (fun _ a => barMu (fun _ => p) R a)) - ame (fun _ => p) R = 0
  rw [augmented_unbiased _ _ _ (fun _ => hp), sub_self]

lemma T42_B_mean {N : ℕ} (p : ℝ) (R : CircleTable N)
    (hp : 0 < p ∧ p < 1) (hN : 0 < N) (a : Bool) :
    expect (fun _ => p) (T42_B p R a) = 0 := by
  let π := fun _ : Fin N => p
  let μ := barMu π R a
  have hc : coin p a ≠ 0 := (T42_coin_pos p hp a).ne'
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hi (i : Fin N) :
      expect π (fun z => if z i = a then R i z-μ else 0) =
        coin p a * (marginal π R i a-μ) := by
    have he : (fun z => if z i = a then R i z-μ else 0) =
        fun z => (if z i = a then R i z else 0) - (if z i = a then μ else 0) := by
      funext z
      split_ifs <;> simp
    rw [he, expect_sub, bernoulli_selection π R i a hc,
      selected_update π (fun _ => hp) (fun _ => μ) i a, expect_const]
    ring
  change expect π (fun z => (∑ i, if z i=a then R i z-μ else 0)/(N*coin p a)) = 0
  rw [expect_div, expect_sum]
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp [μ, barMu]
  field_simp <;> ring

lemma T42_arm_ht {N : ℕ} (p : ℝ) (R : CircleTable N) (a : Bool) :
    ht (fun _ => p) (T42_arm_table p R a) = fun z => armSign a * T42_B p R a z := by
  funext z
  have hi (i : Fin N) :
      bit (z i)*T42_arm_table p R a i z/p -
        (1-bit (z i))*T42_arm_table p R a i z/(1-p) =
      armSign a * (if z i=a then R i z-barMu (fun _ => p) R a else 0) / coin p a := by
    cases a <;> cases hz : z i <;> simp [T42_arm_table, armSign, bit, coin, hz] <;> ring
  unfold ht
  simp_rw [hi]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  simp only [T42_B, div_eq_mul_inv, mul_inv_rev]
  ring

/-- A generic centered HT second-moment bound on a finite local table. -/
lemma T42_ht_moment {N : ℕ} (p : ℝ) (F : CircleTable N)
    (B : Fin N → Finset (Fin N)) (hp : 0 < p ∧ p < 1) (hN : 0 < N)
    (M D : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hF : ∀ i z, |F i z| ≤ M)
    (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (hout : ∀ i j, j ∉ B i → ¬sharesSource F i j)
    (hdeg : ∀ i, ((B i).card : ℝ) ≤ D)
    (hm : expect (fun _ => p) (ht (fun _ => p) F) = 0) :
    expect (fun _ => p) (fun z => (ht (fun _ => p) F z)^2) ≤
      D*(M/p+M/(1-p))^2/N := by
  let π := fun _ : Fin N => p
  let T := fun i => residualContrast π F (fun _ _ => 0) i
  let S := M/p+M/(1-p)
  have hp0 : 0 < p := hp.1
  have hq0 : 0 < 1-p := sub_pos.mpr hp.2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hTabs : ∀ i z, |T i z| ≤ S := raw_contrast_abs_le p M F hp hM hF
  have hsecond (i : Fin N) : expect π (fun z => (T i z)^2) ≤ S^2 := by
    calc
      _ ≤ expect π (fun _ => S^2) := expect_mono π (fun _ => hp) _ _ (fun z => by
        have hh := hTabs i z
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (T i z)) hh 2)
      _ = _ := expect_const _ _
  have he : ht π F = fun z => (∑ i, T i z)/N := by
    funext z
    simp only [ht, T, residualContrast, sub_zero]
  have hvar := finite_covariance_degree_bound π (fun _ => hp) T B hsymm
    (fun i j hij => GraphCompletion.residual_cov_zero π F _ i j (hout i j hij))
  have hsum : (∑ i, (B i).card * expect π (fun z => (T i z)^2)) ≤ (N:ℝ)*D*S^2 := by
    calc
      _ ≤ ∑ _i : Fin N, D*S^2 := Finset.sum_le_sum (fun i _ =>
        (mul_le_mul_of_nonneg_left (hsecond i) (Nat.cast_nonneg _)).trans
          (mul_le_mul_of_nonneg_right (hdeg i) (sq_nonneg S)))
      _ = _ := by simp [mul_assoc]
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hv : variance π (ht π F) = expect π (fun z => (ht π F z)^2) := by
    change expect π (ht π F) = 0 at hm
    simp only [variance, cov]
    rw [hm]
    simp only [zero_mul, sub_zero, pow_two]
  rw [← he, hv] at hvar
  exact hvar.trans (by
    calc
      _ ≤ ((N:ℝ)*D*S^2)/(N:ℝ)^2 := div_le_div_of_nonneg_right hsum (sq_nonneg _)
      _ = _ := by
        change ((N:ℝ)*D*S^2)/(N:ℝ)^2 = D*S^2/N
        field_simp [hn.ne'] <;> ring)

lemma T42_B_moment {N : ℕ} (p : ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (hp : 0 < p ∧ p < 1) (hN : 0 < N)
    (M D : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D) (hR : ∀ i z, |R i z| ≤ M)
    (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (hout : ∀ i j, j ∉ B i → ¬sharesSource R i j)
    (hdeg : ∀ i, ((B i).card : ℝ) ≤ D) (a : Bool) :
    expect (fun _ => p) (fun z => (T42_B p R a z)^2) ≤
      D*((2*M)/p+(2*M)/(1-p))^2/N := by
  let F := T42_arm_table p R a
  have hF (i : Fin N) (z : Assignment N) : |F i z| ≤ 2*M := by
    dsimp [F, T42_arm_table]
    split_ifs
    · exact (abs_sub _ _).trans (by linarith [hR i z, T42_barMu_bound p R hp hN M hR a])
    · simpa using mul_nonneg (by norm_num : (0:ℝ)≤2) hM
  have houtF (i j : Fin N) (hij : j ∉ B i) : ¬sharesSource F i j := by
    rintro ⟨k, hik, hjk⟩
    apply hout i j hij
    exact ⟨k, T42_transform_interferes R (fun _ b x => if b=a then x-barMu (fun _ => p) R a else 0) i k hik,
      T42_transform_interferes R (fun _ b x => if b=a then x-barMu (fun _ => p) R a else 0) j k hjk⟩
  have hm : expect (fun _ => p) (ht (fun _ => p) F) = 0 := by
    rw [show F=T42_arm_table p R a from rfl, T42_arm_ht, expect_mul, T42_B_mean p R hp hN a, mul_zero]
  have hv := T42_ht_moment p F B hp hN (2*M) D (by positivity) hD hF hsymm houtF hdeg hm
  rw [show F=T42_arm_table p R a from rfl, T42_arm_ht] at hv
  cases a <;> simpa [armSign] using hv

lemma T42_E_moment {N : ℕ} (p : ℝ) (hp : 0 < p ∧ p < 1) (hN : 0 < N) (a : Bool) :
    expect (fun _ : Fin N => p) (fun z => (T42_E p a z)^2) =
      ((1-coin p a)/coin p a)/N := by
  have hc := T42_coin_pos p hp a
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have he : (fun z : Assignment N => (T42_E p a z)^2) =
      fun z => (armCount z a/N-coin p a)^2/(coin p a)^2 := by
    funext z
    dsimp [T42_E]
    field_simp [hc.ne', hn.ne'] <;> ring
  rw [he, expect_div, (T34_fraction_moments p hp hN a).2]
  field_simp [hc.ne', hn.ne'] <;> ring

lemma T42_ratio_error (B c : ℝ) (hc : |c-1| ≤ 1/2) :
    |B/c-B| ≤ B^2+(c-1)^2 := by
  have hc0 : 0 < c := by have := (abs_le.mp hc).1; linarith
  have hc2 : 1/2 ≤ c := by have := (abs_le.mp hc).1; linarith
  have he : B/c-B = -B*(c-1)/c := by field_simp [hc0.ne'] <;> ring
  rw [he, abs_div, abs_mul, abs_neg, abs_of_pos hc0]
  have hh : |B| * |c-1|/c ≤ 2*|B| * |c-1| := by
    apply (div_le_iff₀ hc0).mpr
    have hp := mul_nonneg (mul_nonneg (abs_nonneg B) (abs_nonneg (c-1)))
      (sub_nonneg.mpr hc2)
    nlinarith
  refine hh.trans ?_
  nlinarith [sq_nonneg (|B|-|c-1|), sq_abs B, sq_abs (c-1)]

lemma T42_linear_clt (P : PopulationSequence Space) (p d : ℝ)
    (hp : 0 < p ∧ p < 1) (hd : 0 ≤ d) (hP : SpatialLocalConditions P)
    (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hv : Nondegenerate (fun N => variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d)))) :
    NormalLimit (fun _ _ => p) (fun N z =>
      (linearHajek (fun _ => p) (circleAverage (P N) d) z -
        ame (fun _ => p) (circleAverage (P N) d)) /
      Real.sqrt (variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d)))) := by
  obtain ⟨M, hM, hbout⟩ := hP.1
  obtain ⟨h, hh, hloc⟩ := hP.2.1
  obtain ⟨c, hc⟩ := hP.2.2
  obtain ⟨v, hv, hvN⟩ := hv
  let R := fun N => circleAverage (P N) d
  let F := fun N => T42_recenter p (R N)
  let B : ∀ N, Fin N → Finset (Fin N) := fun N i => ball (nodeSeparation (P N)) i (h d)
  have hevent : ∀ᶠ N in atTop, 0<N ∧ (∀ i z, |R N i z|≤M) ∧
      LocalAt (R N) (nodeSeparation (P N)) (h d) ∧
      (∀ i, ((B N i).card:ℝ)≤c (h d)) ∧
      v≤(N:ℝ)*variance (fun _=>p) (linearHajek (fun _=>p) (R N)) := by
    filter_upwards [eventually_gt_atTop 0, hbout, hWD, hloc d hd,
      hc (h d) (hh d hd), hvN] with N hN hbN hwdN hlN hcN hvN
    refine ⟨hN, ?_, hlN, hcN, hvN⟩
    exact circleAverage_abs_le (P N) d M hwdN (fun x z => (hbN x z).le)
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp hevent
  have htail (n : ℕ) := hk (n+k) (Nat.le_add_left k n)
  have hF (n : ℕ) (i : Fin (n+k)) (z : Assignment (n+k)) : |F (n+k) i z|≤2*M := by
    exact (abs_sub _ _).trans (by
      linarith [(htail n).2.1 i z,
        T42_barMu_bound p (R (n+k)) hp (htail n).1 M (htail n).2.1 (z i)])
  have hvF (N : ℕ) (hN : 0<N) : variance (fun _=>p) (ht (fun _=>p) (F N)) =
      variance (fun _=>p) (linearHajek (fun _=>p) (R N)) := by
    rw [T42_recenter_identity p (R N) hN]
    simpa only [sub_eq_add_neg] using
      GraphCompletion.variance_add_const (fun _ : Fin N=>p)
        (linearHajek (fun _=>p) (R N)) (-ame (fun _=>p) (R N))
  have hG (n : ℕ) : FiniteDependencyGraph (fun _=>p)
      (fun i z=>residualContrast (fun _=>p) (F (n+k)) (fun _ _=>0) i z) (B (n+k)) := by
    apply design_dependency_graph _ _ _ _ (fun _=>hp)
    · intro i
      simp only [B, ball, Finset.mem_filter, Finset.mem_univ, true_and, nodeSeparation_self]
      exact hh d hd
    · intro i j
      simp only [B, ball, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [nodeSeparation_symm (P (n+k)) i j]
    · intro i j hij
      have hlF : LocalAt (F (n+k)) (nodeSeparation (P (n+k))) (h d) :=
        T42_transform_local (R (n+k))
          (fun _ a x => x-barMu (fun _=>p) (R (n+k)) a) _ _ (htail n).2.2.1
      apply hlF i j
      simpa only [B, ball, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hij
  have hdeg : ∀ n i, (B (n+k) i).card ≤ Nat.ceil (c (h d)) := by
    intro n i
    exact_mod_cast ((htail n).2.2.2.1 i).trans (Nat.le_ceil (c (h d)))
  intro x
  apply (tendsto_add_atTop_iff_nat k).mp
  have ht := ht_clt_shift k p (2*M) v F B hp (by positivity) hv
    (fun n => (htail n).1) hF hG (Nat.ceil (c (h d))) hdeg
    (fun n => by rw [hvF (n+k) (htail n).1]; exact (htail n).2.2.2.2) x
  apply ht.congr
  intro n
  rw [hvF (n+k) (htail n).1]
  dsimp only [F]
  simp only [T42_recenter_mean p (R (n+k)) hp (htail n).1,
    sub_zero, T42_recenter_identity p (R (n+k)) (htail n).1]
  rfl

/-- The four squared errors majorize the ratio remainder on nonempty arms.
The count conditions below imply nonemptiness; no convention at an empty arm is changed. -/
lemma T42_remainder_bound {N : ℕ} (p : ℝ) (R : CircleTable N)
    (hp : 0<p ∧ p<1) (hN : 0<N) (z : Assignment N)
    (h1 : |T42_E p true z|≤1/2) (h0 : |T42_E p false z|≤1/2) :
    |hajek R z-linearHajek (fun _=>p) R z| ≤
      (T42_B p R true z)^2+(T42_B p R false z)^2+
        (T42_E p true z)^2+(T42_E p false z)^2 := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hc (a : Bool) (ha : |T42_E p a z|≤1/2) : 0<armCount z a := by
    have hl := (abs_le.mp ha).1
    change -(1/2:ℝ) ≤ armCount z a/(N*coin p a)-1 at hl
    have hd : 0<(N:ℝ)*coin p a := mul_pos hn (T42_coin_pos p hp a)
    have hfrac : 0<armCount z a/(N*coin p a) := by linarith
    exact (div_pos_iff_of_pos_right hd).mp hfrac
  have hid := hajek_ratio_identity p R z hN hp (hc true h1) (hc false h0)
  have hb1 : (∑ i, bit (z i)*(R i z-barMu (fun _=>p) R true))/(N*p) = T42_B p R true z := by
    unfold T42_B
    simp only [coin, if_true]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases hz : z i <;> simp [bit, hz]
  have hb0 : (∑ i, (1-bit (z i))*(R i z-barMu (fun _=>p) R false))/(N*(1-p)) = T42_B p R false z := by
    unfold T42_B
    simp only [coin, Bool.false_eq_true, if_false]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases hz : z i <;> simp [bit, hz]
  dsimp only at hid
  rw [hb1, hb0] at hid
  let c1 := armCount z true/(N*p)
  let c0 := armCount z false/(N*(1-p))
  have he : hajek R z-linearHajek (fun _=>p) R z =
      (T42_B p R true z/c1-T42_B p R true z) -
      (T42_B p R false z/c0-T42_B p R false z) := by
    dsimp [c1, c0]
    linarith [hid.1, hid.2]
  have hc1 : |c1-1|≤1/2 := by simpa [c1, T42_E, coin] using h1
  have hc0 : |c0-1|≤1/2 := by simpa [c0, T42_E, coin] using h0
  rw [he]
  have hr1 := T42_ratio_error (T42_B p R true z) c1 hc1
  have hr0 := T42_ratio_error (T42_B p R false z) c0 hc0
  have hab := abs_sub (T42_B p R true z/c1-T42_B p R true z)
    (T42_B p R false z/c0-T42_B p R false z)
  have he1 : c1-1=T42_E p true z := by simp [c1, T42_E, coin]
  have he0 : c0-1=T42_E p false z := by simp [c0, T42_E, coin]
  rw [he1] at hr1
  rw [he0] at hr0
  linarith

lemma T42_remainder_inProb (P : PopulationSequence Space) (p d : ℝ)
    (hp : 0 < p ∧ p < 1) (hd : 0 ≤ d) (hP : SpatialLocalConditions P)
    (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hv : Nondegenerate (fun N => variance (fun _=>p) (linearHajek (fun _=>p) (circleAverage (P N) d)))) :
    InProb (fun _ _ => p) (fun N z =>
      (hajek (circleAverage (P N) d) z-linearHajek (fun _=>p) (circleAverage (P N) d) z)/
      Real.sqrt (variance (fun _=>p) (linearHajek (fun _=>p) (circleAverage (P N) d)))) := by
  obtain ⟨M, hM, hbout⟩ := hP.1
  obtain ⟨h, hh, hloc⟩ := hP.2.1
  obtain ⟨c, hc⟩ := hP.2.2
  obtain ⟨v, hv, hvN⟩ := hv
  let R := fun N => circleAverage (P N) d
  let V := fun N => variance (fun _=>p) (linearHajek (fun _=>p) (R N))
  let B : ∀ N, Fin N → Finset (Fin N) := fun N i => ball (nodeSeparation (P N)) i (h d)
  let D := |c (h d)|+1
  let KB := D*((2*M)/p+(2*M)/(1-p))^2
  let K1 := (1-p)/p
  let K0 := p/(1-p)
  let K := 2*KB+K1+K0
  have hD : 0 < D := by dsimp [D]; positivity
  have hKB : 0 ≤ KB := by dsimp [KB]; positivity
  have hK1 : 0 < K1 := div_pos (sub_pos.mpr hp.2) hp.1
  have hK0 : 0 < K0 := div_pos hp.1 (sub_pos.mpr hp.2)
  have hK : 0 ≤ K := by dsimp [K]; linarith
  let Q := fun N (z : Assignment N) =>
    (T42_B p (R N) true z)^2+(T42_B p (R N) false z)^2+
      (T42_E p true z)^2+(T42_E p false z)^2
  have hQnonneg (N : ℕ) (z : Assignment N) : 0 ≤ Q N z := by dsimp [Q]; positivity
  have hevent : ∀ᶠ N in atTop, 0<N ∧ (∀ i z, |R N i z|≤M) ∧
      LocalAt (R N) (nodeSeparation (P N)) (h d) ∧
      (∀ i, ((B N i).card:ℝ)≤D) ∧ v≤(N:ℝ)*V N := by
    filter_upwards [eventually_gt_atTop 0, hbout, hWD, hloc d hd,
      hc (h d) (hh d hd), hvN] with N hN hbN hwdN hlN hcN hvN
    refine ⟨hN, circleAverage_abs_le (P N) d M hwdN (fun x z => (hbN x z).le), hlN, ?_, hvN⟩
    intro i
    exact (hcN i).trans ((le_abs_self (c (h d))).trans (by dsimp [D]; linarith))
  intro ε hε
  have hbound : ∀ᶠ N in atTop,
      prob (fun _ : Fin N=>p) (fun z => ε < |(hajek (R N) z-linearHajek (fun _=>p) (R N) z)/Real.sqrt (V N)|) ≤
      (4*K1+4*K0)/(N:ℝ)+(K/(ε*Real.sqrt v))*(Real.sqrt N)⁻¹ := by
    filter_upwards [hevent] with N hNall
    obtain ⟨hN, hR, hlN, hdeg, hNV⟩ := hNall
    have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
    have hV : 0<V N := by nlinarith
    have hsV : 0<Real.sqrt (V N) := Real.sqrt_pos.2 hV
    have hsN : 0<Real.sqrt N := Real.sqrt_pos.2 hn
    have hsv : 0<Real.sqrt v := Real.sqrt_pos.2 hv
    have hsymm (i j : Fin N) : j∈B N i ↔ i∈B N j := by
      simp only [B, ball, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [nodeSeparation_symm (P N) i j]
    have hout (i j : Fin N) (hij : j∉B N i) : ¬sharesSource (R N) i j := by
      apply hlN i j
      simpa only [B, ball, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hij
    have hb1 := T42_B_moment p (R N) (B N) hp hN M D hM.le hD.le hR hsymm hout hdeg true
    have hb0 := T42_B_moment p (R N) (B N) hp hN M D hM.le hD.le hR hsymm hout hdeg false
    have he1 : expect (fun _ : Fin N=>p) (fun z => (T42_E p true z)^2) = K1/N := by
      simpa [coin, K1] using T42_E_moment p hp hN true
    have he0 : expect (fun _ : Fin N=>p) (fun z => (T42_E p false z)^2) = K0/N := by
      simpa [coin, K0, sub_sub_cancel] using T42_E_moment p hp hN false
    have hQ : expect (fun _ : Fin N=>p) (Q N) ≤ K/N := by
      dsimp only [Q]
      rw [expect_add, expect_add, expect_add, he1, he0]
      change _ ≤ (2*KB+K1+K0)/N
      change _ ≤ KB/N at hb1 hb0
      linear_combination hb1 + hb0
    have hinc : ∀ z : Assignment N,
        ε < |(hajek (R N) z-linearHajek (fun _=>p) (R N) z)/Real.sqrt (V N)| →
        (1/2:ℝ)< |T42_E p true z| ∨ (1/2:ℝ)< |T42_E p false z| ∨
          ε*Real.sqrt (V N)<Q N z := by
      intro z hz
      by_cases h1 : (1/2:ℝ)< |T42_E p true z|
      · exact Or.inl h1
      by_cases h0 : (1/2:ℝ)< |T42_E p false z|
      · exact Or.inr (Or.inl h0)
      right; right
      have hr := T42_remainder_bound p (R N) hp hN z (le_of_not_gt h1) (le_of_not_gt h0)
      rw [abs_div, abs_of_pos hsV] at hz
      exact ((lt_div_iff₀ hsV).mp hz).trans_le hr
    have hprob := T34_prob_mono (fun _ : Fin N=>p) (fun _=>hp) _ _ hinc
    have hunion := T34_prob_union (fun _ : Fin N=>p) (fun _=>hp)
      (fun z => (1/2:ℝ)< |T42_E p true z|)
      (fun z => (1/2:ℝ)< |T42_E p false z| ∨ ε*Real.sqrt (V N)<Q N z)
    have hunion0 := T34_prob_union (fun _ : Fin N=>p) (fun _=>hp)
      (fun z => (1/2:ℝ)< |T42_E p false z|)
      (fun z => ε*Real.sqrt (V N)<Q N z)
    have hc1 := T34_chebyshev (fun _ : Fin N=>p) (fun _=>hp) (T42_E p true) (1/2) (by norm_num)
    have hc0 := T34_chebyshev (fun _ : Fin N=>p) (fun _=>hp) (T42_E p false) (1/2) (by norm_num)
    rw [he1] at hc1
    rw [he0] at hc0
    have hmark := T34_markov (fun _ : Fin N=>p) (fun _=>hp)
      (fun z => ε*Real.sqrt (V N)<Q N z) (Q N) (ε*Real.sqrt (V N))
      (mul_pos hε hsV) (hQnonneg N) (fun z hz => hz.le)
    have hmark' := hmark.trans (div_le_div_of_nonneg_right hQ (mul_pos hε hsV).le)
    have hsprod : Real.sqrt v ≤ Real.sqrt N*Real.sqrt (V N) := by
      have hh := Real.sqrt_le_sqrt hNV
      rwa [Real.sqrt_mul hn.le] at hh
    have hden : Real.sqrt v*Real.sqrt N ≤ (N:ℝ)*Real.sqrt (V N) := by
      calc
        _ ≤ (Real.sqrt N*Real.sqrt (V N))*Real.sqrt N :=
          mul_le_mul_of_nonneg_right hsprod hsN.le
        _ = (Real.sqrt N)^2*Real.sqrt (V N) := by ring
        _ = _ := by rw [Real.sq_sqrt hn.le]
    have hinv := one_div_le_one_div_of_le (mul_pos hsv hsN) hden
    have hterm : (K/(N:ℝ))/(ε*Real.sqrt (V N)) ≤
        (K/(ε*Real.sqrt v))*(Real.sqrt N)⁻¹ := by
      have hh := mul_le_mul_of_nonneg_left hinv (div_nonneg hK hε.le)
      convert hh using 1 <;> field_simp <;> ring
    have hcounts : (K1/(N:ℝ))/(1/2:ℝ)^2+(K0/(N:ℝ))/(1/2:ℝ)^2 =
        (4*K1+4*K0)/(N:ℝ) := by ring
    linarith
  have hlim : Tendsto (fun N : ℕ =>
      (4*K1+4*K0)/(N:ℝ)+(K/(ε*Real.sqrt v))*(Real.sqrt N)⁻¹) atTop (nhds 0) := by
    have hnlim : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_natCast_atTop_atTop.inv_tendsto_atTop
    have hslim : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (nhds 0) :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    simpa only [div_eq_mul_inv, mul_zero, zero_add] using
      (hnlim.const_mul (4*K1+4*K0)).add (hslim.const_mul (K/(ε*Real.sqrt v)))
  exact squeeze_zero' (Eventually.of_forall (fun N => T34_prob_nonneg _ (fun _=>hp) _)) hbound hlim

/-- Continuity of the Gaussian CDF follows from the absence of atoms. -/
lemma T42_normal_continuous (x : ℝ) : ContinuousAt normalCDF x := by
  let μ := ProbabilityTheory.gaussianReal 0 1
  letI : NullSingletonClass μ := ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1:NNReal)≠0)
  have hm : Monotone (ProbabilityTheory.cdf μ) := ProbabilityTheory.monotone_cdf μ
  have hc : ContinuousAt (ProbabilityTheory.cdf μ) x := by
    rw [hm.continuousAt_iff_leftLim_eq_rightLim]
    have hr : Function.rightLim (ProbabilityTheory.cdf μ) x = ProbabilityTheory.cdf μ x :=
      (hm.continuousWithinAt_Ioi_iff_rightLim_eq).1
        (((ProbabilityTheory.cdf μ).right_continuous x).mono Set.Ioi_subset_Ici_self)
    have hl : Function.leftLim (ProbabilityTheory.cdf μ) x ≤ ProbabilityTheory.cdf μ x := hm.leftLim_le le_rfl
    have hg : ProbabilityTheory.cdf μ x ≤ Function.leftLim (ProbabilityTheory.cdf μ) x := by
      have hh := (ProbabilityTheory.cdf μ).measure_singleton x
      rw [ProbabilityTheory.measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos] at hh
      exact hh
    rw [le_antisymm hl hg, hr]
  have he : normalCDF = ProbabilityTheory.cdf μ := by
    funext t
    rw [ProbabilityTheory.cdf_eq_real]
    rfl
  rw [he]
  exact hc

lemma T42_slutsky (p : ∀ N, Fin N → ℝ) (hp : ∀ N i, 0<p N i ∧ p N i<1)
    (X Y : ∀ N, Assignment N → ℝ) (hX : NormalLimit p X)
    (herror : InProb p (fun N z => Y N z-X N z)) : NormalLimit p Y := by
  intro x
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let η := (normalCDF x-a)/4
    have hη : 0<η := by dsimp [η]; linarith
    obtain ⟨δ, hδ, hc⟩ := Metric.continuousAt_iff.mp (T42_normal_continuous x) η hη
    let t := δ/2
    have ht : 0<t := by dsimp [t]; linarith
    have hclose : dist (x-t) x < δ := by rw [Real.dist_eq]; dsimp [t]; rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by linarith : 0<δ/2)]; linarith
    have hΦ := hc hclose
    rw [Real.dist_eq] at hΦ
    have hΦlo := (abs_lt.mp hΦ).1
    have hlinear := (hX (x-t)).eventually (eventually_gt_nhds (show normalCDF (x-t)-η < normalCDF (x-t) by linarith))
    have herr := (herror t ht).eventually (eventually_lt_nhds hη)
    filter_upwards [hlinear, herr] with N hlinN herrN
    have hinc : ∀ z, X N z≤x-t → Y N z≤x ∨ t< |Y N z-X N z| := by
      intro z hz
      by_cases hy : Y N z≤x
      · exact Or.inl hy
      · right
        have hy' : x<Y N z := lt_of_not_ge hy
        exact lt_of_lt_of_le (by linarith) (le_abs_self _)
    have hm := T34_prob_mono (p N) (hp N) _ _ hinc
    have hu := T34_prob_union (p N) (hp N) (fun z => Y N z≤x) (fun z => t< |Y N z-X N z|)
    dsimp [η] at hΦlo hlinN herrN
    linarith
  · intro b hb
    let η := (b-normalCDF x)/4
    have hη : 0<η := by dsimp [η]; linarith
    obtain ⟨δ, hδ, hc⟩ := Metric.continuousAt_iff.mp (T42_normal_continuous x) η hη
    let t := δ/2
    have ht : 0<t := by dsimp [t]; linarith
    have hclose : dist (x+t) x < δ := by rw [Real.dist_eq, add_sub_cancel_left]; dsimp [t]; rw [abs_of_pos (by linarith : 0<δ/2)]; linarith
    have hΦ := hc hclose
    rw [Real.dist_eq] at hΦ
    have hΦhi := (abs_lt.mp hΦ).2
    have hlinear := (hX (x+t)).eventually (eventually_lt_nhds (show normalCDF (x+t)<normalCDF (x+t)+η by linarith))
    have herr := (herror t ht).eventually (eventually_lt_nhds hη)
    filter_upwards [hlinear, herr] with N hlinN herrN
    have hinc : ∀ z, Y N z≤x → X N z≤x+t ∨ t< |Y N z-X N z| := by
      intro z hz
      by_cases hx : X N z≤x+t
      · exact Or.inl hx
      · right
        have hx' : x+t<X N z := lt_of_not_ge hx
        exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
    have hm := T34_prob_mono (p N) (hp N) _ _ hinc
    have hu := T34_prob_union (p N) (hp N) (fun z => X N z≤x+t) (fun z => t< |Y N z-X N z|)
    dsimp [η] at hΦhi hlinN herrN
    linarith

theorem hajek_central_limit_proof (P : PopulationSequence Space) (p d : ℝ)
    (hp : 0 < p ∧ p < 1) (hd : 0 ≤ d) (hP : SpatialLocalConditions P)
    (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hv : Nondegenerate (fun N => variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d)))) :
    NormalLimit (fun _ _ => p) (fun N z =>
      (hajek (circleAverage (P N) d) z-ame (fun _ => p) (circleAverage (P N) d)) /
        Real.sqrt (variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d)))) := by
  have hlin := T42_linear_clt P p d hp hd hP hWD hv
  have hrem := T42_remainder_inProb P p d hp hd hP hWD hv
  apply T42_slutsky (fun _ _=>p) (fun _ _=>hp) _ _ hlin
  convert hrem using 1
  funext N z
  ring

end
end AronowAudit.P004.Wave1
