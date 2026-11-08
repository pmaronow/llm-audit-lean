import SAP.P031.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Finset Filter
open SAP.P031 SAP.P031.WH.W3

noncomputable section
namespace SAP.P031.WH.W3.GateAudit

theorem first_leaf : T6_L1 := by
  intro N M v C hM hMN hC hF
  have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast (hM.trans hMN)
  have hmn : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hm0 : (0 : ℝ) < M := by linarith
  have hn0 : (0 : ℝ) < N := by linarith
  have hn1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hPowSum : (∑ i, (v i ^ 2) ^ 2) = ∑ i, v i ^ 4 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  let nu := groupMean univ (fun i => v i ^ 2)
  have hCS2 : (∑ i, v i ^ 2) ^ 2 ≤ (N : ℝ) * ∑ i, v i ^ 4 := by
    have h : (∑ i, v i ^ 2) ^ 2 ≤ (N : ℝ) * ∑ i, (v i ^ 2) ^ 2 := by
      simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ : Fin N => (1 : ℝ))
        (fun i => v i ^ 2))
    rw [hPowSum] at h
    exact h
  have hNuSq : nu ^ 2 ≤ fourthMomentW3 v := by
    dsimp only [nu, groupMean, fourthMomentW3]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [div_pow]
    calc
      _ ≤ ((N : ℝ) * ∑ i, v i ^ 4) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hCS2 (sq_nonneg _)
      _ = _ := by field_simp [hn0.ne']
  have hNu : nu ≤ Real.sqrt C := Real.le_sqrt_of_sq_le (hNuSq.trans hF)
  have hCS1 : (∑ i, v i) ^ 2 ≤ (N : ℝ) * ∑ i, v i ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ : Fin N => (1 : ℝ)) v)
  have hMeanNu : (groupMean univ v) ^ 2 ≤ nu := by
    dsimp only [nu, groupMean]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [div_pow]
    calc
      _ ≤ ((N : ℝ) * ∑ i, v i ^ 2) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hCS1 (sq_nonneg _)
      _ = _ := by field_simp [hn0.ne']
  have hRaw : popVariance v = nu - (groupMean univ v) ^ 2 := by
    simpa [nu, popVariance, AronowAudit.P031.popVariance,
      groupMean, AronowAudit.P031.groupMean] using
      (AronowAudit.P031.pop_variance_raw v (by simpa using hn0.ne'))
  have hVar : popVariance v ≤ Real.sqrt C := by
    rw [hRaw]
    linarith [sq_nonneg (groupMean univ v)]
  have hRaw2 : popVariance (fun i => v i ^ 2) = fourthMomentW3 v - nu ^ 2 := by
    have h : popVariance (fun i => v i ^ 2) =
        (∑ i, (v i ^ 2) ^ 2) / (N : ℝ) - nu ^ 2 := by
      simpa [nu, popVariance, AronowAudit.P031.popVariance,
        groupMean, AronowAudit.P031.groupMean] using
      (AronowAudit.P031.pop_variance_raw (fun i => v i ^ 2)
        (by simpa using hn0.ne'))
    rw [hPowSum] at h
    simpa only [fourthMomentW3, groupMean, Finset.card_univ, Fintype.card_fin] using h
  have hVar2 : popVariance (fun i => v i ^ 2) ≤ C := by
    rw [hRaw2]
    linarith [sq_nonneg nu]
  let f : ℝ := ((N : ℝ) - M) / ((M : ℝ) * ((N : ℝ) - 1))
  have hf0 : 0 ≤ f := div_nonneg (by linarith) (by positivity)
  have hf : f ≤ 1 / (M : ℝ) := by
    apply (div_le_iff₀ (mul_pos hm0 hn1)).mpr
    have he : 1 / (M : ℝ) * ((M : ℝ) * ((N : ℝ) - 1)) = (N : ℝ) - 1 := by
      field_simp [hm0.ne']
    rw [he]
    linarith
  have hSample : ∀ w : Fin N → ℝ,
      expectation M (fun s => (groupMean s w - groupMean univ w) ^ 2) = f * popVariance w := by
    intro w
    simpa [f, expectation, AronowAudit.P031.expectation,
      groupMean, AronowAudit.P031.groupMean,
      popVariance, AronowAudit.P031.popVariance] using
      (AronowAudit.P031.sample_mean_squared_error M hM (by simpa using hMN) w)
  refine ⟨?_, ?_, hMeanNu.trans hNu, hVar⟩
  · rw [hSample]
    calc
      f * popVariance v ≤ f * Real.sqrt C := mul_le_mul_of_nonneg_left hVar hf0
      _ ≤ (1 / (M : ℝ)) * Real.sqrt C :=
        mul_le_mul_of_nonneg_right hf (Real.sqrt_nonneg C)
      _ = _ := by ring
  · rw [hSample]
    calc
      f * popVariance (fun i => v i ^ 2) ≤ f * C :=
        mul_le_mul_of_nonneg_left hVar2 hf0
      _ ≤ (1 / (M : ℝ)) * C := mul_le_mul_of_nonneg_right hf hC
      _ = _ := by ring

#print axioms first_leaf

theorem second_leaf : T6_L2 := by
  intro h1 N M v C hM hMN hC hF
  obtain ⟨hE1, hE2, hMean, hVar⟩ := h1 N M v C hM hMN hC hF
  let m : ℝ := M
  let b := Real.sqrt C
  let t := Real.sqrt (C / m)
  let mu := groupMean univ v
  let nu := groupMean univ (fun i => v i ^ 2)
  let d := fun s => groupMean s v - mu
  let e := fun s => groupMean s (fun i => v i ^ 2) - nu
  let r := m / (m - 1)
  have hm : (2 : ℝ) ≤ m := by change (2 : ℝ) ≤ M; exact_mod_cast hM
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb : 0 ≤ b := Real.sqrt_nonneg C
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hbsq : b ^ 2 = C := Real.sq_sqrt hC
  have hM0 : (M : ℝ) ≠ 0 := hm0.ne'
  have hM1 : (M : ℝ) - 1 ≠ 0 := hm1.ne'
  have hr0 : 0 ≤ r := div_nonneg hm0.le hm1.le
  have hr2 : r ≤ 2 := (div_le_iff₀ hm1).mpr (by linarith)
  have hV0 : 0 ≤ popVariance v := by
    unfold popVariance
    positivity
  have hRaw : popVariance v = nu - mu ^ 2 := by
    simpa [nu, mu, popVariance, AronowAudit.P031.popVariance,
      groupMean, AronowAudit.P031.groupMean] using
      (AronowAudit.P031.pop_variance_raw v (by simpa using hn0.ne'))
  have hAbsSqrt : ∀ f : Finset (Fin N) → ℝ,
      expectation M (fun s => |f s|) ≤ Real.sqrt (expectation M (fun s => f s ^ 2)) := by
    intro f
    simpa only [expectation, AronowAudit.P031.expectation] using
      (AronowAudit.P031.Wave1.FootnoteThreeProbability.n2_proof N M f hMN)
  have hD : expectation M (fun s => d s ^ 2) ≤ b / m := hE1
  have hE : expectation M (fun s => e s ^ 2) ≤ C / m := hE2
  have hAbsD : expectation M (fun s => |d s|) ≤ Real.sqrt (b / m) :=
    (hAbsSqrt d).trans (Real.sqrt_le_sqrt hD)
  have hAbsE : expectation M (fun s => |e s|) ≤ t :=
    (hAbsSqrt e).trans (Real.sqrt_le_sqrt hE)
  have hProd : |mu| * expectation M (fun s => |d s|) ≤ t := by
    apply (mul_le_mul_of_nonneg_left hAbsD (abs_nonneg mu)).trans
    apply Real.le_sqrt_of_sq_le
    calc
      (|mu| * Real.sqrt (b / m)) ^ 2 = mu ^ 2 * (b / m) := by
        rw [mul_pow, sq_abs, Real.sq_sqrt (div_nonneg hb hm0.le)]
      _ ≤ b * (b / m) := mul_le_mul_of_nonneg_right hMean (div_nonneg hb hm0.le)
      _ = C / m := by rw [← mul_div_assoc, ← sq, hbsq]
  have hPoint : ∀ s ∈ (univ : Finset (Fin N)).powersetCard M,
      |sampleVariance s v - popVariance v| ≤
        2 * |e s| + 2 * d s ^ 2 + 4 * |mu| * |d s| + popVariance v / (m - 1) := by
    intro s hs
    have hc : s.card = M := (Finset.mem_powersetCard.mp hs).2
    have hSampleRaw : sampleVariance s v =
        r * (groupMean s (fun i => v i ^ 2) - (groupMean s v) ^ 2) := by
      unfold sampleVariance
      have hsse := AronowAudit.P031.group_sse_raw s v (by simpa [hc] using hM0)
      have hsse' : (∑ i ∈ s, (v i - groupMean s v) ^ 2) =
          (∑ i ∈ s, v i ^ 2) - (∑ i ∈ s, v i) ^ 2 / s.card := by
        simpa only [groupMean, AronowAudit.P031.groupMean] using hsse
      rw [hsse']
      dsimp only [r, m, groupMean]
      rw [hc]
      field_simp [hM0, hM1]
      <;> ring
    have hIdentity : sampleVariance s v - popVariance v =
        r * (e s - ((groupMean s v) ^ 2 - mu ^ 2)) + popVariance v / (m - 1) := by
      rw [hSampleRaw, hRaw]
      dsimp only [r, e]
      field_simp [hm1.ne']
      <;> ring
    have hSquareError : |(groupMean s v) ^ 2 - mu ^ 2| ≤ d s ^ 2 + 2 * |mu| * |d s| := by
      have heq : (groupMean s v) ^ 2 - mu ^ 2 = d s ^ 2 + 2 * mu * d s := by
        dsimp only [d]
        ring
      rw [heq]
      calc
        _ ≤ |d s ^ 2| + |2 * mu * d s| := abs_add_le _ _
        _ = _ := by rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_mul]; norm_num
    rw [hIdentity]
    calc
      _ ≤ |r * (e s - ((groupMean s v) ^ 2 - mu ^ 2))| +
          |popVariance v / (m - 1)| := abs_add_le _ _
      _ = r * |e s - ((groupMean s v) ^ 2 - mu ^ 2)| +
          popVariance v / (m - 1) := by
        rw [abs_mul, abs_of_nonneg hr0, abs_of_nonneg (div_nonneg hV0 hm1.le)]
      _ ≤ r * (|e s| + d s ^ 2 + 2 * |mu| * |d s|) +
          popVariance v / (m - 1) := by
        gcongr
        exact (abs_sub _ _).trans (by linarith [hSquareError])
      _ ≤ 2 * (|e s| + d s ^ 2 + 2 * |mu| * |d s|) +
          popVariance v / (m - 1) := by
        nlinarith [mul_le_mul_of_nonneg_right hr2
          (show 0 ≤ |e s| + d s ^ 2 + 2 * |mu| * |d s| by positivity)]
      _ = _ := by ring
  have hEPoint := AronowAudit.P031.expectation_mono M hPoint
  simp only [AronowAudit.P031.expectation_add, AronowAudit.P031.expectation_mul,
    AronowAudit.P031.expectation_const (ι := Fin N) M (by simpa using hMN)] at hEPoint
  have hEBound : expectation M (fun s => |sampleVariance s v - popVariance v|) ≤
      2 * expectation M (fun s => |e s|) + 2 * expectation M (fun s => d s ^ 2) +
        4 * |mu| * expectation M (fun s => |d s|) + popVariance v / (m - 1) := by
    simpa only [expectation, AronowAudit.P031.expectation] using hEPoint
  have hSmall : b / m ≤ t := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, hbsq]
    apply (div_le_div_iff₀ (sq_pos_of_pos hm0) hm0).mpr
    have hMM : 0 ≤ m ^ 2 - m := by nlinarith
    nlinarith [mul_nonneg hC hMM]
  have hRemainder : b / (m - 1) ≤ 2 * t := by
    calc
      b / (m - 1) = r * (b / m) := by dsimp only [r]; field_simp [hm0.ne', hm1.ne']
      _ ≤ 2 * (b / m) := mul_le_mul_of_nonneg_right hr2 (div_nonneg hb hm0.le)
      _ ≤ 2 * t := mul_le_mul_of_nonneg_left hSmall (by norm_num)
  have hVarBound : popVariance v / (m - 1) ≤ 2 * t :=
    (div_le_div_of_nonneg_right hVar hm1.le).trans hRemainder
  change expectation M (fun s => |sampleVariance s v - popVariance v|) ≤ 16 * t
  nlinarith [hEBound, hAbsE, hD, hProd, hSmall, hVarBound]

#print axioms second_leaf

example : T6CitedRegimeStatement := T6_assembly first_leaf second_leaf

end SAP.P031.WH.W3.GateAudit
