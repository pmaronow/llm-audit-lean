import AronowAudit.P004.Wave1.NedHeadlineBlueprint
import AronowAudit.P004.Wave1.NedHeadline.LOCERR
import AronowAudit.P004.Wave1.NedHeadline.PROJCLT
import AronowAudit.P004.Wave1.FiniteConditioning.FC3
import AronowAudit.P004.Wave1.FiniteConditioning.FC7
import AronowAudit.P004.Wave1.DesignLimits.DL6
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Removal of fixed-radius localization.

The finite-design helper below contains the variance reverse triangle argument and
the comparison of the two *separately variance-standardized* sums.  The radii in
the final proof are all beyond a single deterministic threshold; the sample-size
threshold in each application remains free to depend on its fixed radius.
-/

universe u

namespace AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

/-- A finite-design reverse triangle argument, with the normalization error made explicit.
Here `n` is the sample size viewed as a positive real number. -/
private theorem localization_standardization {N : ℕ} (p : Fin N → ℝ)
    (hp : FiniteConditioning.Admissible p) (U V : Assignment N → ℝ)
    (n v E : ℝ) (hn : 0 < n) (hv : 0 < v) (hE : 0 ≤ E) (hEsmall : E ≤ v / 4)
    (hUmean : expect p U = 0) (hVmean : expect p V = 0)
    (hfloor : v * n ≤ variance p U)
    (herror : expect p (fun z => (U z - V z)^2) ≤ n * E) :
    v / 4 * n ≤ variance p V ∧
      l2Norm p (fun z => U z / Real.sqrt (variance p U) -
        V z / Real.sqrt (variance p V)) ≤ 2 * Real.sqrt (E / v) := by
  classical
  obtain ⟨hnonneg, hadd, hsub, hsum, hscale, hsup, hmono, hCS, hcov, hvar⟩ :=
    FiniteConditioning.fc7_proof p hp
  let σ : ℝ := l2Norm p U
  let τ : ℝ := l2Norm p V
  let δ : ℝ := l2Norm p (fun z => U z - V z)
  let η : ℝ := Real.sqrt (E / v)
  have hσ0 : 0 ≤ σ := hnonneg U
  have hτ0 : 0 ≤ τ := hnonneg V
  have hδ0 : 0 ≤ δ := hnonneg _
  have hη0 : 0 ≤ η := Real.sqrt_nonneg _
  have hUvar : variance p U = σ^2 := hvar U hUmean
  have hVvar : variance p V = τ^2 := hvar V hVmean
  have hσfloor : v * n ≤ σ^2 := hfloor.trans_eq hUvar
  have hσpos : 0 < σ := by nlinarith [mul_pos hv hn]
  have hmoment0 : 0 ≤ expect p (fun z => (U z - V z)^2) := by
    have hh := expect_mono p hp (fun _ => 0) (fun z => (U z - V z)^2)
      (fun z => sq_nonneg _)
    simpa only [expect_const] using hh
  have hδsq : δ^2 ≤ n * E := by
    have hh : δ^2 = expect p (fun z => (U z - V z)^2) := Real.sq_sqrt hmoment0
    exact hh.trans_le herror
  have hfrac0 : 0 ≤ E / v := div_nonneg hE hv.le
  have hηsq : η^2 = E / v := Real.sq_sqrt hfrac0
  have hηhalf : η ≤ 1 / 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, (div_le_iff₀ hv).mpr ?_⟩
    nlinarith
  have hrelative : δ ≤ η * σ := by
    apply (sq_le_sq₀ hδ0 (mul_nonneg hη0 hσ0)).mp
    calc
      δ^2 ≤ n * E := hδsq
      _ = (E / v) * (v * n) := by field_simp [hv.ne'] <;> ring
      _ ≤ (E / v) * σ^2 := mul_le_mul_of_nonneg_left hσfloor hfrac0
      _ = (η * σ)^2 := by rw [mul_pow, hηsq]
  have hδhalf : δ ≤ σ / 2 := by
    calc
      δ ≤ η * σ := hrelative
      _ ≤ (1 / 2) * σ := mul_le_mul_of_nonneg_right hηhalf hσ0
      _ = σ / 2 := by ring

  have hσtri : σ ≤ δ + τ := by
    calc
      σ = l2Norm p (fun z => (U z - V z) + V z) := by
        change l2Norm p U = _
        congr 1
        funext z
        ring
      _ ≤ δ + τ := hadd _ _
  have hcomm : l2Norm p (fun z => V z - U z) = δ := by
    apply le_antisymm
    · exact hmono _ _ (fun z => (abs_sub_comm (V z) (U z)).le)
    · exact hmono _ _ (fun z => (abs_sub_comm (U z) (V z)).le)
  have hτtri : τ ≤ δ + σ := by
    calc
      τ = l2Norm p (fun z => (V z - U z) + U z) := by
        change l2Norm p V = _
        congr 1
        funext z
        ring
      _ ≤ l2Norm p (fun z => V z - U z) + σ := hadd _ _
      _ = δ + σ := by rw [hcomm]
  have hreverse : |τ - σ| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
  have hτhalf : σ / 2 ≤ τ := by linarith
  have hτpos : 0 < τ := lt_of_lt_of_le (half_pos hσpos) hτhalf
  have hprojectedFloor : v / 4 * n ≤ variance p V := by
    rw [hVvar]
    have hsq : (σ / 2)^2 ≤ τ^2 :=
      (sq_le_sq₀ (by positivity) hτ0).mpr hτhalf
    nlinarith
  have hsqrtU : Real.sqrt (variance p U) = σ := by rw [hUvar, Real.sqrt_sq hσ0]
  have hsqrtV : Real.sqrt (variance p V) = τ := by rw [hVvar, Real.sqrt_sq hτ0]
  have hnormalized : l2Norm p (fun z => U z / σ - V z / τ) ≤ 2 * η := by
    have hsplit : (fun z => U z / σ - V z / τ) = fun z =>
        (1 / σ) * (U z - V z) + ((τ - σ) / (σ * τ)) * V z := by
      funext z
      field_simp [hσpos.ne', hτpos.ne'] <;> ring
    have hscalar : |1 / σ| * δ + |(τ - σ) / (σ * τ)| * τ =
        δ / σ + |τ - σ| / σ := by
      rw [abs_of_pos (one_div_pos.mpr hσpos), abs_div, abs_mul,
        abs_of_pos hσpos, abs_of_pos hτpos]
      field_simp [hσpos.ne', hτpos.ne'] <;> ring
    have hδdiv : δ / σ ≤ η := (div_le_iff₀ hσpos).mpr hrelative
    calc
      l2Norm p (fun z => U z / σ - V z / τ) =
          l2Norm p (fun z => (1 / σ) * (U z - V z) + ((τ - σ) / (σ * τ)) * V z) :=
        congrArg (l2Norm p) hsplit
      _ ≤ l2Norm p (fun z => (1 / σ) * (U z - V z)) +
          l2Norm p (fun z => ((τ - σ) / (σ * τ)) * V z) := hadd _ _
      _ = |1 / σ| * δ + |(τ - σ) / (σ * τ)| * τ := by
        rw [hscale, hscale]
      _ = δ / σ + |τ - σ| / σ := hscalar
      _ ≤ δ / σ + δ / σ := add_le_add le_rfl
        (div_le_div_of_nonneg_right hreverse hσpos.le)
      _ ≤ 2 * η := by linarith
  refine ⟨hprojectedFloor, ?_⟩
  rw [hsqrtU, hsqrtV]
  exact hnormalized

/-- Generic spacing-graph NED CLT, via fixed-radius dependency-graph approximations. -/
theorem locclt_proof : LOCCLT := by
  classical
  unfold LOCCLT
  intro p hp X D ψ Kc Cb A e M v hD hspacing hCb hψ hψanti he hA henv hKc
    hNED hbound hmean hv hvar
  let C : ℝ := Cb * Kc^2 * A^2 * (10 + 74 / (1 - (2 : ℝ) ^ (2 - e)))
  let E : ℝ → ℝ := fun t => C * t ^ (2 - 2 * e)
  have hden : 0 < 1 - (2 : ℝ) ^ (2 - e) := by
    apply sub_pos.mpr
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hE0 (t : ℝ) (ht : 0 ≤ t) : 0 ≤ E t :=
    mul_nonneg hC (Real.rpow_nonneg ht _)
  have hpowerLimit : Tendsto (fun t : ℝ => t ^ (2 - 2 * e)) atTop (nhds 0) := by
    have hexp : 2 - 2 * e = -(2 * e - 2) := by ring
    rw [hexp]
    exact tendsto_rpow_neg_atTop (by linarith)
  have hELimit : Tendsto E atTop (nhds 0) := by
    simpa only [E, mul_zero] using
      (tendsto_const_nhds.mul hpowerLimit :
        Tendsto (fun t : ℝ => C * t ^ (2 - 2 * e)) atTop (nhds (C * 0)))
  have hsmallEventually : ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ E t < v / 4 :=
    (eventually_ge_atTop 1).and ((tendsto_order.1 hELimit).2 (v / 4) (by positivity))
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.1 hsmallEventually
  have hr₀1 : 1 ≤ r₀ := (hr₀ r₀ le_rfl).1
  let ρ : ℕ → ℝ := fun r => r₀ + r
  have hρge (r : ℕ) : r₀ ≤ ρ r := by
    dsimp only [ρ]
    exact le_add_of_nonneg_right (Nat.cast_nonneg r)
  have hρ1 (r : ℕ) : 1 ≤ ρ r := (hr₀ (ρ r) (hρge r)).1
  have hEsmall (r : ℕ) : E (ρ r) ≤ v / 4 := (hr₀ (ρ r) (hρge r)).2.le
  have hρLimit : Tendsto ρ atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop :
      Tendsto (fun r : ℕ => (r : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop (b - r₀))] with r hr
    dsimp only [ρ]
    linarith
  let η : ℕ → ℝ := fun r => 2 * Real.sqrt (E (ρ r) / v)
  have hηLimit : Tendsto η atTop (nhds 0) := by
    have hh : Tendsto (fun r => E (ρ r) / v) atTop (nhds 0) := by
      simpa only [zero_div, Function.comp_apply] using (hELimit.comp hρLimit).div_const v
    simpa only [η, Real.sqrt_zero, mul_zero] using
      (tendsto_const_nhds.mul hh.sqrt :
        Tendsto (fun r => 2 * Real.sqrt (E (ρ r) / v)) atTop (nhds (2 * Real.sqrt 0)))

  let S : ∀ N, Assignment N → ℝ := fun N z => ∑ i, X N i z
  let Sr : ℕ → ∀ N, Assignment N → ℝ := fun r N z =>
    ∑ i, conditionOn (fun _ => p) (ball (D N) i (ρ r)) (X N i) z
  have hSmean (N : ℕ) : expect (fun _ => p) (S N) = 0 := by
    rw [expect_sum]
    exact Finset.sum_eq_zero (fun i _ => hmean N i)
  have hSrmean (r N : ℕ) : expect (fun _ => p) (Sr r N) = 0 := by
    rw [expect_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [FiniteConditioning.fc3_proof (fun _ => p) (fun _ => hp)]
    exact hmean N i
  have hfamily : ∀ᶠ N in atTop, LocalFamily p (X N) (D N) ψ Kc Cb A e := by
    filter_upwards [hspacing] with N hspace
    exact ⟨hp, hD N, hspace, hCb, hψ, hψanti, he, hA, henv, hKc, hNED N⟩
  have herror (r : ℕ) : ∀ᶠ N in atTop,
      expect (fun _ => p) (fun z => (S N z - Sr r N z)^2) ≤ N * E (ρ r) := by
    filter_upwards [hfamily] with N hF
    have hh := locerr_proof p (X N) (D N) ψ Kc Cb A e (ρ r) hF (hρ1 r)
    simpa only [S, Sr, Finset.sum_sub_distrib, E, C] using hh

  have hcomparison (r : ℕ) : ∀ᶠ N in atTop,
      v / 4 * N ≤ variance (fun _ => p) (Sr r N) ∧
        l2Norm (fun _ => p) (fun z => S N z /
            Real.sqrt (variance (fun _ => p) (S N)) -
          Sr r N z / Real.sqrt (variance (fun _ => p) (Sr r N))) ≤ η r := by
    filter_upwards [hvar, herror r, eventually_gt_atTop 0] with N hvN herr hN
    exact localization_standardization (fun _ => p) (fun _ => hp) (S N) (Sr r N)
      (N : ℝ) v (E (ρ r)) (by exact_mod_cast hN) hv
      (hE0 (ρ r) (le_trans zero_le_one (hρ1 r))) (hEsmall r)
      (hSmean N) (hSrmean r N) hvN herr

  let T : ∀ N, Assignment N → ℝ := fun N z =>
    S N z / Real.sqrt (variance (fun _ => p) (S N))
  let Tr : ℕ → ∀ N, Assignment N → ℝ := fun r N z =>
    Sr r N z / Real.sqrt (variance (fun _ => p) (Sr r N))
  have hprojectedCLT (r : ℕ) : NormalLimit (fun _ _ => p) (Tr r) := by
    apply projclt_proof p hp X D (ρ r) (Cb * (1 + (2 * ρ r)^2)) M (v / 4)
      hD (le_trans zero_le_one (hρ1 r))
    · filter_upwards [hspacing] with N hspace i
      exact hspace i (2 * ρ r) (by linarith [hρ1 r])
    · exact hbound
    · exact hmean
    · positivity
    · exact (hcomparison r).mono (fun _ h => h.1)
  have hlimit := DesignLimits.dl6_proof (fun _ _ => p) (fun _ _ => hp) T Tr η
    hηLimit hprojectedCLT (fun r => (hcomparison r).mono (fun _ h => h.2))
  exact hlimit

end
end AronowAudit.P004.Wave1.NedHeadline
