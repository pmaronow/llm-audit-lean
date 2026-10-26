import AronowAudit.P004.Wave1.NedFarCovarianceBlueprint
import AronowAudit.P004.Wave1.NedFarCovariance.E2

/-! E3: the two larger balls are disjoint, so the covariance of their projected rows is zero.
Expand the original covariance into two errors and apply finite L² Cauchy--Schwarz. -/

namespace AronowAudit.P004.Wave1.NedFarCovariance

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem e3_proof : E3 := by
  classical
  intro N p R D K ψ B M G L b μ1 μ0 hs hμ1 hμ0 i j hij
  let T : ℝ := D i j / 3
  let A : ℝ := (B + M) / min p (1 - p)
  let H : ℝ := |G| / min p (1 - p)
  let mi : ℝ := ((ball D i b).card : ℝ)
  let mj : ℝ := ((ball D j b).card : ℝ)
  let Si : ℝ := ∑ k ∈ ball D i b, ψ (T - D i k)
  let Sj : ℝ := ∑ k ∈ ball D j b, ψ (T - D j k)
  let U : Assignment N → ℝ := nedVRow p R D K b μ1 μ0 i
  let V : Assignment N → ℝ := nedVRow p R D K b μ1 μ0 j
  let U' : Assignment N → ℝ := projRow p R D K b μ1 μ0 (ball D i T) i
  let V' : Assignment N → ℝ := projRow p R D K b μ1 μ0 (ball D j T) j
  have hp : FiniteConditioning.Admissible (fun _ : Fin N => p) := fun _ => hs.hp
  have hq : 0 < min p (1 - p) := lt_min hs.hp.1 (sub_pos.mpr hs.hp.2)
  have hN : (0 : ℝ) < N := by exact_mod_cast hs.hN
  have hA : 0 ≤ A := div_nonneg (add_nonneg hs.hB0 hs.hM) hq.le
  have hH : 0 ≤ H := div_nonneg (abs_nonneg _) hq.le
  have hL : 0 ≤ L := le_trans (abs_nonneg (K 0)) (hs.hK 0 le_rfl)
  have hmi : 0 ≤ mi := Nat.cast_nonneg _
  have hmj : 0 ≤ mj := Nat.cast_nonneg _
  have hbT : b < T := by dsimp only [T]; linarith
  have hgap : 2 * T < D i j := by dsimp only [T]; linarith [hs.hb]
  have hSi : 0 ≤ Si := by
    apply Finset.sum_nonneg
    intro k hk
    apply hs.hψ
    have hki : D i k ≤ b := by
      simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and] using hk
    linarith
  have hSj : 0 ≤ Sj := by
    apply Finset.sum_nonneg
    intro k hk
    apply hs.hψ
    have hkj : D j k ≤ b := by
      simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and] using hk
    linarith
  rcases e2_proof p R D K ψ B M G L b μ1 μ0 i T hs hμ1 hμ0 hbT with
    ⟨hEi, _hU, hU', hdepI⟩
  rcases e2_proof p R D K ψ B M G L b μ1 μ0 j T hs hμ1 hμ0 hbT with
    ⟨hEj, hV, _hV', hdepJ⟩
  change l2Norm (fun _ => p) (fun z => U z - U' z) ≤
    2 * L * A * H * Si / (N : ℝ)^2 at hEi
  change l2Norm (fun _ => p) (fun z => V z - V' z) ≤
    2 * L * A * H * Sj / (N : ℝ)^2 at hEj
  rcases FiniteConditioning.fc7_proof (fun _ : Fin N => p) hp with
    ⟨hnonneg, _hadd, _hsub, _hsum, _hscale, hsup, _hmono, _hexpect, hcov, _hvar⟩
  have hVnorm : l2Norm (fun _ => p) V ≤ L * A^2 * mj / (N : ℝ)^2 :=
    hsup V _ hV
  have hU'norm : l2Norm (fun _ => p) U' ≤ L * A^2 * mi / (N : ℝ)^2 :=
    hsup U' _ hU'

  -- A common coordinate would force D i j ≤ 2T, contradicting the choice T=D i j/3.
  have hdisj : Disjoint (↑(ball D i T) : Set (Fin N)) (↑(ball D j T) : Set (Fin N)) := by
    apply Set.disjoint_left.mpr
    intro k hki hkj
    have hi : D i k ≤ T := by
      simpa only [Finset.mem_coe, ball, Finset.mem_filter, Finset.mem_univ, true_and] using hki
    have hj : D j k ≤ T := by
      simpa only [Finset.mem_coe, ball, Finset.mem_filter, Finset.mem_univ, true_and] using hkj
    have htri := hs.hDtri i k j
    rw [hs.hDsymm k j] at htri
    linarith
  have hV'compl : DependsOn V' ((↑(ball D i T) : Set (Fin N))ᶜ) := by
    intro z z' hzz'
    apply hdepJ
    intro k hk
    exact hzz' k (fun hki => (Set.disjoint_left.mp hdisj) hki hk)
  have hzero : cov (fun _ => p) U' V' = 0 := by
    unfold cov
    rw [GraphCompletion.expect_mul_of_disjoint_depends (fun _ : Fin N => p)
      (↑(ball D i T) : Set (Fin N)) U' V' hdepI hV'compl]
    ring

  -- These are identities for the finite design expectation; no expectation-preservation
  -- property of the projection is needed in this covariance expansion.
  have hleft : cov (fun _ => p) (fun z => U z - U' z) V =
      cov (fun _ => p) U V - cov (fun _ => p) U' V := by
    simp only [cov, sub_mul, expect_sub]
    ring
  have hright : cov (fun _ => p) U' (fun z => V z - V' z) =
      cov (fun _ => p) U' V - cov (fun _ => p) U' V' := by
    simp only [cov, mul_sub, expect_sub]
    ring
  have hdecomp : cov (fun _ => p) U V =
      cov (fun _ => p) (fun z => U z - U' z) V +
      cov (fun _ => p) U' (fun z => V z - V' z) := by
    linarith
  have hfirst : |cov (fun _ => p) (fun z => U z - U' z) V| ≤
      (2 * L * A * H * Si / (N : ℝ)^2) * (L * A^2 * mj / (N : ℝ)^2) := by
    calc
      |cov (fun _ => p) (fun z => U z - U' z) V|
          ≤ l2Norm (fun _ => p) (fun z => U z - U' z) * l2Norm (fun _ => p) V :=
        hcov _ _
      _ ≤ _ := mul_le_mul hEi hVnorm (hnonneg V) (by positivity)
  have hsecond : |cov (fun _ => p) U' (fun z => V z - V' z)| ≤
      (L * A^2 * mi / (N : ℝ)^2) * (2 * L * A * H * Sj / (N : ℝ)^2) := by
    calc
      |cov (fun _ => p) U' (fun z => V z - V' z)|
          ≤ l2Norm (fun _ => p) U' * l2Norm (fun _ => p) (fun z => V z - V' z) :=
        hcov _ _
      _ ≤ _ := mul_le_mul hU'norm hEj (hnonneg _) (le_trans (hnonneg U') hU'norm)
  change |cov (fun _ => p) U V| ≤
    2 * L^2 * A^3 * H * (mj * Si + mi * Sj) / (N : ℝ)^4
  calc
    |cov (fun _ => p) U V| =
        |cov (fun _ => p) (fun z => U z - U' z) V +
          cov (fun _ => p) U' (fun z => V z - V' z)| := congrArg abs hdecomp
    _ ≤ |cov (fun _ => p) (fun z => U z - U' z) V| +
        |cov (fun _ => p) U' (fun z => V z - V' z)| := abs_add_le _ _
    _ ≤ (2 * L * A * H * Si / (N : ℝ)^2) * (L * A^2 * mj / (N : ℝ)^2) +
        (L * A^2 * mi / (N : ℝ)^2) * (2 * L * A * H * Sj / (N : ℝ)^2) :=
      add_le_add hfirst hsecond
    _ = 2 * L^2 * A^3 * H * (mj * Si + mi * Sj) / (N : ℝ)^4 := by ring

end
end AronowAudit.P004.Wave1.NedFarCovariance
