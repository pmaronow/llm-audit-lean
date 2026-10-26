import AronowAudit.P004.Wave1.NedFarCovarianceBlueprint
import AronowAudit.P004.Wave1.NedFarCovariance.E1
import AronowAudit.P004.Wave1.FiniteConditioning.FC1
import AronowAudit.P004.Wave1.FiniteConditioning.FC5
import AronowAudit.P004.Wave1.FiniteConditioning.FC6
import AronowAudit.P004.Wave1.FiniteConditioning.FC7

/-! E2: project every factor of one row onto the same larger ball. -/

namespace AronowAudit.P004.Wave1.NedFarCovariance

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem e2_proof : E2 := by
  classical
  intro N p R D K ψ B M G L b μ1 μ0 i T hs hμ1 hμ0 hbT
  let q : ℝ := min p (1 - p)
  let A : ℝ := (B + M) / q
  let H : ℝ := |G| / q
  let I : Finset (Fin N) := ball D i b
  let J : Finset (Fin N) := ball D i T
  let e : CircleTable N := nedEpsilon p R μ1 μ0
  let f : CircleTable N := fun k => projEps p R μ1 μ0 J k
  have hp : FiniteConditioning.Admissible (fun _ : Fin N => p) := fun _ => hs.hp
  have hq : 0 < q := lt_min hs.hp.1 (sub_pos.mpr hs.hp.2)
  have hN : (0 : ℝ) < N := by exact_mod_cast hs.hN
  have hA : 0 ≤ A := div_nonneg (add_nonneg hs.hB0 hs.hM) hq.le
  have hH : 0 ≤ H := div_nonneg (abs_nonneg _) hq.le
  have hL : 0 ≤ L := le_trans (abs_nonneg (K 0)) (hs.hK 0 le_rfl)
  have ha : 0 ≤ A / (N : ℝ) := div_nonneg hA hN.le
  have hh : 0 ≤ H / (N : ℝ) := div_nonneg hH hN.le
  have hT : 0 < T := lt_trans hs.hb hbT
  rcases FiniteConditioning.fc7_proof (fun _ : Fin N => p) hp with
    ⟨hnonneg, hadd, _hsub, hsum, hscale, _hsup, hmono, _hexpect, _hcov, _hvar⟩
  have hE1 := e1_proof p R B M μ1 μ0 hs.hN hs.hp hs.hB hμ1 hμ0
  have he : ∀ k z, |e k z| ≤ A / (N : ℝ) := by
    intro k z
    calc
      |e k z| ≤ (B + M) / (min p (1 - p) * N) := hE1.1 k z
      _ = A / (N : ℝ) := by dsimp only [A, q]; ring
  have hf : ∀ k z, |f k z| ≤ A / (N : ℝ) := by
    intro k z
    exact FiniteConditioning.fc5_proof (fun _ : Fin N => p) hp J (e k)
      (A / (N : ℝ)) (he k) z
  have hK : ∀ k : Fin N, |K (D i k / b)| ≤ L := by
    intro k
    exact hs.hK _ (div_nonneg (hs.hD0 i k) hs.hb.le)
  have hmem : ∀ k ∈ I, D i k ≤ b := by
    intro k hk
    simpa only [I, ball, Finset.mem_filter, Finset.mem_univ, true_and] using hk

  -- First transfer the outcome NED bound on a ball contained in J.
  have hlocal : ∀ (k : Fin N) (s : ℝ), 0 ≤ s → ball D k s ⊆ J →
      l2Norm (fun _ => p) (fun z => e k z - f k z) ≤ H / (N : ℝ) * ψ s := by
    intro k s hs0 hsub
    have hk : k ∈ ball D k s := by
      simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [hs.hDself k] using hs0
    calc
      l2Norm (fun _ => p) (fun z => e k z - f k z)
          ≤ l2Norm (fun _ => p) (fun z => e k z -
            conditionOn (fun _ => p) (ball D k s) (e k) z) :=
        (FiniteConditioning.fc6_proof (fun _ : Fin N => p) hp J (e k)).2
          (ball D k s) hsub
      _ ≤ l2Norm (fun _ => p) (fun z => R k z -
            conditionOn (fun _ => p) (ball D k s) (R k) z) /
          (q * (N : ℝ)) := hE1.2 k (ball D k s) hk
      _ ≤ (G * ψ s) / (q * (N : ℝ)) :=
        div_le_div_of_nonneg_right (hs.hNED k s hs0) (mul_nonneg hq.le hN.le)
      _ ≤ (|G| * ψ s) / (q * (N : ℝ)) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self G) (hs.hψ s hs0))
          (mul_nonneg hq.le hN.le)
      _ = H / (N : ℝ) * ψ s := by dsimp only [H]; ring
  have hei : l2Norm (fun _ => p) (fun z => e i z - f i z) ≤ H / (N : ℝ) * ψ T :=
    hlocal i T hT.le (by intro k hk; exact hk)
  have hek : ∀ k ∈ I,
      l2Norm (fun _ => p) (fun z => e k z - f k z) ≤ H / (N : ℝ) * ψ (T - D i k) := by
    intro k hk
    have htk : 0 ≤ T - D i k := by have := hmem k hk; linarith
    apply hlocal k (T - D i k) htk
    intro l hl
    have hkl : D k l ≤ T - D i k := by
      simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and] using hl
    change l ∈ ball D i T
    simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and]
    linarith [hs.hDtri i k l]
  have hanti : ∀ k ∈ I, ψ T ≤ ψ (T - D i k) := by
    intro k hk
    have htk : 0 ≤ T - D i k := by have := hmem k hk; linarith
    exact hs.hψanti htk hT.le (by linarith [hs.hD0 i k])

  -- Multiplying an L² error by a uniformly bounded factor costs A/N.
  have hmul : ∀ U V : Assignment N → ℝ, (∀ z, |V z| ≤ A / (N : ℝ)) →
      l2Norm (fun _ => p) (fun z => U z * V z) ≤
        A / (N : ℝ) * l2Norm (fun _ => p) U := by
    intro U V hV
    calc
      l2Norm (fun _ => p) (fun z => U z * V z)
          ≤ l2Norm (fun _ => p) (fun z => (A / (N : ℝ)) * U z) := by
        apply hmono
        intro z
        rw [abs_mul, abs_mul, abs_of_nonneg ha]
        calc
          |U z| * |V z| ≤ |U z| * (A / (N : ℝ)) :=
            mul_le_mul_of_nonneg_left (hV z) (abs_nonneg _)
          _ = (A / (N : ℝ)) * |U z| := mul_comm _ _
      _ = A / (N : ℝ) * l2Norm (fun _ => p) U := by
        rw [hscale, abs_of_nonneg ha]
  have hproduct : ∀ k ∈ I,
      l2Norm (fun _ => p) (fun z =>
        (e i z * e k z - f i z * f k z) * K (D i k / b)) ≤
          2 * L * A * H * ψ (T - D i k) / (N : ℝ)^2 := by
    intro k hk
    let U : Assignment N → ℝ := fun z => (e i z - f i z) * e k z
    let V : Assignment N → ℝ := fun z => (e k z - f k z) * f i z
    have hU : l2Norm (fun _ => p) U ≤ (A / (N : ℝ)) * (H / (N : ℝ) * ψ T) := by
      calc
        l2Norm (fun _ => p) U ≤ (A / (N : ℝ)) *
            l2Norm (fun _ => p) (fun z => e i z - f i z) :=
          hmul (fun z => e i z - f i z) (e k) (he k)
        _ ≤ _ := mul_le_mul_of_nonneg_left hei ha
    have hV : l2Norm (fun _ => p) V ≤
        (A / (N : ℝ)) * (H / (N : ℝ) * ψ (T - D i k)) := by
      calc
        l2Norm (fun _ => p) V ≤ (A / (N : ℝ)) *
            l2Norm (fun _ => p) (fun z => e k z - f k z) :=
          hmul (fun z => e k z - f k z) (f i) (hf i)
        _ ≤ _ := mul_le_mul_of_nonneg_left (hek k hk) ha
    have hUV : l2Norm (fun _ => p) (fun z => U z + V z) ≤
        (A / (N : ℝ)) * (H / (N : ℝ) * ψ T) +
        (A / (N : ℝ)) * (H / (N : ℝ) * ψ (T - D i k)) :=
      le_trans (hadd U V) (add_le_add hU hV)
    have heq : (fun z => (e i z * e k z - f i z * f k z) * K (D i k / b)) =
        (fun z => K (D i k / b) * (U z + V z)) := by
      funext z
      dsimp only [U, V]
      ring
    calc
      l2Norm (fun _ => p) (fun z =>
          (e i z * e k z - f i z * f k z) * K (D i k / b))
          = |K (D i k / b)| * l2Norm (fun _ => p) (fun z => U z + V z) := by
        rw [heq, hscale]
      _ ≤ L * ((A / (N : ℝ)) * (H / (N : ℝ) * ψ T) +
          (A / (N : ℝ)) * (H / (N : ℝ) * ψ (T - D i k))) :=
        mul_le_mul (hK k) hUV (hnonneg _) hL
      _ = (L * (A / (N : ℝ)) * (H / (N : ℝ))) * (ψ T + ψ (T - D i k)) := by ring
      _ ≤ (L * (A / (N : ℝ)) * (H / (N : ℝ))) *
          (ψ (T - D i k) + ψ (T - D i k)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hanti k hk) le_rfl) (by positivity)
      _ = 2 * L * A * H * ψ (T - D i k) / (N : ℝ)^2 := by ring

  -- The same pointwise argument bounds the original and projected rows.
  have hrowabs : ∀ U : CircleTable N, (∀ k z, |U k z| ≤ A / (N : ℝ)) → ∀ z,
      |∑ k ∈ I, U i z * U k z * K (D i k / b)| ≤
        L * A^2 * (I.card : ℝ) / (N : ℝ)^2 := by
    intro U hU z
    calc
      |∑ k ∈ I, U i z * U k z * K (D i k / b)|
          ≤ ∑ k ∈ I, |U i z * U k z * K (D i k / b)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ I, L * (A / (N : ℝ))^2 := by
        apply Finset.sum_le_sum
        intro k _hk
        calc
          |U i z * U k z * K (D i k / b)| =
              (|U i z| * |U k z|) * |K (D i k / b)| := by rw [abs_mul, abs_mul]
          _ ≤ ((A / (N : ℝ)) * (A / (N : ℝ))) * |K (D i k / b)| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (hU i z) (hU k z) (abs_nonneg _) ha) (abs_nonneg _)
          _ ≤ ((A / (N : ℝ)) * (A / (N : ℝ))) * L :=
            mul_le_mul_of_nonneg_left (hK k) (mul_nonneg ha ha)
          _ = L * (A / (N : ℝ))^2 := by ring
      _ = L * A^2 * (I.card : ℝ) / (N : ℝ)^2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hrow : (fun z => nedVRow p R D K b μ1 μ0 i z -
          projRow p R D K b μ1 μ0 (ball D i T) i z) =
        (fun z => ∑ k ∈ I, (e i z * e k z - f i z * f k z) * K (D i k / b)) := by
      funext z
      change (∑ k ∈ I, e i z * e k z * K (D i k / b)) -
        (∑ k ∈ I, f i z * f k z * K (D i k / b)) = _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    rw [hrow]
    calc
      l2Norm (fun _ => p) (fun z =>
          ∑ k ∈ I, (e i z * e k z - f i z * f k z) * K (D i k / b))
          ≤ ∑ k ∈ I, l2Norm (fun _ => p) (fun z =>
            (e i z * e k z - f i z * f k z) * K (D i k / b)) :=
        hsum I (fun k z => (e i z * e k z - f i z * f k z) * K (D i k / b))
      _ ≤ ∑ k ∈ I, 2 * L * A * H * ψ (T - D i k) / (N : ℝ)^2 :=
        Finset.sum_le_sum hproduct
      _ = 2 * L * A * H * (∑ k ∈ I, ψ (T - D i k)) / (N : ℝ)^2 := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
      _ = _ := rfl
  · intro z
    exact hrowabs e he z
  · intro z
    exact hrowabs f hf z
  · intro z z' hzz'
    have hfactor : ∀ k : Fin N, f k z = f k z' := by
      intro k
      exact FiniteConditioning.fc1_proof (fun _ : Fin N => p) J (e k) z z'
        (fun l hl => hzz' l hl)
    change (∑ k ∈ I, f i z * f k z * K (D i k / b)) =
      ∑ k ∈ I, f i z' * f k z' * K (D i k / b)
    apply Finset.sum_congr rfl
    intro k _hk
    rw [hfactor i, hfactor k]

end
end AronowAudit.P004.Wave1.NedFarCovariance
