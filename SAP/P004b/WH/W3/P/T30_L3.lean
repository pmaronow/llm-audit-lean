import SAP.P004b.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3.P.T30_L3

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

lemma expect_add_local {N : ℕ} (p : Fin N → ℝ) (X Y : Assignment N → ℝ) :
    expect p (fun z => X z + Y z) = expect p X + expect p Y := by
  unfold expect
  simp only [mul_add, Finset.sum_add_distrib]

lemma expect_sub_local {N : ℕ} (p : Fin N → ℝ) (X Y : Assignment N → ℝ) :
    expect p (fun z => X z - Y z) = expect p X - expect p Y := by
  unfold expect
  simp only [mul_sub, Finset.sum_sub_distrib]

lemma expect_mul_local {N : ℕ} (p : Fin N → ℝ) (c : ℝ) (X : Assignment N → ℝ) :
    expect p (fun z => c * X z) = c * expect p X := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

lemma design_normalized_local {N : ℕ} (p : Fin N → ℝ) :
    (∑ z : Assignment N, designWeight p z) = 1 := by
  simp only [designWeight]
  rw [← Fintype.prod_sum]
  simp [coin, Fintype.sum_bool]

lemma expect_const_local {N : ℕ} (p : Fin N → ℝ) (c : ℝ) :
    expect p (fun _ : Assignment N => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, design_normalized_local, one_mul]

lemma designWeight_nonneg_local {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (z : Assignment N) : 0 ≤ designWeight p z := by
  unfold designWeight
  apply Finset.prod_nonneg
  intro i hi
  by_cases h : z i
  · simp [coin, h, (hp i).1.le]
  · simp [coin, h, (sub_nonneg.mpr (le_of_lt (hp i).2))]

lemma variance_centered_local {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) :
    variance p X = expect p (fun z => (X z - expect p X)^2) := by
  unfold variance cov
  let m := expect p X
  have he : expect p (fun z => (X z - m)^2) =
      expect p (fun z => X z * X z) - 2*m*expect p X + m*m := by
    have hpoint : (fun z => (X z - m)^2) =
        fun z => X z * X z - 2*m*(X z) + m*m := by
      funext z
      ring
    rw [hpoint]
    simp only [expect_add_local, expect_sub_local, expect_mul_local, expect_const_local]
  dsimp [m] at he
  rw [he]
  ring

lemma variance_nonneg_local {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (X : Assignment N → ℝ) : 0 ≤ variance p X := by
  rw [variance_centered_local]
  unfold expect
  apply Finset.sum_nonneg
  intro z hz
  exact mul_nonneg (designWeight_nonneg_local p hp z) (sq_nonneg _)

lemma variance_sub_mul_local {N : ℕ} (p : Fin N → ℝ)
    (X Y : Assignment N → ℝ) (a : ℝ) :
    variance p (fun z => X z - a * Y z) =
      variance p X - 2*a*cov p X Y + a^2*variance p Y := by
  unfold variance cov
  have hprod : (fun z => (X z - a*Y z)*(X z-a*Y z)) =
      fun z => X z*X z - (a*(X z*Y z)+a*(Y z*X z)) + a^2*(Y z*Y z) := by
    funext z
    ring
  have hmean : expect p (fun z => X z-a*Y z) = expect p X-a*expect p Y := by
    rw [expect_sub_local, expect_mul_local]
  rw [hprod]
  simp only [expect_add_local, expect_sub_local, expect_mul_local]
  have hxy : expect p (fun z => Y z * X z) = expect p (fun z => X z * Y z) := by
    congr 1
    funext z
    ring
  rw [hxy]
  ring

lemma augmented_sub_count_local {N : ℕ} (p : ℝ) (R : CircleTable N)
    (c1 c0 : ℝ) (hp0 : p ≠ 0) (hp1 : 1-p ≠ 0) (hN : 0 < N) :
    augmented (fun _ => p) R (fun _ a => if a then c1 else c0) =
      fun z => ht (fun _ => p) R z - (c1/p+c0/(1-p))*wholeCountFluctuation p z := by
  funext z
  dsimp [augmented, ht, wholeCountFluctuation]
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hterm (i : Fin N) :
      c1-c0 + bit (z i) * (R i z-c1) / p -
        (1-bit (z i)) * (R i z-c0) / (1-p) =
      bit (z i)*R i z/p - (1-bit (z i))*R i z/(1-p) -
        (c1/p+c0/(1-p))*(bit (z i)-p) := by
    cases hi : z i <;> simp [bit, hi] <;> field_simp [hp0, hp1] <;> ring
  have hsum :
      (∑ i : Fin N, (c1-c0 + bit (z i)*(R i z-c1)/p -
        (1-bit (z i))*(R i z-c0)/(1-p))) =
      (∑ i : Fin N, (bit (z i)*R i z/p-(1-bit (z i))*R i z/(1-p))) -
        (c1/p+c0/(1-p))*((∑ i : Fin N, bit (z i))-(N : ℝ)*p) := by
    calc
      _ = ∑ i : Fin N,
          (bit (z i)*R i z/p-(1-bit (z i))*R i z/(1-p)-
            (c1/p+c0/(1-p))*(bit (z i)-p)) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hterm i
      _ = (∑ i : Fin N, (bit (z i)*R i z/p-(1-bit (z i))*R i z/(1-p))) -
          ∑ i : Fin N, (c1/p+c0/(1-p))*(bit (z i)-p) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ i : Fin N, (bit (z i)*R i z/p-(1-bit (z i))*R i z/(1-p))) -
          (c1/p+c0/(1-p))*(∑ i : Fin N, (bit (z i)-p)) := by
        rw [← Finset.mul_sum]
      _ = (∑ i : Fin N, (bit (z i)*R i z/p-(1-bit (z i))*R i z/(1-p))) -
          (c1/p+c0/(1-p))*((∑ i : Fin N, bit (z i))-(∑ i : Fin N, p)) := by
        have hsub : (∑ i : Fin N, (bit (z i)-p)) =
            (∑ i : Fin N, bit (z i))-(∑ i : Fin N, p) := by
          rw [Finset.sum_sub_distrib]
        rw [hsub]
      _ = (∑ i : Fin N, (bit (z i)*R i z/p-(1-bit (z i))*R i z/(1-p))) -
          (c1/p+c0/(1-p))*((∑ i : Fin N, bit (z i))-(N : ℝ)*p) := by
        have hpsum : (∑ i : Fin N, p) = (N : ℝ)*p := by simp
        rw [hpsum]
  have hcount : (∑ i : Fin N, bit (z i)) = armCount z true := by
    unfold armCount
    apply Finset.sum_congr rfl
    intro i hi
    cases z i <;> simp [bit]
  have hmain := congrArg (fun x : ℝ => x/(N : ℝ)) hsum
  rw [hcount] at hmain
  have harith (S T : ℝ) :
      (S-(c1/p+c0/(1-p))*(T-(N : ℝ)*p))/(N : ℝ) =
        S/(N : ℝ)-(c1/p+c0/(1-p))*(T/(N : ℝ)-p) := by
    field_simp [ne_of_gt hn]
    <;> ring
  rw [hmain]
  exact harith _ _

end
end SAP.P004b.WH.W3.P.T30_L3

open SAP.P004b.WH.W3.P.T30_L3

theorem SAP.P004b.WH.W3.T30_L3_proof : SAP.P004b.WH.W3.T30_L3 := by
  intro hMom N hN p hp R
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have hp1 : 1-p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hBmean, hBvar, hHTB⟩ := hMom N hN p hp R
  let B : Assignment N → ℝ := wholeCountFluctuation p
  let H : Assignment N → ℝ := ht (fun _ => p) R
  let opt : ℝ := wholeOptimalCoefficient p R
  let C : ℝ := wholeVarianceConstant p R
  have hBmean' : expect (fun _ => p) B = 0 := hBmean
  have hBvar' : variance (fun _ => p) B = p*(1-p)/N := hBvar
  have hHTB' : cov (fun _ => p) H B =
      ((1-p)*barMu (fun _ => p) R true + p*barMu (fun _ => p) R false +
        p*wholeDelta p R)/N := hHTB
  have hVariance (c1 c0 : ℝ) :
      variance (fun _ => p) (augmented (fun _ => p) R (fun _ a => if a then c1 else c0)) =
        variance (fun _ => p) H - 2*(c1/p+c0/(1-p))*cov (fun _ => p) H B +
          (c1/p+c0/(1-p))^2*variance (fun _ => p) B := by
    rw [augmented_sub_count_local p R c1 c0 hp0 hp1 hN]
    dsimp [H, B]
    exact variance_sub_mul_local (fun _ => p) _ _ _
  have hSquare : ∀ c1 c0 : ℝ,
      variance (fun _ => p) (augmented (fun _ => p) R (fun _ a => if a then c1 else c0)) =
        p*(1-p)/N*(c1/p+c0/(1-p)-wholeOptimalCoefficient p R)^2 +
          wholeVarianceConstant p R := by
    intro c1 c0
    rw [hVariance c1 c0, hBvar', hHTB']
    dsimp [wholeVarianceConstant, wholeOptimalCoefficient]
    field_simp [hp0, hp1, ne_of_gt hNreal]
    <;> ring
  have hC_nonneg : 0 ≤ C := by
    let t := opt
    have hfit := hSquare (p*t) 0
    have hcoef : p*t/p + 0/(1-p) = opt := by
      dsimp [t]
      field_simp [hp0]
      ring
    rw [hcoef] at hfit
    have hvarnn := variance_nonneg_local (fun _ => p) (fun _ => hp)
      (augmented (fun _ => p) R (fun _ a => if a then p*t else 0))
    have hfit0 : variance (fun _ => p)
        (augmented (fun _ => p) R (fun _ a => if a then p*t else 0)) = C := by
      simpa [C, opt, hcoef] using hfit
    rw [← hfit0]
    exact hvarnn
  have hfull : variance (fun _ => p) (linearHajek (fun _ => p) R) =
      wholeVarianceConstant p R + p*(wholeDelta p R)^2/(N*(1-p)) := by
    have hlin : linearHajek (fun _ => p) R =
        augmented (fun _ => p) R (fun _ a => barMu (fun _ => p) R a) := rfl
    have hg : (fun (_ : Fin N) (a : Bool) => barMu (fun _ => p) R a) =
        (fun (_ : Fin N) (a : Bool) => if a then barMu (fun _ => p) R true else barMu (fun _ => p) R false) := by
      funext i a
      cases a <;> rfl
    have haug : augmented (fun _ => p) R (fun (_ : Fin N) (a : Bool) => barMu (fun _ => p) R a) =
        augmented (fun _ => p) R
          (fun (_ : Fin N) (a : Bool) => if a then barMu (fun _ => p) R true else barMu (fun _ => p) R false) := by
      unfold augmented
      congr 1
    have hcoef : barMu (fun _ => p) R true/p + barMu (fun _ => p) R false/(1-p) -
        wholeOptimalCoefficient p R = -wholeDelta p R/(1-p) := by
      dsimp [wholeOptimalCoefficient]
      ring
    have hfit := hSquare (barMu (fun _ => p) R true) (barMu (fun _ => p) R false)
    rw [hcoef] at hfit
    have hfit' : variance (fun _ => p) (linearHajek (fun _ => p) R) =
        p*(1-p)/N*(-wholeDelta p R/(1-p))^2 + wholeVarianceConstant p R := by
      calc
        _ = variance (fun _ => p)
            (augmented (fun _ => p) R (fun _ a => barMu (fun _ => p) R a)) :=
              congrArg (variance (fun _ => p)) hlin
        _ = variance (fun _ => p)
            (augmented (fun _ => p) R
              (fun (_ : Fin N) (a : Bool) => if a then barMu (fun _ => p) R true else barMu (fun _ => p) R false)) :=
              congrArg (variance (fun _ => p)) haug
        _ = _ := hfit
    rw [hfit']
    dsimp [wholeVarianceConstant]
    field_simp [hp0, hp1, ne_of_gt hNreal]
    <;> ring
  refine ⟨hC_nonneg, ⟨?_, hfull, ?_, ?_⟩⟩
  · exact hSquare
  · intro ε hε hDelta
    rw [hfull]
    simp only [add_sub_cancel_left]
    constructor
    · have hden : 0 < (N : ℝ)*(1-p) := mul_pos hNreal (sub_pos.mpr hp.2)
      exact div_nonneg (mul_nonneg (le_of_lt hp.1) (sq_nonneg _)) (le_of_lt hden)
    · have hsq : (wholeDelta p R)^2 ≤ ε^2 := by
        have habs : |wholeDelta p R| ≤ ε := hDelta
        have hprod := mul_nonneg (sub_nonneg.mpr habs)
          (add_nonneg hε (abs_nonneg (wholeDelta p R)))
        nlinarith [hprod, sq_abs (wholeDelta p R)]
      have hden : 0 < (N : ℝ)*(1-p) := mul_pos hNreal (sub_pos.mpr hp.2)
      apply (div_le_div_iff_of_pos_right hden).2
      exact mul_le_mul_of_nonneg_left hsq (le_of_lt hp.1)
  · intro hDelta
    rw [hfull, hDelta]
    simp
