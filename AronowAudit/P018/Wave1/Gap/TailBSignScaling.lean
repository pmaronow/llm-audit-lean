import AronowAudit.P018.Wave1.Gap.TailBSignSample
import AronowAudit.P018.Wave1.Gap.TailBSignRemainder

/-! The normalized second-order formula equals N² times the fitted sandwich variance estimate for the slope. -/
noncomputable section
namespace AronowAudit.P018.Wave1.TailBSign
open Finset Matrix
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem tb05_scalar_rescaling (q s u r : ℝ) (hq : q ≠ 0) (hq1 : q^2-1 ≠ 0)
    (hgram : (q^2*(q^2-1)/2)^2-((s^2-q^2)/2)^2 ≠ 0) :
    let D := q^2*(q^2-1)/2
    let T := (s^2-q^2)/2
    let a := (D*(q^2-1)*u-T*(s*r-u))/(D^2-T^2)
    let b := (D*(s*r-u)-T*(q^2-1)*u)/(D^2-T^2)
    q^4*(tb05_nodePolynomial (q^2) s u r a b (T/D)-
      tb05_edgePolynomial (q^2) D s u r a b (T/D))/(D^2*(1-(T/D)^2)^2) =
      tb05_normalizedVariance ![q⁻¹,s/q,u/q,r/q] := by
  dsimp only
  let D := q^2*(q^2-1)/2
  let T := (s^2-q^2)/2
  let a := (D*(q^2-1)*u-T*(s*r-u))/(D^2-T^2)
  let b := (D*(s*r-u)-T*(q^2-1)*u)/(D^2-T^2)
  let p : Fin 4 → ℝ := ![q⁻¹,s/q,u/q,r/q]
  have hD : D ≠ 0 := by dsimp [D]; exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hq) hq1) (by norm_num)
  have hG : D^2-T^2 ≠ 0 := hgram
  have hden : 1-(T/D)^2 ≠ 0 := by
    intro h
    apply hG
    field_simp [hD] at h
    nlinarith [h]
  have hl : tb05_lambda p=T/D := by
    dsimp [tb05_lambda,p,D,T]
    field_simp [hq,hq1]
    <;> ring
  have hbar : tb05_bbar p=q*b := by
    unfold tb05_bbar
    rw [hl]
    dsimp [p,b,D,T]
    field_simp [hq,hq1,hgram]
    <;> ring
  have hbasic (d t y c : ℝ) (hd : d ≠ 0) (hg : d^2-t^2 ≠ 0) :
      y/d-(t/d)*((d*c-t*y)/(d^2-t^2))=(d*y-t*c)/(d^2-t^2) := by
    field_simp [hd,hg]
    <;> ring
  have hy : ((q^2-1)*u)/D=2*u/q^2 := by
    dsimp [D]
    field_simp [hq,hq1]
    <;> ring
  have ha0 : 2*u/q^2-(T/D)*b=a := by
    have hh := hbasic D T ((q^2-1)*u) (s*r-u) hD hG
    rw [hy] at hh
    convert hh using 1 <;> dsimp only [a,b] <;> ring
  have ha : tb05_alpha p=a := by
    unfold tb05_alpha
    rw [hl,hbar]
    change 2*q⁻¹*(u/q)-(T/D)*q⁻¹*(q*b)=a
    calc
      _ = 2*u/q^2-(T/D)*b := by field_simp [hq]
      _ = a := ha0
  let A := -(T/D)*u+a*(1+(T/D)*(q^2-1))-b*(q^2-1+T/D)
  let B := r-a*s+b*(T/D)*s
  let C := -2-(T/D)*(q^2-2)
  have hA : tb05_nodeA p=A/q := by
    unfold tb05_nodeA
    rw [hl,ha,hbar]
    dsimp [p,A,D,T]
    field_simp [hq,hq1]
    <;> ring
  have hB : tb05_nodeB p=B/q := by
    unfold tb05_nodeB
    rw [ha,hbar,hl]
    dsimp [p,B]
    field_simp [hq]
    <;> ring
  have hC : tb05_nodeC p=C/q := by
    dsimp [tb05_nodeC,p,C,D,T]
    field_simp [hq,hq1]
    <;> ring
  have hn : tb05_nodeNorm p=tb05_nodePolynomial (q^2) s u r a b (T/D)/q^4 := by
    unfold tb05_nodeNorm
    rw [hA,hB,hC]
    dsimp [p,tb05_nodePolynomial,A,B,C]
    field_simp [hq]
    <;> ring
  have he : tb05_edgeNorm p=tb05_edgePolynomial (q^2) D s u r a b (T/D)/q^4 := by
    unfold tb05_edgeNorm
    rw [hl,ha,hbar]
    dsimp [p,tb05_edgePolynomial,D]
    field_simp [hq]
    <;> ring
  change q^4*(tb05_nodePolynomial (q^2) s u r a b (T/D)-
    tb05_edgePolynomial (q^2) D s u r a b (T/D))/(D^2*(1-(T/D)^2)^2) =
      tb05_normalizedVariance p
  unfold tb05_normalizedVariance
  rw [hn,he,hl]
  dsimp only [p,Matrix.cons_val_zero]
  dsimp only [D]
  field_simp [hq,hq1,hden]
  <;> ring

/-- Exact formula for N² times the fitted sandwich variance estimate for the slope,
in normalized sign sums. -/
theorem tb05_sample_normalized_identity {N : ℕ} (z w : Fin N → ℝ)
    (hz : ∀ i,(z i)^2=1) (hw : ∀ i,(w i)^2=1) (hN : 2 ≤ N)
    (hgram : (Dreal N)^2-(tb05_T z)^2 ≠ 0) :
    (N:ℝ)^2*sampleVariance members (tb05_design z) (tb05_response w) 1 1 =
      tb05_normalizedVariance ![(Real.sqrt N)⁻¹,(∑ i,z i)/Real.sqrt N,
        (∑ i,w i)/Real.sqrt N,(∑ i,z i*w i)/Real.sqrt N] := by
  let q := Real.sqrt (N:ℝ)
  have hq2 : q^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hq : q ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))).ne'
  have hq1 : q^2-1 ≠ 0 := by
    rw [hq2]
    have : (2:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hD : Dreal N=q^2*(q^2-1)/2 := by rw [hq2]; rfl
  have hT : tb05_T z=((∑ i,z i)^2-q^2)/2 := by rw [tb05_T_formula z hz,hq2]
  have hG : (q^2*(q^2-1)/2)^2-(((∑ i,z i)^2-q^2)/2)^2 ≠ 0 := by
    simpa only [← hD,← hT] using hgram
  have h := tb05_scalar_rescaling q (∑ i,z i) (∑ i,w i) (∑ i,z i*w i) hq hq1 hG
  change (N:ℝ)^2*sampleVariance members (tb05_design z) (tb05_response w) 1 1 =
    tb05_normalizedVariance ![q⁻¹,(∑ i,z i)/q,(∑ i,w i)/q,(∑ i,z i*w i)/q]
  rw [tb05_slope_bread_meat z w hz hw hN hgram]
  simp only [tb05_fitA,tb05_fitB,hD,hT,← hq2]
  convert h using 1 <;> ring

/-- A deterministic remainder bound for N² times the fitted sandwich variance estimate
for the slope, on a bounded normalized-sums event. -/
theorem tb05_sample_second_order_remainder (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (z w : Fin N → ℝ),
      (∀ i,(z i)^2=1) → (∀ i,(w i)^2=1) → 2 ≤ N →
      (Dreal N)^2-(tb05_T z)^2 ≠ 0 →
      (Real.sqrt N)⁻¹ ≤ 1/(2*(R^2+2)) →
      |(∑ i,z i)/Real.sqrt N| ≤ R → |(∑ i,w i)/Real.sqrt N| ≤ R →
      |(∑ i,z i*w i)/Real.sqrt N| ≤ R →
      |(N:ℝ)^2*sampleVariance members (tb05_design z) (tb05_response w) 1 1-
        4*(((∑ i,z i)/Real.sqrt N)^2+((∑ i,z i*w i)/Real.sqrt N)^2-1)| ≤
          C/Real.sqrt N := by
  obtain ⟨C,hC,hbound⟩ := tb05_bounded_normalized_remainder R hR
  refine ⟨C,hC,?_⟩
  intro N z w hz hw hN hG hx hs hu hr
  rw [tb05_sample_normalized_identity z w hz hw hN hG]
  simpa only [abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)),div_eq_mul_inv] using
    hbound (Real.sqrt N)⁻¹ ((∑ i,z i)/Real.sqrt N) ((∑ i,w i)/Real.sqrt N)
      ((∑ i,z i*w i)/Real.sqrt N)
      (by simpa only [abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))] using hx) hs hu hr


/-- The same normalized box automatically excludes singular samples. -/
theorem tb05_gram_nonsingular_on_box {N : ℕ} (z : Fin N → ℝ)
    (hz : ∀ i,(z i)^2=1) (hN : 2 ≤ N) (R : ℝ) (hR : 0 ≤ R)
    (hx : (Real.sqrt N)⁻¹ ≤ 1/(2*(R^2+2)))
    (hs : |(∑ i,z i)/Real.sqrt N| ≤ R) :
    (Dreal N)^2-(tb05_T z)^2 ≠ 0 := by
  let q := Real.sqrt (N:ℝ)
  let p : Fin 4 → ℝ := ![q⁻¹,(∑ i,z i)/q,0,0]
  have hq2 : q^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hq : q ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))).ne'
  have hq1 : q^2-1 ≠ 0 := by
    rw [hq2]
    have : (2:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hD : Dreal N ≠ 0 := (printed_Dpos hN).ne'
  have hl : tb05_lambda p=tb05_T z/Dreal N := by
    rw [tb05_T_formula z hz]
    dsimp [tb05_lambda,p,Dreal]
    rw [← hq2]
    field_simp [hq,hq1]
    <;> ring
  have hden := (tb05_denominators R hR p
    (by
      change |q⁻¹| ≤ _
      rw [abs_of_nonneg (inv_nonneg.2 (show 0 ≤ q from Real.sqrt_nonneg _))]
      exact hx)
    hs).2
  rw [hl] at hden
  intro hG
  apply hden
  field_simp [hD]
  nlinarith [hG]

/-- A deterministic second-order remainder bound for N² times the fitted sandwich
variance estimate for the slope, on a bounded normalized-sign-sums event,
with no separate rank assumption. -/
theorem tb05_slope_second_order_bounded_sums (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (z w : Fin N → ℝ),
      (∀ i,(z i)^2=1) → (∀ i,(w i)^2=1) → 2 ≤ N →
      (Real.sqrt N)⁻¹ ≤ 1/(2*(R^2+2)) →
      |(∑ i,z i)/Real.sqrt N| ≤ R → |(∑ i,w i)/Real.sqrt N| ≤ R →
      |(∑ i,z i*w i)/Real.sqrt N| ≤ R →
      |(N:ℝ)^2*sampleVariance members (tb05_design z) (tb05_response w) 1 1-
        4*(((∑ i,z i)/Real.sqrt N)^2+((∑ i,z i*w i)/Real.sqrt N)^2-1)| ≤
          C/Real.sqrt N := by
  obtain ⟨C,hC,hbound⟩ := tb05_sample_second_order_remainder R hR
  refine ⟨C,hC,?_⟩
  intro N z w hz hw hN hx hs hu hr
  exact hbound N z w hz hw hN (tb05_gram_nonsingular_on_box z hz hN R hR hx hs)
    hx hs hu hr

end AronowAudit.P018.Wave1.TailBSign
