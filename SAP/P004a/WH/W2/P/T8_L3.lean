import SAP.P004a.WH.W2.Leaves
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace SAP.P004a.WH.W2.P.T8_L3

open Set
open scoped Classical

noncomputable section

def ratioLog (ν x : ℝ) : ℝ :=
  Real.log (studentDensity ν x / ProbabilityTheory.gaussianPDFReal 0 1 x)

lemma student_pos (ν x : ℝ) (hν : 0 < ν) : 0 < studentDensity ν x := by
  unfold studentDensity
  apply mul_pos
  · exact AronowAudit.P004.Wave1.t7_student_prefactor_pos ν hν
  · exact Real.rpow_pos_of_pos (by positivity) _

lemma gaussian_pos (x : ℝ) : 0 < ProbabilityTheory.gaussianPDFReal 0 1 x := by
  exact ProbabilityTheory.gaussianPDFReal_pos 0 1 x (by norm_num)

lemma ratio_pos (ν x : ℝ) (hν : 0 < ν) :
    0 < studentDensity ν x / ProbabilityTheory.gaussianPDFReal 0 1 x :=
  div_pos (student_pos ν x hν) (gaussian_pos x)

lemma deriv_neg {ν : ℝ} (hν : 0 < ν)
    (hd : ∀ x : ℝ, HasDerivAt (ratioLog ν)
      (x*(x^2-1)/(ν+x^2)) x) {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    deriv (ratioLog ν) x < 0 := by
  rw [(hd x).deriv]
  have hden : 0 < ν+x^2 := by positivity
  apply div_neg_of_neg_of_pos
  · apply mul_neg_of_pos_of_neg hx₀
    nlinarith
  · exact hden

lemma deriv_pos {ν : ℝ} (hν : 0 < ν)
    (hd : ∀ x : ℝ, HasDerivAt (ratioLog ν)
      (x*(x^2-1)/(ν+x^2)) x) {x : ℝ} (hx : 1 < x) :
    0 < deriv (ratioLog ν) x := by
  rw [(hd x).deriv]
  have hden : 0 < ν+x^2 := by positivity
  apply div_pos
  · exact mul_pos (by linarith) (by nlinarith)
  · exact hden

lemma deriv_nonneg_tail {ν : ℝ} (hν : 0 < ν)
    (hd : ∀ x : ℝ, HasDerivAt (ratioLog ν)
      (x*(x^2-1)/(ν+x^2)) x) {x : ℝ}
    (hx2 : 2 ≤ x) (hxν : 2*ν ≤ x^2) :
    x/4 ≤ deriv (ratioLog ν) x := by
  rw [(hd x).deriv]
  have hden : 0 < ν+x^2 := by positivity
  have hcoeff : ν+4 ≤ 3*x^2 := by
    by_cases hν8 : ν ≤ 8
    · nlinarith [sq_nonneg (x^2)]
    · nlinarith
  rw [le_div_iff₀ hden]
  have hmul := mul_le_mul_of_nonneg_left hcoeff (show 0 ≤ x by linarith)
  nlinarith

lemma strictAnti01 {ν : ℝ} (hν : 0 < ν)
    (hd : ∀ x : ℝ, HasDerivAt (ratioLog ν)
      (x*(x^2-1)/(ν+x^2)) x) :
    StrictAntiOn (ratioLog ν) (Icc (0:ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
  · intro x hx
    exact (hd x).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x ∧ x < 1 := by simpa [interior_Icc] using hx
    exact deriv_neg hν hd hx'.1 hx'.2

lemma mono_right {ν : ℝ} (hν : 0 < ν)
    (hd : ∀ x : ℝ, HasDerivAt (ratioLog ν)
      (x*(x^2-1)/(ν+x^2)) x) (b : ℝ) (_hb : 1 ≤ b) :
    MonotoneOn (ratioLog ν) (Icc 1 b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 1 b)
  · intro x hx
    exact (hd x).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 1 < x ∧ x < b := by simpa [interior_Icc] using hx
    have hpos := deriv_pos hν hd hx'.1
    linarith

lemma strictMono_right {ν : ℝ} (hν : 0 < ν)
    (hd : ∀ x : ℝ, HasDerivAt (ratioLog ν)
      (x*(x^2-1)/(ν+x^2)) x) (b : ℝ) :
    StrictMonoOn (ratioLog ν) (Icc 1 b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 1 b)
  · intro x hx
    exact (hd x).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 1 < x ∧ x < b := by simpa [interior_Icc] using hx
    exact deriv_pos hν hd hx'.1

def tailAux (ν : ℝ) (x : ℝ) : ℝ := ratioLog ν x - x^2/8

lemma tailAux_deriv {ν : ℝ}
    (hd : ∀ x : ℝ, HasDerivAt (ratioLog ν)
      (x*(x^2-1)/(ν+x^2)) x) (x : ℝ) :
    HasDerivAt (tailAux ν) (x*(x^2-1)/(ν+x^2)-x/4) x := by
  have hp : HasDerivAt (fun t : ℝ => t^2/8) (x/4) x := by
    convert ((hasDerivAt_id x).pow 2).div_const 8 using 1
    · funext t
      simp
    · simp
      ring
  exact (hd x).sub hp

lemma mono_tailAux {ν : ℝ} (hν : 0 < ν)
    (hd : ∀ x : ℝ, HasDerivAt (ratioLog ν)
      (x*(x^2-1)/(ν+x^2)) x) (a b : ℝ) (ha : 2 ≤ a)
    (haν : 2*ν ≤ a^2) (_hab : a ≤ b) :
    MonotoneOn (tailAux ν) (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · intro x hx
    exact (tailAux_deriv hd x).continuousAt.continuousWithinAt
  · intro x hx
    exact (tailAux_deriv hd x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : a < x ∧ x < b := by simpa [interior_Icc] using hx
    have hx2 : 2 ≤ x := le_trans ha (le_of_lt hx'.1)
    have hxν : 2*ν ≤ x^2 := by
      have hsq : a^2 ≤ x^2 := by
        nlinarith [mul_nonneg (show 0 ≤ x-a by linarith)
          (show 0 ≤ x+a by linarith)]
      linarith
    have hder := deriv_nonneg_tail hν hd hx2 hxν
    rw [(tailAux_deriv hd x).deriv]
    rw [(hd x).deriv] at hder
    linarith

lemma at_one_neg {ν : ℝ} (hν : 0 < ν)
    (hcenter : studentDensity ν 0 ≤ ProbabilityTheory.gaussianPDFReal 0 1 0)
    (hd : ∀ x : ℝ, HasDerivAt (ratioLog ν)
      (x*(x^2-1)/(ν+x^2)) x) : ratioLog ν 1 < 0 := by
  have hanti := strictAnti01 hν hd
  have h01 : 0 ∈ Icc (0:ℝ) 1 ∧ 1 ∈ Icc (0:ℝ) 1 := by norm_num
  have hstrict := hanti h01.1 h01.2 (by norm_num : (0:ℝ) < 1)
  have hzero : ratioLog ν 0 ≤ 0 := by
    dsimp [ratioLog]
    rw [Real.log_nonpos_iff (le_of_lt (ratio_pos ν 0 hν)), div_le_one (gaussian_pos 0)]
    exact hcenter
  linarith

lemma log_le_densities {ν x : ℝ} (hν : 0 < ν) :
    ratioLog ν x ≤ 0 ↔ studentDensity ν x ≤ ProbabilityTheory.gaussianPDFReal 0 1 x := by
  dsimp [ratioLog]
  rw [Real.log_nonpos_iff (le_of_lt (ratio_pos ν x hν)), div_le_one (gaussian_pos x)]

lemma log_ge_densities {ν x : ℝ} (hν : 0 < ν) :
    0 ≤ ratioLog ν x ↔ ProbabilityTheory.gaussianPDFReal 0 1 x ≤ studentDensity ν x := by
  dsimp [ratioLog]
  rw [Real.log_nonneg_iff (ratio_pos ν x hν), one_le_div (gaussian_pos x)]

end

end SAP.P004a.WH.W2.P.T8_L3

theorem SAP.P004a.WH.W2.T8_L3_proof : SAP.P004a.WH.W2.T8_L3 := by
  intro ν hν hcenter hderiv
  let f : ℝ → ℝ := SAP.P004a.WH.W2.P.T8_L3.ratioLog ν
  have hd : ∀ x : ℝ, HasDerivAt f (x*(x^2-1)/(ν+x^2)) x := by
    intro x
    exact hderiv x
  have hf0 : f 0 ≤ 0 := by
    simpa [f, SAP.P004a.WH.W2.P.T8_L3.ratioLog] using
      (SAP.P004a.WH.W2.P.T8_L3.log_le_densities hν (x := 0)).2 hcenter
  have hf1 : f 1 < 0 := by
    simpa [f] using SAP.P004a.WH.W2.P.T8_L3.at_one_neg hν hcenter hderiv
  let a : ℝ := max 2 (2*ν)
  have ha2 : 2 ≤ a := le_max_left _ _
  have haν : 2*ν ≤ a^2 := by
    by_cases hsmall : ν ≤ 2
    · have : 2*ν ≤ 4 := by linarith
      nlinarith [sq_nonneg a]
    · have h : 2*ν ≤ a := le_max_right _ _
      nlinarith [sq_nonneg a]
  let b : ℝ := a + 8*|f a| + 8
  have hab : a ≤ b := by dsimp [b]; have := abs_nonneg (f a); linarith
  have hb1 : 1 < b := by linarith [ha2]
  have hmono := SAP.P004a.WH.W2.P.T8_L3.mono_tailAux hν hderiv a b ha2 haν hab
  have htail : f a - a^2/8 ≤ f b - b^2/8 := by
    have := hmono (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
      (show b ∈ Icc a b from ⟨hab, le_rfl⟩) hab
    simpa [SAP.P004a.WH.W2.P.T8_L3.tailAux] using this
  have hba : b-a = 8*|f a|+8 := by dsimp [b]; ring
  have hsum : 4 ≤ b+a := by linarith [ha2]
  have hprod : 32*|f a|+32 ≤ (b-a)*(b+a) := by
    have hnonneg : 0 ≤ 8*|f a|+8 := by positivity
    have hm := mul_le_mul_of_nonneg_left hsum hnonneg
    calc
      32*|f a|+32 = (8*|f a|+8)*4 := by ring
      _ ≤ (8*|f a|+8)*(b+a) := hm
      _ = (b-a)*(b+a) := by rw [hba]
  have hsq : b^2-a^2 = (b-a)*(b+a) := by ring
  have hfb : 0 < f b := by
    have habound : f a + (b^2-a^2)/8 ≤ f b := by nlinarith [htail]
    have habs : -|f a| ≤ f a := neg_abs_le (f a)
    nlinarith [habound, hprod, hsq]
  have hcont : ContinuousOn f (Icc 1 b) := by
    intro x hx
    exact (hd x).continuousAt.continuousWithinAt
  have hrootMem : (0:ℝ) ∈ f '' Icc 1 b := by
    apply intermediate_value_Icc (le_of_lt hb1) hcont
    exact ⟨by linarith, le_of_lt hfb⟩
  rcases hrootMem with ⟨ρ, hρmem, hρval⟩
  have hρ : f ρ = 0 := hρval
  have hρlo : 1 ≤ ρ := hρmem.1
  have hρhi : ρ ≤ b := hρmem.2
  have hρgt : 1 < ρ := by
    by_contra hn
    have heq : ρ = 1 := by linarith
    rw [heq] at hρ
    linarith
  refine ⟨ρ, hρgt, ?_, ?_⟩
  · intro x hx0 hxρ
    have hfx : f x ≤ 0 := by
      by_cases hx1 : x ≤ 1
      · have hanti := SAP.P004a.WH.W2.P.T8_L3.strictAnti01 hν hderiv
        have hmono : SAP.P004a.WH.W2.P.T8_L3.ratioLog ν x ≤
            SAP.P004a.WH.W2.P.T8_L3.ratioLog ν 0 := by
          by_cases hxeq : x = 0
          · simp [hxeq]
          · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxeq)
            have hxstrict := hanti (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1)
              (show x ∈ Icc (0:ℝ) 1 from ⟨hx0, hx1⟩) hxpos
            exact hxstrict.le
        have hmono' : f x ≤ f 0 := by simpa [f] using hmono
        linarith
      · have hmono := SAP.P004a.WH.W2.P.T8_L3.mono_right hν hderiv ρ hρlo
        have hfx' := hmono (show x ∈ Icc 1 ρ from ⟨le_of_not_ge hx1, hxρ⟩)
          (show ρ ∈ Icc 1 ρ from ⟨hρlo, le_rfl⟩) hxρ
        have hρ' : SAP.P004a.WH.W2.P.T8_L3.ratioLog ν ρ = 0 := by
          simpa [f] using hρ
        rw [hρ'] at hfx'
        change SAP.P004a.WH.W2.P.T8_L3.ratioLog ν x ≤ 0
        exact hfx'
    exact (SAP.P004a.WH.W2.P.T8_L3.log_le_densities hν).1 (by simpa [f] using hfx)
  · intro x hxρ
    have hmono := SAP.P004a.WH.W2.P.T8_L3.mono_right hν hderiv x (le_trans hρgt.le hxρ)
    have hfx := hmono (show ρ ∈ Icc 1 x from ⟨hρlo, hxρ⟩)
      (show x ∈ Icc 1 x from ⟨le_trans hρlo hxρ, le_rfl⟩) hxρ
    have hρ' : SAP.P004a.WH.W2.P.T8_L3.ratioLog ν ρ = 0 := by
      simpa [f] using hρ
    rw [hρ'] at hfx
    exact (SAP.P004a.WH.W2.P.T8_L3.log_ge_densities hν).1 (by simpa [f] using hfx)
