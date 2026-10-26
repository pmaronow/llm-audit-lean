import AronowAudit.P026.P026_FiniteDesign
namespace AronowAudit.P026.VarianceStability
open Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000

lemma expectation_abs_bound {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (D : Design Ω I ℝ) (hD : probabilityDesign D) (f : Ω → ℝ) (C : ℝ)
    (h : ∀ w, |f w| ≤ C) : |expectation D f| ≤ C := by
  calc
    |expectation D f| ≤ ∑ w, |D.weight w*f w| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ w, D.weight w*|f w| := by
      apply sum_congr rfl
      intro w _
      rw [abs_mul,abs_of_nonneg (hD.1 w)]
    _ ≤ ∑ w, D.weight w*C := sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (h w) (hD.1 w))
    _ = C := by rw [←sum_mul,hD.2,one_mul]

theorem variance_difference_bound {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (D : Design Ω I ℝ) (hD : probabilityDesign D) (f g : Ω → ℝ)
    (M δ : ℝ) (hM : 0≤M) (hδ : 0≤δ)
    (hf : ∀ w, |f w|≤M) (hg : ∀ w, |g w|≤M)
    (hd : ∀ w, |f w-g w|≤δ) :
    |variance D f-variance D g|≤4*M*δ := by
  have hEf := expectation_abs_bound D hD f M hf
  have hEg := expectation_abs_bound D hD g M hg
  have hEd := expectation_abs_bound D hD (fun w => f w-g w) δ hd
  rw [expectation_sub] at hEd
  have hsum : |expectation D f+expectation D g|≤2*M :=
    (abs_add_le _ _).trans (by linarith)
  have hsquare : ∀ w, |f w*f w-g w*g w|≤2*M*δ := by
    intro w
    have hh : |f w+g w|≤2*M := (abs_add_le _ _).trans (by linarith [hf w,hg w])
    calc
      |f w*f w-g w*g w|=|f w-g w| *|f w+g w| := by rw [←abs_mul];congr 1;ring
      _ ≤ δ*(2*M) := mul_le_mul (hd w) hh (abs_nonneg _) hδ
      _ = 2*M*δ := by ring
  have hEs := expectation_abs_bound D hD (fun w => f w*f w-g w*g w) (2*M*δ) hsquare
  rw [expectation_sub] at hEs
  have hmeans : |(expectation D f)^2-(expectation D g)^2|≤2*M*δ := by
    calc
      |(expectation D f)^2-(expectation D g)^2|=
          |expectation D f-expectation D g| *|expectation D f+expectation D g| := by
        rw [←abs_mul];congr 1;ring
      _ ≤ δ*(2*M) := mul_le_mul hEd hsum (abs_nonneg _) hδ
      _ = 2*M*δ := by ring
  have hid : variance D f-variance D g=
      (expectation D (fun w => f w*f w)-expectation D (fun w => g w*g w))-
        ((expectation D f)^2-(expectation D g)^2) := by
    unfold variance covariance
    ring
  rw [hid]
  exact (abs_sub _ _).trans (by linarith)

end
end AronowAudit.P026.VarianceStability
