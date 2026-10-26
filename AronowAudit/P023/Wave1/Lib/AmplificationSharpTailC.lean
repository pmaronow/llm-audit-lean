import AronowAudit.P023.Wave1.Lib.ResidualSharpIntegralTailC
import AronowAudit.P023.Wave1.Lib.AmplificationDivergenceTailC

/-! The exact L1 coefficient and bounded sharp logarithmic amplification remainder. -/
namespace AronowAudit.P023.Wave1
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
set_option maxHeartbeats 600000

/-- The exact coefficient for the actual residual, with a fixed quantified remainder. -/
theorem uniform_residual_L1_asymptotic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      |expectation uniformMargins (fun x => |popResidual uniformMargins (2*n-1) x|) -
        Real.log (n : ℝ)/(Real.pi^2*(n : ℝ))| ≤ C/(n : ℝ) := by
  obtain ⟨C,hC,hcos⟩ := tc11_absolute_cosine_log_bound
  let K : ℝ := 2+(Real.pi+4)/Real.pi+Real.pi+Real.pi^2
  let B : ℝ := C/(2*Real.pi)+|Real.log (Real.pi/2)|/Real.pi^2
  refine ⟨K+B,by dsimp [K,B]; positivity,?_⟩
  intro n hn
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let a : ℝ := 1/(n : ℝ)
  let b : ℝ := Real.pi/2
  let k : ℝ := 2*(n : ℝ)+1/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hab : a ≤ b := by
    have hhalf : a ≤ 1/2 := by dsimp [a]; exact one_div_le_one_div_of_le (by norm_num) hn2
    dsimp [b]
    linarith [Real.two_le_pi]
  have hka : 1 ≤ k*a := by dsimp [k,a]; field_simp; nlinarith
  have hcb : |(∫ t in a..b, |Real.cos (k*t)|/t) - (2/Real.pi)*Real.log (b/a)| ≤ C := by
    exact (hcos a b k ha hab hk).trans
      (div_le_self hC hka)
  have hD : (∫ t in a..b, tc11_leadingDensity n t) =
      (∫ t in a..b, |Real.cos (k*t)|/t)/(2*Real.pi*(n : ℝ)) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [tc11_leadingDensity,k]
    ring
  have hlog : Real.log (b/a) = Real.log b + Real.log (n : ℝ) := by
    rw [Real.log_div hb.ne' ha.ne']
    dsimp [a]
    rw [one_div, Real.log_inv]
    ring
  have he : (∫ t in a..b, tc11_leadingDensity n t) - Real.log (n : ℝ)/(Real.pi^2*(n : ℝ)) =
      ((∫ t in a..b, |Real.cos (k*t)|/t) - (2/Real.pi)*Real.log (b/a))/(2*Real.pi*(n : ℝ)) +
        Real.log b/(Real.pi^2*(n : ℝ)) := by
    rw [hD,hlog]
    field_simp
    ring
  have hmodel : |(∫ t in a..b, tc11_leadingDensity n t) -
      Real.log (n : ℝ)/(Real.pi^2*(n : ℝ))| ≤ B/(n : ℝ) := by
    rw [he]
    calc
      _ ≤ |((∫ t in a..b, |Real.cos (k*t)|/t) - (2/Real.pi)*Real.log (b/a))/(2*Real.pi*(n : ℝ))| +
          |Real.log b/(Real.pi^2*(n : ℝ))| := abs_add_le _ _
      _ ≤ C/(2*Real.pi*(n : ℝ)) + |Real.log b|/(Real.pi^2*(n : ℝ)) := by
        rw [abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi*(n : ℝ)),
          abs_div,abs_of_pos (by positivity : 0 < Real.pi^2*(n : ℝ))]
        gcongr
      _ = _ := by dsimp [B,b]; ring
  have hlead := tc11_l1_leading_density n hn
  have h := (abs_sub_le (expectation uniformMargins (fun x => |popResidual uniformMargins (2*n-1) x|))
    (∫ t in a..b, tc11_leadingDensity n t) (Real.log (n : ℝ)/(Real.pi^2*(n : ℝ)))).trans
      (add_le_add hlead hmodel)
  exact h.trans_eq (by dsimp [K]; ring)

/-- Wallis controls the inverse variance to bounded absolute error, not merely relative error. -/
theorem tc11_inverse_variance_bounds (n : ℕ) (hn : 1 ≤ n) :
    4*Real.pi*(n : ℝ) ≤ 1/residualVariance uniformMargins (2*n-1) ∧
    1/residualVariance uniformMargins (2*n-1) ≤ 4*Real.pi*((n : ℝ)+1/2) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hv : 0 < residualVariance uniformMargins (2*n-1) :=
    (uniform_projection_variance (2*n-1) (by omega)).2.2.2
  have hvhi := tc09_variance_upper n hn
  have hvlo : 1/(4*Real.pi*((n : ℝ)+1/2)) ≤ residualVariance uniformMargins (2*n-1) := by
    rw [tc09_variance_exact n hn]
    have h := div_le_div_of_nonneg_right (central_binomial_wallis_bounds n hn).1 (by norm_num : (0 : ℝ) ≤ 4)
    exact (show 1/(4*Real.pi*((n : ℝ)+1/2)) = (1/(Real.pi*((n : ℝ)+1/2)))/4 by field_simp).trans_le h
  constructor
  · apply (le_div_iff₀ hv).mpr
    have h := (le_div_iff₀ (by positivity : 0 < 4*Real.pi*(n : ℝ))).mp hvhi
    nlinarith
  · apply (div_le_iff₀ hv).mpr
    have h := (div_le_iff₀ (by positivity : 0 < 4*Real.pi*((n : ℝ)+1/2))).mp hvlo
    nlinarith

/-- Sharp logarithmic amplification along all odd degrees. -/
theorem tc11_odd_amplification_sharp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      |amplification uniformMargins (2*n-1) - (4/Real.pi)*Real.log (n : ℝ)| ≤ C := by
  obtain ⟨C,hC,hL1⟩ := uniform_residual_L1_asymptotic
  refine ⟨6*Real.pi*C+2/Real.pi,by positivity,?_⟩
  intro n hn
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  let v := residualVariance uniformMargins (2*n-1)
  let E := expectation uniformMargins (fun x => |popResidual uniformMargins (2*n-1) x|)
  let A := Real.log (n : ℝ)/(Real.pi^2*(n : ℝ))
  have hv : 0 < v := (uniform_projection_variance (2*n-1) (by omega)).2.2.2
  obtain ⟨hlo,hhi⟩ := tc11_inverse_variance_bounds n (by omega)
  have herr : |1/v-4*Real.pi*(n : ℝ)| ≤ 2*Real.pi := by
    apply abs_le.mpr
    dsimp [v]
    constructor <;> linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlogle : Real.log (n : ℝ) ≤ n := (Real.log_le_sub_one_of_pos hp).trans (by linarith)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hfirst : |(E-A)/v| ≤ 6*Real.pi*C := by
    rw [abs_div,abs_of_pos hv]
    calc
      _ ≤ (C/(n : ℝ))/v := div_le_div_of_nonneg_right (hL1 n hn) hv.le
      _ = (C/(n : ℝ))*(1/v) := by ring
      _ ≤ (C/(n : ℝ))*(4*Real.pi*((n : ℝ)+1/2)) := mul_le_mul_of_nonneg_left hhi (by positivity)
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hp).mpr
        nlinarith [mul_nonneg (by positivity : 0 ≤ Real.pi*C) (sub_nonneg.mpr hn1)]
  have hsecond : |A*(1/v-4*Real.pi*(n : ℝ))| ≤ 2/Real.pi := by
    rw [abs_mul,abs_of_nonneg hA]
    calc
      _ ≤ A*(2*Real.pi) := mul_le_mul_of_nonneg_left herr hA
      _ ≤ _ := by
        dsimp [A]
        rw [div_mul_eq_mul_div]
        apply (div_le_div_iff₀ (by positivity : 0 < Real.pi^2*(n : ℝ)) Real.pi_pos).mpr
        nlinarith [mul_le_mul_of_nonneg_left hlogle (by positivity : 0 ≤ 2*Real.pi^2)]
  have he : amplification uniformMargins (2*n-1)-(4/Real.pi)*Real.log (n : ℝ) =
      (E-A)/v + A*(1/v-4*Real.pi*(n : ℝ)) := by
    dsimp [amplification,E,A,v]
    field_simp
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-- The exact bounded remainder around `(4/pi) log J` at every large degree. -/
theorem uniform_amplification_sharp_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ J₀, ∀ J ≥ J₀, 1 ≤ J →
      |amplification uniformMargins J - (4/Real.pi)*Real.log J| ≤ C := by
  obtain ⟨C,hC,hodd⟩ := tc11_odd_amplification_sharp
  refine ⟨C+8/Real.pi,by positivity,3,?_⟩
  intro J hJ3 hJ
  let n := (J+1)/2
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hnJ : n ≤ J := by dsimp [n]; omega
  have hJn : J ≤ 2*n := by dsimp [n]; omega
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hnc : (n : ℝ) ≤ J := by exact_mod_cast hnJ
  have hJc : (J : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast hJn
  have hlog : |Real.log (J : ℝ)-Real.log (n : ℝ)| ≤ 2 := by
    have hl := Real.log_le_log hnp hnc
    have hratio : (J : ℝ)/(n : ℝ) ≤ 2 := (div_le_iff₀ hnp).mpr hJc
    have hratioP : 0 < (J : ℝ)/(n : ℝ) := div_pos hJp hnp
    rw [abs_of_nonneg (sub_nonneg.mpr hl), ← Real.log_div hJp.ne' hnp.ne']
    exact (Real.log_le_sub_one_of_pos hratioP).trans (by linarith)
  have hmain := hodd n hn
  rw [← tc09_uniform_amplification_index J hJ] at hmain
  have he : amplification uniformMargins J - (4/Real.pi)*Real.log (J : ℝ) =
      (amplification uniformMargins J - (4/Real.pi)*Real.log (n : ℝ)) +
        (4/Real.pi)*(Real.log (n : ℝ)-Real.log (J : ℝ)) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_pos (by positivity : 0 < (4/Real.pi : ℝ)),abs_sub_comm (Real.log (n : ℝ))]
  exact add_le_add hmain ((mul_le_mul_of_nonneg_left hlog (by positivity)).trans_eq (by ring))

end
end AronowAudit.P023.Wave1
