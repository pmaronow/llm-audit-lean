import AronowAudit.P018.Wave1.Gap.TailBSignAlgebra
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! A deterministic uniform remainder for the second-order sign slope. -/
noncomputable section
namespace AronowAudit.P018.Wave1.TailBSign
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- Arguments are inverse square-root sample size, and the three normalized sums. -/
def tb05_lambda (p : Fin 4 → ℝ) : ℝ := p 0^2*(p 1^2-1)/(1-p 0^2)
def tb05_bbar (p : Fin 4 → ℝ) : ℝ :=
  2*p 0*p 1*(p 3-p 0*p 1*p 2)/((1-p 0^2)*(1-tb05_lambda p^2))
def tb05_alpha (p : Fin 4 → ℝ) : ℝ := 2*p 0*p 2-tb05_lambda p*p 0*tb05_bbar p
def tb05_nodeA (p : Fin 4 → ℝ) : ℝ :=
  -tb05_lambda p*p 2+tb05_alpha p*p 0*p 1^2-
    tb05_bbar p*(1-p 0^2+tb05_lambda p*p 0^2)
def tb05_nodeB (p : Fin 4 → ℝ) : ℝ :=
  p 3-tb05_alpha p*p 1+p 0*tb05_bbar p*tb05_lambda p*p 1
def tb05_nodeC (p : Fin 4 → ℝ) : ℝ :=
  -p 0*(2+(p 1^2-1)*(1-2*p 0^2)/(1-p 0^2))
def tb05_nodeNorm (p : Fin 4 → ℝ) : ℝ :=
  tb05_nodeA p^2+tb05_nodeB p^2+tb05_nodeC p^2+p 1^2+
  2*p 0*((tb05_nodeA p*tb05_nodeB p+tb05_nodeC p*p 1)*p 1+
    (tb05_nodeA p*tb05_nodeC p+tb05_nodeB p*p 1)*p 2+
    (tb05_nodeA p*p 1+tb05_nodeB p*tb05_nodeC p)*p 3)
def tb05_edgeNorm (p : Fin 4 → ℝ) : ℝ :=
  (1+tb05_lambda p^2)*(1+p 0^2*(p 2^2-2)-
    2*tb05_alpha p*p 0*(1-p 0^2)*p 2-
    2*(p 0*tb05_bbar p)*p 0^2*(p 1*p 3-p 0*p 2)+
    (tb05_alpha p^2+(p 0*tb05_bbar p)^2)*(1-p 0^2)/2+
    tb05_alpha p*(p 0*tb05_bbar p)*p 0^2*(p 1^2-1)) -
  2*tb05_lambda p*(p 0^2*(p 1^2+p 3^2-2)-
    2*tb05_alpha p*p 0^2*(p 1*p 3-p 0*p 2)-
    2*(p 0*tb05_bbar p)*p 0*(1-p 0^2)*p 2+
    (tb05_alpha p^2+(p 0*tb05_bbar p)^2)*p 0^2*(p 1^2-1)/2+
    tb05_alpha p*(p 0*tb05_bbar p)*(1-p 0^2))
def tb05_normalizedVariance (p : Fin 4 → ℝ) : ℝ :=
  4*(tb05_nodeNorm p-tb05_edgeNorm p)/((1-p 0^2)^2*(1-tb05_lambda p^2)^2)

theorem tb05_normalized_at_zero (z w v : ℝ) :
    tb05_normalizedVariance ![0,z,w,v] = 4*(z^2+v^2-1) := by
  norm_num [tb05_normalizedVariance,tb05_nodeNorm,tb05_edgeNorm,tb05_nodeA,
    tb05_nodeB,tb05_nodeC,tb05_alpha,tb05_bbar,tb05_lambda]
  ring

/-- A compact box around the limiting inverse-size coordinate has no singular bread. -/
theorem tb05_denominators (R : ℝ) (hR : 0 ≤ R) (p : Fin 4 → ℝ)
    (hx : |p 0| ≤ 1/(2*(R^2+2))) (hz : |p 1| ≤ R) :
    1-p 0^2 ≠ 0 ∧ 1-tb05_lambda p^2 ≠ 0 := by
  let d : ℝ := 1/(2*(R^2+2))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdm : d*(R^2+2)=1/2 := by dsimp [d]; field_simp
  have hd2 : d ≤ 1/2 := by nlinarith [sq_nonneg R]
  have hx2 : p 0^2 ≤ d^2 := by
    have := sq_le_sq₀ (abs_nonneg (p 0)) hd.le |>.2 hx
    simpa only [sq_abs] using this
  have hz2 : p 1^2 ≤ R^2 := by
    have := sq_le_sq₀ (abs_nonneg (p 1)) hR |>.2 hz
    simpa only [sq_abs] using this
  have hm : p 0^2*(R^2+2) ≤ 1/4 := by
    calc
      _ ≤ d^2*(R^2+2) := mul_le_mul_of_nonneg_right hx2 (by positivity)
      _ = d/2 := by nlinarith [hdm]
      _ ≤ 1/4 := by linarith
  have hxsmall : p 0^2 ≤ 1/8 := by nlinarith [sq_nonneg (p 0),sq_nonneg R]
  have hl : -(1-p 0^2) < p 0^2*(p 1^2-1) := by
    nlinarith [mul_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))]
  have hu : p 0^2*(p 1^2-1) < 1-p 0^2 := by
    have := mul_le_mul_of_nonneg_left hz2 (sq_nonneg (p 0))
    nlinarith
  have hden : 0 < 1-p 0^2 := by linarith
  have hll : -1 < tb05_lambda p := by
    unfold tb05_lambda
    exact (lt_div_iff₀ hden).2 (by nlinarith [hl])
  have hlu : tb05_lambda p < 1 := by
    unfold tb05_lambda
    exact (div_lt_iff₀ hden).2 (by nlinarith [hu])
  constructor
  · exact ne_of_gt hden
  · have : tb05_lambda p^2 < 1 := (sq_lt_one_iff_abs_lt_one _).2 (abs_lt.2 ⟨hll,hlu⟩)
    linarith

/-- The whole rational second-order formula, uniformly over bounded normalized sums,
has an O(1/sqrt N) deterministic remainder. The constant depends only on the box. -/
theorem tb05_bounded_normalized_remainder (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z w v : ℝ,
      |x| ≤ 1/(2*(R^2+2)) → |z| ≤ R → |w| ≤ R → |v| ≤ R →
      |tb05_normalizedVariance ![x,z,w,v]-4*(z^2+v^2-1)| ≤ C*|x| := by
  let d : ℝ := 1/(2*(R^2+2))
  let lo : Fin 4 → ℝ := ![-d,-R,-R,-R]
  let hi : Fin 4 → ℝ := ![d,R,R,R]
  let s := Set.Icc lo hi
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hden (p : Fin 4 → ℝ) (hp : p ∈ s) :
      1-p 0^2 ≠ 0 ∧ 1-tb05_lambda p^2 ≠ 0 := by
    apply tb05_denominators R hR p
    · exact abs_le.2 ⟨hp.1 0,hp.2 0⟩
    · exact abs_le.2 ⟨hp.1 1,hp.2 1⟩
  have hc : ContDiffOn ℝ 1 tb05_normalizedVariance s := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    have h0 := (hden p hp).1
    have h1 := (hden p hp).2
    have hL : ContDiffAt ℝ 1 tb05_lambda p := by
      unfold tb05_lambda
      fun_prop (disch := assumption)
    have hmul := mul_ne_zero h0 h1
    have hpow := mul_ne_zero (pow_ne_zero 2 h0) (pow_ne_zero 2 h1)
    unfold tb05_normalizedVariance tb05_nodeNorm tb05_edgeNorm tb05_nodeA
      tb05_nodeB tb05_nodeC tb05_alpha tb05_bbar
    fun_prop (disch := first | assumption | norm_num)
  obtain ⟨K,hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc lo hi) isCompact_Icc
  refine ⟨K, K.coe_nonneg, ?_⟩
  intro x z w v hx hz hw hv
  have hp : ![x,z,w,v] ∈ s := by
    constructor <;> intro i <;> fin_cases i <;>
      simp_all [s,lo,hi,d,abs_le]
  have hq : ![0,z,w,v] ∈ s := by
    constructor <;> intro i <;> fin_cases i <;>
      simp_all [s,lo,hi,d,abs_le]
  have ht := hK.dist_le_mul _ hp _ hq
  have hb : dist (![x,z,w,v] : Fin 4 → ℝ) ![0,z,w,v] ≤ |x| := by
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg x)).2
    intro i
    fin_cases i <;> simp
  rw [Real.dist_eq,tb05_normalized_at_zero] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left hb K.coe_nonneg)

end AronowAudit.P018.Wave1.TailBSign
