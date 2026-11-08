import SAP.P018a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P018a.WH.W2.P.T7_L4

open Finset Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
open SAP.P018a.WH.W2

lemma normalized_fitB_bound (R x a b c : ℝ) (hR : 0 < R)
    (hx0 : 0 ≤ x) (hx : x ≤ 1/(2*(R^2+2)))
    (ha : |a| ≤ R) (hb : |b| ≤ R) (hc : |c| ≤ R) :
    |2*(1-x^2)*(a*c-x*a^2*b)/
        ((1-x^2*a^2)*(1+x^2*(a^2-2)))-2*a*c| ≤
      8*(R^2+R^4*(R^2+2)+R^3)*x := by
  let d := (1-x^2*a^2)*(1+x^2*(a^2-2))
  let F := x^2*a*c+x^4*a^3*c*(a^2-2)-x*a^2*b*(1-x^2)
  have hS : 0 < R^2+2 := by positivity
  have hS2 : 2 ≤ R^2+2 := by nlinarith [sq_nonneg R]
  have hxmul : x*(R^2+2) ≤ 1/2 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2*(R^2+2))).mp hx
    nlinarith
  have hxle1 : x ≤ 1 := by
    have ht := mul_le_mul_of_nonneg_left hS2 hx0
    nlinarith
  have hx2S : x^2*(R^2+2) ≤ 1/2 := by
    calc
      x^2*(R^2+2) = x*(x*(R^2+2)) := by ring
      _ ≤ x*(1/2) := mul_le_mul_of_nonneg_left hxmul hx0
      _ ≤ 1/2 := by nlinarith
  have hA2 : a^2 ≤ R^2 := by
    have hpow := pow_le_pow_left₀ (abs_nonneg a) ha 2
    simpa only [sq_abs] using hpow
  have hA2abs : |a|^2 ≤ R^2 := pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hAdiff : |a^2-2| ≤ R^2+2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg a]
  have hxA : x*|a| ≤ 1/2 := by
    have hAR : |a| ≤ R^2+2 := by nlinarith
    calc
      x*|a| ≤ x*(R^2+2) := mul_le_mul_of_nonneg_left hAR hx0
      _ ≤ 1/2 := hxmul
  have hxAsq : x^2*a^2 = (x*|a|)^2 := by
    rw [← sq_abs a]
    ring
  have hfirst : 1/2 ≤ 1-x^2*a^2 := by
    rw [hxAsq]
    nlinarith [sq_nonneg (x*|a|-1/2)]
  have hsecond : 1/2 ≤ 1+x^2*(a^2-2) := by
    have htemp : x^2*|a^2-2| ≤ 1/2 := by
      calc
        x^2*|a^2-2| ≤ x^2*(R^2+2) := mul_le_mul_of_nonneg_left hAdiff (sq_nonneg x)
        _ ≤ 1/2 := hx2S
    have hlow : -|a^2-2| ≤ a^2-2 := neg_abs_le _
    nlinarith
  have hd : 1/4 ≤ d := by
    dsimp [d]
    calc
      (1:ℝ)/4 = (1/2)*(1/2) := by norm_num
      _ ≤ (1-x^2*a^2)*(1+x^2*(a^2-2)) :=
        mul_le_mul hfirst hsecond (by norm_num) (by linarith)
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have heq :
      2*(1-x^2)*(a*c-x*a^2*b)/d-2*a*c = 2*F/d := by
    dsimp [F,d]
    field_simp [hdne]
    ring
  have hx2 : x^2 ≤ x := by
    have h1x : 0 ≤ 1-x := by linarith
    nlinarith [mul_nonneg hx0 h1x]
  have hx3 : x^3 ≤ x^2 := by
    calc
      x^3 = x^2*x := by ring
      _ ≤ x^2*1 := mul_le_mul_of_nonneg_left hxle1 (sq_nonneg x)
      _ = x^2 := by ring
  have hx4 : x^4 ≤ x^3 := by
    calc
      x^4 = x^3*x := by ring
      _ ≤ x^3*1 := mul_le_mul_of_nonneg_left hxle1 (by positivity)
      _ = x^3 := by ring
  have hterm1 : |x^2*a*c| ≤ x*R^2 := by
    have he : |x^2*a*c| = x^2*((|a|)*(|c|)) := by
      calc
        |x^2*a*c| = (abs (x^2))*(abs a)*(abs c) := by simp only [abs_mul]
        _ = x^2*((|a|)*(|c|)) := by rw [abs_of_nonneg (sq_nonneg x)]; ring
    rw [he]
    calc
      x^2*((abs a)*(abs c)) ≤ x^2*(R*R) :=
        mul_le_mul_of_nonneg_left (mul_le_mul ha hc (abs_nonneg c) hR.le) (sq_nonneg x)
      _ = x^2*R^2 := by ring
      _ ≤ x*R^2 := by
        exact mul_le_mul_of_nonneg_right hx2 (sq_nonneg R)
  have hApow : (abs a)^3 ≤ R^3 := pow_le_pow_left₀ (abs_nonneg a) ha 3
  have hAcpow : (abs a)^3*(abs c) ≤ R^3*R :=
    mul_le_mul hApow hc (abs_nonneg c) (by positivity)
  have hinner2 : (abs a)^3*(abs c)*(abs (a^2-2)) ≤ R^4*(R^2+2) := by
    calc
      (abs a)^3*(abs c)*(abs (a^2-2)) ≤ (R^3*R)*(R^2+2) :=
        mul_le_mul hAcpow hAdiff (abs_nonneg (a^2-2)) (by positivity)
      _ = R^4*(R^2+2) := by ring
  have hterm2 : |x^4*a^3*c*(a^2-2)| ≤ x*R^4*(R^2+2) := by
    have he : |x^4*a^3*c*(a^2-2)| = x^4*((abs a)^3*(abs c)*(abs (a^2-2))) := by
      calc
        |x^4*a^3*c*(a^2-2)| = (abs (x^4))*(abs (a^3))*(abs c)*(abs (a^2-2)) := by
          simp only [abs_mul]
        _ = x^4*((|a|)^3*(|c|)*(|a^2-2|)) := by
          rw [abs_of_nonneg (by positivity : 0 ≤ x^4), abs_pow]
          ring
    rw [he]
    calc
      x^4*((abs a)^3*(abs c)*(abs (a^2-2))) ≤ x^4*(R^4*(R^2+2)) :=
        mul_le_mul_of_nonneg_left hinner2 (by positivity)
      _ ≤ x*(R^4*(R^2+2)) := mul_le_mul_of_nonneg_right (hx4.trans (hx3.trans hx2)) (by positivity)
      _ = x*R^4*(R^2+2) := by ring
  have hlow : 0 ≤ 1-x^2 := by nlinarith [hx2]
  have habdiff : |1-x^2| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [hx2]
  have hinner3 : (abs a)^2*(abs b)*(abs (1-x^2)) ≤ R^3 := by
    calc
      (abs a)^2*(abs b)*(abs (1-x^2)) ≤ (R^2*R)*1 := by
        exact mul_le_mul (mul_le_mul hA2abs hb (abs_nonneg b) (by positivity)) habdiff
          (abs_nonneg (1-x^2)) (by positivity)
      _ = R^3 := by ring
  have hterm3 : |x*a^2*b*(1-x^2)| ≤ x*R^3 := by
    have he : |x*a^2*b*(1-x^2)| = x*((abs a)^2*(abs b)*(abs (1-x^2))) := by
      calc
        |x*a^2*b*(1-x^2)| = (abs x)*(abs (a^2))*(abs b)*(abs (1-x^2)) := by
          simp only [abs_mul]
        _ = x*((abs a)^2*(abs b)*(abs (1-x^2))) := by
          rw [abs_of_nonneg hx0, abs_pow]
          ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hinner3 hx0
  have hF : abs F ≤ x*(R^2+R^4*(R^2+2)+R^3) := by
    dsimp [F]
    calc
      abs (x^2*a*c+x^4*a^3*c*(a^2-2)-x*a^2*b*(1-x^2)) ≤
          |x^2*a*c|+|x^4*a^3*c*(a^2-2)|+|x*a^2*b*(1-x^2)| := by
        calc
          _ = abs ((x^2*a*c+x^4*a^3*c*(a^2-2)) + -(x*a^2*b*(1-x^2))) := by congr 1 <;> ring
          _ ≤ abs (x^2*a*c+x^4*a^3*c*(a^2-2))+abs (-(x*a^2*b*(1-x^2))) := abs_add_le _ _
          _ ≤ (|x^2*a*c|+|x^4*a^3*c*(a^2-2)|)+|x*a^2*b*(1-x^2)| := by
            rw [abs_neg]
            exact add_le_add (abs_add_le _ _) (le_rfl)
      _ ≤ x*R^2+x*R^4*(R^2+2)+x*R^3 := by linarith [hterm1,hterm2,hterm3]
      _ = x*(R^2+R^4*(R^2+2)+R^3) := by ring
  rw [heq, abs_div, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ)), abs_of_pos hdpos]
  have haux : (abs F)*(1/4) ≤ (abs F)*d := mul_le_mul_of_nonneg_left hd (abs_nonneg F)
  have hscale : 2*(abs F)/d ≤ 8*(abs F) := by
    apply (div_le_iff₀ hdpos).2
    nlinarith [haux]
  calc
    2*(abs F)/d ≤ 8*(abs F) := hscale
    _ ≤ 8*(x*(R^2+R^4*(R^2+2)+R^3)) := by nlinarith [hF]
    _ = 8*(R^2+R^4*(R^2+2)+R^3)*x := by ring

lemma fitB_normalized {N : ℕ} (z w : Fin N → ℝ)
    (hz : ∀ i, (z i)^2 = 1) (hN : 2 ≤ N)
    (hgram : (AronowAudit.P018.Dreal N)^2 -
      (AronowAudit.P018.Wave1.TailBSign.tb05_T z)^2 ≠ 0) :
    (N : ℝ) * AronowAudit.P018.Wave1.TailBSign.tb05_fitB z w =
      2 * (1 - (Real.sqrt (N : ℝ))⁻¹^2) *
        (((∑ i, z i) / Real.sqrt N) * ((∑ i, z i*w i) / Real.sqrt N) -
          (Real.sqrt (N : ℝ))⁻¹ * ((∑ i, z i) / Real.sqrt N)^2 *
            ((∑ i, w i) / Real.sqrt N)) /
        ((1 - (Real.sqrt (N : ℝ))⁻¹^2 * ((∑ i, z i) / Real.sqrt N)^2) *
          (1 + (Real.sqrt (N : ℝ))⁻¹^2 * (((∑ i, z i) / Real.sqrt N)^2 - 2))) := by
  let q : ℝ := Real.sqrt N
  let x : ℝ := q⁻¹
  let s : ℝ := ∑ i, z i
  let u : ℝ := ∑ i, w i
  let v : ℝ := ∑ i, z i*w i
  let a : ℝ := s/q
  let b : ℝ := u/q
  let c : ℝ := v/q
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hq : q ≠ 0 := (Real.sqrt_pos.2 hN0).ne'
  have hq2 : q^2 = (N : ℝ) := by
    dsimp [q]
    exact Real.sq_sqrt (by positivity)
  have hD : AronowAudit.P018.Dreal N = q^2*(q^2-1)/2 := by
    unfold AronowAudit.P018.Dreal
    rw [hq2]
  have hs : (∑ i, z i) = q*a := by
    dsimp [a, s]
    field_simp [hq]
  have hu : (∑ i, w i) = q*b := by
    dsimp [b, u]
    field_simp [hq]
  have hv : (∑ i, z i*w i) = q*c := by
    dsimp [c, v]
    field_simp [hq]
  have hT : AronowAudit.P018.Wave1.TailBSign.tb05_T z = (q^2*a^2-q^2)/2 := by
    rw [AronowAudit.P018.Wave1.TailBSign.tb05_T_formula z hz, hs]
    simp only [mul_pow, hq2]
  have hdenfact : (AronowAudit.P018.Dreal N)^2 -
      (AronowAudit.P018.Wave1.TailBSign.tb05_T z)^2 =
      (q^8/4)*((1-x^2*a^2)*(1+x^2*(a^2-2))) := by
    rw [hD, hT]
    dsimp [x]
    field_simp [hq]
    rw [hq2]
    ring
  have hnorm : (1-x^2*a^2)*(1+x^2*(a^2-2)) ≠ 0 := by
    intro h
    apply hgram
    rw [hdenfact, h]
    ring
  change (N : ℝ) * AronowAudit.P018.Wave1.TailBSign.tb05_fitB z w =
      2*(1-x^2)*(a*c-x*a^2*b)/((1-x^2*a^2)*(1+x^2*(a^2-2)))
  rw [AronowAudit.P018.Wave1.TailBSign.tb05_fitB, hD, hT, hs, hu, hv, hq2]
  dsimp [x]
  field_simp [hq, hgram, hnorm]
  <;> simp only [hq2]
  <;> ring

lemma fitB_box_bound (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (z w : Fin N → ℝ),
      (∀ i, (z i)^2 = 1) → (∀ i, (w i)^2 = 1) → 2 ≤ N →
      (Real.sqrt N)⁻¹ ≤ 1/(2*(R^2+2)) →
      |(∑ i,z i)/Real.sqrt N| ≤ R → |(∑ i,w i)/Real.sqrt N| ≤ R →
      |(∑ i,z i*w i)/Real.sqrt N| ≤ R →
      |(N:ℝ)*AronowAudit.P018.Wave1.TailBSign.tb05_fitB z w -
        2*((∑ i,z i)/Real.sqrt N)*((∑ i,z i*w i)/Real.sqrt N)| ≤ C/Real.sqrt N := by
  let C : ℝ := 8*(R^2+R^4*(R^2+2)+R^3)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N z w hz hw hN hx ha hb hc
  have hG := AronowAudit.P018.Wave1.TailBSign.tb05_gram_nonsingular_on_box
    z hz hN R hR.le hx ha
  rw [fitB_normalized z w hz hN hG]
  have h := normalized_fitB_bound R (Real.sqrt (N:ℝ))⁻¹
    ((∑ i,z i)/Real.sqrt N) ((∑ i,w i)/Real.sqrt N)
    ((∑ i,z i*w i)/Real.sqrt N) hR (inv_nonneg.2 (Real.sqrt_nonneg _)) hx ha hb hc
  simpa [C, div_eq_mul_inv, mul_comm] using h

lemma sample_slope_fitB {N : ℕ} (ω : Fin N → Bool × Bool)
    (hG : (AronowAudit.P018.Dreal N)^2 -
      (AronowAudit.P018.Wave1.TailBSign.tb05_T
        (AronowAudit.P018.Wave1.TailBSign.tb05_z ω))^2 ≠ 0) :
    sampleOLS (design signPairKernel ω) (response signPairKernel ω) 1 =
      AronowAudit.P018.Wave1.TailBSign.tb05_fitB
        (AronowAudit.P018.Wave1.TailBSign.tb05_z ω)
        (AronowAudit.P018.Wave1.TailBSign.tb05_w ω) := by
  have hz : ∀ i, (AronowAudit.P018.Wave1.TailBSign.tb05_z ω i)^2 = 1 := by
    intro i
    exact AronowAudit.P018.Wave1.printed_sign_square (ω i).1
  have h := AronowAudit.P018.Wave1.TailBSign.tb05_sample_ols
    (AronowAudit.P018.Wave1.TailBSign.tb05_z ω)
    (AronowAudit.P018.Wave1.TailBSign.tb05_w ω) hz hG
  have h1 := congrFun h (1 : Fin 2)
  have hX : design signPairKernel ω =
      AronowAudit.P018.Wave1.TailBSign.tb05_design
        (AronowAudit.P018.Wave1.TailBSign.tb05_z ω) := by
    funext d
    have ends := SAP.P018a.Bridge.endpoints_agree d
    simp [design, signPairKernel, SAP.P018a.signValue, AronowAudit.P018.signValue,
      AronowAudit.P018.Wave1.TailBSign.tb05_design,
      AronowAudit.P018.Wave1.TailBSign.tb05_z, ends.1, ends.2]
  have hY : response signPairKernel ω =
      AronowAudit.P018.Wave1.TailBSign.tb05_response
        (AronowAudit.P018.Wave1.TailBSign.tb05_w ω) := by
    funext d
    have ends := SAP.P018a.Bridge.endpoints_agree d
    simp [response, signPairKernel, SAP.P018a.signValue, AronowAudit.P018.signValue,
      AronowAudit.P018.Wave1.TailBSign.tb05_response,
      AronowAudit.P018.Wave1.TailBSign.tb05_w, ends.1, ends.2]
  rw [hX, hY]
  exact h1

lemma model_slope_box_eventual (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ ω : Fin N → Bool × Bool,
      |(∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i)/Real.sqrt N| ≤ R →
      |(∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_w ω i)/Real.sqrt N| ≤ R →
      |(∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i*
        AronowAudit.P018.Wave1.TailBSign.tb05_w ω i)/Real.sqrt N| ≤ R →
      |(N:ℝ)*sampleOLS (design signPairKernel ω) (response signPairKernel ω) 1 -
        2*((∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i)/Real.sqrt N)*
          ((∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i*
            AronowAudit.P018.Wave1.TailBSign.tb05_w ω i)/Real.sqrt N)| ≤ C/Real.sqrt N := by
  obtain ⟨C,hC,hbound⟩ := fitB_box_bound R hR
  refine ⟨C,hC,?_⟩
  have hi : Tendsto (fun N : ℕ => (Real.sqrt (N:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hd : (0:ℝ) < 1/(2*(R^2+2)) := by positivity
  filter_upwards [eventually_ge_atTop 2, hi.eventually (gt_mem_nhds hd)] with N hN hx
  intro ω ha hb hc
  have hz : ∀ i, (AronowAudit.P018.Wave1.TailBSign.tb05_z ω i)^2 = 1 := by
    intro i
    exact AronowAudit.P018.Wave1.printed_sign_square (ω i).1
  have hw : ∀ i, (AronowAudit.P018.Wave1.TailBSign.tb05_w ω i)^2 = 1 := by
    intro i
    exact AronowAudit.P018.Wave1.printed_sign_square (ω i).2
  have hG := AronowAudit.P018.Wave1.TailBSign.tb05_gram_nonsingular_on_box
    (AronowAudit.P018.Wave1.TailBSign.tb05_z ω) hz hN R hR.le hx.le ha
  have hfit := sample_slope_fitB ω hG
  have h := hbound N (AronowAudit.P018.Wave1.TailBSign.tb05_z ω)
    (AronowAudit.P018.Wave1.TailBSign.tb05_w ω) hz hw hN hx.le ha hb hc
  rw [hfit]
  exact h

end SAP.P018a.WH.W2.P.T7_L4

open Finset Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
open SAP.P018a.WH.W2

theorem SAP.P018a.WH.W2.T7_L4_proof : SAP.P018a.WH.W2.T7_L4 := by
  letI : IsProbabilityMeasure SAP.P018a.fairLaw := by
    unfold SAP.P018a.fairLaw
    infer_instance
  letI : IsProbabilityMeasure SAP.P018a.signPairKernel.μ := by
    dsimp [SAP.P018a.signPairKernel]
    infer_instance
  letI (N : ℕ) : IsProbabilityMeasure (SAP.P018a.unitSampleLaw SAP.P018a.signPairKernel N) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => SAP.P018a.signPairKernel.μ))
    infer_instance
  change AronowAudit.P018.inProbability (unitSampleLaw signPairKernel) (fun N ω =>
    (N : ℝ)*sampleOLS (design signPairKernel ω) (response signPairKernel ω) 1 -
      2*((∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i)/Real.sqrt N)*
        ((∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i*
          AronowAudit.P018.Wave1.TailBSign.tb05_w ω i)/Real.sqrt N))
  intro ε hε
  rw [Metric.tendsto_nhds]
  intro δ hδ
  let R : ℝ := 3/δ+1
  have hR1 : 1 < R := by
    have hp : (0:ℝ) < 3/δ := by positivity
    dsimp [R]
    linarith
  have hR : 0 < R := by linarith
  have hδR : δ*R=3+δ := by dsimp [R]; field_simp <;> ring
  have htail : 3/R^2 < δ := by
    apply (div_lt_iff₀ (sq_pos_of_pos hR)).2
    have hp := mul_pos (mul_pos hδ hR) (sub_pos.2 hR1)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := SAP.P018a.WH.W2.P.T7_L4.model_slope_box_eventual R hR
  have hi : Tendsto (fun N : ℕ => C/Real.sqrt N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul C
  filter_upwards [hbound,hi.eventually (gt_mem_nhds hε),eventually_ge_atTop 1]
    with N hb hs hN
  have hsub : {ω | ε ≤ ‖(N:ℝ)*sampleOLS (design signPairKernel ω)
      (response signPairKernel ω) 1 -
      2*((∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i)/Real.sqrt N)*
        ((∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i*
          AronowAudit.P018.Wave1.TailBSign.tb05_w ω i)/Real.sqrt N)‖} ⊆
      AronowAudit.P018.Wave1.TailBSign.tb05_badBox N R := by
    intro ω hω
    by_contra hn
    have hg :
        |(∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i)/Real.sqrt N| ≤ R ∧
        |(∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_w ω i)/Real.sqrt N| ≤ R ∧
        |(∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i*
          AronowAudit.P018.Wave1.TailBSign.tb05_w ω i)/Real.sqrt N| ≤ R := by
      simpa only [AronowAudit.P018.Wave1.TailBSign.tb05_badBox, Set.mem_setOf_eq,
        not_or, not_lt] using hn
    have he := hb ω hg.1 hg.2.1 hg.2.2
    change ε ≤ |(N:ℝ)*sampleOLS (design signPairKernel ω)
      (response signPairKernel ω) 1 -
      2*((∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i)/Real.sqrt N)*
        ((∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i*
          AronowAudit.P018.Wave1.TailBSign.tb05_w ω i)/Real.sqrt N)| at hω
    have he' : |(N:ℝ)*sampleOLS (design signPairKernel ω)
        (response signPairKernel ω) 1 -
        2*((∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i)/Real.sqrt N)*
          ((∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i*
            AronowAudit.P018.Wave1.TailBSign.tb05_w ω i)/Real.sqrt N)| ≤ C/Real.sqrt N := he
    have hs' : C/Real.sqrt N < ε := hs
    linarith
  have hp : (unitSampleLaw signPairKernel N
      {ω | ε ≤ ‖(N:ℝ)*sampleOLS (design signPairKernel ω)
        (response signPairKernel ω) 1 -
        2*((∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i)/Real.sqrt N)*
          ((∑ i,AronowAudit.P018.Wave1.TailBSign.tb05_z ω i*
            AronowAudit.P018.Wave1.TailBSign.tb05_w ω i)/Real.sqrt N)‖}).toReal < δ := by
    calc
      _ ≤ (unitSampleLaw signPairKernel N
          (AronowAudit.P018.Wave1.TailBSign.tb05_badBox N R)).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ ≤ 3/R^2 := AronowAudit.P018.Wave1.TailBSign.tb05_box_probability
        (by omega) R hR
      _ < δ := htail
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] using hp
