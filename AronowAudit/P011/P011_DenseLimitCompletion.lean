/- Dense quadratic-form probability limit and PSD conservativeness, derived from a finite O(n) variance bound. -/
import AronowAudit.P011.P011_DenseInfrastructure
import AronowAudit.P011.P011_TraceCompletion
namespace AronowAudit.P011.DenseLimitCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
local instance : ENNReal.HolderTriple (4:ENNReal) 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add]⟩

lemma quadratic_centered_memLp {n : ℕ} (m:Model n) (c:ℝ)
    (hb:∀ᵐ y∂m.law,∀i,|weighted m y i-beta m| ≤c)
    (M:Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun y=>quadratic M (centered (weighted m y))) 2 m.law := by
  let : IsProbabilityMeasure m.law:=m.probability
  have hw (i:Fin n):MemLp (fun y=>weighted m y i) 4 m.law:=by
    have hu:=OracleCompletion.U_memLp m c hb 4 i
    have ha:=hu.add (memLp_const (beta m))
    have he : (OracleCompletion.U m i+(fun _=>beta m))=(fun y=>weighted m y i):=by
      funext y
      dsimp [OracleCompletion.U]
      ring
    rw [he] at ha
    exact ha
  have hav:MemLp (fun y=>average (weighted m y)) 4 m.law:=by
    unfold average
    simpa only [div_eq_mul_inv] using (memLp_finsetSum Finset.univ (fun i _=>hw i)).mul_const ((n:ℝ)⁻¹)
  have he (i:Fin n):MemLp (fun y=>centered (weighted m y) i) 4 m.law:=(hw i).sub hav
  have hp (i j:Fin n):MemLp (fun y=>M i j*centered (weighted m y) i*centered (weighted m y) j) 2 m.law:=by
    have hh0:MemLp (fun y=>centered (weighted m y) i*centered (weighted m y) j) 2 m.law:=(he i).mul (he j)
    have hh:=hh0.const_mul (M i j)
    exact (memLp_congr_ae (Eventually.of_forall fun y=>by ring)).mp hh
  unfold quadratic
  exact memLp_finsetSum Finset.univ (fun i _=>memLp_finsetSum Finset.univ (fun j _=>hp i j))

lemma limit_clauses_from_variance (F : Family) (c1 c2 c3 c4 K : ℝ)
    (h : Scaling F c1 c2 c3 c4)
    (M : ∀ k,Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ)
    (hM : ∀ k i j,M k i j=M k j i) (hK : ∀ k,operatorNorm (M k)≤K)
    (hVar : ∃ B : ℝ,0≤B ∧∃ k0 : ℕ,∀ k≥k0,
      var (F.model k) (fun y=>quadratic (M k) (centered (weighted (F.model k) y)))≤B*(F.size k:ℝ)) :
    InProbability F
      (fun k y=>(F.size k:ℝ)*varianceForm (M k) (weighted (F.model k) y)-scaledTrue F k)
      (fun k=>(Matrix.trace ((M k-oracleMatrix (F.model k).G)*covariance (F.model k))+
        quadratic (M k) (delta (F.model k)))/(F.size k:ℝ)) ∧
    ((∀ k,PSD (M k)∧PSD (M k-oracleMatrix (F.model k).G))→
      (∀ k,0≤quadratic (M k) (delta (F.model k))∧
        0≤Matrix.trace ((M k-oracleMatrix (F.model k).G)*covariance (F.model k)))∧
      Conservative F (fun k y=>varianceForm (M k) (weighted (F.model k) y))) := by
  classical
  let (k:ℕ):IsProbabilityMeasure (F.model k).law:=(F.model k).probability
  rcases h with ⟨_,hc1,hc2,_,_,hDep,hBound,hDeg,_,_⟩
  let Q:=fun k y=>quadratic (M k) (centered (weighted (F.model k) y))
  let a:=fun k=>(Matrix.trace (M k*covariance (F.model k))+quadratic (M k) (delta (F.model k)))/(F.size k:ℝ)
  have hn (k:ℕ):0<(F.size k:ℝ):=by exact_mod_cast F.positive k
  have hN:Tendsto (fun k=>(F.size k:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp F.grows
  have hQ (k:ℕ):MemLp (Q k) 2 (F.model k).law:=quadratic_centered_memLp _ c1 (hBound k) (M k)
  have hL2 (k:ℕ):∀i,MemLp (fun y=>weighted (F.model k) y i) 2 (F.model k).law:=
    ProbabilityCompletion.weighted_memLp _ c1 (hBound k)
  have hQn (k:ℕ):MemLp (fun y=>Q k y/(F.size k:ℝ)) 2 (F.model k).law:=by
    simpa only [div_eq_mul_inv] using (hQ k).mul_const ((F.size k:ℝ)⁻¹)
  have hQV:Tendsto (fun k=>ProbabilityTheory.variance (fun y=>Q k y/(F.size k:ℝ)) (F.model k).law) atTop (𝓝 0):=by
    obtain ⟨B,hB,k0,hv⟩:=hVar
    apply squeeze_zero' (Eventually.of_forall fun k=>ProbabilityTheory.variance_nonneg _ _) ?_ (hN.const_div_atTop B)
    filter_upwards [eventually_ge_atTop k0] with k hk
    have he:var (F.model k) (Q k)=ProbabilityTheory.variance (Q k) (F.model k).law:=
      (ProbabilityTheory.variance_eq_integral (hQ k).aemeasurable).symm
    have hv':ProbabilityTheory.variance (Q k) (F.model k).law≤B*(F.size k:ℝ):=by rw [←he];exact hv k hk
    have hid:(fun y=>Q k y/(F.size k:ℝ))=fun y=>(F.size k:ℝ)⁻¹*Q k y:=by funext y;ring
    rw [hid,ProbabilityTheory.variance_const_mul]
    calc
      _ ≤ ((F.size k:ℝ)⁻¹)^2*(B*(F.size k:ℝ)):=mul_le_mul_of_nonneg_left hv' (sq_nonneg _)
      _ = _:=by field_simp <;> ring
  have hmean:=OracleCompletion.rowCP_of_variance (fun k=>(F.model k).law)
    (fun k y=>Q k y/(F.size k:ℝ)) hQn hQV
  have hK0:0≤K:=(norm_nonneg _).trans (hK 0)
  let C:=3*K*(1+c2)*c1^2
  have hE:Tendsto (fun k=>expectation (F.model k) (Q k)/(F.size k:ℝ)-a k) atTop (𝓝 0):=by
    apply squeeze_zero_norm' (Eventually.of_forall fun k=>?_) (hN.const_div_atTop C)
    have hb:=DenseCompletion.finite_expectation_error (F.positive k) (F.model k) c1 (1+c2)
      hc1.le (by linarith) (hDep k) (hBound k) (fun i=>by linarith [hDeg k i]) (M k) (hM k)
    have hb':|expectation (F.model k) (Q k)-
        (Matrix.trace (M k*covariance (F.model k))+quadratic (M k) (delta (F.model k)))|≤C:=by
      exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hK k) (by norm_num : 0≤(3:ℝ))) (by linarith : 0≤1+c2)) (sq_nonneg c1))
    rw [Real.norm_eq_abs]
    dsimp only [a]
    rw [←sub_div,abs_div,abs_of_pos (hn k)]
    exact div_le_div_of_nonneg_right hb' (hn k).le
  have hErr:CoverageCompletion.RowCP (fun k=>(F.model k).law)
      (fun k _=>expectation (F.model k) (Q k)/(F.size k:ℝ)-a k) 0:=
    CoverageCompletion.rowCP_det _ _ _ hE
  have hQA:∀ε>0,Tendsto (fun k=>(F.model k).law.real {y| |Q k y/(F.size k:ℝ)-a k| >ε}) atTop (𝓝 0):=by
    suffices hh:∀ε>0,Tendsto (fun k=>(F.model k).law.real {y | |Q k y/(F.size k:ℝ)-a k-0| >ε}) atTop (𝓝 0) by
      simpa only [sub_zero] using hh
    apply OracleCompletion.row_moving_add_error (fun k=>(F.model k).law)
      (fun k y=>Q k y/(F.size k:ℝ)-expectation (F.model k) (Q k)/(F.size k:ℝ))
      (fun k y=>Q k y/(F.size k:ℝ)-a k) (fun _=>0) ?_ ?_
    · simpa only [expectation,integral_div,sub_zero] using hmean
    · convert hErr using 1 <;> ext k y <;> ring
  let b:=fun k=>(Matrix.trace ((M k-oracleMatrix (F.model k).G)*covariance (F.model k))+
        quadratic (M k) (delta (F.model k)))/(F.size k:ℝ)
  have hid (k:ℕ) (y:Fin (F.size k)→ℝ):
      (F.size k:ℝ)*varianceForm (M k) (weighted (F.model k) y)-scaledTrue F k-b k=
        Q k y/(F.size k:ℝ)-a k:=by
    dsimp [b,Q,a,varianceForm,scaledTrue]
    rw [QuadraticCompletion.beta_variance _ (hL2 k),Matrix.sub_mul,Matrix.trace_sub,
      OracleCompletion.oracle_trace _ (hDep k) (hL2 k)]
    field_simp
    ring
  have hCP:InProbability F
      (fun k y=>(F.size k:ℝ)*varianceForm (M k) (weighted (F.model k) y)-scaledTrue F k) b:=by
    simpa only [InProbability,probability,hid] using hQA
  refine ⟨hCP,?_⟩
  intro hPSD
  have hp (k:ℕ):0≤quadratic (M k) (delta (F.model k))∧
      0≤Matrix.trace ((M k-oracleMatrix (F.model k).G)*covariance (F.model k)):=
    ⟨(hPSD k).1.2 _,DenseTraceCompletion.trace_psd_covariance _ (hL2 k) _ (hPSD k).2⟩
  refine ⟨hp,?_⟩
  intro ε hε
  apply squeeze_zero (fun k=>measureReal_nonneg) (fun k=>?_) (hCP ε hε)
  apply measureReal_mono (μ:=(F.model k).law) ?_ (measure_ne_top _ _)
  intro y hy
  change ε<(F.size k:ℝ)*(var (F.model k) (betaHat (F.model k))-varianceForm (M k) (weighted (F.model k) y)) at hy
  change ε< |(F.size k:ℝ)*varianceForm (M k) (weighted (F.model k) y)-scaledTrue F k-b k|
  have hb:0≤b k:=div_nonneg (add_nonneg (hp k).2 (hp k).1) (hn k).le
  have ha:=neg_le_abs ((F.size k:ℝ)*varianceForm (M k) (weighted (F.model k) y)-scaledTrue F k-b k)
  dsimp [scaledTrue] at ha ⊢
  nlinarith
end
end AronowAudit.P011.DenseLimitCompletion
