import AronowAudit.P015.P015_MatrixDefinitions
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import AronowAudit.P015.P015_ConvergenceCompletion
namespace AronowAudit.P015.OLSCompletion
noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators Topology
open ConvergenceCompletion
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

lemma normalized_ols {N Q : Type*} [Fintype N] [Fintype Q] [DecidableEq Q]
    (V : Matrix N Q ℝ) (Y : N → ℝ) (c : ℝ) (hc:c≠0) :
    ols V Y=(c • (V.transpose*V))⁻¹.mulVec (c • V.transpose.mulVec Y) := by
  unfold ols
  rw [inverse_smul_real _ _ hc,Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul,
    inv_mul_cancel₀ hc,one_smul]

/-- Actual finite-sample OLS is a continuous function of its empirical Gram and
cross moments at every nonsingular population Gram matrix. The totalized
inverse also defines OLS for singular sample matrices. -/
lemma ols_moment_limit {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q] [DecidableEq Q]
    (P : Measure Ω) (V : ℕ → Ω → Q → ℝ) (Y : ℕ → Ω → ℝ)
    (G : Matrix Q Q ℝ) (b : Q → ℝ) (hdet:G.det≠0)
    (hG : ∀j k,TendstoInMeasure P (fun n s=>(∑i:Fin n,V i s j*V i s k)/(n:ℝ)) atTop (fun _=>G j k))
    (hb : ∀j,TendstoInMeasure P (fun n s=>(∑i:Fin n,V i s j*Y i s)/(n:ℝ)) atTop (fun _=>b j)) :
    ∀j,TendstoInMeasure P (fun n s=>ols (fun i:Fin n=>V i s) (fun i=>Y i s) j)
      atTop (fun _=>G⁻¹.mulVec b j) := by
  let I:= (Q×Q)⊕Q
  let a:I→ℝ:=Sum.elim (fun jk=>G jk.1 jk.2) b
  let f:ℕ→Ω→I→ℝ:=fun n s=>Sum.elim
    (fun jk=>(∑i:Fin n,V i s jk.1*V i s jk.2)/(n:ℝ))
    (fun j=>(∑i:Fin n,V i s j*Y i s)/(n:ℝ))
  let A:(I→ℝ)→Matrix Q Q ℝ:=fun v j k=>v (.inl (j,k))
  let B:(I→ℝ)→Q→ℝ:=fun v j=>v (.inr j)
  have ha:A a=G:=rfl
  have hba:B a=b:=rfl
  have hA:Continuous A:=by unfold A;fun_prop
  have hB:Continuous B:=by unfold B;fun_prop
  have hInv:ContinuousAt (fun v=>(A v)⁻¹) a:=by
    have hg:ContinuousAt Inv.inv G:=continuousAt_matrix_inv G (by
      simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet))
    exact hg.comp_of_eq hA.continuousAt ha
  have hf:∀i,TendstoInMeasure P (fun n s=>f n s i) atTop (fun _=>a i):=by
    intro i
    cases i with
    | inl jk => exact hG jk.1 jk.2
    | inr j => exact hb j
  intro j
  have hc:ContinuousAt (fun v=>(A v)⁻¹.mulVec (B v) j) a:=by
    change Tendsto (fun v=>∑k,(A v)⁻¹ j k*B v k) (𝓝 a) (𝓝 (∑k,(A a)⁻¹ j k*B a k))
    apply tendsto_finsetSum Finset.univ
    intro k _
    exact ((continuous_apply k).continuousAt.comp ((continuous_apply j).continuousAt.comp hInv)).mul
      ((continuous_apply k).continuousAt.comp hB.continuousAt)
  have hlim:=finite_cmt P f a (fun v=>(A v)⁻¹.mulVec (B v) j) hf hc
  have he:∀ᶠn:ℕ in atTop,(fun s=>(A (f n s))⁻¹.mulVec (B (f n s)) j)=ᵐ[P]
      fun s=>ols (fun i:Fin n=>V i s) (fun i=>Y i s) j:=by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact Eventually.of_forall (fun s=>by
      have hn0:(n:ℝ)≠0:=by exact_mod_cast (by omega:n≠0)
      let W : Matrix (Fin n) Q ℝ:=fun i=>V i s
      have hAA:A (f n s)=(n:ℝ)⁻¹ • (W.transpose*W):=by
        ext j k
        simp [W,A,f,Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv,Finset.mul_sum,mul_comm]
      have hBB:B (f n s)=(n:ℝ)⁻¹ • (W.transpose.mulVec (fun i=>Y i s)):=by
        ext j
        simp [W,B,f,Matrix.mulVec,dotProduct,Matrix.transpose_apply,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,Finset.mul_sum,mul_comm]
      change ((A (f n s))⁻¹).mulVec (B (f n s)) j=ols W (fun i=>Y i s) j
      rw [hAA,hBB]
      exact congrFun (normalized_ols W (fun i=>Y i s) (n:ℝ)⁻¹ (inv_ne_zero hn0)).symm j)
  simpa only [ha,hba] using TendstoInMeasure.congr' he EventuallyEq.rfl hlim

lemma projection_population_equations {Ω B Q : Type*} [MeasurableSpace Ω]
    [MeasurableSpace B] [Fintype Q] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (hX : Measurable X) (V : Ω → Q → ℝ)
    (hV : ∀j,Measurable[MeasurableSpace.comap X inferInstance] (fun s=>V s j))
    (D : Ω → ℝ) (hiD : Integrable D P) (ω : Q → ℝ)
    (hlinear : P[D|MeasurableSpace.comap X inferInstance]=ᵐ[P] fun s=>dotProduct (V s) ω)
    (hVD : ∀j,Integrable (fun s=>V s j*D s) P)
    (hVV : ∀j k,Integrable (fun s=>V s j*V s k) P) :
    Matrix.mulVec (fun j k=>∫s,V s j*V s k∂P) ω=(fun j=>∫s,V s j*D s∂P) := by
  ext j
  have hp:=condExp_mul_of_stronglyMeasurable_left (hV j).stronglyMeasurable (hVD j) hiD
  have he:(∫s,V s j*D s∂P)=(∫s,V s j*dotProduct (V s) ω∂P):=by
    calc
      _ = ∫s,P[(fun s=>V s j*D s)|MeasurableSpace.comap X inferInstance] s∂P:=
        (integral_condExp hX.comap_le).symm
      _ = _:=by
        apply integral_congr_ae
        filter_upwards [hp,hlinear] with s hs hl
        change P[(fun u=>V u j*D u)|MeasurableSpace.comap X inferInstance] s=V s j*P[D|MeasurableSpace.comap X inferInstance] s at hs
        rw [hs,hl]
  change (∑k,(∫s,V s j*V s k∂P)*ω k)=_
  calc
    _ = ∑k,∫s,(V s j*V s k)*ω k∂P:=by simp only [integral_mul_const]
    _ = ∫s,∑k,(V s j*V s k)*ω k∂P := (integral_finsetSum _ (fun k _=>(hVV j k).mul_const (ω k))).symm
    _ = ∫s,V s j*dotProduct (V s) ω∂P:=by
      apply integral_congr_ae
      exact Eventually.of_forall (fun s=>by simp [dotProduct,Finset.mul_sum,mul_assoc])
    _ = _:=he.symm

lemma weighted_residual_expansion {N Q : Type*} [Fintype N] [Fintype Q]
    (r Z : N → ℝ) (V : Matrix N Q ℝ) (δ : Q → ℝ) :
    (∑i,(r i-V.mulVec δ i)^2*Z i)=
      (∑i,r i^2*Z i)-2*(∑j,δ j*(∑i,r i*Z i*V i j))+
        ∑j,∑k,δ j*δ k*(∑i,Z i*V i j*V i k) := by
  have hc:(∑i,r i*V.mulVec δ i*Z i)=∑j,δ j*(∑i,r i*Z i*V i j):=by
    calc
      _ = ∑i,∑j,δ j*(r i*Z i*V i j):=by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑j,∑i,δ j*(r i*Z i*V i j):=Finset.sum_comm
      _ = _:=by simp only [Finset.mul_sum]
  have hq:(∑i,(V.mulVec δ i)^2*Z i)=∑j,∑k,δ j*δ k*(∑i,Z i*V i j*V i k):=by
    calc
      _ = ∑i,∑j,∑k,δ j*δ k*(Z i*V i j*V i k):=by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Matrix.mulVec,dotProduct,pow_two,Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑j,∑k,∑i,δ j*δ k*(Z i*V i j*V i k):=by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
      _ = _:=by simp only [Finset.mul_sum]
  have he(i:N):(r i-V.mulVec δ i)^2*Z i=r i^2*Z i-2*(r i*V.mulVec δ i*Z i)+(V.mulVec δ i)^2*Z i:=by ring
  simp_rw [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
  rw [hc,hq]

lemma weighted_residual_average_expansion {N Q : Type*} [Fintype N] [Fintype Q]
    (r Z : N → ℝ) (V : Matrix N Q ℝ) (δ : Q → ℝ) (t:ℝ) :
    (∑i,(r i-V.mulVec δ i)^2*Z i)/t=
      (∑i,r i^2*Z i)/t-2*(∑j,δ j*((∑i,r i*Z i*V i j)/t))+
        ∑j,∑k,δ j*δ k*((∑i,Z i*V i j*V i k)/t) := by
  simpa only [add_div,sub_div,mul_div_assoc,Finset.sum_div] using
    congrArg (fun x:ℝ=>x/t) (weighted_residual_expansion r Z V δ)


lemma weighted_perturbation_limit {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (P : Measure Ω) (r Z : ℕ → Ω → ℝ) (V : ℕ → Ω → Q → ℝ)
    (δ : ℕ → Ω → Q → ℝ) (a:ℝ) (c:Q→ℝ) (q:Q→Q→ℝ)
    (hδ:∀j,TendstoInMeasure P (fun n s=>δ n s j) atTop (fun _=>0))
    (ha:TendstoInMeasure P (fun n s=>(∑i:Fin n,r i s^2*Z i s)/(n:ℝ)) atTop (fun _=>a))
    (hc:∀j,TendstoInMeasure P (fun n s=>(∑i:Fin n,r i s*Z i s*V i s j)/(n:ℝ)) atTop (fun _=>c j))
    (hq:∀j k,TendstoInMeasure P (fun n s=>(∑i:Fin n,Z i s*V i s j*V i s k)/(n:ℝ)) atTop (fun _=>q j k)) :
    TendstoInMeasure P (fun n s=>(∑i:Fin n,(r i s-Matrix.mulVec (fun i:Fin n=>V i s) (δ n s) i)^2*Z i s)/(n:ℝ))
      atTop (fun _=>a) := by
  have hcross:TendstoInMeasure P (fun n s=>∑j,δ n s j*((∑i:Fin n,r i s*Z i s*V i s j)/(n:ℝ))) atTop (fun _=>0):=by
    have h:=sum_limit P (fun j n s=>δ n s j*((∑i:Fin n,r i s*Z i s*V i s j)/(n:ℝ)))
      (fun _=>0) (fun j=>by simpa using mul_limit P (hδ j) (hc j))
    simpa using h
  have hquad:TendstoInMeasure P (fun n s=>∑j,∑k,δ n s j*δ n s k*((∑i:Fin n,Z i s*V i s j*V i s k)/(n:ℝ)))
      atTop (fun _=>0):=by
    have hj(j:Q):TendstoInMeasure P (fun n s=>∑k,δ n s j*δ n s k*((∑i:Fin n,Z i s*V i s j*V i s k)/(n:ℝ))) atTop (fun _=>0):=by
      have h:=sum_limit P (fun k n s=>δ n s j*δ n s k*((∑i:Fin n,Z i s*V i s j*V i s k)/(n:ℝ)))
        (fun _=>0) (fun k=>by simpa using mul_limit P (mul_limit P (hδ j) (hδ k)) (hq j k))
      simpa using h
    simpa using sum_limit P _ (fun _=>0) hj
  have h:=add_limit P (sub_limit P ha (mul_limit P (constant_limit P 2) hcross)) hquad
  have h':TendstoInMeasure P (fun n s=>(∑i:Fin n,r i s^2*Z i s)/(n:ℝ)-2*(∑j,δ n s j*((∑i:Fin n,r i s*Z i s*V i s j)/(n:ℝ)))+
      ∑j,∑k,δ n s j*δ n s k*((∑i:Fin n,Z i s*V i s j*V i s k)/(n:ℝ))) atTop (fun _=>a):=by simpa using h
  exact TendstoInMeasure.congr_left (fun n=>Eventually.of_forall (fun s=>
    (weighted_residual_average_expansion (fun i:Fin n=>r i s) (fun i=>Z i s)
      (fun i:Fin n=>V i s) (δ n s) (n:ℝ)).symm)) h'

end
end AronowAudit.P015.OLSCompletion
