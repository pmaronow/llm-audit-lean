import AronowAudit.P011.P011_DenseInfrastructure
import AronowAudit.P011.P011_DenseCumulant
import AronowAudit.P011.P011_DenseCenteredVariance
import AronowAudit.P011.P011_DenseLimitCompletion

namespace AronowAudit.P011.DenseSampleCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open DenseCompletion
open Causalean.Mathlib.Probability.SteinMethod
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
local instance : ENNReal.HolderTriple (4:ENNReal) 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add]⟩

lemma quadratic_mulVec {n : ℕ} (M P : Matrix (Fin n) (Fin n) ℝ) (x : Fin n→ℝ) :
    quadratic M (P*ᵥx)=quadratic (Pᵀ*M*P) x := by
  have hq (N:Matrix (Fin n) (Fin n) ℝ) (z:Fin n→ℝ):quadratic N z=z ⬝ᵥ (N*ᵥz):=by
    simp [quadratic,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_comm,mul_left_comm]
  rw [hq,hq,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

lemma quadratic_centered {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n→ℝ) :
    quadratic M (centered x)=quadratic (centeringMatrix n*M*centeringMatrix n) x := by
  rw [←center_mulVec,quadratic_mulVec]
  have hp:(centeringMatrix n)ᵀ=centeringMatrix n:=by ext i j;exact centering_symm j i
  rw [hp]

lemma quadratic_translate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA:∀i j,A i j=A j i) (x b:Fin n→ℝ) :
    quadratic A (fun i=>x i+b i)=quadratic A x+
      2*(∑i,(A*ᵥb) i*x i)+quadratic A b := by
  classical
  have he:(∑i,∑j,A i j*b i*x j)=(∑i,∑j,A i j*x i*b j):=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro j _
    rw [hA j i];ring
  simp only [quadratic,Matrix.mulVec,dotProduct,Finset.sum_mul]
  simp_rw [show ∀i j,A i j*(x i+b i)*(x j+b j)=
    A i j*x i*x j+A i j*x i*b j+A i j*b i*x j+A i j*b i*b j by intros;ring]
  simp only [Finset.sum_add_distrib]
  rw [he]
  have hh:(∑i,∑j,A i j*b j*x i)=(∑i,∑j,A i j*x i*b j):=by
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro j _
    ring
  rw [hh]
  ring

lemma linear_variance {n:ℕ} (m:Model n) (hL2:∀i,MemLp (fun y=>weighted m y i) 2 m.law)
    (v:Fin n→ℝ) :
    variance (fun y=>∑i,v i*(weighted m y i-expectation m (fun z=>weighted m z i))) m.law
      =quadratic (covariance m) v := by
  let : IsProbabilityMeasure m.law:=m.probability
  have hz(i:Fin n):MemLp (fun y=>weighted m y i-expectation m (fun z=>weighted m z i)) 2 m.law:=
    (hL2 i).sub (memLp_const _)
  rw [variance_fun_sum (fun i=>(hz i).const_mul (v i))]
  simp only [covariance_const_mul_left,covariance_const_mul_right]
  unfold quadratic
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  rw [covariance_sub_const_left ((hL2 i).integrable (by norm_num)),
    covariance_sub_const_right ((hL2 j).integrable (by norm_num))]
  rw [←QuadraticCompletion.covariance_eq_mathlib]
  ring

lemma linear_variance_bound {n:ℕ} (m:Model n) (c d:ℝ) (hc:0≤c)
    (hdep:Dependency m) (hb:∀ᵐy∂m.law,∀i,|weighted m y i-beta m|≤c)
    (hd:∀i,(degree m.G i:ℝ)+1≤d) (v:Fin n→ℝ) :
    variance (fun y=>∑i,v i*(weighted m y i-expectation m (fun z=>weighted m z i))) m.law
      ≤d*c^2*(∑i,v i^2) := by
  classical
  have hL2:=ProbabilityCompletion.weighted_memLp m c hb
  have ht(i j:Fin n):|covariance m i j|≤oracleMatrix m.G i j*c^2:=by
    rw [CliqueCompletion.oracle_apply]
    by_cases hh:i=j∨m.G.val i j=true
    · simpa only [ite_eq_left hh,one_mul] using ExpectationCompletion.covariance_abs_le m c hc hb i j
    · have hij:i≠j:=fun he=>hh (Or.inl he)
      have hg:m.G.val i j=false:=by cases he:m.G.val i j <;>simp_all
      rw [ite_eq_right hh,OracleCompletion.covariance_support m hdep hL2 i j hij hg]
      simp
  rw [linear_variance m hL2]
  calc
    _ ≤ ∑i,∑j,oracleMatrix m.G i j*c^2*(v i^2+v j^2)/2:=by
      apply Finset.sum_le_sum;intro i _
      apply Finset.sum_le_sum;intro j _
      have hp:|v i*v j|≤(v i^2+v j^2)/2:=by
        rw [abs_le];constructor <;>nlinarith [sq_nonneg (v i-v j),sq_nonneg (v i+v j)]
      calc
        covariance m i j*v i*v j ≤ |covariance m i j| *|v i*v j|:=by
          simpa only [abs_mul,mul_assoc] using le_abs_self (covariance m i j*v i*v j)
        _ ≤ (oracleMatrix m.G i j*c^2)*((v i^2+v j^2)/2):=
          mul_le_mul (ht i j) hp (abs_nonneg _) (mul_nonneg (OracleCompletion.oracle_nonneg _ _ _) (sq_nonneg _))
        _ = _:=by ring
    _ = ∑i,((degree m.G i:ℝ)+1)*c^2*v i^2:=by
      have hcol(j:Fin n):(∑i,oracleMatrix m.G i j)=(degree m.G j:ℝ)+1:=by
        simp_rw [ExpectationCompletion.oracle_symmetric m.G _ j]
        exact OracleCompletion.oracle_row_sum _ _
      simp only [mul_add,add_div,Finset.sum_add_distrib,←Finset.sum_div]
      have h1:(∑i,∑j,oracleMatrix m.G i j*c^2*v i^2)=∑i,((degree m.G i:ℝ)+1)*c^2*v i^2:=by
        simp_rw [←Finset.sum_mul,OracleCompletion.oracle_row_sum]
      have h2:(∑i,∑j,oracleMatrix m.G i j*c^2*v j^2)=∑i,((degree m.G i:ℝ)+1)*c^2*v i^2:=by
        rw [Finset.sum_comm]
        simp_rw [←Finset.sum_mul,hcol]
      rw [h1,h2];ring
    _ ≤ _:=by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum;intro i _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hd i) (sq_nonneg c)) (sq_nonneg _)

lemma variance_add_le {Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω) [IsProbabilityMeasure μ]
    (X Y:Ω→ℝ) (hX:MemLp X 2 μ) (hY:MemLp Y 2 μ) :
    variance (fun ω=>X ω+Y ω) μ≤2*variance X μ+2*variance Y μ:=by
  have hm:=variance_nonneg (fun ω=>X ω-Y ω) μ
  rw [variance_fun_sub hX hY] at hm
  rw [variance_fun_add hX hY]
  linarith

lemma centered_sub_const {n:ℕ} (hn:0<n) (x:Fin n→ℝ) (b:ℝ) :
    centered (fun i=>x i-b)=centered x:=by
  have hn0:(n:ℝ)≠0:=by exact_mod_cast hn.ne'
  ext i
  simp only [centered,average,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  field_simp
  ring

lemma own_centered_mean {n:ℕ} (m:Model n) (hL2:∀i,MemLp (fun y=>weighted m y i) 2 m.law)
    (i:Fin n): (∫y,weighted m y i-expectation m (fun z=>weighted m z i)∂m.law)=0:=by
  let : IsProbabilityMeasure m.law:=m.probability
  rw [integral_sub ((hL2 i).integrable (by norm_num)) (integrable_const _)]
  simp [expectation]

lemma sample_variance_bound {n:ℕ} (hn:0<n) (m:Model n) (c d:ℝ) (hc:0≤c) (hd0:0≤d)
    (hdep:Dependency m) (hb:∀ᵐy∂m.law,∀i,|weighted m y i-beta m|≤c)
    (hd:∀i,(degree m.G i:ℝ)+1≤d) (M:Matrix (Fin n) (Fin n) ℝ)
    (hM:∀i j,M i j=M j i):
    var m (fun y=>quadratic M (centered (weighted m y)))≤
      (2*(144*d^3+2*d^2)*(2*c)^4+8*d*c^4)*(operatorNorm M)^2*(n:ℝ):=by
  classical
  let : IsProbabilityMeasure m.law:=m.probability
  let Z:=fun (i:Fin n) y=>weighted m y i-expectation m (fun z=>weighted m z i)
  let D:=ProbabilityCompletion.modelDep m hdep
  let A:=centeringMatrix n*M*centeringMatrix n
  let v:=A*ᵥdelta m
  let Q:=fun y=>quadratic A (fun i=>Z i y)
  let L:=fun y=>∑i,v i*Z i y
  have hL2:=ProbabilityCompletion.weighted_memLp m c hb
  have hzb:∀i,∀ᵐy∂m.law,|Z i y|≤2*c:=fun i=>
    (ProbabilityCompletion.own_centred_bound m c hL2 hb).mono (fun y hy=>hy i)
  have hz2(i:Fin n):MemLp (Z i) 2 m.law:=
    SampleCompletion.bounded_memLp _ _ (D.meas i) (2*c) (hzb i) 2
  have hQ:MemLp Q 2 m.law:=by
    have hp(i j:Fin n):MemLp (fun y=>A i j*Z i y*Z j y) 2 m.law:=by
      have ht:=DenseCumulant.pair_memLp m.law Z D.meas (2*c) (by positivity) hzb i j
      exact (memLp_congr_ae (Eventually.of_forall fun y=>by ring)).mp (ht.const_mul (A i j))
    exact memLp_finsetSum Finset.univ (fun i _=>memLp_finsetSum Finset.univ (fun j _=>hp i j))
  have hL:MemLp L 2 m.law:=memLp_finsetSum Finset.univ (fun i _=>(hz2 i).const_mul (v i))
  have he(y:Fin n→ℝ):quadratic M (centered (weighted m y))=
      Q y+2*L y+quadratic A (delta m):=by
    have hx:(fun i=>Z i y+delta m i)=(fun i=>weighted m y i-beta m):=by
      funext i;dsimp [Z,delta];ring
    have hcq:quadratic M (centered (weighted m y))=
      quadratic A (fun i=>Z i y+delta m i):=by
      rw [hx,←quadratic_centered,centered_sub_const hn]
    rw [hcq,quadratic_translate A (centering_sandwich_symm M hM)]
  have hAn:operatorNorm A≤operatorNorm M:=centering_sandwich_norm hn M
  have hAs:0≤operatorNorm A:=norm_nonneg _
  have hMs:0≤operatorNorm M:=norm_nonneg _
  have hAn2:(operatorNorm A)^2≤(operatorNorm M)^2:=sq_le_sq₀ hAs hMs |>.mpr hAn
  have hrow(i:Fin n):(∑j,if D.G i j then (1:ℝ) else 0)≤d:=by
    have hh(j:Fin n):D.G i j↔i=j∨m.G.val i j=true:=by rfl
    simp_rw [hh]
    simpa only [CliqueCompletion.oracle_apply] using
      ((OracleCompletion.oracle_row_sum m.G i).le.trans (hd i))
  have hQV:variance Q m.law≤(144*d^3+2*d^2)*(2*c)^4*(operatorNorm M)^2*(n:ℝ):=by
    have hh:=DenseCenteredVariance.centered_variance_bound m.law Z D
      (own_centered_mean m hL2) (2*c) (by positivity) hzb d hd0 hrow A
      (by ext i j;exact centering_sandwich_symm M hM j i)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hAn2 (by positivity)) (Nat.cast_nonneg n))
  have hdelta(i:Fin n):|delta m i|≤c:=ProbabilityCompletion.own_mean_bound m c hL2 hb i
  have hv:l2 v≤operatorNorm M*(Real.sqrt n*c):=by
    calc
      _ ≤ operatorNorm A*l2 (delta m):=mulVec_l2 A _
      _ ≤ operatorNorm M*l2 (delta m):=mul_le_mul_of_nonneg_right hAn (l2_nonneg _)
      _ ≤ _:=mul_le_mul_of_nonneg_left (l2_abs_bound _ c hc hdelta) hMs
  have hvs:(∑i,v i^2)≤(operatorNorm M)^2*(n:ℝ)*c^2:=by
    have hh: (l2 v)^2≤(operatorNorm M*(Real.sqrt n*c))^2:=
      (sq_le_sq₀ (l2_nonneg _) (by positivity)).mpr hv
    rw [l2_sq] at hh
    simpa only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),mul_assoc] using hh
  have hLV:variance L m.law≤d*c^4*(operatorNorm M)^2*(n:ℝ):=by
    have hh:=linear_variance_bound m c d hc hdep hb hd v
    have hh2:=mul_le_mul_of_nonneg_left hvs (show 0≤d*c^2 by positivity)
    exact hh.trans (by nlinarith [hh2])
  have hvadd:=variance_add_le m.law Q (fun y=>2*L y) hQ (hL.const_mul 2)
  have hfun:(fun y=>quadratic M (centered (weighted m y)))=
      (fun y=>(Q y+2*L y)+quadratic A (delta m)):=funext he
  unfold var expectation
  rw [←variance_eq_integral (DenseLimitCompletion.quadratic_centered_memLp m c hb M).aemeasurable,hfun]
  have hvc:variance (fun y=>Q y+2*L y+quadratic A (delta m)) m.law=
      variance (fun y=>Q y+2*L y) m.law:=
    variance_add_const (X:=fun y=>Q y+2*L y) ((hQ.add (hL.const_mul 2)).aestronglyMeasurable) _
  rw [hvc]
  rw [variance_const_mul] at hvadd
  nlinarith [hQV,hLV]

lemma uniform_sample_variance (F:Family) (c1 c2 c3 c4 K:ℝ) (h:Scaling F c1 c2 c3 c4)
    (M:∀k,Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ)
    (hM:∀k i j,M k i j=M k j i) (hK:∀k,operatorNorm (M k)≤K):
    ∃B:ℝ,0≤B∧∃k0:ℕ,∀k≥k0,
      var (F.model k) (fun y=>quadratic (M k) (centered (weighted (F.model k) y)))≤B*(F.size k:ℝ):=by
  rcases h with ⟨_,hc1,hc2,_,_,hDep,hBound,hDeg,_,_⟩
  let C:=2*(144*(1+c2)^3+2*(1+c2)^2)*(2*c1)^4+8*(1+c2)*c1^4
  have hC:0≤C:=by dsimp [C];positivity
  have hK0:0≤K:=(norm_nonneg _).trans (hK 0)
  refine ⟨C*K^2,by positivity,0,?_⟩
  intro k _
  have hv:=sample_variance_bound (F.positive k) (F.model k) c1 (1+c2) hc1.le
    (by positivity) (hDep k) (hBound k) (fun i=>by linarith [hDeg k i]) (M k) (hM k)
  have hk:(operatorNorm (M k))^2≤K^2:=(sq_le_sq₀ (norm_nonneg _) hK0).mpr (hK k)
  exact hv.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hC) (Nat.cast_nonneg _))


end
end AronowAudit.P011.DenseSampleCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
/-- P011-T4(ii)–(iv): quadratic-form expansion for deterministic symmetric
matrices with uniformly bounded Euclidean operator norm, including
Var(eᵀMe)=O(n) and conservativeness when both M and M-(I+A) are PSD. -/
theorem deterministic_quadratic_expansion (F : Family) (c1 c2 c3 c4 K : ℝ)
    (h : Scaling F c1 c2 c3 c4)
    (M : ∀ k, Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ)
    (hM : ∀ k i j, M k i j = M k j i) (hK : ∀ k, operatorNorm (M k) ≤ K) :
    (∃ B : ℝ, 0 ≤ B ∧ ∃ k0 : ℕ, ∀ k ≥ k0,
      var (F.model k) (fun y => quadratic (M k) (centered (weighted (F.model k) y)))
        ≤ B*(F.size k : ℝ)) ∧
    InProbability F
      (fun k y => (F.size k : ℝ)*varianceForm (M k) (weighted (F.model k) y) - scaledTrue F k)
      (fun k => (Matrix.trace ((M k - oracleMatrix (F.model k).G)*covariance (F.model k)) +
        quadratic (M k) (delta (F.model k))) / (F.size k : ℝ)) ∧
    ((∀ k, PSD (M k) ∧ PSD (M k - oracleMatrix (F.model k).G)) →
      (∀ k, 0 ≤ quadratic (M k) (delta (F.model k)) ∧
        0 ≤ Matrix.trace ((M k-oracleMatrix (F.model k).G)*covariance (F.model k))) ∧
      Conservative F (fun k y => varianceForm (M k) (weighted (F.model k) y)))  := by
  have hv:=DenseSampleCompletion.uniform_sample_variance F c1 c2 c3 c4 K h M hM hK
  exact ⟨hv,DenseLimitCompletion.limit_clauses_from_variance F c1 c2 c3 c4 K h M hM hK hv⟩


end
end AronowAudit.P011
