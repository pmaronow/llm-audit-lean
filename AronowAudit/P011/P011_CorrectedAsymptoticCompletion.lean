/- P011 T5: corrected-estimator conservativeness.
Supplied degree caps may grow; bounded true-degree matrices and pointwise domination
handle that case. Sample-chosen maximizers enter only through their actual maximizing
property, not through the deterministic matrix expansion. -/
import AronowAudit.P011.P011_DenseVarianceCompletion
import AronowAudit.P011.P011_CorollariesCompletion
import AronowAudit.P011.P011_SchurCompletion
namespace AronowAudit.P011.CorrectedAsymptoticCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency true

lemma correction_le_one {n:ℕ} (d:Fin n→ℕ) (i:Fin n):degreeCorrection d i≤1:=by
  unfold degreeCorrection
  split_ifs
  · norm_num
  · exact sub_le_self _ (one_div_nonneg.mpr (Nat.cast_nonneg _))

lemma corrected_row_bound {n:ℕ} (R G:Graph n) (d:Fin n→ℕ) (hv:Compatible R d G)
    (c:ℝ) (hd:∀i,(degree G i:ℝ)≤c) (i:Fin n):
    (∑j,|correctedMatrix d G i j|)≤1+2*c:=by
  have ht:0≤degreeCorrection d i:=(corrected_diagonal_bounds R G d hv i).1
  have he(j:Fin n):0≤correctedMatrix d G i j:=by
    unfold correctedMatrix
    simp only [Matrix.add_apply,Matrix.diagonal_apply]
    apply add_nonneg (OracleCompletion.oracle_nonneg G i j)
    split_ifs
    · exact mul_nonneg ht (Nat.cast_nonneg _)
    · exact le_refl _
  simp_rw [abs_of_nonneg (he _)]
  simp only [correctedMatrix,Matrix.add_apply,Finset.sum_add_distrib,Matrix.diagonal_apply,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true,OracleCompletion.oracle_row_sum]
  have hh:=mul_le_mul_of_nonneg_right (correction_le_one d i) (Nat.cast_nonneg (degree G i))
  linarith [hd i]

lemma young_row_bound {n:ℕ} (G:Graph n) (c:ℝ) (hd:∀i,(degree G i:ℝ)≤c) (i:Fin n):
    (∑j,|(1+Matrix.diagonal (fun i=>(degree G i:ℝ))) i j|)≤1+c:=by
  classical
  have he(j:Fin n):(1+Matrix.diagonal (fun i=>(degree G i:ℝ))) i j=
      if i=j then 1+(degree G i:ℝ) else 0:=by
    by_cases hij:i=j
    · subst j;simp [Matrix.add_apply,Matrix.one_apply,Matrix.diagonal_apply]
    · simp [Matrix.add_apply,Matrix.one_apply,Matrix.diagonal_apply,hij]
  simp_rw [he]
  simp only [abs_ite,abs_of_nonneg (show 0≤1+(degree G i:ℝ) by positivity),abs_zero,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  linarith [hd i]


lemma conservative_min (F:Family) (V W:∀k,(Fin (F.size k)→ℝ)→ℝ)
    (hV:Conservative F V) (hW:Conservative F W):
    Conservative F (fun k y=>min (V k y) (W k y)):=by
  intro ε hε
  let (k:ℕ):IsProbabilityMeasure (F.model k).law:=(F.model k).probability
  apply squeeze_zero (fun k=>measureReal_nonneg) (fun k=>?_) (by simpa only [zero_add] using (hV ε hε).add (hW ε hε))
  change (F.model k).law.real _≤(F.model k).law.real _+(F.model k).law.real _
  apply (measureReal_mono (μ:=(F.model k).law) ?_ (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  intro y hy
  change ε<(F.size k:ℝ)*(var (F.model k) (betaHat (F.model k))-min (V k y) (W k y)) at hy
  change ε<(F.size k:ℝ)*(var (F.model k) (betaHat (F.model k))-V k y)∨
    ε<(F.size k:ℝ)*(var (F.model k) (betaHat (F.model k))-W k y)
  rcases le_total (V k y) (W k y) with hv|hw
  · left;simpa only [min_eq_left hv] using hy
  · right;simpa only [min_eq_right hw] using hy

lemma young_true_psd {n:ℕ} (G:Graph n):
    PSD (1+Matrix.diagonal (fun i=>(degree G i:ℝ)))∧
      PSD ((1+Matrix.diagonal (fun i=>(degree G i:ℝ)))-oracleMatrix G):=by
  have hi:PSD (1:Matrix (Fin n) (Fin n) ℝ):=by
    have he:(1:Matrix (Fin n) (Fin n) ℝ)=Matrix.diagonal (fun _=>1):=by ext i j;simp [Matrix.one_apply,Matrix.diagonal_apply]
    rw [he];exact psd_diagonal _ (by intro i;norm_num)
  refine ⟨psd_add _ _ hi (psd_diagonal _ (fun i=>Nat.cast_nonneg _)),?_⟩
  have he:(1+Matrix.diagonal (fun i=>(degree G i:ℝ)))-oracleMatrix G=
      Matrix.diagonal (fun i=>(degree G i:ℝ))-adjacency G:=by unfold oracleMatrix;abel
  rw [he]
  exact graph_laplacian_psd G

lemma young_true_le {n:ℕ} (R G:Graph n) (d:Fin n→ℕ) (hv:Compatible R d G) (x:Fin n→ℝ):
    varianceForm (1+Matrix.diagonal (fun i=>(degree G i:ℝ))) x≤VYoung d x:=by
  have hI:(1:Matrix (Fin n) (Fin n) ℝ)=Matrix.diagonal (fun _=>1):=by ext i j;simp [Matrix.one_apply,Matrix.diagonal_apply]
  unfold varianceForm VYoung
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  rw [quadratic_add,hI,quadratic_diagonal,quadratic_diagonal,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum;intro i _
  have hd: (degree G i:ℝ)≤(truncatedDegree d i:ℝ):=by exact_mod_cast compatible_truncated_degree R G d hv i
  nlinarith [sq_nonneg (centered x i)]

lemma young_eq_prime_of_constant {n:ℕ} (hn:0<n) (d:Fin n→ℕ) (D:ℕ)
    (hd:∀i,truncatedDegree d i=D) (x:Fin n→ℝ):VYoung d x=V2prime d x:=by
  have hn0:(n:ℝ)≠0:=by exact_mod_cast hn.ne'
  simp only [VYoung,V2prime,sampleVariance,hd,←Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

lemma corrected_asymptotic_from_norms (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hv : Valid F)
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1plus (F.model k).d B (weighted (F.model k) y)) (A k y))
    (hCN:∀k,operatorNorm (correctedMatrix (F.model k).d (F.model k).G)≤1+2*c2)
    (hYN:∀k,operatorNorm (1+Matrix.diagonal (fun i=>(degree (F.model k).G i:ℝ)))≤1+c2):
    (∀ k, operatorNorm (correctedMatrix (F.model k).d (F.model k).G) ≤ 1+2*c2) ∧
    (∀ k y, V1plus (F.model k).d (F.model k).G (weighted (F.model k) y) ≤
      V1plus (F.model k).d (A k y) (weighted (F.model k) y)) ∧
    Conservative F (fun k y => V1plus (F.model k).d (F.model k).G (weighted (F.model k) y)) ∧
    Conservative F (fun k y => V1plus (F.model k).d (A k y) (weighted (F.model k) y)) ∧
    Conservative F (fun k y => VYoung (F.model k).d (weighted (F.model k) y)) ∧
    Conservative F (fun k y => min
      (V1plus (F.model k).d (A k y) (weighted (F.model k) y))
      (VYoung (F.model k).d (weighted (F.model k) y))) ∧
    ((∀ k, ∃ D : ℕ, ∀ i, truncatedDegree (F.model k).d i = D) →
      Conservative F (fun k y => V2prime (F.model k).d (weighted (F.model k) y))) := by
  let MC:=fun k=>correctedMatrix (F.model k).d (F.model k).G
  let MY:=fun k=>(1:Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ)+Matrix.diagonal (fun i=>(degree (F.model k).G i:ℝ))
  have hCP(k:ℕ):PSD (MC k)∧PSD (MC k-oracleMatrix (F.model k).G):=by
    have hh:=corrected_matrix_majorant (F.model k).R (F.model k).G (F.model k).d (hv k) (fun _=>0)
    exact ⟨hh.1,hh.2.1⟩
  have hYP(k:ℕ):PSD (MY k)∧PSD (MY k-oracleMatrix (F.model k).G):=young_true_psd _
  have hC0:=((deterministic_quadratic_expansion F c1 c2 c3 c4 (1+2*c2) h MC
    (fun k=>(hCP k).1.1) hCN).2.2 hCP).2
  have hC:Conservative F (fun k y=>V1plus (F.model k).d (F.model k).G (weighted (F.model k) y)):=by
    have he(k:ℕ) (y:Fin (F.size k)→ℝ):V1plus (F.model k).d (F.model k).G (weighted (F.model k) y)=
        varianceForm (MC k) (weighted (F.model k) y):=
      (corrected_matrix_majorant (F.model k).R (F.model k).G (F.model k).d (hv k) _).2.2.1
    simpa only [he] using hC0
  have hY0:=((deterministic_quadratic_expansion F c1 c2 c3 c4 (1+c2) h MY
    (fun k=>(hYP k).1.1) hYN).2.2 hYP).2
  have hY:Conservative F (fun k y=>VYoung (F.model k).d (weighted (F.model k) y)):=
    CorollaryCompletion.conservative_mono F _ _ hY0 (fun k y=>young_true_le _ _ _ (hv k) _)
  have hdom(k:ℕ) (y:Fin (F.size k)→ℝ):
      V1plus (F.model k).d (F.model k).G (weighted (F.model k) y)≤
        V1plus (F.model k).d (A k y) (weighted (F.model k) y):=(hm k y).2 _ (hv k)
  have hSel:=CorollaryCompletion.conservative_mono F _ _ hC hdom
  refine ⟨hCN,hdom,hC,hSel,hY,conservative_min F _ _ hSel hY,?_⟩
  intro hd
  have he(k:ℕ) (y:Fin (F.size k)→ℝ):VYoung (F.model k).d (weighted (F.model k) y)=
      V2prime (F.model k).d (weighted (F.model k) y):=by
    obtain ⟨D,hD⟩:=hd k
    exact young_eq_prime_of_constant (F.positive k) _ D hD _
  simpa only [he] using hY


end
end AronowAudit.P011.CorrectedAsymptoticCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
/-- T5(b),(c),(h),(i): Assumption 2 and valid constraints suffice even when
supplied degree bounds grow. All four repaired estimators are nonnegative and
n-scaled conservative; constant degree caps make V̂_Y′ equal the paper's V̂₂′. -/
theorem corrected_asymptotic (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hv : Valid F)
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1plus (F.model k).d B (weighted (F.model k) y)) (A k y)) :
    (∀ k, operatorNorm (correctedMatrix (F.model k).d (F.model k).G) ≤ 1+2*c2) ∧
    (∀ k y, V1plus (F.model k).d (F.model k).G (weighted (F.model k) y) ≤
      V1plus (F.model k).d (A k y) (weighted (F.model k) y)) ∧
    Conservative F (fun k y => V1plus (F.model k).d (F.model k).G (weighted (F.model k) y)) ∧
    Conservative F (fun k y => V1plus (F.model k).d (A k y) (weighted (F.model k) y)) ∧
    Conservative F (fun k y => VYoung (F.model k).d (weighted (F.model k) y)) ∧
    Conservative F (fun k y => min
      (V1plus (F.model k).d (A k y) (weighted (F.model k) y))
      (VYoung (F.model k).d (weighted (F.model k) y))) ∧
    ((∀ k, ∃ D : ℕ, ∀ i, truncatedDegree (F.model k).d i = D) →
      Conservative F (fun k y => V2prime (F.model k).d (weighted (F.model k) y)))  := by
  have hs:=h
  rcases hs with ⟨_,hc1,hc2,_,_,hDep,hBound,hDeg,_,_⟩
  have hCN(k:ℕ):operatorNorm (correctedMatrix (F.model k).d (F.model k).G)≤1+2*c2:=by
    apply SchurSupport.operatorNorm_le_abs_row_sum _
      (corrected_matrix_majorant (F.model k).R (F.model k).G (F.model k).d (hv k) (fun _=>0)).1.1
      (1+2*c2) (by positivity)
    exact CorrectedAsymptoticCompletion.corrected_row_bound _ _ _ (hv k) c2 (hDeg k)
  have hYN(k:ℕ):operatorNorm (1+Matrix.diagonal (fun i=>(degree (F.model k).G i:ℝ)))≤1+c2:=by
    apply SchurSupport.operatorNorm_le_abs_row_sum _ (CorrectedAsymptoticCompletion.young_true_psd (F.model k).G).1.1
      (1+c2) (by positivity)
    exact CorrectedAsymptoticCompletion.young_row_bound _ c2 (hDeg k)
  exact CorrectedAsymptoticCompletion.corrected_asymptotic_from_norms F c1 c2 c3 c4 h hv A hm hCN hYN


end
end AronowAudit.P011
