import AronowAudit.P004.P004_ConditioningCompletion

namespace AronowAudit.P004.ComponentCompletion
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter CLTCompletion
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem expect_abs_le {N : ℕ} (p : Fin N→ℝ) (hp : ∀i,0<p i ∧ p i<1)
    (F : Assignment N→ℝ) (b : ℝ) (hF : ∀z,|F z|≤b) : |expect p F|≤b:=by
  have hl:=expect_mono p hp (fun _=> -b) F (fun z=>(abs_le.mp (hF z)).1)
  have hu:=expect_mono p hp F (fun _=>b) (fun z=>(abs_le.mp (hF z)).2)
  rw [expect_const] at hl hu
  exact abs_le.mpr ⟨hl,hu⟩

theorem coin_ne_zero {N : ℕ} (p : Fin N→ℝ) (hp : ∀i,0<p i ∧ p i<1)
    (i : Fin N) (a : Bool) : coin (p i) a≠0:=by
  cases a <;> simp only [coin,ite_false,ite_true]
  · exact (sub_pos.mpr (hp i).2).ne'
  · exact (hp i).1.ne'

theorem selected_update {N : ℕ} (p : Fin N→ℝ) (hp : ∀i,0<p i ∧ p i<1)
    (F : Assignment N→ℝ) (i : Fin N) (a : Bool) :
    expect p (fun z=>if z i=a then F z else 0)=coin (p i) a*expect p (fun z=>F (Function.update z i a)):=by
  rw [bernoulli_selection p (fun _ z=>F z) i a (coin_ne_zero p hp i a),marginal_is_marginalization p (fun _ z=>F z) i a hp]

theorem pair_marginal_forced {N : ℕ} (p : Fin N→ℝ) (hp : ∀i,0<p i ∧ p i<1)
    (F : Assignment N→ℝ) (i j : Fin N) (hij : i≠j) (a b : Bool) :
    pairMarginal p F i j a b=expect p (fun z=>F (Function.update (Function.update z j b) i a)):=by
  have he : (fun z=>if z i=a ∧ z j=b then F z else 0)=
      (fun z=>if z i=a then (if z j=b then F z else 0) else 0):=by
    funext z
    split_ifs <;> simp_all
  have hu : (fun z=>if (Function.update z i a) j=b then F (Function.update z i a) else 0)=
      (fun z=>if z j=b then F (Function.update z i a) else 0):=by
    funext z
    rw [Function.update_of_ne hij.symm]
  unfold pairMarginal
  rw [he,selected_update p hp _ i a,hu,selected_update p hp _ j b]
  field_simp [coin_ne_zero p hp i a,coin_ne_zero p hp j b]

theorem marginal_abs_le {N : ℕ} (p : Fin N→ℝ) (hp : ∀i,0<p i ∧ p i<1)
    (R : CircleTable N) (b : ℝ) (hR : ∀i z,|R i z|≤b) (i : Fin N) (a : Bool) :
    |marginal p R i a|≤b:=by
  rw [marginal_is_marginalization p R i a hp]
  exact expect_abs_le p hp _ b (fun z=>hR i _)

theorem pair_cov_abs_le {N : ℕ} (p : Fin N→ℝ) (hp : ∀i,0<p i ∧ p i<1)
    (R : CircleTable N) (b : ℝ) (hb : 0≤b) (hR : ∀i z,|R i z|≤b)
    (i j : Fin N) (hij : i≠j) (a c : Bool) :
    |pairMarginal p (fun z=>R i z*R j z) i j a c-marginal p R i a*marginal p R j c|≤2*b^2:=by
  have hpairs : |pairMarginal p (fun z=>R i z*R j z) i j a c|≤b^2:=by
    rw [pair_marginal_forced p hp _ i j hij]
    apply expect_abs_le p hp
    intro z
    rw [abs_mul]
    simpa only [pow_two] using mul_le_mul (hR i _) (hR j _) (abs_nonneg _) hb
  have hm : |marginal p R i a*marginal p R j c|≤b^2:=by
    rw [abs_mul]
    simpa only [pow_two] using mul_le_mul (marginal_abs_le p hp R b hR i a) (marginal_abs_le p hp R b hR j c) (abs_nonneg _) hb
  have h1:=abs_le.mp hpairs
  have h2:=abs_le.mp hm
  apply abs_le.mpr
  constructor <;> linarith


theorem bounded_local_sum {N : ℕ} (B : Fin N→Finset (Fin N)) (L : ℝ)
    (hN : 0<N) (hL : 0≤L) (hself : ∀i,i∈B i) (F : Fin N→Fin N→ℝ)
    (hF : ∀i j,j∈(B i).erase i→|F i j|≤L) :
    |(∑i,∑j∈(B i).erase i,F i j)/(N:ℝ)^2|≤L*((maxDegree B:ℝ)-1)/(N:ℝ):=by
  have hn : 0<(N:ℝ):=Nat.cast_pos.mpr hN
  have hcard (i : Fin N) : (((B i).erase i).card:ℝ)≤(maxDegree B:ℝ)-1:=by
    have hc : 1≤(B i).card:=Finset.one_le_card.mpr ⟨i,hself i⟩
    rw [Finset.card_erase_of_mem (hself i),Nat.cast_sub hc,Nat.cast_one]
    apply sub_le_sub_right
    exact_mod_cast (show (B i).card≤maxDegree B from Finset.le_sup (f:=fun i=>(B i).card) (Finset.mem_univ i))
  have hs : |∑i,∑j∈(B i).erase i,F i j|≤(N:ℝ)*((maxDegree B:ℝ)-1)*L:=by
    calc
      _ ≤ ∑i,|∑j∈(B i).erase i,F i j|:=Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑i,∑j∈(B i).erase i,|F i j|:=Finset.sum_le_sum (fun i _=>Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑i,∑_j∈(B i).erase i,L:=Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j hj=>hF i j hj))
      _ = ∑i,(((B i).erase i).card:ℝ)*L:=by simp
      _ ≤ ∑_i:Fin N,((maxDegree B:ℝ)-1)*L:=Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (hcard i) hL)
      _ = _:=by simp [mul_assoc]
  rw [abs_div,abs_of_nonneg (sq_nonneg (N:ℝ))]
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  apply hs.trans_eq
  field_simp
  <;> ring

theorem marginal_sq_le {N : ℕ} (p : Fin N→ℝ) (hp : ∀i,0<p i ∧ p i<1)
    (R : CircleTable N) (b : ℝ) (hb : 0≤b) (hR : ∀i z,|R i z|≤b) (i : Fin N) (a : Bool) :
    marginal p (fun i z=>(R i z)^2) i a≤b^2:=by
  rw [marginal_is_marginalization]
  rw [←expect_const p (b^2)]
  apply expect_mono p hp
  intro z
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr (hR i (Function.update z i a))
  exact hp

theorem residual_cov_abs_le {N : ℕ} (p : Fin N→ℝ) (hp : ∀i,0<p i ∧ p i<1)
    (R : CircleTable N) (b : ℝ) (hb : 0≤b) (hR : ∀i z,|R i z|≤b)
    (i j : Fin N) (hij : i≠j) :
    |cov p (residualContrast p R (fun _ _=>0) i) (residualContrast p R (fun _ _=>0) j)|≤8*b^2:=by
  let C:=fun a c=>pairMarginal p (fun z=>R i z*R j z) i j a c-marginal p R i a*marginal p R j c
  have he : cov p (residualContrast p R (fun _ _=>0) i) (residualContrast p R (fun _ _=>0) j)=
      C false false-C false true-C true false+C true true:=by
    dsimp only [C]
    rw [cov,residual_pair_moment p R (fun _ _=>0) i j hij hp,
      residualContrast_mean p R (fun _ _=>0) i hp,residualContrast_mean p R (fun _ _=>0) j hp]
    simp only [Fintype.sum_bool,armSign,Bool.false_eq_true,ite_false,ite_true,residualEffect,sub_zero,nodeEffect]
    ring
  have hff:=abs_le.mp (pair_cov_abs_le p hp R b hb hR i j hij false false)
  have hft:=abs_le.mp (pair_cov_abs_le p hp R b hb hR i j hij false true)
  have htf:=abs_le.mp (pair_cov_abs_le p hp R b hb hR i j hij true false)
  have htt:=abs_le.mp (pair_cov_abs_le p hp R b hb hR i j hij true true)
  rw [he]
  dsimp only [C]
  apply abs_le.mpr
  constructor <;> linarith

end
end AronowAudit.P004.ComponentCompletion

namespace AronowAudit.P004
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter CLTCompletion
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

open ComponentCompletion

/-- T32(b), corrected diagonal and pair-covariance component bounds
in Lemma A.2, Supplement A pp. 2–3. The symbols b and c_N retain
their outcome-bound and maximum-neighborhood meanings. -/
theorem ht_variance_components {N : ℕ} (p b : ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (hN : 0 < N) (hp : 0 < p ∧ p < 1)
    (hb : ∀ i z, |R i z| < b) (hself : ∀ i, i ∈ B i) :
    let π := fun _ : Fin N => p
    let diagonal := (∑ i, (marginal π (fun i z => (R i z)^2) i true/p +
      marginal π (fun i z => (R i z)^2) i false/(1-p) - (nodeEffect π R i)^2))/(N : ℝ)^2
    0 ≤ diagonal ∧ diagonal ≤ b^2/(N*p)+b^2/(N*(1-p)) ∧
    ∀ a c : Bool,
      |(∑ i, ∑ j ∈ (B i).erase i, (pairMarginal π (fun z => R i z*R j z) i j a c -
        marginal π R i a*marginal π R j c))/(N : ℝ)^2| ≤
          2*b^2*((maxDegree B : ℝ)-1)/N := by
  let π:=fun _:Fin N=>p
  have hbpos : 0<b:=(abs_nonneg (R ⟨0,hN⟩ (fun _=>false))).trans_lt (hb _ _)
  have hR : ∀i z,|R i z|≤b:=fun i z=>(hb i z).le
  have hnode (i : Fin N) :
      marginal π (fun i z=>(R i z)^2) i true/p+
      marginal π (fun i z=>(R i z)^2) i false/(1-p)-(nodeEffect π R i)^2=
      variance π (residualContrast π R (fun _ _=>0) i):=by
    symm
    simpa only [sub_zero,residualEffect] using node_variance_identity π R (fun _ _=>0) i (fun _=>hp)
  dsimp only
  refine ⟨?_,?_,?_⟩
  · apply div_nonneg
    · apply Finset.sum_nonneg
      intro i _
      rw [hnode i]
      exact variance_nonneg π (fun _=>hp) _
    · exact sq_nonneg _
  · have hle (i : Fin N) : marginal π (fun i z=>(R i z)^2) i true/p+
        marginal π (fun i z=>(R i z)^2) i false/(1-p)-(nodeEffect π R i)^2≤b^2/p+b^2/(1-p):=by
      have h1:=div_le_div_of_nonneg_right (marginal_sq_le π (fun _=>hp) R b hbpos.le hR i true) hp.1.le
      have h0:=div_le_div_of_nonneg_right (marginal_sq_le π (fun _=>hp) R b hbpos.le hR i false) (sub_pos.mpr hp.2).le
      nlinarith [sq_nonneg (nodeEffect π R i)]
    calc
      _ ≤ (∑_i:Fin N,(b^2/p+b^2/(1-p)))/(N:ℝ)^2:=div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _=>hle i)) (sq_nonneg _)
      _ = _:=by
        simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]
        have hn : (N:ℝ)≠0:=by exact_mod_cast hN.ne'
        have hp0 : p≠0:=hp.1.ne'
        have hq : 1-p≠0:=(sub_pos.mpr hp.2).ne'
        field_simp
        <;> ring
  · intro a c
    exact bounded_local_sum B (2*b^2) hN (by positivity) hself _
      (fun i j hj=>pair_cov_abs_le π (fun _=>hp) R b hbpos.le hR i j (Finset.ne_of_mem_erase hj).symm a c)


/-- T32(a,c), corrected exact HT variance and explicit finite-N bound;
the local radius can be zero because B is supplied directly. -/
theorem ht_variance_bound {N : ℕ} (p b : ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (hN : 0 < N) (hp : 0 < p ∧ p < 1)
    (hb : ∀ i z, |R i z| < b) (hself : ∀ i, i ∈ B i)
    (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (houtside : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    variance (fun _ => p) (ht (fun _ => p) R) =
      secondMomentBound (fun _ => p) R B (fun _ _ => 0) - homophilyQ (fun _ => p) R B (fun _ _ => 0)/N ∧
    variance (fun _ => p) (ht (fun _ => p) R) ≤
      b^2/(N*p)+b^2/(N*(1-p))+8*b^2*((maxDegree B : ℝ)-1)/N := by
  let π:=fun _:Fin N=>p
  let T:=residualContrast π R (fun _ _=>0)
  have hbpos : 0<b:=(abs_nonneg (R ⟨0,hN⟩ (fun _=>false))).trans_lt (hb _ _)
  have hR : ∀i z,|R i z|≤b:=fun i z=>(hb i z).le
  constructor
  · have hz : augmented π R (fun _ _=>0)=ht π R:=by
      funext z
      simp only [augmented,ht,sub_zero,zero_add]
    have hi:=augmented_variance π R B (fun _ _=>0) hN (fun _=>hp) hself houtside
    rw [hz] at hi
    exact hi
  · have hlocal : (∑i,∑j,cov π (T i) (T j))=∑i,∑j∈B i,cov π (T i) (T j):=by
      apply Finset.sum_congr rfl
      intro i _
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun j _ hj=>GraphCompletion.residual_cov_zero π R _ i j (houtside i j hj))
    have hsplit : (∑i,∑j,cov π (T i) (T j))=
        (∑i,variance π (T i))+(∑i,∑j∈(B i).erase i,cov π (T i) (T j)):=by
      rw [hlocal,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [←Finset.sum_erase_add _ _ (hself i)]
      change _+cov π (T i) (T i)=cov π (T i) (T i)+_
      ring
    have hnode (i : Fin N) : marginal π (fun i z=>(R i z)^2) i true/p+
        marginal π (fun i z=>(R i z)^2) i false/(1-p)-(nodeEffect π R i)^2=
        variance π (T i):=by
      symm
      simpa only [sub_zero,residualEffect] using node_variance_identity π R (fun _ _=>0) i (fun _=>hp)
    have hdiagle:=(ht_variance_components p b R B hN hp hb hself).2.1
    have hdiagle' : (∑i,variance π (T i))/(N:ℝ)^2≤b^2/(N*p)+b^2/(N*(1-p)):=by
      convert hdiagle using 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (hnode i).symm
    have hoff:=bounded_local_sum B (8*b^2) hN (by positivity) hself
      (fun i j=>cov π (T i) (T j)) (fun i j hj=>residual_cov_abs_le π (fun _=>hp) R b hbpos.le hR i j (Finset.ne_of_mem_erase hj).symm)
    have he : ht π R=fun z=>(∑i,T i z)/(N:ℝ):=by
      funext z
      simp only [T,ht,residualContrast,sub_zero]
    change variance π (ht π R)≤_
    rw [he,variance_div,variance_sum,hsplit,add_div]
    linarith [(abs_le.mp hoff).2]

end
end AronowAudit.P004
