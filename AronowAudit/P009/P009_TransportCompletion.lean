import AronowAudit.P009.P009_ValidityCompletion
namespace AronowAudit.P009.ValidityCompletion
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

theorem normalized_holder_factor {n : ℕ} (hn : 0<n) (r : ℝ) (hr : 1<r)
    (S : ℝ) (hS : 0≤S) :
    Real.rpow (n:ℝ) (-1/r)*Real.rpow (S/(n:ℝ)) (1/(r/(r-1)))=
      Real.rpow S (1/(r/(r-1)))/(n:ℝ) := by
  simp only [Real.rpow_eq_pow]
  have hnR : 0<(n:ℝ) := by positivity
  have hp : r.HolderConjugate (r/(r-1)) := Real.holderConjugate_iff_eq_conjExponent hr |>.mpr rfl
  have he : 1/r+1/(r/(r-1))=1 := by simpa only [one_div] using (Real.holderConjugate_iff.mp hp).2
  have hpow : (n:ℝ)^(1/r)*(n:ℝ)^(1/(r/(r-1)))=(n:ℝ) := by
    rw [←Real.rpow_add hnR,he,Real.rpow_one]
  rw [Real.div_rpow hS hnR.le,show -1/r= -(1/r) by ring,Real.rpow_neg hnR.le]
  calc
    _ = S^(1/(r/(r-1)))/((n:ℝ)^(1/r)*(n:ℝ)^(1/(r/(r-1)))) := by ring
    _ = _ := by rw [hpow]

theorem assignment_ATE_lipschitz_completed {n : ℕ} (hn : 0<n) (E : Experiment n)
    (K r : ℝ) (hK : BoundedEffects E K) (hr : 1≤r) (z z' : Assignment n) :
    |ateAt E z-ateAt E z'| ≤
      2*K*Real.rpow (n:ℝ) (-1/r)*conjugateC E r*lrDistance r z z' := by
  classical
  have hnR : 0<(n:ℝ) := by positivity
  have hk : 0≤K := (abs_nonneg _).trans (hK ⟨0,hn⟩ z)
  apply (assignment_ATE_hamming hn E K hK z z').trans
  by_cases hr1 : r=1
  · subst r
    have hb (i : Fin n) : outgoing E i≤Cinf E :=
      le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)
    have hs : (∑ i,|bit (z i)-bit (z' i)| *outgoing E i)≤
        (∑ i,|bit (z i)-bit (z' i)|)*Cinf E := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _))
    have hl : lrDistance 1 z z'=∑ i,|bit (z i)-bit (z' i)| := by
      simp [lrDistance]
    simp only [conjugateC,ite_true,hl,Real.rpow_eq_pow,div_one,Real.rpow_neg_one]
    calc
      _ ≤ 2*K/(n:ℝ)*((∑ i,|bit (z i)-bit (z' i)|)*Cinf E) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  · have hr' : 1<r := lt_of_le_of_ne hr (Ne.symm hr1)
    have hp : r.HolderConjugate (r/(r-1)) := Real.holderConjugate_iff_eq_conjExponent hr' |>.mpr rfl
    have hs0 := Real.inner_le_Lp_mul_Lq_of_nonneg (s:=Finset.univ)
      (f:=fun i=>|bit (z i)-bit (z' i)|) (g:=outgoing E) hp
      (fun i _=>abs_nonneg _) (fun i _=>outgoing_nonneg E i)
    have hs : (∑ i,|bit (z i)-bit (z' i)| *outgoing E i) ≤
        lrDistance r z z' * Real.rpow (∑ i,Real.rpow (outgoing E i) (r/(r-1))) (1/(r/(r-1))) := by
      simpa only [lrDistance,Real.rpow_eq_pow] using hs0
    have hnorm := normalized_holder_factor hn r hr'
      (∑ i,Real.rpow (outgoing E i) (r/(r-1)))
      (Finset.sum_nonneg (fun i _=>Real.rpow_nonneg (outgoing_nonneg E i) _))
    calc
      _ ≤ 2*K/(n:ℝ)*(lrDistance r z z'*
          Real.rpow (∑ i,Real.rpow (outgoing E i) (r/(r-1))) (1/(r/(r-1)))) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 2*K*(Real.rpow (∑ i,Real.rpow (outgoing E i) (r/(r-1))) (1/(r/(r-1)))/(n:ℝ))*
          lrDistance r z z' := by ring
      _ = _ := by rw [←hnorm]; simp only [conjugateC,if_neg hr1,Cp];ring
end
end AronowAudit.P009.ValidityCompletion

namespace AronowAudit.P009.ValidityCompletion
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 600000

def productCoupling {Ω : Type*} [Fintype Ω] (P Q : Law Ω) : Law (Ω×Ω) where
  mass zz:=P.mass zz.1*Q.mass zz.2
  nonneg zz:=mul_nonneg (P.nonneg _) (Q.nonneg _)
  total:=by simp only [Fintype.sum_prod_type,←Finset.mul_sum,Q.total,mul_one,P.total]

theorem productCoupling_marginals {Ω : Type*} [Fintype Ω] (P Q : Law Ω) :
    Coupling P Q (productCoupling P Q) := by
  constructor
  · intro x
    simp [productCoupling,←Finset.mul_sum,Q.total]
  · intro y
    simp [productCoupling,←Finset.sum_mul,P.total]

theorem coupling_mean_left {Ω : Type*} [Fintype Ω] (P Q : Law Ω)
    (J : Law (Ω×Ω)) (hJ : Coupling P Q J) (f : Ω→ℝ) :
    mean J (fun zz=>f zz.1)=mean P f := by
  unfold mean
  rw [Fintype.sum_prod_type]
  simp_rw [←Finset.sum_mul,hJ.1]

theorem coupling_mean_right {Ω : Type*} [Fintype Ω] (P Q : Law Ω)
    (J : Law (Ω×Ω)) (hJ : Coupling P Q J) (f : Ω→ℝ) :
    mean J (fun zz=>f zz.2)=mean Q f := by
  unfold mean
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [←Finset.sum_mul,hJ.2]

theorem coupling_function_bound {Ω : Type*} [Fintype Ω] (P Q : Law Ω)
    (J : Law (Ω×Ω)) (hJ : Coupling P Q J) (f : Ω→ℝ)
    (cost : Ω→Ω→ℝ) (L : ℝ) (hLip : ∀x y,|f x-f y|≤L*cost x y) :
    |mean P f-mean Q f|≤L*mean J (fun zz=>cost zz.1 zz.2) := by
  rw [←coupling_mean_left P Q J hJ f,←coupling_mean_right P Q J hJ f,←mean_sub]
  calc
    _ ≤ ∑ zz,|J.mass zz*(f zz.1-f zz.2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ zz,J.mass zz*(L*cost zz.1 zz.2) := by
      apply Finset.sum_le_sum
      intro zz _
      rw [abs_mul,abs_of_nonneg (J.nonneg zz)]
      exact mul_le_mul_of_nonneg_left (hLip _ _) (J.nonneg _)
    _ = _ := by simp only [mean,Finset.mul_sum];apply Finset.sum_congr rfl;intro zz _;ring

theorem finite_transport_bound {n : ℕ} (P Q : Law (Assignment n)) (f : Assignment n→ℝ)
    (r L : ℝ) (hL : 0≤L) (hLip : ∀z z',|f z-f z'|≤L*lrDistance r z z') :
    |mean P f-mean Q f|≤L*wasserstein r P Q := by
  have hex : Set.Nonempty {v | ∃J : Law (Assignment n×Assignment n),Coupling P Q J ∧
      v=mean J (fun zz=>lrDistance r zz.1 zz.2)} :=
    ⟨_,productCoupling P Q,productCoupling_marginals P Q,rfl⟩
  rcases eq_or_lt_of_le hL with he | hp
  · have hb:=coupling_function_bound P Q (productCoupling P Q) (productCoupling_marginals P Q)
      f (lrDistance r) L hLip
    rw [←he] at hb ⊢
    simpa using hb
  · rw [mul_comm]
    apply (div_le_iff₀ hp).mp
    apply le_csInf hex
    rintro v ⟨J,hJ,rfl⟩
    exact (div_le_iff₀ hp).mpr (by
      rw [mul_comm]
      exact coupling_function_bound P Q J hJ f (lrDistance r) L hLip)
end
end AronowAudit.P009.ValidityCompletion

namespace AronowAudit.P009.ValidityCompletion
open scoped BigOperators
noncomputable section

theorem external_validity_wasserstein_completed {n : ℕ} (hn : 0<n) (E : Experiment n)
    (Q : Law (Assignment n)) (K r : ℝ) (hK : BoundedEffects E K) (hr : 1≤r) :
    |eate E-eate {E with design:=Q}| ≤
      2*K*Real.rpow (n:ℝ) (-1/r)*conjugateC E r*wasserstein r E.design Q := by
  classical
  have hk : 0≤K := (abs_nonneg _).trans (hK ⟨0,hn⟩ (fun _=>false))
  have hc : 0≤conjugateC E r := by
    unfold conjugateC
    split_ifs
    · exact (outgoing_nonneg E ⟨0,hn⟩).trans
        (le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self (⟨0,hn⟩ : Fin n)))
    · unfold Cp
      exact Real.rpow_nonneg (div_nonneg
        (Finset.sum_nonneg (fun i _=>Real.rpow_nonneg (outgoing_nonneg E i) _)) (Nat.cast_nonneg _)) _
  have hL : 0≤2*K*Real.rpow (n:ℝ) (-1/r)*conjugateC E r :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hc
  change |mean E.design (ateAt E)-mean Q (ateAt E)|≤_
  exact finite_transport_bound E.design Q (ateAt E) r _ hL
    (assignment_ATE_lipschitz_completed hn E K r hK hr)
end
end AronowAudit.P009.ValidityCompletion

namespace AronowAudit.P009
/-- T38, Lemma 2 (p. 695): the assignment-conditional ATE has the printed
L_r Lipschitz constant for every real r≥1, including the C_infinity endpoint. -/
theorem assignment_ATE_lipschitz {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (K r : ℝ) (hK : BoundedEffects E K) (hr : 1 ≤ r) (z z' : Assignment n) :
    |ateAt E z-ateAt E z'| ≤
      2*K*Real.rpow (n:ℝ) (-1/r)*conjugateC E r*lrDistance r z z' := by
  exact ValidityCompletion.assignment_ATE_lipschitz_completed hn E K r hK hr z z'

/-- T39, Proposition 13 (p. 696): the EATE difference under two designs is
bounded using the FIRST-order Wasserstein distance with L_r ground metric. -/
theorem external_validity_wasserstein {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (Q : Law (Assignment n)) (K r : ℝ) (hK : BoundedEffects E K) (hr : 1 ≤ r) :
    |eate E-eate {E with design := Q}| ≤
      2*K*Real.rpow (n:ℝ) (-1/r)*conjugateC E r*wasserstein r E.design Q := by
  exact ValidityCompletion.external_validity_wasserstein_completed hn E Q K r hK hr

end AronowAudit.P009

