/- Portions adapted from StatLean, Apache-2.0; see NOTICE at the repository root.
Modified finite-array rank proof; local product-symmetry bridges. -/
import AronowAudit.P004.P004_KernelCompletion

/-!
The finite minimum-rank argument in `rank_count_bound` is adapted from
StatLean.HypothesisTesting.Randomization.ExactLevel.superUniform_randPValue
(Apache-2.0). The product-weight and coordinate-swap lemmas give the
finite-product rank bound.
-/
namespace AronowAudit.P004.MCCompletion
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def arrayWeight {A : Type*} {m : ℕ} (w : A→ℝ) (d : Fin m→A) : ℝ:=∏r,w (d r)
def arrayExpect {A : Type*} [Fintype A] {m : ℕ} (w : A→ℝ) (F : (Fin m→A)→ℝ) : ℝ:=
  ∑d,arrayWeight w d*F d

theorem arrayExpect_const {A : Type*} [Fintype A] {m : ℕ} (w : A→ℝ)
    (hw : ∑a,w a=1) (c : ℝ) : arrayExpect (m:=m) w (fun _=>c)=c:=by
  have hm : (∑d:Fin m→A,arrayWeight w d)=1:=by
    unfold arrayWeight
    rw [←Fintype.prod_sum]
    simp only [hw,Finset.prod_const_one]
  unfold arrayExpect
  rw [←Finset.sum_mul,hm,one_mul]

theorem arrayExpect_sum {A : Type*} [Fintype A] {m : ℕ} (w : A→ℝ)
    (F : Fin m→(Fin m→A)→ℝ) :
    arrayExpect w (fun d=>∑r,F r d)=∑r,arrayExpect w (F r):=by
  simp only [arrayExpect,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem arrayExpect_mono {A : Type*} [Fintype A] {m : ℕ} (w : A→ℝ)
    (hw : ∀a,0≤w a) (F G : (Fin m→A)→ℝ) (hFG : ∀d,F d≤G d) :
    arrayExpect w F≤arrayExpect w G:=by
  apply Finset.sum_le_sum
  intro d _
  exact mul_le_mul_of_nonneg_left (hFG d) (Finset.prod_nonneg (fun r _=>hw (d r)))

theorem arrayExpect_perm {A : Type*} [Fintype A] {m : ℕ} (w : A→ℝ)
    (σ : Equiv.Perm (Fin m)) (F : (Fin m→A)→ℝ) :
    arrayExpect w (fun d=>F (fun r=>d (σ r)))=arrayExpect w F:=by
  let e : (Fin m→A)≃(Fin m→A):={
    toFun:=fun d r=>d (σ r)
    invFun:=fun d r=>d (σ.symm r)
    left_inv:=by intro d;funext r;simp
    right_inv:=by intro d;funext r;simp }
  unfold arrayExpect
  rw [←e.sum_comp (fun d=>arrayWeight w d*F d)]
  apply Finset.sum_congr rfl
  intro d _
  change (∏r,w (d r))*F (fun r=>d (σ r))=(∏r,w (d (σ r)))*F (fun r=>d (σ r))
  rw [Equiv.prod_comp σ (fun r=>w (d r))]

def upperP {m : ℕ} (v : Fin m→ℝ) (r : Fin m) : ℝ:=
  ((Finset.univ.filter (fun s=>v r≤v s)).card:ℝ)/(m:ℝ)

theorem upperP_perm {m : ℕ} (v : Fin m→ℝ) (σ : Equiv.Perm (Fin m)) (r : Fin m) :
    upperP (fun s=>v (σ s)) r=upperP v (σ r):=by
  have hh : (Finset.univ.filter (fun s=>v (σ r)≤v (σ s))).card=
      (Finset.univ.filter (fun s=>v (σ r)≤v s)).card:=by
    apply Finset.card_bijective σ σ.bijective
    intro s
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  unfold upperP
  rw [hh]

theorem rank_count_bound {m : ℕ} (hm : 0<m) (v : Fin m→ℝ) (t : ℝ) (ht : 0≤t) :
    (∑r:Fin m,if upperP v r≤t then (1:ℝ) else 0)≤(m:ℝ)*t:=by
  have hmR : 0<(m:ℝ):=Nat.cast_pos.mpr hm
  rw [Finset.sum_boole]
  let S:=Finset.univ.filter (fun r=>upperP v r≤t)
  change (S.card:ℝ)≤_
  rcases S.eq_empty_or_nonempty with hs|hs
  · rw [hs]
    simp only [Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg hmR.le ht
  · obtain ⟨r,hr,hmin⟩:=Finset.exists_min_image S v hs
    have hsub : S⊆Finset.univ.filter (fun s=>v r≤v s):=by
      intro s hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmin s hs⟩
    have hcard : (S.card:ℝ)≤((Finset.univ.filter (fun s=>v r≤v s)).card:ℝ):=by
      exact_mod_cast Finset.card_le_card hsub
    have hp := (Finset.mem_filter.mp hr).2
    have hupper : ((Finset.univ.filter (fun s=>v r≤v s)).card:ℝ)≤(m:ℝ)*t:=by
      simpa only [mul_comm] using (div_le_iff₀ hmR).mp hp
    exact hcard.trans hupper

theorem product_rank_bound {A : Type*} [Fintype A] {m : ℕ} (hm : 0<m)
    (w : A→ℝ) (hwn : ∀a,0≤w a) (hw : ∑a,w a=1) (T : A→ℝ) (t : ℝ) (ht : 0≤t) :
    arrayExpect w (fun d=>if upperP (fun r=>T (d r)) ⟨0,hm⟩≤t then (1:ℝ) else 0)≤t:=by
  let zero : Fin m:=⟨0,hm⟩
  let F:=fun (r : Fin m) (d : Fin m→A)=>if upperP (fun s=>T (d s)) r≤t then (1:ℝ) else 0
  have he (r : Fin m) : arrayExpect w (F r)=arrayExpect w (F zero):=by
    have hh:=arrayExpect_perm w (Equiv.swap zero r) (F zero)
    have hf : (fun d=>F zero (fun s=>d (Equiv.swap zero r s)))=F r:=by
      funext d
      dsimp only [F]
      rw [upperP_perm (fun s=>T (d s)) (Equiv.swap zero r) zero]
      simp only [Equiv.swap_apply_left]
    rw [hf] at hh
    exact hh
  have hsum : arrayExpect w (fun d=>∑r,F r d)=(m:ℝ)*arrayExpect w (F zero):=by
    rw [arrayExpect_sum]
    simp_rw [he]
    simp
  have hle:=arrayExpect_mono w hwn (fun d=>∑r,F r d) (fun _=>(m:ℝ)*t)
    (fun d=>rank_count_bound hm (fun r=>T (d r)) t ht)
  rw [hsum,arrayExpect_const w hw] at hle
  exact le_of_mul_le_mul_left hle (Nat.cast_pos.mpr hm)

theorem mc_upperP {N P : ℕ} (T : Assignment N→ℝ) (d : Fin (P+1)→Assignment N) :
    upperP (fun r=>|T (d r)|) 0=mcPlusPvalue T d:=by
  let S:=Finset.univ.filter (fun r:Fin (P+1)=>|T (d 0)|≤|T (d r)|)
  have hz : (0:Fin (P+1))∈S:=by simp [S]
  have hs : S.erase 0=Finset.univ.filter (fun r:Fin (P+1)=>r≠0 ∧ |T (d 0)|≤|T (d r)|):=by
    ext r
    simp only [S,Finset.mem_erase,Finset.mem_filter,Finset.mem_univ,true_and]
  have hc : S.card=mcExceedances T d+1:=by
    rw [←Finset.card_erase_add_one hz,hs]
    rfl
  change (S.card:ℝ)/(P+1:ℕ)=_
  rw [hc]
  simp only [mcPlusPvalue,Nat.cast_add,Nat.cast_one,add_comm]

end
end AronowAudit.P004.MCCompletion

namespace AronowAudit.P004
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter MCCompletion
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

/-- T13(a–b), corrected randomization level for every finite P, including
ties, and the finite bound for B/P. Sharp-null outcomes enter via fixed T. -/
theorem mc_exact_level {N P : ℕ} (p : Fin N → ℝ) (T : Assignment N → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hP : 0 < P) (α : ℝ) (hα : 0 < α ∧ α < 1) :
    (∑ draws : Fin (P+1) → Assignment N,
      mcDrawWeight p draws * (if mcPlusPvalue T draws ≤ α then 1 else 0)) ≤ α ∧
    (∑ draws : Fin (P+1) → Assignment N,
      mcDrawWeight p draws * (if (mcExceedances T draws : ℝ) / P ≤ α then 1 else 0)) ≤
        (Int.floor (α*P) + 1 : ℝ) / (P+1) ∧
    (Int.floor (α*P) + 1 : ℝ) / (P+1) ≤ α + (1-α)/(P+1) := by
  have hwn (z : Assignment N) : 0≤designWeight p z:=by
    unfold designWeight
    apply Finset.prod_nonneg
    intro i _
    cases hz : z i <;> simp [coin,hz]
    · linarith [(hp i).2]
    · exact (hp i).1
  have hw : (∑z,designWeight p z)=1:=design_normalized p
  have hpr : 0<(P:ℝ):=Nat.cast_pos.mpr hP
  have hmr : 0<(P:ℝ)+1:=by positivity
  let t:=((Int.floor (α*(P:ℝ)):ℤ):ℝ)+1
  have ht : 0≤t:=by
    have hf : 0≤Int.floor (α*(P:ℝ)):=Int.floor_nonneg.mpr (mul_nonneg hα.1.le hpr.le)
    have hfr : (0:ℝ)≤(Int.floor (α*(P:ℝ)):ℤ):=by exact_mod_cast hf
    dsimp [t]
    linarith
  have hfirst:=product_rank_bound (Nat.zero_lt_succ P) (designWeight p) hwn hw (fun z=>|T z|) α hα.1.le
  have hsecond:=product_rank_bound (Nat.zero_lt_succ P) (designWeight p) hwn hw (fun z=>|T z|) (t/(P+1)) (div_nonneg ht hmr.le)
  change arrayExpect (designWeight p) (fun d : Fin (P+1)→Assignment N=>if upperP (fun r=>|T (d r)|) 0≤α then (1:ℝ) else 0)≤α at hfirst
  change arrayExpect (designWeight p) (fun d : Fin (P+1)→Assignment N=>if upperP (fun r=>|T (d r)|) 0≤t/(P+1) then (1:ℝ) else 0)≤t/(P+1) at hsecond
  simp_rw [mc_upperP T] at hfirst hsecond
  refine ⟨hfirst,?_,?_⟩
  · change arrayExpect (designWeight p) (fun d=>if (mcExceedances T d:ℝ)/(P:ℝ)≤α then (1:ℝ) else 0)≤t/(P+1)
    apply (arrayExpect_mono (designWeight p) hwn _ _ ?_).trans hsecond
    intro d
    have himp : (mcExceedances T d:ℝ)/(P:ℝ)≤α→mcPlusPvalue T d≤t/(P+1):=by
      intro hd
      have hbr : (mcExceedances T d:ℝ)≤α*(P:ℝ):=(div_le_iff₀ hpr).mp hd
      have hbi : (mcExceedances T d:ℤ)≤Int.floor (α*(P:ℝ)):=Int.le_floor.mpr (by exact_mod_cast hbr)
      have hb : (mcExceedances T d:ℝ)≤(Int.floor (α*(P:ℝ)):ℤ):=by exact_mod_cast hbi
      unfold mcPlusPvalue
      apply div_le_div_of_nonneg_right _ hmr.le
      dsimp [t]
      linarith
    split_ifs <;> simp_all
  · have hf:=Int.floor_le (α*(P:ℝ))
    apply (div_le_iff₀ hmr).mpr
    have he : (α+(1-α)/((P:ℝ)+1))*((P:ℝ)+1)=α*(P:ℝ)+1:=by field_simp;ring
    rw [he]
    linarith


end
end AronowAudit.P004
