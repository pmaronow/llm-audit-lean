/- Exact complete-randomization conditional finite-law identities, proved by coordinate permutations outside the mask. -/
import AronowAudit.P009.P009_CompleteMixing
namespace AronowAudit.P009.CompleteConditional
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
open CompleteMixing

lemma mean_support_congr {Ω : Type*} [Fintype Ω] (P : Law Ω) (F G : Ω→ℝ)
    (h : ∀ w,0<P.mass w→F w=G w) : mean P F=mean P G := by
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : 0<P.mass w
  · rw [h w hw]
  · have hz : P.mass w=0 := le_antisymm (le_of_not_gt hw) (P.nonneg w)
    simp [hz]

lemma supported_treated_count {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (z : Assignment n) (hz : 0<E.design.mass z) : (∑ i,bit (z i))=(m:ℝ) := by
  have hc : (∑ i,if z i then (1:ℕ) else 0)=m := by
    by_contra hh
    have he : E.design.mass z=0 := by rw [hCR.2.2 z]; exact if_neg hh
    linarith
  simp only [bit]
  exact_mod_cast hc

lemma outside_weighted_mean_equal {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (H : Finset (Fin n)) (i j : Fin n) (hi : i∉H) (hj : j∉H)
    (F : Assignment n→ℝ) (hF : DependsOn F (H : Set (Fin n))) :
    mean E.design (fun z=>bit (z i)*F z)=mean E.design (fun z=>bit (z j)*F z) := by
  let σ := Equiv.swap i j
  have hfixed (z : Assignment n) : F (relabel σ z)=F z := by
    apply hF
    intro l hl
    have hli : l≠i := by intro he; subst l; exact hi hl
    have hlj : l≠j := by intro he; subst l; exact hj hl
    simp [relabel,σ,Equiv.swap_apply_def,hli,hlj]
  have hh := complete_mean_relabel E m hCR σ (fun z=>bit (z i)*F z)
  simp_rw [hfixed] at hh
  simpa [relabel,σ] using hh.symm

lemma conditional_weighted_count {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (H : Finset (Fin n)) (i : Fin n) (hi : i∉H)
    (F : Assignment n→ℝ) (hF : DependsOn F (H : Set (Fin n))) :
    ((n:ℝ)-(H.card:ℝ))*mean E.design (fun z=>bit (z i)*F z)=
      (m:ℝ)*mean E.design F-mean E.design (fun z=>(∑ j∈H,bit (z j))*F z) := by
  have hsupport : mean E.design (fun z=>(∑ j,bit (z j))*F z)=(m:ℝ)*mean E.design F := by
    rw [←mean_const_mul]
    apply mean_support_congr
    intro z hz
    rw [supported_treated_count E m hCR z hz]
  have hsplit : mean E.design (fun z=>(∑ j,bit (z j))*F z)=
      mean E.design (fun z=>(∑ j∈H,bit (z j))*F z)+
      ∑ j∈Finset.univ\H,mean E.design (fun z=>bit (z j)*F z) := by
    have hp (z : Assignment n) : (∑ j,bit (z j))*F z=
        (∑ j∈H,bit (z j))*F z + ∑ j∈Finset.univ\H,bit (z j)*F z := by
      rw [←Finset.sum_mul]
      rw [←Finset.sum_sdiff (Finset.subset_univ H) (f:=fun j=>bit (z j))]
      ring
    simp_rw [hp]
    rw [mean_add]
    congr 1
    unfold mean
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hout : (∑ j∈Finset.univ\H,mean E.design (fun z=>bit (z j)*F z))=
      ((n:ℝ)-(H.card:ℝ))*mean E.design (fun z=>bit (z i)*F z) := by
    calc
      _ = ∑ j∈Finset.univ\H,mean E.design (fun z=>bit (z i)*F z) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact outside_weighted_mean_equal E m hCR H j i (Finset.mem_sdiff.mp hj).2 hi F hF
      _ = _ := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ H),Finset.card_univ,Fintype.card_fin,Nat.cast_sub (by simpa using Finset.card_le_univ H)]
  rw [hout,hsupport] at hsplit
  linarith

lemma mean_mono {Ω : Type*} [Fintype Ω] (P : Law Ω) (F G : Ω→ℝ)
    (h : ∀ w,F w ≤ G w) : mean P F ≤ mean P G :=
  Finset.sum_le_sum (fun w _=>mul_le_mul_of_nonneg_left (h w) (P.nonneg w))

lemma weighted_abs_bound {Ω : Type*} [Fintype Ω] (P : Law Ω) (A F : Ω→ℝ)
    (C : ℝ) (hA : ∀ w,|A w| ≤ C) :
    |mean P (fun w=>A w*F w)| ≤ C*mean P (fun w=>|F w|) := by
  calc
    _ ≤ mean P (fun w=>|A w*F w|) := BernoulliCompletion.mean_abs_le P _
    _ ≤ mean P (fun w=>C*|F w|) := mean_mono P _ _ (fun w=>by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hA w) (abs_nonneg _))
    _ = _ := mean_const_mul P C _

lemma bit_bounds (b : Bool) : 0 ≤ bit b ∧ bit b ≤ 1 := by cases b <;> simp [bit]

lemma mask_count_bounds {n : ℕ} (H : Finset (Fin n)) (z : Assignment n) :
    0 ≤ (∑ j∈H,bit (z j)) ∧ (∑ j∈H,bit (z j)) ≤ (H.card:ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun j _=>(bit_bounds _).1)
  · calc
      _ ≤ ∑ _j∈H,(1:ℝ) := Finset.sum_le_sum (fun j _=>(bit_bounds _).2)
      _ = _ := by simp

lemma complete_centered_weighted_bound {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (H : Finset (Fin n)) (i : Fin n) (hi : i∉H)
    (F : Assignment n→ℝ) (hF : DependsOn F (H : Set (Fin n))) :
    |mean E.design (fun z=>(bit (z i)-(m:ℝ)/n)*F z)| ≤
      (2*(H.card:ℝ)/(n:ℝ))*mean E.design (fun z=>|F z|) := by
  have hn : (0:ℝ)<n := by exact_mod_cast (lt_trans hCR.1 hCR.2.1)
  have hp := fixed_count_fraction E m hCR
  let p := (m:ℝ)/n
  let A := |mean E.design (fun z=>(bit (z i)-p)*F z)|
  let M := mean E.design (fun z=>|F z|)
  have hM : 0 ≤ M := Finset.sum_nonneg (fun z _=>mul_nonneg (E.design.nonneg z) (abs_nonneg _))
  have hA : 0 ≤ A := abs_nonneg _
  have htriv : A ≤ M := by
    have ht := weighted_abs_bound E.design (fun z=>bit (z i)-p) F 1 (fun z=>by
      have hb := bit_bounds (z i)
      apply abs_le.mpr
      dsimp [p]
      constructor <;> linarith [hp.1,hp.2])
    simpa only [one_mul] using ht
  have hid : ((n:ℝ)-(H.card:ℝ))*mean E.design (fun z=>(bit (z i)-p)*F z)=
      mean E.design (fun z=>(p*(H.card:ℝ)-(∑ j∈H,bit (z j)))*F z) := by
    have hw := conditional_weighted_count E m hCR H i hi F hF
    have hn0 := hn.ne'
    have hnp : (n:ℝ)*p=(m:ℝ) := by dsimp [p]; field_simp
    have hleft : mean E.design (fun z=>(bit (z i)-p)*F z)=
        mean E.design (fun z=>bit (z i)*F z)-p*mean E.design F := by
      rw [←mean_const_mul,←mean_sub]
      congr 1
      funext z
      ring
    have hright : mean E.design (fun z=>(p*(H.card:ℝ)-(∑ j∈H,bit (z j)))*F z)=
        p*(H.card:ℝ)*mean E.design F-mean E.design (fun z=>(∑ j∈H,bit (z j))*F z) := by
      rw [←mean_const_mul,←mean_sub]
      congr 1
      funext z
      ring
    rw [hleft,hright]
    nlinarith [congrArg (fun a:ℝ=>a*mean E.design F) hnp]
  have hH : (H.card:ℝ) ≤ n := by exact_mod_cast (by simpa using Finset.card_le_univ H : H.card ≤ n)
  have hscaled : ((n:ℝ)-(H.card:ℝ))*A ≤ (H.card:ℝ)*M := by
    have hh := weighted_abs_bound E.design (fun z=>p*(H.card:ℝ)-(∑ j∈H,bit (z j))) F (H.card:ℝ)
      (fun z=>by
        have hc := mask_count_bounds H z
        have hpH0 : 0 ≤ p*(H.card:ℝ) := mul_nonneg hp.1 (Nat.cast_nonneg _)
        have hpH1 : p*(H.card:ℝ) ≤ (H.card:ℝ) := mul_le_of_le_one_left (Nat.cast_nonneg _) hp.2
        apply abs_le.mpr
        constructor <;> linarith)
    rw [←hid,abs_mul,abs_of_nonneg (sub_nonneg.mpr hH)] at hh
    exact hh
  -- Normalize the final scalar inequality without dividing by the mask complement.
  change A ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hn).mpr
  by_cases hs : 2*(H.card:ℝ) ≤ n
  · nlinarith [mul_nonneg (by linarith : 0 ≤ (n:ℝ)-2*(H.card:ℝ)) hA]
  · have hs' : (n:ℝ) ≤ 2*(H.card:ℝ) := le_of_lt (lt_of_not_ge hs)
    have h1 := mul_le_mul_of_nonneg_right htriv hn.le
    have h2 := mul_le_mul_of_nonneg_right hs' hM
    nlinarith

lemma complete_marginal_true {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (i : Fin n) : marginal E i true=(m:ℝ)/n := by
  have hn : (n:ℝ)≠0 := by exact_mod_cast (lt_trans hCR.1 hCR.2.1).ne'
  have hh := conditional_weighted_count E m hCR ∅ i (by simp) (fun _=>1) (by intro a b h; rfl)
  simp only [Finset.card_empty,Nat.cast_zero,sub_zero,Finset.sum_empty,zero_mul,
    mul_one,mean_const,sub_zero] at hh
  have hmeanbit : mean E.design (fun z=>bit (z i))=marginal E i true := by
    unfold marginal prob
    apply congrArg (mean E.design)
    funext z
    cases hz : z i <;> simp [bit,hz]
  rw [hmeanbit] at hh
  apply (eq_div_iff hn).mpr
  nlinarith

lemma complete_marginal_false {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (i : Fin n) : marginal E i false=1-(m:ℝ)/n := by
  have hh := marginal_partition E i
  rw [complete_marginal_true E m hCR i] at hh
  linarith

lemma complete_indicator_weighted_bound {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (H : Finset (Fin n)) (i : Fin n) (hi : i∉H)
    (F : Assignment n→ℝ) (hF : DependsOn F (H : Set (Fin n))) (b : Bool) :
    |mean E.design (fun z=>((if z i=b then (1:ℝ) else 0)-marginal E i b)*F z)| ≤
      (2*(H.card:ℝ)/(n:ℝ))*mean E.design (fun z=>|F z|) := by
  have hh := complete_centered_weighted_bound E m hCR H i hi F hF
  cases b
  · rw [complete_marginal_false E m hCR i]
    have he : (fun z : Assignment n=>((if z i=false then (1:ℝ) else 0)-(1-(m:ℝ)/n))*F z)=
        (fun z=> -((bit (z i)-(m:ℝ)/n)*F z)) := by
      funext z
      cases hz : z i <;> simp [bit,hz] <;> ring
    rw [he]
    have hm : mean E.design (fun z=> -((bit (z i)-(m:ℝ)/n)*F z))=
        -mean E.design (fun z=>(bit (z i)-(m:ℝ)/n)*F z) := by simp [mean,mul_neg,Finset.sum_neg_distrib]
    rw [hm,abs_neg]
    exact hh
  · rw [complete_marginal_true E m hCR i]
    exact hh

lemma conditional_mean_difference {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω→Prop)
    (F : Ω→ℝ) (hp : prob P A≠0) :
    cmean P A F-mean P F=
      mean P (fun w=>((if A w then (1:ℝ) else 0)-prob P A)*F w)/prob P A := by
  have he : mean P (fun w=>((if A w then (1:ℝ) else 0)-prob P A)*F w)=
      mean P (fun w=>if A w then F w else 0)-prob P A*mean P F := by
    rw [←mean_const_mul,←mean_sub]
    congr 1
    funext w
    split_ifs <;> ring
  rw [he]
  unfold cmean
  field_simp

lemma complete_conditional_mean_bound {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (H : Finset (Fin n)) (i : Fin n) (hi : i∉H)
    (F : Assignment n→ℝ) (hF : DependsOn F (H : Set (Fin n))) (b : Bool)
    (hp : 0 < marginal E i b) :
    |cmean E.design (fun z=>z i=b) F-mean E.design F| ≤
      (2*(H.card:ℝ)/(n:ℝ))*(marginal E i b)⁻¹*mean E.design (fun z=>|F z|) := by
  have hh := complete_indicator_weighted_bound E m hCR H i hi F hF b
  rw [conditional_mean_difference E.design (fun z=>z i=b) F hp.ne',abs_div]
  have hp' : 0 < prob E.design (fun z=>z i=b) := hp
  rw [abs_of_pos hp']
  calc
    _ ≤ ((2*(H.card:ℝ)/(n:ℝ))*mean E.design (fun z=>|F z|))/marginal E i b :=
      div_le_div_of_nonneg_right (by
        convert hh using 1
        congr 1
        apply congrArg (mean E.design)
        funext w
        unfold marginal
        split_ifs <;> rfl) hp.le
    _ = _ := by ring

end
end AronowAudit.P009.CompleteConditional

