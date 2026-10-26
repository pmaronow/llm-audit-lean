import AronowAudit.P009.P009_BernoulliCompletion

/-!
Paired-randomization finite identities and consistency under the P009
assumptions. The paired mass factors over closed coordinate blocks;
full-cube interference then gives covariance cancellation. Exact arm counts
identify HT and Hájek on support. A finite second-moment bound supplies all
three printed rate terms.
-/

namespace AronowAudit.P009.PairedCompletion
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

/-- A finite product-shaped mass factors expectations even when the two
factor masses are not separately normalized. The design's total mass suffices. -/
theorem mean_product_of_partition_mass {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (P : Law Ω) (e : Ω ≃ A × B) (q : A → ℝ) (r : B → ℝ)
    (hMass : ∀ x y, P.mass (e.symm (x,y)) = q x*r y) (F : A → ℝ) (G : B → ℝ) :
    mean P (fun z => F (e z).1*G (e z).2) =
      mean P (fun z => F (e z).1)*mean P (fun z => G (e z).2) := by
  have htotal : (∑ x, q x)*(∑ y, r y) = 1 := by
    rw [Finset.sum_mul_sum]
    calc
      _ = ∑ z, P.mass z := by
        rw [← e.symm.sum_comp, Fintype.sum_prod_type]
        simp only [hMass]
      _ = 1 := P.total
  have hF : mean P (fun z => F (e z).1) = (∑ x, q x*F x)*(∑ y, r y) := by
    unfold mean
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    simp only [Equiv.apply_symm_apply, hMass]
    ring
  have hG : mean P (fun z => G (e z).2) = (∑ x, q x)*(∑ y, r y*G y) := by
    unfold mean
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    simp only [Equiv.apply_symm_apply, hMass]
    ring
  have hFG : mean P (fun z => F (e z).1*G (e z).2) =
      (∑ x, q x*F x)*(∑ y, r y*G y) := by
    unfold mean
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    simp only [Equiv.apply_symm_apply, hMass]
    ring
  rw [hF,hG,hFG]
  calc
    _ = ((∑ x, q x)*(∑ y, r y))*((∑ x, q x*F x)*(∑ y, r y*G y)) := by rw [htotal]; ring
    _ = _ := by ring

/-- Simultaneous treatment reversal preserves the actual paired law. -/
def flipAll {n : ℕ} : Assignment n ≃ Assignment n where
  toFun := fun z i => !(z i)
  invFun := fun z i => !(z i)
  left_inv := by intro z; funext i; simp
  right_inv := by intro z; funext i; simp

theorem mass_flipAll {n : ℕ} (E : Experiment n) (ρ : Pairing n) (hPair : Paired E ρ)
    (z : Assignment n) : E.design.mass (flipAll z) = E.design.mass z := by
  rw [hPair.2, hPair.2]
  congr 1
  apply propext
  apply forall_congr'
  intro i
  cases hi : z i <;> cases hj : z (ρ.partner i) <;> simp [flipAll, hi, hj]

theorem marginal_half {n : ℕ} (E : Experiment n) (ρ : Pairing n) (hPair : Paired E ρ)
    (i : Fin n) (b : Bool) : marginal E i b = 1/2 := by
  have he : marginal E i true = marginal E i false := by
    unfold marginal prob mean
    have hh := flipAll.sum_comp (fun z => E.design.mass z*(@ite ℝ (z i = true) (Classical.propDecidable _) 1 0))
    rw [← hh]
    apply Finset.sum_congr rfl
    intro z _
    rw [mass_flipAll E ρ hPair]
    cases hz : z i <;> simp [flipAll, hz]
  have hs := marginal_partition E i
  cases b <;> linarith

/-- A support assignment has one treated member of every pair. -/
theorem supported_opposite {n : ℕ} (E : Experiment n) (ρ : Pairing n) (hPair : Paired E ρ)
    (z : Assignment n) (hz : 0 < E.design.mass z) : ∀ i, z i ≠ z (ρ.partner i) := by
  have hm := hPair.2 z
  by_contra hn
  rw [ite_eq_right hn] at hm
  rw [hm] at hz
  exact (lt_irrefl 0 hz)

/-- Paired randomization factors across any partition into whole pairs. -/
theorem mean_product_of_closed_partition {n : ℕ} (E : Experiment n) (ρ : Pairing n)
    (hPair : Paired E ρ) (S : Set (Fin n)) (hS : ∀ i, ρ.partner i ∈ S ↔ i ∈ S)
    (f g : Assignment n → ℝ) (hf : DependsOn f S) (hg : DependsOn g Sᶜ) :
    mean E.design (fun z => f z*g z) = mean E.design f*mean E.design g := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Bool)
  let jS := fun (i : S) => (⟨ρ.partner i, (hS i).mpr i.property⟩ : S)
  let jC := fun (i : {i : Fin n // i ∉ S}) =>
    (⟨ρ.partner i, fun h => i.property ((hS i).mp h)⟩ : {i : Fin n // i ∉ S})
  let q := fun x : S → Bool => if ∀ i, x i ≠ x (jS i) then (1:ℝ) else 0
  let r := fun y : {i : Fin n // i ∉ S} → Bool =>
    if ∀ i, y i ≠ y (jC i) then (1/(2:ℝ)^(n/2)) else 0
  have hm (x : S → Bool) (y : {i : Fin n // i ∉ S} → Bool) :
      E.design.mass (e.symm (x,y)) = q x*r y := by
    rw [hPair.2]
    have hv : (∀ i, e.symm (x,y) i ≠ e.symm (x,y) (ρ.partner i)) ↔
        (∀ i, x i ≠ x (jS i)) ∧ (∀ i, y i ≠ y (jC i)) := by
      constructor
      · intro h
        constructor
        · intro i
          simpa [e, Equiv.piEquivPiSubtypeProd, i.property, (hS i).mpr i.property, jS] using h i
        · intro i
          have hnot : ρ.partner i ∉ S := fun hi => i.property ((hS i).mp hi)
          simpa [e, Equiv.piEquivPiSubtypeProd, i.property, hnot, jC] using h i
      · rintro ⟨hx,hy⟩ i
        by_cases hi : i ∈ S
        · have hp := (hS i).mpr hi
          simpa [e, Equiv.piEquivPiSubtypeProd, hi, hp, jS] using hx ⟨i,hi⟩
        · have hp : ρ.partner i ∉ S := fun h => hi ((hS i).mp h)
          simpa [e, Equiv.piEquivPiSubtypeProd, hi, hp, jC] using hy ⟨i,hi⟩
    simp only [hv]
    dsimp [q,r]
    split_ifs <;> simp_all
  let F := fun x : S → Bool => f (e.symm (x, fun _ => false))
  let G := fun y : {i : Fin n // i ∉ S} → Bool => g (e.symm (fun _ => false,y))
  have hf' (z : Assignment n) : f z = F (e z).1 := by
    apply hf
    intro i hi
    simp [F,e,Equiv.piEquivPiSubtypeProd,hi]
  have hg' (z : Assignment n) : g z = G (e z).2 := by
    apply hg
    intro i hi
    change i ∉ S at hi
    simp [G,e,Equiv.piEquivPiSubtypeProd,hi]
  simpa only [← hf', ← hg'] using mean_product_of_partition_mass E.design e q r hm F G


theorem covariance_nonedge {n : ℕ} (E : Experiment n) (ρ : Pairing n) (hPair : Paired E ρ)
    (i j : Fin n) (hd : ¬ Dependent E i j)
    (he : ¬ ∃ ℓ, Interferes E ℓ i ∧ Interferes E (ρ.partner ℓ) j) (b : Bool) :
    cov E.design (armVariable E b 1 i) (armVariable E b 1 j) = 0 := by
  let S : Set (Fin n) := {ℓ | Interferes E ℓ i ∨ Interferes E (ρ.partner ℓ) i}
  have hS (ℓ : Fin n) : ρ.partner ℓ ∈ S ↔ ℓ ∈ S := by
    dsimp [S]
    rw [ρ.involution]
    tauto
  have hi : DependsOn (armVariable E b 1 i) S :=
    DependsOn.mono (fun ℓ hℓ => Or.inl hℓ) (BernoulliCompletion.arm_dependsOn E i b 1)
  have hj : DependsOn (armVariable E b 1 j) Sᶜ := by
    apply DependsOn.mono _ (BernoulliCompletion.arm_dependsOn E j b 1)
    intro ℓ hℓ hh
    change Interferes E ℓ j at hℓ
    rcases hh with h1 | h1
    · exact hd ⟨ℓ,h1,hℓ⟩
    · exact he ⟨ρ.partner ℓ,h1,by simpa only [ρ.involution] using hℓ⟩
  rw [BernoulliCompletion.covariance_product_formula,
    mean_product_of_closed_partition E ρ hPair S hS _ _ hi hj, sub_self]

theorem covariance_graph_cancellation {n : ℕ} (E : Experiment n) (ρ : Pairing n)
    (hPair : Paired E ρ) (i j : Fin n) (b : Bool) :
    (1-d E i j)*(1-e E ρ i j)*cov E.design (armVariable E b 1 i) (armVariable E b 1 j) = 0 := by
  by_cases hd : Dependent E i j
  · simp [d,hd]
  · by_cases he : ∃ ℓ, Interferes E ℓ i ∧ Interferes E (ρ.partner ℓ) j
    · simp [e,hd,he]
    · rw [covariance_nonedge E ρ hPair i j hd he b]
      simp

theorem arm_variance_bound {n : ℕ} (hn : 0 < n) (E : Experiment n) (ρ : Pairing n)
    (hPair : Paired E ρ) (k q s : ℝ) (hReg : Regular E k q s) (b : Bool) :
    var E.design (muHat E b) ≤ 4*k^2*(dAvg E+eAvg E ρ)/(n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hcov (i j : Fin n) :
      |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤ (d E i j+e E ρ i j)*k^2 := by
    have hh := (corrected_moment_covariance E k q hReg.1 hReg.2.1 hReg.2.2.2.2.1
      1 (by simpa using hReg.2.1) i j b).2.2.2.2.2.2
    by_cases hd : Dependent E i j
    · simpa [d,e,hd] using hh
    · by_cases he : ∃ ℓ, Interferes E ℓ i ∧ Interferes E (ρ.partner ℓ) j
      · simpa [d,e,hd,he] using hh
      · simp [d,e,hd,he,covariance_nonedge E ρ hPair i j hd he b]
  have hmu : muHat E b = fun z => (∑ i, (2:ℝ)*armVariable E b 1 i z)/(n:ℝ) := by
    funext z
    simp only [muHat,armVariable,pow_one,marginal_half E ρ hPair]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hmu,BernoulliCompletion.variance_div]
  have hv := (weighted_variance_absolute E.design (armVariable E b 1)
    (fun _ => (2:ℝ)) 2 (fun _ => ⟨by norm_num,le_rfl⟩)).2
  calc
    _ ≤ (2^2*(∑ i, ∑ j, |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)|))/(n:ℝ)^2 :=
      div_le_div_of_nonneg_right hv (sq_nonneg _)
    _ ≤ (2^2*(∑ i, ∑ j, (d E i j+e E ρ i j)*k^2))/(n:ℝ)^2 := by
      gcongr with i j
      exact hcov i j
    _ = _ := by
      simp only [dAvg,degree,eAvg,add_mul,Finset.sum_add_distrib,← Finset.sum_mul]
      field_simp
      ring

theorem supported_arm_counts {n : ℕ} (E : Experiment n) (ρ : Pairing n) (hPair : Paired E ρ)
    (z : Assignment n) (hz : 0 < E.design.mass z) (b : Bool) : nHat E b z = n := by
  have hopp := supported_opposite E ρ hPair z hz
  have hi (i : Fin n) : (if z i = b then (1:ℝ) else 0)+
      (if z (ρ.partner i) = b then (1:ℝ) else 0) = 1 := by
    have hh := hopp i
    cases b <;> cases hzi : z i <;> cases hzj : z (ρ.partner i) <;> simp_all
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [Finset.sum_add_distrib] at hs
  have hperm := ρ.partner.sum_comp (fun i => if z i = b then (1:ℝ) else 0)
  change (∑ i, if z (ρ.partner i) = b then (1:ℝ) else 0) = _ at hperm
  rw [hperm] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hs
  unfold nHat
  simp only [marginal_half E ρ hPair,div_eq_mul_inv,inv_div,inv_one,mul_one]
  rw [← Finset.sum_mul]
  nlinarith only [hs]

theorem supported_estimators_eq {n : ℕ} (hn : 0 < n) (E : Experiment n) (ρ : Pairing n)
    (hPair : Paired E ρ) (z : Assignment n) (hz : 0 < E.design.mass z) : ht E z = hajek E z := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hT := supported_arm_counts E ρ hPair z hz true
  have hC := supported_arm_counts E ρ hPair z hz false
  have ha : ArmsNonempty E z := ⟨by rw [hT]; exact hnR, by rw [hC]; exact hnR⟩
  rw [hajek,ite_eq_left ha,hT,hC]
  unfold ht
  field_simp

/-- Conditioning on either member of a fair binary partition changes its
mean by at most the unconditional absolute first moment. -/
theorem fair_conditioning_bound {n : ℕ} (E : Experiment n) (ρ : Pairing n) (hPair : Paired E ρ)
    (i : Fin n) (b : Bool) (f : Assignment n → ℝ) :
    |cmean E.design (fun z => z i = b) f-mean E.design f| =
      (1/2)*|cmean E.design (fun z => z i = b) f-cmean E.design (fun z => z i = !b) f| ∧
    |cmean E.design (fun z => z i = b) f-mean E.design f| ≤ mean E.design (fun z => |f z|) := by
  have hnum : mean E.design (fun z => if z i = b then f z else 0)+
      mean E.design (fun z => if z i = !b then f z else 0) = mean E.design f := by
    rw [← mean_add]
    congr 1
    funext z
    cases b <;> cases hzi : z i <;> simp [hzi]
  have hc (b : Bool) : cmean E.design (fun z => z i = b) f =
      2*mean E.design (fun z => if z i = b then f z else 0) := by
    have hi : (fun z => @ite ℝ (z i = b) (Classical.propDecidable _) (f z) 0) =
        (fun z => if z i = b then f z else 0) := by
      funext z
      by_cases hz : z i = b <;> simp [hz]
    unfold cmean
    rw [hi]
    change mean E.design (fun z => if z i = b then f z else 0)/marginal E i b = _
    rw [marginal_half E ρ hPair]
    ring
  have he : cmean E.design (fun z => z i = b) f-mean E.design f =
      (1/2)*(cmean E.design (fun z => z i = b) f-cmean E.design (fun z => z i = !b) f) := by
    rw [hc,hc]
    linarith only [hnum]
  refine ⟨by rw [he,abs_mul]; norm_num, ?_⟩
  have hs : cmean E.design (fun z => z i = b) f-mean E.design f =
      mean E.design (fun z => if z i = b then f z else -f z) := by
    rw [hc]
    have hf : (fun z => if z i = b then f z else -f z) =
        (fun z => 2*(if z i = b then f z else 0)-f z) := by
      funext z
      by_cases hz : z i = b <;> simp [hz] <;> ring
    rw [hf,mean_sub,mean_const_mul]
  rw [hs]
  have hh := BernoulliCompletion.mean_abs_le E.design (fun z => if z i = b then f z else -f z)
  simpa only [abs_ite,abs_neg,ite_self] using hh

theorem conditional_potential_eq_mean_of_nonpartner {n : ℕ} (E : Experiment n) (ρ : Pairing n)
    (hPair : Paired E ρ) (i : Fin n) (b : Bool) (hno : ¬Interferes E (ρ.partner i) i) :
    cmean E.design (fun z => z i = b) (potential E i b) = mean E.design (potential E i b) := by
  let S : Set (Fin n) := {i,ρ.partner i}
  have hS (ℓ : Fin n) : ρ.partner ℓ ∈ S ↔ ℓ ∈ S := by
    simp only [S,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · right
        have hh := congrArg ρ.partner h
        simpa only [ρ.involution] using hh
      · left
        exact ρ.partner.injective h
    · rintro (h | h)
      · subst ℓ; simp
      · rw [h,ρ.involution]; simp
  let f := fun z : Assignment n => if z i = b then (1:ℝ) else 0
  have hf : DependsOn f S := by
    intro z z' hagree
    have he := hagree i (by simp [S])
    simp only [f,he]
  have hg : DependsOn (potential E i b) Sᶜ := by
    intro z z' hagree
    apply BernoulliCompletion.outcome_dependsOn E i
    intro ℓ hℓ
    by_cases hli : ℓ = i
    · subst ℓ; simp
    · have hlp : ℓ ≠ ρ.partner i := by intro he; subst ℓ; exact hno hℓ
      have he := hagree ℓ (by simp [S,hli,hlp])
      simp only [Function.update_of_ne hli,he]
  have hmul := mean_product_of_closed_partition E ρ hPair S hS f (potential E i b) hf hg
  have hn : mean E.design (fun z => if z i = b then potential E i b z else 0) =
      mean E.design (fun z => f z*potential E i b z) := by
    congr 1
    funext z
    by_cases hz : z i = b <;> simp [f,hz]
  have hi : (fun z => @ite ℝ (z i = b) (Classical.propDecidable _) (potential E i b z) 0) =
      (fun z => if z i = b then potential E i b z else 0) := by
    funext z
    by_cases hz : z i = b <;> simp [hz]
  unfold cmean
  rw [hi,hn,hmul]
  have hfmean : mean E.design f = marginal E i b := by
    exact BernoulliCompletion.indicator_mean E b i
  rw [hfmean]
  change (marginal E i b)*mean E.design (potential E i b)/marginal E i b = _
  rw [marginal_half E ρ hPair]
  ring


theorem conditional_potential_bound {n : ℕ} (E : Experiment n) (ρ : Pairing n)
    (hPair : Paired E ρ) (k q s : ℝ) (hReg : Regular E k q s) (i : Fin n) (b : Bool) :
    |cmean E.design (fun z => z i = b) (potential E i b)-mean E.design (potential E i b)| ≤ k := by
  exact (fair_conditioning_bound E ρ hPair i b (potential E i b)).2.trans
    (BernoulliCompletion.mean_abs_of_moment E.design _ k s hReg.1 hReg.2.2.1
      (hReg.2.2.2.2.2 i b))

theorem bias_bound {n : ℕ} (hn : 0 < n) (E : Experiment n) (ρ : Pairing n)
    (hPair : Paired E ρ) (k q s : ℝ) (hReg : Regular E k q s) :
    |adse E-eate E| ≤ 2*k^2*rSum E ρ/(n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hk2 := BernoulliCompletion.regular_k_ge_two hn E k q s hReg
  have hI (i : Fin n) : 0 ≤ I E (ρ.partner i) i := by unfold I; split_ifs <;> norm_num
  have hunit (i : Fin n) (b : Bool) :
      |cmean E.design (fun z => z i = b) (potential E i b)-mean E.design (potential E i b)| ≤
        k*I E (ρ.partner i) i := by
    by_cases hi : Interferes E (ρ.partner i) i
    · simpa [I,hi] using conditional_potential_bound E ρ hPair k q s hReg i b
    · rw [conditional_potential_eq_mean_of_nonpartner E ρ hPair i b hi]
      simp [I,hi]
  have he : adse E-eate E = (∑ i,
      ((cmean E.design (fun z => z i = true) (potential E i true)-mean E.design (potential E i true))-
       (cmean E.design (fun z => z i = false) (potential E i false)-mean E.design (potential E i false))))/(n:ℝ) := by
    rw [eate_finite_identity]
    simp only [adse,← BernoulliCompletion.conditional_potential_eq_observed,
      Finset.sum_sub_distrib, sub_div]
    ring
  rw [he,abs_div,abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑ i, |(cmean E.design (fun z => z i = true) (potential E i true)-mean E.design (potential E i true))-
       (cmean E.design (fun z => z i = false) (potential E i false)-mean E.design (potential E i false))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2*k*I E (ρ.partner i) i := by
      apply Finset.sum_le_sum
      intro i _
      have hh := abs_sub_le
        (cmean E.design (fun z => z i = true) (potential E i true)-mean E.design (potential E i true)) 0
        (cmean E.design (fun z => z i = false) (potential E i false)-mean E.design (potential E i false))
      simp only [sub_zero,zero_sub,abs_neg] at hh
      nlinarith only [hh,hunit i true,hunit i false]
    _ = 2*k*rSum E ρ := by simp only [rSum,Finset.mul_sum,mul_assoc]
    _ ≤ (2*k^2*rSum E ρ/(n:ℝ))*(n:ℝ) := by
      have hr : 0 ≤ rSum E ρ := Finset.sum_nonneg (fun i _ => hI i)
      have hkk : k ≤ k^2 := by nlinarith only [hk2,sq_nonneg (k-1)]
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkk (by norm_num : (0:ℝ) ≤ 2)) hr
      simpa only [div_mul_cancel₀ _ hnR.ne'] using hh

/-- Weighted means ignore assignments of zero design mass. -/
theorem mean_congr_on_support {Ω : Type*} [Fintype Ω] (P : Law Ω) (X Y : Ω → ℝ)
    (h : ∀ z, 0 < P.mass z → X z = Y z) : mean P X = mean P Y := by
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : 0 < P.mass z
  · rw [h z hz]
  · have hm : P.mass z = 0 := le_antisymm (le_of_not_gt hz) (P.nonneg z)
    simp [hm]

 theorem eAvg_nonneg {n : ℕ} (E : Experiment n) (ρ : Pairing n) : 0 ≤ eAvg E ρ := by
  unfold eAvg
  apply div_nonneg _ (Nat.cast_nonneg n)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  unfold e
  split_ifs <;> norm_num

 theorem rSum_nonneg {n : ℕ} (E : Experiment n) (ρ : Pairing n) : 0 ≤ rSum E ρ := by
  unfold rSum
  apply Finset.sum_nonneg
  intro i _
  unfold I
  split_ifs <;> norm_num

 theorem ht_mse_bound {n : ℕ} (hn : 0 < n) (E : Experiment n) (ρ : Pairing n)
    (hPair : Paired E ρ) (k q s : ℝ) (hReg : Regular E k q s) :
    mean E.design (fun z => (ht E z-eate E)^2) ≤
      32*k^2*((dAvg E+eAvg E ρ)/(n:ℝ))+8*k^4*(rSum E ρ/(n:ℝ))^2 := by
  have hp (i : Fin n) : 0 < marginal E i true ∧ 0 < marginal E i false := by
    rw [marginal_half E ρ hPair,marginal_half E ρ hPair]
    constructor <;> norm_num
  have hm := ht_unbiased_ADSE E hp
  have hv : var E.design (ht E) ≤ 16*k^2*((dAvg E+eAvg E ρ)/(n:ℝ)) := by
    have hh := BernoulliCompletion.variance_sub_le E.design (muHat E true) (muHat E false)
    change var E.design (fun z => muHat E true z-muHat E false z) ≤ _
    calc
      _ ≤ 2*(var E.design (muHat E true)+var E.design (muHat E false)) := hh
      _ ≤ 2*(4*k^2*(dAvg E+eAvg E ρ)/(n:ℝ)+4*k^2*(dAvg E+eAvg E ρ)/(n:ℝ)) := by
        gcongr <;> apply arm_variance_bound hn E ρ hPair k q s hReg
      _ = _ := by ring
  have hb := bias_bound hn E ρ hPair k q s hReg
  have hB : 0 ≤ 2*k^2*rSum E ρ/(n:ℝ) := by positivity [rSum_nonneg E ρ]
  have hbs : (adse E-eate E)^2 ≤ 4*k^4*(rSum E ρ/(n:ℝ))^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) hB).mpr hb
    rw [sq_abs] at hh
    convert hh using 1 <;> ring
  have hpoint : mean E.design (fun z => (ht E z-eate E)^2) ≤
      2*var E.design (ht E)+2*(adse E-eate E)^2 := by
    rw [← BernoulliCompletion.centered_square_mean,← mean_const_mul,
      ← mean_const E.design (2*(adse E-eate E)^2),← mean_add]
    unfold mean
    apply Finset.sum_le_sum
    intro z _
    apply mul_le_mul_of_nonneg_left _ (E.design.nonneg z)
    change (ht E z-eate E)^2 ≤ 2*(ht E z-mean E.design (ht E))^2+2*(adse E-eate E)^2
    rw [hm]
    nlinarith only [sq_nonneg ((ht E z-adse E)-(adse E-eate E))]
  nlinarith only [hpoint,hv,hbs]

 def pairedRate (S : Study) (ρ : (t : ℕ) → Pairing (S.N t)) (t : ℕ) : ℝ :=
  bernoulliRate S t+Real.sqrt (eAvg (S.experiment t) (ρ t))/Real.sqrt (size S t)+
    rSum (S.experiment t) (ρ t)/size S t

 theorem paired_rate_pos (S : Study) (ρ : (t : ℕ) → Pairing (S.N t)) (t : ℕ) :
    0 < pairedRate S ρ t := by
  have hn : (0:ℝ) < size S t := by dsimp [size]; exact_mod_cast S.positive t
  have h1 := BernoulliCompletion.bernoulli_rate_pos S t
  have h2 : 0 ≤ Real.sqrt (eAvg (S.experiment t) (ρ t))/Real.sqrt (size S t) := by positivity
  have h3 : 0 ≤ rSum (S.experiment t) (ρ t)/size S t := div_nonneg (rSum_nonneg _ _) hn.le
  dsimp [pairedRate]
  linarith

 theorem paired_rate_square (S : Study) (ρ : (t : ℕ) → Pairing (S.N t)) (t : ℕ) :
    (dAvg (S.experiment t)+eAvg (S.experiment t) (ρ t))/size S t ≤ (pairedRate S ρ t)^2 ∧
    (rSum (S.experiment t) (ρ t)/size S t)^2 ≤ (pairedRate S ρ t)^2 := by
  have hn : (0:ℝ) < size S t := by dsimp [size]; exact_mod_cast S.positive t
  have h1 := (BernoulliCompletion.bernoulli_rate_pos S t).le
  have h2 : 0 ≤ Real.sqrt (eAvg (S.experiment t) (ρ t))/Real.sqrt (size S t) := by positivity
  have h3 : 0 ≤ rSum (S.experiment t) (ρ t)/size S t := div_nonneg (rSum_nonneg _ _) hn.le
  have he : (Real.sqrt (eAvg (S.experiment t) (ρ t))/Real.sqrt (size S t))^2 =
      eAvg (S.experiment t) (ρ t)/size S t := by
    rw [div_pow,Real.sq_sqrt (eAvg_nonneg _ _),Real.sq_sqrt hn.le]
  have hd := BernoulliCompletion.bernoulli_rate_square S t
  dsimp [pairedRate]
  rw [add_div,← hd,← he]
  constructor <;> nlinarith only [mul_nonneg h1 h2,mul_nonneg h1 h3,mul_nonneg h2 h3,sq_nonneg (bernoulliRate S t),sq_nonneg (Real.sqrt (eAvg (S.experiment t) (ρ t))/Real.sqrt (size S t)),sq_nonneg (rSum (S.experiment t) (ρ t)/size S t)]

 theorem paired_rate_zero (S : Study) (ρ : (t : ℕ) → Pairing (S.N t))
    (hRestricted : Restricted S)
    (hE : LittleO (fun t => eAvg (S.experiment t) (ρ t)) (size S))
    (hR : LittleO (fun t => rSum (S.experiment t) (ρ t)) (size S)) :
    Tendsto (pairedRate S ρ) atTop (nhds 0) := by
  have he : Tendsto (fun t => Real.sqrt (eAvg (S.experiment t) (ρ t))/Real.sqrt (size S t))
      atTop (nhds 0) := by
    have hh := hE.sqrt
    simpa only [Real.sqrt_div (eAvg_nonneg _ _),Real.sqrt_zero] using hh
  change Tendsto (fun t => bernoulliRate S t+Real.sqrt (eAvg (S.experiment t) (ρ t))/Real.sqrt (size S t)+
    rSum (S.experiment t) (ρ t)/size S t) atTop (nhds 0)
  simpa only [add_zero] using
    ((BernoulliCompletion.bernoulli_rate_zero S hRestricted).add he).add hR

 theorem paired_estimators_op (S : Study) (ρ : (t : ℕ) → Pairing (S.N t)) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hPair : ∀ t, Paired (S.experiment t) (ρ t)) :
    Op S (fun t z => ht (S.experiment t) z-eate (S.experiment t)) (pairedRate S ρ) ∧
    Op S (fun t z => hajek (S.experiment t) z-eate (S.experiment t)) (pairedRate S ρ) := by
  have hk := (hReg 0).1
  have hM (t : ℕ) : mean (S.experiment t).design (fun z => (ht (S.experiment t) z-eate (S.experiment t))^2) ≤
      (32*k^2+8*k^4)*(pairedRate S ρ t)^2 := by
    have hh := ht_mse_bound (S.positive t) (S.experiment t) (ρ t) (hPair t) k q s (hReg t)
    change _ ≤ 32*k^2* _+8*k^4* _ at hh
    calc
      _ ≤ 32*k^2*((dAvg (S.experiment t)+eAvg (S.experiment t) (ρ t))/size S t)+
          8*k^4*(rSum (S.experiment t) (ρ t)/size S t)^2 := hh
      _ ≤ 32*k^2*(pairedRate S ρ t)^2+8*k^4*(pairedRate S ρ t)^2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (paired_rate_square S ρ t).1 (by positivity))
          (mul_le_mul_of_nonneg_left (paired_rate_square S ρ t).2 (by positivity))
      _ = _ := by ring
  have hH (t : ℕ) : mean (S.experiment t).design (fun z => (hajek (S.experiment t) z-eate (S.experiment t))^2) ≤
      (32*k^2+8*k^4)*(pairedRate S ρ t)^2 := by
    rw [mean_congr_on_support (S.experiment t).design _
      (fun z => (ht (S.experiment t) z-eate (S.experiment t))^2)
      (fun z hz => by rw [supported_estimators_eq (S.positive t) _ (ρ t) (hPair t) z hz])]
    exact hM t
  exact ⟨BernoulliCompletion.op_of_second_moment S _ _ (32*k^2+8*k^4) (by positivity)
    (paired_rate_pos S ρ) hM,
    BernoulliCompletion.op_of_second_moment S _ _ (32*k^2+8*k^4) (by positivity)
    (paired_rate_pos S ρ) hH⟩


end
end AronowAudit.P009.PairedCompletion

namespace AronowAudit.P009
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

/-- T34, corrected justification of Lemma A17's unchanged constant,
Supplement A p. 17: paired treatment probability 1/2 gives each conditional
potential-mean difference at most k, and their sum at most 2k≤2k². -/
theorem corrected_paired_bias_bound {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (ρ : Pairing n) (hPair : Paired E ρ) (k q s : ℝ) (hReg : Regular E k q s) :
    (∀ i b, |cmean E.design (fun z => z i = b) (potential E i b) -
      mean E.design (potential E i b)| =
      (1/2)*|cmean E.design (fun z => z i = b) (potential E i b) -
        cmean E.design (fun z => z i = !b) (potential E i b)| ∧
      |cmean E.design (fun z => z i = b) (potential E i b) -
        mean E.design (potential E i b)| ≤ k) ∧
    2 ≤ k ∧ 2*k ≤ 2*k^2 ∧ |adse E-eate E| ≤ 2*k^2*rSum E ρ/(n:ℝ) := by
  have hk := BernoulliCompletion.regular_k_ge_two hn E k q s hReg
  refine ⟨fun i b => ⟨(PairedCompletion.fair_conditioning_bound E ρ hPair i b (potential E i b)).1,
    PairedCompletion.conditional_potential_bound E ρ hPair k q s hReg i b⟩, hk, ?_,
    PairedCompletion.bias_bound hn E ρ hPair k q s hReg⟩
  nlinarith only [hk,sq_nonneg (k-1)]

/-- T44 finite lemmas, Supplement A pp. 16–18: the corrected pair-bias
constant, covariance graph, arm variance bounds and exact HT/Hájek equality. -/
theorem paired_finite_lemmas {n : ℕ} (hn : 0 < n) (E : Experiment n) (ρ : Pairing n)
    (hPair : Paired E ρ) (k q s : ℝ) (hReg : Regular E k q s) :
    eAvg E ρ ≤ C2 E^2 ∧ |adse E-eate E| ≤ 2*k^2*rSum E ρ/(n:ℝ) ∧
    (∀ i b, marginal E i b = 1/2) ∧
    (∀ i j b, (1-d E i j)*(1-e E ρ i j)*cov E.design
      (armVariable E b 1 i) (armVariable E b 1 j) = 0) ∧
    (∀ b, var E.design (muHat E b) ≤ 4*k^2*(dAvg E+eAvg E ρ)/(n:ℝ)) ∧
    (∀ z, 0 < E.design.mass z → nHat E true z = n ∧ nHat E false z = n ∧
      ht E z = hajek E z) := by
  exact ⟨(corrected_pair_dependence hn E ρ).2.2,
    PairedCompletion.bias_bound hn E ρ hPair k q s hReg,
    PairedCompletion.marginal_half E ρ hPair,
    PairedCompletion.covariance_graph_cancellation E ρ hPair,
    PairedCompletion.arm_variance_bound hn E ρ hPair k q s hReg,
    fun z hz => ⟨PairedCompletion.supported_arm_counts E ρ hPair z hz true,
      PairedCompletion.supported_arm_counts E ρ hPair z hz false,
      PairedCompletion.supported_estimators_eq hn E ρ hPair z hz⟩⟩

/-- T44, Proposition 4 (p. 686): paired HT and Hájek consistency and all
three printed rate terms under Assumptions 1–4. Only even-size designs satisfy
Paired; the study's size parameter allows that regime without dummy odd designs. -/
theorem paired_consistency (S : Study) (ρ : (t : ℕ) → Pairing (S.N t)) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hPair : ∀ t, Paired (S.experiment t) (ρ t))
    (hRestricted : Restricted S)
    (hE : LittleO (fun t => eAvg (S.experiment t) (ρ t)) (size S))
    (hR : LittleO (fun t => rSum (S.experiment t) (ρ t)) (size S)) :
    EstimatorClaims S (fun t => eate (S.experiment t))
      (fun t => bernoulliRate S t + Real.sqrt (eAvg (S.experiment t) (ρ t))/Real.sqrt (size S t) +
        rSum (S.experiment t) (ρ t)/size S t) := by
  have hh := PairedCompletion.paired_estimators_op S ρ k q s hReg hPair
  have ha := PairedCompletion.paired_rate_zero S ρ hRestricted hE hR
  exact ⟨BernoulliCompletion.probability_of_op_zero S _ _ ha hh.1,
    BernoulliCompletion.probability_of_op_zero S _ _ ha hh.2,hh.1,hh.2⟩

end
end AronowAudit.P009
