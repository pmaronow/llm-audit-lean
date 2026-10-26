import AronowAudit.P004.P004_FiniteGraphCompletion

namespace AronowAudit.P004.GraphCompletion
open scoped BigOperators
open MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem residual_depends {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i : Fin N) :
    DependsOn (residualContrast p R g i) {k | interferes R i k} := by
  intro x y hxy
  have he := residual_family_depends p R g ({i}:Finset (Fin N))
    (x:=x) (y:=y) (by simpa only [sources,Set.mem_setOf_eq,Finset.mem_singleton,exists_eq_left] using hxy)
  exact congrFun he ⟨i,by simp⟩

theorem residual_cov_zero {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i j : Fin N) (hij : ¬sharesSource R i j) :
    cov p (residualContrast p R g i) (residualContrast p R g j)=0 := by
  have hj : DependsOn (residualContrast p R g j) ({k | interferes R i k}ᶜ) :=
    (residual_depends p R g j).mono (by
      intro k hk hki
      exact hij ⟨k,hki,hk⟩)
  unfold cov
  rw [expect_mul_of_disjoint_depends p _ _ _ (residual_depends p R g i) hj,sub_self]

theorem variance_add_const {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) (c : ℝ) :
    variance p (fun z=>X z+c)=variance p X := by
  have he : (fun z=>(X z+c)*(X z+c))=(fun z=>X z*X z+c*X z+c*X z+c*c) := by
    funext z
    ring
  dsimp only [variance,cov]
  rw [he]
  simp only [expect_add,expect_mul,expect_const]
  ring

theorem augmented_variance_reduction {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) :
    variance p (augmented p R g)=variance p (fun z=>(∑ i,residualContrast p R g i z)/N) := by
  have he : augmented p R g=fun z=>(∑ i,residualContrast p R g i z)/N+(∑ i,(g i true-g i false))/N := by
    funext z
    rw [←add_div,←Finset.sum_add_distrib]
    unfold augmented residualContrast
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,variance_add_const]

theorem local_second_sum {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N))
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hself : ∀ i,i∈B i) :
    (∑ i,∑ j∈B i,expect p (fun z=>residualContrast p R g i z*residualContrast p R g j z))/(N:ℝ)^2 =
      secondMomentBound p R B g := by
  unfold secondMomentBound
  congr 1
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_erase_add _ _ (hself i)]
  rw [show expect p (fun z=>residualContrast p R g i z*residualContrast p R g i z)=
      marginal p (fun i z=>(R i z-g i true)^2) i true/p i+
      marginal p (fun i z=>(R i z-g i false)^2) i false/(1-p i) by
        simpa only [pow_two] using residual_square_moment p R g i (hp i)]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact residual_pair_moment p R g i j (Finset.ne_of_mem_erase hj).symm hp

theorem expect_finset_sum {N : ℕ} {ι : Type*} (p : Fin N → ℝ) (S : Finset ι)
    (F : ι → Assignment N → ℝ) :
    expect p (fun z=>∑ i∈S,F i z)=∑ i∈S,expect p (F i) := by
  unfold expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

end
end AronowAudit.P004.GraphCompletion

namespace AronowAudit.P004
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem augmented_variance {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ)
    (hN : 0 < N) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (hself : ∀ i, i ∈ B i) (houtside : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    variance p (augmented p R g) = secondMomentBound p R B g - homophilyQ p R B g / N := by
  rw [GraphCompletion.augmented_variance_reduction,variance_div,variance_sum]
  have hl : (∑ i,∑ j,cov p (residualContrast p R g i) (residualContrast p R g j))=
      ∑ i,∑ j∈B i,cov p (residualContrast p R g i) (residualContrast p R g j) := by
    apply Finset.sum_congr rfl
    intro i _
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (fun j _ hj=>GraphCompletion.residual_cov_zero p R g i j (houtside i j hj))
  rw [hl]
  simp only [cov,Finset.sum_sub_distrib,residualContrast_mean p R g _ hp,sub_div]
  rw [GraphCompletion.local_second_sum p R g B hp hself]
  simp only [homophilyQ,div_div,pow_two]

theorem hajek_homophily_identity {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (hN : 0 < N) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (hself : ∀ i, i ∈ B i)
    (houtside : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    secondMomentBound p R B (fun _ a => barMu p R a) - variance p (linearHajek p R) =
      homophilyQ p R B (fun _ a => barMu p R a) / N ∧
    (variance p (linearHajek p R) ≤ secondMomentBound p R B (fun _ a => barMu p R a) ↔
      0 ≤ homophilyQ p R B (fun _ a => barMu p R a)) := by
  have hv := augmented_variance p R B (fun _ a=>barMu p R a) hN hp hself houtside
  change variance p (linearHajek p R)=_ at hv
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  refine ⟨by linarith,?_⟩
  constructor
  · intro h
    have hq : 0≤homophilyQ p R B (fun _ a=>barMu p R a)/N := by linarith
    simpa only [zero_mul] using (le_div_iff₀ hn).mp hq
  · intro h
    have hq := div_nonneg h hn.le
    linarith

theorem hajek_variance_identity {N : ℕ} (p : ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (hN : 0 < N) (hp : 0 < p ∧ p < 1)
    (hself : ∀ i, i ∈ B i) (houtside : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    variance (fun _ => p) (linearHajek (fun _ => p) R) =
      secondMomentBound (fun _ => p) R B (fun _ a => barMu (fun _ => p) R a) -
      homophilyQ (fun _ => p) R B (fun _ a => barMu (fun _ => p) R a)/N := by
  exact augmented_variance (fun _=>p) R B (fun _ a=>barMu (fun _=>p) R a) hN (fun _=>hp) hself houtside

theorem hajek_sah_bound {N : ℕ} (p : ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (hN : 0 < N) (hp : 0 < p ∧ p < 1)
    (hself : ∀ i, i ∈ B i) (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (houtside : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    variance (fun _ => p) (linearHajek (fun _ => p) R) ≤
      sahLimit (fun _ => p) R B (fun _ a => barMu (fun _ => p) R a) := by
  unfold linearHajek
  rw [GraphCompletion.augmented_variance_reduction]
  exact (raw_sah_bound (fun _=>p) R B _ hN (fun _=>hp) hself hsymm
    (fun i j hj=>GraphCompletion.residual_cov_zero _ _ _ i j (houtside i j hj))).1

theorem augmented_homophily_bound {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ)
    (hN : 0 < N) (hp : ∀ i, 0 < p i ∧ p i < 1) (hself : ∀ i, i ∈ B i)
    (houtside : ∀ i j, j ∉ B i → ¬ sharesSource R i j)
    (hh : 0 ≤ homophilyQ p R B g) :
    variance p (augmented p R g) ≤ secondMomentBound p R B g := by
  rw [augmented_variance p R B g hN hp hself houtside]
  exact sub_le_self _ (div_nonneg hh (Nat.cast_nonneg _))

theorem ht_standardized_summands {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (hN : 0 < N) (hp : ∀ i, 0 < p i ∧ p i < 1) (hv : 0 < variance p (ht p R)) :
    let U := fun i z => (residualContrast p R (fun _ _ => 0) i z-nodeEffect p R i) /
      (N*Real.sqrt (variance p (ht p R)))
    (∀ z, (∑ i, U i z) = (ht p R z-ame p R)/Real.sqrt (variance p (ht p R))) ∧
    (∀ i, expect p (U i) = 0) ∧ variance p (fun z => ∑ i, U i z) = 1 := by
  dsimp only
  have hsum : ∀ z, (∑ i,(residualContrast p R (fun _ _=>0) i z-nodeEffect p R i)/
      ((N:ℝ)*Real.sqrt (variance p (ht p R))))=(ht p R z-ame p R)/Real.sqrt (variance p (ht p R)) := by
    intro z
    rw [←Finset.sum_div,Finset.sum_sub_distrib]
    unfold ht ame residualContrast
    simp only [sub_zero,div_eq_mul_inv,mul_inv_rev]
    ring
  refine ⟨hsum,?_,?_⟩
  · intro i
    rw [expect_div,expect_sub,residualContrast_mean p R (fun _ _=>0) i hp,expect_const]
    simp only [residualEffect,sub_zero,sub_self,zero_div]
  · simp_rw [hsum]
    rw [variance_div]
    rw [show variance p (fun z=>ht p R z-ame p R)=variance p (ht p R) from
      by simpa only [sub_eq_add_neg] using GraphCompletion.variance_add_const p (ht p R) (-ame p R)]
    rw [Real.sq_sqrt hv.le,div_self hv.ne']

theorem corrected_ipw_oracle {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (B : Fin N → Finset (Fin N))
    (hN : 0 < N) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (hself : ∀ i, i ∈ B i) (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (houtside : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    expect p (oracleHAC p R B (scoreFits p R O)) =
      variance p (augmented p R (scoreFits p R O)) + homophilyQ p R B (printedFits p R O) / N ∧
    variance p (augmented p R (scoreFits p R O)) ≤ expect p (rawSAH p R B (scoreFits p R O)) := by
  have hc : homophilyQ p R B (scoreFits p R O)=homophilyQ p R B (printedFits p R O) := by
    have he : ∀ i,residualEffect p R (scoreFits p R O) i=residualEffect p R (printedFits p R O) i := by
      intro i
      unfold residualEffect scoreFits
      dsimp only
      simp only [Bool.false_eq_true,ite_false,ite_true]
      ring
    unfold homophilyQ
    simp_rw [he]
  have heH : expect p (oracleHAC p R B (scoreFits p R O))=secondMomentBound p R B (scoreFits p R O) := by
    unfold oracleHAC
    rw [expect_div,expect_sum]
    simp_rw [GraphCompletion.expect_finset_sum]
    exact GraphCompletion.local_second_sum p R (scoreFits p R O) B hp hself
  constructor
  · rw [heH]
    have hv := augmented_variance p R B (scoreFits p R O) hN hp hself houtside
    rw [hc] at hv
    linarith
  · rw [GraphCompletion.augmented_variance_reduction]
    have hh := raw_sah_bound p R B (scoreFits p R O) hN hp hself hsymm
      (fun i j hj=>GraphCompletion.residual_cov_zero p R (scoreFits p R O) i j (houtside i j hj))
    exact hh.1.trans_eq hh.2


end
end AronowAudit.P004
