import SAP.P004c.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004c.Bridge
open SAP.P004c MeasureTheory Filter
open scoped BigOperators Classical
noncomputable section

theorem homophily_correspondence {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) :
    homophilyQ p R B (fun _ a => barMu p R a) = effectHomophily p R B := by
  have hbar : barMu p R true-barMu p R false = ame p R :=
    AronowAudit.P004.barMu_difference p R
  simp only [homophilyQ, residualEffect, hbar, effectHomophily, Finset.mul_sum]

/-- Distribute the existing homophily correction into diagonal and pair terms.
This is finite-sum algebra, not a new variance argument. -/
theorem expansion_correspondence {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ)
    (hself : ∀ i, i ∈ B i) :
    secondMomentBound p R B g - homophilyQ p R B g/N = varianceExpansion p R B g := by
  have hpair (i j : Fin N) :
      (∑ a : Bool, ∑ b : Bool, armSign a * armSign b *
        ((marginal p R i a - g i a)*(marginal p R j b - g j b))) =
        residualEffect p R g i * residualEffect p R g j := by
    simp only [Fintype.sum_bool, armSign, Bool.false_eq_true, ite_false, ite_true,
      residualEffect, nodeEffect]
    ring
  have hcovpair (i j : Fin N) :
      (∑ a : Bool, ∑ b : Bool, armSign a * armSign b *
        (pairMarginal p (fun z => (R i z-g i a)*(R j z-g j b)) i j a b -
          (marginal p R i a-g i a)*(marginal p R j b-g j b))) =
        (∑ a : Bool, ∑ b : Bool, armSign a * armSign b *
          pairMarginal p (fun z => (R i z-g i a)*(R j z-g j b)) i j a b) -
          residualEffect p R g i * residualEffect p R g j := by
    rw [← hpair]
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hsplit : (∑ i, ∑ j ∈ B i, residualEffect p R g i * residualEffect p R g j) =
      (∑ i, (residualEffect p R g i)^2) +
      ∑ i, ∑ j ∈ (B i).erase i, residualEffect p R g i * residualEffect p R g j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_erase_add _ _ (hself i)]
    ring
  unfold varianceExpansion secondMomentBound homophilyQ
  simp_rw [hcovpair]
  simp only [Finset.sum_sub_distrib]
  rw [hsplit, div_div]
  ring

theorem ht_upper_correspondence {N : ℕ} (p : ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) :
    htVarianceUpper p R B = varianceExpansion (fun _ => p) R B (fun _ _ => 0) +
      (∑ i, (nodeEffect (fun _ => p) R i)^2)/(N : ℝ)^2 := by
  unfold htVarianceUpper varianceExpansion residualEffect
  simp only [sub_zero, Finset.sum_sub_distrib]
  ring

theorem ht_expansion {N : ℕ} (p : ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (hN : 0 < N) (hp : 0 < p ∧ p < 1)
    (hself : ∀ i, i ∈ B i) (houtside : ∀ i j, j ∉ B i → ¬ sharesSource R i j) :
    variance (fun _ => p) (ht (fun _ => p) R) =
      varianceExpansion (fun _ => p) R B (fun _ _ => 0) := by
  have h : variance (fun _ => p) (augmented (fun _ => p) R (fun _ _ => 0)) =
    secondMomentBound (fun _ => p) R B (fun _ _ => 0) -
      homophilyQ (fun _ => p) R B (fun _ _ => 0)/N :=
    AronowAudit.P004.augmented_variance (fun _ => p) R B (fun _ _ => 0)
      hN (fun _ => hp) hself houtside
  have hz : augmented (fun _ => p) R (fun _ _ => 0) = ht (fun _ => p) R := by
    funext z
    simp only [augmented, ht, sub_zero, zero_add]
  rw [hz, expansion_correspondence _ _ _ _ hself] at h
  exact h

/-- The explicit negative-eigenvalue expansion is scalar distributive algebra. -/
theorem spectral_difference {N : ℕ} (values : Fin N → ℝ)
    (vectors : Matrix (Fin N) (Fin N) ℝ) :
    spectralKernel values vectors true - spectralKernel values vectors false =
      spectralKernel (fun k => -values k) vectors true := by
  ext i j
  change (∑ k, max (values k) 0*vectors i k*vectors j k) -
    (∑ k, values k*vectors i k*vectors j k) =
      ∑ k, max (-values k) 0*vectors i k*vectors j k
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hmax : max (values k) 0 - values k = max (-values k) 0 := by
    by_cases h : 0 ≤ values k
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      ring
    · have h' := le_of_not_ge h
      rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
      ring
  calc
    _ = (max (values k) 0-values k)*vectors i k*vectors j k := by ring
    _ = _ := by rw [hmax]

end
end SAP.P004c.Bridge
