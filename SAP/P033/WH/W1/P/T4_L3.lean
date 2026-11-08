import SAP.P033.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P033.WH.W1.P.T4_L3

open SAP.P033.WH.W1
open scoped BigOperators

lemma active_distance_scale (n : ℕ) (hg : wholePhysicalGeometry n) (j : Fin n) :
    wholePhysicalDistance n (wholeActiveIndex n j) =
      wholeBandwidth n * shrinkingDistance n j := by
  rcases hg with ⟨hpos, hdist, _, _, _, _, _⟩
  have h := hdist (wholeActiveIndex n j)
  have hv : (((wholeActiveIndex n j : Fin (n*(n+1))) : ℝ) + 1) /
      ((n : ℝ) + 1) = shrinkingDistance n j := by
    simpa [wholeActiveIndex, shrinkingDistance] using h
  apply (div_eq_iff (ne_of_gt hpos)).mp at h
  rw [hv] at h
  simpa [mul_comm] using h

lemma physical_gram_scale (n p : ℕ) (hg : wholePhysicalGeometry n)
    (r s : Fin (p+1)) :
    wholeGridGram
        (fun ji : Fin (n*(n+1)) × Fin 5 => wholePhysicalDistance n ji.1)
        (fun ji => wholePhysicalKernel n ji.1) p r s =
      5 * wholeBandwidth n ^ (r.val+s.val) *
        wholeGridGram (shrinkingDistance n) (shrinkingKernel n) p r s := by
  rcases hg with ⟨hpos, hdist, hposK, hcard, hactiveK, hred, hpad⟩
  let k := r.val + s.val
  have hs : ∀ j : Fin n,
      wholePhysicalDistance n (wholeActiveIndex n j) =
        wholeBandwidth n * shrinkingDistance n j :=
    active_distance_scale n ⟨hpos, hdist, hposK, hcard, hactiveK, hred, hpad⟩
  unfold wholeGridGram
  rw [Fintype.sum_prod_type]
  calc
    (∑ j : Fin (n*(n+1)), ∑ i : Fin 5,
        wholePhysicalKernel n j * wholePhysicalDistance n j ^ k) =
      5 * ∑ j : Fin (n*(n+1)),
        wholePhysicalKernel n j * wholePhysicalDistance n j ^ k := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          rw [← Finset.mul_sum]
    _ = 5 * ∑ j : Fin n,
        shrinkingKernel n j *
          wholePhysicalDistance n (wholeActiveIndex n j) ^ k := by
          rw [hred]
    _ = 5 * (wholeBandwidth n ^ k *
          ∑ j : Fin n, shrinkingKernel n j * shrinkingDistance n j ^ k) := by
          congr 1
          calc
            (∑ j : Fin n, shrinkingKernel n j *
                wholePhysicalDistance n (wholeActiveIndex n j) ^ k) =
              ∑ j : Fin n, wholeBandwidth n ^ k *
                (shrinkingKernel n j * shrinkingDistance n j ^ k) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [hs j, mul_pow]
                  ring
            _ = wholeBandwidth n ^ k *
                ∑ j : Fin n, shrinkingKernel n j * shrinkingDistance n j ^ k :=
                  by rw [← Finset.mul_sum]
    _ = 5 * wholeBandwidth n ^ k *
          wholeGridGram (shrinkingDistance n) (shrinkingKernel n) p r s := by
          simp [wholeGridGram, k]
          ring

lemma physical_rhs_scale (n p : ℕ) (hg : wholePhysicalGeometry n)
    (y : Fin (n*(n+1)) → Fin 5 → ℝ) (r : Fin (p+1)) :
    (∑ ji : Fin (n*(n+1)) × Fin 5,
        (fun ji => wholePhysicalKernel n ji.1) ji *
          (fun ji => wholePhysicalDistance n ji.1) ji ^ r.val *
            (fun ji => y ji.1 ji.2) ji) =
      5 * wholeBandwidth n ^ r.val *
        (∑ j : Fin n, shrinkingKernel n j * shrinkingDistance n j ^ r.val *
          wholeActiveMean n y j) := by
  rcases hg with ⟨hpos, hdist, hposK, hcard, hactiveK, hred, hpad⟩
  have hs : ∀ j : Fin n,
      wholePhysicalDistance n (wholeActiveIndex n j) =
        wholeBandwidth n * shrinkingDistance n j :=
    active_distance_scale n ⟨hpos, hdist, hposK, hcard, hactiveK, hred, hpad⟩
  let F : Fin (n*(n+1)) → ℝ := fun j =>
    wholePhysicalDistance n j ^ r.val * wholeClusterMean n y j
  calc
    (∑ ji : Fin (n*(n+1)) × Fin 5,
        wholePhysicalKernel n ji.1 * wholePhysicalDistance n ji.1 ^ r.val *
          y ji.1 ji.2) =
      ∑ j : Fin (n*(n+1)),
        wholePhysicalKernel n j * wholePhysicalDistance n j ^ r.val *
          (∑ i : Fin 5, y j i) := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro j hj
          calc
            (∑ i : Fin 5,
                wholePhysicalKernel n j * wholePhysicalDistance n j ^ r.val * y j i) =
              ∑ i : Fin 5,
                (wholePhysicalKernel n j * wholePhysicalDistance n j ^ r.val) * y j i := by
                  simp [mul_assoc]
            _ = (wholePhysicalKernel n j * wholePhysicalDistance n j ^ r.val) *
                ∑ i : Fin 5, y j i := by rw [← Finset.mul_sum]
    _ = 5 * ∑ j : Fin (n*(n+1)),
        wholePhysicalKernel n j * F j := by
          dsimp [F]
          apply congrArg (fun z : ℝ => z) ?_
          calc
            (∑ j : Fin (n*(n+1)),
                wholePhysicalKernel n j * wholePhysicalDistance n j ^ r.val *
                  (∑ i : Fin 5, y j i)) =
              ∑ j : Fin (n*(n+1)),
                5 * (wholePhysicalKernel n j *
                  (wholePhysicalDistance n j ^ r.val * wholeClusterMean n y j)) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    simp [wholeClusterMean]
                    ring
            _ = 5 * ∑ j : Fin (n*(n+1)),
                wholePhysicalKernel n j *
                  (wholePhysicalDistance n j ^ r.val * wholeClusterMean n y j) := by
                    rw [Finset.mul_sum]
    _ = 5 * ∑ j : Fin n,
        shrinkingKernel n j * F (wholeActiveIndex n j) := by
          rw [hred]
    _ = 5 * wholeBandwidth n ^ r.val *
        (∑ j : Fin n, shrinkingKernel n j * shrinkingDistance n j ^ r.val *
          wholeActiveMean n y j) := by
          calc
            5 * (∑ j : Fin n, shrinkingKernel n j *
                F (wholeActiveIndex n j)) =
              5 * ∑ j : Fin n, wholeBandwidth n ^ r.val *
                (shrinkingKernel n j * shrinkingDistance n j ^ r.val *
                  wholeActiveMean n y j) := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro j hj
                    simp [F, wholeActiveMean, hs j, hactiveK, mul_pow,
                      wholeClusterMean]
                    ring
            _ = 5 * wholeBandwidth n ^ r.val *
                ∑ j : Fin n, shrinkingKernel n j * shrinkingDistance n j ^ r.val *
                  wholeActiveMean n y j := by
                    calc
                      5 * (∑ j : Fin n, wholeBandwidth n ^ r.val *
                          (shrinkingKernel n j * shrinkingDistance n j ^ r.val *
                            wholeActiveMean n y j)) =
                        ∑ j : Fin n, 5 * (wholeBandwidth n ^ r.val *
                          (shrinkingKernel n j * shrinkingDistance n j ^ r.val *
                            wholeActiveMean n y j)) := by rw [Finset.mul_sum]
                      _ = ∑ j : Fin n, (5 * wholeBandwidth n ^ r.val) *
                          (shrinkingKernel n j * shrinkingDistance n j ^ r.val *
                            wholeActiveMean n y j) := by
                              apply Finset.sum_congr rfl
                              intro j hj
                              ring
                      _ = (5 * wholeBandwidth n ^ r.val) *
                          ∑ j : Fin n, shrinkingKernel n j * shrinkingDistance n j ^ r.val *
                            wholeActiveMean n y j := by rw [Finset.mul_sum]

lemma whole_grid_fit_rescale (n p : ℕ) (hp : p = 1 ∨ p = 2)
    (hg : wholePhysicalGeometry n) (hrank : wholePhysicalRank n)
    (y : Fin (n*(n+1)) → Fin 5 → ℝ) :
    ∀ r : Fin (p+1),
      wholeBandwidth n ^ r.val * wholePhysicalFit n p y r =
        wholeNormalizedFit n p (wholeActiveMean n y) r := by
  intro r
  let G := wholeGridGram (shrinkingDistance n) (shrinkingKernel n) p
  let A := wholeGridGram
      (fun ji : Fin (n*(n+1)) × Fin 5 => wholePhysicalDistance n ji.1)
      (fun ji => wholePhysicalKernel n ji.1) p
  let b : Fin (p+1) → ℝ := fun q =>
    ∑ j : Fin n, shrinkingKernel n j * shrinkingDistance n j ^ q.val *
      wholeActiveMean n y j
  let c : Fin (p+1) → ℝ := fun q =>
    wholeNormalizedFit n p (wholeActiveMean n y) q / wholeBandwidth n ^ q.val
  have hunitG : IsUnit G := by
    dsimp [G]
    exact (hrank p hp).1
  have hunitA : IsUnit A := by
    dsimp [A]
    exact (hrank p hp).2
  have hGsol : G.mulVec (wholeNormalizedFit n p (wholeActiveMean n y)) = b := by
    change G.mulVec (G⁻¹.mulVec b) = b
    have hd := Matrix.mul_nonsing_inv
      G
      ((Matrix.isUnit_iff_isUnit_det _).mp hunitG)
    rw [Matrix.mulVec_mulVec, hd, Matrix.one_mulVec]
  have hAsol : A.mulVec (wholePhysicalFit n p y) =
      (fun q => ∑ ji : Fin (n*(n+1)) × Fin 5,
        wholePhysicalKernel n ji.1 * wholePhysicalDistance n ji.1 ^ q.val *
          y ji.1 ji.2) := by
    change A.mulVec (A⁻¹.mulVec (fun q => ∑ ji : Fin (n*(n+1)) × Fin 5,
      wholePhysicalKernel n ji.1 * wholePhysicalDistance n ji.1 ^ q.val *
        y ji.1 ji.2)) = _
    have hd := Matrix.mul_nonsing_inv
      A
      ((Matrix.isUnit_iff_isUnit_det _).mp hunitA)
    rw [Matrix.mulVec_mulVec, hd, Matrix.one_mulVec]
  have hcand : A.mulVec c =
      (fun q => ∑ ji : Fin (n*(n+1)) × Fin 5,
        wholePhysicalKernel n ji.1 * wholePhysicalDistance n ji.1 ^ q.val *
          y ji.1 ji.2) := by
    funext q
    have hgram (s : Fin (p+1)) : A q s =
        5 * wholeBandwidth n ^ (q.val+s.val) * G q s := by
      dsimp [A, G]
      exact physical_gram_scale n p hg q s
    have hrhs := physical_rhs_scale n p hg y q
    have hh : wholeBandwidth n ≠ 0 := ne_of_gt (hg.1)
    change A.mulVec c q = _
    rw [Matrix.mulVec_apply]
    simp only [dotProduct]
    calc
      (∑ s : Fin (p+1), A q s * c s) =
          ∑ s : Fin (p+1),
            (5 * wholeBandwidth n ^ q.val) * (G q s *
              wholeNormalizedFit n p (wholeActiveMean n y) s) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [hgram s]
          dsimp [c]
          rw [pow_add]
          field_simp [hh]
      _ = (5 * wholeBandwidth n ^ q.val) *
          (G.mulVec (wholeNormalizedFit n p (wholeActiveMean n y)) q) := by
          rw [← Finset.mul_sum]
          change (5 * wholeBandwidth n ^ q.val) *
            (G.mulVec (wholeNormalizedFit n p (wholeActiveMean n y)) q) = _
          rfl
      _ = 5 * wholeBandwidth n ^ q.val * b q := by rw [hGsol]
      _ = _ := by rw [hrhs]
  have hfit_eq : wholePhysicalFit n p y = c := by
    apply (Matrix.mulVec_injective_iff_isUnit).2 hunitA
    rw [hAsol, hcand]
  have hpow : wholeBandwidth n ^ r.val ≠ 0 := pow_ne_zero _ (ne_of_gt hg.1)
  have hres := congrFun hfit_eq r
  dsimp [c] at hres
  calc
    wholeBandwidth n ^ r.val * wholePhysicalFit n p y r =
        wholeBandwidth n ^ r.val *
          (wholeNormalizedFit n p (wholeActiveMean n y) r /
            wholeBandwidth n ^ r.val) := by rw [hres]
    _ = wholeNormalizedFit n p (wholeActiveMean n y) r :=
      mul_div_cancel₀ _ hpow

end SAP.P033.WH.W1.P.T4_L3

theorem SAP.P033.WH.W1.T4_L3_proof : SAP.P033.WH.W1.T4_L3 := by
  intro n hn hg hrank
  intro p hp y r
  exact SAP.P033.WH.W1.P.T4_L3.whole_grid_fit_rescale n p hp hg hrank y r
