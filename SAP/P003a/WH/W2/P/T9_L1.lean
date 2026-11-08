import SAP.P003a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W2.P.T9_L1

open scoped BigOperators
open SAP.P003a.WH.W2
attribute [local instance 0] Classical.propDecidable

def threeAtoms : List ℤ := [-1, 0, 1]

noncomputable def threeAtomWeight : ℤ → ℝ := fun _ => (1 : ℝ) / 3

theorem three_mass_identification :
    (fun i : ℤ =>
      (threeAtoms.map (fun q => if q = i then threeAtomWeight q else 0)).sum / 1) =
      w2ThreeMass := by
  funext i
  by_cases hneg : i = -1
  · subst i
    norm_num [threeAtoms, threeAtomWeight, w2ThreeMass]
  by_cases hzero : i = 0
  · subst i
    norm_num [threeAtoms, threeAtomWeight, w2ThreeMass]
  by_cases hpos : i = 1
  · subst i
    norm_num [threeAtoms, threeAtomWeight, w2ThreeMass]
  have h1 : (-1 : ℤ) ≠ i := by omega
  have h0 : (0 : ℤ) ≠ i := by omega
  have h2 : (1 : ℤ) ≠ i := by omega
  simp [threeAtoms, threeAtomWeight, w2ThreeMass, hneg, hzero, hpos, h1, h0, h2]

theorem three_mass : IsMass w2ThreeMass := by
  have hfinite : IsMass (fun i : ℤ =>
      (threeAtoms.map (fun q => if q = i then threeAtomWeight q else 0)).sum / 1) :=
    AronowAudit.P003.Wave1.discordant_estimator_sd_finite_mass
      threeAtoms id threeAtomWeight 1 (by norm_num)
      (by intro q; norm_num [threeAtomWeight])
      (by norm_num [threeAtoms, threeAtomWeight])
  rw [← three_mass_identification]
  exact hfinite

theorem three_mass_symmetric : ∀ i : ℤ, w2ThreeMass (0-i) = w2ThreeMass i := by
  intro i
  by_cases hneg : i = -1
  · subst i
    norm_num [w2ThreeMass]
  by_cases hzero : i = 0
  · subst i
    norm_num [w2ThreeMass]
  by_cases hpos : i = 1
  · subst i
    norm_num [w2ThreeMass]
  have hn : -i ≠ -1 := by omega
  have hz : -i ≠ 0 := by omega
  have hp : -i ≠ 1 := by omega
  simp [w2ThreeMass, hneg, hzero, hpos, hn, hz, hp]

theorem three_mass_decreasing :
    ∀ i j : ℤ, 0 ≤ 2*i → i ≤ j → w2ThreeMass j ≤ w2ThreeMass i := by
  intro i j hi hij
  by_cases hzero : i = 0
  · subst i
    unfold w2ThreeMass
    split_ifs <;> norm_num <;> omega
  by_cases hone : i = 1
  · subst i
    unfold w2ThreeMass
    split_ifs <;> norm_num <;> omega
  have hi2 : 2 ≤ i := by omega
  have hj2 : 2 ≤ j := by omega
  unfold w2ThreeMass
  split_ifs <;> norm_num <;> omega

theorem three_shape : SDShape w2ThreeMass 0 := by
  exact ⟨three_mass_symmetric, three_mass_decreasing⟩

end SAP.P003a.WH.W2.P.T9_L1

theorem SAP.P003a.WH.W2.T9_L1_proof : SAP.P003a.WH.W2.T9_L1 := by
  constructor
  · have hm : IsMass w2ThreeMass := SAP.P003a.WH.W2.P.T9_L1.three_mass
    have hmean :=
      AronowAudit.P003.Wave1.discordant_estimator_sd_mean_of_symmetry
        w2ThreeMass hm 0 SAP.P003a.WH.W2.P.T9_L1.three_mass_symmetric
    exact ⟨hm, 0, by simpa using hmean, SAP.P003a.WH.W2.P.T9_L1.three_shape⟩
  · have hm : IsMass w2ThreeMass := SAP.P003a.WH.W2.P.T9_L1.three_mass
    simpa using
      (AronowAudit.P003.Wave1.discordant_estimator_sd_mean_of_symmetry
        w2ThreeMass hm 0 SAP.P003a.WH.W2.P.T9_L1.three_mass_symmetric)
