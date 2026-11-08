import SAP.P061b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061b
open scoped BigOperators Classical

abbrev Household := Fin 2 × Fin 2

def ownAssignment (i : Fin 2) (z : Household) : ℝ :=
  if i = 0 then (z.1.val : ℝ) else (z.2.val : ℝ)

def housemateAssignment (i : Fin 2) (z : Household) : ℝ :=
  if i = 0 then (z.2.val : ℝ) else (z.1.val : ℝ)

noncomputable def oneTreated : AtomicDesign Household where
  p := fun z => if z.1 = z.2 then 0 else 1/2
  nonneg := fun z => by split_ifs <;> norm_num
  summable := Summable.of_finite
  total := by norm_num [tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]

noncomputable def bothOrNeither : AtomicDesign Household where
  p := fun z => if z.1 = z.2 then 1/2 else 0
  nonneg := fun z => by split_ifs <;> norm_num
  summable := Summable.of_finite
  total := by norm_num [tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]

noncomputable def independentHousehold : AtomicDesign Household where
  p := fun _ => (Fintype.card Household : ℝ)⁻¹
  nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  summable := Summable.of_finite
  total := by norm_num [tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]

noncomputable def attenuatedOutcome (i : Fin 2) (z : Household) : ℝ :=
  if z.1 = z.2 then 1/2 else ownAssignment i z

def amplifiedOutcome (_i : Fin 2) (z : Household) : ℝ :=
  if z.1 = 1 ∧ z.2 = 1 then 1 else 0

abbrev VersionHousehold := Fin 3 × Fin 3

def versionResponse (i : Fin 2) (z : VersionHousehold) : ℝ :=
  if i = 0 then (z.1.val : ℝ) else (z.2.val : ℝ)

def versionCategory (i : Fin 2) (z : VersionHousehold) : ℝ :=
  if (if i = 0 then z.1 else z.2) = 0 then 0 else 1

noncomputable def oneVersionTreated (v : Fin 3) (hv : v = 1 ∨ v = 2) :
    AtomicDesign VersionHousehold where
  p := fun z => if (z.1 = 0 ∧ z.2 = v) ∨ (z.1 = v ∧ z.2 = 0) then 1/2 else 0
  nonneg := fun z => by split_ifs <;> norm_num
  summable := Summable.of_finite
  total := by
    rcases hv with rfl | rfl <;>
      norm_num [tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_succ]

noncomputable def covarianceSum {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d e : ℝ) : ℝ :=
  (N : ℝ)⁻¹^2 * ∑ i, ∑ j,
    ((jointExposureProbability D g i j d e - exposureProbability D g i d *
      exposureProbability D g j e) / (exposureProbability D g i d *
      exposureProbability D g j e)) * exposureMean D g y i d * exposureMean D g y j e

noncomputable def indicatorVarianceSum {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d : ℝ) : ℝ :=
  (N : ℝ)⁻¹^2 * ∑ i, ∑ j,
    designCovariance D (exposureIndicator g i d) (exposureIndicator g j d) *
      (exposureMean D g y i d * exposureMean D g y j d) /
      (exposureProbability D g i d * exposureProbability D g j d)

noncomputable def htVarianceEstimate {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d : ℝ) (z : Ω) : ℝ :=
  (N : ℝ)⁻¹^2 * ∑ i, ∑ j,
    ((jointExposureProbability D g i j d d - exposureProbability D g i d *
      exposureProbability D g j d) / (exposureProbability D g i d *
      exposureProbability D g j d)) * y i z * y j z *
      (if g i z = d ∧ g j z = d then 1 else 0) / jointExposureProbability D g i j d d

noncomputable def conservativeVarianceEstimate {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y : Schedule Ω N) (d : ℝ) (z : Ω) : ℝ :=
  (N : ℝ)⁻¹^2 * ∑ i, ∑ j,
    if 0 < jointExposureProbability D g i j d d then
      ((jointExposureProbability D g i j d d - exposureProbability D g i d *
        exposureProbability D g j d) / (exposureProbability D g i d *
        exposureProbability D g j d)) * y i z * y j z *
        (if g i z = d ∧ g j z = d then 1 else 0) / jointExposureProbability D g i j d d
    else if jointExposureProbability D g i j d d = 0 then
      (if g i z = d then y i z^2 / 2 else 0) / exposureProbability D g i d +
      (if g j z = d then y j z^2 / 2 else 0) / exposureProbability D g j d
    else 0

noncomputable def adjustedMean {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g y F : Schedule Ω N) (d : ℝ) (z : Ω) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (if g i z = d then y i z - F i z else 0) / exposureProbability D g i d +
  (N : ℝ)⁻¹ * ∑ i, F i z

def PredictionCalibrated {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g F : Schedule Ω N) (d : ℝ) : Prop :=
  ∀ i, designMean D (fun z => (if g i z = d then F i z else 0) /
    exposureProbability D g i d) = designMean D (F i)

end SAP.P061b
