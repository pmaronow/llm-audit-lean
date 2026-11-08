import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P037a

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

structure Design (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ w, 0 ≤ weight w
  total : ∑ w, weight w = 1

noncomputable def mean {Ω : Type*} [Fintype Ω]
    (d : Design Ω) (X : Ω → ℝ) : ℝ := ∑ w, d.weight w * X w

noncomputable def variance {Ω : Type*} [Fintype Ω]
    (d : Design Ω) (X : Ω → ℝ) : ℝ :=
  mean d (fun w => (X w)^2) - (mean d X)^2

noncomputable def covariance {Ω : Type*} [Fintype Ω]
    (d : Design Ω) (X Y : Ω → ℝ) : ℝ :=
  mean d (fun w => X w*Y w) - mean d X * mean d Y

def treatmentPair (w : Fin 6) : Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)] w

noncomputable def treatment (w : Fin 6) (i : Fin 4) : ℝ :=
  if i = (treatmentPair w).1 ∨ i = (treatmentPair w).2 then 1 else 0

noncomputable def blockDesign : Design (Fin 6) where
  weight := fun _ => 1/6
  nonneg := fun _ => by norm_num
  total := by norm_num [Fin.sum_univ_succ]

noncomputable def doubleBlockDesign : Design (Fin 6 × Fin 6) where
  weight := fun _ => 1/36
  nonneg := fun _ => by norm_num
  total := by norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ]

structure ExposureData where
  school : ℕ
  seed : ℕ
  peers : ℕ
  referentPeers : ℕ

def ExposureData.Feasible (x : ExposureData) : Prop :=
  x.school ≤ 1 ∧ x.seed ≤ x.school ∧ x.referentPeers ≤ x.peers

inductive ExposureCase | control | school | nonreferent | referent | direct
  deriving DecidableEq

def printedCase (x : ExposureData) : ExposureCase → Prop
  | .control => x.school = 0
  | .school => x.school = 1 ∧ x.seed = 0 ∧ x.peers = 0
  | .nonreferent => x.school = 1 ∧ x.referentPeers = 0
  | .referent => x.school = 1 ∧ x.seed = 0 ∧ 0 < x.referentPeers
  | .direct => x.seed = 1

def correctedCase (x : ExposureData) : ExposureCase → Prop
  | .control => x.school = 0
  | .school => x.school = 1 ∧ x.seed = 0 ∧ x.peers = 0
  | .nonreferent => x.school = 1 ∧ x.seed = 0 ∧ 0 < x.peers ∧ x.referentPeers = 0
  | .referent => x.school = 1 ∧ x.seed = 0 ∧ 0 < x.referentPeers
  | .direct => x.seed = 1

noncomputable def frequency {A : Type*} [DecidableEq A]
    (J : ℕ) (draws : Fin J → A) (target : A) : ℝ :=
  (∑ j, if draws j = target then (1:ℝ) else 0) / J

noncomputable def contribution (I pi y g : ℝ) : ℝ :=
  g + I/pi*(y-g)

noncomputable def independentDesign {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (d : ∀ i, Design (Ω i)) :
    Design (∀ i, Ω i) where
  weight := fun w => ∏ i, (d i).weight (w i)
  nonneg := fun w => Finset.prod_nonneg (fun i _ => (d i).nonneg (w i))
  total := by
    classical
    calc
      (∑ w : ∀ i, Ω i, ∏ i, (d i).weight (w i)) = ∏ i, ∑ z, (d i).weight z := by
        symm
        simpa using Finset.prod_univ_sum (fun i => (Finset.univ : Finset (Ω i)))
          (fun i z => (d i).weight z)
      _ = 1 := by simp_rw [Design.total]; simp

noncomputable def probability {Ω : Type*} [Fintype Ω]
    (d : Design Ω) (event : Ω → Prop) : ℝ := by
  classical
  exact mean d (fun w => if event w then (1:ℝ) else 0)

noncomputable def waldStatistic (estimate se : ℝ) : ℝ := |estimate| / se

def tableS6Bins (estimate se : ℝ) : Prop :=
  estimate < 0 ∧ 11/200 < |estimate| ∧ |estimate| < 13/200 ∧
  1/40 < se ∧ se < 7/200

noncomputable def reduction (control treated : ℝ) : ℝ :=
  (control - treated) / control

def eligibleCount (n : ℕ) : ℕ :=
  if n ≤ 200 then 40 else if 550 ≤ n then 64 else
    4 * (10 + (6 * (n-200) + 175) / 350)

noncomputable def fittedEffect (intercept slope c : ℝ) : ℝ :=
  intercept + slope*c

end SAP.P037a
