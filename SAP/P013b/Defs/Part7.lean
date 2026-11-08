import Mathlib
import SAP.P013b.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P013b
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]


def T22Statement : Prop :=
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ) (z : Ω) (hN : 0 < N) (hd : ∀ i, 0 < pi F i d),
    differenceTotal (shiftPopulation F c) d (fun i => g i + h i) z -
      differenceTotal F d g z =
        c * htCount F d z + ∑ i, (1 - exposureWeight F d z i) * h i) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ) (z : Ω) (hN : 0 < N) (hd : ∀ i, 0 < pi F i d),
    differenceTotal (shiftPopulation F c) d (fun i => g i + h i) z -
      differenceTotal F d g z - c * N = translationError F d h c z) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ) (z : Ω) (hN : 0 < N) (hd : ∀ i, 0 < pi F i d),
    (differenceTotal (shiftPopulation F c) d (fun i => g i + h i) z =
      differenceTotal F d g z + c * N) ↔ translationError F d h c z = 0) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g : Fin N → ℝ) (c : ℝ) (z : Ω) (hN : 0 < N) (hd : ∀ i, 0 < pi F i d),
    differenceTotal (shiftPopulation F c) d (fun i => g i + c) z =
      differenceTotal F d g z + c * N) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d e : Fin K)
    (gk gl : Fin N → ℝ) (c : ℝ) (z : Ω) (hd : ∀ i, 0 < pi F i d)
    (he : ∀ i, 0 < pi F i e) (hne : d ≠ e),
    (differenceTotal (shiftPopulation F c) d (fun i => gk i + c) z / N =
      differenceTotal F d gk z / N + c) ∧
    (differenceTotal (shiftPopulation F c) e (fun i => gl i + c) z / N =
      differenceTotal F e gl z / N + c) ∧
    (∀ i, F.exposure z i = d → observed (shiftPopulation F c) z i - (gk i + c) = observed F z i - gk i) ∧
    (∀ i, F.exposure z i = e → observed (shiftPopulation F c) z i - (gl i + c) = observed F z i - gl i) ∧
    differenceEffect (shiftPopulation F c) d e (fun i => gk i + c) (fun i => gl i + c) z =
      differenceEffect F d e gk gl z ∧
    potentialTotal (shiftPopulation F c) d = potentialTotal F d + c * N ∧
    potentialTotal (shiftPopulation F c) e = potentialTotal F e + c * N ∧
    causalEffect (shiftPopulation F c) d e = causalEffect F d e) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d e : Fin K)
    (gk gl hk hl : Fin N → ℝ) (c : ℝ) (z : Ω) (hd : ∀ i, 0 < pi F i d)
    (he : ∀ i, 0 < pi F i e) (hne : d ≠ e),
    differenceEffect (shiftPopulation F c) d e (fun i => gk i + hk i)
        (fun i => gl i + hl i) z - differenceEffect F d e gk gl z =
      (translationError F d hk c z - translationError F e hl c z) / N ∧
    (differenceEffect (shiftPopulation F c) d e (fun i => gk i + hk i)
        (fun i => gl i + hl i) z = differenceEffect F d e gk gl z ↔
      translationError F d hk c z = translationError F e hl c z)) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d e : Fin K)
    (gk gl : Fin N → ℝ) (c : ℝ) (z : Ω) (hd : ∀ i, 0 < pi F i d)
    (he : ∀ i, 0 < pi F i e) (hne : d ≠ e),
    differenceTotal (shiftPopulation F c) d gk z - differenceTotal F d gk z =
      c * htCount F d z ∧
    differenceTotal (shiftPopulation F c) d gk z - differenceTotal F d gk z - c * N =
      c * (htCount F d z - N) ∧
    differenceEffect (shiftPopulation F c) d e gk gl z - differenceEffect F d e gk gl z =
      c * (htCount F d z - htCount F e z) / N ∧
    (c ≠ 0 → (differenceTotal (shiftPopulation F c) d gk z =
      differenceTotal F d gk z + c * N ↔ htCount F d z = N) ∧
      (differenceEffect (shiftPopulation F c) d e gk gl z = differenceEffect F d e gk gl z ↔
        htCount F d z = htCount F e z))) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (i : Fin N) (hi : 0 < pi F i d),
    expectation P (fun z => exposureWeight F d z i) = 1) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d e : Fin K) (c : ℝ) (z : Ω) (hd : ∀ i, 0 < pi F i d)
    (he : ∀ i, 0 < pi F i e) (hne : d ≠ e),
    differenceTotal F d (fun _ => 0) z = htTotal F d z ∧
    differenceEffect F d e (fun _ => 0) (fun _ => 0) z = htEffect F d e z ∧
    htTotal (shiftPopulation F c) d z - htTotal F d z = c * htCount F d z ∧
    htEffect (shiftPopulation F c) d e z - htEffect F d e z =
      c * (htCount F d z - htCount F e z) / N) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ)
    (hd : ∀ i, 0 < pi F i d),
    expectation P (translationError F d h c) = 0 ∧
    expectation P (differenceTotal (shiftPopulation F c) d (fun i => g i + h i)) =
      expectation P (differenceTotal F d g) + c * N ∧
    expectation P (differenceTotal (shiftPopulation F c) d (fun i => g i + h i)) =
      potentialTotal F d + c * N ∧
    expectation P (htCount F d) = N) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d e : Fin K) (c : ℝ)
    (hd : ∀ i, 0 < pi F i d) (he : ∀ i, 0 < pi F i e) (hN : 0 < N) (hne : d ≠ e),
    expectation P (fun z => c * (htCount F d z - N)) = 0 ∧
    expectation P (fun z => c * (htCount F d z - htCount F e z) / N) = 0) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d : Fin K) (m : ℕ) (hm : 1 ≤ m)
    (hcount : ∀ z, ∑ i, indicator F.exposure i d z = (m : ℝ))
    (hmarg : ∀ i, pi F i d = (m : ℝ) / N) (g : Fin N → ℝ) (c : ℝ),
    ∀ z, htCount F d z = N ∧
      differenceTotal (shiftPopulation F c) d g z = differenceTotal F d g z + c * N) ∧
  (
    (∀ d, Positivity calibrationPopulation d) ∧
    (∀ z, htCount calibrationPopulation 1 z = 2 ∧
      differenceTotal (shiftPopulation calibrationPopulation 1) 1 (fun _ => 0) z =
        differenceTotal calibrationPopulation 1 (fun _ => 0) z + 2))

end
end SAP.P013b
