import SAP.P053.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The corrected Section 4 claim includes the affine identities, the explicit factor uniform
over outcome vectors with the same total, the symmetric-sample assertion and its converse,
and the exact table-constancy criterion. The existential sample-cardinality certificates
only supply the indices for the two ordered samples.
-/

namespace SAP.P053
open Filter
open scoped BigOperators Topology
noncomputable section

/-- All five clauses of the corrected table-statistic claim, with a common
factor across all binary outcome vectors having the same total number of successes. -/
def T1Statement (S : Type*) : Prop :=
  ∀ (n1 n0 : ℕ), 0 < n1 → 0 < n0 → ∀ y : Fin (n1+n0) → Bool,
    (∀ s ∈ support n1,
      binaryTau n1 n0 y s =
        (((n1 : ℝ)+n0)*successes y s-n1*totalSuccesses y)/((n1 : ℝ)*n0) ∧
      reconstruct n1 n0 (totalSuccesses y) (binaryTau n1 n0 y s) = (successes y s : ℝ)) ∧
    (∀ s ∈ support n1, ∀ t ∈ support n1,
      (binaryTau n1 n0 y s = binaryTau n1 n0 y t ↔ successes y s = successes y t) ∧
      (successes y s = successes y t ↔
        countTable n1 n0 (totalSuccesses y) (successes y s) =
          countTable n1 n0 (totalSuccesses y) (successes y t))) ∧
    (∀ h : (ℤ × ℤ × ℤ × ℤ) → S, ∃ g : ℝ → S,
      g = tableFactor n1 n0 (totalSuccesses y) h ∧
      ∀ yy : Fin (n1+n0) → Bool, totalSuccesses yy = totalSuccesses y →
        ∀ s ∈ support n1,
          h (countTable n1 n0 (totalSuccesses y) (successes yy s)) = g (binaryTau n1 n0 yy s)) ∧
    (∀ F : (Fin n1 → Bool) → (Fin n0 → Bool) → S,
      (∀ x1 x0 (p1 : Equiv.Perm (Fin n1)) (p0 : Equiv.Perm (Fin n0)),
        F (x1 ∘ p1) (x0 ∘ p0) = F x1 x0) →
      ∃ g : ℝ → S, ∀ (s : Finset (Fin (n1+n0))) (_hs : s ∈ support n1),
        ∃ ht : s.card = n1, ∃ hc : sᶜ.card = n0,
          F (orderedBinarySample y s ht) (orderedBinarySample y sᶜ hc) =
            F (canonical n1 (successes y s)) (canonical n0 (totalSuccesses y-successes y s)) ∧
          F (orderedBinarySample y s ht) (orderedBinarySample y sᶜ hc) = g (binaryTau n1 n0 y s)) ∧
    (∀ (h : (ℤ × ℤ × ℤ × ℤ) → S) (x1 : Fin n1 → Bool) (x0 : Fin n0 → Bool)
      (p1 : Equiv.Perm (Fin n1)) (p0 : Equiv.Perm (Fin n0)),
      h ((totalSuccesses (x1 ∘ p1) : ℤ), (n1 : ℤ)-totalSuccesses (x1 ∘ p1),
          (totalSuccesses (x0 ∘ p0) : ℤ), (n0 : ℤ)-totalSuccesses (x0 ∘ p0)) =
      h ((totalSuccesses x1 : ℤ), (n1 : ℤ)-totalSuccesses x1,
          (totalSuccesses x0 : ℤ), (n0 : ℤ)-totalSuccesses x0)) ∧
    (∀ T : {s : Finset (Fin (n1+n0)) // s.card = n1} → S,
      (∃ g : ℝ → S, ∀ s, T s = g (binaryTau n1 n0 y s.val)) ↔
      (∀ s t, countTable n1 n0 (totalSuccesses y) (successes y s.val) =
        countTable n1 n0 (totalSuccesses y) (successes y t.val) → T s = T t))

end
end SAP.P053
