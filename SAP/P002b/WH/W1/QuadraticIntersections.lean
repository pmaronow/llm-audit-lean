import SAP.P002b.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b.WH.W1
noncomputable section
open SAP.P002b

/-- The former T28 root-count obligation is proved here so that retaining the
corrected theorem creates no extra writer obligation for the refuted target. -/
theorem quadratic_intersections_bound (Q R : QuadraticAR) (hQ : ARRegular Q)
    (hR : ARRegular R) (hne : arFunction Q ≠ arFunction R) :
    ∃ roots : Finset ℝ, (∀ β, β ∈ roots ↔ arFunction Q β = arFunction R β) ∧
      roots.card ≤ 4 := by
  let num (q : QuadraticAR) : Polynomial ℝ :=
    Polynomial.C q.a * Polynomial.X^2 + Polynomial.C q.b * Polynomial.X + Polynomial.C q.c
  let den (q : QuadraticAR) : Polynomial ℝ :=
    Polynomial.C q.d * Polynomial.X^2 + Polynomial.C q.e * Polynomial.X + Polynomial.C q.f
  let p := num Q * den R - num R * den Q
  have hD (q : QuadraticAR) (hq : ARRegular q) (β : ℝ) :
      q.d*β^2+q.e*β+q.f ≠ 0 := ne_of_gt (hq.1 β)
  have heval (β : ℝ) : p.eval β =
      (Q.a*β^2+Q.b*β+Q.c)*(R.d*β^2+R.e*β+R.f) -
      (R.a*β^2+R.b*β+R.c)*(Q.d*β^2+Q.e*β+Q.f) := by simp [p, num, den]
  have hp : p ≠ 0 := by
    intro hz
    apply hne
    funext β
    apply (div_eq_div_iff (hD Q hQ β) (hD R hR β)).mpr
    have H : p.eval β = 0 := by rw [hz]; simp
    rw [heval] at H
    exact sub_eq_zero.mp H
  have hdeg : p.natDegree ≤ 4 := by
    dsimp [p, num, den]
    compute_degree
  refine ⟨p.roots.toFinset, ?_, ?_⟩
  · intro β
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    change p.eval β = 0 ↔ arFunction Q β = arFunction R β
    rw [heval, sub_eq_zero]
    exact (div_eq_div_iff (hD Q hQ β) (hD R hR β)).symm
  · exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' p).trans hdeg)

end
end SAP.P002b.WH.W1
