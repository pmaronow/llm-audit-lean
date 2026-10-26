import AronowAudit.P018.Wave1.Gap.GP0181B1

/-! Finite sign-sample algebra, with the same unordered dyads as P018. -/
noncomputable section
namespace AronowAudit.P018.Wave1.TailBSign
open Finset Matrix
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem tb05_pair_product {N : ℕ} (z : Fin N → ℝ) :
    2 * (∑ d : Dyad N, z (firstUnit d) * z (secondUnit d)) =
      (∑ i, z i)^2 - ∑ i, (z i)^2 := by
  have h := printed_pair_sum (fun i j => z i * z j) (fun i j => mul_comm _ _)
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← pow_two] using h

theorem tb05_pair_mixed {N : ℕ} (z w : Fin N → ℝ) (hz : ∀ i, (z i)^2 = 1) :
    (∑ d : Dyad N, z (firstUnit d) * z (secondUnit d) *
      (w (firstUnit d) + w (secondUnit d))) =
      (∑ i, z i) * (∑ i, z i * w i) - ∑ i, w i := by
  have h := printed_pair_sum (fun i j => z i * z j * (w i + w j))
    (fun i j => by ring)
  have hrow (i : Fin N) : (∑ j, z i * z j * (w i + w j)) =
      z i * w i * (∑ j, z j) + z i * (∑ j, z j * w j) := by
    simp_rw [show ∀ j, z i * z j * (w i + w j) =
      (z i * w i) * z j + z i * (z j * w j) from fun j => by ring]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hdiag (i : Fin N) : z i * z i * (w i + w i) = 2 * w i := by
    calc
      _ = 2*w i*(z i)^2 := by ring
      _ = _ := by rw [hz]; ring
  simp_rw [hrow, hdiag] at h
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum] at h
  linarith

theorem tb05_incident {N : ℕ} (F : Fin N → Fin N → ℝ)
    (hs : ∀ i j, F i j = F j i) (i : Fin N) :
    (∑ d : Dyad N, if i ∈ members d then F (firstUnit d) (secondUnit d) else 0) =
      (∑ j, F i j) - F i i := by
  classical
  let H : Fin N → Fin N → ℝ := fun a b =>
    if i ∈ ({a,b} : Finset (Fin N)) then F a b else 0
  have hsym : ∀ a b, H a b = H b a := by
    intro a b
    by_cases ha : i = a <;> by_cases hb : i = b <;> simp [H, ha, hb, hs a b]
  have h := printed_pair_sum H hsym
  have hrow (a : Fin N) : (∑ b, H a b) - H a a =
      if a = i then (∑ b, F i b) - F i i else F a i := by
    by_cases ha : a = i
    · subst a
      simp [H]
    · simp [H, ha, Ne.symm ha, eq_comm]
  simp_rw [hrow] at h
  have hsplit : (∑ a : Fin N,
      if a = i then (∑ b, F i b) - F i i else F a i) =
      ((∑ b, F i b) - F i i) + (∑ a, if a ≠ i then F a i else 0) := by
    simp [Finset.sum_ite, Finset.filter_ne', Finset.filter_eq']
  have hoff : (∑ a, if a ≠ i then F a i else 0) = (∑ a, F i a) - F i i := by
    simpa only [hs, ne_comm] using printed_offdiag (fun _ a => F a i) i
  rw [hsplit, hoff] at h
  simp_rw [H, ← printed_members_endpoints] at h
  linarith

theorem tb05_basis_square {N : ℕ} (z w : Fin N → ℝ)
    (hz : ∀ i, (z i)^2 = 1) (hw : ∀ i, (w i)^2 = 1) (A B C E : ℝ) :
    (∑ i, (A + B*z i + C*w i + E*z i*w i)^2) =
      (N : ℝ)*(A^2+B^2+C^2+E^2) +
      2*((A*B+C*E)*(∑ i,z i) + (A*C+B*E)*(∑ i,w i) +
        (A*E+B*C)*(∑ i,z i*w i)) := by
  have ht (i : Fin N) : (A+B*z i+C*w i+E*z i*w i)^2 =
      (A^2+B^2+C^2+E^2) + 2*(A*B+C*E)*z i +
        2*(A*C+B*E)*w i + 2*(A*E+B*C)*(z i*w i) := by
    ring_nf
    simp only [hz, hw]
    ring
  simp_rw [ht]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- Centered slope score after the exact two-regressor OLS fit. -/
def tb05_slopeScore {N : ℕ} (z w : Fin N → ℝ) (a b l : ℝ) (i j : Fin N) : ℝ :=
  (z i*z j-l)*(w i+w j-a-b*z i*z j)

theorem tb05_node_score {N : ℕ} (z w : Fin N → ℝ) (hz : ∀ i, (z i)^2 = 1)
    (a b l : ℝ) (i : Fin N) :
    (∑ d : Dyad N, if i ∈ members d then
      tb05_slopeScore z w a b l (firstUnit d) (secondUnit d) else 0) =
      (-l*(∑ j,w j)+a*(1+l*((N:ℝ)-1))-b*((N:ℝ)-1+l)) +
      ((∑ j,z j*w j)-a*(∑ j,z j)+b*l*(∑ j,z j))*z i +
      (-2-l*((N:ℝ)-2))*w i + (∑ j,z j)*z i*w i := by
  rw [tb05_incident _ (fun i j => by dsimp [tb05_slopeScore]; ring)]
  have ht (j : Fin N) : tb05_slopeScore z w a b l i j =
      z i*w i*z j + z i*(z j*w j) - l*w i - l*w j - a*z i*z j + a*l - b + b*l*z i*z j := by
    dsimp [tb05_slopeScore]
    ring_nf
    simp only [hz]
    ring
  have hd : tb05_slopeScore z w a b l i i = (1-l)*(2*w i-a-b) := by
    have h4 : (z i)^4=1 := by rw [show (4:ℕ)=2*2 by decide,pow_mul,hz]; norm_num
    dsimp [tb05_slopeScore]
    ring_nf
    simp only [hz,h4]
    ring
  rw [hd]
  simp_rw [ht]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring


theorem tb05_pair_twisted_square {N : ℕ} (z w : Fin N → ℝ)
    (hz : ∀ i, (z i)^2 = 1) (hw : ∀ i, (w i)^2 = 1) :
    (∑ d : Dyad N, z (firstUnit d)*z (secondUnit d)*
      (w (firstUnit d)+w (secondUnit d))^2) =
      (∑ i,z i)^2+(∑ i,z i*w i)^2-2*(N:ℝ) := by
  have h1 := tb05_pair_product z
  have h2 := tb05_pair_product (fun i => z i*w i)
  have ht (i j : Fin N) : z i*z j*(w i+w j)^2 =
      2*(z i*z j)+2*((z i*w i)*(z j*w j)) := by
    calc
      _ = z i*z j*((w i)^2+2*w i*w j+(w j)^2) := by ring
      _ = _ := by rw [hw,hw]; ring
  simp_rw [ht]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [mul_pow,hz,hw,mul_one,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at h1 h2
  linarith

theorem tb05_edge_score_square {N : ℕ} (z w : Fin N → ℝ)
    (hz : ∀ i, (z i)^2 = 1) (hw : ∀ i, (w i)^2 = 1) (a b l : ℝ) :
    (∑ d : Dyad N, (tb05_slopeScore z w a b l (firstUnit d) (secondUnit d))^2) =
      (1+l^2)*((N:ℝ)*((N:ℝ)-2)+(∑ i,w i)^2-
        2*a*((N:ℝ)-1)*(∑ i,w i)-2*b*((∑ i,z i)*(∑ i,z i*w i)-(∑ i,w i))+
        (a^2+b^2)*Dreal N+a*b*((∑ i,z i)^2-(N:ℝ))) -
      2*l*((∑ i,z i)^2+(∑ i,z i*w i)^2-2*(N:ℝ)-
        2*a*((∑ i,z i)*(∑ i,z i*w i)-(∑ i,w i))-
        2*b*((N:ℝ)-1)*(∑ i,w i)+
        (a^2+b^2)*((∑ i,z i)^2-(N:ℝ))/2+2*a*b*Dreal N) := by
  have ht (i j : Fin N) : (tb05_slopeScore z w a b l i j)^2 =
      (1+l^2)*((w i+w j)^2-2*a*(w i+w j)-2*b*(z i*z j*(w i+w j))+
        (a^2+b^2)+2*a*b*(z i*z j)) -
      2*l*(z i*z j*(w i+w j)^2-2*a*(z i*z j*(w i+w j))-
        2*b*(w i+w j)+(a^2+b^2)*(z i*z j)+2*a*b) := by
    have hpoly (t y : ℝ) (h2 : t^2=1) : ((t-l)*(y-a-b*t))^2 =
        (1+l^2)*(y^2-2*a*y-2*b*(t*y)+(a^2+b^2)+2*a*b*t)-
        2*l*(t*y^2-2*a*(t*y)-2*b*y+(a^2+b^2)*t+2*a*b) := by
      have h3 : t^3=t := by rw [pow_succ,h2,one_mul]
      have h4 : t^4=1 := by rw [show (4:ℕ)=2*2 by decide,pow_mul,h2]; norm_num
      ring_nf
      simp only [h2,h3,h4]
      ring
    convert hpoly (z i*z j) (w i+w j) (by rw [mul_pow,hz,hz]; ring) using 1 <;>
      dsimp only [tb05_slopeScore] <;> ring
  simp only [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hadd : (∑ d : Dyad N,w (firstUnit d))+(∑ d : Dyad N,w (secondUnit d)) =
      ((N:ℝ)-1)*(∑ i,w i) := by
    rw [← Finset.sum_add_distrib]
    exact printed_pair_add w
  rw [printed_pair_square, tb05_pair_mixed z w hz,
    tb05_pair_twisted_square z w hz hw]
  simp only [hadd]
  have hp := tb05_pair_product z
  simp only [hz, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hp
  simp only [hw, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, printed_card_real, mul_one]
  have hp' : (∑ d : Dyad N,z (firstUnit d)*z (secondUnit d)) =
      ((∑ i,z i)^2-(N:ℝ))/2 := by linarith [hp]
  rw [hp']
  ring

end AronowAudit.P018.Wave1.TailBSign
