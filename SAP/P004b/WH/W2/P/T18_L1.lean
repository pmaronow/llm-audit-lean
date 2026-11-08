import SAP.P004b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2.P.T18_L1

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section

lemma balancedSign_sum (m : ℕ) :
    (∑ i : Fin (2*m), SAP.P004b.balancedSign (2*m) i) = 0 := by
  simp only [SAP.P004b.balancedSign]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => if i < (2*m)/2 then (1 : ℝ) else -1) (2*m)]
  rw [show 2*m = m+m by omega, Finset.sum_range_add]
  have hhalf : (m+m)/2 = m := by omega
  have hleft : (∑ i ∈ Finset.range m, (if i < m then (1 : ℝ) else -1)) = m := by
    calc
      _ = ∑ i ∈ Finset.range m, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        simp [hi']
      _ = m := by simp
  have hright : (∑ i ∈ Finset.range m, (if m+i < m then (1 : ℝ) else -1)) = -m := by
    have hfalse : ∀ i ∈ Finset.range m, ¬ m+i < m := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      omega
    calc
      _ = ∑ i ∈ Finset.range m, (-1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hf := hfalse i hi
        simp [hf]
      _ = -m := by simp
  rw [hhalf, hleft, hright]
  push_cast
  ring

lemma balancedSign_sq (m : ℕ) (i : Fin (2*m)) :
    (SAP.P004b.balancedSign (2*m) i)^2 = 1 := by
  simp [SAP.P004b.balancedSign]

lemma balanced_marginal {m : ℕ} (i : Fin (2*m)) (a : Bool) :
    SAP.P004b.marginal (fun _ : Fin (2*m) => (1/4 : ℝ))
      (SAP.P004b.balancedTable (2*m)) i a = SAP.P004b.balancedSign (2*m) i := by
  change AronowAudit.P004.marginal _ _ _ _ = _
  rw [AronowAudit.P004.marginal_is_marginalization _ _ _ _ (fun _ => by norm_num)]
  simp only [SAP.P004b.balancedTable]
  rw [AronowAudit.P004.expect_const]

lemma balanced_barMu_zero {m : ℕ} (_hm : 0 < m) (a : Bool) :
    SAP.P004b.barMu (fun _ : Fin (2*m) => (1/4 : ℝ))
      (SAP.P004b.balancedTable (2*m)) a = 0 := by
  unfold SAP.P004b.barMu
  have hs : (∑ i : Fin (2*m),
      SAP.P004b.marginal (fun _ => (1/4 : ℝ)) (SAP.P004b.balancedTable (2*m)) i a) = 0 := by
    simp_rw [balanced_marginal]
    exact balancedSign_sum m
  rw [hs]
  simp

lemma balanced_ame_zero {m : ℕ} (_hm : 0 < m) :
    SAP.P004b.ame (fun _ : Fin (2*m) => (1/4 : ℝ))
      (SAP.P004b.balancedTable (2*m)) = 0 := by
  unfold SAP.P004b.ame SAP.P004b.nodeEffect
  simp_rw [balanced_marginal]
  norm_num

lemma centered_mean {N : ℕ} (p : Fin N → ℝ) (a : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) :
    AronowAudit.P004.expect p (fun z => ∑ i, a i * (AronowAudit.P004.bit (z i)-p i)) = 0 := by
  rw [AronowAudit.P004.Wave1.TailBIpw_expect_finset p Finset.univ
    (fun i z => a i * (AronowAudit.P004.bit (z i)-p i))]
  apply Finset.sum_eq_zero
  intro i hi
  exact AronowAudit.P004.Wave1.TailBIpw_centered_mean p hp a i

lemma centered_second_moment {N : ℕ} (p : Fin N → ℝ) (a : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) :
    AronowAudit.P004.expect p (fun z => (∑ i, a i * (AronowAudit.P004.bit (z i)-p i))^2) =
      ∑ i, p i*(1-p i)*(a i)^2 := by
  have h := AronowAudit.P004.Wave1.TailBIpw_centered_moments p hp a Finset.univ
  simpa using h.1

lemma variance_of_scaled_centered {N : ℕ} (p : Fin N → ℝ)
    (X : SAP.P004b.Assignment N → ℝ) (c : ℝ) (hX : SAP.P004b.expect p X = 0) :
    SAP.P004b.variance p (fun z => c*X z) =
      c^2 * SAP.P004b.expect p (fun z => (X z)^2) := by
  unfold SAP.P004b.variance SAP.P004b.cov
  have hprod : (fun z => c*X z*(c*X z)) = fun z => c^2*(X z)^2 := by
    funext z
    ring
  rw [hprod]
  have he1 : SAP.P004b.expect p (fun z => c^2*(X z)^2) =
      c^2*SAP.P004b.expect p (fun z => (X z)^2) := by
    unfold SAP.P004b.expect
    calc
      _ = ∑ z, c^2*(SAP.P004b.designWeight p z*(X z)^2) := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _ = _ := by rw [Finset.mul_sum]
  have he2 : SAP.P004b.expect p (fun z => c*X z) = c*SAP.P004b.expect p X := by
    unfold SAP.P004b.expect
    calc
      _ = ∑ z, c*(SAP.P004b.designWeight p z*X z) := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _ = _ := by rw [Finset.mul_sum]
  rw [he1, he2, hX]
  ring

lemma balanced_formula_diff {m : ℕ} (hm : 0 < m)
    (z : SAP.P004b.Assignment (2*m)) :
    SAP.P004b.printedLinear (1/4) (SAP.P004b.balancedTable (2*m)) z -
      SAP.P004b.linearHajek (fun _ => (1/4 : ℝ)) (SAP.P004b.balancedTable (2*m)) z =
    -(1/(1/4 : ℝ)-1/(1-1/4 : ℝ)) *
      (∑ i, (1-SAP.P004b.bit (z i))*SAP.P004b.balancedSign (2*m) i)/(2*m) := by
  let p : Fin (2*m) → ℝ := fun _ => 1/4
  let R := SAP.P004b.balancedTable (2*m)
  have hN : 0 < 2*m := by omega
  have hmt := balanced_barMu_zero hm true
  have hmf := balanced_barMu_zero hm false
  have hame := balanced_ame_zero hm
  have hlin := SAP.P004b.Bridge.linearFormula_eq p R hN z
  rw [show p = (fun _ : Fin (2*m) => (1/4 : ℝ)) from rfl,
      show R = SAP.P004b.balancedTable (2*m) from rfl] at hlin
  rw [hlin]
  unfold SAP.P004b.printedLinear SAP.P004b.linearFormula
  rw [hame, hmt, hmf]
  simp only [zero_sub, sub_zero, add_zero, zero_add]
  simp only [R, SAP.P004b.balancedTable]
  have hnum :
      (∑ i, (SAP.P004b.bit (z i)*SAP.P004b.balancedSign (2*m) i/(1/4 : ℝ) -
        (1-SAP.P004b.bit (z i))*SAP.P004b.balancedSign (2*m) i/(1/4 : ℝ))) -
      (∑ i, (SAP.P004b.bit (z i)*SAP.P004b.balancedSign (2*m) i/(1/4 : ℝ) -
        (1-SAP.P004b.bit (z i))*SAP.P004b.balancedSign (2*m) i/(1-1/4 : ℝ))) =
      -(1/(1/4 : ℝ)-1/(1-1/4 : ℝ)) *
        ∑ i, (1-SAP.P004b.bit (z i))*SAP.P004b.balancedSign (2*m) i := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ i, (-(1/(1/4 : ℝ)-1/(1-1/4 : ℝ)) *
          ((1-SAP.P004b.bit (z i))*SAP.P004b.balancedSign (2*m) i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        norm_num
        ring
      _ = _ := by rw [Finset.mul_sum]
  rw [← sub_div, hnum]
  norm_num

lemma centered_rewrite {m : ℕ} (z : SAP.P004b.Assignment (2*m)) :
    (∑ i : Fin (2*m), (1-SAP.P004b.bit (z i))*SAP.P004b.balancedSign (2*m) i) =
      -(∑ i, SAP.P004b.balancedSign (2*m) i *
          (SAP.P004b.bit (z i)-(1/4 : ℝ))) := by
  have hsum := SAP.P004b.WH.W2.P.T18_L1.balancedSign_sum m
  have hleft :
      (∑ i : Fin (2*m), (1-SAP.P004b.bit (z i))*SAP.P004b.balancedSign (2*m) i) =
        (∑ i, SAP.P004b.balancedSign (2*m) i) -
          ∑ i, SAP.P004b.balancedSign (2*m) i*SAP.P004b.bit (z i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hright :
      (∑ i : Fin (2*m), SAP.P004b.balancedSign (2*m) i *
          (SAP.P004b.bit (z i)-(1/4 : ℝ))) =
        (∑ i, SAP.P004b.balancedSign (2*m) i*SAP.P004b.bit (z i)) -
          (1/4 : ℝ)*(∑ i, SAP.P004b.balancedSign (2*m) i) := by
    calc
      _ = ∑ i, (SAP.P004b.balancedSign (2*m) i*SAP.P004b.bit (z i) -
          (1/4 : ℝ)*SAP.P004b.balancedSign (2*m) i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hleft, hright, hsum]
  ring

end
end SAP.P004b.WH.W2.P.T18_L1

theorem SAP.P004b.WH.W2.T18_L1_proof : SAP.P004b.WH.W2.T18_L1 := by
  unfold SAP.P004b.WH.W2.T18_L1 SAP.P004b.BalancedLinearFacts
  intro m hm
  let N : ℕ := 2*m
  let p : Fin N → ℝ := fun _ => 1/4
  let R : SAP.P004b.CircleTable N := SAP.P004b.balancedTable N
  have hN : 0 < N := by dsimp [N]; omega
  have hsign : (∑ i : Fin N, SAP.P004b.balancedSign N i) = 0 := by
    simpa [N] using SAP.P004b.WH.W2.P.T18_L1.balancedSign_sum m
  have hsq : ∀ i : Fin N, (SAP.P004b.balancedSign N i)^2 = 1 := by
    intro i
    simpa [N] using SAP.P004b.WH.W2.P.T18_L1.balancedSign_sq m i
  have hmt : SAP.P004b.barMu p R true = 0 := by
    simpa [p, R, N] using SAP.P004b.WH.W2.P.T18_L1.balanced_barMu_zero hm true
  have hmf : SAP.P004b.barMu p R false = 0 := by
    simpa [p, R, N] using SAP.P004b.WH.W2.P.T18_L1.balanced_barMu_zero hm false
  have hame : SAP.P004b.ame p R = 0 := by
    simpa [p, R, N] using SAP.P004b.WH.W2.P.T18_L1.balanced_ame_zero hm
  have hformula : ∀ z,
      SAP.P004b.printedLinear (1/4) R z-SAP.P004b.linearHajek p R z =
        -(1/(1/4 : ℝ)-1/(1-1/4 : ℝ)) *
          (∑ i, (1-SAP.P004b.bit (z i))*SAP.P004b.balancedSign N i)/N := by
    intro z
    simpa [N, R, p] using SAP.P004b.WH.W2.P.T18_L1.balanced_formula_diff hm z
  have hp : ∀ i : Fin N, 0 < p i ∧ p i < 1 := by
    intro i
    norm_num [p]
  let a : Fin N → ℝ := fun i => SAP.P004b.balancedSign N i
  let G : SAP.P004b.Assignment N → ℝ := fun z =>
    ∑ i, a i*(SAP.P004b.bit (z i)-p i)
  have hGmean : SAP.P004b.expect p G = 0 := by
    change AronowAudit.P004.expect p
      (fun z => ∑ i, a i*(AronowAudit.P004.bit (z i)-p i)) = 0
    exact SAP.P004b.WH.W2.P.T18_L1.centered_mean p a hp
  have hGsecond : SAP.P004b.expect p (fun z => (G z)^2) = (3/16 : ℝ)*(N : ℝ) := by
    change AronowAudit.P004.expect p
      (fun z => (∑ i, a i*(AronowAudit.P004.bit (z i)-p i))^2) = (3/16 : ℝ)*(N : ℝ)
    have h := SAP.P004b.WH.W2.P.T18_L1.centered_second_moment p a hp
    rw [h]
    simp only [p, a]
    have hconst : ∀ i : Fin N,
        (1/4 : ℝ)*(1-1/4)*(SAP.P004b.balancedSign N i)^2 = 3/16 := by
      intro i
      rw [hsq]
      norm_num
    simp_rw [hconst]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsum_center : ∀ z,
      (∑ i, (1-SAP.P004b.bit (z i))*SAP.P004b.balancedSign N i) = -G z := by
    intro z
    dsimp [G, a, p]
    simpa [N] using SAP.P004b.WH.W2.P.T18_L1.centered_rewrite z
  have hdiff : ∀ z,
      SAP.P004b.printedLinear (1/4) R z-SAP.P004b.linearHajek p R z =
        ((8/3 : ℝ)/(N : ℝ))*G z := by
    intro z
    rw [hformula z, hsum_center z]
    norm_num
    ring
  let c : ℝ := (8/3 : ℝ)/(N : ℝ)
  have hfun : (fun z => SAP.P004b.printedLinear (1/4) R z-
      SAP.P004b.linearHajek p R z) = fun z => c*G z := by
    funext z
    rw [hdiff z]
  have hvar : SAP.P004b.variance p (fun z => c*G z) =
      c^2*SAP.P004b.expect p (fun z => (G z)^2) :=
    SAP.P004b.WH.W2.P.T18_L1.variance_of_scaled_centered p G c hGmean
  have hscaled : (N : ℝ)*SAP.P004b.variance p
      (fun z => SAP.P004b.printedLinear (1/4) R z-
        SAP.P004b.linearHajek p R z) = 4/3 := by
    rw [hfun, hvar, hGsecond]
    dsimp [c]
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
    field_simp [hNne]
    <;> norm_num
    <;> ring
  refine ⟨hmt, hmf, ?_, hscaled⟩
  intro z
  simpa [N, R, p] using hformula z

