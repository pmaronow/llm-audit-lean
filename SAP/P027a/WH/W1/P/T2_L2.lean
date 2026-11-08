import SAP.P027a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a.WH.W1.P.T2_L2

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory SAP.P027a.Bridge
attribute [local instance] Classical.propDecidable

end
end SAP.P027a.WH.W1.P.T2_L2

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory SAP.P027a.Bridge

theorem SAP.P027a.WH.W1.T2_L2_proof : SAP.P027a.WH.W1.T2_L2 := by
  intro Ξ _ μ _ r m hr hm β σ2 hσ ε hε
  dsimp only
  let K := Σ _ : Fin r × Fin 2, Fin m
  let D := phaseOriginal r m hr
  let z := centeredOutcomes phaseSize β ε
  let Y := fun ξ => groupTotal (fun _ : Fin r × Fin 2 => m) (z ξ)
  let q : ℝ := 2*r
  let N : ℝ := (m:ℝ)*q
  let M := 16*(m:ℝ)^2*β^2+(m:ℝ)*σ2*(1-1/q)
  let V := fun ξ => variance D (htTotal D (z ξ))
  let H := fun ξ => expect D (htVarianceEstimator D (z ξ))
  let Vm := fun ξ => variance D (htMean D (z ξ))
  let Hm := fun ξ => expect D (fun g => htVarianceEstimator D (z ξ) g/N^2)
  have hq : q ≠ 0 := by dsimp [q]; positivity
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN : N ≠ 0 := by dsimp [N]; exact mul_ne_zero hmR hq
  have hcard : (Fintype.card K : ℝ) = N := by
    simp only [K, Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul,
      Nat.cast_ofNat]
    dsimp [N, q]
    ring
  have hK : 0 < Fintype.card K := by
    have ht : (0:ℝ) < Fintype.card K := by rw [hcard]; dsimp [N, q]; positivity
    exact_mod_cast ht
  have hsizeSum : (∑ k : K, phaseSize k) = 6*N := by
    have hs := (AronowAudit.P027.periodic_size_moments r m hr hm).1
    simpa [K, N, q, SAP.P027a.phaseSize, AronowAudit.P027.phaseSize] using hs
  have hmeanx : (∑ k : K, phaseSize k)/(Fintype.card K:ℝ) = 6 := by
    rw [hcard, hsizeSum]
    field_simp [hN]
  have hmodel :=
    SAP.P027a.WH.W1.periodic_outcome_core μ r m hr hm β σ2 hσ ε hε
  dsimp only at hmodel
  rcases hmodel with ⟨hYSraw, _, hEVraw, hEHraw, _, hratiosraw⟩
  have hYS (g : Fin r × Fin 2) :
      Integrable (fun ξ => Y ξ g^2) μ ∧ outcomeE μ (fun ξ => Y ξ g^2) = M := by
    simpa [Y, M, q, z, SAP.P027a.groupTotal, SAP.P027a.centeredOutcomes,
      SAP.P027a.rawOutcomes, SAP.P027a.phaseSize] using hYSraw g
  have hEV : outcomeE μ V = (9/5)*q^2*M := by
    simpa [V, D, z, q, M] using hEVraw
  have hEH : outcomeE μ H = outcomeE μ V-q*M := by
    simpa [H, V, D, z, q, M] using hEHraw
  have hratios : 0 < M →
      (outcomeE μ H-outcomeE μ V)/outcomeE μ V = -5/(9*q) := by
    simpa [H, V, D, z, q, M] using hratiosraw
  have hrep1 (ξ : Ξ) (k : K) :
      z ξ k = β*(phaseSize k-6)+ε k ξ-(∑ l : K, ε l ξ)/N := by
    change SAP.P027a.centeredOutcomes phaseSize β ε ξ k = _
    unfold SAP.P027a.centeredOutcomes SAP.P027a.rawOutcomes
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsizeSum, hcard]
    field_simp [hN]
    ring
  have hrep2 (ξ : Ξ) (g : Fin r × Fin 2) :
      Y ξ g = (m:ℝ)*β*(if g.2 = 0 then -4 else 4) +
        (∑ j : Fin m, ε ⟨g,j⟩ ξ) - (m:ℝ)*(∑ l : K, ε l ξ)/N := by
    change (∑ j : Fin m, z ξ ⟨g,j⟩) = _
    simp_rw [hrep1 ξ]
    have hphase (j : Fin m) : phaseSize (⟨g,j⟩ : K)-6 =
        if g.2 = 0 then -4 else 4 := by
      unfold SAP.P027a.phaseSize
      split_ifs <;> norm_num
    simp_rw [hphase]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [hN]
  have hS : Integrable (fun ξ => ∑ g : Fin r × Fin 2, Y ξ g^2) μ :=
    integrable_finsetSum _ (fun g _ => (hYS g).1)
  have hzero (ξ : Ξ) : ∑ k : K, z ξ k = 0 := by
    have hcard0 : (Fintype.card K:ℝ) ≠ 0 := by rw [hcard]; exact hN
    unfold z SAP.P027a.centeredOutcomes SAP.P027a.rawOutcomes
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard]
    field_simp [hN]
    ring
  have hfinite (ξ : Ξ) :
      (∑ g : Fin r × Fin 2, Y ξ g = 0) ∧
        biasA D (z ξ) = -(∑ g : Fin r × Fin 2, Y ξ g^2) ∧
        0 ≤ (∑ g : Fin r × Fin 2, Y ξ g^2) ∧
        ((∑ g : Fin r × Fin 2, Y ξ g^2) = 0 ↔ ∀ g, Y ξ g = 0) ∧
        expect D (htTotal D (z ξ)) = 0 ∧
        variance D (htTotal D (z ξ)) = ∑ g : Fin r × Fin 2, Y ξ g^2/phaseProb r g ∧
        expect D (htVarianceEstimator D (z ξ)) =
          variance D (htTotal D (z ξ))-(∑ g : Fin r × Fin 2, Y ξ g^2) ∧
        True := by
    have hb := SAP.P027a.WH.W1.periodic_bias_core r m hr hm (z ξ) (hzero ξ)
    dsimp only at hb
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1,
      hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1, trivial⟩
  have hAfun : (fun ξ => biasA D (z ξ)) =
      (fun ξ => -(∑ g : Fin r × Fin 2, Y ξ g^2)) := by
    funext ξ
    exact (hfinite ξ).2.1
  have hVfun : V = (fun ξ => ∑ g : Fin r × Fin 2, Y ξ g^2/phaseProb r g) := by
    funext ξ
    exact (hfinite ξ).2.2.2.2.2.1
  have hHfun : H = (fun ξ => V ξ-(∑ g : Fin r × Fin 2, Y ξ g^2)) := by
    funext ξ
    exact (hfinite ξ).2.2.2.2.2.2.1
  have hVi (g : Fin r × Fin 2) :
      Integrable (fun ξ => Y ξ g^2/phaseProb r g) μ := (hYS g).1.div_const _
  have hExpDiv (f : Fin r × Fin 2 → ℝ) (c : ℝ) :
      SAP.P027a.expect D (fun ω => f ω/c) = SAP.P027a.expect D f/c := by
    unfold SAP.P027a.expect
    change (∑ ω, D.weight ω * (f ω/c)) = _
    calc
      (∑ ω, D.weight ω * (f ω/c)) =
          ∑ ω, (D.weight ω*f ω)/c := by
        apply Finset.sum_congr rfl
        intro ω hω
        ring
      _ = (∑ ω, D.weight ω*f ω)/c := by
        symm
        exact Finset.sum_div Finset.univ (fun ω => D.weight ω*f ω) c
  have hVint : Integrable V μ := by
    rw [hVfun]
    exact integrable_finsetSum _ (fun g _ => hVi g)
  have hHint : Integrable H μ := by
    rw [hHfun]
    exact hVint.sub hS
  have hAint : Integrable (fun ξ => biasA D (z ξ)) μ := by
    rw [hAfun]
    exact hS.neg
  have hVmfun : Vm = (fun ξ => V ξ/N^2) := by
    funext ξ
    change variance D (fun ω => htTotal D (z ξ) ω/(Fintype.card K:ℝ)) = _
    unfold SAP.P027a.variance
    rw [hExpDiv]
    simp only [← sub_div, div_pow]
    rw [hcard]
    exact hExpDiv _ _
  have hHmfun : Hm = (fun ξ => H ξ/N^2) := by
    funext ξ
    change expect D (fun g => htVarianceEstimator D (z ξ) g/N^2) = _
    exact hExpDiv _ _
  have hVmInt : Integrable Vm μ := by
    rw [hVmfun]
    exact hVint.div_const _
  have hHmInt : Integrable Hm μ := by
    rw [hHmfun]
    exact hHint.div_const _
  have hdiff : outcomeE μ (fun ξ => H ξ-V ξ) = -q*M := by
    unfold outcomeE
    rw [integral_sub hHint hVint]
    change outcomeE μ H-outcomeE μ V = -q*M
    rw [hEH, hEV]
    ring
  have hED : outcomeE μ (fun ξ => Hm ξ-Vm ξ) =
      outcomeE μ (fun ξ => H ξ-V ξ)/N^2 := by
    rw [hHmfun, hVmfun]
    unfold outcomeE
    rw [integral_sub (hHint.div_const (N^2)) (hVint.div_const (N^2))]
    simp only [integral_div]
    rw [integral_sub hHint hVint]
    ring
  refine ⟨hrep1, hrep2, hVint, hHint, hAint, hVmInt, hHmInt, hdiff, ?_⟩
  intro hM
  have hEVpos : 0 < outcomeE μ V := by
    rw [hEV]
    dsimp [q]
    positivity
  have hEVm : outcomeE μ Vm = outcomeE μ V/N^2 := by
    rw [hVmfun]
    unfold outcomeE
    rw [integral_div]
  have hEVmpos : 0 < outcomeE μ Vm := by
    rw [hEVm]
    exact div_pos hEVpos (sq_pos_of_ne_zero hN)
  have hratio : outcomeE μ (fun ξ => H ξ-V ξ)/outcomeE μ V = -5/(9*q) := by
    rw [show outcomeE μ (fun ξ => H ξ-V ξ) = outcomeE μ H-outcomeE μ V by
      unfold outcomeE
      rw [integral_sub hHint hVint]]
    exact (hratios hM)
  have hratioM : outcomeE μ (fun ξ => Hm ξ-Vm ξ)/outcomeE μ Vm = -5/(9*q) := by
    rw [hED, hEVm]
    calc
      (outcomeE μ (fun ξ => H ξ-V ξ)/N^2)/(outcomeE μ V/N^2) =
          outcomeE μ (fun ξ => H ξ-V ξ)/outcomeE μ V := by
        field_simp [hN]
      _ = -5/(9*q) := hratio
  exact ⟨hEVpos, hEVmpos, hratio, hratioM⟩
