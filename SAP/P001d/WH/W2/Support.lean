import SAP.P001d.Defs.WholeW2
import SAP.P001d.Bridge
import AronowAudit.P001.Wave1.Gap.TailA.HeavyMedian
import AronowAudit.P001.Wave1.Gap.TailA.MedianMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W2

local instance instDecidableSupport (p : Prop) : Decidable p := Classical.propDecidable p

theorem restricted58 : T58Statement := by
  have h := AronowAudit.P001.signed_kernel_not_cdf
  exact ⟨h.1, h.2.1, h.2.2.1, fun a => ⟨by simp [kernelDensity], h.2.2.2 a⟩⟩

theorem restricted61 {Ω : Type*} [MeasurableSpace Ω] : T61Statement Ω := by
  intro μ hμ X hiid hlaw
  exact ⟨AronowAudit.P001.Wave1.TailA.heavy_median_bootstrap_variance_counterexample_final
      μ X hiid hlaw,
    AronowAudit.P001.Wave1.regular_functional_bootstrap_variance_counterexample_proof
      μ X hiid hlaw⟩

theorem restricted70 : T70Statement := by
  intro n hn J x y
  have hu : ∀ B : ℝ, ∃ b : Fin (J+1) → ℝ,
      (∑ i, (y i-∑ k, b k*x i^k.val)) < B := by
    intro B
    obtain ⟨b0, hb⟩ := AronowAudit.P001.unsquared_sieve_no_minimum hn y B
    refine ⟨fun k => if k = 0 then b0 else 0, ?_⟩
    simpa [Fin.sum_univ_succ] using hb
  refine ⟨hu, ?_, ?_, ?_⟩
  · rintro ⟨b, hb⟩
    obtain ⟨c, hc⟩ := hu (∑ i, (y i-∑ k, b k*x i^k.val))
    exact (not_lt_of_ge (hb c)) hc
  · intro b
    simp only [olsRSS, polynomialDesign, Matrix.mulVec, dotProduct, mul_comm]
  · intro hunit
    exact (AronowAudit.P001.polynomial_squared_criterion_ols x y (polynomialDesign x J)
      (fun _ _ => rfl) hunit).2

/-- Factor evaluation through the finite set of distinct nodes and compare dimensions. -/
theorem distinct_nodes {n J : ℕ} (x : Fin n → ℝ)
    (hu : IsUnit ((polynomialDesign x J).transpose * polynomialDesign x J).det) :
    J+1 ≤ (Finset.univ.image x).card := by
  let s := Finset.univ.image x
  let P := polynomialDesign x J
  let Q : Matrix s (Fin (J+1)) ℝ := fun z k => (z : ℝ)^k.val
  have hiG : Function.Injective (P.transpose * P).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  have hiP : Function.Injective P.mulVec := by
    intro b c h
    apply hiG
    simpa only [← Matrix.mulVec_mulVec] using congrArg P.transpose.mulVec h
  have hiQ : Function.Injective Q.mulVecLin := by
    intro b c h
    apply hiP
    funext i
    have hx : x i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact congrFun h ⟨x i, hx⟩
  have hd := LinearMap.finrank_le_finrank_of_injective hiQ
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Fintype.card_coe, smul_eq_mul, mul_one] using hd

theorem unsquared_expansion {n J : ℕ} (x y : Fin n → ℝ) (b : Fin (J+1) → ℝ) :
    wholeUnsquared x y b =
      (∑ i, y i) - (n : ℝ)*b 0 - ∑ k : Fin J, b k.succ * ∑ i, x i ^ k.succ.val := by
  simp only [wholeUnsquared, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  ring

theorem unsquared_limit {n J : ℕ} (hn : 0 < n) (x y : Fin n → ℝ)
    (b : Fin (J+1) → ℝ) :
    Tendsto (fun a : ℝ => wholeUnsquared x y (Function.update b 0 a)) atTop atBot := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp_rw [unsquared_expansion, Function.update_self]
  have he (a : ℝ) (k : Fin J) : Function.update b 0 a k.succ = b k.succ :=
    Function.update_of_ne (Fin.succ_ne_zero k) a b
  simp_rw [he]
  apply Filter.tendsto_atBot.mpr
  intro B
  let C := (∑ i, y i) - ∑ k : Fin J, b k.succ * ∑ i, x i ^ k.succ.val
  filter_upwards [eventually_ge_atTop ((C-B)/(n : ℝ))] with a ha
  have hh := (div_le_iff₀ hnR).mp ha
  dsimp [C] at hh
  simp only [Fin.val_succ] at hh ⊢
  nlinarith

theorem finite73 : T73WholeStatement := by
  have hbase : T73Statement := by
    refine ⟨?_, ?_, ?_⟩
    · norm_num [finiteProb, heteroX, Fin.sum_univ_succ]
    · norm_num [finiteProb, heteroX, Fin.sum_univ_succ]
    · simpa only [Bridge.finiteCond_eq, Bridge.finiteMean_eq, Bridge.finiteCov_eq,
        Bridge.project_finiteProb_eq, Bridge.heteroX_eq, Bridge.heteroY_eq,
        Bridge.heteroResidual_eq] using AronowAudit.P001.cef_residual_not_independent
  refine ⟨hbase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> norm_num [heteroResidual, heteroX, heteroY]
  · intro r
    by_cases h1 : r = -1
    · subst r; norm_num [finiteProb, heteroResidual, heteroX, heteroY, Fin.sum_univ_succ]
    by_cases h2 : r = 1
    · subst r; norm_num [finiteProb, heteroResidual, heteroX, heteroY, Fin.sum_univ_succ]
    by_cases h3 : r = -3
    · subst r; norm_num [finiteProb, heteroResidual, heteroX, heteroY, Fin.sum_univ_succ]
    by_cases h4 : r = 3
    · subst r; norm_num [finiteProb, heteroResidual, heteroX, heteroY, Fin.sum_univ_succ]
    have h1' := Ne.symm h1
    have h2' := Ne.symm h2
    have h3' := Ne.symm h3
    have h4' := Ne.symm h4
    norm_num [finiteProb, heteroResidual, heteroX, heteroY, Fin.sum_univ_succ,
      h1, h2, h3, h4, h1', h2', h3', h4']
  · intro i
    fin_cases i <;> norm_num [finiteCond, finiteProb, heteroX, heteroY, Fin.sum_univ_succ]
  · intro x hx
    rcases hx with rfl | hx
    · norm_num [finiteCond, finiteProb, heteroResidual, heteroX, heteroY, Fin.sum_univ_succ]
    have he : x = 1 := hx
    subst x
    norm_num [finiteCond, finiteProb, heteroResidual, heteroX, heteroY, Fin.sum_univ_succ]
  · intro g
    simp [finiteCov, finiteMean, heteroResidual, heteroX, heteroY, Fin.sum_univ_succ]
    ring
  · intro x hx
    rcases hx with rfl | hx
    · norm_num [wholeFiniteCondVariance, finiteCond, finiteProb,
        heteroResidual, heteroX, heteroY, Fin.sum_univ_succ]
    have he : x = 1 := hx
    subst x
    norm_num [wholeFiniteCondVariance, finiteCond, finiteProb,
      heteroResidual, heteroX, heteroY, Fin.sum_univ_succ]
  · norm_num [wholeFiniteVariance, finiteMean, heteroResidual, heteroX, heteroY, Fin.sum_univ_succ]
  · norm_num [wholeFiniteCondVariance, finiteMean, finiteCond, finiteProb,
      heteroResidual, heteroX, heteroY, Fin.sum_univ_succ]

end SAP.P001d.WH.W2
