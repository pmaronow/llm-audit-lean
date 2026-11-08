import SAP.P009b.WH.W2.Leaves
import AronowAudit.P009.P009_BernoulliCompletion
import AronowAudit.P009.P009_NormalCompletion
import AronowAudit.P009.Wave1.Gap.GLP0091B5

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace SAP.P009b.WH.W2.P.T22_L1

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem mean_const_here {Ω : Type*} [Fintype Ω]
    (P : SAP.P009b.Law Ω) (c : ℝ) : SAP.P009b.mean P (fun _ => c) = c := by
  unfold SAP.P009b.mean
  rw [← Finset.sum_mul, P.total]
  simp

private theorem mean_le_constant_here {Ω : Type*} [Fintype Ω]
    (P : SAP.P009b.Law Ω) (X : Ω → ℝ) (c : ℝ)
    (h : ∀ ω, X ω ≤ c) : SAP.P009b.mean P X ≤ c := by
  calc
    SAP.P009b.mean P X ≤ SAP.P009b.mean P (fun _ => c) := by
      unfold SAP.P009b.mean
      apply Finset.sum_le_sum
      intro ω hω
      exact mul_le_mul_of_nonneg_left (h ω) (P.nonneg ω)
    _ = c := mean_const_here P c

private theorem bit_bounds (b : Bool) : 0 ≤ SAP.P009b.bit b ∧ SAP.P009b.bit b ≤ 1 := by
  cases b <;> simp [SAP.P009b.bit]

private theorem oneSource_bound {n : ℕ} (b : ℕ) (c : Fin n → ℝ) (k : ℝ)
    (hc : ∀ i, |c i| ≤ 2 * k) (i : Fin n) (z : SAP.P009b.Assignment n) :
    |SAP.P009b.oneSourceOutcome b c i z| ≤ 2 * k + 2 := by
  unfold SAP.P009b.oneSourceOutcome
  split_ifs with hs
  · let j : Fin n := ⟨0, by omega⟩
    have hj := bit_bounds (z j)
    have hi := bit_bounds (z i)
    have hprod0 : 0 ≤ SAP.P009b.bit (z j) * SAP.P009b.bit (z i) :=
      mul_nonneg hj.1 hi.1
    have hprod1 : SAP.P009b.bit (z j) * SAP.P009b.bit (z i) ≤ 1 := by
      calc
        SAP.P009b.bit (z j) * SAP.P009b.bit (z i) ≤ 1 * SAP.P009b.bit (z i) :=
          mul_le_mul_of_nonneg_right hj.2 hi.1
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hi.2 (by norm_num)
        _ = 1 := by norm_num
    calc
      |2 * SAP.P009b.bit (z j) * SAP.P009b.bit (z i) + c i|
          ≤ |2 * SAP.P009b.bit (z j) * SAP.P009b.bit (z i)| + |c i| := abs_add_le _ _
      _ = 2 * (SAP.P009b.bit (z j) * SAP.P009b.bit (z i)) + |c i| := by
        rw [abs_of_nonneg (by nlinarith [hprod0])]
        ring
      _ ≤ 2 + |c i| := by nlinarith
      _ ≤ 2 + 2 * k := by nlinarith [hc i]
      _ = 2 * k + 2 := by ring
  · have hi := bit_bounds (z i)
    calc
      |SAP.P009b.bit (z i) + c i| ≤ |SAP.P009b.bit (z i)| + |c i| := abs_add_le _ _
      _ = SAP.P009b.bit (z i) + |c i| := by rw [abs_of_nonneg hi.1]
      _ ≤ 1 + 2 * k := add_le_add (hi.2) (hc i)
      _ ≤ 2 * k + 2 := by linarith

end
end SAP.P009b.WH.W2.P.T22_L1

open SAP.P009b.WH.W2.P.T22_L1

theorem SAP.P009b.WH.W2.T22_L1_proof : SAP.P009b.WH.W2.T22_L1 := by
  classical
  intro n hn E k q s hReg cutoff c hdesign hout
  let K : ℝ := 2 * k + 2
  have hq : 1 ≤ q := by linarith [hReg.2.1]
  have hmoment (i : Fin n) :
      AronowAudit.P009.mean (SAP.P009b.Bridge.toLaw E.design)
        (fun z => Real.rpow |E.outcome i z| q) ≤ Real.rpow k q := by
    rw [← SAP.P009b.Bridge.mean_correspondence]
    exact hReg.2.2.2.2.1 i
  have hmeanAudit (i : Fin n) :
      AronowAudit.P009.mean (SAP.P009b.Bridge.toLaw E.design)
        (fun z => |E.outcome i z|) ≤ k :=
    AronowAudit.P009.BernoulliCompletion.mean_abs_of_moment
      (SAP.P009b.Bridge.toLaw E.design) (fun z => E.outcome i z) k q
      hReg.1 hq (hmoment i)
  have hmean (i : Fin n) : SAP.P009b.mean E.design (fun z => |E.outcome i z|) ≤ k := by
    rw [SAP.P009b.Bridge.mean_correspondence]
    exact hmeanAudit i
  have hdesignLaw : SAP.P009b.Bridge.toLaw E.design = AronowAudit.P009.fairLaw n := by
    rw [hdesign]
    rfl
  have hbaseline (i : Fin n) : |c i| ≤ 2 * k := by
    have hnum := AronowAudit.P009.Wave1.oneSourceFormulas_one_numerator
      n i false (fun z => |E.outcome i z|)
    rw [← hdesignLaw] at hnum
    have hcontrol : (fun z : SAP.P009b.Assignment n =>
        |E.outcome i (Function.update z i false)|) = fun _ => |c i| := by
      funext z
      rw [hout]
      simp [SAP.P009b.oneSourceOutcome, SAP.P009b.bit, Function.update_apply]
    rw [hcontrol, AronowAudit.P009.mean_const] at hnum
    have hpart : AronowAudit.P009.mean (SAP.P009b.Bridge.toLaw E.design)
        (fun z => if z i = false then |E.outcome i z| else 0) ≤
        AronowAudit.P009.mean (SAP.P009b.Bridge.toLaw E.design)
          (fun z => |E.outcome i z|) := by
      unfold AronowAudit.P009.mean
      apply Finset.sum_le_sum
      intro z hz
      apply mul_le_mul_of_nonneg_left _ ((SAP.P009b.Bridge.toLaw E.design).nonneg z)
      by_cases hz' : z i = false <;> simp [hz']
    have hcontrib : (1 / 2 : ℝ) * |c i| ≤ k := by
      rw [hnum] at hpart
      exact hpart.trans (hmeanAudit i)
    nlinarith
  have hKpos : 0 < K := by
    dsimp [K]
    linarith [hReg.1]
  have hKtwo : 2 ≤ K := by
    dsimp [K]
    linarith [hReg.1]
  have hinv : K⁻¹ ≤ (1 / 2 : ℝ) := by
    have hinv' := (inv_le_inv₀ hKpos (by norm_num : (0 : ℝ) < 2)).2 hKtwo
    norm_num at hinv' ⊢
    exact hinv'
  have hbound : ∀ i z, |E.outcome i z| ≤ K := by
    intro i z
    rw [hout]
    exact oneSource_bound cutoff c k hbaseline i z
  have hfair : ∀ i b, SAP.P009b.marginal E i b = 1 / 2 := by
    intro i b
    change AronowAudit.P009.marginal
      (⟨SAP.P009b.Bridge.toLaw E.design, E.outcome⟩ : AronowAudit.P009.Experiment n)
      i b = 1 / 2
    rw [hdesignLaw]
    exact AronowAudit.P009.SparseCompletion.fair_marginal n E.outcome i b
  change SAP.P009b.Regular E K 4 1
  refine ⟨hKpos, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro i
    rw [hfair]
    constructor <;> linarith
  · intro i
    apply mean_le_constant_here E.design _ (Real.rpow K 4)
    intro z
    exact Real.rpow_le_rpow (abs_nonneg _) (hbound i z) (by norm_num)
  · intro i arm
    apply mean_le_constant_here E.design _ (Real.rpow K 1)
    intro z
    exact Real.rpow_le_rpow (abs_nonneg _) (hbound i (Function.update z i arm)) (by norm_num)
