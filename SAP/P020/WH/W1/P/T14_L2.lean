import SAP.P020.WH.W1.Leaves
import Mathlib
import AronowAudit.P020.P020_Design
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
namespace SAP.P020.WH.W1.P.T14_L2
open SAP.P020.WH.W1
open SAP.P020
noncomputable section
private theorem arm_deriv_formula (P : ClusterPopulation) (a : Bool) (k : ℝ) : deriv (W1ArmVariance P a) k = 2 * k * W1SizeVariance P - 2 * W1SizeCovariance P a := by
  have hf : W1ArmVariance P a = fun x => clusterVariance (if a then P.y1 else P.y0) + x^2 * W1SizeVariance P - 2 * x * W1SizeCovariance P a := by
    funext x
    exact (arm_expansion P a x).2.2
  have hp : HasDerivAt (fun x : ℝ => clusterVariance (if a then P.y1 else P.y0) + x^2 * W1SizeVariance P - 2 * x * W1SizeCovariance P a)
      (2 * k * W1SizeVariance P - 2 * W1SizeCovariance P a) k := by
    convert (((hasDerivAt_const k (clusterVariance (if a then P.y1 else P.y0))).add
      (((hasDerivAt_id k).pow 2).const_mul (W1SizeVariance P))).sub
        ((hasDerivAt_id k).const_mul (2 * W1SizeCovariance P a))) using 1
    · ext x
      simp
      ring
    · simp only [id_eq]
      ring
  calc
    deriv (W1ArmVariance P a) k = deriv (fun x => clusterVariance (if a then P.y1 else P.y0) + x^2 * W1SizeVariance P - 2 * x * W1SizeCovariance P a) k := congrArg (fun f : ℝ → ℝ => deriv f k) hf
    _ = _ := hp.deriv
private theorem common_deriv_formula (P : ClusterPopulation) (k : ℝ) : deriv (rajMomentObjective P) k = 2 * (W1c P + W1t P + 2) * k * W1SizeVariance P - 2 * ((W1c P + 1) * W1SizeCovariance P false + (W1t P + 1) * W1SizeCovariance P true) := by
  let s := W1SizeVariance P
  let q0 := W1SizeCovariance P false
  let q1 := W1SizeCovariance P true
  let c := W1c P
  let t := W1t P
  have hf : rajMomentObjective P = fun x => (c + t + 2) * s * x^2 - 2 * ((c + 1) * q0 + (t + 1) * q1) * x + (c * clusterVariance P.y0 + t * clusterVariance P.y1 + 2 * clusterCovariance P.y0 P.y1) := by
    funext x
    have hx := objective_expansion P x
    rw [hx.2]
    dsimp [s, q0, q1, c, t, W1SizeVariance, W1SizeCovariance]
    ring
  have hp : HasDerivAt (fun x : ℝ => (c + t + 2) * s * x^2 - 2 * ((c + 1) * q0 + (t + 1) * q1) * x + (c * clusterVariance P.y0 + t * clusterVariance P.y1 + 2 * clusterCovariance P.y0 P.y1))
      (2 * (c + t + 2) * s * k - 2 * ((c + 1) * q0 + (t + 1) * q1)) k := by
    convert (((hasDerivAt_id k).pow 2).const_mul ((c + t + 2) * s) |>.sub
      ((hasDerivAt_id k).const_mul (2 * ((c + 1) * q0 + (t + 1) * q1)))).add
      (hasDerivAt_const k
        (c * clusterVariance P.y0 + t * clusterVariance P.y1 + 2 * clusterCovariance P.y0 P.y1)) using 1
    · ext x
      simp
    · simp only [id_eq]
      ring
  calc
    deriv (rajMomentObjective P) k = deriv (fun x => (c + t + 2) * s * x^2 - 2 * ((c + 1) * q0 + (t + 1) * q1) * x + (c * clusterVariance P.y0 + t * clusterVariance P.y1 + 2 * clusterCovariance P.y0 P.y1)) k := congrArg (fun f : ℝ → ℝ => deriv f k) hf
    _ = _ := by
      have hh := hp.deriv
      dsimp [s, q0, q1, c, t] at hh ⊢
      linarith
theorem T14_L2_helper : SAP.P020.WH.W1.T14_L2 := by
  intro P hguard
  let s : ℝ := W1SizeVariance P
  let q0 : ℝ := W1SizeCovariance P false
  let q1 : ℝ := W1SizeCovariance P true
  let c : ℝ := W1c P
  let t : ℝ := W1t P
  let mc : ℝ := controlCount P
  let mt : ℝ := P.mt
  let M : ℝ := P.M
  let κ : ℝ := optimalCoefficient P
  have hs_nonneg : 0 ≤ s := by
    dsimp [s, W1SizeVariance, W1Sizes]
    exact AronowAudit.P020.clusterVariance_nonneg _
  have hs : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := le_antisymm (not_lt.mp hn) hs_nonneg
    exact hguard (by simpa [s] using hs0)
  have hmcNat : 0 < controlCount P := Nat.sub_pos_of_lt P.mt_lt
  have hMNat : 0 < P.M := lt_trans P.mt_pos P.mt_lt
  have hmc : 0 < mc := by dsimp [mc]; exact_mod_cast hmcNat
  have hmt : 0 < mt := by dsimp [mt]; exact_mod_cast P.mt_pos
  have hM : 0 < M := by dsimp [M]; exact_mod_cast hMNat
  have hN : 0 < (populationSize P : ℝ) := by
    exact_mod_cast AronowAudit.P020.populationSize_pos (SAP.P020.Bridge.toPopulation P)
  have hM2 : 2 ≤ P.M := by
    exact le_trans (Nat.succ_le_succ (Nat.succ_le_of_lt P.mt_pos))
      (Nat.succ_le_iff.mpr P.mt_lt)
  have hM1Nat : 1 < P.M := by omega
  have hM1 : 1 < M := by
    change (1 : ℝ) < (P.M : ℝ)
    exact_mod_cast hM1Nat
  have hcountNat : controlCount P + P.mt = P.M := by
    dsimp [controlCount]
    exact Nat.sub_add_cancel (Nat.le_of_lt P.mt_lt)
  have hcount : mc + mt = M := by
    dsimp [mc, mt, M]
    exact_mod_cast hcountNat
  have hcm : (P.M : ℝ) - mc = mt := by
    change M - mc = mt
    linarith [hcount]
  have hct : (P.M : ℝ) - mt = mc := by
    change M - mt = mc
    linarith [hcount]
  have hsizevar : 0 < clusterVariance (fun j => (P.n j : ℝ)) := by
    change 0 < s
    exact hs
  have hv : 0 < W1v P := by
    unfold W1v
    positivity
  have hc : 0 < c := by
    dsimp [c, W1c]
    rw [hcm]
    exact div_pos hmt hmc
  have ht : 0 < t := by
    dsimp [t, W1t]
    rw [hct]
    exact div_pos hmc hmt
  have hct2 : 0 < c + t + 2 := by linarith
  have hden : s ≠ 0 := ne_of_gt hs
  have hmc0 : mc ≠ 0 := ne_of_gt hmc
  have hmt0 : mt ≠ 0 := ne_of_gt hmt
  have hM0 : M ≠ 0 := ne_of_gt hM
  have hcform : c = mt / mc := by
    dsimp [c, W1c, mc, mt]
    rw [hcm]
  have htform : t = mc / mt := by
    dsimp [t, W1t, mc, mt]
    rw [hct]
  have hcplus : c + 1 = M / mc := by
    rw [hcform]
    field_simp [hmc0, hM0]
    nlinarith [hcount]
  have htplus : t + 1 = M / mt := by
    rw [htform]
    field_simp [hmt0, hM0]
    nlinarith [hcount]
  have hcoeff : c + t + 2 = M / mc + M / mt := by
    rw [← hcplus, ← htplus]
    ring
  have hq0 : q0 = clusterCovariance (fun j => (P.n j : ℝ)) P.y0 := by
    rfl
  have hq1 : q1 = clusterCovariance (fun j => (P.n j : ℝ)) P.y1 := by
    rfl
  have hk0 : armOptimalCoefficient P false = q0 / s := by
    dsimp [q0, s, W1SizeCovariance, W1SizeVariance, W1Sizes,
      AronowAudit.P020.armOptimalCoefficient]
    rfl
  have hk1 : armOptimalCoefficient P true = q1 / s := by
    dsimp [q1, s, W1SizeCovariance, W1SizeVariance, W1Sizes,
      AronowAudit.P020.armOptimalCoefficient]
    rfl
  have hκdef : κ = mt / M * (q0 / s) + mc / M * (q1 / s) := by
    dsimp [κ, optimalCoefficient, mc, mt, M]
    rw [hk0, hk1]
  have hroot : (c + t + 2) * κ * s = (c + 1) * q0 + (t + 1) * q1 := by
    rw [hcoeff, hcplus, htplus, hκdef, ← hcount]
    field_simp [hmc0, hmt0, hden]
    <;> ring
  have hstationary_root :
      deriv (rajMomentObjective P) κ = 0 := by
    rw [common_deriv_formula]
    nlinarith [hroot]
  have hstationary_formula :
      2 * (c + t + 2) * κ * s - 2 * ((c + 1) * q0 + (t + 1) * q1) = 0 := by
    rw [common_deriv_formula] at hstationary_root
    exact hstationary_root
  have hApos : 0 < 2 * (c + t + 2) * s := by positivity
  change 0 < s ∧ 0 < W1v P ∧ 0 < c + t + 2 ∧ (∀ a : Bool, 0 < 2 * s ∧ ∀ k : ℝ,
      (deriv (W1ArmVariance P a) k = 0 ↔ k = armOptimalCoefficient P a)) ∧
    (∀ k : ℝ, deriv (rajMomentObjective P) k = 0 ↔ k = κ) ∧
    0 < 2 * (c + t + 2) * s ∧
    0 = c * (2 * κ * s - 2 * q0) + t * (2 * κ * s - 2 * q1) +
      2 * (-q0 - q1 + 2 * κ * s) ∧
    c * κ * s + t * κ * s + 2 * κ * s = c * q0 + t * q1 + q0 + q1 ∧
    (c + t + 2) * κ * s = (c + 1) * q0 + (t + 1) * q1 ∧
    ((M - mc) / mc + (M - mt) / mt + mc / mc + mt / mt) * κ * s =
      ((M - mc) / mc + mc / mc) * q0 + ((M - mt) / mt + mt / mt) * q1 ∧
    (M / mc + M / mt) * κ * s = (M / mc) * q0 + (M / mt) * q1 ∧
    κ = (1 / mc + 1 / mt)⁻¹ * ((1 / mc) * (q0 / s) + (1 / mt) * (q1 / s)) ∧
    κ = (1 / mc + 1 / mt)⁻¹ *
      (armOptimalCoefficient P false / mc + armOptimalCoefficient P true / mt) ∧
    κ = mt / M * armOptimalCoefficient P false + mc / M * armOptimalCoefficient P true ∧
    (∀ k : ℝ, rajMomentObjective P κ ≤ rajMomentObjective P k ∧
      (rajMomentObjective P κ = rajMomentObjective P k ↔ k = κ))
  refine ⟨hs, hv, hct2, ?_, ?_, hApos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    constructor
    · linarith
    · intro k
      rw [arm_deriv_formula]
      cases a with
      | true =>
        constructor
        · intro hh
          rw [hk1]
          have hmul : k * s = q1 := by nlinarith
          field_simp [hden]
          exact hmul
        · intro hh
          rw [hk1] at hh
          rw [hh]
          field_simp [hden]
          simp only [q1, s]
          ring
      | false =>
        constructor
        · intro hh
          rw [hk0]
          have hmul : k * s = q0 := by nlinarith
          field_simp [hden]
          exact hmul
        · intro hh
          rw [hk0] at hh
          rw [hh]
          field_simp [hden]
          simp only [q0, s]
          ring
  · intro k
    rw [common_deriv_formula]
    constructor
    · intro hk
      have hk' : 2 * (c + t + 2) * k * s =
          2 * ((c + 1) * q0 + (t + 1) * q1) := by
        change 2 * (c + t + 2) * k * s -
          2 * ((c + 1) * q0 + (t + 1) * q1) = 0 at hk
        linarith
      have hfactor : (c + t + 2) * s ≠ 0 :=
        mul_ne_zero (ne_of_gt hct2) hden
      have heq : ((c + t + 2) * s) * k = ((c + t + 2) * s) * κ := by
        nlinarith [hk', hroot]
      exact mul_left_cancel₀ hfactor (by nlinarith [heq])
    · intro hk
      rw [hk]
      exact hstationary_formula
  · nlinarith [hroot]
  · nlinarith [hroot]
  · exact hroot
  · have hroot' := hroot
    rw [hcform, htform] at hroot'
    rw [hcm, hct, div_self hmc0, div_self hmt0]
    convert hroot' using 1 <;> ring
  · rw [hcoeff] at hroot
    rw [hcplus, htplus] at hroot
    exact hroot
  · rw [hκdef]
    rw [← hcount]
    field_simp [hmc0, hmt0, hden]
    <;> ring
  · rw [hκdef, hk0, hk1]
    rw [← hcount]
    field_simp [hmc0, hmt0, hden]
    <;> ring
  · rw [hκdef, hk0, hk1]
  · intro k
    have hmin0 := AronowAudit.P020.optimal_raj_variance
      (SAP.P020.Bridge.toPopulation P) hsizevar k
    have hκbridge : AronowAudit.P020.optimalCoefficient
        (SAP.P020.Bridge.toPopulation P) = κ := by
      rfl
    simp only [SAP.P020.Bridge.toPopulation] at hκbridge
    have hdesκ := SAP.P020.Bridge.desRaj_eq P κ
    have hdesk := SAP.P020.Bridge.desRaj_eq P k
    have hlaw := SAP.P020.Bridge.clusterLaw_eq P
    simp only [SAP.P020.Bridge.toPopulation] at hdesκ hdesk hlaw
    have hmin : designVariance (clusterLaw P) (desRaj P κ) ≤
        designVariance (clusterLaw P) (desRaj P k) ∧
        (designVariance (clusterLaw P) (desRaj P κ) =
          designVariance (clusterLaw P) (desRaj P k) ↔ k = κ) := by
      have hminLe := hmin0.1
      have hminEq := hmin0.2.1
      simp only [SAP.P020.Bridge.toPopulation] at hminLe hminEq
      rw [hκbridge, hdesκ, hdesk, hlaw,
        SAP.P020.Bridge.variance_eq] at hminLe hminEq
      exact ⟨hminLe, hminEq⟩
    have hscaleκ := (objective_expansion P κ).1
    have hscalek := (objective_expansion P k).1
    constructor
    · have := mul_le_mul_of_nonneg_left hmin.1 (le_of_lt hv)
      rw [hscaleκ, hscalek] at this
      exact this
    · constructor
      · intro heq
        have hmul : W1v P * designVariance (clusterLaw P) (desRaj P κ) =
            W1v P * designVariance (clusterLaw P) (desRaj P k) := by
          rw [hscaleκ, hscalek]
          exact heq
        have hvar : designVariance (clusterLaw P) (desRaj P κ) =
            designVariance (clusterLaw P) (desRaj P k) :=
          mul_left_cancel₀ (ne_of_gt hv) hmul
        exact hmin.2.mp hvar
      · intro hk
        have hvar : designVariance (clusterLaw P) (desRaj P κ) =
            designVariance (clusterLaw P) (desRaj P k) := hmin.2.mpr hk
        have hmul := congrArg (fun x : ℝ => W1v P * x) hvar
        rw [hscaleκ, hscalek] at hmul
        exact hmul
end
end SAP.P020.WH.W1.P.T14_L2
theorem SAP.P020.WH.W1.T14_L2_proof : SAP.P020.WH.W1.T14_L2 :=
  SAP.P020.WH.W1.P.T14_L2.T14_L2_helper
