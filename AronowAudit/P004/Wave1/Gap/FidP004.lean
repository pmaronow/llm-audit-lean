import AronowAudit.P004.P004_MCCompletion

namespace AronowAudit.P004.Wave1

open scoped BigOperators Topology Matrix Classical
open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P004 AronowAudit.P004.MCCompletion

noncomputable section

set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

/-- T13(a–b): finite resampling bounds for any assignment probability law. -/
theorem mc_exact_level {N P : ℕ}
    (w : Assignment N → ℝ) (T : Assignment N → ℝ)
    (hwn : ∀ z, 0 ≤ w z) (hw : (∑ z, w z) = 1)
    (hP : 0 < P) (α : ℝ) (hα : 0 < α ∧ α < 1) :
    (∑ draws : Fin (P + 1) → Assignment N,
      (∏ r, w (draws r)) *
        (if mcPlusPvalue T draws ≤ α then (1 : ℝ) else 0)) ≤ α ∧
    (∑ draws : Fin (P + 1) → Assignment N,
      (∏ r, w (draws r)) *
        (if (mcExceedances T draws : ℝ) / (P : ℝ) ≤ α then (1 : ℝ) else 0)) ≤
      ((Int.floor (α * (P : ℝ)) : ℝ) + 1) / ((P : ℝ) + 1) ∧
    ((Int.floor (α * (P : ℝ)) : ℝ) + 1) / ((P : ℝ) + 1) ≤
      α + (1 - α) / ((P : ℝ) + 1) := by
  have hpr : 0 < (P : ℝ) := Nat.cast_pos.mpr hP
  have hmr : 0 < (P : ℝ) + 1 := by positivity
  let t := (Int.floor (α * (P : ℝ)) : ℝ) + 1
  have ht : 0 ≤ t := by
    have hf : 0 ≤ Int.floor (α * (P : ℝ)) :=
      Int.floor_nonneg.mpr (mul_nonneg hα.1.le hpr.le)
    have hfr : (0 : ℝ) ≤ (Int.floor (α * (P : ℝ)) : ℝ) := by
      exact_mod_cast hf
    dsimp [t]
    linarith
  have hfirst := product_rank_bound (Nat.zero_lt_succ P) w hwn hw
    (fun z => |T z|) α hα.1.le
  have hsecond := product_rank_bound (Nat.zero_lt_succ P) w hwn hw
    (fun z => |T z|) (t / ((P : ℝ) + 1)) (div_nonneg ht hmr.le)
  change arrayExpect w (fun d : Fin (P + 1) → Assignment N =>
    if upperP (fun r => |T (d r)|) 0 ≤ α then (1 : ℝ) else 0) ≤ α at hfirst
  change arrayExpect w (fun d : Fin (P + 1) → Assignment N =>
    if upperP (fun r => |T (d r)|) 0 ≤ t / ((P : ℝ) + 1) then (1 : ℝ) else 0) ≤
      t / ((P : ℝ) + 1) at hsecond
  simp_rw [mc_upperP T] at hfirst hsecond
  refine ⟨hfirst, ?_, ?_⟩
  · change arrayExpect w (fun d =>
      if (mcExceedances T d : ℝ) / (P : ℝ) ≤ α then (1 : ℝ) else 0) ≤
        t / ((P : ℝ) + 1)
    apply (arrayExpect_mono w hwn _ _ ?_).trans hsecond
    intro d
    have himp : (mcExceedances T d : ℝ) / (P : ℝ) ≤ α →
        mcPlusPvalue T d ≤ t / ((P : ℝ) + 1) := by
      intro hd
      have hbr : (mcExceedances T d : ℝ) ≤ α * (P : ℝ) :=
        (div_le_iff₀ hpr).mp hd
      have hbi : (mcExceedances T d : ℤ) ≤ Int.floor (α * (P : ℝ)) :=
        Int.le_floor.mpr (by exact_mod_cast hbr)
      have hb : (mcExceedances T d : ℝ) ≤ (Int.floor (α * (P : ℝ)) : ℝ) := by
        exact_mod_cast hbi
      unfold mcPlusPvalue
      apply div_le_div_of_nonneg_right _ hmr.le
      dsimp [t]
      linarith
    split_ifs <;> simp_all
  · have hf := Int.floor_le (α * (P : ℝ))
    apply (div_le_iff₀ hmr).mpr
    have he : (α + (1 - α) / ((P : ℝ) + 1)) * ((P : ℝ) + 1) =
        α * (P : ℝ) + 1 := by
      field_simp
      ring
    rw [he]
    linarith


/-- Partition the numerator using each node's own masses, including zero shells. -/
private theorem supported_shell_identity_full {A : Type*} [Fintype A] {m N : ℕ}
    (a : Fin N → A → ℝ) (shell : Fin N → A → Fin m)
    (δ : Fin N → A → ℝ) (ha : ∀ i x, 0 ≤ a i x) :
    ∀ i, finiteAverage (a i) (δ i) = ∑ k,
      supportedShellMass (a i) shell i k / (∑ x, a i x) *
        ((∑ x, if shell i x = k then a i x * δ i x else 0) /
          supportedShellMass (a i) shell i k) := by
  have hcancel : ∀ i k,
      supportedShellMass (a i) shell i k / (∑ x, a i x) *
        ((∑ x, if shell i x = k then a i x * δ i x else 0) /
          supportedShellMass (a i) shell i k) =
        (∑ x, if shell i x = k then a i x * δ i x else 0) / (∑ x, a i x) := by
    intro i k
    by_cases h : supportedShellMass (a i) shell i k = 0
    · have hz := shell_zero_numerator (a i) (δ i) (shell i) k (ha i) h
      simp [h, hz]
    · field_simp
  intro i
  simp_rw [hcancel]
  rw [← Finset.sum_div, shell_partition_sum]
  rfl

/-- T15(b–c): positive-shell and common-weight identities for node-specific masses. -/
theorem supported_shell_identity {A : Type*} [Fintype A] {m N : ℕ}
    (a : Fin N → A → ℝ) (shell : Fin N → A → Fin m)
    (δ : Fin N → A → ℝ)
    (ha : ∀ i x, 0 ≤ a i x) (hpos : ∀ i, 0 < ∑ x, a i x) :
    (∀ i, finiteAverage (a i) (δ i) =
      ∑ k ∈ Finset.univ.filter (fun k => 0 < supportedShellMass (a i) shell i k),
        supportedShellMass (a i) shell i k / (∑ x, a i x) *
          ((∑ x, if shell i x = k then a i x * δ i x else 0) /
            supportedShellMass (a i) shell i k)) ∧
    (∀ w : Fin m → ℝ,
      (∀ i k, supportedShellMass (a i) shell i k / (∑ x, a i x) = w k) →
      (∑ i, finiteAverage (a i) (δ i)) / (N : ℝ) =
        ∑ k, w k *
          ((∑ i, (∑ x, if shell i x = k then a i x * δ i x else 0) /
            supportedShellMass (a i) shell i k) / (N : ℝ))) := by
  constructor
  · intro i
    exact (AronowAudit.P004.shell_mass_identity (a i) shell δ (ha i) (hpos i)).1 i
  · intro w hw
    simp_rw [supported_shell_identity_full a shell δ ha, hw]
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.mul_sum, mul_div_assoc]

/-- An alias for the node-specific shell identities. -/
theorem shell_mass_identity {A : Type*} [Fintype A] {m N : ℕ}
    (a : Fin N → A → ℝ) (shell : Fin N → A → Fin m)
    (δ : Fin N → A → ℝ)
    (ha : ∀ i x, 0 ≤ a i x) (hpos : ∀ i, 0 < ∑ x, a i x) :
    (∀ i, finiteAverage (a i) (δ i) =
      ∑ k ∈ Finset.univ.filter (fun k => 0 < supportedShellMass (a i) shell i k),
        supportedShellMass (a i) shell i k / (∑ x, a i x) *
          ((∑ x, if shell i x = k then a i x * δ i x else 0) /
            supportedShellMass (a i) shell i k)) ∧
    (∀ w : Fin m → ℝ,
      (∀ i k, supportedShellMass (a i) shell i k / (∑ x, a i x) = w k) →
      (∑ i, finiteAverage (a i) (δ i)) / (N : ℝ) =
        ∑ k, w k *
          ((∑ i, (∑ x, if shell i x = k then a i x * δ i x else 0) /
            supportedShellMass (a i) shell i k) / (N : ℝ))) := by
  exact supported_shell_identity a shell δ ha hpos

end
end AronowAudit.P004.Wave1
