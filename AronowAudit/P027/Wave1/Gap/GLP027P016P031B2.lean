import AronowAudit.P027.P027_Audit
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import AronowAudit.External.Causalean.Stat.CLT.ChiSquaredProjection
import Mathlib.MeasureTheory.Integral.Pi

namespace AronowAudit.P027.Wave1

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

/-! The finite linear algebra used by the deterministic contrast. -/

def tdc_sumMap (I : Type) [Fintype I] : (I → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, v i
  map_add' v w := Finset.sum_add_distrib
  map_smul' c v := by simp [← Finset.mul_sum]

lemma tdc_sumMap_surjective {I : Type} [Fintype I] (i : I) :
    Function.Surjective (tdc_sumMap I) := by
  intro x
  refine ⟨Pi.single i x, ?_⟩
  simp [tdc_sumMap]

lemma tdc_sumKernel_rank {I : Type} [Fintype I] (i : I) :
    Module.finrank ℝ (LinearMap.ker (tdc_sumMap I)) = Fintype.card I - 1 := by
  have h := (tdc_sumMap I).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (tdc_sumMap_surjective i),
    finrank_top, Module.finrank_self, Module.finrank_pi] at h
  omega

def tdc_groupMap (r m : ℕ) :
    ((Σ _ : Fin r × Fin 2, Fin m) → ℝ) →ₗ[ℝ] ((Fin r × Fin 2) → ℝ) where
  toFun v g := ∑ j, v ⟨g,j⟩
  map_add' v w := by ext g; exact Finset.sum_add_distrib
  map_smul' c v := by ext g; simp [← Finset.mul_sum]

lemma tdc_groupMap_surjective (r m : ℕ) (hm : 0 < m) :
    Function.Surjective (tdc_groupMap r m) := by
  intro x
  refine ⟨fun k => if k.2 = ⟨0,hm⟩ then x k.1 else 0, ?_⟩
  ext g
  simp [tdc_groupMap]

lemma tdc_centered_rank (r m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    Module.finrank ℝ (phaseCenteredSpace r m) = m*(2*r)-1 := by
  have he : phaseCenteredSpace r m =
      LinearMap.ker (tdc_sumMap (Σ _ : Fin r × Fin 2, Fin m)) := rfl
  rw [he, tdc_sumKernel_rank (⟨(⟨0,hr⟩,0),⟨0,hm⟩⟩ : Σ _ : Fin r × Fin 2, Fin m)]
  simp [Fintype.card_sigma, Nat.mul_comm, Nat.mul_left_comm]

lemma tdc_within_rank (r m : ℕ) (hm : 0 < m) :
    Module.finrank ℝ (phaseWithinSpace r m) = m*(2*r)-2*r := by
  have he : phaseWithinSpace r m = LinearMap.ker (tdc_groupMap r m) := by
    ext v; simp [phaseWithinSpace, LinearMap.mem_ker, tdc_groupMap, funext_iff]
  have h := (tdc_groupMap r m).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (tdc_groupMap_surjective r m hm),
    finrank_top, Module.finrank_pi, Module.finrank_pi] at h
  rw [he]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] at h
  have heq : r*2*m = m*(2*r) := by ring
  rw [heq, Nat.mul_comm r 2] at h
  omega

lemma tdc_signal_rank (r m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    Module.finrank ℝ (phaseSignalSpace r m) = 1 := by
  apply finrank_span_singleton
  intro h
  have hh := congrFun h (⟨(⟨0,hr⟩,0),⟨0,hm⟩⟩ : Σ _ : Fin r × Fin 2, Fin m)
  norm_num [phaseSize] at hh

def tdc_parityLift (r m : ℕ) (b : Fin 2) (v : Fin r → ℝ) :
    (Σ _ : Fin r × Fin 2, Fin m) → ℝ :=
  fun k => if k.1.2 = b then v k.1.1 else 0

lemma tdc_parityLift_sum (r m : ℕ) (b : Fin 2) (v : Fin r → ℝ) :
    (∑ k, tdc_parityLift r m b v k) = (m:ℝ) * ∑ i, v i := by
  fin_cases b <;>
    simp [tdc_parityLift, Fintype.sum_sigma, Fintype.sum_prod_type,
      Fin.sum_univ_two, ← Finset.mul_sum]

def tdc_parityEquiv (r m : ℕ) (hm : 0 < m) (high : Bool) :
    LinearMap.ker (tdc_sumMap (Fin r)) ≃ₗ[ℝ] phaseParitySpace r m high where
  toFun v := ⟨tdc_parityLift r m (if high then 1 else 0) v, by
    refine ⟨?_, ?_, ?_⟩
    · intro g i j; rfl
    · intro k hk
      cases high <;> simp_all [tdc_parityLift]
    · rw [tdc_parityLift_sum]
      have hv : (∑ i, v.val i) = 0 := v.property
      rw [hv, mul_zero]⟩
  invFun v := ⟨fun i => v.val ⟨(i,if high then 1 else 0),⟨0,hm⟩⟩, by
    have hv : (v : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) =
        tdc_parityLift r m (if high then 1 else 0)
          (fun i => v.val ⟨(i,if high then 1 else 0),⟨0,hm⟩⟩) := by
      funext k
      obtain ⟨⟨i,b⟩,j⟩ := k
      have hc := v.property.1 (i,b) j ⟨0,hm⟩
      have hs := v.property.2.1
      cases high <;> fin_cases b <;>
        simp_all [tdc_parityLift]
    have hz := v.property.2.2
    rw [hv, tdc_parityLift_sum] at hz
    have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    exact (mul_eq_zero.mp hz).resolve_left hmR⟩
  left_inv v := by ext i; simp [tdc_parityLift]
  right_inv v := by
    apply Subtype.ext
    funext k
    obtain ⟨⟨i,b⟩,j⟩ := k
    have hc := v.property.1 (i,b) j ⟨0,hm⟩
    have hs := v.property.2.1
    cases high <;> fin_cases b <;> simp_all [tdc_parityLift]
  map_add' v w := by
    apply Subtype.ext
    funext k
    change (if k.1.2 = (if high then 1 else 0) then _ else 0) = _
    by_cases hk : k.1.2 = (if high then 1 else 0) <;> simp [tdc_parityLift, hk]
  map_smul' c v := by
    apply Subtype.ext
    funext k
    change (if k.1.2 = (if high then 1 else 0) then _ else 0) = _
    by_cases hk : k.1.2 = (if high then 1 else 0) <;> simp [tdc_parityLift, hk]

lemma tdc_parity_rank (r m : ℕ) (hr : 0 < r) (hm : 0 < m) (high : Bool) :
    Module.finrank ℝ (phaseParitySpace r m high) = r-1 := by
  rw [← (tdc_parityEquiv r m hm high).finrank_eq,
    tdc_sumKernel_rank (⟨0,hr⟩ : Fin r), Fintype.card_fin]

def tdc_mean {r m : ℕ} (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ)
    (g : Fin r × Fin 2) : ℝ := (∑ j, z ⟨g,j⟩)/(m:ℝ)

def tdc_alpha {r m : ℕ} (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) : ℝ :=
  (∑ i : Fin r, tdc_mean z (i,0))/(r:ℝ)

lemma tdc_mean_total {r m : ℕ} (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ)
    (hz : ∑ k, z k = 0) : (∑ g, tdc_mean z g) = 0 := by
  simp only [tdc_mean, ← Finset.sum_div, ← Fintype.sum_sigma, hz, zero_div]

lemma tdc_mean_parity {r m : ℕ} (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (hz : ∑ k, z k = 0) :
    (∑ i, tdc_mean z (i,0)) = (r:ℝ)*tdc_alpha z ∧
    (∑ i, tdc_mean z (i,1)) = -(r:ℝ)*tdc_alpha z := by
  have hrR : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hl : (∑ i, tdc_mean z (i,0)) = (r:ℝ)*tdc_alpha z := by
    dsimp [tdc_alpha]; field_simp
  refine ⟨hl, ?_⟩
  have ht := tdc_mean_total z hz
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib] at ht
  linarith

def tdc_decomposition {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (hz : ∑ k, z k = 0) :
    PhaseDecomposition r m z where
  within k := z k - tdc_mean z k.1
  signal k := if k.1.2 = 0 then tdc_alpha z else -tdc_alpha z
  low k := if k.1.2 = 0 then tdc_mean z k.1 - tdc_alpha z else 0
  high k := if k.1.2 = 0 then 0 else tdc_mean z k.1 + tdc_alpha z
  within_zero g := by
    have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [groupTotal, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, tdc_mean]
    field_simp; ring
  signal_multiple := by
    refine ⟨-tdc_alpha z / 4, ?_⟩
    intro k
    dsimp [phaseSize]
    split <;> ring
  low_constant := by
    refine ⟨fun g => if g.2 = 0 then tdc_mean z g - tdc_alpha z else 0, ?_, ?_, ?_⟩
    · simpa [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_sub_distrib,
        (tdc_mean_parity hr z hz).1] using (sub_self ((r:ℝ)*tdc_alpha z))
    · intro g hg; simp [hg]
    · intro k; rfl
  high_constant := by
    refine ⟨fun g => if g.2 = 0 then 0 else tdc_mean z g + tdc_alpha z, ?_, ?_, ?_⟩
    · simp [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib,
        (tdc_mean_parity hr z hz).2]
    · intro g hg; simp [hg]
    · intro k; rfl
  reconstruct k := by split <;> ring

lemma tdc_signal_mem {r m : ℕ} (v : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) :
    v ∈ phaseSignalSpace r m ↔ ∃ b : ℝ, ∀ k, v k = b*(phaseSize k-6) := by
  change v ∈ Submodule.span ℝ {fun k => phaseSize k-6} ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨b,hb⟩; exact ⟨b, fun k => (congrFun hb k).symm⟩
  · rintro ⟨b,hb⟩; exact ⟨b, funext (fun k => (hb k).symm)⟩

lemma tdc_parity_mem_of_data {r m : ℕ} (high : Bool)
    (v : (Fin r × Fin 2) → ℝ) (hv : ∑ g, v g = 0)
    (hs : ∀ g, (if high then g.2 = 0 else g.2 ≠ 0) → v g = 0) :
    (fun k : Σ _ : Fin r × Fin 2, Fin m => v k.1) ∈ phaseParitySpace r m high := by
  refine ⟨fun _ _ _ => rfl, fun k hk => hs k.1 hk, ?_⟩
  simp [Fintype.sum_sigma, ← Finset.mul_sum, hv]

def tdc_parts {r m : ℕ} {z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ}
    (d : PhaseDecomposition r m z) : Fin 4 → (Σ _ : Fin r × Fin 2, Fin m) → ℝ :=
  ![d.within, d.signal, d.low, d.high]

lemma tdc_parts_mem {r m : ℕ} {z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ}
    (d : PhaseDecomposition r m z) (i : Fin 4) :
    tdc_parts d i ∈ phaseComponentSpace r m i := by
  fin_cases i
  · exact d.within_zero
  · exact (tdc_signal_mem d.signal).mpr d.signal_multiple
  · change d.low ∈ phaseParitySpace r m false
    obtain ⟨v,hv,hs,he⟩ := d.low_constant
    have h := tdc_parity_mem_of_data (m := m) false v hv hs
    simpa only [← funext he] using h
  · change d.high ∈ phaseParitySpace r m true
    obtain ⟨v,hv,hs,he⟩ := d.high_constant
    have h := tdc_parity_mem_of_data (m := m) true v hv hs
    simpa only [← funext he] using h

lemma tdc_parts_sum {r m : ℕ} {z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ}
    (d : PhaseDecomposition r m z) (k : Σ _ : Fin r × Fin 2, Fin m) :
    (∑ i, tdc_parts d i k) = z k := by
  simpa [tdc_parts, Fin.sum_univ_succ, add_assoc] using (d.reconstruct k).symm

def tdc_dot {I : Type} [Fintype I] (v w : I → ℝ) : ℝ := ∑ k, v k*w k

lemma tdc_dot_comm {I : Type} [Fintype I] (v w : I → ℝ) :
    tdc_dot v w = tdc_dot w v := by simp [tdc_dot, mul_comm]

lemma tdc_within_dot {r m : ℕ}
    (v w : (Σ _ : Fin r × Fin 2, Fin m) → ℝ)
    (hv : v ∈ phaseWithinSpace r m)
    (hw : ∀ g i j, w ⟨g,i⟩ = w ⟨g,j⟩) : tdc_dot v w = 0 := by
  cases m with
  | zero => simp [tdc_dot]
  | succ m =>
    rw [tdc_dot, Fintype.sum_sigma]
    apply Finset.sum_eq_zero
    intro g _
    simp_rw [hw g _ (0 : Fin (m+1)), ← Finset.sum_mul]
    rw [hv g, zero_mul]

lemma tdc_signal_constant {r m : ℕ}
    {v : (Σ _ : Fin r × Fin 2, Fin m) → ℝ} (hv : v ∈ phaseSignalSpace r m) :
    ∀ g i j, v ⟨g,i⟩ = v ⟨g,j⟩ := by
  obtain ⟨b,hb⟩ := (tdc_signal_mem v).mp hv
  intro g i j
  rw [hb, hb]; rfl

lemma tdc_signal_parity_dot {r m : ℕ} (high : Bool)
    {v w : (Σ _ : Fin r × Fin 2, Fin m) → ℝ}
    (hv : v ∈ phaseSignalSpace r m) (hw : w ∈ phaseParitySpace r m high) :
    tdc_dot v w = 0 := by
  obtain ⟨b,hb⟩ := (tdc_signal_mem v).mp hv
  have he (k : Σ _ : Fin r × Fin 2, Fin m) :
      v k*w k = (if high then 4*b else -4*b)*w k := by
    rw [hb]
    cases high
    · by_cases hk : k.1.2 = 0
      · simp only [phaseSize, if_pos hk, Bool.false_eq_true, ↓reduceIte]; ring
      · have hz := hw.2.1 k hk
        simp [hz]
    · by_cases hk : k.1.2 = 0
      · have hz := hw.2.1 k hk
        simp [hz]
      · change b*((if k.1.2 = 0 then 2 else 10)-6)*w k = 4*b*w k
        rw [if_neg hk]; ring
  simp only [tdc_dot, he, ← Finset.mul_sum, hw.2.2, mul_zero]

lemma tdc_low_high_dot {r m : ℕ}
    {v w : (Σ _ : Fin r × Fin 2, Fin m) → ℝ}
    (hv : v ∈ phaseParitySpace r m false) (hw : w ∈ phaseParitySpace r m true) :
    tdc_dot v w = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k.1.2 = 0
  · rw [hw.2.1 k hk, mul_zero]
  · rw [hv.2.1 k hk, zero_mul]

lemma tdc_component_orthogonal (r m : ℕ)
    (i j : Fin 4) (v w : (Σ _ : Fin r × Fin 2, Fin m) → ℝ)
    (hij : i ≠ j) (hv : v ∈ phaseComponentSpace r m i)
    (hw : w ∈ phaseComponentSpace r m j) : tdc_dot v w = 0 := by
  fin_cases i <;> fin_cases j
  all_goals first | exact False.elim (hij rfl) | skip
  all_goals norm_num [phaseComponentSpace] at hv hw
  all_goals first
    | exact tdc_within_dot v w hv (tdc_signal_constant hw)
    | exact tdc_within_dot v w hv hw.1
    | exact (tdc_dot_comm v w).trans (tdc_within_dot w v hw (tdc_signal_constant hv))
    | exact (tdc_dot_comm v w).trans (tdc_within_dot w v hw hv.1)
    | exact tdc_signal_parity_dot _ hv hw
    | exact (tdc_dot_comm v w).trans (tdc_signal_parity_dot _ hw hv)
    | exact tdc_low_high_dot hv hw
    | exact (tdc_dot_comm v w).trans (tdc_low_high_dot hw hv)

lemma tdc_components_unique (r m : ℕ)
    (v w : Fin 4 → (Σ _ : Fin r × Fin 2, Fin m) → ℝ)
    (hv : ∀ i, v i ∈ phaseComponentSpace r m i)
    (hw : ∀ i, w i ∈ phaseComponentSpace r m i)
    (he : ∀ k, (∑ i, v i k) = ∑ i, w i k) : v = w := by
  let u := fun i k => v i k - w i k
  have hu (i : Fin 4) : u i ∈ phaseComponentSpace r m i :=
    (phaseComponentSpace r m i).sub_mem (hv i) (hw i)
  have hs (k) : (∑ i, u i k) = 0 := by
    dsimp [u]; rw [Finset.sum_sub_distrib, he, sub_self]
  funext i k
  have hd : tdc_dot (u i) (u i) = 0 := by
    calc
      _ = ∑ j, tdc_dot (u i) (u j) := by
        symm
        apply Finset.sum_eq_single i
        · intro j _ hji
          exact tdc_component_orthogonal r m i j _ _ hji.symm (hu i) (hu j)
        · simp
      _ = ∑ k, u i k * (∑ j, u j k) := by
        simp only [tdc_dot, Finset.mul_sum]
        exact Finset.sum_comm
      _ = 0 := by simp only [hs, mul_zero, Finset.sum_const_zero]
  have hz : u i k * u i k = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_self_nonneg (u i k))).mp hd k
      (Finset.mem_univ k)
  have : u i k = 0 := (mul_self_eq_zero.mp hz)
  exact sub_eq_zero.mp this

lemma tdc_decomposition_unique {r m : ℕ} {z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ}
    (d₁ d₂ : PhaseDecomposition r m z) :
    d₁.within = d₂.within ∧ d₁.signal = d₂.signal ∧
      d₁.low = d₂.low ∧ d₁.high = d₂.high := by
  have he := tdc_components_unique r m (tdc_parts d₁) (tdc_parts d₂)
    (tdc_parts_mem d₁) (tdc_parts_mem d₂)
    (fun k => (tdc_parts_sum d₁ k).trans (tdc_parts_sum d₂ k).symm)
  exact ⟨congrFun he 0, congrFun he 1, congrFun he 2, congrFun he 3⟩

lemma tdc_square_parts {r m : ℕ} {z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ}
    (d : PhaseDecomposition r m z) :
    populationSquareNorm z = populationSquareNorm d.within + populationSquareNorm d.signal +
      populationSquareNorm d.low + populationSquareNorm d.high := by
  have hd (i : Fin 4) : (∑ j, tdc_dot (tdc_parts d i) (tdc_parts d j)) =
      populationSquareNorm (tdc_parts d i) := by
    rw [Finset.sum_eq_single i]
    · simp [tdc_dot, populationSquareNorm, pow_two]
    · intro j _ hji
      exact tdc_component_orthogonal r m i j _ _ hji.symm
        (tdc_parts_mem d i) (tdc_parts_mem d j)
    · simp
  calc
    populationSquareNorm z = ∑ k, (∑ i, tdc_parts d i k)*(∑ j, tdc_parts d j k) := by
      simp only [tdc_parts_sum, populationSquareNorm, pow_two]
    _ = ∑ i, ∑ j, tdc_dot (tdc_parts d i) (tdc_parts d j) := by
      simp only [Finset.sum_mul, Finset.mul_sum, tdc_dot]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simpa only [mul_comm] using
        (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
          (f := fun k j => tdc_parts d i k * tdc_parts d j k))
    _ = ∑ i, populationSquareNorm (tdc_parts d i) := by simp_rw [hd]
    _ = _ := by simp [tdc_parts, Fin.sum_univ_succ, add_assoc]

lemma tdc_shift_square {I : Type} [Fintype I] (v : I → ℝ) (c : ℝ)
    (hv : ∑ i, v i = 0) :
    (∑ i, (v i+c)^2) = (∑ i, v i^2)+(Fintype.card I:ℝ)*c^2 := by
  simp_rw [show ∀ x : ℝ, (x+c)^2 = x^2+2*c*x+c^2 by intro x; ring]
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, hv]

lemma tdc_H_formula {r m : ℕ} (hr : 0 < r) (hm : 2 ≤ m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (hz : ∑ k, z k = 0) :
    periodicMeanH hr z =
      (((6*(r:ℝ)-1)*(∑ i : Fin r, (groupTotal (fun _ => m) z (i,0))^2))+
        ((6*(r:ℝ)/5-1)*(∑ i : Fin r, (groupTotal (fun _ => m) z (i,1))^2))) /
          ((m:ℝ)*(2*r))^2 := by
  have hrR : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have h := periodic_mean_identities r m hr hm z hz
  dsimp only at h
  rw [h.2.1, h.1]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, phaseProb,
    Finset.sum_add_distrib]
  simp only [Prod.snd, show (1:Fin 2) ≠ 0 by decide, ↓reduceIte]
  have h0 (x : ℝ) : x / (1/(6*(r:ℝ))) = (6*r)*x := by field_simp
  have h1 (x : ℝ) : x / (5/(6*(r:ℝ))) = (6*r/5)*x := by field_simp
  simp_rw [h0, h1]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

lemma tdc_diagonal {r m : ℕ} (hr : 0 < r) (hm : 2 ≤ m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (hz : ∑ k, z k = 0)
    (d : PhaseDecomposition r m z) :
    periodicContrast hr z = (((m:ℝ)*(2*r)-m)/((m:ℝ)*(2*r))^2) *
      (populationSquareNorm d.within+contrastCoefficient (2*r)*
        (populationSquareNorm d.high-populationSquareNorm d.low)) := by
  obtain ⟨b,hb⟩ := d.signal_multiple
  obtain ⟨L,hL,hLs,hLe⟩ := d.low_constant
  obtain ⟨G,hG,hGs,hGe⟩ := d.high_constant
  have hL1 (i : Fin r) : L (i,1) = 0 := hLs (i,1) (by change (1:Fin 2) ≠ 0; decide)
  have hG0 (i : Fin r) : G (i,0) = 0 := hGs (i,0) rfl
  have hL0 : (∑ i : Fin r, L (i,0)) = 0 := by
    simpa [Fintype.sum_prod_type, Fin.sum_univ_two, hL1] using hL
  have hG1 : (∑ i : Fin r, G (i,1)) = 0 := by
    simpa [Fintype.sum_prod_type, Fin.sum_univ_two, hG0] using hG
  have hQL : populationSquareNorm d.low = (m:ℝ)*∑ i : Fin r, L (i,0)^2 := by
    simp [populationSquareNorm, hLe, Fintype.sum_sigma, Fintype.sum_prod_type,
      Fin.sum_univ_two, hL1, ← Finset.mul_sum]
  have hQG : populationSquareNorm d.high = (m:ℝ)*∑ i : Fin r, G (i,1)^2 := by
    simp [populationSquareNorm, hGe, Fintype.sum_sigma, Fintype.sum_prod_type,
      Fin.sum_univ_two, hG0, ← Finset.mul_sum]
  have hQS : populationSquareNorm d.signal = 32*(m:ℝ)*r*b^2 := by
    simp [populationSquareNorm, hb, phaseSize, Fintype.sum_sigma,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  have hY (g : Fin r × Fin 2) : groupTotal (fun _ => m) z g =
      (m:ℝ)*(b*(phaseSize (⟨g,⟨0,by omega⟩⟩ : Σ _ : Fin r × Fin 2, Fin m)-6)+L g+G g) := by
    simp only [groupTotal, d.reconstruct, Finset.sum_add_distrib, hb, hLe, hGe]
    have hw := d.within_zero g
    change (∑ j, d.within ⟨g,j⟩) = 0 at hw
    change (∑ j : Fin m, d.within ⟨g,j⟩) +
      (∑ _ : Fin m, b*((if g.2 = 0 then 2 else 10)-6)) +
      (∑ _ : Fin m, L g) + (∑ _ : Fin m, G g) = _
    rw [hw]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp only [phaseSize]
    ring
  have hYL : (∑ i : Fin r, (groupTotal (fun _ => m) z (i,0))^2) =
      (m:ℝ)^2*((∑ i : Fin r, L (i,0)^2)+16*r*b^2) := by
    have he (i : Fin r) : groupTotal (fun _ => m) z (i,0) =
        (m:ℝ)*(L (i,0)+(-4*b)) := by
      rw [hY]
      simp only [phaseSize, if_pos rfl, ↓reduceIte, hG0]
      ring
    simp_rw [he, mul_pow, ← Finset.mul_sum]
    rw [tdc_shift_square _ _ hL0]
    simp only [Fintype.card_fin]
    ring
  have hYG : (∑ i : Fin r, (groupTotal (fun _ => m) z (i,1))^2) =
      (m:ℝ)^2*((∑ i : Fin r, G (i,1)^2)+16*r*b^2) := by
    have he (i : Fin r) : groupTotal (fun _ => m) z (i,1) =
        (m:ℝ)*(G (i,1)+(4*b)) := by
      rw [hY]
      simp only [phaseSize, show (1:Fin 2) ≠ 0 by decide, ↓reduceIte, hL1]
      ring
    simp_rw [he, mul_pow, ← Finset.mul_sum]
    rw [tdc_shift_square _ _ hG1]
    simp only [Fintype.card_fin]
    ring
  have hC := (periodic_mean_identities r m hr hm z hz).2.2.2.1
  have hH := tdc_H_formula hr hm z hz
  rw [hYL, hYG] at hH
  have hQ := tdc_square_parts d
  rw [hQS, hQL, hQG] at hQ
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hN : (m:ℝ)*(2*r) ≠ 0 := by positivity
  have hD : 9*(2*(r:ℝ))-5 ≠ 0 := by
    have : (1:ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have ht : periodicContrast hr z =
      (((m:ℝ)*(2*r)-m)*populationSquareNorm z)/((m:ℝ)*(2*r))^2 -
        contrastR (2*r)*periodicMeanH hr z := by
    unfold periodicContrast
    change periodicMeanC hr z-periodicMeanH hr z =
      (((m:ℝ)*(2*r)-m)*populationSquareNorm z)/((m:ℝ)*(2*r))^2 at hC
    rw [show periodicMeanC hr z = _ from (sub_eq_iff_eq_add.mp hC)]
    ring
  rw [ht, hQ, hH, hQL, hQG]
  unfold contrastR contrastCoefficient
  have hD' : -5+(r:ℝ)*18 ≠ 0 := by
    have : (1:ℝ) ≤ r := by exact_mod_cast hr
    linarith
  field_simp [hN,hD,hD',hrR.ne',hmR.ne']
  ring_nf
  field_simp [hD']
  <;> ring

lemma tdc_signal_sum (r m : ℕ) (b : ℝ) :
    (∑ k : Σ _ : Fin r × Fin 2, Fin m, b*(phaseSize k-6)) = 0 := by
  simp [Fintype.sum_sigma, Fintype.sum_prod_type, Fin.sum_univ_two, phaseSize]
  ring

def tdc_shift_decomposition {r m : ℕ} {z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ}
    (d : PhaseDecomposition r m z) (β : ℝ) :
    PhaseDecomposition r m (fun k => β*(phaseSize k-6)+z k) where
  within := d.within
  signal k := β*(phaseSize k-6)+d.signal k
  low := d.low
  high := d.high
  within_zero := d.within_zero
  signal_multiple := by
    obtain ⟨b,hb⟩ := d.signal_multiple
    refine ⟨β+b, ?_⟩
    intro k; rw [hb]; ring
  low_constant := d.low_constant
  high_constant := d.high_constant
  reconstruct k := by rw [d.reconstruct]; ring

lemma tdc_lower_bound {r m : ℕ} (hr : 0 < r) (hm : 2 ≤ m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (hz : ∑ k, z k = 0)
    (d : PhaseDecomposition r m z) :
    -(((m:ℝ)*(2*r)-m)*contrastCoefficient (2*r)/((m:ℝ)*(2*r))^2)*
      populationSquareNorm d.low ≤ periodicContrast hr z := by
  rw [tdc_diagonal hr hm z hz d]
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hmR : (0:ℝ) ≤ m := by positivity
  have hA : 0 ≤ ((m:ℝ)*(2*r)-m)/((m:ℝ)*(2*r))^2 :=
    div_nonneg (by nlinarith) (sq_nonneg _)
  have hc : 0 ≤ contrastCoefficient (2*r) := by
    unfold contrastCoefficient
    apply div_nonneg (by positivity) (by linarith)
  have hW : 0 ≤ populationSquareNorm d.within := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hG : 0 ≤ populationSquareNorm d.high := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h := mul_nonneg hA (add_nonneg hW (mul_nonneg hc hG))
  convert (le_add_of_nonneg_right h :
    -(((m:ℝ)*(2*r)-m)*contrastCoefficient (2*r)/((m:ℝ)*(2*r))^2)*populationSquareNorm d.low ≤
    -(((m:ℝ)*(2*r)-m)*contrastCoefficient (2*r)/((m:ℝ)*(2*r))^2)*populationSquareNorm d.low +
    (((m:ℝ)*(2*r)-m)/((m:ℝ)*(2*r))^2) *
      (populationSquareNorm d.within+contrastCoefficient (2*r)*populationSquareNorm d.high)) using 1 <;> ring

theorem contrast_deterministic_correction_proof (r m : ℕ) (hr : 0 < r) (hm : 2 ≤ m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (hz : ∑ k, z k = 0) :
    Module.finrank ℝ (phaseCenteredSpace r m) = m*(2*r)-1 ∧
    Module.finrank ℝ (phaseWithinSpace r m) = m*(2*r)-2*r ∧
    Module.finrank ℝ (phaseSignalSpace r m) = 1 ∧
    Module.finrank ℝ (phaseParitySpace r m false) = r-1 ∧
    Module.finrank ℝ (phaseParitySpace r m true) = r-1 ∧
    (∀ (i j : Fin 4) (v w : (Σ _ : Fin r × Fin 2, Fin m) → ℝ),
      i ≠ j → v ∈ phaseComponentSpace r m i → w ∈ phaseComponentSpace r m j →
      (∑ k, v k * w k) = 0) ∧
    (Nonempty (PhaseDecomposition r m z)) ∧
    (∀ d₁ d₂ : PhaseDecomposition r m z,
      d₁.within = d₂.within ∧ d₁.signal = d₂.signal ∧
      d₁.low = d₂.low ∧ d₁.high = d₂.high) ∧
    (∀ d : PhaseDecomposition r m z, periodicContrast hr z =
      (((m:ℝ)*(2*r)-m)/((m:ℝ)*(2*r))^2) *
        (populationSquareNorm d.within+contrastCoefficient (2*r)*
          (populationSquareNorm d.high-populationSquareNorm d.low)) ∧
      -(((m:ℝ)*(2*r)-m)*contrastCoefficient (2*r)/((m:ℝ)*(2*r))^2)*
        populationSquareNorm d.low ≤ periodicContrast hr z) ∧
    (∀ β : ℝ, periodicContrast hr (fun k => β*(phaseSize k-6)+z k) =
      periodicContrast hr z) := by
  have hm0 : 0 < m := by omega
  refine ⟨tdc_centered_rank r m hr hm0, tdc_within_rank r m hm0,
    tdc_signal_rank r m hr hm0, tdc_parity_rank r m hr hm0 false,
    tdc_parity_rank r m hr hm0 true, tdc_component_orthogonal r m,
    ⟨tdc_decomposition hr hm0 z hz⟩, tdc_decomposition_unique, ?_, ?_⟩
  · intro d
    exact ⟨tdc_diagonal hr hm z hz d, tdc_lower_bound hr hm z hz d⟩
  · intro β
    let d := tdc_decomposition hr hm0 z hz
    have hz' : (∑ k, (β*(phaseSize k-6)+z k)) = 0 := by
      rw [Finset.sum_add_distrib, tdc_signal_sum, hz, add_zero]
    rw [tdc_diagonal hr hm _ hz' (tdc_shift_decomposition d β),
      tdc_diagonal hr hm z hz d]
    rfl

/-! Gaussian laws are transported through the genuine Euclidean norm. -/

def tgc_equi (I : Type) [Fintype I] : (I → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ I :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).symm.toLinearEquiv

lemma tgc_inner {I : Type} [Fintype I] (v w : I → ℝ) :
    inner ℝ (tgc_equi I v) (tgc_equi I w) = tdc_dot v w := by
  simp [tgc_equi, PiLp.inner_apply, tdc_dot, mul_comm]

lemma tgc_norm_sq {I : Type} [Fintype I] (v : I → ℝ) :
    ‖tgc_equi I v‖^2 = populationSquareNorm v := by
  rw [← real_inner_self_eq_norm_sq, tgc_inner]
  simp [tdc_dot, populationSquareNorm, pow_two]

def tgc_space (r m : ℕ) (i : Fin 4) :
    Submodule ℝ (EuclideanSpace ℝ (Σ _ : Fin r × Fin 2, Fin m)) :=
  (phaseComponentSpace r m i).map (tgc_equi _).toLinearMap

lemma tgc_space_rank (r m : ℕ) (i : Fin 4) :
    Module.finrank ℝ (tgc_space r m i) = Module.finrank ℝ (phaseComponentSpace r m i) :=
  (tgc_equi _).finrank_map_eq _

lemma tgc_space_mem {r m : ℕ} (i : Fin 4)
    (v : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) :
    tgc_equi _ v ∈ tgc_space r m i ↔ v ∈ phaseComponentSpace r m i := by
  simp only [tgc_space, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

lemma tgc_space_orthogonal (r m : ℕ) (i j : Fin 4) (hij : i ≠ j)
    (v w : EuclideanSpace ℝ (Σ _ : Fin r × Fin 2, Fin m))
    (hv : v ∈ tgc_space r m i) (hw : w ∈ tgc_space r m j) :
    inner ℝ v w = 0 := by
  obtain ⟨v,hv,rfl⟩ := hv
  obtain ⟨w,hw,rfl⟩ := hw
  change inner ℝ (tgc_equi _ v) (tgc_equi _ w) = 0
  rw [tgc_inner]
  exact tdc_component_orthogonal r m i j v w hij hv hw

open scoped RealInnerProductSpace in
lemma tgc_chi_eq (d : ℕ) : Causalean.Stat.chiSqDist d = chiSquaredLaw d := by
  unfold Causalean.Stat.chiSqDist Causalean.Mathlib.stdGaussian
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  unfold chiSquaredLaw
  apply Measure.map_congr
  exact ae_of_all _ (fun v => by
    simp only [Function.comp_def, EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply])

lemma tgc_chi_moment (d : ℕ) :
    Integrable (id : ℝ → ℝ) (chiSquaredLaw d) ∧
      (∫ x : ℝ, x ∂chiSquaredLaw d) = (d:ℝ) := by
  let ν : Measure (Fin d → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  let S : (Fin d → ℝ) → ℝ := fun v => ∑ i, v i^2
  have hS : Measurable S := by dsimp [S]; fun_prop
  have hLp : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have hsq : Integrable (fun x : ℝ => x^2) (gaussianReal 0 1) := hLp.integrable_sq
  have hsecond : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_eq_sub hLp
    simp only [Pi.pow_apply, id_eq] at h
    rw [variance_id_gaussianReal, integral_id_gaussianReal] at h
    simpa using h.symm
  have hcoord (i : Fin d) : Integrable (fun v : Fin d → ℝ => v i^2) ν :=
    integrable_comp_eval (μ := fun _ : Fin d => gaussianReal 0 1) (i := i) hsq
  have hInt : Integrable S ν := integrable_finsetSum Finset.univ (fun i _ => hcoord i)
  refine ⟨(integrable_map_measure aestronglyMeasurable_id hS.aemeasurable).mpr hInt, ?_⟩
  change (∫ x : ℝ, x ∂ν.map S) = _
  rw [integral_map (f := fun x : ℝ => x) hS.aemeasurable (by fun_prop)]
  change (∫ v, ∑ i, v i^2 ∂ν) = _
  rw [integral_finsetSum Finset.univ (fun i _ => hcoord i)]
  simp only [ν, integral_comp_eval (μ := fun _ : Fin d => gaussianReal 0 1) hsq.aestronglyMeasurable, hsecond,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma tgc_projection_laws {Ξ E : Type} [MeasurableSpace Ξ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (Z : Ξ → E) (hZm : AEMeasurable Z μ)
    (hZ : μ.map Z = ProbabilityTheory.stdGaussian E) (U : Fin 3 → Submodule ℝ E)
    (hU : ∀ i j, i ≠ j → ∀ v ∈ U i, ∀ w ∈ U j, inner ℝ v w = 0) :
    iIndepFun (fun i ξ => ‖(U i).starProjection (Z ξ)‖^2) μ ∧
    ∀ i, μ.map (fun ξ => ‖(U i).starProjection (Z ξ)‖^2) =
      chiSquaredLaw (Module.finrank ℝ (U i)) := by
  have hGauss : HasGaussianLaw Z μ := ⟨hZm, by rw [hZ]; infer_instance⟩
  let P : E →L[ℝ] (Fin 3 → E) := ContinuousLinearMap.pi (fun i => (U i).starProjection)
  have hjoint : HasGaussianLaw (fun ξ i => (U i).starProjection (Z ξ)) μ :=
    hGauss.map P
  have hind : iIndepFun (fun i ξ => (U i).starProjection (Z ξ)) μ := by
    apply hjoint.iIndepFun_of_covariance_inner
    intro i j hij x y
    simp_rw [← Submodule.inner_starProjection_left_eq_right]
    have hc := covariance_map (μ := μ)
      (X := fun v : E => inner ℝ ((U i).starProjection x) v)
      (Y := fun v : E => inner ℝ ((U j).starProjection y) v)
      (by fun_prop) (by fun_prop) hZm
    rw [hZ] at hc
    simp only [Function.comp_def] at hc
    rw [← hc, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian]
    exact hU i j hij _ ((U i).starProjection_apply_mem x) _
      ((U j).starProjection_apply_mem y)
  refine ⟨hind.comp (fun _ v => ‖v‖^2) (by fun_prop), ?_⟩
  intro i
  change μ.map ((fun v : E => ‖(U i).starProjection v‖^2) ∘ Z) = _
  rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hZm, hZ]
  have h := Causalean.Stat.stdGaussian_map_normSq_orthogonalProjection
    ((U i).starProjection) (isSelfAdjoint_starProjection _)
    ((U i).isIdempotentElem_starProjection)
  rw [Submodule.range_starProjection, tgc_chi_eq] at h
  exact h

lemma tgc_standardize {Ξ I : Type} [Fintype I] [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (ε : I → Ξ → ℝ)
    (σ2 : ℝ) (hσ : 0 < σ2) (hε : GaussianNoise μ ε σ2) :
    AEMeasurable (fun ξ => tgc_equi I (fun i => ε i ξ / Real.sqrt σ2)) μ ∧
    μ.map (fun ξ => tgc_equi I (fun i => ε i ξ / Real.sqrt σ2)) =
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ I) := by
  let Y : I → Ξ → ℝ := fun i ξ => ε i ξ / Real.sqrt σ2
  have hYm (i : I) : AEMeasurable (Y i) μ := (hε.1 i).1.div_const _
  have hYi (i : I) : μ.map (Y i) = gaussianReal 0 1 := by
    change μ.map ((fun x : ℝ => x / Real.sqrt σ2) ∘ ε i) = _
    rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) (hε.1 i).1,
      (hε.1 i).2, gaussianReal_map_div_const]
    congr 1
    · simp
    · apply NNReal.eq
      simp only [NNReal.coe_div, Real.coe_toNNReal σ2 hσ.le,
        Real.sq_sqrt hσ.le, NNReal.coe_mk, NNReal.coe_one]
      exact div_self hσ.ne'
  have hInd : iIndepFun Y μ := hε.2.comp (fun _ x => x / Real.sqrt σ2) (by fun_prop)
  have hY : μ.map (fun ξ i => Y i ξ) = Measure.pi (fun _ : I => gaussianReal 0 1) := by
    rw [hInd.map_fun_eq_pi_map hYm]
    simp only [hYi]
  have hmeas : AEMeasurable (fun ξ i => Y i ξ) μ := AEMeasurable.of_eval hYm
  have hE : Measurable (tgc_equi I) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).symm.continuous.measurable
  refine ⟨hE.comp_aemeasurable hmeas, ?_⟩
  change μ.map ((tgc_equi I) ∘ (fun ξ i => Y i ξ)) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hE.aemeasurable hmeas, hY]
  exact map_pi_eq_stdGaussian

lemma tgc_component_centered {r m : ℕ} (i : Fin 4)
    (v : (Σ _ : Fin r × Fin 2, Fin m) → ℝ)
    (hv : v ∈ phaseComponentSpace r m i) : (∑ k, v k) = 0 := by
  fin_cases i
  · change ∀ g, (∑ j, v ⟨g,j⟩) = 0 at hv
    simp only [Fintype.sum_sigma, hv, Finset.sum_const_zero]
  · change v ∈ phaseSignalSpace r m at hv
    obtain ⟨b,hb⟩ := (tdc_signal_mem v).mp hv
    simp_rw [hb]
    exact tdc_signal_sum r m b
  · exact hv.2.2
  · exact hv.2.2

lemma tgc_project_part {r m : ℕ} {z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ}
    (d : PhaseDecomposition r m z) (i : Fin 4) :
    (tgc_space r m i).starProjection (tgc_equi _ z) = tgc_equi _ (tdc_parts d i) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((tgc_space_mem i _).mpr (tdc_parts_mem d i))
  intro w hw
  obtain ⟨v,hv,rfl⟩ := hw
  change inner ℝ (tgc_equi _ z - tgc_equi _ (tdc_parts d i)) (tgc_equi _ v) = 0
  rw [inner_sub_left, tgc_inner, tgc_inner]
  have he : tdc_dot z v = ∑ j, tdc_dot (tdc_parts d j) v := by
    calc
      _ = ∑ k, (∑ j, tdc_parts d j k)*v k := by simp [tdc_dot, tdc_parts_sum]
      _ = _ := by simp only [tdc_dot, Finset.sum_mul]; exact Finset.sum_comm
  rw [he, Finset.sum_eq_single i, sub_self]
  · intro j _ hji
    exact tdc_component_orthogonal r m j i _ _ hji (tdc_parts_mem d j) hv
  · simp

lemma tgc_project_constant {r m : ℕ} (i : Fin 4) (c : ℝ) :
    (tgc_space r m i).starProjection (tgc_equi _ (fun _ => c)) = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  intro w hw
  obtain ⟨v,hv,rfl⟩ := hw
  change inner ℝ (tgc_equi _ (fun _ => c) - 0) (tgc_equi _ v) = 0
  rw [sub_zero, tgc_inner]
  simp [tdc_dot, ← Finset.mul_sum, tgc_component_centered i v hv]

lemma tgc_project_signal {r m : ℕ} (i : Fin 4) (hi : i ≠ 1) :
    (tgc_space r m i).starProjection
      (tgc_equi _ (fun k : Σ _ : Fin r × Fin 2, Fin m => phaseSize k-6)) = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  intro w hw
  obtain ⟨v,hv,rfl⟩ := hw
  change inner ℝ (tgc_equi _ (fun k => phaseSize k-6) - 0) (tgc_equi _ v) = 0
  rw [sub_zero, tgc_inner]
  apply tdc_component_orthogonal r m 1 i _ _ hi.symm _ hv
  change (fun k : Σ _ : Fin r × Fin 2, Fin m => phaseSize k-6) ∈ phaseSignalSpace r m
  exact Submodule.mem_span_singleton_self _

lemma tgc_project_affine {r m : ℕ} (i : Fin 4) (hi : i ≠ 1)
    (v : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (b c : ℝ) :
    (tgc_space r m i).starProjection
      (tgc_equi _ (fun k => b*(phaseSize k-6)+v k+c)) =
        (tgc_space r m i).starProjection (tgc_equi _ v) := by
  have he : (fun k : Σ _ : Fin r × Fin 2, Fin m => b*(phaseSize k-6)+v k+c) =
      b • (fun k => phaseSize k-6) + v + (fun _ => c) := by ext k; rfl
  simp only [he, map_add, map_smul, tgc_project_signal i hi, tgc_project_constant,
    smul_zero, zero_add, add_zero]

lemma tgc_project_generated {Ξ : Type} {r m : ℕ} (i : Fin 4) (hi : i ≠ 1)
    (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ) (β : ℝ) (ξ : Ξ) :
    (tgc_space r m i).starProjection (tgc_equi _ (centeredOutcomes phaseSize β ε ξ)) =
      (tgc_space r m i).starProjection (tgc_equi _ (fun k => ε k ξ)) := by
  convert tgc_project_affine i hi (fun k => ε k ξ) β
    (6*β-(∑ l, rawOutcomes phaseSize β ε ξ l)/
      (Fintype.card (Σ _ : Fin r × Fin 2, Fin m):ℝ)) using 1
  congr 2
  funext k
  dsimp [centeredOutcomes, rawOutcomes]
  ring

lemma tgc_component_norm {Ξ : Type} {r m : ℕ} (σ2 : ℝ) (hσ : 0 < σ2)
    (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ) (β : ℝ) (ξ : Ξ)
    (d : PhaseDecomposition r m (centeredOutcomes phaseSize β ε ξ))
    (i : Fin 4) (hi : i ≠ 1) :
    populationSquareNorm (tdc_parts d i) = σ2 *
      ‖(tgc_space r m i).starProjection
        (tgc_equi _ (fun k => ε k ξ / Real.sqrt σ2))‖^2 := by
  have hs : Real.sqrt σ2 ≠ 0 := (Real.sqrt_pos.mpr hσ).ne'
  have he : (fun k => ε k ξ) =
      Real.sqrt σ2 • (fun k => ε k ξ / Real.sqrt σ2) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [← tgc_norm_sq, ← tgc_project_part d i, tgc_project_generated i hi,
    he, map_smul, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt hσ.le]

lemma tgc_transfer_moment {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (X : Ξ → ℝ) (hX : AEMeasurable X μ) (d : ℕ)
    (hlaw : μ.map X = chiSquaredLaw d) :
    Integrable X μ ∧ (∫ ξ, X ξ ∂μ) = (d:ℝ) := by
  have hInt : Integrable (id : ℝ → ℝ) (μ.map X) := hlaw.symm ▸ (tgc_chi_moment d).1
  refine ⟨(integrable_map_measure aestronglyMeasurable_id hX).mp hInt, ?_⟩
  rw [← integral_map (f := fun x : ℝ => x) hX (by fun_prop), hlaw]
  exact (tgc_chi_moment d).2

theorem contrast_gaussian_law_proof {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (r m : ℕ) (hr : 0 < r) (hm : 2 ≤ m)
    (β σ2 : ℝ) (hσ : 0 < σ2)
    (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ) (hε : GaussianNoise μ ε σ2) :
    let z := centeredOutcomes phaseSize β ε
    let N : ℝ := m*(2*r)
    let a := (N-m)*σ2/N^2
    let c := contrastCoefficient (2*r)
    (∃ X : Fin 3 → Ξ → ℝ, iIndepFun X μ ∧
      μ.map (X 0) = chiSquaredLaw (m*(2*r)-2*r) ∧
      μ.map (X 1) = chiSquaredLaw (r-1) ∧ μ.map (X 2) = chiSquaredLaw (r-1) ∧
      (∀ᵐ ξ ∂μ, periodicContrast hr (z ξ) = a*(X 0 ξ+c*(X 1 ξ-X 2 ξ)))) ∧
    outcomeE μ (fun ξ => periodicContrast hr (z ξ)) = a*(N-2*r) ∧
    0 < outcomeE μ (fun ξ => periodicContrast hr (z ξ)) := by
  let z := centeredOutcomes phaseSize β ε
  let N : ℝ := m*(2*r)
  let a := (N-m)*σ2/N^2
  let c := contrastCoefficient (2*r)
  change (∃ X : Fin 3 → Ξ → ℝ, _) ∧ _ ∧ _
  let Z := fun ξ => tgc_equi _ (fun k => ε k ξ / Real.sqrt σ2)
  let ix : Fin 3 → Fin 4 := ![0,3,2]
  let U := fun i => tgc_space r m (ix i)
  let X : Fin 3 → Ξ → ℝ := fun i ξ => ‖(U i).starProjection (Z ξ)‖^2
  have hstd := tgc_standardize μ ε σ2 hσ hε
  have hix : Function.Injective ix := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [ix]
  have horth : ∀ i j : Fin 3, i ≠ j → ∀ v ∈ U i, ∀ w ∈ U j, inner ℝ v w = 0 := by
    intro i j hij v hv w hw
    exact tgc_space_orthogonal r m (ix i) (ix j) (hix.ne hij) v w hv hw
  have hdist := tgc_projection_laws μ Z hstd.1 hstd.2 U horth
  have hm0 : 0 < m := by omega
  have hd0 : Module.finrank ℝ (U 0) = m*(2*r)-2*r := by
    rw [tgc_space_rank]
    exact tdc_within_rank r m hm0
  have hd1 : Module.finrank ℝ (U 1) = r-1 := by
    rw [tgc_space_rank]
    exact tdc_parity_rank r m hr hm0 true
  have hd2 : Module.finrank ℝ (U 2) = r-1 := by
    rw [tgc_space_rank]
    exact tdc_parity_rank r m hr hm0 false
  have hlaw0 : μ.map (X 0) = chiSquaredLaw (m*(2*r)-2*r) := by
    simpa only [hd0] using hdist.2 0
  have hlaw1 : μ.map (X 1) = chiSquaredLaw (r-1) := by
    simpa only [hd1] using hdist.2 1
  have hlaw2 : μ.map (X 2) = chiSquaredLaw (r-1) := by
    simpa only [hd2] using hdist.2 2
  have hK : 0 < Fintype.card (Σ _ : Fin r × Fin 2, Fin m) := by
    simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
    positivity
  have hz (ξ : Ξ) : ∑ k, z ξ k = 0 := centered_outcomes_zero hK phaseSize β ε ξ
  have hrep (ξ : Ξ) : periodicContrast hr (z ξ) = a*(X 0 ξ+c*(X 1 ξ-X 2 ξ)) := by
    let d := tdc_decomposition hr hm0 (z ξ) (hz ξ)
    have hW := tgc_component_norm σ2 hσ ε β ξ d 0 (by decide)
    have hG := tgc_component_norm σ2 hσ ε β ξ d 3 (by decide)
    have hL := tgc_component_norm σ2 hσ ε β ξ d 2 (by decide)
    change populationSquareNorm d.within = σ2*X 0 ξ at hW
    change populationSquareNorm d.high = σ2*X 1 ξ at hG
    change populationSquareNorm d.low = σ2*X 2 ξ at hL
    rw [tdc_diagonal hr hm (z ξ) (hz ξ) d, hW, hG, hL]
    dsimp only [a,N,c]
    ring
  have hXm (i : Fin 3) : AEMeasurable (X i) μ := by
    exact (by fun_prop : Measurable (fun v => ‖(U i).starProjection v‖^2)).comp_aemeasurable hstd.1
  have h0 := tgc_transfer_moment μ (X 0) (hXm 0) _ hlaw0
  have h1 := tgc_transfer_moment μ (X 1) (hXm 1) _ hlaw1
  have h2 := tgc_transfer_moment μ (X 2) (hXm 2) _ hlaw2
  have hmean : outcomeE μ (fun ξ => periodicContrast hr (z ξ)) = a*(N-2*r) := by
    unfold outcomeE
    simp_rw [hrep]
    have hdiff : Integrable (fun ξ => X 1 ξ-X 2 ξ) μ := h1.1.sub h2.1
    rw [integral_const_mul, integral_add h0.1 (hdiff.const_mul c),
      integral_const_mul, integral_sub h1.1 h2.1, h0.2, h1.2, h2.2,
      sub_self, mul_zero, add_zero]
    congr 1
    dsimp [N]
    rw [Nat.cast_sub (by nlinarith : 2*r ≤ m*(2*r))]
    push_cast
    ring
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hNm : 0 < N-m := by dsimp [N]; nlinarith
  have hNq : 0 < N-2*r := by dsimp [N]; nlinarith
  have ha : 0 < a := by dsimp [a]; exact div_pos (mul_pos hNm hσ) (sq_pos_of_pos (by dsimp [N]; positivity))
  exact ⟨⟨X, hdist.1, hlaw0, hlaw1, hlaw2, ae_of_all _ hrep⟩,
    hmean, hmean.symm ▸ mul_pos ha hNq⟩

end
end AronowAudit.P027.Wave1
