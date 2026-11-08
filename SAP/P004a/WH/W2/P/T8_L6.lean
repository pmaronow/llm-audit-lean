import SAP.P004a.WH.W2.Leaves
import AronowAudit.P004.P004_Spatial

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [local instance] Classical.propDecidable

namespace SAP.P004a.WH.W2.P.T8_L6

open Filter
open scoped BigOperators Classical

private theorem armCount_nonneg {N : ℕ} (z : SAP.P004a.Assignment N) (a : Bool) :
    0 ≤ SAP.P004a.armCount z a := by
  unfold SAP.P004a.armCount
  exact Finset.sum_nonneg (fun i _ => by positivity)

private theorem armCount_zero_const {N : ℕ} (z : SAP.P004a.Assignment N) :
    SAP.P004a.armCount z true = 0 → z = fun _ => false := by
  intro hc
  funext i
  by_contra h
  have hi : z i = true := by cases hz : z i <;> simp_all
  have hle : (if z i = true then (1 : ℝ) else 0) ≤ SAP.P004a.armCount z true := by
    unfold SAP.P004a.armCount
    exact Finset.single_le_sum (f := fun j => if z j = true then (1 : ℝ) else 0)
      (fun j hj => by positivity) (Finset.mem_univ i)
  simp [hi] at hle
  linarith

private theorem armCount_false_zero_const {N : ℕ} (z : SAP.P004a.Assignment N) :
    SAP.P004a.armCount z false = 0 → z = fun _ => true := by
  intro hc
  funext i
  by_contra h
  have hi : z i = false := by cases hz : z i <;> simp_all
  have hle : (if z i = false then (1 : ℝ) else 0) ≤ SAP.P004a.armCount z false := by
    unfold SAP.P004a.armCount
    exact Finset.single_le_sum (f := fun j => if z j = false then (1 : ℝ) else 0)
      (fun j hj => by positivity) (Finset.mem_univ i)
  simp [hi] at hle
  linarith

private theorem bad_iff_constant {N : ℕ} (z : SAP.P004a.Assignment N) :
    ¬ SAP.P004a.ValidArms z ↔ z = (fun _ => false) ∨ z = (fun _ => true) := by
  constructor
  · intro hb
    by_cases ht : SAP.P004a.armCount z true = 0
    · exact Or.inl (armCount_zero_const z ht)
    · have htpos : 0 < SAP.P004a.armCount z true := lt_of_le_of_ne (armCount_nonneg z true) (Ne.symm ht)
      have hcf : SAP.P004a.armCount z false = 0 := by
        by_contra hcf
        have hcfpos : 0 < SAP.P004a.armCount z false := lt_of_le_of_ne (armCount_nonneg z false) (Ne.symm hcf)
        exact hb ⟨htpos, hcfpos⟩
      exact Or.inr (armCount_false_zero_const z hcf)
  · rintro (h | h) hv
    · subst z
      have : SAP.P004a.armCount (fun _ : Fin N => false) true = 0 := by
        simp [SAP.P004a.armCount]
      have hh := hv.1
      rw [this] at hh
      norm_num at hh
    · subst z
      have : SAP.P004a.armCount (fun _ : Fin N => true) false = 0 := by
        simp [SAP.P004a.armCount]
      have hh := hv.2
      rw [this] at hh
      norm_num at hh

private theorem bad_prob_formula {N : ℕ} (p : ℝ) (hN : 0 < N) :
    SAP.P004a.prob (fun _ : Fin N => p)
      (fun z : SAP.P004a.Assignment N => ¬ SAP.P004a.ValidArms z) = p^N + (1-p)^N := by
  let z₀ : SAP.P004a.Assignment N := fun _ => false
  let z₁ : SAP.P004a.Assignment N := fun _ => true
  have hne : z₀ ≠ z₁ := by
    intro he
    obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hN
    have := congrFun he i
    simp [z₀, z₁] at this
  have hind (z : SAP.P004a.Assignment N) :
      (if ¬ SAP.P004a.ValidArms z then (1 : ℝ) else 0) =
        (if z = z₀ then 1 else 0) + (if z = z₁ then 1 else 0) := by
    by_cases hb : ¬ SAP.P004a.ValidArms z
    · have hc := (bad_iff_constant z).mp hb
      rcases hc with hc | hc
      · have : z = z₀ := hc
        subst z
        simp [z₀, z₁, hne, hb]
      · have : z = z₁ := hc
        subst z
        simp [z₀, z₁, Ne.symm hne, hb]
    · have hne0 : z ≠ z₀ := by
        intro hz
        subst z
        apply hb
        exact (bad_iff_constant z₀).2 (Or.inl rfl)
      have hne1 : z ≠ z₁ := by
        intro hz
        subst z
        apply hb
        exact (bad_iff_constant z₁).2 (Or.inr rfl)
      simp [hb, hne0, hne1]
  have hsum :
      (∑ z : SAP.P004a.Assignment N,
        SAP.P004a.designWeight (fun _ => p) z *
          (if ¬ SAP.P004a.ValidArms z then (1 : ℝ) else 0)) =
      SAP.P004a.designWeight (fun _ => p) z₀ + SAP.P004a.designWeight (fun _ => p) z₁ := by
    calc
      _ = ∑ z : SAP.P004a.Assignment N,
          SAP.P004a.designWeight (fun _ => p) z *
            ((if z = z₀ then (1 : ℝ) else 0) + (if z = z₁ then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [hind]
      _ = (∑ z : SAP.P004a.Assignment N,
          SAP.P004a.designWeight (fun _ => p) z * (if z = z₀ then (1 : ℝ) else 0)) +
          ∑ z : SAP.P004a.Assignment N,
          SAP.P004a.designWeight (fun _ => p) z * (if z = z₁ then (1 : ℝ) else 0) := by
              simp only [mul_add, Finset.sum_add_distrib]
      _ = SAP.P004a.designWeight (fun _ => p) z₀ + SAP.P004a.designWeight (fun _ => p) z₁ := by
              simp [z₀, z₁]
  have hw0 : SAP.P004a.designWeight (fun _ : Fin N => p) z₀ = (1-p)^N := by
    simp [SAP.P004a.designWeight, SAP.P004a.coin, z₀]
  have hw1 : SAP.P004a.designWeight (fun _ : Fin N => p) z₁ = p^N := by
    simp [SAP.P004a.designWeight, SAP.P004a.coin, z₁]
  calc
    SAP.P004a.prob (fun _ : Fin N => p)
        (fun z : SAP.P004a.Assignment N => ¬ SAP.P004a.ValidArms z) =
        SAP.P004a.designWeight (fun _ => p) z₀ + SAP.P004a.designWeight (fun _ => p) z₁ := by
          unfold SAP.P004a.prob SAP.P004a.expect
          convert hsum using 1
          apply Finset.sum_congr rfl
          intro z hz
          apply congrArg (fun x : ℝ => SAP.P004a.designWeight (fun _ => p) z * x)
          dsimp
          by_cases hh : ¬ SAP.P004a.ValidArms z <;> simp [hh]
    _ = p^N + (1-p)^N := by rw [hw0, hw1]; ring

end SAP.P004a.WH.W2.P.T8_L6

open SAP.P004a.WH.W2.P.T8_L6
open Filter
open scoped Topology BigOperators Classical

theorem SAP.P004a.WH.W2.T8_L6_proof : SAP.P004a.WH.W2.T8_L6 := by
  intro p hp
  refine ⟨?_, ?_⟩
  · intro N hN
    exact bad_prob_formula p hN
  · have hp0 : 0 ≤ p := le_of_lt hp.1
    have hq0 : 0 ≤ 1-p := by linarith
    have hpseq : Tendsto (fun N : ℕ => p ^ N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hp0 hp.2
    have hqseq : Tendsto (fun N : ℕ => (1-p) ^ N) atTop (nhds 0) := by
      apply tendsto_pow_atTop_nhds_zero_of_lt_one hq0
      linarith
    have hsum : Tendsto (fun N : ℕ => p ^ N + (1-p)^N) atTop (nhds 0) := by
      simpa using hpseq.add hqseq
    have hpos : ∀ᶠ N : ℕ in atTop, 0 < N := by
      filter_upwards [Filter.eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
      exact hN
    refine hsum.congr' ?_
    filter_upwards [hpos] with N hN
    symm
    exact bad_prob_formula p hN
