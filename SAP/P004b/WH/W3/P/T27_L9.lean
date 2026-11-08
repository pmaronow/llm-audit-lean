import SAP.P004b.WH.W3.Leaves
import AronowAudit.P004.Wave1.Gap.GP0042B2b

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3.P.T27_L9

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

private def pHalf {N : ℕ} : Fin N → ℝ := fun _ => 1/2

private def countBad (N : ℕ) (z : Assignment N) : Prop :=
  ¬ (2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ)-1)

private lemma expect_sub_local {N : ℕ} (p : Fin N → ℝ)
    (X Y : Assignment N → ℝ) :
    expect p (fun z => X z - Y z) = expect p X - expect p Y := by
  unfold expect
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

private lemma expect_add_local {N : ℕ} (p : Fin N → ℝ)
    (X Y : Assignment N → ℝ) :
    expect p (fun z => X z + Y z) = expect p X + expect p Y := by
  unfold expect
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

private lemma prob_mono {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A B : Assignment N → Prop)
    (hAB : ∀ z, A z → B z) : prob p A ≤ prob p B := by
  unfold prob
  apply AronowAudit.P004.expect_mono p hp
  intro z
  by_cases ha : A z
  · simp only [if_pos ha, if_pos (hAB z ha), le_refl]
  · by_cases hb : B z <;> simp [ha, hb]

private lemma prob_difference {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1)
    (A B Bad C : Assignment N → Prop)
    (hcover : ∀ z, A z → ¬ B z → ¬ Bad z → C z) :
    prob p A - prob p B - prob p Bad ≤ prob p C := by
  change expect p (fun z => if A z then (1 : ℝ) else 0) -
      expect p (fun z => if B z then (1 : ℝ) else 0) -
      expect p (fun z => if Bad z then (1 : ℝ) else 0) ≤ _
  rw [← expect_sub_local p, ← expect_sub_local p]
  apply AronowAudit.P004.expect_mono p hp
  intro z
  by_cases ha : A z
  · by_cases hb : B z
    · by_cases hg : Bad z <;> by_cases hc : C z <;> norm_num [ha, hb, hg, hc]
    · by_cases hg : Bad z
      · by_cases hc : C z <;> norm_num [ha, hb, hg, hc]
      · simp [ha, hb, hg, hcover z ha hb hg]
  · by_cases hb : B z <;> by_cases hg : Bad z <;> by_cases hc : C z <;>
      norm_num [ha, hb, hg, hc]

private lemma prob_two_upper {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A B C : Assignment N → Prop)
    (hcover : ∀ z, A z → B z ∨ C z) : prob p A ≤ prob p B + prob p C := by
  change _ ≤ expect p (fun z => if B z then (1 : ℝ) else 0) +
    expect p (fun z => if C z then (1 : ℝ) else 0)
  rw [← expect_add_local p]
  apply AronowAudit.P004.expect_mono p hp
  intro z
  by_cases ha : A z
  · rcases hcover z ha with hb | hc
    · by_cases hc : C z <;> simp [ha, hb, hc]
    · by_cases hb : B z <;> simp [ha, hb, hc]
  · by_cases hb : B z <;> by_cases hc : C z <;> simp [ha, hb, hc]

private lemma first_probability {N : ℕ} (hN : 0 < N) :
    prob pHalf (fun z : Assignment N => wholeFirst z = true) = 1/2 := by
  have heq : (fun z : Assignment N => wholeFirst z = true) =
      (fun z => z ⟨0, hN⟩ = true) := by
    funext z
    simp [wholeFirst, hN]
  rw [heq]
  exact AronowAudit.P004.Wave1.T27_first_probability hN

private lemma branch_joint {N : ℕ} (b : Bool) (E : Assignment N → Prop) :
    prob pHalf (fun z => wholeFirst z = b ∧ E z) =
      wholeSparseCond N b E / 2 := by
  unfold wholeSparseCond
  change prob pHalf (fun z => wholeFirst z = b ∧ E z) =
    (2 * prob pHalf (fun z => wholeFirst z = b ∧ E z)) / 2
  ring

private lemma countBad_tendsto (hLaw : WholeSparseCountLaw) :
    Tendsto (fun N => prob pHalf (countBad N)) atTop (nhds 0) := by
  have hpow : Tendsto (fun N : ℕ => (1/2 : ℝ)^N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun N : ℕ => 4 * (1/2 : ℝ)^N) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hpow
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 3] with N hN
  have h := (hLaw N hN).2.1
  have heq : prob pHalf (countBad N) = 4 * (1/2 : ℝ)^N := by
    calc
      prob pHalf (countBad N) =
          prob (fun _ : Fin N => 1/2)
            (fun z => ¬ (2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ)-1)) := rfl
      _ = 4 / (2 : ℝ)^N := h
      _ = 4 * (1/2 : ℝ)^N := by
        have hpowne : (2 : ℝ)^N ≠ 0 := pow_ne_zero _ (by norm_num)
        field_simp [hpowne]
        rw [← mul_pow]
        norm_num
  exact heq.symm

private lemma valid_cover_of_close {N : ℕ} (hFin : WholeSparseFinite)
    (a ε : ℝ) (hε : 0 < ε) (hgap : ε ≤ a - 5/8)
    (z : Assignment N) (hN : 3 ≤ N)
    (hgood : 2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ)-1)
    (hclose : ¬ ε < |wholeSparseT N z - 5/8|) :
    wholeCovered (1/2) (wholeSparseR N) (wholeSparseQmat N) (-a) a z := by
  have hf := hFin N hN z hgood.1 hgood.2
  rcases hf with ⟨hvalid, _, _, hstat⟩
  have habs : |wholeSparseT N z - 5/8| ≤ ε := le_of_not_gt hclose
  have hbounds := (abs_le.mp habs)
  change ValidInterval (wholeSparseR N) (wholeSparseQmat N) z ∧
    -a ≤ wholeSparseT N z ∧ wholeSparseT N z ≤ a
  refine ⟨hvalid, ?_⟩
  constructor <;> linarith

private lemma false_cover_forces_tail {N : ℕ} (a ε : ℝ)
    (ha : a < 5/2) (hε : ε < 5/2-a) (z : Assignment N)
    (hc : wholeCovered (1/2) (wholeSparseR N) (wholeSparseQmat N) (-a) a z) :
    ε < |wholeSparseT N z - (-5/2)| := by
  change ValidInterval (wholeSparseR N) (wholeSparseQmat N) z ∧
    -a ≤ wholeSparseT N z ∧ wholeSparseT N z ≤ a at hc
  have hl := hc.2.1
  have hpos : 0 < wholeSparseT N z + 5/2 := by linarith
  have harg : wholeSparseT N z - (-5/2) = wholeSparseT N z + 5/2 := by ring
  rw [harg]
  rw [abs_of_pos hpos]
  linarith

theorem proof : SAP.P004b.WH.W3.T27_L9 := by
  intro hLaw hFin hStat a ha1 ha2
  let ε₁ : ℝ := (a - 5/8) / 2
  let ε₀ : ℝ := (5/2 - a) / 2
  have hε₁ : 0 < ε₁ := by dsimp [ε₁]; linarith
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; linarith
  have hgap₁ : ε₁ ≤ a - 5/8 := by dsimp [ε₁]; linarith
  have hgap₀ : ε₀ < 5/2 - a := by dsimp [ε₀]; linarith
  let Tail₁ : ∀ N : ℕ, Assignment N → Prop := fun N z =>
    ε₁ < |wholeSparseT N z - 5/8|
  let Tail₀ : ∀ N : ℕ, Assignment N → Prop := fun N z =>
    ε₀ < |wholeSparseT N z - (-5/2)|
  have hTail₁ : Tendsto (fun N => wholeSparseCond N true (Tail₁ N)) atTop (nhds 0) := by
    simpa [Tail₁, ε₁] using hStat true ε₁ hε₁
  have hTail₀ : Tendsto (fun N => wholeSparseCond N false (Tail₀ N)) atTop (nhds 0) := by
    simpa [Tail₀, ε₀] using hStat false ε₀ hε₀
  have hBad := countBad_tendsto hLaw
  have hLow : Tendsto (fun N => (1/2 : ℝ) -
      wholeSparseCond N true (Tail₁ N)/2 - prob pHalf (countBad N))
      atTop (nhds (1/2 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub (hTail₁.div_const 2)).sub hBad
  have hUp : Tendsto (fun N => (1/2 : ℝ) +
      wholeSparseCond N false (Tail₀ N)/2) atTop (nhds (1/2 : ℝ)) := by
    simpa using tendsto_const_nhds.add (hTail₀.div_const 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLow hUp
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hNpos : 0 < N := by omega
    have hfirst := first_probability hNpos
    have hbound := prob_difference
      pHalf (fun _ => by norm_num [pHalf]) (fun z => wholeFirst z = true)
      (fun z => wholeFirst z = true ∧ Tail₁ N z) (countBad N)
      (fun z => wholeCovered (1/2) (wholeSparseR N) (wholeSparseQmat N) (-a) a z) ?_
    have hjoint := branch_joint true (Tail₁ N)
    have htailid : prob pHalf (fun z => wholeFirst z = true ∧ Tail₁ N z) =
        wholeSparseCond N true (Tail₁ N)/2 := hjoint
    have hfirstid : prob pHalf (fun z => wholeFirst z = true) = 1/2 := hfirst
    rw [hfirstid, htailid] at hbound
    exact hbound
    intro z hz hnotTail hnotBad
    have hgood : 2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ)-1 := by
      by_contra h
      exact hnotBad (by simpa [countBad] using h)
    apply valid_cover_of_close hFin a ε₁ hε₁ hgap₁ z hN hgood
    intro htail
    exact hnotTail ⟨hz, by simpa [Tail₁] using htail⟩
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hNpos : 0 < N := by omega
    have hfirst := first_probability hNpos
    have hbound := prob_two_upper
      pHalf (fun _ => by norm_num [pHalf])
      (fun z => wholeCovered (1/2) (wholeSparseR N) (wholeSparseQmat N) (-a) a z)
      (fun z => wholeFirst z = true)
      (fun z => wholeFirst z = false ∧ Tail₀ N z) ?_
    have htailupper : prob pHalf (fun z => wholeFirst z = false ∧ Tail₀ N z) ≤
        wholeSparseCond N false (Tail₀ N)/2 := by
      exact (branch_joint false (Tail₀ N)).le
    have hfirstid : prob pHalf (fun z => wholeFirst z = true) = 1/2 := hfirst
    have hcovupper : prob pHalf
        (fun z => wholeCovered (1/2) (wholeSparseR N) (wholeSparseQmat N) (-a) a z) ≤
          (1/2 : ℝ) + wholeSparseCond N false (Tail₀ N)/2 := by
      linarith [hbound, hfirstid, htailupper]
    exact hcovupper
    intro z hc
    by_cases hb : wholeFirst z = true
    · exact Or.inl hb
    · have hfalse : wholeFirst z = false := by
        cases hh : wholeFirst z with
        | false => rfl
        | true => exact (hb hh).elim
      have ht := false_cover_forces_tail a ε₀ ha2 hgap₀ z hc
      exact Or.inr ⟨hfalse, by simpa [Tail₀] using ht⟩

end
end SAP.P004b.WH.W3.P.T27_L9

theorem SAP.P004b.WH.W3.T27_L9_proof : SAP.P004b.WH.W3.T27_L9 := by
  exact SAP.P004b.WH.W3.P.T27_L9.proof

