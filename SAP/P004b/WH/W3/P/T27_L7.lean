import SAP.P004b.WH.W3.Leaves
import AronowAudit.P004.Wave1.DesignLimits.DL9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3.P.T27_L7

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

open SAP.P004b.WH.W3

/-- The continuous formula for the statistic as a function of its two scaled
count inputs. -/
def statMap (a : Bool) (u : Fin 2 → ℝ) : ℝ :=
  if a then (1 - 3 * u 0 / 4) * Real.sqrt (u 0 / (u 0 - u 1))
  else -(1 + 3 * u 0) * Real.sqrt (u 0 / (u 0 - u 1))

def statCenter : Fin 2 → ℝ := ![(1 / 2 : ℝ), 0]

def statInput (N : ℕ) (z : Assignment N) : Fin 2 → ℝ :=
  ![wholeSparseQ z / (N : ℝ), 1 / (N : ℝ)]

lemma statMap_continuousAt (a : Bool) : ContinuousAt (statMap a) statCenter := by
  have hx : ContinuousAt (fun u : Fin 2 → ℝ => u 0) statCenter :=
    (continuous_apply 0).continuousAt
  have hy : ContinuousAt (fun u : Fin 2 → ℝ => u 1) statCenter :=
    (continuous_apply 1).continuousAt
  have hrootarg : ContinuousAt (fun u : Fin 2 → ℝ => u 0 / (u 0 - u 1)) statCenter := by
    apply hx.div (hx.sub hy)
    norm_num [statCenter]
  have hroot : ContinuousAt (fun u : Fin 2 → ℝ => Real.sqrt (u 0 / (u 0 - u 1))) statCenter :=
    Real.continuous_sqrt.continuousAt.comp hrootarg
  have hc1 : ContinuousAt (fun u : Fin 2 → ℝ => 1 - 3 * u 0 / 4) statCenter := by
    have hmul : ContinuousAt (fun u : Fin 2 → ℝ => 3 * u 0) statCenter :=
      continuousAt_const.mul hx
    have hdiv : ContinuousAt (fun u : Fin 2 → ℝ => (3 * u 0) / 4) statCenter := by
      apply hmul.div continuousAt_const
      norm_num
    exact continuousAt_const.sub hdiv
  have hc0 : ContinuousAt (fun u : Fin 2 → ℝ => 1 + 3 * u 0) statCenter := by
    exact continuousAt_const.add (continuousAt_const.mul hx)
  cases a
  · change ContinuousAt (fun u : Fin 2 → ℝ => (-(1 + 3 * u 0)) *
      Real.sqrt (u 0 / (u 0 - u 1))) statCenter
    exact (hc0.neg).mul hroot
  · change ContinuousAt (fun u : Fin 2 → ℝ => (1 - 3 * u 0 / 4) *
      Real.sqrt (u 0 / (u 0 - u 1))) statCenter
    exact hc1.mul hroot

lemma statMap_center (a : Bool) : statMap a statCenter = if a then 5 / 8 else -5 / 2 := by
  cases a <;> norm_num [statMap, statCenter, Real.sqrt_one]

lemma statMap_formula (N : ℕ) (z : Assignment N) (a : Bool)
    (hN : 3 ≤ N) (hqlo : 2 ≤ wholeSparseQ z)
    (hqhi : wholeSparseQ z ≤ (N : ℝ) - 1)
    (hfirst : wholeFirst z = a)
    (hfinite : WholeSparseFinite) :
    wholeSparseT N z = statMap a (statInput N z) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hq1 : wholeSparseQ z - 1 ≠ 0 := by
    have hq : (1 : ℝ) < wholeSparseQ z := by linarith
    linarith
  have hden : wholeSparseQ z / (N : ℝ) - 1 / (N : ℝ) =
      (wholeSparseQ z - 1) / (N : ℝ) := by ring
  have hratio : wholeSparseQ z / (wholeSparseQ z - 1) =
      (wholeSparseQ z / (N : ℝ)) /
        (wholeSparseQ z / (N : ℝ) - 1 / (N : ℝ)) := by
    rw [hden]
    field_simp [hNne, hq1]
    <;> ring
  rcases hfinite N hN z hqlo hqhi with ⟨_, _, _, ht⟩
  rw [ht, hfirst]
  dsimp [statMap, statInput, hfirst]
  by_cases ha : a
  · simp only [if_pos ha]
    rw [← hratio]
    have hcoef : 1 - 3 * wholeSparseQ z / (4 * (N : ℝ)) =
        1 - 3 * (wholeSparseQ z / (N : ℝ)) / 4 := by
      field_simp [hNne]
      <;> ring
    rw [hcoef]
  · have han : a ≠ true := by simpa using ha
    simp only [if_neg han]
    rw [← hratio]
    have hcoef : -(1 + 3 * wholeSparseQ z / (N : ℝ)) =
        -(1 + 3 * (wholeSparseQ z / (N : ℝ))) := by
      field_simp [hNne]
      <;> ring
    rw [hcoef]

lemma prob_half_nonneg {N : ℕ} (E : Assignment N → Prop) :
    0 ≤ prob (fun _ : Fin N => (1 / 2 : ℝ)) E := by
  apply AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_nonneg
  · intro i
    norm_num

lemma statMap_local_bound (a : Bool) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : Fin 2 → ℝ,
      dist u statCenter < δ → |statMap a u - (if a then 5 / 8 else -5 / 2)| < ε := by
  obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousAt_iff.mp (statMap_continuousAt a)) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro u hu
  have hc := hnear hu
  rw [Real.dist_eq, statMap_center] at hc
  exact hc

end
end SAP.P004b.WH.W3.P.T27_L7

open SAP.P004b.WH.W3.P.T27_L7
open Filter
open scoped Topology

/-- The statistic inherits the two conditional limits from the count law and
its conditional law of large numbers. -/
theorem SAP.P004b.WH.W3.T27_L7_proof : SAP.P004b.WH.W3.T27_L7 := by
  classical
  intro hcount hcountlim hfinite
  intro a ε hε
  obtain ⟨δ, hδ, hnear⟩ := statMap_local_bound a ε hε
  have hhalfδ : 0 < δ / 2 := by linarith
  have hinvT : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hinv : ∀ᶠ N : ℕ in atTop, |(N : ℝ)⁻¹| < δ / 2 := by
    have hnb := Metric.tendsto_nhds.mp hinvT (δ / 2) hhalfδ
    filter_upwards [hnb] with N hN
    change dist ((N : ℝ)⁻¹) (0 : ℝ) < δ / 2 at hN
    rw [Real.dist_eq, sub_zero] at hN
    exact hN
  have hlarge : ∀ᶠ N : ℕ in atTop, 3 ≤ N :=
    Filter.eventually_atTop.2 ⟨3, fun N hN => hN⟩
  have hcountT : Tendsto
      (fun N => wholeSparseCond N a
        (fun z => δ / 2 < |wholeSparseQ z / N - 1 / 2|)) atTop (nhds 0) := by
    simpa using hcountlim a (δ / 2) hhalfδ
  have hendT : Tendsto (fun N : ℕ => 2 * (4 / (2 : ℝ) ^ N)) atTop (nhds 0) := by
    have hp : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hmul : Tendsto (fun N : ℕ => (8 : ℝ) * (1 / 2 : ℝ) ^ N)
        atTop (nhds (8 * 0)) := by
      exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (8 : ℝ)) atTop (nhds 8)).mul hp
    have heq : (fun N : ℕ => 2 * (4 / (2 : ℝ) ^ N)) =
        (fun N => 8 * (1 / 2 : ℝ) ^ N) := by
      funext N
      simp [div_pow]
      ring
    rw [heq]
    simpa using hmul
  have hstatNonneg : ∀ N : ℕ, 0 ≤ wholeSparseCond N a
      (fun z => ε < |wholeSparseT N z - (if a then 5 / 8 else -5 / 2)|) := by
    intro N
    unfold wholeSparseCond
    exact mul_nonneg (by norm_num) (prob_half_nonneg _)
  have hbound : ∀ᶠ N : ℕ in atTop,
      wholeSparseCond N a
        (fun z => ε < |wholeSparseT N z - (if a then 5 / 8 else -5 / 2)|) ≤
      wholeSparseCond N a (fun z => δ / 2 < |wholeSparseQ z / N - 1 / 2|) +
        2 * (4 / (2 : ℝ) ^ N) := by
    filter_upwards [hlarge, hinv] with N hN hNinv
    let p : Fin N → ℝ := fun _ => 1 / 2
    have hp : ∀ i, 0 < p i ∧ p i < 1 := by
      intro i
      norm_num [p]
    let A : Assignment N → Prop := fun z =>
      wholeFirst z = a ∧ ε < |wholeSparseT N z - (if a then 5 / 8 else -5 / 2)|
    let B : Assignment N → Prop := fun z =>
      wholeFirst z = a ∧ δ / 2 < |wholeSparseQ z / N - 1 / 2|
    let C : Assignment N → Prop := fun z =>
      wholeFirst z = a ∧ ¬ (2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ) - 1)
    have hsplit : ∀ z, A z → B z ∨ C z := by
      intro z hz
      by_cases hbad : δ / 2 < |wholeSparseQ z / N - 1 / 2|
      · exact Or.inl ⟨hz.1, hbad⟩
      by_cases hend : ¬ (2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ) - 1)
      · exact Or.inr ⟨hz.1, hend⟩
      have hvalid : 2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ) - 1 := by
        by_contra hn
        exact hend hn
      have hx : |(statInput N z) 0 - statCenter 0| ≤ δ / 2 := by
        simpa [statInput, statCenter] using (le_of_not_gt hbad)
      have hy : |(statInput N z) 1 - statCenter 1| < δ / 2 := by
        simpa [statInput, statCenter, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ))] using hNinv
      have hvec : dist (statInput N z) statCenter < δ := by
        apply (dist_pi_lt_iff hδ).2
        intro i
        fin_cases i
        · rw [Real.dist_eq]
          exact lt_of_le_of_lt hx (by linarith)
        · rw [Real.dist_eq]
          exact lt_trans hy (by linarith)
      have hmap := hnear (statInput N z) hvec
      rcases hfinite N (by omega) z hvalid.1 hvalid.2 with ⟨_, _, _, ht⟩
      have htmap : wholeSparseT N z = statMap a (statInput N z) := by
        exact statMap_formula N z a (by omega) hvalid.1 hvalid.2 hz.1 hfinite
      rw [← htmap] at hmap
      exact False.elim ((not_lt_of_ge (le_of_lt hz.2)) hmap)
    have hprob := AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_le_add
      p hp A B C hsplit
    have hC : 2 * prob p C ≤ 2 * (4 / (2 : ℝ) ^ N) := by
      have hmono := AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_mono
        p hp C (fun z => ¬ (2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ) - 1))
        (fun _ hz => hz.2)
      have he := (hcount N (by omega)).2.1
      calc
        2 * prob p C ≤
            2 * prob p (fun z => ¬ (2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left hmono (by norm_num)
        _ = 2 * (4 / (2 : ℝ) ^ N) := by
          simpa [p] using congrArg (fun x : ℝ => 2 * x) he
    unfold wholeSparseCond
    change 2 * prob p A ≤ 2 * prob p B + 2 * (4 / (2 : ℝ) ^ N)
    calc
      2 * prob p A ≤ 2 * (prob p B + prob p C) :=
        mul_le_mul_of_nonneg_left hprob (by norm_num)
      _ = 2 * prob p B + 2 * prob p C := by ring
      _ ≤ 2 * prob p B + 2 * (4 / (2 : ℝ) ^ N) :=
        by linarith [hC]
  have hupper : Tendsto
      (fun N => wholeSparseCond N a
        (fun z => ε < |wholeSparseT N z - (if a then 5 / 8 else -5 / 2)|))
      atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall hstatNonneg) hbound
    simpa only [zero_add] using hcountT.add hendT
  exact hupper
