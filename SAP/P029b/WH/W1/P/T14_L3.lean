import SAP.P029b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

namespace SAP.P029b.WH.W1.P.T14_L3

private theorem stratum_tail_probability
    {G Ω : Type*} [Fintype G] [MeasurableSpace Ω]
    (μ : Measure Ω) (n1 n0 : G → ℕ → ℕ) (p1 p0 : G → ℝ)
    [IsProbabilityMeasure μ]
    (K : (g : G) → (n : ℕ) → Ω → Fin (n1 g n + 1) × Fin (n0 g n + 1))
    (hK : ∀ g n, Measurable (K g n))
    (hmarg : ∀ g n k, mP μ {ω | K g n ω = k} =
      binomialArmLaw (n1 g n) (n0 g n) (p1 g) (p0 g) k)
    (g : G) (n : ℕ) (δ : ℝ) :
    mP μ {ω | δ < |armRateScore (n1 g n) (n0 g n) (K g n ω) - (p1 g-p0 g)|} =
      fP (binomialArmLaw (n1 g n) (n0 g n) (p1 g) (p0 g))
        (fun k => δ < |armRateScore (n1 g n) (n0 g n) k - (p1 g-p0 g)|) := by
  classical
  let X := Fin (n1 g n + 1) × Fin (n0 g n + 1)
  let tail : X → Prop := fun k =>
    δ < |armRateScore (n1 g n) (n0 g n) k - (p1 g-p0 g)|
  let fiber : X → Set Ω := fun k => if tail k then {ω | K g n ω = k} else ∅
  have hevent : {ω | δ < |armRateScore (n1 g n) (n0 g n) (K g n ω) - (p1 g-p0 g)|} =
      ⋃ k : X, fiber k := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    change tail (K g n ω) ↔ ∃ k : X, ω ∈ fiber k
    constructor
    · intro h
      exact ⟨K g n ω, by simp [fiber, h]⟩
    · rintro ⟨k, hk⟩
      by_cases htail : tail k
      · have heq : K g n ω = k := by simpa [fiber, htail] using hk
        simpa [heq] using htail
      · simp [fiber, htail] at hk
  have hdisj : Pairwise (fun j k => Disjoint (fiber j) (fiber k)) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro ω hj hk
    by_cases hjt : tail j <;> by_cases hkt : tail k
    · simp only [fiber, if_pos hjt, if_pos hkt, Set.mem_setOf_eq] at hj hk
      exact hjk (hj.symm.trans hk)
    · simp [fiber, hjt, hkt] at hk
    · simp [fiber, hjt, hkt] at hj
    · simp [fiber, hjt, hkt] at hj
  have hmeas : ∀ k, MeasurableSet (fiber k) := by
    intro k
    by_cases hk : tail k
    · change MeasurableSet (if tail k then {ω | K g n ω = k} else ∅)
      rw [if_pos hk]
      change MeasurableSet ((K g n) ⁻¹' {k})
      exact hK g n (measurableSet_singleton k)
    · simp [fiber, hk]
  calc
    mP μ {ω | δ < |armRateScore (n1 g n) (n0 g n) (K g n ω) - (p1 g-p0 g)|}
        = μ.real (⋃ k : X, fiber k) := by
            rw [hevent]
            rfl
    _ = ∑ k : X, μ.real (fiber k) := by
          exact measureReal_iUnion_fintype hdisj hmeas
    _ = ∑ k : X, if tail k then
          binomialArmLaw (n1 g n) (n0 g n) (p1 g) (p0 g) k else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases htail : tail k
          · simp only [fiber, if_pos htail]
            change (μ {ω | K g n ω = k}).toReal = _
            exact hmarg g n k
          · simp [fiber, htail, mP]
    _ = fP (binomialArmLaw (n1 g n) (n0 g n) (p1 g) (p0 g)) tail := by
          rfl

end SAP.P029b.WH.W1.P.T14_L3

theorem SAP.P029b.WH.W1.T14_L3_proof : SAP.P029b.WH.W1.T14_L3 := by
  classical
  change SAP.P029b.JointStratumConsistencyW1
  intro G Ω _ _ μ hμ n1 n0 p1 p0 hn1 hn0 ht1 ht0 hp K hK hmarg δ hδ
  have htail (g : G) : Tendsto (fun n =>
      fP (binomialArmLaw (n1 g n) (n0 g n) (p1 g) (p0 g))
        (fun k => δ < |armRateScore (n1 g n) (n0 g n) k - (p1 g-p0 g)|))
      atTop (𝓝 0) :=
    SAP.P029b.Bridge.saturated_score_consistency_proof
      (n1 g) (n0 g) (hn1 g) (hn0 g) (ht1 g) (ht0 g)
      (p1 g) (p0 g) (hp g).1 (hp g).2.1 (hp g).2.2 δ hδ
  have hsum : Tendsto (fun n => ∑ g : G,
      fP (binomialArmLaw (n1 g n) (n0 g n) (p1 g) (p0 g))
        (fun k => δ < |armRateScore (n1 g n) (n0 g n) k - (p1 g-p0 g)|))
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset G) (fun g _ => htail g)
  have hbound (n : ℕ) : mP μ {ω | ∃ g, δ <
      |armRateScore (n1 g n) (n0 g n) (K g n ω) - (p1 g-p0 g)|} ≤
      ∑ g : G, fP (binomialArmLaw (n1 g n) (n0 g n) (p1 g) (p0 g))
        (fun k => δ < |armRateScore (n1 g n) (n0 g n) k - (p1 g-p0 g)|) := by
    have hevent : {ω | ∃ g, δ <
        |armRateScore (n1 g n) (n0 g n) (K g n ω) - (p1 g-p0 g)|} =
        ⋃ g : G, {ω | δ <
          |armRateScore (n1 g n) (n0 g n) (K g n ω) - (p1 g-p0 g)|} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    calc
      mP μ {ω | ∃ g, δ <
          |armRateScore (n1 g n) (n0 g n) (K g n ω) - (p1 g-p0 g)|}
          = μ.real (⋃ g : G, {ω | δ <
              |armRateScore (n1 g n) (n0 g n) (K g n ω) - (p1 g-p0 g)|}) := by
                rw [hevent]
                rfl
      _ ≤ ∑ g : G, mP μ {ω | δ <
            |armRateScore (n1 g n) (n0 g n) (K g n ω) - (p1 g-p0 g)|} :=
          measureReal_iUnion_fintype_le _
      _ = _ := by
          apply Finset.sum_congr rfl
          intro g hg
          exact SAP.P029b.WH.W1.P.T14_L3.stratum_tail_probability
            μ n1 n0 p1 p0 K hK hmarg g n δ
  apply squeeze_zero (fun n => measureReal_nonneg) hbound hsum
