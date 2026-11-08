import SAP.P012b.WH.W1.Existing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

namespace SAP.P012b.WH.W1

open Finset SAP.P012b.Bridge
noncomputable section

theorem pair_h_statistics (H K : State) (hp : SamePair H K) :
    hNumerator H = hNumerator K ∧ hDenominator H = hDenominator K ∧
    homophily H = homophily K := by
  obtain ⟨hv, he, hz⟩ := hp
  have hd : ∀ v, graphDegree H v = graphDegree K v := by
    intro v; simp only [graphDegree, he]
  have ha : ∀ v w, adjacency H v w = adjacency K v w := by
    intro v w; simp only [adjacency, he]
  have hnum : hNumerator H = hNumerator K := by
    unfold hNumerator
    rw [← hv, ← he]
    apply sum_congr rfl
    intro v hv'
    apply sum_congr rfl
    intro w hw'
    simp only [ha, hd, z, hz v hv', hz w hw']
  have hden : hDenominator H = hDenominator K := by
    unfold hDenominator
    rw [← hv, ← he]
    apply sum_congr rfl
    intro v hv'
    apply sum_congr rfl
    intro w hw'
    simp only [hd, z, hz v hv', hz w hw']
  refine ⟨hnum, hden, ?_⟩
  simp only [homophily, HomophilyDefined, hValue, he, hnum, hden]

theorem pair_p_congr (D : Data) (H K : State) (hD : Admissible D)
    (hH : Compatible D H) (hp : SamePair H K) :
    preferential D H = preferential D K := by
  obtain ⟨hv, he, hz⟩ := hp
  have hs : ∀ i j, susceptible D H i j = susceptible D K i j := by
    intro i j; simp only [susceptible, hv, he]
  have hsum : pSum D H = pSum D K := by
    apply sum_congr rfl
    intro j hj
    have hjv := hH.2.1 (mem_image_of_mem s (mem_sdiff.mp hj).1)
    have hpv := hH.2.1 (mem_image_of_mem s (hD.2.2.1 j hj).1)
    have hm : sameSusceptible D H (D.parent j) j =
        sameSusceptible D K (D.parent j) j := by
      unfold sameSusceptible
      rw [← hs]
      apply filter_congr
      intro v hv'
      rw [hz v (mem_filter.mp hv').1, hz _ hpv]
    rw [hz _ hjv, hz _ hpv, hm, hs]
  simp only [preferential, PreferentialDefined, hs, pValue, hsum]

theorem smallest_interval (values : Set ℝ) (L U : ℝ)
    (hL : IsLeast values L) (hU : IsGreatest values U) :
    SmallestValueInterval values L U := by
  refine ⟨fun _ hx => ⟨hL.2 hx, hU.2 hx⟩, ?_⟩
  intro I hI hsub
  exact hI.out (hsub hL.1) (hsub hU.1)

theorem domainA_same (H : State) (hH : Compatible domainA H) :
    SamePair H (dyad false false) := by
  have hz : ∀ i ∈ domainA.sampled, domainA.degree i = recruitmentDegree domainA i := by
    decide
  have hu : H.vertices = sampledVertices domainA ∧ H.edges = recruitmentEdges domainA ∧
      ∀ v ∈ H.vertices, H.trait v = (recruitmentState domainA).trait v := by
    sap_transfer (AronowAudit.P012.zero_spare_compatible_unique (toData domainA)
      restricted14.1.1 hz (toState H) hH)
  refine ⟨?_, ?_, ?_⟩
  · simpa [sampledVertices, domainA, dyad] using hu.1
  · exact hu.2.1.trans (by decide)
  · intro v hv
    rw [hu.2.2 v hv]
    cases v <;> simp [recruitmentState, domainA, dyad]

theorem domainA_all (H : State) (hH : Compatible domainA H) :
    SamePair H (dyad false false) ∧ hNumerator H = 0 ∧ hDenominator H = 0 ∧
      homophily H = none ∧ preferential domainA H = some 0 := by
  have hp := domainA_same H hH
  have hh := pair_h_statistics H _ hp
  have hq := pair_p_congr domainA H _ restricted14.1.1 hH hp
  exact ⟨hp, hh.1.trans restricted14.1.2.2.1,
    hh.2.1.trans restricted14.1.2.2.2.1,
    hh.2.2.trans restricted14.1.2.2.2.2.1,
    hq.trans restricted14.1.2.2.2.2.2⟩

theorem domainC_same (H : State) (hH : Compatible domainC H) :
    SamePair H domainCState := by
  have hz : ∀ i ∈ domainC.sampled, domainC.degree i = recruitmentDegree domainC i := by
    norm_num [domainC, recruitmentDegree, recruitmentEdges, nonseeds]
  have hu : H.vertices = sampledVertices domainC ∧ H.edges = recruitmentEdges domainC ∧
      ∀ v ∈ H.vertices, H.trait v = (recruitmentState domainC).trait v := by
    sap_transfer (AronowAudit.P012.zero_spare_compatible_unique (toData domainC)
      restricted14.2.2.1.1 hz (toState H) hH)
  refine ⟨?_, ?_, ?_⟩
  · simpa [sampledVertices, domainC, domainCState] using hu.1
  · simpa [recruitmentEdges, nonseeds, domainC, domainCState] using hu.2.1
  · intro v hv
    rw [hu.2.2 v hv]
    cases v <;> simp [recruitmentState, domainC, domainCState]

theorem no_h_region (D : Data) (H : State) (hH : Compatible D H)
    (hn : homophily H = none) : ¬ ∃ L U, FullHomophilyRegion D L U := by
  rintro ⟨L, U, hr⟩
  have hd := hr.1 H hH
  rw [homophily, if_pos hd] at hn
  cases hn

theorem leaf_flip_scalar (x y c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c)
    (hyc : 0 < 2*y+c) :
    wholePhi (x+1) y c - wholePhi x y (c+1) =
      2*(x+c+1)/((2*x+c+1)*(2*x+c+2)) +
      2*y/((2*y+c+1)*(2*y+c)) ∧
    0 < wholePhi (x+1) y c - wholePhi x y (c+1) := by
  have hx1 : 0 < 2*x+c+1 := by linarith
  have hx2 : 0 < 2*x+c+2 := by linarith
  have hy1 : 0 < 2*y+c+1 := by linarith
  have heq : wholePhi (x+1) y c - wholePhi x y (c+1) =
      2*(x+c+1)/((2*x+c+1)*(2*x+c+2)) +
      2*y/((2*y+c+1)*(2*y+c)) := by
    unfold wholePhi
    field_simp [ne_of_gt hx1, ne_of_gt hx2, ne_of_gt hy1, ne_of_gt hyc,
      show 2*(x+1)+c ≠ 0 by linarith,
      show 2*x+(c+1) ≠ 0 by linarith,
      show 2*y+(c+1) ≠ 0 by linarith]
    <;> ring
  refine ⟨heq, ?_⟩
  rw [heq]
  apply add_pos_of_pos_of_nonneg
  · exact div_pos (by linarith) (mul_pos hx1 hx2)
  · exact div_nonneg (by positivity) (le_of_lt (mul_pos hy1 hyc))

end
end SAP.P012b.WH.W1
