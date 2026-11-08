import SAP.P012b.Defs.WholeW2
import SAP.P012b.Bridge
import AronowAudit.P012.P012_Identification
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
namespace SAP.P012b.WH.W2
open Finset Filter SAP.P012b.Bridge
open scoped Topology
noncomputable section
attribute [local simp] Finset.filter_insert Finset.image_insert Finset.sdiff_insert
  Finset.insert_sdiff_of_mem Finset.insert_sdiff_of_notMem Finset.insert_subset_iff
  Finset.filter_singleton Finset.image_singleton Finset.sdiff_singleton_eq_erase
  Finset.erase_insert_of_ne Finset.range_add_one
  AronowAudit.P012.pair_edge_eq
/-- Exchange of binary labels preserves the partial assortativity statistic on
every finite simple graph, including graphs on which it is undefined.
Route: exchange the two trait-degree totals and homogeneous edge counts; leave
the mixed count fixed. Use `homophily_domain` for the domain, then
`graph_homophily_formula` and the symmetry of `phi` for the defined value.
Treat zero edges separately. Estimated proof: 100-180 lines. -/ def T23_L1 : Prop := ∀ H : State, Simple H → homophily (wholeComplementState H) = homophily H
/-- Equality of matching traits gives preferential invariance by a short
finite-filter calculation, including equality of the partial domains. -/ private theorem complement_preferential (D : Data) (H : State) :
    preferential (wholeComplementData D) (wholeComplementState H) = preferential D H := by
  have hs (i j : ℕ) :
      susceptible (wholeComplementData D) (wholeComplementState H) i j = susceptible D H i j := rfl
  have hm (i j : ℕ) :
      sameSusceptible (wholeComplementData D) (wholeComplementState H) i j = sameSusceptible D H i j := by
    unfold sameSusceptible
    rw [hs]
    simp only [wholeComplementState, Bool.not_inj_iff]
  have hn : nonseeds (wholeComplementData D) = nonseeds D := rfl
  have hr : (wholeComplementData D).parent = D.parent := rfl
  have ht : (wholeComplementState H).trait = fun v => !(H.trait v) := rfl
  simp only [preferential, PreferentialDefined, pValue, pSum, hn, hs, hm, hr, ht, Bool.not_inj_iff]
private theorem retime_admissible (τ : ℕ → ℕ)
    (hτ : StrictMonoOn τ (↑figureData.sampled : Set ℕ)) :
    Admissible (wholeFigureData τ) := by
  have hD : Admissible figureData := AronowAudit.P012.figure1_endpoint_arithmetic.1
  refine ⟨hD.1, ?_, ?_, hD.2.2.2⟩
  · intro i hi j hj heq
    exact hτ.injOn hi hj heq
  · intro j hj
    have hr := hD.2.2.1 j hj
    exact ⟨hr.1, hτ hr.1 (Finset.mem_sdiff.mp hj).1 hr.2⟩
private theorem retime_susceptible (τ : ℕ → ℕ)
    (hτ : StrictMonoOn τ (↑figureData.sampled : Set ℕ)) (H : State)
    (i j : ℕ) (hj : j ∈ figureData.sampled) :
    susceptible (wholeFigureData τ) H i j = susceptible figureData H i j := by
  have hys (v : Vertex) :
      notYetSampled (wholeFigureData τ) j v = notYetSampled figureData j v := by
    cases v with
    | inr w => rfl
    | inl k =>
      change decide (k ∉ figureData.sampled ∨ τ j ≤ τ k) = decide (k ∉ figureData.sampled ∨ j ≤ k)
      by_cases hk : k ∈ figureData.sampled
      · simp only [hk, not_true_eq_false, false_or, hτ.le_iff_le hj hk]
      · simp only [hk, not_false_eq_true, true_or]
  unfold susceptible
  simp only [hys]
private theorem retime_preferential (τ : ℕ → ℕ)
    (hτ : StrictMonoOn τ (↑figureData.sampled : Set ℕ)) (H : State) :
    preferential (wholeFigureData τ) H = preferential figureData H := by
  have hn : nonseeds (wholeFigureData τ) = nonseeds figureData := rfl
  have hr : (wholeFigureData τ).parent = figureData.parent := rfl
  have hs (i j : ℕ) (hj : j ∈ nonseeds figureData) :
      susceptible (wholeFigureData τ) H i j = susceptible figureData H i j := retime_susceptible τ hτ H i j (Finset.mem_sdiff.mp hj).1
  have hm (i j : ℕ) (hj : j ∈ nonseeds figureData) :
      sameSusceptible (wholeFigureData τ) H i j = sameSusceptible figureData H i j := by
    unfold sameSusceptible
    rw [hs i j hj]
  have hd : PreferentialDefined (wholeFigureData τ) H ↔ PreferentialDefined figureData H := by
    simp only [PreferentialDefined, hn, hr]
    exact and_congr_right (fun _ => forall_congr' (fun j => forall_congr' (fun hj =>
      by rw [hs _ j hj])))
  have hsum : pSum (wholeFigureData τ) H = pSum figureData H := by
    unfold pSum
    simp only [hn, hr]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs _ j hj, hm _ j hj]
  simp only [preferential, hd, pValue, hsum, hn]
private theorem complement_data_twice (D : Data) :
    wholeComplementData (wholeComplementData D) = D := by
  cases D
  simp [wholeComplementData]
private theorem complement_state_twice (H : State) :
    wholeComplementState (wholeComplementState H) = H := by
  cases H
  simp [wholeComplementState]
private theorem complement_compatible (D : Data) (H : State) :
    Compatible (wholeComplementData D) (wholeComplementState H) ↔ Compatible D H := by
  constructor
  · intro h
    refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2⟩
    intro i hi
    exact Bool.not_inj_iff.mp (h.2.2.2.1 i hi)
  · intro h
    refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2⟩
    intro i hi
    exact congrArg Bool.not (h.2.2.2.1 i hi)
private theorem complement_relabeling (D : Data) (H K : State) :
    wholeRelabeling (wholeComplementData D) (wholeComplementState H)
      (wholeComplementState K) ↔ wholeRelabeling D H K := by
  constructor
  · rintro ⟨e, hf, hv, he, ht⟩
    refine ⟨e, hf, hv, he, ?_⟩
    intro v hv
    exact Bool.not_inj_iff.mp (ht v hv)
  · rintro ⟨e, hf, hv, he, ht⟩
    refine ⟨e, hf, hv, he, ?_⟩
    intro v hv
    exact congrArg Bool.not (ht v hv)
private theorem homophily_domain_of_some (H : State) (r : ℝ)
    (h : homophily H = some r) : HomophilyDefined H := by
  by_contra hn
  simp [homophily, hn] at h
private theorem preferential_domain_of_some (D : Data) (H : State) (r : ℝ)
    (h : preferential D H = some r) : PreferentialDefined D H := by
  by_contra hn
  simp [preferential, hn] at h
private theorem assertions_of_regions (D : Data) (hD : Admissible D)
    (hh : FullHomophilyRegion D (-5/8) (79/105))
    (hp : FullPreferentialRegion D (-11/80) (49/120))
    (hw : ∃ H K, Compatible D H ∧ Compatible D K ∧ preferential D H = some (-11/80) ∧ preferential D K = some (-11/80) ∧ ¬ wholeRelabeling D H K) : WholeFigure1Assertions D := by
  refine ⟨hD, hh, hp, ?_, hw⟩
  intro H hH
  have hhv : homophily H = some (hValue H) := ite_eq_left (hh.1 H hH)
  have hpv : preferential D H = some (pValue D H) := ite_eq_left (hp.1 H hH)
  have hmh : hValue H ∈ hValues D := ⟨H, hH, hhv⟩
  have hmp : pValue D H ∈ pValues D := ⟨H, hH, hpv⟩
  have hbH := And.intro (hh.2.1.2 hmh) (hh.2.2.2 hmh)
  have hbP := And.intro (hp.2.1.2 hmp) (hp.2.2.2 hmp)
  refine ⟨hhv, hpv, hbH, hbP, ?_, ?_⟩ <;> constructor <;> linarith [hbH.1, hbH.2, hbP.1, hbP.2]
private theorem complement_assertions (h1 : T23_L1)
    (D : Data) (ha : WholeFigure1Assertions D) :
    WholeFigure1Assertions (wholeComplementData D) := by
  have h2 := complement_preferential
  have hc (H : State) (hH : Compatible (wholeComplementData D) H) :
      Compatible D (wholeComplementState H) := by
    simpa only [complement_data_twice] using
      (complement_compatible (wholeComplementData D) H).mpr hH
  have hvh : hValues (wholeComplementData D) = hValues D := by
    ext r
    constructor
    · rintro ⟨H, hH, hr⟩
      exact ⟨wholeComplementState H, hc H hH, (h1 H hH.1.1).trans hr⟩
    · rintro ⟨H, hH, hr⟩
      exact ⟨wholeComplementState H, (complement_compatible D H).mpr hH, (h1 H hH.1.1).trans hr⟩
  have hvp : pValues (wholeComplementData D) = pValues D := by
    ext r
    constructor
    · rintro ⟨H, hH, hr⟩
      refine ⟨wholeComplementState H, hc H hH, ?_⟩
      simpa only [complement_data_twice] using (h2 (wholeComplementData D) H).trans hr
    · rintro ⟨H, hH, hr⟩
      exact ⟨wholeComplementState H, (complement_compatible D H).mpr hH, (h2 D H).trans hr⟩
  have hh : FullHomophilyRegion (wholeComplementData D) (-5/8) (79/105) := by
    refine ⟨?_, ?_⟩
    · intro H hH
      apply homophily_domain_of_some H (hValue (wholeComplementState H))
      exact (h1 H hH.1.1).symm.trans (ite_eq_left (ha.2.1.1 _ (hc H hH)))
    · simpa only [hvh] using ha.2.1.2
  have hp : FullPreferentialRegion (wholeComplementData D) (-11/80) (49/120) := by
    refine ⟨?_, ?_⟩
    · intro H hH
      apply preferential_domain_of_some (wholeComplementData D) H
        (pValue D (wholeComplementState H))
      have heq := h2 (wholeComplementData D) H
      rw [complement_data_twice] at heq
      exact heq.symm.trans (ite_eq_left (ha.2.2.1.1 _ (hc H hH)))
    · simpa only [hvp] using ha.2.2.1.2
  apply assertions_of_regions (wholeComplementData D) ha.1 hh hp
  obtain ⟨H, K, hH, hK, hpH, hpK, hn⟩ := ha.2.2.2.2
  exact ⟨wholeComplementState H, wholeComplementState K, (complement_compatible D H).mpr hH, (complement_compatible D K).mpr hK, (h2 D H).trans hpH, (h2 D K).trans hpK, fun hr => hn ((complement_relabeling D H K).mp hr)⟩
private theorem figure_arithmetic : WholeFigure1Arithmetic figureData := by
  norm_num [WholeFigure1Arithmetic, wholePContribution, wholeEdgeCount_W2, wholeMixedCount_W2, wholeTraitSpare, wholePhi_W2, recruitmentState, recruitmentDegree, recruitmentEdges, nonseeds, spare, sampledTraitDegree, sameSusceptible, susceptible, leafCompletion, leafVertices, leafEdges, sampledVertices, figureData, s, u, Finset.filter_insert, Finset.filter_singleton, Finset.image_insert, Finset.image_singleton]
private theorem retime_arithmetic (τ : ℕ → ℕ)
    (hτ : StrictMonoOn τ (↑figureData.sampled : Set ℕ)) :
    WholeFigure1Arithmetic (wholeFigureData τ) := by
  have hc (same : Bool) (j : ℕ) (hj : j ∈ figureData.sampled) :
      wholePContribution (wholeFigureData τ) (leafCompletion (wholeFigureData τ) same) j = wholePContribution figureData (leafCompletion figureData same) j := by
    change wholePContribution (wholeFigureData τ) (leafCompletion figureData same) j = _
    unfold wholePContribution sameSusceptible
    rw [retime_susceptible τ hτ _ _ j hj]
    rfl
  have hl (same : Bool) :
      [2,3,4,5].map (wholePContribution (wholeFigureData τ)
        (leafCompletion (wholeFigureData τ) same)) = [2,3,4,5].map (wholePContribution figureData (leafCompletion figureData same)) := by
    simp only [List.map_cons, List.map_nil, hc same 2 (by decide), hc same 3 (by decide), hc same 4 (by decide), hc same 5 (by decide)]
  unfold WholeFigure1Arithmetic
  rw [hl true, hl false]
  exact figure_arithmetic
private theorem figure_nonunique :
    ∃ H K, Compatible figureData H ∧ Compatible figureData K ∧ preferential figureData H = some (-11/80) ∧ preferential figureData K = some (-11/80) ∧ ¬ wholeRelabeling figureData H K := by
  have hd := AronowAudit.P012.figure1_endpoint_arithmetic
  have hH : Compatible figureData (leafCompletion figureData true) := by
    sap_transfer (AronowAudit.P012.leafCompletion_compatible _ hd.1 true)
  have hpH : preferential figureData (leafCompletion figureData true) = some (-11/80) := by
    have hp := (AronowAudit.P012.leaf_preferential_endpoints _ hd.1 (by decide)).1
    rw [hd.2.2.2.1] at hp
    sap_transfer hp
  have hK : Compatible figureData wholeFigureMerged := by decide
  have hpK : preferential figureData wholeFigureMerged = some (-11/80) := by
    norm_num [preferential, PreferentialDefined, pValue, pSum, sameSusceptible, susceptible, wholeFigureMerged, leafCompletion, leafVertices, leafEdges,
      sampledVertices, recruitmentEdges, nonseeds, spare, recruitmentDegree,
      figureData, s, u, Finset.filter_insert, Finset.filter_singleton,
      Finset.image_insert, Finset.image_singleton]
  refine ⟨_, _, hH, hK, hpH, hpK, ?_⟩
  rintro ⟨e, _, hv, _, _⟩
  have hcard := congrArg Finset.card hv
  rw [Finset.card_image_of_injective _ e.injective] at hcard
  have cH : (leafCompletion figureData true).vertices.card = 14 := by decide
  have cK : wholeFigureMerged.vertices.card = 13 := by decide
  omega
/-- Assemble the whole Figure 1 claim from the homophily invariance lemma.
Finite calculations, existing sharp bounds, and inequivalent extremizers are
proved here; none is left as a proof obligation for a writer. -/
theorem T23_assembly (h1 : T23_L1) :
    T23WholeStatement := by
  have hb : Admissible figureData ∧
      FullHomophilyRegion figureData (-5/8) (79/105) ∧
      FullPreferentialRegion figureData (-11/80) (49/120) := by
    sap_transfer AronowAudit.P012.figure1_extrema
  have ha := assertions_of_regions figureData hb.1 hb.2.1 hb.2.2 figure_nonunique
  intro τ hτ
  have hD := retime_admissible τ hτ
  have heq := retime_preferential τ hτ
  have hvp : pValues (wholeFigureData τ) = pValues figureData := by
    ext r
    simp only [pValues, heq]
    rfl
  have hp : FullPreferentialRegion (wholeFigureData τ) (-11/80) (49/120) := by
    refine ⟨?_, ?_⟩
    · intro H hH
      exact preferential_domain_of_some _ _ _ ((heq H).trans (ite_eq_left (hb.2.2.1 H hH)))
    · simpa only [hvp] using hb.2.2.2
  have hw : ∃ H K, Compatible (wholeFigureData τ) H ∧ Compatible (wholeFigureData τ) K ∧
      preferential (wholeFigureData τ) H = some (-11/80) ∧
      preferential (wholeFigureData τ) K = some (-11/80) ∧
      ¬ wholeRelabeling (wholeFigureData τ) H K := by
    obtain ⟨H, K, hH, hK, hpH, hpK, hn⟩ := ha.2.2.2.2
    exact ⟨H, K, hH, hK, (heq H).trans hpH, (heq K).trans hpK, hn⟩
  have ht := assertions_of_regions (wholeFigureData τ) hD hb.2.1 hp hw
  refine ⟨retime_arithmetic τ hτ, ht, complement_assertions h1 _ ht, ?_⟩
  intro H hH
  exact ⟨(complement_compatible _ _).mpr hH, h1 H hH.1.1, complement_preferential _ H⟩
/-- The literal printed annealing construction is refuted by an accepted
out-of-space proposal on ordinary-domain data. All ingredients are existing
project results or direct four-vertex arithmetic, so this target has no leaves. -/
theorem T24_assembly : T24WholeStatement := by
  have hw := AronowAudit.P012.proposal_counterexample
  have hD : Admissible wholeProposalData := hw.1
  have hH : Compatible wholeProposalData wholeProposalStart := hw.2.1
  have hP : Proposal wholeProposalData false wholeProposalStart wholeProposalBad := by
    exact (Proposal_eq _ _ _ _).mp (hw.2.2.2.1 false).1
  have hn : ¬ Compatible wholeProposalData wholeProposalBad := (hw.2.2.2.1 false).2
  have hh : homophily wholeProposalStart = some (-1/3) := hw.2.2.2.2.1
  have hp : preferential wholeProposalData wholeProposalStart = some (-1/2) := hw.2.2.2.2.2
  have hbadV : wholeProposalBad.vertices = {s 1, s 2, u 3 0, u 4 0} := by decide
  have hbadE : wholeProposalBad.edges = {{s 1,s 2},{s 1,u 4 0},{u 3 0,u 4 0}} := by decide
  have hbadZ : wholeProposalBad.trait = wholeProposalStart.trait := by
    funext v
    change Function.update wholeProposalStart.trait (u 4 0) false v = wholeProposalStart.trait v
    by_cases hv : v = u 4 0
    · subst v
      simp [wholeProposalStart, s, u]
    · simp only [Function.update_of_ne hv]
  have hbadH : homophily wholeProposalBad = some (-1/5) := by
    norm_num [homophily, HomophilyDefined, hValue, hNumerator, hDenominator,
      graphDegree, adjacency, z, hbadV, hbadE, hbadZ, wholeProposalStart, s, u,
      Finset.filter_insert, Finset.filter_singleton]
  have hbadP : preferential wholeProposalData wholeProposalBad = some (-1/2) := by
    norm_num [preferential, PreferentialDefined, pValue, pSum, susceptible,
      sameSusceptible, hbadV, hbadE, hbadZ, wholeProposalStart, wholeProposalData,
      nonseeds, s, u, Finset.filter_insert, Finset.filter_singleton]
  have hvH : hValue wholeProposalStart = -1/3 := by
    simpa only [homophily, ite_eq_left (homophily_domain_of_some _ _ hh), Option.some.injEq] using hh
  have hvK : hValue wholeProposalBad = -1/5 := by
    simpa only [homophily, ite_eq_left (homophily_domain_of_some _ _ hbadH), Option.some.injEq] using hbadH
  refine ⟨hD, ?_, hH, hP, hn, ?_, hh, hp, hbadH, hbadP, ?_,
    AronowAudit.P012.no_positive_nondecreasing_zero_limit,
    AronowAudit.P012.printed_first_temperature_undefined⟩
  · have h0 : 0 < sampledTraitDegree wholeProposalData false := by decide
    have h1 : 0 < sampledTraitDegree wholeProposalData true := by decide
    have hN : wholeProposalData.seeds.card < wholeProposalData.sampled.card := by decide
    intro H hC
    exact ⟨(AronowAudit.P012.full_domain_conditions (toData wholeProposalData) hD).mpr
        ⟨h0,h1⟩ (toState H) hC,
      (AronowAudit.P012.full_p_domain_conditions (toData wholeProposalData) hD).mpr
        hN (toState H) hC⟩
  · decide
  · intro ε T hε _hT
    refine ⟨?_, ?_, ?_⟩
    · rw [hvH]; linarith
    · rw [hvK]; linarith
    · exact lt_min (by norm_num) (Real.exp_pos _)
end
end SAP.P012b.WH.W2
