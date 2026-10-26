import AronowAudit.P011.Wave1.PropositionOneBlueprint

/-!
The path dependency proof uses the complete tuples on separated vertex sets.
A source coordinate can be shared only by the same vertex or two adjacent vertices.
-/

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PropositionOne

open AronowAudit.P011 MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

theorem n3_proof : N3 := by
  classical
  intro h1 K
  -- Sign 0 feeds local vertices 0 and 1; sign 1 feeds local vertices 1 and 2.
  let uses (i : Fin (3 * K)) (p : Fin K × Fin 2) : Prop :=
    blockIndex (by decide : 0 < 3) i = p.1 ∧
      ((p.2 = 0 ∧ localIndex (by decide : 0 < 3) i ≠ 2) ∨
       (p.2 = 1 ∧ localIndex (by decide : 0 < 3) i ≠ 0))
  let sources (S : Finset (Fin (3 * K))) : Finset (Fin K × Fin 2) :=
    Finset.univ.filter (fun p => ∃ i ∈ S, uses i p)
  have hmask : ∀ (r s : Fin 3) (c : Fin 2),
      ((c = 0 ∧ r ≠ 2) ∨ (c = 1 ∧ r ≠ 0)) →
      ((c = 0 ∧ s ≠ 2) ∨ (c = 1 ∧ s ≠ 0)) →
      r = s ∨ pathGraph.val r s = true := by
    decide
  have hcoordinate (r : Fin 3) (U V U' V' : Bool)
      (hU : r ≠ 2 → U = U') (hV : r ≠ 0 → V = V') :
      pathBlock 2 (sign U) (sign V) r = pathBlock 2 (sign U') (sign V') r := by
    fin_cases r
    · simp [pathBlock, hU (by decide)]
    · rw [hU (by decide), hV (by decide)]
    · simp [pathBlock, hV (by decide)]
  have hdepends (S : Finset (Fin (3 * K)))
      (u v : Fin K → Fin 2 → Bool)
      (huv : ∀ p ∈ sources S, u p.1 p.2 = v p.1 p.2) :
      (fun i : {i // i ∈ S} => pathSource K u i.val) =
        (fun i : {i // i ∈ S} => pathSource K v i.val) := by
    funext i
    unfold pathSource
    apply hcoordinate
    · intro hr
      apply huv (blockIndex (by decide) i.val, 0)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, i.val, i.property, ?_⟩
      exact ⟨rfl, Or.inl ⟨rfl, hr⟩⟩
    · intro hr
      apply huv (blockIndex (by decide) i.val, 1)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, i.val, i.property, ?_⟩
      exact ⟨rfl, Or.inr ⟨rfl, hr⟩⟩

  unfold Dependency VariableDependency
  intro S T hST hsep
  have hsource_disjoint : Disjoint (sources S) (sources T) := by
    apply Finset.disjoint_left.mpr
    intro p hpS hpT
    obtain ⟨i, hiS, hi⟩ := (Finset.mem_filter.mp hpS).2
    obtain ⟨j, hjT, hj⟩ := (Finset.mem_filter.mp hpT).2
    have hblock : blockIndex (by decide : 0 < 3) i = blockIndex (by decide) j :=
      hi.1.trans hj.1.symm
    have hquot : i.val / 3 = j.val / 3 := congrArg Fin.val hblock
    rcases hmask (localIndex (by decide) i) (localIndex (by decide) j) p.2 hi.2 hj.2
      with hlocal | hedge
    · have hmod : i.val % 3 = j.val % 3 := congrArg Fin.val hlocal
      have hij : i = j := by
        apply Fin.ext
        calc
          i.val = i.val % 3 + 3 * (i.val / 3) := (Nat.mod_add_div i.val 3).symm
          _ = j.val % 3 + 3 * (j.val / 3) := by rw [hmod, hquot]
          _ = j.val := Nat.mod_add_div j.val 3
      have hiT : i ∈ T := by
        rw [hij]
        exact hjT
      exact Finset.disjoint_left.mp hST hiS hiT
    · have hG : (pathModel 2 K).G.val i j = true := by
        change (decide (i.val / 3 = j.val / 3) &&
          pathGraph.val (localIndex (by decide) i) (localIndex (by decide) j)) = true
        simp [hquot, hedge]
      have hfalse := hsep i hiS j hjT
      rw [hG] at hfalse
      cases hfalse
  have hi : IndepFun
      (fun u : Fin K → Fin 2 → Bool => fun i : {i // i ∈ S} => pathSource K u i.val)
      (fun u : Fin K → Fin 2 → Bool => fun j : {j // j ∈ T} => pathSource K u j.val)
      (PMF.uniformOfFintype (Fin K → Fin 2 → Bool)).toMeasure :=
    h1 K (sources S) (sources T) hsource_disjoint _ _ (hdepends S) (hdepends T)

  -- Push the whole tuple independence statement to the raw outcome space.
  let f : (Fin (3 * K) → ℝ) → ({i // i ∈ S} → ℝ) := fun y i => y i.val
  let g : (Fin (3 * K) → ℝ) → ({j // j ∈ T} → ℝ) := fun y j => y j.val
  have hf : Measurable f := Measurable.of_eval (fun i => measurable_pi_apply i.val)
  have hg : Measurable g := Measurable.of_eval (fun j => measurable_pi_apply j.val)
  have hsource : Measurable (pathSource K) := measurable_of_finite _
  change IndepFun f g (uniformLaw (pathSource K))
  unfold uniformLaw
  rw [← PMF.toMeasure_map (pathSource K)
    (PMF.uniformOfFintype (Fin K → Fin 2 → Bool)) hsource]
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have hfs : MeasurableSet (f ⁻¹' s) := hs.preimage hf
  have hgt : MeasurableSet (g ⁻¹' t) := ht.preimage hg
  rw [Measure.map_apply hsource (hfs.inter hgt), Measure.map_apply hsource hfs,
    Measure.map_apply hsource hgt]
  simpa only [Set.preimage_inter, Set.preimage_preimage, Function.comp_def, f, g] using
    hi.measure_inter_preimage_eq_mul s t hs ht

end

end AronowAudit.P011.Wave1.PropositionOne
