import SAP.P061a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a.WH.W1.P.T4_L2

open scoped BigOperators Classical

private theorem pairIndex_ne {K : ℕ} (i j : Fin (K*2))
    (hij : i ≠ j) (hjp : j ≠ SAP.P061a.partnerIndexW1 K i) :
    (finProdFinEquiv.symm i).1 ≠ (finProdFinEquiv.symm j).1 := by
  intro hpair
  let a := finProdFinEquiv.symm i
  let b := finProdFinEquiv.symm j
  have ha : a.2 = 0 ∨ a.2 = 1 := by omega
  have hb : b.2 = 0 ∨ b.2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · have hab : a = b := Prod.ext hpair (ha.trans hb.symm)
    exact hij (finProdFinEquiv.symm.injective (by simpa [a, b] using hab))
  · have hab : b = (a.1, if a.2 = 0 then 1 else 0) := by
      apply Prod.ext
      · exact hpair.symm
      · simp [ha, hb]
    have hs : finProdFinEquiv.symm j = finProdFinEquiv.symm
        (SAP.P061a.partnerIndexW1 K i) := by
      simpa [a, b, SAP.P061a.partnerIndexW1] using hab
    exact hjp (finProdFinEquiv.symm.injective hs)
  · have hab : b = (a.1, if a.2 = 0 then 1 else 0) := by
      apply Prod.ext
      · exact hpair.symm
      · simp [ha, hb]
    have hs : finProdFinEquiv.symm j = finProdFinEquiv.symm
        (SAP.P061a.partnerIndexW1 K i) := by
      simpa [a, b, SAP.P061a.partnerIndexW1] using hab
    exact hjp (finProdFinEquiv.symm.injective hs)
  · have hab : a = b := Prod.ext hpair (ha.trans hb.symm)
    exact hij (finProdFinEquiv.symm.injective (by simpa [a, b] using hab))

private theorem project_eq_local (m : ℕ) (hm : 2 ≤ m)
    (D : AtomicDesign (Fin (m^8) → BitPair))
    (hD : ∀ z, D.mass z = ∏ k : Fin (m^8),
      if (z k).1 = (z k).2 then (1+pairParameter m)/4 else (1-pairParameter m)/4) :
    Bridge.toProject D = AronowAudit.P061.localDesign m := by
  apply Bridge.project_design_ext
  funext z
  change D.mass z = _
  rw [hD z]
  simp [Bridge.toProject, AronowAudit.P061.localDesign,
    AronowAudit.P061.productDesign, AronowAudit.P061.correlatedPairDesign,
    AronowAudit.P061.localParameter, pairParameter, hm]

private theorem local_independent_of_pairIndex_ne (m : ℕ)
    (i j : Fin (m^8*2))
    (hij : (finProdFinEquiv.symm i).1 ≠ (finProdFinEquiv.symm j).1) :
    AronowAudit.P061.Independent (AronowAudit.P061.localDesign m)
      (pairedOwnBit (m^8) i) (pairedOwnBit (m^8) j) := by
  let a := finProdFinEquiv.symm i
  let b := finProdFinEquiv.symm j
  let q := AronowAudit.P061.correlatedPairDesign
    (AronowAudit.P061.localParameter m)
    (AronowAudit.P061.local_parameter_bounds m)
  change ∀ E F, _
  intro E F
  have h := AronowAudit.P061.product_coordinate_independent (m^8)
    (fun _ => q) a.1 (AronowAudit.P061.pairAssignment a.2)
    E (fun w => F (AronowAudit.P061.pairAssignment b.2
      (w ⟨b.1, fun hh => hij hh.symm⟩)))
  simpa [AronowAudit.P061.localDesign, AronowAudit.P061.pairedAssignment,
    pairedOwnBit, a, b, q, ownBit, AronowAudit.P061.pairAssignment] using h

private theorem local_partner_joint (m : ℕ) (hm : 2 ≤ m) (i : Fin (m^8*2)) :
    AronowAudit.P061.probability (AronowAudit.P061.localDesign m)
      (fun z => pairedOwnBit (m^8) i z = 1 ∧
        pairedOwnBit (m^8) (SAP.P061a.partnerIndexW1 (m^8) i) z = 1) =
      (1 + 1/(m : ℝ))/4 := by
  let a := finProdFinEquiv.symm i
  let q := AronowAudit.P061.correlatedPairDesign
    (AronowAudit.P061.localParameter m)
    (AronowAudit.P061.local_parameter_bounds m)
  have ha : AronowAudit.P061.localParameter m = 1/(m : ℝ) := by
    simp [AronowAudit.P061.localParameter, hm]
  have he : AronowAudit.P061.probability (AronowAudit.P061.localDesign m)
      (fun z => pairedOwnBit (m^8) i z = 1 ∧
        pairedOwnBit (m^8) (SAP.P061a.partnerIndexW1 (m^8) i) z = 1) =
      AronowAudit.P061.probability q (fun w =>
        ownBit a.2 w = 1 ∧
          ownBit (if a.2 = 0 then 1 else 0) w = 1) := by
    calc
      _ = AronowAudit.P061.probability (AronowAudit.P061.productDesign (m^8) (fun _ => q))
          (fun z => ownBit a.2 (z a.1) = 1 ∧
            ownBit (if a.2 = 0 then 1 else 0) (z a.1) = 1) := by
        congr 1
        funext z
        simp [AronowAudit.P061.localDesign, pairedOwnBit,
          SAP.P061a.partnerIndexW1, a, ownBit, AronowAudit.P061.pairAssignment]
      _ = _ := AronowAudit.P061.coordinate_probability (m^8) (fun _ => q) a.1
        (fun w => ownBit a.2 w = 1 ∧
          ownBit (if a.2 = 0 then 1 else 0) w = 1)
  rw [he]
  generalize hs : a.2 = s
  fin_cases s <;>
    norm_num [AronowAudit.P061.probability, q,
      AronowAudit.P061.correlatedPairDesign, AronowAudit.P061.pairAssignment,
      ownBit, AronowAudit.P061.localParameter, hm,
      tsum_fintype, Fintype.sum_prod_type,
      Fin.sum_univ_two] <;> ring

end SAP.P061a.WH.W1.P.T4_L2

theorem SAP.P061a.WH.W1.T4_L2_proof : SAP.P061a.WH.W1.T4_L2 := by
  intro m hm D hD i j
  let K := m^8
  have hproj := SAP.P061a.WH.W1.P.T4_L2.project_eq_local m hm D hD
  constructor
  · rintro ⟨hij, hni⟩
    by_contra hjp
    have hkl : (finProdFinEquiv.symm i).1 ≠ (finProdFinEquiv.symm j).1 :=
      SAP.P061a.WH.W1.P.T4_L2.pairIndex_ne i j hij hjp
    have hlocal := SAP.P061a.WH.W1.P.T4_L2.local_independent_of_pairIndex_ne m i j hkl
    have hDind : independent D (pairedOwnBit K i) (pairedOwnBit K j) := by
      intro E F
      simpa only [Bridge.probability_correspondence, hproj] using hlocal E F
    exact hni hDind
  · intro hjp
    subst j
    have hnot : i ≠ partnerIndexW1 K i := by
      intro heq
      have hs := congrArg finProdFinEquiv.symm heq
      have ht : (finProdFinEquiv.symm i).2 = 0 ∨ (finProdFinEquiv.symm i).2 = 1 := by omega
      rcases ht with ht | ht
      · have ht' : i.modNat = 0 := by simpa using ht
        simp [partnerIndexW1, ht'] at hs
      · have ht' : i.modNat = 1 := by simpa using ht
        simp [partnerIndexW1, ht'] at hs
    refine ⟨hnot, ?_⟩
    intro hInd
    have hlocalInd : AronowAudit.P061.Independent (AronowAudit.P061.localDesign m)
        (pairedOwnBit K i) (pairedOwnBit K (partnerIndexW1 K i)) := by
      intro E F
      have h := hInd E F
      simpa only [Bridge.probability_correspondence, hproj] using h
    have hjoint := hlocalInd (fun x => x = 1) (fun x => x = 1)
    have hmargin1 : AronowAudit.P061.probability (AronowAudit.P061.localDesign m)
        (fun z => pairedOwnBit K i z = 1) = 1/2 := by
      change AronowAudit.P061.pi (AronowAudit.P061.localDesign m)
        (AronowAudit.P061.pairedAssignment K) i 1 = 1/2
      exact (AronowAudit.P061.local_assignment_marginals m i).1
    have hmargin2 : AronowAudit.P061.probability (AronowAudit.P061.localDesign m)
        (fun z => pairedOwnBit K (partnerIndexW1 K i) z = 1) = 1/2 := by
      change AronowAudit.P061.pi (AronowAudit.P061.localDesign m)
        (AronowAudit.P061.pairedAssignment K) (partnerIndexW1 K i) 1 = 1/2
      exact (AronowAudit.P061.local_assignment_marginals m (partnerIndexW1 K i)).1
    rw [SAP.P061a.WH.W1.P.T4_L2.local_partner_joint m hm i, hmargin1, hmargin2] at hjoint
    have hpos : 0 < (1/(m:ℝ)) := by positivity
    linarith
