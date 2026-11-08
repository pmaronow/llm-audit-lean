import SAP.P012a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W2.P.T6_L1

open SAP.P012a Finset
open scoped Classical

theorem recruitment_trait_degree_sum (D : Data) (z : Bool) :
    (∑ i ∈ D.sampled.filter (fun i => D.trait i = z), recruitmentDegree D i) =
      traitDegree (recruitmentState D) z := by
  have hf : (recruitmentState D).vertices.filter
      (fun v => (recruitmentState D).trait v = z) =
      (D.sampled.filter (fun i => D.trait i = z)).image s := by
    change (D.sampled.image s).filter
      (fun v => (recruitmentState D).trait v = z) = _
    rw [Finset.filter_image]
    rfl
  unfold traitDegree
  rw [hf]
  rw [Finset.sum_image (by
    intro i hi j hj h
    exact Sum.inl.inj h)]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

end SAP.P012a.WH.W2.P.T6_L1

open SAP.P012a Finset
open scoped Classical

theorem SAP.P012a.WH.W2.T6_L1_proof : SAP.P012a.WH.W2.T6_L1 := by
  intro D hD
  have hD' : AronowAudit.P012.Admissible (SAP.P012a.Bridge.data D) := by
    simpa only [SAP.P012a.Bridge.Admissible_eq] using hD
  have hbin' := AronowAudit.P012.binary_edge_counts
    (AronowAudit.P012.recruitmentState (SAP.P012a.Bridge.data D))
    (AronowAudit.P012.recruitment_skeleton_counts (SAP.P012a.Bridge.data D) hD').1
  have hbin1 : traitDegree (recruitmentState D) true =
      2 * edgeCount (recruitmentState D) true + mixedCount (recruitmentState D) := by
    simpa only [SAP.P012a.Bridge.recruitmentState_eq,
      SAP.P012a.Bridge.traitDegree_eq, SAP.P012a.Bridge.edgeCount_eq,
      SAP.P012a.Bridge.mixedCount_eq] using hbin'.1
  have hbin0 : traitDegree (recruitmentState D) false =
      2 * edgeCount (recruitmentState D) false + mixedCount (recruitmentState D) := by
    simpa only [SAP.P012a.Bridge.recruitmentState_eq,
      SAP.P012a.Bridge.traitDegree_eq, SAP.P012a.Bridge.edgeCount_eq,
      SAP.P012a.Bridge.mixedCount_eq] using hbin'.2.1
  have hpoint : ∀ z : Bool, ∀ i ∈ D.sampled.filter (fun i => D.trait i = z),
      D.degree i = recruitmentDegree D i + spare D i := by
    intro z i hi
    exact (Nat.add_sub_of_le (hD.2.2.2 i (mem_filter.mp hi).1)).symm
  have hsum : ∀ z : Bool,
      sampledTraitDegree D z =
        (∑ i ∈ D.sampled.filter (fun i => D.trait i = z), recruitmentDegree D i) +
          traitSpare D z := by
    intro z
    unfold sampledTraitDegree traitSpare
    calc
      (∑ i ∈ D.sampled.filter (fun i => D.trait i = z), D.degree i) =
          ∑ i ∈ D.sampled.filter (fun i => D.trait i = z),
            (recruitmentDegree D i + spare D i) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hpoint z i hi
      _ = (∑ i ∈ D.sampled.filter (fun i => D.trait i = z), recruitmentDegree D i) +
          ∑ i ∈ D.sampled.filter (fun i => D.trait i = z), spare D i :=
            Finset.sum_add_distrib
  constructor
  · calc
      sampledTraitDegree D false =
          (∑ i ∈ D.sampled.filter (fun i => D.trait i = false), recruitmentDegree D i) +
            traitSpare D false := hsum false
      _ = 2 * b D + cR D + traitSpare D false := by
        rw [SAP.P012a.WH.W2.P.T6_L1.recruitment_trait_degree_sum, hbin0]
        rfl
  · calc
      sampledTraitDegree D true =
          (∑ i ∈ D.sampled.filter (fun i => D.trait i = true), recruitmentDegree D i) +
            traitSpare D true := hsum true
      _ = 2 * a D + cR D + traitSpare D true := by
        rw [SAP.P012a.WH.W2.P.T6_L1.recruitment_trait_degree_sum, hbin1]
        rfl

