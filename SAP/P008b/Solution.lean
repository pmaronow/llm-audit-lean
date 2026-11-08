import SAP.P008b.WH.W1.Proofs.T22
import SAP.P008b.WH.W1.Proofs.T25
import SAP.P008b.WH.W1.Proofs.T26
import SAP.P008b.WH.W1.Proofs.T15
import SAP.P008b.WH.W2.Proofs.T17
import SAP.P008b.WH.W2.Proofs.T18
import SAP.P008b.WH.W2.Proofs.T27
import SAP.P008b.WH.W3.Proofs.T16
import SAP.P008b.Defs
import SAP.P008b.Bridge
import AronowAudit.P008.P008_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b

open scoped BigOperators
open MeasureTheory Filter

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem T15 : SAP.P008b.T15WholeStatement := SAP.P008b.WH.W1.T15_whole

theorem T16 : SAP.P008b.T16WholeStatement_W3 := SAP.P008b.WH.W3.T16_whole

theorem T17 : SAP.P008b.T17WholeStatement := SAP.P008b.WH.W2.T17_whole

theorem T18 : SAP.P008b.T18WholeStatement := SAP.P008b.WH.W2.T18_whole

theorem T19 : T19Statement := by
  have h := AronowAudit.P008.polygon_raster_counterexample
  have hc : ∀ i, (rasterPolygonCells i).card = 25 ∧
      (rasterPolygonBoundary i).card = 16 := h.2.1
  have ha : ∀ i z, polygonRasterAreaM i z =
      if i = 0 then (9 / 25 : ℝ) * bit (z 0) else 0 := h.2.2.2.2.2.1
  refine ⟨h, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hs : rasterPolygonBoundary i ⊆ rasterPolygonCells i := Finset.filter_subset _ _
    rw [Finset.card_sdiff_of_subset hs, (hc i).1, (hc i).2]
  · intro i
    have hm := ha i ![true, false]
    unfold polygonRasterAreaM countMean at hm
    rw [(hc i).1] at hm
    by_cases hi : i = 0 <;> simp only [hi, ite_true, ite_false] at hm ⊢ <;>
      norm_num [bit] at hm <;> linarith
  · intro i
    have ht : (fun z => polygonRasterAreaM i (Function.update z i true)) =
        (fun _ : Assignment 2 => if i = 0 then (9 / 25 : ℝ) else 0) := by
      funext z
      rw [ha]
      by_cases hi : i = 0 <;> simp [hi, bit]
    have hf : (fun z => polygonRasterAreaM i (Function.update z i false)) =
        (fun _ : Assignment 2 => (0 : ℝ)) := by
      funext z
      rw [ha]
      by_cases hi : i = 0 <;> simp [hi, bit]
    have he (c : ℝ) : (uniformLaw (Assignment 2)).expect (fun _ => c) = c :=
      AronowAudit.P008.expect_const (Bridge.law (uniformLaw (Assignment 2))) c
    change (uniformLaw (Assignment 2)).expect _ - (uniformLaw (Assignment 2)).expect _ = _
    rw [ht, hf, he, he, sub_zero]
  · norm_num [nTreated, bit, Fin.sum_univ_succ]
  · norm_num [nControl, nTreated, bit, Fin.sum_univ_succ]

theorem T20 : T20Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R Y hbd
    exact AronowAudit.P008.raster_zero_summaries R Y hbd
  · have h := AronowAudit.P008.boundary_counterexample
    have hn := AronowAudit.P008.block_boundary_is_eight_neighbour
    exact ⟨h.1, h.2.1, h.2.2.1, hn.1, hn.2⟩
  · exact AronowAudit.P008.zero_distance_is_boundary
  · obtain ⟨_, _, _, _, _, _, _, _, he, ha, ae, aa, _⟩ :=
      AronowAudit.P008.polygon_raster_counterexample
    exact ⟨he, ha, ae, aa⟩

theorem T21 : T21Statement := by
  exact AronowAudit.P008.uganda_printed_comparison

theorem T22 : SAP.P008b.T22WholeStatement := SAP.P008b.WH.W1.T22_whole

theorem T23 : T23Statement := by
  intro Ω _ N Q φ D c hz
  exact AronowAudit.P008.dependence_cutoff_identity (Bridge.law Q) φ D c hz

theorem T25 : SAP.P008b.T25WholeStatement := SAP.P008b.WH.W1.T25_whole

theorem T26 : SAP.P008b.T26WholeStatement := SAP.P008b.WH.W1.T26_whole

theorem T27 : SAP.P008b.T27WholeStatement := SAP.P008b.WH.W2.T27_whole

theorem T28 : T28Statement := by
  intro Q M p H exceptional D hp hp' hH hQ hb hd
  exact AronowAudit.P008.sufficient_hajek_consistency
    (fun n => Bridge.law (Q n)) M p H exceptional D hp hp' hH hQ hb hd

end SAP.P008b
