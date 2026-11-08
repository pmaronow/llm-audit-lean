import SAP.P001c.WH.W1.Leaves
import AronowAudit.P001.Wave1.Lib.TailA.CDFLinearImage

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001.Wave1
open AronowAudit.P001.Wave1.TailA
open scoped BigOperators ENNReal NNReal Topology Classical

theorem SAP.P001c.WH.W1.T57_L1_proof : SAP.P001c.WH.W1.T57_L1 := by
  intro mK bK P hP ν hν hbridge L
  classical
  obtain ⟨Y, hfin, hlim⟩ :=
    ta18_cdf_linear_approx (AronowAudit.P001.cdf P id)
      (cdf_value_totallyBounded P) L
  have hex (n : ℕ) : ∃ v : ℝ≥0, ν.map (Y n) = gaussianReal 0 v := by
    obtain ⟨r, x, a, hY⟩ := hfin n
    let v := ∑ j, ∑ k,
      a j * (min (AronowAudit.P001.cdf P id (x j))
        (AronowAudit.P001.cdf P id (x k)) -
        AronowAudit.P001.cdf P id (x j) * AronowAudit.P001.cdf P id (x k)) * a k
    refine ⟨⟨max v 0, le_max_right _ _⟩, ?_⟩
    rw [show (Y n : CDFSpace → ℝ) =
      (fun h => ∑ j, a j * h (x j)) from funext hY]
    exact (hbridge.2 r x a).2
  choose v hv using hex
  have hae : ∀ᵐ h ∂ν, Tendsto (fun n => Y n h) atTop (𝓝 (L h)) := by
    filter_upwards [ae_iff.mpr hbridge.1] with h hh
    exact hlim h hh
  obtain ⟨w, hw⟩ := ta18_centered_gaussian_ae_limit ν
    (fun n h => Y n h) (fun h => L h)
    (fun n => (Y n).continuous.aemeasurable) L.continuous.aemeasurable
    v hv hae
  have hmap : MemLp id 2 (ν.map L) := by
    rw [hw]
    exact memLp_id_gaussianReal 2
  exact hmap.comp_of_map L.continuous.aemeasurable

