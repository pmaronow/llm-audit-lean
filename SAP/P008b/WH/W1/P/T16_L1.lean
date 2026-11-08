import SAP.P008b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b.WH.W1.P.T16_L1

open scoped BigOperators

noncomputable section

def square (c : ℝ) : Set Plane :=
  {x | |x 0 - c| ≤ (1 / 8 : ℝ) ∧ |x 1| ≤ (1 / 8 : ℝ)}

def center (c : ℝ) : Plane := WithLp.toLp 2 ![c, 0]

def strictSquare (c : ℝ) : Set Plane :=
  {x | |x 0 - c| < (1 / 8 : ℝ) ∧ |x 1| < (1 / 8 : ℝ)}

lemma square_closed (c : ℝ) : IsClosed (square c) := by
  have h0 : Continuous fun x : Plane => |x 0 - c| := by fun_prop
  have h1 : Continuous fun x : Plane => |x 1| := by fun_prop
  exact (isClosed_le h0 continuous_const).inter (isClosed_le h1 continuous_const)

lemma strictSquare_open (c : ℝ) : IsOpen (strictSquare c) := by
  have h0 : Continuous fun x : Plane => |x 0 - c| := by fun_prop
  have h1 : Continuous fun x : Plane => |x 1| := by fun_prop
  exact (isOpen_lt h0 continuous_const).inter (isOpen_lt h1 continuous_const)

lemma strictSquare_subset (c : ℝ) : strictSquare c ⊆ square c := by
  intro x hx
  simp only [strictSquare, square, Set.mem_setOf_eq] at hx ⊢
  exact ⟨hx.1.le, hx.2.le⟩

lemma square_frontier_nonempty_and_infDist (c : ℝ) :
    (frontier (square c)).Nonempty ∧
      Metric.infDist (center c) (frontier (square c)) = (1 / 8 : ℝ) := by
  let q : Plane := WithLp.toLp 2 ![c + (1 / 8 : ℝ), 0]
  have hclosed := square_closed c
  have hqmem : q ∈ square c := by
    change |q 0 - c| ≤ (1 / 8 : ℝ) ∧ |q 1| ≤ (1 / 8 : ℝ)
    norm_num [q, PiLp.toLp_apply]
  have hqnot : q ∉ interior (square c) := by
    intro hqi
    obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp isOpen_interior) q hqi
    let y : Plane := WithLp.toLp 2 ![c + (1 / 8 : ℝ) + ε / 2, 0]
    have hydist : dist q y = ε / 2 := by
      apply (sq_eq_sq₀ (dist_nonneg) (by positivity)).mp
      rw [EuclideanSpace.dist_sq_eq]
      norm_num [q, y, PiLp.toLp_apply, abs_of_pos hε]
    have hyball : y ∈ Metric.ball q ε := by
      rw [Metric.mem_ball, dist_comm, hydist]
      linarith
    have hys := interior_subset (hball hyball)
    change |y 0 - c| ≤ (1 / 8 : ℝ) ∧ |y 1| ≤ (1 / 8 : ℝ) at hys
    change |c + (1 / 8 : ℝ) + ε / 2 - c| ≤ (1 / 8 : ℝ) ∧
      |(0 : ℝ)| ≤ (1 / 8 : ℝ) at hys
    have harg : c + (1 / 8 : ℝ) + ε / 2 - c = (1 / 8 : ℝ) + ε / 2 := by ring
    have hfirst := hys.1
    rw [harg, abs_of_nonneg (by positivity)] at hfirst
    have : 0 < ε / 2 := by positivity
    linarith [hfirst]
  have hqfront : q ∈ frontier (square c) := by
    rw [hclosed.frontier_eq]
    exact ⟨hqmem, hqnot⟩
  have hqdist : dist (center c) q = (1 / 8 : ℝ) := by
    apply (sq_eq_sq₀ (dist_nonneg) (by norm_num)).mp
    rw [EuclideanSpace.dist_sq_eq]
    norm_num [center, q, PiLp.toLp_apply]
  have hside (x : Plane) (hx : x ∈ frontier (square c)) :
      |x 0 - c| = (1 / 8 : ℝ) ∨ |x 1| = (1 / 8 : ℝ) := by
    rw [hclosed.frontier_eq] at hx
    rcases hx with ⟨hxmem, hxnot⟩
    by_contra hnot
    push_neg at hnot
    have h0 : |x 0 - c| < (1 / 8 : ℝ) := by
      have := hxmem.1
      have hne : |x 0 - c| ≠ (1 / 8 : ℝ) := hnot.1
      by_contra hlt
      exact hnot.1 (le_antisymm hxmem.1 (le_of_not_gt hlt))
    have h1 : |x 1| < (1 / 8 : ℝ) := by
      have := hxmem.2
      have hne : |x 1| ≠ (1 / 8 : ℝ) := hnot.2
      by_contra hlt
      exact hnot.2 (le_antisymm hxmem.2 (le_of_not_gt hlt))
    have hxstrict : x ∈ strictSquare c := ⟨h0, h1⟩
    have hxinter : x ∈ interior (square c) :=
      (subset_interior_iff_isOpen.mpr (strictSquare_open c)).trans
        (interior_mono (strictSquare_subset c)) hxstrict
    exact hxnot hxinter
  have hlower : (1 / 8 : ℝ) ≤ Metric.infDist (center c) (frontier (square c)) := by
    apply (Metric.le_infDist ⟨q, hqfront⟩).mpr
    intro x hx
    rcases hside x hx with h0 | h1
    · have hn := PiLp.norm_apply_le (x - center c) 0
      have hn' : |x 0 - c| ≤ ‖x - center c‖ := by
        simpa [center, PiLp.sub_apply, PiLp.toLp_apply, Real.norm_eq_abs] using hn
      have hd : ‖x - center c‖ = dist (center c) x := by
        calc
          ‖x - center c‖ = dist x (center c) := (dist_eq_norm _ _).symm
          _ = dist (center c) x := dist_comm _ _
      rw [← hd]
      linarith
    · have hn := PiLp.norm_apply_le (x - center c) 1
      have hn' : |x 1| ≤ ‖x - center c‖ := by
        simpa [center, PiLp.sub_apply, PiLp.toLp_apply, Real.norm_eq_abs] using hn
      have hd : ‖x - center c‖ = dist (center c) x := by
        calc
          ‖x - center c‖ = dist x (center c) := (dist_eq_norm _ _).symm
          _ = dist (center c) x := dist_comm _ _
      rw [← hd]
      linarith
  have hupper : Metric.infDist (center c) (frontier (square c)) ≤ (1 / 8 : ℝ) := by
    calc
      Metric.infDist (center c) (frontier (square c)) ≤ dist (center c) q :=
        Metric.infDist_le_dist_of_mem hqfront
      _ = (1 / 8 : ℝ) := hqdist
  exact ⟨⟨q, hqfront⟩, le_antisymm hupper hlower⟩

end

end SAP.P008b.WH.W1.P.T16_L1

theorem SAP.P008b.WH.W1.T16_L1_proof : SAP.P008b.WH.W1.T16_L1 := by
  intro i
  simpa [SAP.P008b.wholeSquare,
    SAP.P008b.wholeSquareCenter,
    SAP.P008b.WH.W1.P.T16_L1.square,
    SAP.P008b.WH.W1.P.T16_L1.center] using
      SAP.P008b.WH.W1.P.T16_L1.square_frontier_nonempty_and_infDist
        (20 * (i : ℝ))
