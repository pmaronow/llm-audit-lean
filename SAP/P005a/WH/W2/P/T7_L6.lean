import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace SAP.P005a.WH.W2.P.T7_L6

open Finset SAP.P005a.Bridge
open scoped BigOperators

noncomputable section

private def xsum (S : Finset (Fin 12)) : ℤ :=
  ∑ i ∈ (S.filter (fun i => i.val ≠ 0)), ((i.val : ℤ) - 6)

private def xsum2 (S : Finset (Fin 12)) : ℤ :=
  ∑ i ∈ (S.filter (fun i => i.val ≠ 0)), (((i.val : ℤ) - 6)^2)

private def cnum (S : Finset (Fin 12)) : ℤ :=
  6*xsum2 S - 720*xsum S - xsum S^2

private def dnum (S : Finset (Fin 12)) : ℤ :=
  2592000 + 6*xsum2 S - 1440*xsum S - xsum S^2

private def rnum (S : Finset (Fin 12)) : ℤ :=
  xsum S*dnum S*4321 - (xsum S+360)*cnum S*4321 -
    12*30*dnum S*4321 - (288*xsum S-24)*30*dnum S

private def rden (S : Finset (Fin 12)) : ℤ := 30*dnum S*4321

private theorem integer_certificate :
    ∀ S : Finset (Fin 12), S.card = 6 → (0 : Fin 12) ∈ S →
      0 < dnum S ∧ 0 < rden S ∧
        8690712840 * rden S ≤ 752921287 * |rnum S| := by decide

private def z12 : Fin 12 := ⟨0, by omega⟩

private theorem ordinary_filter_eq_erase (S : Finset (Fin 12)) :
    S.filter (fun i => i.val ≠ 0) = S.erase z12 := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_erase]
  have hi : i.val ≠ 0 ↔ i ≠ z12 := by
    constructor
    · intro h he
      subst i
      exact h rfl
    · intro h hv
      apply h
      exact Fin.ext hv
  simp [hi, and_comm]

private theorem spikeV_ordinary (i : Fin 12) (hi : i ≠ z12) :
    SAP.P005a.spikeV 12 i = ((i.val : ℝ)-6)/5 := by
  have hne : i.val ≠ 0 := by
    intro hv
    apply hi
    exact Fin.ext hv
  have hge : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hne
  simp only [SAP.P005a.spikeV, if_neg hne]
  rw [Nat.cast_sub hge]
  norm_num
  ring_nf

private theorem spikeA_ordinary (i : Fin 12) (hi : i ≠ z12) :
    SAP.P005a.spikeA 12 i = SAP.P005a.spikeV 12 i / 144 := by
  have hne : i.val ≠ 0 := by
    intro hv
    apply hi
    exact Fin.ext hv
  norm_num [SAP.P005a.spikeA, hne]

private theorem spikeV_sum (S : Finset (Fin 12)) (hzero : z12 ∈ S) :
    (∑ i ∈ S, SAP.P005a.spikeV 12 i) = (xsum S : ℝ)/5 := by
  have hfilter := ordinary_filter_eq_erase S
  calc
    (∑ i ∈ S, SAP.P005a.spikeV 12 i) =
        SAP.P005a.spikeV 12 z12 + ∑ i ∈ S.erase z12, SAP.P005a.spikeV 12 i := by
          exact (Finset.add_sum_erase S (fun i => SAP.P005a.spikeV 12 i) hzero).symm
    _ = 0 + ∑ i ∈ S.erase z12, ((i.val : ℝ)-6)/5 := by
          have hz : SAP.P005a.spikeV 12 z12 = 0 := by norm_num [SAP.P005a.spikeV, z12]
          have ht : (∑ i ∈ S.erase z12, SAP.P005a.spikeV 12 i) =
              ∑ i ∈ S.erase z12, ((i.val : ℝ)-6)/5 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact spikeV_ordinary i (Finset.ne_of_mem_erase hi)
          rw [hz, ht]
    _ = (xsum S : ℝ)/5 := by
          rw [← hfilter]
          simp only [xsum]
          push_cast
          rw [Finset.sum_div]
          ring

private theorem spikeV_sq_sum (S : Finset (Fin 12)) (hzero : z12 ∈ S) :
    (∑ i ∈ S, (SAP.P005a.spikeV 12 i)^2) = (xsum2 S : ℝ)/25 := by
  have hfilter := ordinary_filter_eq_erase S
  calc
    (∑ i ∈ S, (SAP.P005a.spikeV 12 i)^2) =
        (SAP.P005a.spikeV 12 z12)^2 + ∑ i ∈ S.erase z12, (SAP.P005a.spikeV 12 i)^2 := by
          exact (Finset.add_sum_erase S (fun i => (SAP.P005a.spikeV 12 i)^2) hzero).symm
    _ = 0 + ∑ i ∈ S.erase z12, (((i.val : ℝ)-6)^2)/25 := by
          have hz : (SAP.P005a.spikeV 12 z12)^2 = 0 := by norm_num [SAP.P005a.spikeV, z12]
          have ht : (∑ i ∈ S.erase z12, (SAP.P005a.spikeV 12 i)^2) =
              ∑ i ∈ S.erase z12, (((i.val : ℝ)-6)^2)/25 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [spikeV_ordinary i (Finset.ne_of_mem_erase hi)]
            ring
          rw [hz, ht]
    _ = (xsum2 S : ℝ)/25 := by
          rw [← hfilter]
          simp only [xsum2]
          push_cast
          rw [Finset.sum_div]
          ring

private theorem spikeA_sum (S : Finset (Fin 12)) (hzero : z12 ∈ S) :
    (∑ i ∈ S, SAP.P005a.spikeA 12 i) = 1 + (xsum S : ℝ)/720 := by
  have hfilter := ordinary_filter_eq_erase S
  calc
    (∑ i ∈ S, SAP.P005a.spikeA 12 i) =
        SAP.P005a.spikeA 12 z12 + ∑ i ∈ S.erase z12, SAP.P005a.spikeA 12 i := by
          exact (Finset.add_sum_erase S (fun i => SAP.P005a.spikeA 12 i) hzero).symm
    _ = 1 + (∑ i ∈ S.erase z12, SAP.P005a.spikeV 12 i)/144 := by
          have hz : SAP.P005a.spikeA 12 z12 = 1 := by norm_num [SAP.P005a.spikeA, z12]
          have ht : (∑ i ∈ S.erase z12, SAP.P005a.spikeA 12 i) =
              (∑ i ∈ S.erase z12, SAP.P005a.spikeV 12 i)/144 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i hi
            exact spikeA_ordinary i (Finset.ne_of_mem_erase hi)
          rw [hz, ht]
    _ = 1 + (xsum S : ℝ)/720 := by
          have hv := spikeV_sum S hzero
          have hzv : SAP.P005a.spikeV 12 z12 = 0 := by norm_num [SAP.P005a.spikeV, z12]
          have he : (∑ i ∈ S.erase z12, SAP.P005a.spikeV 12 i) =
              ∑ i ∈ S, SAP.P005a.spikeV 12 i := by
            have ha := Finset.add_sum_erase S (fun i => SAP.P005a.spikeV 12 i) hzero
            simpa [hzv] using ha
          rw [he, hv]
          ring

private theorem spikeAV_sum (S : Finset (Fin 12)) (hzero : z12 ∈ S) :
    (∑ i ∈ S, SAP.P005a.spikeA 12 i * SAP.P005a.spikeV 12 i) =
      (xsum2 S : ℝ)/3600 := by
  have hfilter := ordinary_filter_eq_erase S
  calc
    (∑ i ∈ S, SAP.P005a.spikeA 12 i * SAP.P005a.spikeV 12 i) =
        SAP.P005a.spikeA 12 z12 * SAP.P005a.spikeV 12 z12 +
          ∑ i ∈ S.erase z12, SAP.P005a.spikeA 12 i * SAP.P005a.spikeV 12 i := by
          exact (Finset.add_sum_erase S (fun i => SAP.P005a.spikeA 12 i * SAP.P005a.spikeV 12 i) hzero).symm
    _ = 0 + (∑ i ∈ S.erase z12, (SAP.P005a.spikeV 12 i)^2)/144 := by
          have hz : SAP.P005a.spikeA 12 z12 * SAP.P005a.spikeV 12 z12 = 0 := by
            norm_num [SAP.P005a.spikeA, SAP.P005a.spikeV, z12]
          have ht : (∑ i ∈ S.erase z12, SAP.P005a.spikeA 12 i * SAP.P005a.spikeV 12 i) =
              (∑ i ∈ S.erase z12, (SAP.P005a.spikeV 12 i)^2)/144 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i hi
            rw [spikeA_ordinary i (Finset.ne_of_mem_erase hi)]
            ring
          rw [hz, ht]
    _ = (xsum2 S : ℝ)/3600 := by
          have hv := spikeV_sq_sum S hzero
          have hzv : (SAP.P005a.spikeV 12 z12)^2 = 0 := by norm_num [SAP.P005a.spikeV, z12]
          have he : (∑ i ∈ S.erase z12, (SAP.P005a.spikeV 12 i)^2) =
              ∑ i ∈ S, (SAP.P005a.spikeV 12 i)^2 := by
            have ha := Finset.add_sum_erase S (fun i => (SAP.P005a.spikeV 12 i)^2) hzero
            simpa [hzv] using ha
          rw [he, hv]
          ring

private theorem spikeA_sq_sum (S : Finset (Fin 12)) (hzero : z12 ∈ S) :
    (∑ i ∈ S, (SAP.P005a.spikeA 12 i)^2) = 1 + (xsum2 S : ℝ)/518400 := by
  have hfilter := ordinary_filter_eq_erase S
  calc
    (∑ i ∈ S, (SAP.P005a.spikeA 12 i)^2) =
        (SAP.P005a.spikeA 12 z12)^2 + ∑ i ∈ S.erase z12, (SAP.P005a.spikeA 12 i)^2 := by
          exact (Finset.add_sum_erase S (fun i => (SAP.P005a.spikeA 12 i)^2) hzero).symm
    _ = 1 + (∑ i ∈ S.erase z12, (SAP.P005a.spikeV 12 i)^2)/20736 := by
          have hz : (SAP.P005a.spikeA 12 z12)^2 = 1 := by norm_num [SAP.P005a.spikeA, z12]
          have ht : (∑ i ∈ S.erase z12, (SAP.P005a.spikeA 12 i)^2) =
              (∑ i ∈ S.erase z12, (SAP.P005a.spikeV 12 i)^2)/20736 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i hi
            rw [spikeA_ordinary i (Finset.ne_of_mem_erase hi)]
            ring
          rw [hz, ht]
    _ = 1 + (xsum2 S : ℝ)/518400 := by
          have hv := spikeV_sq_sum S hzero
          have hzv : (SAP.P005a.spikeV 12 z12)^2 = 0 := by norm_num [SAP.P005a.spikeV, z12]
          have he : (∑ i ∈ S.erase z12, (SAP.P005a.spikeV 12 i)^2) =
              ∑ i ∈ S, (SAP.P005a.spikeV 12 i)^2 := by
            have ha := Finset.add_sum_erase S (fun i => (SAP.P005a.spikeV 12 i)^2) hzero
            simpa [hzv] using ha
          rw [he, hv]
          ring

private theorem spikeFit_formula (S : Finset (Fin 12)) (hcard : S.card = 6)
    (hzero : z12 ∈ S) :
    SAP.P005a.spikeFit 12 S =
      (xsum S : ℝ)/30 - ((xsum S : ℝ)+360) *
        (6*(xsum2 S : ℝ)-720*(xsum S : ℝ)-(xsum S : ℝ)^2) /
        (30*(2592000+6*(xsum2 S : ℝ)-1440*(xsum S : ℝ)-(xsum S : ℝ)^2)) := by
  let X : ℝ := (xsum S : ℝ)
  let Y : ℝ := (xsum2 S : ℝ)
  let C : ℝ := 6*Y-720*X-X^2
  let D : ℝ := 2592000+6*Y-1440*X-X^2
  have hcert := integer_certificate S hcard hzero
  have hDpos : 0 < D := by
    have ht : (dnum S : ℝ) = D := by
      dsimp [D, dnum, X, Y]
      push_cast
      ring
    rw [← ht]
    exact_mod_cast hcert.1
  have hv : SAP.P005a.mean S (SAP.P005a.spikeV 12) = X/30 := by
    unfold SAP.P005a.mean
    rw [spikeV_sum S hzero, hcard]
    dsimp [X]
    ring
  have hv2 : SAP.P005a.mean S (fun i => (SAP.P005a.spikeV 12 i)^2) = Y/150 := by
    unfold SAP.P005a.mean
    rw [spikeV_sq_sum S hzero, hcard]
    dsimp [Y]
    ring
  have ha : SAP.P005a.mean S (SAP.P005a.spikeA 12) = 1/6+X/4320 := by
    unfold SAP.P005a.mean
    rw [spikeA_sum S hzero, hcard]
    dsimp [X]
    ring
  have hav : SAP.P005a.mean S (fun i => SAP.P005a.spikeA 12 i * SAP.P005a.spikeV 12 i) = Y/21600 := by
    unfold SAP.P005a.mean
    rw [spikeAV_sum S hzero, hcard]
    dsimp [Y]
    ring
  have ha2 : SAP.P005a.mean S (fun i => (SAP.P005a.spikeA 12 i)^2) = 1/6+Y/3110400 := by
    unfold SAP.P005a.mean
    rw [spikeA_sq_sum S hzero, hcard]
    dsimp [Y]
    ring
  have hcov : SAP.P005a.sampleCov S (SAP.P005a.spikeA 12) (SAP.P005a.spikeV 12) = C/129600 := by
    unfold SAP.P005a.sampleCov
    rw [hav, ha, hv]
    dsimp [C, X, Y]
    ring
  have hvar : SAP.P005a.sampleCov S (SAP.P005a.spikeA 12) (SAP.P005a.spikeA 12) = D/18662400 := by
    unfold SAP.P005a.sampleCov
    have ha2' : SAP.P005a.mean S (fun i => SAP.P005a.spikeA 12 i * SAP.P005a.spikeA 12 i) =
        1/6+Y/3110400 := by simpa only [pow_two] using ha2
    rw [ha2', ha]
    dsimp [D, X, Y]
    ring
  have hslope : SAP.P005a.scalarSlope S (SAP.P005a.spikeA 12) (SAP.P005a.spikeV 12) = 144*C/D := by
    unfold SAP.P005a.scalarSlope
    rw [hcov, hvar]
    field_simp [ne_of_gt hDpos]
    <;> ring
  unfold SAP.P005a.spikeFit
  rw [hv, ha, hslope]
  change (X/30 + (1/12-(1/6+X/4320))*(144*C/D)) =
    X/30-(X+360)*C/(30*D)
  field_simp [ne_of_gt hDpos]
  <;> ring

private theorem spikeR_formula (h : SAP.P005a.WH.W2.T7_L3)
    (S : Finset (Fin 12)) (hS : S ∈ SAP.P005a.design 12 6) :
    SAP.P005a.spikeR 12 S =
      SAP.P005a.spikeFit 12 S - SAP.P005a.spikeFit 12 (SAP.P005a.control S) -
        (SAP.P005a.mean S (SAP.P005a.spikeE 12) -
          SAP.P005a.mean (SAP.P005a.control S) (SAP.P005a.spikeE 12)) := by
  have hcard : S.card = 6 := (Finset.mem_powersetCard.mp hS).2
  have hc : (SAP.P005a.control S).card = 6 := by
    have hcc : (SAP.P005a.control S).card = 12-S.card := by
      simp [SAP.P005a.control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    omega
  have hcalc : SAP.P005a.interactedATE (SAP.P005a.spikePopulation 12) S =
      SAP.P005a.spikeFit 12 S - SAP.P005a.spikeFit 12 (SAP.P005a.control S) := by
    have ht := SAP.P005a.WH.W2.spikeFit_eq 12 (by norm_num) S (by omega)
    have ht' := SAP.P005a.WH.W2.spikeFit_eq 12 (by norm_num) (SAP.P005a.control S) (by omega)
    dsimp only [SAP.P005a.interactedATE]
    change SAP.P005a.mean S (SAP.P005a.spikeV 12) - SAP.P005a.mean (SAP.P005a.control S) (SAP.P005a.spikeV 12) -
      (SAP.P005a.dot (SAP.P005a.xMean (SAP.P005a.spikePopulation 12) S)
        (SAP.P005a.armBetaHat (SAP.P005a.spikePopulation 12) S (SAP.P005a.spikeV 12)) -
        SAP.P005a.dot (SAP.P005a.xMean (SAP.P005a.spikePopulation 12) (SAP.P005a.control S))
          (SAP.P005a.armBetaHat (SAP.P005a.spikePopulation 12) (SAP.P005a.control S) (SAP.P005a.spikeV 12))) = _
    rw [← ht, ← ht']
    ring
  have hp := h 12 (by norm_num)
  have hlead := (hp.2.2.2.2.2 S hS).1
  have hate : SAP.P005a.ate (SAP.P005a.spikePopulation 12) = 0 := by
    simp [SAP.P005a.ate, SAP.P005a.spikePopulation]
  unfold SAP.P005a.spikeR
  rw [hcalc, hate, hlead]
  ring

private theorem balanced_control_card (S : Finset (Fin 12)) (hcard : S.card = 6) :
    (SAP.P005a.control S).card = 6 := by
  have hc : (SAP.P005a.control S).card = 12-S.card := by
    simp [SAP.P005a.control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  omega

private theorem mem_design_of_card (S : Finset (Fin 12)) (hcard : S.card = 6) :
    S ∈ SAP.P005a.design 12 6 := by
  change S ∈ (Finset.univ : Finset (Fin 12)).powersetCard 6
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ _, hcard⟩

private theorem spikeResidualSum (h : SAP.P005a.WH.W2.T7_L3)
    (S : Finset (Fin 12)) (hcard : S.card = 6) (hzero : z12 ∈ S) :
    (∑ i ∈ S, SAP.P005a.spikeE 12 i) = (864*(xsum S : ℝ)-72)/4321 := by
  have hb0 := (h 12 (by norm_num)).1
  have hb : SAP.P005a.spikeB 12 = (144:ℝ)/4321 := by
    norm_num at hb0
    exact hb0
  simp_rw [SAP.P005a.spikeE, SAP.P005a.spikeZ]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [spikeV_sum S hzero, spikeA_sum S hzero, hb]
  simp [Finset.sum_const, hcard]
  norm_num
  ring_nf

private theorem spikeResidualTotal (h : SAP.P005a.WH.W2.T7_L3) :
    (∑ i : Fin 12, SAP.P005a.spikeE 12 i) = 0 := by
  have hb0 := (h 12 (by norm_num)).1
  have hb : SAP.P005a.spikeB 12 = (144:ℝ)/4321 := by
    norm_num at hb0
    exact hb0
  simp only [SAP.P005a.spikeE, SAP.P005a.spikeZ]
  rw [hb]
  have hu : (Finset.univ : Finset (Fin 12)) = {0,1,2,3,4,5,6,7,8,9,10,11} := by decide
  norm_num [SAP.P005a.spikeE, SAP.P005a.spikeZ, SAP.P005a.spikeV,
    SAP.P005a.spikeA, hu]

private theorem spikeResidualDifference (h : SAP.P005a.WH.W2.T7_L3)
    (S : Finset (Fin 12)) (hcard : S.card = 6) (hzero : z12 ∈ S) :
    SAP.P005a.mean S (SAP.P005a.spikeE 12) -
      SAP.P005a.mean (SAP.P005a.control S) (SAP.P005a.spikeE 12) =
        (288*(xsum S : ℝ)-24)/4321 := by
  have hc := balanced_control_card S hcard
  have hsum := spikeResidualSum h S hcard hzero
  have htotal := spikeResidualTotal h
  have hsplit : (∑ i ∈ SAP.P005a.control S, SAP.P005a.spikeE 12 i) +
      (∑ i ∈ S, SAP.P005a.spikeE 12 i) = (∑ i, SAP.P005a.spikeE 12 i) := by
    simpa [SAP.P005a.control] using
      (Finset.sum_sdiff (Finset.subset_univ S) (fun i => SAP.P005a.spikeE 12 i))
  have hcsum : (∑ i ∈ SAP.P005a.control S, SAP.P005a.spikeE 12 i) =
      - (∑ i ∈ S, SAP.P005a.spikeE 12 i) := by linarith
  unfold SAP.P005a.mean
  rw [hcard, hc]
  rw [hcsum, hsum]
  norm_num
  ring_nf

private theorem spikeR_integer_ratio (h : SAP.P005a.WH.W2.T7_L3)
    (S : Finset (Fin 12)) (hcard : S.card = 6) (hzero : z12 ∈ S) :
    SAP.P005a.spikeR 12 S = (rnum S : ℝ)/(rden S : ℝ) := by
  have hS := mem_design_of_card S hcard
  have hR := spikeR_formula h S hS
  have hfitC : SAP.P005a.spikeFit 12 (SAP.P005a.control S) = 12 := by
    have hno : ∀ i ∈ SAP.P005a.control S, i.val ≠ 0 := by
      intro i hi hv
      have hiz : i = z12 := Fin.ext hv
      subst i
      exact (Finset.mem_sdiff.mp hi).2 hzero
    exact (SAP.P005a.WH.W2.spikeLowFit 12 (by norm_num) (SAP.P005a.control S)
      (by rw [balanced_control_card S hcard]; omega) hno).2
  let X : ℝ := (xsum S : ℝ)
  let Y : ℝ := (xsum2 S : ℝ)
  let C : ℝ := 6*Y-720*X-X^2
  let D : ℝ := 2592000+6*Y-1440*X-X^2
  have hDcast : (dnum S : ℝ) = D := by
    dsimp [dnum, D, X, Y]
    push_cast
    ring
  have hCcast : (cnum S : ℝ) = C := by
    dsimp [cnum, C, X, Y]
    push_cast
    ring
  have hRnum : (rnum S : ℝ) =
      X*D*4321-(X+360)*C*4321-12*30*D*4321-(288*X-24)*30*D := by
    dsimp [rnum, cnum, dnum, C, D, X, Y]
    push_cast
    ring
  have hRden : (rden S : ℝ) = 30*D*4321 := by
    dsimp [rden, dnum, D, X, Y]
    push_cast
    ring
  have hDpos : 0 < D := by
    rw [← hDcast]
    exact_mod_cast (integer_certificate S hcard hzero).1
  have hRres := spikeResidualDifference h S hcard hzero
  have hleft : SAP.P005a.spikeR 12 S =
      X/30-(X+360)*C/(30*D)-12-(288*X-24)/4321 := by
    rw [hR, spikeFit_formula S hcard hzero, hfitC, hRres]
  have hAlgebra : X/30-(X+360)*C/(30*D)-12-(288*X-24)/4321 =
      (X*D*4321-(X+360)*C*4321-12*30*D*4321-(288*X-24)*30*D)/(30*D*4321) := by
    field_simp [ne_of_gt hDpos]
    <;> ring
  rw [hleft, hRnum, hRden]
  exact hAlgebra

private theorem spikeR_complement (h : SAP.P005a.WH.W2.T7_L3)
    (S : Finset (Fin 12)) (hS : S ∈ SAP.P005a.design 12 6) :
    SAP.P005a.spikeR 12 (SAP.P005a.control S) = - SAP.P005a.spikeR 12 S := by
  have hcard : S.card = 6 := (Finset.mem_powersetCard.mp hS).2
  have hc := balanced_control_card S hcard
  have hC : SAP.P005a.control S ∈ SAP.P005a.design 12 6 := mem_design_of_card _ hc
  have hinv : SAP.P005a.control (SAP.P005a.control S) = S := by
    ext i
    simp [SAP.P005a.control]
  rw [spikeR_formula h S hS, spikeR_formula h (SAP.P005a.control S) hC, hinv]
  ring

private theorem lower_from_integer (h : SAP.P005a.WH.W2.T7_L3)
    (S : Finset (Fin 12)) (hcard : S.card = 6) (hzero : z12 ∈ S) :
    (8690712840/752921287 : ℝ) ≤ |SAP.P005a.spikeR 12 S| := by
  have hcert := integer_certificate S hcard hzero
  have hratio := spikeR_integer_ratio h S hcard hzero
  have hden : 0 < (rden S : ℝ) := by exact_mod_cast hcert.2.1
  rw [hratio, abs_div, abs_of_pos hden]
  rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 752921287) hden]
  have hc : (8690712840:ℝ)*(rden S:ℝ) ≤ (752921287:ℝ)*|((rnum S:ℤ):ℝ)| := by exact_mod_cast hcert.2.2
  simpa [mul_comm] using hc

private theorem spikeMinimum12 (h : SAP.P005a.WH.W2.T7_L3) :
    SAP.P005a.spikeMinimum 12 (8690712840/752921287) := by
  constructor
  · intro S hS
    have hcard : S.card = 6 := (Finset.mem_powersetCard.mp hS).2
    by_cases hz : z12 ∈ S
    · exact lower_from_integer h S hcard hz
    · have hc := balanced_control_card S hcard
      have hC : SAP.P005a.control S ∈ SAP.P005a.design 12 6 := mem_design_of_card _ hc
      have hzeroC : z12 ∈ SAP.P005a.control S := by
        simp [SAP.P005a.control, hz]
      have hlow := lower_from_integer h (SAP.P005a.control S) hc hzeroC
      rw [spikeR_complement h S hS] at hlow
      simpa [abs_neg] using hlow
  · let S : Finset (Fin 12) := {0,1,2,3,4,5}
    have hcard : S.card = 6 := by norm_num [S]
    have hzero : z12 ∈ S := by norm_num [S, z12]
    refine ⟨S, mem_design_of_card S hcard, ?_⟩
    have hr := spikeR_integer_ratio h S hcard hzero
    have hx : xsum S = -15 := by decide
    have hx2 : xsum2 S = 55 := by decide
    rw [hr]
    norm_num [rnum, rden, cnum, dnum, hx, hx2]

end
end SAP.P005a.WH.W2.P.T7_L6

theorem SAP.P005a.WH.W2.T7_L6_proof : SAP.P005a.WH.W2.T7_L6 := by
  intro h
  exact SAP.P005a.WH.W2.P.T7_L6.spikeMinimum12 h
