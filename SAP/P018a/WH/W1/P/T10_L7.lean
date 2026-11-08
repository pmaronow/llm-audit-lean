import SAP.P018a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W1.P.T10_L7

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open SAP.P018a
open SAP.P018a.WH.W1
open AronowAudit.P018.Wave1
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

private noncomputable def earlyCount (N : ℕ) : ℝ := by
  classical
  exact ∑ d : Dyad N, if (secondUnit d).val < N / 2 then (1 : ℝ) else 0

private def totalRecords (N : ℕ) : ℝ := repeatedL W1MeanWitness N

private def betaScalar (N : ℕ) : ℝ := earlyCount N / totalRecords N

private noncomputable def blockScalar (N : ℕ) (d : Dyad N) : ℝ := by
  classical
  exact if (secondUnit d).val < N / 2 then 1 - betaScalar N else -2 * betaScalar N

private lemma records_le_two (N : ℕ) (d : Dyad N) : W1MeanWitness.T N d ≤ 2 := by
  classical
  simp [W1MeanWitness] <;> split_ifs <;> norm_num

private lemma records_pos (N : ℕ) (hN : 2 ≤ N) (d : Dyad N) :
    0 < W1MeanWitness.T N d := by
  classical
  simp [W1MeanWitness] <;> split_ifs <;> norm_num

private lemma unit_kernel_count (N : ℕ) (d : Dyad N) (t : Fin (W1MeanWitness.T N d))
    (u v : Unit) :
    W1MeanWitness.X N d t u v = ![1] ∧
      W1MeanWitness.Y N d t u v = (if t.val = 0 then 1 else -1) := by
  simp [W1MeanWitness]

private lemma totalRecords_eq_sum (N : ℕ) :
    totalRecords N = ∑ d : Dyad N, (W1MeanWitness.T N d : ℝ) := by
  rfl

private lemma cast_count (N : ℕ) (d : Dyad N) :
    (W1MeanWitness.T N d : ℝ) = if (secondUnit d).val < N / 2 then 1 else 2 := by
  classical
  by_cases h : (secondUnit d).val < N / 2
  · simp [W1MeanWitness, h]
  · simp [W1MeanWitness, h]

private lemma totalRecords_pos (N : ℕ) (hN : 2 ≤ N) : 0 < totalRecords N := by
  classical
  have hdyad : Nonempty (Dyad N) := by
    let i : Fin N := ⟨0, by omega⟩
    let j : Fin N := ⟨1, by omega⟩
    refine ⟨printed_mkDyad i j ?_⟩
    intro hij
    have hv := congrArg Fin.val hij
    norm_num [i, j] at hv
  obtain ⟨d⟩ := hdyad
  have huniv : (Finset.univ : Finset (Dyad N)).Nonempty := ⟨d, Finset.mem_univ _⟩
  rw [totalRecords_eq_sum]
  apply Finset.sum_pos (s := Finset.univ)
  · intro e he
    exact_mod_cast (records_pos N hN e)
  · exact huniv

private lemma repeatedX_const (N : ℕ) (ω : Fin N → Unit) (d : Dyad N)
    (t : Fin (W1MeanWitness.T N d)) : repeatedX W1MeanWitness ω d t = ![1] := by
  simp [repeatedX, W1MeanWitness]

private lemma repeatedY_const (N : ℕ) (ω : Fin N → Unit) (d : Dyad N)
    (t : Fin (W1MeanWitness.T N d)) :
    repeatedY W1MeanWitness ω d t = if t.val = 0 then 1 else -1 := by
  simp [repeatedY, W1MeanWitness]

private lemma scoreSumFin (m : ℕ) (b : ℝ) (hm : m = 1 ∨ m = 2) :
    (∑ t : Fin m, ((if t.val = 0 then 1 else -1) - b)) =
      (if m = 1 then 1 - b else -b - b) := by
  rcases hm with h | h
  · subst m
    rw [Fin.sum_univ_one]
    simp
  · subst m
    rw [Fin.sum_univ_two]
    norm_num [Fin.val_zero, Fin.val_one]
    ring

private lemma blockScore_point (N : ℕ) (ω : Fin N → Unit) (d : Dyad N) :
    repeatedBlockScore W1MeanWitness (betaScalar N • ![1]) ω d =
      (blockScalar N d) • ![1] := by
  classical
  ext i
  fin_cases i
  let m : ℕ := W1MeanWitness.T N d
  have hm : m = 1 ∨ m = 2 := by
    dsimp [m, W1MeanWitness]
    split_ifs <;> simp_all
  have hterm (t : Fin m) :
      (score (repeatedX W1MeanWitness ω d t)
        (repeatedY W1MeanWitness ω d t - dot (repeatedX W1MeanWitness ω d t)
          (betaScalar N • ![1]))) 0 =
          (if t.val = 0 then 1 else -1) - betaScalar N := by
    rw [repeatedX_const, repeatedY_const]
    simp [score, dot]
  simp only [repeatedBlockScore, Finset.sum_apply]
  change (∑ t : Fin m,
      (score (repeatedX W1MeanWitness ω d t)
        (repeatedY W1MeanWitness ω d t - dot (repeatedX W1MeanWitness ω d t)
          (betaScalar N • ![1]))) 0) = _
  simp_rw [hterm]
  have hsum := scoreSumFin m (betaScalar N) hm
  rw [hsum]
  rcases hm with h | h
  · have he : (secondUnit d).val < N / 2 := by
      dsimp [m, W1MeanWitness] at h
      split_ifs at h <;> omega
    simp [blockScalar, he, h]
  · have he : ¬ (secondUnit d).val < N / 2 := by
      dsimp [m, W1MeanWitness] at h
      split_ifs at h <;> omega
    simp [blockScalar, he, h]
    ring

private lemma signSumFin (m : ℕ) (hm : m = 1 ∨ m = 2) :
    (∑ t : Fin m, (if t.val = 0 then (1 : ℝ) else -1)) =
      (if m = 1 then 1 else 0) := by
  rcases hm with h | h
  · subst m
    simp [Fin.sum_univ_one]
  · subst m
    simp [Fin.sum_univ_two]

private lemma dyadSignSum (N : ℕ) (d : Dyad N) :
    (∑ t : Fin (W1MeanWitness.T N d), (if t.val = 0 then (1 : ℝ) else -1)) =
      (if (secondUnit d).val < N / 2 then 1 else 0) := by
  classical
  let m : ℕ := W1MeanWitness.T N d
  have hm : m = 1 ∨ m = 2 := by
    dsimp [m, W1MeanWitness]
    split_ifs <;> simp_all
  change (∑ t : Fin m, (if t.val = 0 then (1 : ℝ) else -1)) = _
  rw [signSumFin m hm]
  rcases hm with h | h
  · have he : (secondUnit d).val < N / 2 := by
      dsimp [m, W1MeanWitness] at h
      split_ifs at h <;> omega
    simp [he, h]
  · have he : ¬ (secondUnit d).val < N / 2 := by
      dsimp [m, W1MeanWitness] at h
      split_ifs at h <;> omega
    simp [he, h]

private def responseTotal (N : ℕ) : ℝ :=
  ∑ d : Dyad N, ∑ t : Fin (W1MeanWitness.T N d),
    if t.val = 0 then (1 : ℝ) else -1

private lemma responseTotal_eq_earlyCount (N : ℕ) : responseTotal N = earlyCount N := by
  classical
  unfold responseTotal earlyCount
  apply Finset.sum_congr rfl
  intro d hd
  exact dyadSignSum N d

private lemma meanVec_const (N : ℕ) (x : Vec 1) :
    meanVec (repeatedLaw W1MeanWitness N) (fun _ => x) = x := by
  ext i
  simp [meanVec, repeatedLaw, integral_const, probReal_univ, W1MeanWitness]

private lemma meanMat_const (N : ℕ) (A : Mat 1) :
    meanMat (repeatedLaw W1MeanWitness N) (fun _ => A) = A := by
  ext i j
  simp [meanMat, repeatedLaw, integral_const, probReal_univ, W1MeanWitness]

private lemma gram_point (N : ℕ) (ω : Fin N → Unit) :
    repeatedGram W1MeanWitness ω = totalRecords N • (1 : Mat 1) := by
  classical
  ext i j
  fin_cases i
  fin_cases j
  have ho : SAP.P018a.outer (![1] : Vec 1) (![1]) = (1 : Mat 1) := by
    ext a b
    fin_cases a
    fin_cases b
    simp [SAP.P018a.outer]
  simp only [repeatedGram, Matrix.sum_apply, repeatedX_const, ho]
  simp [totalRecords, totalRecords_eq_sum, repeatedL]

private lemma meanGram (N : ℕ) :
    meanMat (repeatedLaw W1MeanWitness N) (repeatedGram W1MeanWitness) =
      totalRecords N • (1 : Mat 1) := by
  rw [show repeatedGram W1MeanWitness = fun _ : Fin N → Unit => totalRecords N • (1 : Mat 1) by
    funext ω; exact gram_point N ω]
  exact meanMat_const N _

private lemma totalScore_point (N : ℕ) (ω : Fin N → Unit) :
    (∑ d : Dyad N, ∑ t : Fin (W1MeanWitness.T N d),
      score (repeatedX W1MeanWitness ω d t) (repeatedY W1MeanWitness ω d t)) =
        earlyCount N • ![1] := by
  classical
  ext i
  fin_cases i
  simp only [Finset.sum_apply]
  simp_rw [repeatedX_const, repeatedY_const]
  rw [← responseTotal_eq_earlyCount]
  simp [responseTotal, score, dot]

private lemma meanTotalScore (N : ℕ) :
    meanVec (repeatedLaw W1MeanWitness N) (fun ω =>
      ∑ d : Dyad N, ∑ t : Fin (W1MeanWitness.T N d),
        score (repeatedX W1MeanWitness ω d t) (repeatedY W1MeanWitness ω d t)) =
        earlyCount N • ![1] := by
  rw [show (fun ω : Fin N → Unit =>
      ∑ d : Dyad N, ∑ t : Fin (W1MeanWitness.T N d),
        score (repeatedX W1MeanWitness ω d t) (repeatedY W1MeanWitness ω d t)) =
      fun _ => earlyCount N • ![1] by
    funext ω; exact totalScore_point N ω]
  exact meanVec_const N _

private lemma repeatedBeta_formula (N : ℕ) (hN : 2 ≤ N) :
    repeatedBeta W1MeanWitness N = betaScalar N • ![1] := by
  classical
  have hL : totalRecords N ≠ 0 := (totalRecords_pos N hN).ne'
  unfold repeatedBeta
  rw [meanGram, meanTotalScore]
  rw [AronowAudit.P018.matrix_inverse_scale_total (1 : Mat 1) _ hL]
  simp [betaScalar, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul,
    smul_smul, hL]
  field_simp [hL]

private lemma beta_stacked_eq_zero (N : ℕ) (hN : 2 ≤ N) :
    (∑ d : Dyad N, meanVec (repeatedLaw W1MeanWitness N)
      (fun ω => repeatedBlockScore W1MeanWitness (repeatedBeta W1MeanWitness N) ω d)) = 0 := by
  classical
  have hβ := repeatedBeta_formula N hN
  rw [hβ]
  simp_rw [show ∀ d ω, repeatedBlockScore W1MeanWitness (betaScalar N • ![1]) ω d =
      blockScalar N d • ![1] from fun d ω => blockScore_point N ω d]
  simp_rw [meanVec_const]
  ext i
  fin_cases i
  have hsumT : (∑ d : Dyad N,
      if (secondUnit d).val < N / 2 then (1 : ℝ) else 2) = totalRecords N := by
    rw [totalRecords_eq_sum]
    apply Finset.sum_congr rfl
    intro d hd
    exact (cast_count N d).symm
  have hs : (∑ d : Dyad N, blockScalar N d) =
      earlyCount N - betaScalar N * totalRecords N := by
    have hterm (d : Dyad N) : blockScalar N d =
        (if (secondUnit d).val < N / 2 then 1 else 0) -
          betaScalar N * (if (secondUnit d).val < N / 2 then 1 else 2) := by
      by_cases h : (secondUnit d).val < N / 2 <;> simp [blockScalar, h] <;> ring
    calc
      (∑ d : Dyad N, blockScalar N d) =
          ∑ d : Dyad N, ((if (secondUnit d).val < N / 2 then 1 else 0) -
            betaScalar N * (if (secondUnit d).val < N / 2 then 1 else 2)) := by
          apply Finset.sum_congr rfl
          intro d hd
          exact hterm d
      _ = (∑ d : Dyad N, if (secondUnit d).val < N / 2 then (1 : ℝ) else 0) -
            betaScalar N * (∑ d : Dyad N,
              if (secondUnit d).val < N / 2 then (1 : ℝ) else 2) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = earlyCount N - betaScalar N * totalRecords N := by
          rw [earlyCount, ← hsumT]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ d : Dyad N, blockScalar N d * (1 : ℝ)) = 0
  simp only [mul_one]
  rw [hs]
  have hLp : totalRecords N ≠ 0 := (totalRecords_pos N hN).ne'
  simp [betaScalar, hLp]

private lemma witness_standing : RepeatedStanding W1MeanWitness := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change IsProbabilityMeasure (Measure.dirac ())
    infer_instance
  · intro N hN d
    exact_mod_cast records_pos N hN d
  · intro N d t
    constructor <;> exact measurable_const
  · refine ⟨‖(![1] : Vec 1)‖ + 1, by positivity, ?_⟩
    intro N d t
    filter_upwards [] with uv
    constructor
    · change ‖(![1] : Vec 1)‖ ≤ ‖(![1] : Vec 1)‖ + 1
      exact le_add_of_nonneg_right (by norm_num)
    · change |(if t.val = 0 then 1 else -1 : ℝ)| ≤ ‖(![1] : Vec 1)‖ + 1
      split_ifs <;> have := norm_nonneg (![1] : Vec 1) <;> norm_num at * <;> linarith
  · refine ⟨0, ?_⟩
    intro N d t u v
    simp [W1MeanWitness]

private lemma repeatedH_one (N : ℕ) (hN : 2 ≤ N) :
    repeatedH W1MeanWitness N = (1 : Mat 1) := by
  have hL : totalRecords N ≠ 0 := (totalRecords_pos N hN).ne'
  rw [repeatedH, meanGram]
  have hRL : repeatedL W1MeanWitness N ≠ 0 := by simpa [totalRecords] using hL
  simp only [totalRecords]
  simp [smul_smul, inv_mul_cancel₀ hRL]

private lemma common_record_kernels :
    ∃ fX : ℕ → Unit → Unit → Vec 1, ∃ fY : ℕ → Unit → Unit → ℝ,
      ∀ N d (t : Fin (W1MeanWitness.T N d)) u v,
        W1MeanWitness.X N d t u v = fX t.val u v ∧
        W1MeanWitness.Y N d t u v = fY t.val u v := by
  refine ⟨fun _ _ _ => ![1], fun t _ _ => if t = 0 then 1 else -1, ?_⟩
  intro N d t u v
  simp [W1MeanWitness]

private lemma earlyUnitCount (n : ℕ) :
    (Finset.univ.filter (fun i : Fin (2*n) => i.val < n)).card = n := by
  classical
  refine Finset.card_eq_of_bijective
    (fun i hi => (⟨i, by omega⟩ : Fin (2*n))) ?_ ?_ ?_
  · intro a ha
    have hp := (Finset.mem_filter.mp ha).2
    refine ⟨a.val, hp, ?_⟩
    ext
    rfl
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  · intro i j hi hj hij
    exact congrArg Fin.val hij

private lemma earlyCount_even (n : ℕ) :
    earlyCount (2*n) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  classical
  let F : Fin (2*n) → Fin (2*n) → ℝ :=
    fun i j => if i.val < n ∧ j.val < n then 1 else 0
  have hsym : ∀ i j, F i j = F j i := by
    intro i j
    simp [F, and_comm]
  have hdiv : (2*n)/2 = n := by omega
  have hleft : (∑ d : Dyad (2*n), F (firstUnit d) (secondUnit d)) = earlyCount (2*n) := by
    unfold earlyCount
    apply Finset.sum_congr rfl
    intro d hd
    have hlt : firstUnit d < secondUnit d := by
      exact Finset.min'_lt_max'_of_card (members d) (by rw [members_card]; omega)
    simp only [F]
    by_cases h : (secondUnit d).val < n
    · have hltv : (firstUnit d).val < (secondUnit d).val := by
        change (firstUnit d).val < (secondUnit d).val at hlt
        exact hlt
      have hfirst : (firstUnit d).val < n := hltv.trans h
      simp [h, hdiv, hfirst]
    · simp [h, hdiv]
  have hrow (i : Fin (2*n)) :
      (∑ j : Fin (2*n), F i j) - F i i =
        (if i.val < n then (n : ℝ) - 1 else 0) := by
    by_cases hi : i.val < n
    · have hs : (∑ j : Fin (2*n), if j.val < n then (1 : ℝ) else 0) = n := by
        rw [← Finset.sum_filter]
        simp [earlyUnitCount]
      simp [F, hi, hs]
    · simp [F, hi]
  have htotal : (∑ i : Fin (2*n), if i.val < n then (n : ℝ)-1 else 0) =
      (n : ℝ) * ((n : ℝ)-1) := by
    rw [← Finset.sum_filter]
    simp [earlyUnitCount]
    ring
  have hp := printed_pair_sum F hsym
  have hfirst (d : Dyad (2*n)) :
      firstUnit d = AronowAudit.P018.firstUnit d := by rfl
  have hsecond (d : Dyad (2*n)) :
      secondUnit d = AronowAudit.P018.secondUnit d := by rfl
  have hleft' : (∑ d : AronowAudit.P018.Dyad (2*n),
      F (AronowAudit.P018.firstUnit d) (AronowAudit.P018.secondUnit d)) =
        earlyCount (2*n) := by
    have heq (d : SAP.P018a.Dyad (2*n)) :
        SAP.P018a.firstUnit d = AronowAudit.P018.firstUnit d ∧
        SAP.P018a.secondUnit d = AronowAudit.P018.secondUnit d := ⟨rfl, rfl⟩
    calc
      _ = ∑ d : SAP.P018a.Dyad (2*n), F (SAP.P018a.firstUnit d)
            (SAP.P018a.secondUnit d) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [(heq d).1, (heq d).2]
      _ = earlyCount (2*n) := hleft
  have hp' : (2 : ℝ) * earlyCount (2*n) =
      ∑ i : Fin (2*n), ((∑ j : Fin (2*n), F i j) - F i i) := by
    calc
      _ = 2 * (∑ d : AronowAudit.P018.Dyad (2*n),
          F (AronowAudit.P018.firstUnit d) (AronowAudit.P018.secondUnit d)) :=
            congrArg (fun x : ℝ => 2*x) hleft'.symm
      _ = _ := hp
  simp_rw [hrow] at hp'
  rw [htotal] at hp'
  have : (2 : ℝ) * earlyCount (2*n) = (n : ℝ) * ((n : ℝ)-1) := by linarith
  linarith

private lemma totalRecords_linear (N : ℕ) :
    totalRecords N = 2 * (Fintype.card (Dyad N) : ℝ) - earlyCount N := by
  rw [totalRecords_eq_sum]
  have hterm (d : Dyad N) : (W1MeanWitness.T N d : ℝ) =
      2 - (if (secondUnit d).val < N / 2 then (1 : ℝ) else 0) := by
    rw [cast_count]
    split_ifs <;> norm_num
  calc
    (∑ d : Dyad N, (W1MeanWitness.T N d : ℝ)) =
        ∑ d : Dyad N, (2 - (if (secondUnit d).val < N / 2 then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro d hd
          exact hterm d
    _ = 2 * (Fintype.card (Dyad N) : ℝ) - earlyCount N := by
          rw [Finset.sum_sub_distrib]
          simp [earlyCount, Finset.sum_const, nsmul_eq_mul]
          ring

private lemma dyadCard_even (n : ℕ) :
    (Fintype.card (Dyad (2*n)) : ℝ) = (n : ℝ) * (2*(n:ℝ)-1) := by
  have hd : Fintype.card (AronowAudit.P018.Dyad (2*n)) = (2*n).choose 2 :=
    AronowAudit.P018.number_of_dyads (2*n)
  have hc : Fintype.card (Dyad (2*n)) = (2*n).choose 2 := by
    simpa [SAP.P018a.Dyad, SAP.P018a.dyads, AronowAudit.P018.Dyad,
      AronowAudit.P018.dyads] using hd
  rw [hc, Nat.cast_choose_two]
  push_cast
  ring

private lemma totalRecords_even (n : ℕ) :
    totalRecords (2*n) = (n : ℝ) * (7*(n:ℝ)-3) / 2 := by
  rw [totalRecords_linear, dyadCard_even, earlyCount_even]
  ring

private lemma beta_even (n : ℕ) (hn : 1 ≤ n) :
    betaScalar (2*n) = ((n:ℝ) - 1) / (7*(n:ℝ)-3) := by
  rw [betaScalar, earlyCount_even, totalRecords_even]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (7*(n:ℝ)-3) ≠ 0 := by nlinarith
  field_simp [hn0, hd] <;> ring

private def incidentCount (N : ℕ) (i : Fin N) : ℝ :=
  ∑ d : AronowAudit.P018.Dyad N,
    if i ∈ AronowAudit.P018.members d then (1 : ℝ) else 0

private def earlyIncidentCount (n : ℕ) (i : Fin (2*n)) : ℝ :=
  ∑ d : AronowAudit.P018.Dyad (2*n),
    if i ∈ AronowAudit.P018.members d ∧
        (AronowAudit.P018.secondUnit d).val < n then (1 : ℝ) else 0

private lemma incidentCount_formula (N : ℕ) (i : Fin N) :
    incidentCount N i = (N : ℝ)-1 := by
  classical
  have h := AronowAudit.P018.Wave1.printed_incident_add (fun _ : Fin N => (1:ℝ)) i
  have hterm (d : AronowAudit.P018.Dyad N) :
      (if i ∈ AronowAudit.P018.members d then
        (fun _ : Fin N => (1:ℝ)) (AronowAudit.P018.firstUnit d) +
          (fun _ : Fin N => (1:ℝ)) (AronowAudit.P018.secondUnit d) else 0) =
      2 * (if i ∈ AronowAudit.P018.members d then (1:ℝ) else 0) := by
    split_ifs <;> norm_num
  simp_rw [hterm] at h
  rw [← Finset.mul_sum] at h
  have hsum : 2 * incidentCount N i = (N:ℝ)-2+(N:ℝ) := by
    simpa [incidentCount] using h
  linarith

private lemma earlyUnit_sum (n : ℕ) :
    (∑ i : Fin (2*n), if i.val < n then (1:ℝ) else 0) = n := by
  rw [← Finset.sum_filter]
  simp [earlyUnitCount]

private lemma earlyIncident_formula (n : ℕ) (i : Fin (2*n)) :
    earlyIncidentCount n i = if i.val < n then (n:ℝ)-1 else 0 := by
  classical
  let u : Fin (2*n) → ℝ := fun j => if j.val < n then 1 else 0
  by_cases hi : i.val < n
  · have hinc := AronowAudit.P018.Wave1.printed_incident_add u i
    have hterm (d : AronowAudit.P018.Dyad (2*n)) :
        (if i ∈ AronowAudit.P018.members d then
          u (AronowAudit.P018.firstUnit d) + u (AronowAudit.P018.secondUnit d) else 0) =
        (if i ∈ AronowAudit.P018.members d then (1:ℝ) else 0) +
          (if i ∈ AronowAudit.P018.members d ∧
              (AronowAudit.P018.secondUnit d).val < n then (1:ℝ) else 0) := by
      by_cases him : i ∈ AronowAudit.P018.members d
      · have hend := AronowAudit.P018.Wave1.printed_members_endpoints d
        rw [hend] at him
        simp only [Finset.mem_insert, Finset.mem_singleton] at him
        rcases him with hfirst | hsecond
        · subst i
          have hlt := AronowAudit.P018.Wave1.printed_endpoints_lt d
          have hltv : (AronowAudit.P018.firstUnit d).val <
              (AronowAudit.P018.secondUnit d).val := by
            change (AronowAudit.P018.firstUnit d).val <
              (AronowAudit.P018.secondUnit d).val at hlt
            exact hlt
          rw [hend]
          simp [u, hi]
        · subst i
          have hlt := AronowAudit.P018.Wave1.printed_endpoints_lt d
          have hltv : (AronowAudit.P018.firstUnit d).val <
              (AronowAudit.P018.secondUnit d).val := by
            change (AronowAudit.P018.firstUnit d).val <
              (AronowAudit.P018.secondUnit d).val at hlt
            exact hlt
          have hfirst : (AronowAudit.P018.firstUnit d).val < n := hltv.trans hi
          rw [hend]
          simp [u, hi, hfirst]
      · simp [him]
    have hsplit :
        (∑ d : AronowAudit.P018.Dyad (2*n),
          if i ∈ AronowAudit.P018.members d then
            u (AronowAudit.P018.firstUnit d) + u (AronowAudit.P018.secondUnit d) else 0) =
          incidentCount (2*n) i + earlyIncidentCount n i := by
      calc
        _ = ∑ d : AronowAudit.P018.Dyad (2*n),
          ((if i ∈ AronowAudit.P018.members d then (1:ℝ) else 0) +
            (if i ∈ AronowAudit.P018.members d ∧
              (AronowAudit.P018.secondUnit d).val < n then (1:ℝ) else 0)) := by
              apply Finset.sum_congr rfl
              intro d hd
              exact hterm d
        _ = _ := by simp [incidentCount, earlyIncidentCount, Finset.sum_add_distrib]
    have hU : (∑ j : Fin (2*n), u j) = n := by
      dsimp [u]
      exact earlyUnit_sum n
    have hrhs : ((2*(n:ℝ)-2) * 1 + (n:ℝ)) = 3*(n:ℝ)-2 := by ring
    have hval0 : (∑ d : AronowAudit.P018.Dyad (2*n),
          if i ∈ AronowAudit.P018.members d then
            u (AronowAudit.P018.firstUnit d) + u (AronowAudit.P018.secondUnit d) else 0) =
          (2*(n:ℝ)-2) + n := by
      simpa [u, hi, hU] using hinc
    have hval : (∑ d : AronowAudit.P018.Dyad (2*n),
          if i ∈ AronowAudit.P018.members d then
            u (AronowAudit.P018.firstUnit d) + u (AronowAudit.P018.secondUnit d) else 0) =
          3*(n:ℝ)-2 := by
      calc
        _ = (2*(n:ℝ)-2) + n := hval0
        _ = 3*(n:ℝ)-2 := by ring
    have hc := incidentCount_formula (2*n) i
    push_cast at hc
    rw [hsplit, hc] at hval
    have : earlyIncidentCount n i = (n:ℝ)-1 := by linarith
    simp [hi, this]
  · have hzero : earlyIncidentCount n i = 0 := by
      unfold earlyIncidentCount
      apply Finset.sum_eq_zero
      intro d hd
      by_cases hmem : i ∈ AronowAudit.P018.members d
      · have hend := AronowAudit.P018.Wave1.printed_members_endpoints d
        rw [hend] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with hfirst | hsecond
        · subst i
          have hlt := AronowAudit.P018.Wave1.printed_endpoints_lt d
          have hltv : (AronowAudit.P018.firstUnit d).val <
              (AronowAudit.P018.secondUnit d).val := by
            change (AronowAudit.P018.firstUnit d).val <
              (AronowAudit.P018.secondUnit d).val at hlt
            exact hlt
          by_cases he : (AronowAudit.P018.secondUnit d).val < n
          · have : (AronowAudit.P018.firstUnit d).val < n := hltv.trans he
            exact (False.elim (hi this))
          · simp [he]
        · subst i
          by_cases he : (AronowAudit.P018.secondUnit d).val < n
          · exact (False.elim (hi he))
          · simp [he]
      · simp [hmem]
    simp [hi, hzero]

private def qBlock (N : ℕ) (d : AronowAudit.P018.Dyad N) : Vec 1 :=
  blockScalar N (show Dyad N from d) • ![1]

private def qBlockSAP (N : ℕ) (d : SAP.P018a.Dyad N) : Vec 1 :=
  blockScalar N d • ![1]

private def incidenceAmp (n : ℕ) : ℝ :=
  2*((n:ℝ)-1)*(2*(n:ℝ)-1)/(7*(n:ℝ)-3)

private lemma unitScore_even_raw (n : ℕ) (i : Fin (2*n)) :
    (AronowAudit.P018.unitScore AronowAudit.P018.members (qBlock (2*n)) i) 0 =
      -2 * betaScalar (2*n) * incidentCount (2*n) i +
        (1 + betaScalar (2*n)) * earlyIncidentCount n i := by
  classical
  simp only [AronowAudit.P018.unitScore, Finset.sum_apply, ite_apply, Pi.zero_apply]
  have hterm (d : AronowAudit.P018.Dyad (2*n)) :
      (if i ∈ AronowAudit.P018.members d then qBlock (2*n) d 0 else 0) =
        -2*betaScalar (2*n) *
          (if i ∈ AronowAudit.P018.members d then (1:ℝ) else 0) +
        (1+betaScalar (2*n)) *
          (if i ∈ AronowAudit.P018.members d ∧
              (AronowAudit.P018.secondUnit d).val < n then (1:ℝ) else 0) := by
    have hsec : SAP.P018a.secondUnit d = AronowAudit.P018.secondUnit d := rfl
    by_cases hm : i ∈ AronowAudit.P018.members d
    · by_cases he : (AronowAudit.P018.secondUnit d).val < n
      · have he' : (SAP.P018a.secondUnit d).val < n := by simpa [hsec] using he
        simp [qBlock, blockScalar, hm, he, he']
        ring
      · have he' : ¬ (SAP.P018a.secondUnit d).val < n := by simpa [hsec] using he
        simp [qBlock, blockScalar, hm, he, he']
    · simp [qBlock, hm]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  change (-2 * betaScalar (2*n)) * incidentCount (2*n) i +
      (1 + betaScalar (2*n)) * earlyIncidentCount n i = _
  rfl

private lemma unitScore_even_formula (n : ℕ) (hn : 1 ≤ n) (i : Fin (2*n)) :
    (AronowAudit.P018.unitScore AronowAudit.P018.members (qBlock (2*n)) i) 0 =
      (if i.val < n then incidenceAmp n else -incidenceAmp n) := by
  rw [unitScore_even_raw, incidentCount_formula, earlyIncident_formula]
  rw [beta_even n hn]
  by_cases hi : i.val < n
  · simp only [if_pos hi]
    unfold incidenceAmp
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hd : 7*(n:ℝ)-3 ≠ 0 := by nlinarith
    have hd' : -3 + (n:ℝ)*7 ≠ 0 := by nlinarith
    push_cast
    norm_num [Nat.cast_mul] 
    have hinv : (-3 + (n:ℝ)*7) * (-3 + (n:ℝ)*7)⁻¹ = 1 := mul_inv_cancel₀ hd'
    first | (linear_combination -((n:ℝ)-1) * hinv <;> ring) |
      (linear_combination ((n:ℝ)-1) * hinv <;> ring) | ring
  · simp only [if_neg hi]
    unfold incidenceAmp
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hd : 7*(n:ℝ)-3 ≠ 0 := by nlinarith
    have hd' : -3 + (n:ℝ)*7 ≠ 0 := by nlinarith
    push_cast
    norm_num [Nat.cast_mul] 
    have hinv : (-3 + (n:ℝ)*7) * (-3 + (n:ℝ)*7)⁻¹ = 1 := mul_inv_cancel₀ hd'
    first | (linear_combination -((n:ℝ)-1) * hinv <;> ring) |
      (linear_combination ((n:ℝ)-1) * hinv <;> ring) | ring

private lemma repeatedOLS_formula (N : ℕ) (hN : 2 ≤ N) (ω : Fin N → Unit) :
    repeatedOLS W1MeanWitness ω = betaScalar N • ![1] := by
  classical
  have hL : totalRecords N ≠ 0 := (totalRecords_pos N hN).ne'
  unfold repeatedOLS
  rw [gram_point N ω, totalScore_point N ω]
  rw [AronowAudit.P018.matrix_inverse_scale_total (1 : Mat 1) _ hL]
  ext i
  fin_cases i
  simp [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul,
    betaScalar, hL]
  field_simp [hL]

private lemma meanBlock_q (N : ℕ) (hN : 2 ≤ N) (d : Dyad N) :
    meanVec (repeatedLaw W1MeanWitness N)
      (fun ω => repeatedBlockScore W1MeanWitness (repeatedBeta W1MeanWitness N) ω d) =
        qBlock N d := by
  rw [repeatedBeta_formula N hN]
  rw [show (fun ω : Fin N → Unit =>
      repeatedBlockScore W1MeanWitness (betaScalar N • ![1]) ω d) =
      fun _ => qBlock N d by
        funext ω
        exact (blockScore_point N ω d).trans (by rfl)]
  exact meanVec_const N _

private lemma blockScalar_sum_zero (N : ℕ) (hN : 2 ≤ N) :
    (∑ d : Dyad N, blockScalar N d) = 0 := by
  have hs := beta_stacked_eq_zero N hN
  simp_rw [meanBlock_q N hN] at hs
  have hc := congrArg (fun v : Vec 1 => v 0) hs
  simpa [qBlock, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hc

private lemma stackedScore_point_zero (N : ℕ) (hN : 2 ≤ N) (ω : Fin N → Unit) :
    (∑ d : Dyad N,
      repeatedBlockScore W1MeanWitness (repeatedOLS W1MeanWitness ω) ω d) = 0 := by
  rw [repeatedOLS_formula N hN ω]
  simp_rw [blockScore_point N ω]
  ext i
  fin_cases i
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ d : Dyad N, blockScalar N d) = 0
  exact blockScalar_sum_zero N hN

private lemma varMat_const (N : ℕ) (x : Vec 1) :
    varMat (repeatedLaw W1MeanWitness N) (fun _ => x) = 0 := by
  have hprob : IsProbabilityMeasure (repeatedLaw W1MeanWitness N) := by
    unfold repeatedLaw W1MeanWitness
    infer_instance
  letI := hprob
  ext i j
  change ProbabilityTheory.covariance (fun _ : Fin N → Unit => x i)
    (fun _ : Fin N → Unit => x j) (repeatedLaw W1MeanWitness N) = 0
  exact ProbabilityTheory.covariance_const_left (μ := repeatedLaw W1MeanWitness N) (c := x i)
    (Y := fun _ : Fin N → Unit => x j)

private lemma overlapEven_scalar (n : ℕ) (hn : 1 ≤ n) :
    W1MeanOverlap (2*n) 0 0 =
      32*((n : ℝ)-1)*(2*(n : ℝ)-1)*(4*(n : ℝ)^2-9*(n : ℝ)+3)/(7*(n : ℝ)-3)^4 := by
  classical
  let N := 2*n
  let b := betaScalar N
  let A := incidenceAmp n
  have hdiv : N/2 = n := by dsimp [N]; omega
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hd : (7*(n:ℝ)-3) ≠ 0 := by nlinarith [hnR]
  have hE : (∑ d : AronowAudit.P018.Dyad N, if (secondUnit d).val < n then (1:ℝ) else 0) =
      earlyCount N := by
    unfold earlyCount
    apply Finset.sum_congr rfl
    intro d _
    simp [N, hdiv]
  have hElate : (∑ d : AronowAudit.P018.Dyad N, if (secondUnit d).val < n then (0:ℝ) else 1) =
      (Fintype.card (AronowAudit.P018.Dyad N) : ℝ) - earlyCount N := by
    have hterm (d : AronowAudit.P018.Dyad N) :
        (if (secondUnit d).val < n then (0:ℝ) else 1) =
          1 - (if (secondUnit d).val < n then (1:ℝ) else 0) := by
      split_ifs <;> ring
    calc
      _ = ∑ d : AronowAudit.P018.Dyad N, (1 - (if (secondUnit d).val < n then (1:ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro d _
        exact hterm d
      _ = _ := by rw [Finset.sum_sub_distrib, hE]; simp
  have hdyadSq : (∑ d : AronowAudit.P018.Dyad N, qBlock N d 0 * qBlock N d 0) =
      earlyCount N * (1-b)^2 +
        ((Fintype.card (AronowAudit.P018.Dyad N) : ℝ)-earlyCount N) * (2*b)^2 := by
    have hterm (d : AronowAudit.P018.Dyad N) :
        qBlock N d 0 * qBlock N d 0 =
          (if (secondUnit d).val < n then (1-b)^2 else (2*b)^2) := by
      by_cases he : (secondUnit d).val < n
      · simp [qBlock, blockScalar, N, betaScalar, b, hdiv, he] <;> ring
      · simp [qBlock, blockScalar, N, betaScalar, b, hdiv, he] <;> ring
    have hsplit (d : AronowAudit.P018.Dyad N) :
        (if (secondUnit d).val < n then (1-b)^2 else (2*b)^2) =
          (if (secondUnit d).val < n then (1:ℝ) else 0) * (1-b)^2 +
          (if (secondUnit d).val < n then (0:ℝ) else 1) * (2*b)^2 := by
      split_ifs <;> ring
    calc
      _ = ∑ d : AronowAudit.P018.Dyad N, if (secondUnit d).val < n then (1-b)^2 else (2*b)^2 := by
        apply Finset.sum_congr rfl
        intro d _
        exact hterm d
      _ = (∑ d : AronowAudit.P018.Dyad N, if (secondUnit d).val < n then (1:ℝ) else 0) * (1-b)^2 +
          (∑ d : AronowAudit.P018.Dyad N, if (secondUnit d).val < n then (0:ℝ) else 1) * (2*b)^2 := by
        rw [show (∑ d : AronowAudit.P018.Dyad N, if (secondUnit d).val < n then (1-b)^2 else (2*b)^2) =
            ∑ d : AronowAudit.P018.Dyad N, ((if (secondUnit d).val < n then (1:ℝ) else 0) * (1-b)^2 +
              (if (secondUnit d).val < n then (0:ℝ) else 1) * (2*b)^2) by
          apply Finset.sum_congr rfl
          intro d _
          exact hsplit d]
        rw [Finset.sum_add_distrib]
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ = _ := by rw [hE, hElate]
  have hunitSq : (∑ i : Fin N,
      (AronowAudit.P018.unitScore AronowAudit.P018.members (qBlock N) i 0) *
        (AronowAudit.P018.unitScore AronowAudit.P018.members (qBlock N) i 0)) =
      (N:ℝ) * A^2 := by
    have hscore (i : Fin N) :
        AronowAudit.P018.unitScore AronowAudit.P018.members (qBlock N) i 0 =
          if i.val < n then A else -A := by
      simpa [N, A] using unitScore_even_formula n hn i
    have hterm (i : Fin N) :
        (if i.val < n then A else -A) * (if i.val < n then A else -A) = A^2 := by
      split_ifs <;> ring
    calc
      _ = ∑ i : Fin N, A^2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hscore]
        exact hterm i
      _ = (N:ℝ) * A^2 := by simp [Finset.sum_const, nsmul_eq_mul]
  have hmeat :
      (AronowAudit.P018.meat AronowAudit.P018.members (qBlock N) 0 0) =
        (N:ℝ)*A^2 -
          (earlyCount N*(1-b)^2 +
            ((Fintype.card (AronowAudit.P018.Dyad N):ℝ)-earlyCount N)*(2*b)^2) := by
    rw [AronowAudit.P018.overlap_meat_identity AronowAudit.P018.members
      AronowAudit.P018.members_card
      (fun d e h => Subtype.ext h) (qBlock N)]
    simp only [Matrix.sub_apply, Matrix.sum_apply, AronowAudit.P018.dyadMeat,
      AronowAudit.P018.outer, Finset.sum_apply]
    rw [hunitSq]
    have hdyadSq' : (∑ d : AronowAudit.P018.Dyad N,
        qBlock N d 0 * qBlock N d 0) =
      earlyCount N * (1-b)^2 +
        ((Fintype.card (AronowAudit.P018.Dyad N) : ℝ)-earlyCount N) * (2*b)^2 := by
      simpa [AronowAudit.P018.Dyad, SAP.P018a.Dyad, AronowAudit.P018.dyads, SAP.P018a.dyads] using hdyadSq
    rw [hdyadSq']
  have hcard : (Fintype.card (AronowAudit.P018.Dyad N) : ℝ) = (n:ℝ)*(2*(n:ℝ)-1) := by
    dsimp [N]
    exact dyadCard_even n
  have hL : totalRecords N = (n:ℝ)*(7*(n:ℝ)-3)/2 := by
    dsimp [N]
    exact totalRecords_even n
  have hbeta : b = ((n:ℝ)-1)/(7*(n:ℝ)-3) := by
    dsimp [b, N]
    exact beta_even n hn
  have hcount : earlyCount N = (n:ℝ)*((n:ℝ)-1)/2 := by
    dsimp [N]
    exact earlyCount_even n
  have hA : A = 2*((n:ℝ)-1)*(2*(n:ℝ)-1)/(7*(n:ℝ)-3) := rfl
  have hOne : 1-b = (6*(n:ℝ)-2)/(7*(n:ℝ)-3) := by
    rw [hbeta]
    have hi : (7*(n:ℝ)-3) * (7*(n:ℝ)-3)⁻¹ = 1 := mul_inv_cancel₀ hd
    linear_combination -1 * hi
  have hmeatSimple :
      AronowAudit.P018.meat AronowAudit.P018.members (qBlock N) 0 0 =
        4*(n:ℝ)*((n:ℝ)-1)*(2*(n:ℝ)-1)*
          (4*(n:ℝ)^2-9*(n:ℝ)+3)/(7*(n:ℝ)-3)^2 := by
    rw [hmeat, hcount, hcard, hA, hOne, hbeta]
    simp only [N, Nat.cast_mul, div_eq_mul_inv]
    rw [← inv_pow]
    ring
  unfold W1MeanOverlap
  simp only [Matrix.smul_apply]
  have hmeanmeat : meat SAP.P018a.members
      (fun d : SAP.P018a.Dyad (2*n) => meanVec (repeatedLaw W1MeanWitness (2*n))
        (fun ω => repeatedBlockScore W1MeanWitness
          (repeatedBeta W1MeanWitness (2*n)) ω d)) =
      AronowAudit.P018.meat AronowAudit.P018.members (qBlock (2*n)) := by
    congr 1
    funext d
    exact meanBlock_q (2*n) (by omega) d
  rw [hmeanmeat]
  simp only [Nat.cast_mul]
  change ((2*n:ℝ)/(repeatedL W1MeanWitness (2*n))^2) *
    (AronowAudit.P018.meat AronowAudit.P018.members (qBlock (2*n)) 0 0) = _
  rw [show repeatedL W1MeanWitness (2*n) = totalRecords (2*n) by rfl]
  rw [hL, hmeatSimple]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hn0, hd]
  ring

private lemma sandwich_smul_one (a : ℝ) (M : Mat 1) :
    SAP.P018a.sandwich (a • (1 : Mat 1)) M = a^2 • M := by
  ext i j
  fin_cases i
  fin_cases j
  simp [SAP.P018a.sandwich, Matrix.smul_apply]
  ring

private lemma repeatedVariance_explicit (N : ℕ) (hN : 2 ≤ N) (ω : Fin N → Unit) :
    repeatedVariance W1MeanWitness ω =
      (totalRecords N)⁻¹ ^ 2 • meat SAP.P018a.members (qBlockSAP N) := by
  have hL : totalRecords N ≠ 0 := (totalRecords_pos N hN).ne'
  have hq : (fun d : SAP.P018a.Dyad N =>
      repeatedBlockScore W1MeanWitness (betaScalar N • ![1]) ω d) = qBlockSAP N := by
    funext d
    exact (blockScore_point N ω d).trans (by rfl)
  unfold repeatedVariance
  rw [repeatedOLS_formula N hN ω, gram_point N ω]
  change SAP.P018a.sandwich (totalRecords N • (1 : Mat 1))⁻¹
    (meat SAP.P018a.members (fun d : SAP.P018a.Dyad N =>
      repeatedBlockScore W1MeanWitness (betaScalar N • ![1]) ω d)) = _
  rw [hq]
  rw [AronowAudit.P018.matrix_inverse_scale_total (1 : Mat 1) _ hL]
  have h1inv : (1 : Mat 1)⁻¹ = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.inv_def, Matrix.det_fin_one]
  rw [h1inv]
  exact sandwich_smul_one (totalRecords N)⁻¹ _

private lemma meanMeat_q (N : ℕ) (hN : 2 ≤ N) :
    meat SAP.P018a.members
      (fun d : SAP.P018a.Dyad N => meanVec (repeatedLaw W1MeanWitness N)
        (fun ω => repeatedBlockScore W1MeanWitness
          (repeatedBeta W1MeanWitness N) ω d)) =
      meat SAP.P018a.members (qBlockSAP N) := by
  congr 1
  funext d
  rw [meanBlock_q N hN d]
  rfl

private lemma repeatedTarget_zero (N : ℕ) (hN : 2 ≤ N) :
    repeatedTarget W1MeanWitness N = 0 := by
  have hstack : (fun ω : Fin N → Unit =>
      ∑ d : Dyad N, repeatedBlockScore W1MeanWitness
        (repeatedBeta W1MeanWitness N) ω d) = fun _ => (0 : Vec 1) := by
    funext ω
    rw [repeatedBeta_formula N hN]
    simp_rw [blockScore_point N ω]
    ext i
    fin_cases i
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ d : Dyad N, blockScalar N d) = 0
    exact blockScalar_sum_zero N hN
  rw [repeatedTarget, repeatedH_one N hN]
  rw [show (fun ω : Fin N → Unit =>
      ∑ d : Dyad N, repeatedBlockScore W1MeanWitness
        (repeatedBeta W1MeanWitness N) ω d) = fun _ => (0 : Vec 1) from hstack]
  simp [varMat_const, SAP.P018a.sandwich]

private lemma scaledVariance_eq_overlap (N : ℕ) (hN : 2 ≤ N) (ω : Fin N → Unit) :
    (N : ℝ) • repeatedVariance W1MeanWitness ω - repeatedTarget W1MeanWitness N =
      W1MeanOverlap N := by
  rw [repeatedVariance_explicit N hN ω, repeatedTarget_zero N hN]
  simp only [sub_zero]
  unfold W1MeanOverlap
  rw [meanMeat_q N hN]
  rw [show repeatedL W1MeanWitness N = totalRecords N by rfl]
  have hL : totalRecords N ≠ 0 := (totalRecords_pos N hN).ne'
  have hs : (N:ℝ) * (totalRecords N)⁻¹^2 = (N:ℝ) / (totalRecords N)^2 := by
    field_simp [hL]
  calc
    (N:ℝ) • ((totalRecords N)⁻¹ ^ 2 •
      meat SAP.P018a.members (qBlockSAP N)) =
        ((N:ℝ) * (totalRecords N)⁻¹^2) •
          meat SAP.P018a.members (qBlockSAP N) := by rw [smul_smul]
    _ = ((N:ℝ) / (totalRecords N)^2) •
          meat SAP.P018a.members (qBlockSAP N) := by rw [hs]


end SAP.P018a.WH.W1.P.T10_L7

theorem SAP.P018a.WH.W1.T10_L7_proof : SAP.P018a.WH.W1.T10_L7 := by
  refine ⟨SAP.P018a.WH.W1.P.T10_L7.witness_standing, ?_,
    SAP.P018a.WH.W1.P.T10_L7.common_record_kernels, ?_, ?_, ?_⟩
  · intro N d
    exact SAP.P018a.WH.W1.P.T10_L7.records_le_two N d
  · intro N hN
    exact ⟨SAP.P018a.WH.W1.P.T10_L7.repeatedH_one N hN,
      SAP.P018a.WH.W1.P.T10_L7.beta_stacked_eq_zero N hN⟩
  · intro n hn
    exact SAP.P018a.WH.W1.P.T10_L7.overlapEven_scalar n hn
  · intro N hN ω
    exact SAP.P018a.WH.W1.P.T10_L7.scaledVariance_eq_overlap N hN ω
