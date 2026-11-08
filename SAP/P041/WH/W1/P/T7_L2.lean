import SAP.P041.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace SAP.P041.WH.W1.P.T7_L2

open Matrix
open scoped BigOperators

theorem sum_if_bool {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (y : ι → Bool) (A B : ℝ) :
    (∑ i ∈ s, (if y i then A else B)) =
      ((s.filter (fun i => y i = true)).card : ℝ) * A +
        ((s.filter (fun i => y i = false)).card : ℝ) * B := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun i => y i = true)
    (fun i => if y i then A else B)
  have hpos : (∑ i ∈ s.filter (fun i => y i = true),
      (if y i then A else B)) = ((s.filter (fun i => y i = true)).card : ℝ) * A := by
    calc
      _ = ∑ i ∈ s.filter (fun i => y i = true), A := by
        apply Finset.sum_congr rfl
        intro i hi
        have hy := (Finset.mem_filter.mp hi).2
        simp [hy]
      _ = _ := by simp
  have hneg : (∑ i ∈ s.filter (fun i => ¬ y i = true),
      (if y i then A else B)) = ((s.filter (fun i => y i = false)).card : ℝ) * B := by
    have heq : s.filter (fun i => ¬ y i = true) = s.filter (fun i => y i = false) := by
      ext i
      simp
    rw [heq]
    calc
      _ = ∑ i ∈ s.filter (fun i => y i = false), B := by
        apply Finset.sum_congr rfl
        intro i hi
        have hy := (Finset.mem_filter.mp hi).2
        simp [hy]
      _ = _ := by simp
  rw [← hsplit, hpos, hneg]

theorem gram_meat_diag {n : ℕ} (X : Matrix (Fin n) (Fin 3) ℝ)
    (r : Fin n → ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hsym : ∀ j, H j 1 = H 1 j) :
    (H * AronowAudit.P041.robustMeat X r * H) 1 1 =
      ∑ i : Fin n, r i ^ 2 * (H 1 ⬝ᵥ X i) ^ 2 := by
  classical
  -- Expand the two matrix products and the meat sum.
  unfold AronowAudit.P041.robustMeat
  change (∑ k ∈ (Finset.univ : Finset (Fin 3)),
      (∑ j ∈ (Finset.univ : Finset (Fin 3)), H 1 j *
        (∑ i ∈ (Finset.univ : Finset (Fin n)), r i ^ 2 * X i j * X i k)) * H k 1) = _
  have hmulSum3 (a : ℝ) (f : Fin 3 → ℝ) :
      a * (∑ i : Fin 3, f i) = ∑ i : Fin 3, a * f i := by
    exact Finset.mul_sum Finset.univ f a
  have hsumMul3 (f : Fin 3 → ℝ) (a : ℝ) :
      (∑ i : Fin 3, f i) * a = ∑ i : Fin 3, f i * a := by
    exact Finset.sum_mul Finset.univ f a
  have hmulSumN (a : ℝ) (f : Fin n → ℝ) :
      a * (∑ i : Fin n, f i) = ∑ i : Fin n, a * f i := by
    exact Finset.mul_sum Finset.univ f a
  have hsumMulN (f : Fin n → ℝ) (a : ℝ) :
      (∑ i : Fin n, f i) * a = ∑ i : Fin n, f i * a := by
    exact Finset.sum_mul Finset.univ f a
  have hexpand :
      (∑ k ∈ (Finset.univ : Finset (Fin 3)),
        (∑ j ∈ (Finset.univ : Finset (Fin 3)), H 1 j *
          (∑ i : Fin n, r i ^ 2 * X i j * X i k)) * H k 1) =
      ∑ k ∈ (Finset.univ : Finset (Fin 3)),
        ∑ j ∈ (Finset.univ : Finset (Fin 3)),
          ∑ i ∈ (Finset.univ : Finset (Fin n)),
            (H 1 j * (r i ^ 2 * X i j * X i k)) * H k 1 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsumMul3 (f := fun j : Fin 3 => H 1 j *
      (∑ i : Fin n, r i ^ 2 * X i j * X i k)) (a := H k 1)]
    apply Finset.sum_congr rfl
    intro j hj
    calc
      (H 1 j * (∑ i : Fin n, r i ^ 2 * X i j * X i k)) * H k 1 =
          (∑ i : Fin n, H 1 j * (r i ^ 2 * X i j * X i k)) * H k 1 := by
        rw [hmulSumN (a := H 1 j)
          (f := fun i : Fin n => r i ^ 2 * X i j * X i k)]
      _ = ∑ i : Fin n, (H 1 j * (r i ^ 2 * X i j * X i k)) * H k 1 := by
        rw [hsumMulN (f := fun i : Fin n => H 1 j * (r i ^ 2 * X i j * X i k))
          (a := H k 1)]
  rw [hexpand]
  -- Move the observation sum outside the two coefficient sums.
  have hswap₁ :
      (∑ k ∈ (Finset.univ : Finset (Fin 3)),
        ∑ j ∈ (Finset.univ : Finset (Fin 3)),
        ∑ i ∈ (Finset.univ : Finset (Fin n)),
        (H 1 j * (r i ^ 2 * X i j * X i k)) * H k 1) =
      ∑ k ∈ (Finset.univ : Finset (Fin 3)),
        ∑ i ∈ (Finset.univ : Finset (Fin n)),
        ∑ j ∈ (Finset.univ : Finset (Fin 3)),
        (H 1 j * (r i ^ 2 * X i j * X i k)) * H k 1 := by
    apply Finset.sum_congr rfl
    intro k hk
    exact Finset.sum_comm
  have hswap₂ :
      (∑ k ∈ (Finset.univ : Finset (Fin 3)),
        ∑ i ∈ (Finset.univ : Finset (Fin n)),
        ∑ j ∈ (Finset.univ : Finset (Fin 3)),
        (H 1 j * (r i ^ 2 * X i j * X i k)) * H k 1) =
      ∑ i ∈ (Finset.univ : Finset (Fin n)),
        ∑ k ∈ (Finset.univ : Finset (Fin 3)),
        ∑ j ∈ (Finset.univ : Finset (Fin 3)),
        (H 1 j * (r i ^ 2 * X i j * X i k)) * H k 1 := by
    exact Finset.sum_comm
  rw [hswap₁, hswap₂]
  apply Finset.sum_congr rfl
  intro i hi
  have hfactor :
      (∑ k ∈ (Finset.univ : Finset (Fin 3)),
        ∑ j ∈ (Finset.univ : Finset (Fin 3)),
        (H 1 j * (r i ^ 2 * X i j * X i k)) * H k 1) =
      r i ^ 2 * (H 1 ⬝ᵥ X i) ^ 2 := by
    have hdot : (∑ k : Fin 3, X i k * H k 1) = H 1 ⬝ᵥ X i := by
      change (∑ k : Fin 3, X i k * H k 1) = ∑ k : Fin 3, H 1 k * X i k
      apply Finset.sum_congr rfl
      intro k hk
      rw [hsym k]
      ring
    have hfactorSum :
        (∑ k ∈ (Finset.univ : Finset (Fin 3)),
          ∑ j ∈ (Finset.univ : Finset (Fin 3)),
            (H 1 j * (r i ^ 2 * X i j * X i k)) * H k 1) =
        r i ^ 2 * ((∑ j : Fin 3, H 1 j * X i j) *
          (∑ k : Fin 3, X i k * H k 1)) := by
      have hscalar :
          (∑ k : Fin 3, ∑ j : Fin 3,
            r i ^ 2 * ((H 1 j * X i j) * (X i k * H k 1))) =
            r i ^ 2 * (∑ k : Fin 3, ∑ j : Fin 3,
              (H 1 j * X i j) * (X i k * H k 1)) := by
        calc
          _ = ∑ k : Fin 3, r i ^ 2 *
                (∑ j : Fin 3, (H 1 j * X i j) * (X i k * H k 1)) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact (hmulSum3 (r i ^ 2)
              (fun j : Fin 3 => (H 1 j * X i j) * (X i k * H k 1))).symm
          _ = _ := (hmulSum3 (r i ^ 2)
            (fun k : Fin 3 => ∑ j : Fin 3,
              (H 1 j * X i j) * (X i k * H k 1))).symm
      have hpair :
          (∑ k : Fin 3, ∑ j : Fin 3,
            (H 1 j * X i j) * (X i k * H k 1)) =
          (∑ j : Fin 3, H 1 j * X i j) *
            (∑ k : Fin 3, X i k * H k 1) := by
        rw [Finset.sum_comm]
        exact (Fintype.sum_mul_sum _ _).symm
      calc
        _ = ∑ k : Fin 3, ∑ j : Fin 3,
              r i ^ 2 * ((H 1 j * X i j) * (X i k * H k 1)) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = r i ^ 2 * (∑ k : Fin 3, ∑ j : Fin 3,
              (H 1 j * X i j) * (X i k * H k 1)) := hscalar
        _ = _ := by rw [hpair]
    calc
      _ = r i ^ 2 * ((∑ j : Fin 3, H 1 j * X i j) *
          (∑ k : Fin 3, X i k * H k 1)) := hfactorSum
      _ = _ := by
        have hdot1 : (∑ j : Fin 3, H 1 j * X i j) = H 1 ⬝ᵥ X i := rfl
        rw [hdot1, hdot]
        ring
  exact hfactor

end SAP.P041.WH.W1.P.T7_L2

open Matrix
open scoped BigOperators

theorem SAP.P041.WH.W1.T7_L2_proof : SAP.P041.WH.W1.T7_L2 := by
  intro hL1 n cell y hI
  classical
  let X : Matrix (Fin n) (Fin 3) ℝ := SAP.P041.CitationRowsW1 cell
  let Y : Fin n → ℝ := SAP.P041.BinaryResponseW1 y
  have hfit := hL1 n cell y hI
  rcases hfit with ⟨hgram, hxy, hunit, hinv, hbeta, hpredict⟩
  have hn : n = 200 := hI.1
  have hres (i : Fin n) :
      AronowAudit.P041.olsResidual X Y i =
        Y i - (![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) (cell i) := by
    change SAP.P041.BinaryResponseW1 y i -
      (SAP.P041.CitationRowsW1 cell *ᵥ
        AronowAudit.P041.olsCoefficients (SAP.P041.CitationRowsW1 cell)
          (SAP.P041.BinaryResponseW1 y)) i = _
    change SAP.P041.BinaryResponseW1 y i -
      (SAP.P041.CitationRowsW1 cell *ᵥ
        AronowAudit.P041.olsCoefficients (SAP.P041.CitationRowsW1 cell)
          (SAP.P041.BinaryResponseW1 y)) i =
      SAP.P041.BinaryResponseW1 y i -
        (![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) (cell i)
    congr 1
    exact congrFun hpredict i
  have hres_sq (i : Fin n) :
      (AronowAudit.P041.olsResidual X Y i) ^ 2 =
        if y i then
          (1 - (![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) (cell i)) ^ 2
        else
          ((![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) (cell i)) ^ 2 := by
    rw [hres]
    cases hy : y i <;> simp [Y, SAP.P041.BinaryResponseW1, hy]
  have hfitVal (c : Fin 4) :
      (![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) c =
        SAP.P041.citationCellDesign c ⬝ᵥ SAP.P041.citationBeta := by
    fin_cases c <;>
      norm_num [SAP.P041.citationCellDesign, SAP.P041.citationBeta, dotProduct,
        Fin.sum_univ_succ]
  have hcell (c : Fin 4) :
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => cell i = c),
        (AronowAudit.P041.olsResidual X Y i) ^ 2) =
        AronowAudit.P041.binaryCellSSR 50 (SAP.P041.citationCellSurvivors c)
          (SAP.P041.citationCellDesign c ⬝ᵥ SAP.P041.citationBeta) := by
    let s := Finset.univ.filter (fun i : Fin n => cell i = c)
    have htrueFilter : s.filter (fun i => y i = true) =
        Finset.univ.filter (fun i => cell i = c ∧ y i = true) := by
      ext i
      simp [s, and_comm]
    have hfalseFilter : s.filter (fun i => y i = false) =
        Finset.univ.filter (fun i => cell i = c ∧ y i = false) := by
      ext i
      simp [s, and_comm]
    have hcellCard : s.card = 50 := by
      simpa [s] using hI.2.1 c
    have htrueNat : (s.filter (fun i => y i = true)).card =
        ((![12,25,23,42] : Fin 4 → ℕ) c) := by
      simpa [htrueFilter] using hI.2.2 c
    have htrueReal : ((s.filter (fun i => y i = true)).card : ℝ) =
        SAP.P041.citationCellSurvivors c := by
      have hcast : ((s.filter (fun i => y i = true)).card : ℝ) =
          (((![12,25,23,42] : Fin 4 → ℕ) c : ℕ) : ℝ) := by
        exact_mod_cast htrueNat
      rw [hcast]
      fin_cases c <;> norm_num [SAP.P041.citationCellSurvivors]
    have hpartition :
        (s.filter (fun i => y i = true)).card +
          (s.filter (fun i => ¬ y i = true)).card = s.card := by
      simpa only [Finset.card_eq_sum_ones] using
        (Finset.sum_filter_add_sum_filter_not s (fun i => y i = true) (fun _ => (1 : ℕ)))
    have hnegFilter : s.filter (fun i => ¬ y i = true) =
        s.filter (fun i => y i = false) := by
      ext i
      simp
    have hfalseNat : (s.filter (fun i => y i = false)).card =
        50 - ((![12,25,23,42] : Fin 4 → ℕ) c) := by
      rw [← hnegFilter]
      rw [hcellCard] at hpartition
      omega
    have hfalseReal : ((s.filter (fun i => y i = false)).card : ℝ) =
        50 - SAP.P041.citationCellSurvivors c := by
      have hcast : ((s.filter (fun i => y i = false)).card : ℝ) =
          (((50 - (![12,25,23,42] : Fin 4 → ℕ) c : ℕ) : ℝ)) := by
        exact_mod_cast hfalseNat
      have hbound : ((![12,25,23,42] : Fin 4 → ℕ) c) ≤ 50 := by
        fin_cases c <;> norm_num
      rw [Nat.cast_sub hbound] at hcast
      rw [hcast]
      fin_cases c <;> norm_num [SAP.P041.citationCellSurvivors]
    calc
      _ = ∑ i ∈ s,
          (if y i then
            (1 - (![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) c) ^ 2
          else
            ((![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) c) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hci := (Finset.mem_filter.mp hi).2
        rw [hres_sq i]
        simp [hci]
      _ = ((s.filter (fun i => y i = true)).card : ℝ) *
            (1 - (![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) c) ^ 2 +
          ((s.filter (fun i => y i = false)).card : ℝ) *
            ((![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) c) ^ 2 := by
        simpa using SAP.P041.WH.W1.P.T7_L2.sum_if_bool s y
          ((1 - (![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) c) ^ 2)
          ((![21/100,53/100,49/100,81/100] : Fin 4 → ℝ) c ^ 2)
      _ = _ := by
        rw [htrueReal, hfalseReal]
        rw [← hfitVal c]
        rfl

  have hcellFacts : ∀ c : Fin 4,
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => cell i = c),
        (AronowAudit.P041.olsResidual X Y i) ^ 2) =
        (![1833/200,2509/200,2493/200,1353/200] : Fin 4 → ℝ) c := by
    intro c
    rw [hcell c]
    fin_cases c <;>
      norm_num [AronowAudit.P041.binaryCellSSR, SAP.P041.citationCellSurvivors,
        SAP.P041.citationCellDesign, SAP.P041.citationBeta, dotProduct,
        Fin.sum_univ_succ]

  have hpartitionTotal :
      (∑ i : Fin n, (AronowAudit.P041.olsResidual X Y i) ^ 2) =
        ∑ c : Fin 4, ∑ i ∈ Finset.univ.filter (fun i : Fin n => cell i = c),
          (AronowAudit.P041.olsResidual X Y i) ^ 2 := by
    symm
    simpa using (Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := Finset.univ) (g := cell)
      (fun _ _ => Finset.mem_univ _) (fun i =>
        (AronowAudit.P041.olsResidual X Y i) ^ 2))

  have htotal : (∑ i : Fin n, (AronowAudit.P041.olsResidual X Y i) ^ 2) = 2047/50 := by
    rw [hpartitionTotal]
    simp_rw [hcellFacts]
    norm_num [Fin.sum_univ_succ]

  have hweight (i : Fin n) :
      SAP.P041.citationGramInverse 1 ⬝ᵥ X i =
        (![-1/100,1/100,-1/100,1/100] : Fin 4 → ℝ) (cell i) := by
    change SAP.P041.citationGramInverse 1 ⬝ᵥ
      SAP.P041.citationCellDesign (cell i) =
        (![-1/100,1/100,-1/100,1/100] : Fin 4 → ℝ) (cell i)
    generalize hc : cell i = c
    fin_cases c <;>
      norm_num [SAP.P041.citationCellDesign, SAP.P041.citationGramInverse,
        dotProduct, Fin.sum_univ_succ]

  have hsym : ∀ j : Fin 3, SAP.P041.citationGramInverse j 1 =
      SAP.P041.citationGramInverse 1 j := by
    intro j
    fin_cases j <;> norm_num [SAP.P041.citationGramInverse]

  have hdiag :
      (SAP.P041.citationGramInverse *
        AronowAudit.P041.robustMeat X (AronowAudit.P041.olsResidual X Y) *
        SAP.P041.citationGramInverse) 1 1 =
        ∑ i : Fin n, (AronowAudit.P041.olsResidual X Y i) ^ 2 *
          (SAP.P041.citationGramInverse 1 ⬝ᵥ X i) ^ 2 := by
    exact SAP.P041.WH.W1.P.T7_L2.gram_meat_diag X (AronowAudit.P041.olsResidual X Y)
      SAP.P041.citationGramInverse hsym

  have hhc : AronowAudit.P041.hc1Covariance X Y 1 1 = 2047/492500 := by
    unfold AronowAudit.P041.hc1Covariance
    rw [hinv]
    change ((Fintype.card (Fin n) : ℝ) /
        ((Fintype.card (Fin n) : ℝ) - (Fintype.card (Fin 3) : ℝ))) *
        ((SAP.P041.citationGramInverse *
          AronowAudit.P041.robustMeat X (AronowAudit.P041.olsResidual X Y) *
          SAP.P041.citationGramInverse) 1 1) = 2047/492500
    rw [hdiag]
    have hweighted :
        (∑ i : Fin n, (AronowAudit.P041.olsResidual X Y i) ^ 2 *
          (SAP.P041.citationGramInverse 1 ⬝ᵥ X i) ^ 2) =
          (1/10000 : ℝ) *
            ∑ i : Fin n, (AronowAudit.P041.olsResidual X Y i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hsquare :
          ((![-1/100,1/100,-1/100,1/100] : Fin 4 → ℝ) (cell i)) ^ 2 = 1/10000 := by
        generalize hc : cell i = c
        fin_cases c <;> norm_num
      rw [hweight i, hsquare]
      ring
    rw [hweighted, htotal]
    rw [hn]
    norm_num

  change (∀ c : Fin 4,
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => cell i = c),
        (AronowAudit.P041.olsResidual X Y i) ^ 2) =
        (![1833/200,2509/200,2493/200,1353/200] : Fin 4 → ℝ) c) ∧
    (∑ i : Fin n, (AronowAudit.P041.olsResidual X Y i) ^ 2) = 2047/50 ∧
    (∀ i : Fin n, SAP.P041.citationGramInverse 1 ⬝ᵥ X i =
      (![-1/100,1/100,-1/100,1/100] : Fin 4 → ℝ) (cell i)) ∧
    AronowAudit.P041.hc1Covariance X Y 1 1 = 2047/492500
  refine ⟨hcellFacts, htotal, ?_, hhc⟩
  intro i
  exact hweight i

