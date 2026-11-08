import SAP.P031.Defs.WholeW1
import SAP.P031.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SAP.P031.WH.W1

open scoped BigOperators Topology
open Finset Filter
open AronowAudit.P031.Wave1.LargeSampleRefutation
  (hcQ hcN hcK hcN_ge hypercubePopulation)

noncomputable section

/-- The already constructed hypercube sequence, with the SAP population record.
Row n has N=2^(4(n+1)^2), M=2, y1=q/sqrt(N), and y0=0. -/
def coveragePopulation (n : ℕ) : Population :=
  Bridge.fromPopulation (hypercubePopulation n)

/-- Uniform frequency of the zero value. The applications below have N≥16. -/
def zeroFraction {N : ℕ} (q : Fin N → ℝ) : ℝ := by
  classical
  exact ((univ.filter (fun i => q i = 0)).card : ℝ) / (N : ℝ)

/-- Uniform ordered independent-pair frequency of a nonpositive product. -/
def nonpositiveProductFraction {N : ℕ} (q : Fin N → ℝ) : ℝ := by
  classical
  exact ((univ.filter (fun ij : Fin N × Fin N => q ij.1 * q ij.2 ≤ 0)).card : ℝ) /
    (N : ℝ) ^ 2

/-- T6 leaf 1: the z=1 Neyman coverage event for the hypercube is a
nonpositive-product event for the treated pair, including zero-width intervals.
Use `Finset.card_eq_two` and the zero population effect from
`AronowAudit.P031.Wave1.LargeSampleRefutation.n3_proof n2_proof`.
`AronowAudit.P031.observed_treatment`, `observed_control`, and
`sample_variance_congr` give beta_hat=(A+B)/2 and Vhat_N=(A-B)^2/4.
Then sqrt((A-B)^2)=|A-B|, and squaring the two nonnegative sides gives
|A+B|≤|A-B| iff A*B≤0. The positive common scale in y1=q/sqrt(N) cancels.
Finally use `AronowAudit.P031.expectation_congr` to identify the events.
Estimated proof: 80–140 lines; no limit theorem is needed. -/
def T6_L1 : Prop :=
  ∀ n : ℕ,
    coverage (coveragePopulation n) neymanEstimator 1 =
      eventProbability (coveragePopulation n) (fun s =>
        ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ hcQ n i * hcQ n j ≤ 0)

/-- T6 leaf 2: the empirical hypercube distribution is symmetric about zero.
Complement every binary digit with `Equiv.swap (0 : Fin 2) 1`, transport
through `finFunctionFinEquiv`, and show hcQ of the complemented unit is -hcQ.
Use the resulting involution in `Finset.card_bij` on the strict-sign fibers.
The private flip and sign calculations in LargeSampleRefutation/N2.lean are
proof patterns; only public names listed in the report are donors.
Estimated proof: 50–90 lines. -/
def T6_L2 : Prop :=
  ∀ n : ℕ,
    (univ.filter (fun i : Fin (hcN n) => hcQ n i < 0)).card =
      (univ.filter (fun i : Fin (hcN n) => 0 < hcQ n i)).card

/-- T6 leaf 3: the zero atom of the empirical hypercube distribution vanishes.
Use `n16_proof` with `FootnoteThreeProbability.n7_proof`, `n4_proof`,
`n14_proof`, `n15_proof` to get vanishing actual distinct-pair ties; `n4_proof`
and 1/N→0 then give vanishing independent-pair ties. The product of the
zero fiber with itself is contained in the tie fiber (`Finset.card_product`,
`Finset.card_le_card`), so 0≤p0²≤tie_frequency and p0≥0. Squeeze p0 between
zero and sqrt(tie_frequency), using continuity of sqrt. All denominators are
positive by hcN_ge. Estimated proof: 100–180 lines. -/
def T6_L3 : Prop :=
  Tendsto (fun n => zeroFraction (hcQ n)) atTop (𝓝 0)

/-- T6 leaf 4: exact independent-pair sign counting on a nonempty finite set.
Partition Fin N into its negative, zero, and positive fibers. If their sizes
are b,z,b, then N=2b+z and the nonpositive-product pair count is
2b²+2Nz-z². Prove the disjoint-union and Cartesian-product counts with
`Finset.card_union_of_disjoint` and `Finset.card_product`; cast to reals and
finish by field algebra. The explicit N>0 premise excludes empty averages.
Estimated proof: 120–220 lines. -/
def T6_L4 : Prop :=
  ∀ (N : ℕ) (q : Fin N → ℝ), 0 < N →
    (univ.filter (fun i => q i < 0)).card =
      (univ.filter (fun i => 0 < q i)).card →
    nonpositiveProductFraction q =
      1 / 2 + zeroFraction q - zeroFraction q ^ 2 / 2

/-- T6 leaf 5: the standard normal mass between -1 and 1 exceeds 1/2.
Use `ProbabilityTheory.gaussianReal_apply_eq_integral` and
`StieltjesFunction.measure_Ioc`, `ProbabilityTheory.measure_cdf`, and
`AronowAudit.P053.NormalCompletion.normal_cdf_neg` to identify
2 Phi(1)-1 with that interval mass. On [-1,1],
exp(-x²/2)≥1-x²/2 by `Real.add_one_le_exp`. Integrating the lower bound
gives 5/(3 sqrt(2*pi)), which is greater than 1/2 by `Real.pi_lt_four`.
All functions are continuous on the compact interval, so their integrability
is automatic. Estimated proof: 70–140 lines. -/
def T6_L5 : Prop := (1 / 2 : ℝ) < 2 * normalCDF 1 - 1

/-- The finite bias identity and the existing full-conjunction refutation
already settle T5; there is no new leaf. -/
theorem T5_assembly : T5WholeStatement := by
  refine ⟨?_, Bridge.t5⟩
  intro P
  have hs : 2 ≤ P.M ∧ 2 ≤ P.N - P.M ∧ P.M ≤ P.N ∧ 4 ≤ P.N :=
    AronowAudit.P031.population_sizes (Bridge.toPopulation P)
  have hE : expectation P.M (fun s => neymanEstimator P s) - trueVariance P =
      popVariance (fun i => P.y1 i - P.y0 i) / ((P.N : ℝ) - 1) := by
    change expectation P.M (fun s => neyman s (observed s P.y1 P.y0)) -
      randomizationVariance P.M P.y1 P.y0 = _
    have hIdentity : expectation P.M (fun s => neyman s (observed s P.y1 P.y0)) -
        randomizationVariance P.M P.y1 P.y0 =
        popVariance (fun i => P.y1 i - P.y0 i) / ((Fintype.card (Fin P.N) : ℝ) - 1) :=
      AronowAudit.P031.neyman_bias_identity P.M hs.1
        (by simpa only [Fintype.card_fin] using hs.2.1)
        (by simpa only [Fintype.card_fin] using hs.2.2.1) P.y1 P.y0
    simpa only [Fintype.card_fin] using hIdentity
  refine ⟨hE, ?_⟩
  rw [hE]
  apply div_nonneg
  · unfold popVariance
    exact div_nonneg (sum_nonneg (fun i _ => sq_nonneg _)) (Nat.cast_nonneg _)
  · have hn : (4 : ℝ) ≤ (P.N : ℝ) := by exact_mod_cast hs.2.2.2
    linarith

/-- Restore all of T10(a) directly from the full donor bundle. -/
theorem full_shift_identities : FullShiftIdentities := by
  intro P c d
  have h := AronowAudit.P031.population_shift_invariance (Bridge.toPopulation P) c d
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro s hs
  obtain ⟨hA, hB, hR, hV⟩ := h.2.2.2 s hs
  refine ⟨?_, hA, hB, hR, hV⟩
  intro i
  exact congrFun (AronowAudit.P031.observed_shift s P.y1 P.y0 c d) i

/-- The exact finite-row formulas in T10(b), for all real a. -/
theorem footnote_exact_row (a : ℝ) (n : ℕ) : FootnoteExactRow a n := by
  refine ⟨?_, AronowAudit.P031.footnote_treated_mean_square a n, ?_⟩
  · have h : trueVariance (footnotePopulation a n) =
        (3 * a ^ 2 + 2 * a + 1 / 3) / (((footnotePopulation a n).N : ℝ) - 1) :=
      AronowAudit.P031.footnote_true_variance_formula a n
    rw [h]
    ring
  · intro s hs
    exact AronowAudit.P031.footnote_scaled_ols_formula a n s hs

/-- Every omitted clause of T10 is an existing exact result or finite
normalization, so the whole counterexample needs no new leaf. -/
theorem T10_assembly : T10WholeStatement := by
  obtain ⟨hCount, _, _, hv1, he1, hv2, he2, hvh, heh, hr1, hr2, hrh⟩ :=
    AronowAudit.P031.footnote_finite_comparisons
  refine ⟨Bridge.t10, full_shift_identities, footnote_exact_row, rfl, rfl,
    hCount, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    change (fun i : Fin 8 => if i.val < 4 then (-1 : ℝ) else 1) = _
    ext i
    fin_cases i <;> norm_num
  · change (fun i : Fin 8 => (1 : ℝ) * (if i.val < 4 then -1 else 1) + 2) = _
    ext i
    fin_cases i <;> norm_num
  · change (fun i : Fin 8 => (2 : ℝ) * (if i.val < 4 then -1 else 1) + 2) = _
    ext i
    fin_cases i <;> norm_num
  · change (fun i : Fin 8 => (1 / 2 : ℝ) * (if i.val < 4 then -1 else 1) + 2) = _
    ext i
    fin_cases i <;> norm_num
  · have hv : trueVariance (footnotePopulation 1 0) = 16 / 21 := hv1
    exact ⟨by rw [hv]; norm_num, hv, he1, hr1⟩
  · have hv : trueVariance (footnotePopulation 2 0) = 7 / 3 := hv2
    exact ⟨by rw [hv]; norm_num, hv, he2, hr2⟩
  · have hv : trueVariance (footnotePopulation (1 / 2) 0) = 25 / 84 := hvh
    exact ⟨by rw [hv]; norm_num, hv, heh, hrh⟩

/-- Reuse the proved hypercube growth, positive exact variance, and normal
limit. The fixed treatment arm is legal and every row is unbalanced. -/
theorem coverage_population_properties :
    GrowingPopulations coveragePopulation ∧
    (∀ n, (coveragePopulation n).N ≠ 2 * (coveragePopulation n).M) ∧
    (∀ n, 0 < trueVariance (coveragePopulation n)) ∧
    StandardizedNormalLimit coveragePopulation := by
  have hV := AronowAudit.P031.Wave1.LargeSampleRefutation.n3_proof
    AronowAudit.P031.Wave1.LargeSampleRefutation.n2_proof
  have hNormal := AronowAudit.P031.Wave1.LargeSampleRefutation.n12_proof hV
    AronowAudit.P031.Wave1.LargeSampleRefutation.n4_proof
    AronowAudit.P031.Wave1.LargeSampleRefutation.n5_proof
    (AronowAudit.P031.Wave1.LargeSampleRefutation.n7_proof
      AronowAudit.P031.Wave1.LargeSampleRefutation.n6_proof)
    AronowAudit.P031.Wave1.LargeSampleRefutation.n8_proof
    AronowAudit.P031.Wave1.LargeSampleRefutation.n9_proof
    (AronowAudit.P031.Wave1.LargeSampleRefutation.n10_proof hV)
    AronowAudit.P031.Wave1.LargeSampleRefutation.n11_proof
  refine ⟨AronowAudit.P031.Wave1.LargeSampleRefutation.n1_proof, ?_, ?_, hNormal⟩
  · intro n
    change hcN n ≠ 2 * 2
    have := hcN_ge n
    omega
  · intro n
    change 0 < AronowAudit.P031.trueVariance (hypercubePopulation n)
    rw [(hV n).1]
    have hn : (16 : ℝ) ≤ (hcN n : ℝ) := by exact_mod_cast hcN_ge n
    exact div_pos (by linarith) (mul_pos (mul_pos (by norm_num) (by linarith))
      (by linarith))

/-- A coverage limit strictly below nominal contradicts the definition using
eventual lower bounds. This is order/topology glue, independent of the design. -/
theorem not_conservative_of_limit (P : ℕ → Population) (V : VarianceEstimator)
    (q z : ℝ) (hq : q < 2 * normalCDF z - 1)
    (hLimit : Tendsto (fun n => coverage (P n) V z) atTop (𝓝 q)) :
    ¬ ConservativeCoverage P V z := by
  intro h
  let ε := (2 * normalCDF z - 1 - q) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hLower := ge_of_tendsto hLimit (h ε hε)
  dsimp [ε] at hLower
  linarith

/-- The five new finite/analytic leaves give an independent coverage
counterexample for the Neyman/HC2 contrast; the OLS/CE warning is already proved. -/
theorem T6_assembly (h1 : T6_L1) (h2 : T6_L2) (h3 : T6_L3)
    (h4 : T6_L4) (h5 : T6_L5) : T6WholeStatement := by
  have hPairLimit : Tendsto (fun n => nonpositiveProductFraction (hcQ n))
      atTop (𝓝 (1 / 2)) := by
    have hConst : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)) :=
      tendsto_const_nhds
    have h := (hConst.add h3).sub ((h3.pow 2).div_const 2)
    have h' : Tendsto (fun n => (1 / 2 : ℝ) + zeroFraction (hcQ n) -
        zeroFraction (hcQ n) ^ 2 / 2) atTop (𝓝 (1 / 2)) := by
      simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero, sub_zero] using h
    apply h'.congr
    intro n
    exact (h4 (hcN n) (hcQ n) (by have := hcN_ge n; omega) (h2 n)).symm
  have hInv : Tendsto (fun n => 1 / (hcN n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp
      AronowAudit.P031.Wave1.LargeSampleRefutation.n1_proof
  have hCompare (n : ℕ) :
      |coverage (coveragePopulation n) neymanEstimator 1 -
        nonpositiveProductFraction (hcQ n)| ≤ 1 / (hcN n : ℝ) := by
    rw [h1 n]
    exact AronowAudit.P031.Wave1.LargeSampleRefutation.n4_proof
      (hypercubePopulation n) (fun i j => hcQ n i * hcQ n j ≤ 0) rfl
      (fun i j h => by simpa only [mul_comm] using h)
  have hNeyman : Tendsto (fun n => coverage (coveragePopulation n) neymanEstimator 1)
      atTop (𝓝 (1 / 2)) := by
    have hLo := hPairLimit.sub hInv
    have hHi := hPairLimit.add hInv
    simp only [sub_zero, add_zero] at hLo hHi
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hLo hHi
    · intro n
      have h := (abs_le.mp (hCompare n)).1
      linarith
    · intro n
      have h := (abs_le.mp (hCompare n)).2
      linarith
  have hHC2 : Tendsto (fun n => coverage (coveragePopulation n) hc2Estimator 1)
      atTop (𝓝 (1 / 2)) := by
    apply hNeyman.congr
    intro n
    exact AronowAudit.P031.coverage_neyman_eq_hc2
      (Bridge.toPopulation (coveragePopulation n)) 1
  obtain ⟨hGrow, hUnbalanced, hPositive, hNormal⟩ := coverage_population_properties
  exact ⟨Bridge.t6, h5, coveragePopulation, hGrow, hUnbalanced, hPositive, hNormal,
    hNeyman, hHC2,
    not_conservative_of_limit coveragePopulation neymanEstimator (1 / 2) 1 h5 hNeyman,
    not_conservative_of_limit coveragePopulation hc2Estimator (1 / 2) 1 h5 hHC2⟩

end
end SAP.P031.WH.W1
