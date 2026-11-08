import SAP.P002b.Defs.WholeW1
import SAP.P002b.WH.W1.PrintedIndex
import SAP.P002b.WH.W1.QuadraticIntersections
import SAP.P002b.Bridge
import AronowAudit.P002.Wave1.Gap.GLP0021B2
import AronowAudit.P002.Wave1.Gap.GP0022B1
import AronowAudit.P002.Wave1.Gap.RepairT21
import AronowAudit.P002.Wave1.Lib.FinitePopulationCLT
import AronowAudit.P002.Wave1.Algorithm2
import AronowAudit.P002.Wave1.AlgorithmSupport.N6
import AronowAudit.P002.Wave1.AlgorithmSupport.N7
import AronowAudit.P002.Wave1.AlgorithmSupport.N8
import AronowAudit.P002.Wave1.AlgorithmSupport.N9

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace SAP.P002b.WH.W1
noncomputable section
open SAP.P002b SAP.P002b.Bridge
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- The full finite expansion and the unguarded remainder limit follow from the
checked donors. No new mathematical leaf is needed for T20. -/
theorem T20_assembly : T20WholeStatement := by
  constructor
  · intro n k P hv hm hc hx hg
    have hn : 0 < n := by have := hv.1; omega
    have hphi (a : Bool) (β : ℝ) : psi P a β none = mean (w P.pop a β) :=
      AronowAudit.P002.population_intercept_mean P.x _ hn hx hg
    have hmeans := AronowAudit.P002.mean_w_equal_at_late (toPopulation P.pop) hm hc
    refine ⟨hphi, ?_, sub_eq_zero.mpr hmeans, ?_, ?_⟩
    · intro β
      have H : (∑ i, (w P.pop true β i - w P.pop false β i)) =
          ((compliers P.pop).card : ℝ) * (late P.pop - β) :=
        AronowAudit.P002.sum_w_difference (toPopulation P.pop) hm hc β
      change (∑ i, w P.pop true β i) / (n : ℝ) -
        (∑ i, w P.pop false β i) / (n : ℝ) = _
      rw [← sub_div, ← Finset.sum_sub_distrib]
      rw [H]
      ring
    · rw [hphi, hphi]
      exact sub_eq_zero.mpr hmeans
    · intro S hS
      have H := AronowAudit.P002.corrected_oracle_expansion
        (toCovPopulation P) hv hm hc hx hg S hS
      have hpot : oracleTau P (late P.pop) S = oraclePotentialContrast P (late P.pop) S := by
        unfold oracleTau adjustedWith oraclePotentialContrast
        congr 1
        · apply AronowAudit.P002.groupMean_congr
          intro i hi
          rw [show observedW P.pop (late P.pop) S i = w P.pop true (late P.pop) i from
            AronowAudit.P002.observedW_treated (toPopulation P.pop) _ S i hi]
        · apply AronowAudit.P002.groupMean_congr
          intro i hi
          rw [show observedW P.pop (late P.pop) S i = w P.pop false (late P.pop) i from
            AronowAudit.P002.observedW_control (toPopulation P.pop) _ S i hi]
      have hcenter : oracleCenteredContrast P (late P.pop) S =
          groupMean S (residual P true (late P.pop)) -
            groupMean Sᶜ (residual P false (late P.pop)) := by
        unfold oracleCenteredContrast
        congr 1 <;> apply AronowAudit.P002.groupMean_congr <;> intro i _ <;>
          simp only [residual, dotProduct, Fintype.sum_option, augmented, one_mul, slopeDot] <;>
          ring
      exact ⟨hpot, hpot.symm.trans (H.2.trans hcenter.symm), hcenter⟩
  · intro sizes hsizes k P δ e A B r hk hδ he hA hB hr hP
    exact AronowAudit.P002.Wave1.corrected_E29_proof sizes hsizes k
      (fun j => toCovPopulation (P j)) δ e A B r hk hδ he hA hB hr hP

/-- T22 leaf 1: construct the completed run for an arbitrary admissible adaptive
policy. Adapt AlgorithmSupport.n10_proof, threading the already recorded prefix
through its induction. At left endpoint l use the measure
card(J.toFinset.filter (l < ·)); a selected-curve crossing e belongs to J, is
strictly greater than l, and is removed at the next call. Query the prescribed
policy on prefix ++ [current piece] at nextAlgorithm2Sample J e. At an empty
crossing set emit the last interval ending at top. This construction follows
every policy and cannot continue indefinitely, independently of its choices. -/
def T22_L1 : Prop :=
  ∀ (M : ℕ) (g : Fin M → ℝ → ℝ) (α : ℝ) (J : List ℝ),
    IntersectionList g J → J ≠ [] →
    ∀ choose : List (RecordedPiece M) → ℝ → Fin M,
      AdmissibleIndexPolicy g α choose →
      ∃ pieces, PolicyAlgorithm2Run g α J choose pieces

/-- Completed-run geometry and quantile validity use the existing generic
contract, which has no common-data or regression-rank hypothesis. -/
theorem algorithm2_contract {M : ℕ} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ) (α : ℝ)
    (hM : 0 < M) (hα : 0 < α ∧ α < 1) (hc : ∀ m, Continuous (g m))
    (hn : ∀ m β, 0 ≤ g m β) (hf : ∀ β, 0 ≤ f β)
    (J : List ℝ) (ps : List (RecordedPiece M)) (hps : Algorithm2Run g α J ps) :
    Algorithm2WholeContract f g α J ps := by
  have R := AronowAudit.P002.Wave1.AlgorithmSupport.glue_algorithm2_props
    AronowAudit.P002.Wave1.AlgorithmSupport.n2_proof
    AronowAudit.P002.Wave1.AlgorithmSupport.n3_proof
    AronowAudit.P002.Wave1.AlgorithmSupport.n4_proof
    AronowAudit.P002.Wave1.AlgorithmSupport.n5_proof
    AronowAudit.P002.Wave1.AlgorithmSupport.n11_proof
    AronowAudit.P002.Wave1.AlgorithmSupport.n12_proof
    AronowAudit.P002.Wave1.AlgorithmSupport.n13_proof
    AronowAudit.P002.Wave1.AlgorithmSupport.n14_proof
    f g α hM hα hc hn hf J (ps.map toPiece) ((algorithm2Run_map _ _ _ _).mpr hps)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.length_map] using R.1
  · simpa only [List.map_map, Function.comp_def, toPiece] using R.2.1
  · intro p hp
    exact R.2.2.1 (toPiece p) (List.mem_map_of_mem hp)
  · intro β
    obtain ⟨q, hq, hβ⟩ := R.2.2.2.1 β
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact ⟨p, hp, hβ⟩
  · intro p hp β hβ
    exact R.2.2.2.2.1 (toPiece p) (List.mem_map_of_mem hp) β hβ
  · intro p hp
    exact R.2.2.2.2.2.1 (toPiece p) (List.mem_map_of_mem hp)
  · have Hr := R.2.2.2.2.2.2
    change AronowAudit.P002.returnedSet f g (ps.map toPiece) = mcSet f g α at Hr
    rw [returnedSet_map] at Hr
    exact Hr

/-- Policy termination is the only new leaf; the complete finished-run contract
then supplies the length bound and every interval and set equality. -/
theorem T22_assembly (h1 : T22_L1) : T22WholeStatement := by
  intro M Qf Qg α hM hα hf hg J hJ hne
  dsimp only
  have hreg := AronowAudit.P002.arFamily_regular (fun m => toQuadratic (Qg m)) hg
  have hf' : ∀ β, 0 ≤ arFunction Qf β :=
    fun β => div_nonneg (hf.2 β) (hf.1 β).le
  have hc := algorithm2_contract (arFunction Qf) (fun m => arFunction (Qg m)) α
    hM hα hreg.1 hreg.2.1 hf' J
  refine ⟨?_, hc⟩
  intro choose hchoose
  obtain ⟨ps, hps⟩ := h1 M _ α J hJ hne choose hchoose
  exact ⟨ps, hps, hc ps hps.1⟩

/-- T26 leaf 1: finitely many real polynomials have a common finite sign
partition. Take the union of the root sets of the nonzero polynomials, which are
finite by Polynomial.finite_setOfPred_isRoot. Between consecutive roots a polynomial
cannot change sign by continuity and the intermediate value theorem. The zero
polynomial is identically zero and contributes no cuts. No degree bound is needed. -/
def T26_L1 : Prop :=
  ∀ (ι : Type) [Fintype ι] (p : ι → Polynomial ℝ),
    ∃ cuts : Finset ℝ, ∀ x y : ℝ, SameOpenCell cuts x y →
      ∀ i, (Polynomial.eval x (p i) < 0 ↔ Polynomial.eval y (p i) < 0) ∧
        (Polynomial.eval x (p i) = 0 ↔ Polynomial.eval y (p i) = 0)

/-- T26 leaf 2: apply leaf 1 to all numerators t_i, variances v_i, and comparison
polynomials t_i^2*v_j-t_j^2*v_i. On a cell, split on zero variances and zero
numerators. The zero cases give exactly zero or infinity under absStudent. With
both variances positive, square the nonnegative ratios to reduce their order to
the comparison polynomial's sign. This handles identically zero polynomials too. -/
def T26_L2 : Prop :=
  T26_L1 → ∀ (ι : Type) [Fintype ι] (t v : ι → Polynomial ℝ),
    (∀ i x, 0 ≤ Polynomial.eval x (v i)) →
    ∃ cuts : Finset ℝ, ∀ x y : ℝ, SameOpenCell cuts x y →
      ∀ i j, (absStudent (Polynomial.eval x (t i)) (Polynomial.eval x (v i)) ≤
        absStudent (Polynomial.eval x (t j)) (Polynomial.eval x (v j)) ↔
      absStudent (Polynomial.eval y (t i)) (Polynomial.eval y (v i)) ≤
        absStudent (Polynomial.eval y (t j)) (Polynomial.eval y (v j)))

/-- T26 leaf 3: finite full-randomization quantile acceptance depends only on the
weak ordering of the supported statistics. Prove the rank characterization
g(S) <= quantile(g,alpha) iff P(g(T)<g(S)) < 1-alpha, using nonempty finite support
and an interior alpha. Equal weak orderings give equal strict ranks. This works
for ties and infinity, including a critical value equal to infinity. -/
def T26_L3 : Prop :=
  ∀ {n : ℕ} (P : Population n) (S : Finset (Fin n)) (α : ℝ),
    ValidDesign P → S ∈ assignments P → (0 < α ∧ α < 1) →
    ∀ g : Finset (Fin n) → ℝ≥0∞,
      (g S ≤ quantile P g α ↔ probability P (fun T => g T < g S) < 1-α) ∧
      (∀ h : Finset (Fin n) → ℝ≥0∞,
        (∀ R ∈ assignments P, ∀ T ∈ assignments P, (g R ≤ g T ↔ h R ≤ h T)) →
        (g S ≤ quantile P g α ↔ h S ≤ quantile P h α))

/-- T26 leaf 4: a predicate constant on every complementary open cell of a
finite real cut set is a finite union of intervals. Sort the cuts, use the open
gaps including the two unbounded gaps, retain those on which the predicate is
true, and add exactly the accepted cut points as singletons. Empty cut sets and
the empty accepted set are included. No endpoint continuity is assumed. -/
def T26_L4 : Prop :=
  ∀ (s : Set ℝ) (cuts : Finset ℝ),
    (∀ x y : ℝ, SameOpenCell cuts x y → (x ∈ s ↔ y ∈ s)) → FiniteIntervalUnion s

/-- T26 leaf 5: extract the denominator-independent IV product identity from
adjusted_wald_equals_IV_proof, whose last division is its only use of hd. Reprove
its private moment and arm-identification helpers locally: inverse moment
equations imply zero instrument-residual sums, full-rank arm OLS identifies the
residualized fit, and affine contrast gives N_d*a_IV=N_y. About 200 lines copying
the checked argument; no nonzero N_d premise may be introduced. -/
def T26_L5 : Prop :=
  ∀ {n k : ℕ} (P : CovPopulation n k) (Y D : Fin n → ℝ) (S : Finset (Fin n)),
    ValidDesign P.pop → S ∈ assignments P.pop → (∀ s, ∑ i, P.x i s = 0) →
    (gram P.x S).det ≠ 0 → (gram P.x Sᶜ).det ≠ 0 →
    (ivCross P D S).det ≠ 0 → (instrumentGram P S).det ≠ 0 →
    adjustedTau P D S * ivCoefficients P Y D S (.inl 0) = adjustedTau P Y S

/-- T26 leaf 6: certify the explicit eight-unit noninterval witness by exact
rational arithmetic. Enumerate the 70 four-unit assignments. Compute the 2x2
inverse arm fits, then compare squared studentized statistics at beta=-12,-7,10.
Use the strict-rank criterion from leaf 3 (or prove it locally) to avoid square
root calculations: the numbers strictly below the observed statistic are 24,38,34,
respectively. At alpha=1/2, acceptance requires that count to be less than 35.
The rational certificate in scratch/interval_witness.py gives all inputs. -/
def T26_L6 : Prop :=
  T26_L3 → (-12 : ℝ) ∈ intervalWitnessSet ∧ (10 : ℝ) ∈ intervalWitnessSet ∧
    (-7 : ℝ) ∉ intervalWitnessSet


end
end SAP.P002b.WH.W1
