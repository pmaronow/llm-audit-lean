import AronowAudit.P003.Wave1.Gap.FidP003

/-! Compile-time statement checks and the named printed-contract negation for P003-T28.
The failed-search-as-empty convention below is essential to the numerical refutation. -/

namespace AronowAudit.P003.Wave1

namespace FidP003Contracts

/-- P003-T28, `map-fid-P003/map.json`, record 0, `proposed_statement_lean`:
the certificate's approved type, copied verbatim. Both `ref1-fid-P003/referee.json`
and `ref2-fid-P003/referee.json` accept it with `fixes: []`; no statement fix applies.
The mapper's proof placeholder is replaced by the active check following this definition. -/
def approvedContract_T28 : Prop :=
    ¬ (∀ (v : AronowAudit.P003.Counts) (m K : ℕ) (α ε : ℝ),
      0 < m → v.total = 2 * m → 0 < K →
      (0 < α ∧ α < 1) → (0 ≤ ε ∧ ε < α) →
      (AronowAudit.P003.uniformProb
        (fun ω : AronowAudit.P003.MonteSpace v.total m K =>
          AronowAudit.P003.exactInterval α
              (AronowAudit.P003.canonicalObserved v ω.1.val) ⊆
            AronowAudit.P003.monteInterval false α ε
              (AronowAudit.P003.canonicalObserved v ω.1.val) ω.2) ≥
        1 - 2 * (AronowAudit.P003.testBudget v.total : ℝ) *
          Real.exp (-2 * (K : ℝ) * ε ^ 2)) ∧
      (0 < α - 2 * ε →
        AronowAudit.P003.uniformProb
          (fun ω : AronowAudit.P003.MonteSpace v.total m K =>
            AronowAudit.P003.monteInterval false α ε
                (AronowAudit.P003.canonicalObserved v ω.1.val) ω.2 ⊆
              AronowAudit.P003.exactInterval (α - 2 * ε)
                (AronowAudit.P003.canonicalObserved v ω.1.val)) ≥
          1 - 2 * (AronowAudit.P003.testBudget v.total : ℝ) *
            Real.exp (-2 * (K : ℝ) * ε ^ 2)))

example : approvedContract_T28 :=
  @AronowAudit.P003.Wave1.printed_monte_probability_contract_refuted

/-- P003-T28: the full universal closure of Lemma B.15, p. 27, (B.78)-(B.79),
`runs/P003/staged/main.txt:2180-2188`, with the parameter domains clarified in
`runs/P003/lean/targets.json`, P003-T28. Algorithms 4.3-4.5 are on pp. 8-9
(`main.txt:599-626,657-694`); the literal binary search is Algorithm B.1, p. 20
(`main.txt:1509-1515`). `map-fid-P003`, record 0, and both accepting referees
approve the following explicitly qualified reading.

All natural count vectors, natural m,K, and real α,ε are quantified, with
n=v.total=2m, m>0, K>0, 0<α<1, and 0≤ε<α. Only (B.79) requires α-2ε>0;
α-2ε<1 follows from the other premises. There is no n≥15 restriction and no
endpoint-return clause or conditioning on successful search.

Conventions: counts list types (1,1),(1,0),(0,1),(0,0); `canonicalObserved` uses
their successive blocks of zero-based labels. Exact p-values include tail ties,
acceptance is p≥α, and `exactInterval` is the real closed hull of accepted
effects, empty if none are accepted. The printed ⊂ is read as ordinary set
inclusion, allowing equality, over all real points. Monte Carlo acceptance is
S+ε≥α. `uniformProb` is event cardinality divided by space cardinality in ℝ on
the joint uniform product of the observed m-subset and (2D(n)+1) independent
batches of K m-subsets, where D(n)=(n+1)(Nat.log2(n+1)+3) is the printed floor
logarithm budget. Possible-table enumeration uses bounded natural subtraction;
effects use integer subtraction and exact rational division embedded in ℝ.
Empty sums are zero and rational/real division is total with x/0=0; the stated
design and K>0 avoid zero denominators in these experiments.

`monteInterval false` uses the printed post-update adjacency test and boundary
clauses, with the lower search on complemented outcomes. It uses n+3 search
fuel and modular indexing of the finite batch pool. Returned integer endpoints
lo,hi give the closed interval [-lo/n,hi/n]. If either endpoint is absent, it
gives ∅: this totalization is absent from the paper and is essential here.
The certificate's singleton upper search fails for every fuel, every rejection
function and every index, so the cutoff and batch wrapping do not create its
failure. Its exact interval contains 1, so the empty-hull convention is unused.
Algorithms 4.3/4.5 generate that singleton from admissible data although B.1
requires a strict input range; this concerns the composite printed algorithm.
Without the failure-as-empty convention the witness establishes undefinedness,
not a convention-independent numerical refutation. -/
def printedContract_T28 : Prop :=
    ∀ (v : AronowAudit.P003.Counts) (m K : ℕ) (α ε : ℝ),
      0 < m → v.total = 2 * m → 0 < K →
      (0 < α ∧ α < 1) → (0 ≤ ε ∧ ε < α) →
      (AronowAudit.P003.uniformProb
        (fun ω : AronowAudit.P003.MonteSpace v.total m K =>
          AronowAudit.P003.exactInterval α
              (AronowAudit.P003.canonicalObserved v ω.1.val) ⊆
            AronowAudit.P003.monteInterval false α ε
              (AronowAudit.P003.canonicalObserved v ω.1.val) ω.2) ≥
        1 - 2 * (AronowAudit.P003.testBudget v.total : ℝ) *
          Real.exp (-2 * (K : ℝ) * ε ^ 2)) ∧
      (0 < α - 2 * ε →
        AronowAudit.P003.uniformProb
          (fun ω : AronowAudit.P003.MonteSpace v.total m K =>
            AronowAudit.P003.monteInterval false α ε
                (AronowAudit.P003.canonicalObserved v ω.1.val) ω.2 ⊆
              AronowAudit.P003.exactInterval (α - 2 * ε)
                (AronowAudit.P003.canonicalObserved v ω.1.val)) ≥
          1 - 2 * (AronowAudit.P003.testBudget v.total : ℝ) *
            Real.exp (-2 * (K : ℝ) * ε ^ 2))

end FidP003Contracts

/-- Negation of P003-T28's full printed probability contract under the approved
failed-search-as-empty convention. The existing certificate contradicts (B.78);
it does not individually refute (B.79) or the corrected-search bounds. -/
theorem printed_monte_probability_contract_refuted_printed_negation :
    ¬ FidP003Contracts.printedContract_T28 :=
  printed_monte_probability_contract_refuted

namespace FidP003Contracts

/-- The exact negation endpoint for P003-T28, including its full universal closure. -/
abbrev Target_T28 : Prop := ¬ printedContract_T28

example : Target_T28 :=
  AronowAudit.P003.Wave1.printed_monte_probability_contract_refuted_printed_negation

example : Target_T28 ↔ ¬ printedContract_T28 := Iff.rfl

end FidP003Contracts

#print axioms AronowAudit.P003.Wave1.printed_monte_probability_contract_refuted
#print axioms AronowAudit.P003.Wave1.printed_monte_probability_contract_refuted_printed_negation

end AronowAudit.P003.Wave1
