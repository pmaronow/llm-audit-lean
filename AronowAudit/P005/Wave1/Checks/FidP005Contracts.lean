import AronowAudit.P005.Wave1.Gap.FidP005

namespace AronowAudit.P005.Wave1.FidP005Contracts

open Filter

/- Referee 1 approves the mapper's Lean signature verbatim, with no fixes.
Referee 2's sole fix concerns reader prose:
"For every $n\ge3$, the dimension satisfies $0\le d_n\le n$; zero covariates are allowed, including sequences with both zero and positive dimensions."
The same fix explicitly says:
"No change to the proposed Lean signature or paper proof is required." -/

/-- P005-T17(e): the approved statement from `map-fid-P005/map.json`,
record 0, `proposed_statement_lean`, approved unchanged as a Lean statement
by `ref1-fid-P005/referee.json` and `ref2-fid-P005/referee.json`, record 0.
The binders and conclusion are copied from that record independently of the final theorem. -/
def approvedContract_P005_T17 : Prop := ∀ (d m : ℕ → ℕ)
    (P : (n : ℕ) → AronowAudit.P005.Population n (d n)) (h :
      (∀ n, 3 ≤ n → d n ≤ n ∧ 0 < m n ∧ m n < n) ∧
      (∃ K : ℝ, 0 ≤ K ∧ ∀ n, 3 ≤ n →
        AronowAudit.P005.popMean (fun i => (P n).yT i^2) ≤ K ∧
        AronowAudit.P005.popMean (fun i => (P n).yC i^2) ≤ K ∧
        ∀ k, AronowAudit.P005.popMean (fun i => (P n).x i k^2) ≤ K) ∧
      (∀ᶠ n in Filter.atTop, AronowAudit.P005.standardized (P n)) ∧
      (∃ lo hi : ℝ, 0 < lo ∧ lo < hi ∧ hi < 1 ∧
        ∀ n, 3 ≤ n → lo < AronowAudit.P005.pT n (m n) ∧ AronowAudit.P005.pT n (m n) < hi)),
    Asymptotics.IsBigO Filter.atTop
      (fun n => 1/(AronowAudit.P005.pT n (m n)*AronowAudit.P005.pC n (m n)*n*(n-1)) *
        AronowAudit.P005.popMean (fun i => AronowAudit.P005.leverage (P n) i *
          (AronowAudit.P005.commonResidual (P n) (m n) (P n).yT i-AronowAudit.P005.commonResidual (P n) (m n) (P n).yC i)^2))
      (fun n => AronowAudit.P005.kappa (P n)/n)

example : approvedContract_P005_T17 :=
  @AronowAudit.P005.Wave1.corrected_contraction_order

#print axioms approvedContract_P005_T17
#print axioms AronowAudit.P005.Wave1.corrected_contraction_order

end AronowAudit.P005.Wave1.FidP005Contracts
