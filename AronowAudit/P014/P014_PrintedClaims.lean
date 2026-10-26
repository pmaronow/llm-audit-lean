import AronowAudit.P014.P014_LocalRandomization

namespace AronowAudit.P014.PrintedClaims
open scoped BigOperators
noncomputable section
universe u

/-- P014-T1: the universally quantified printed unbiasedness assertion
(p. 131) under the formal local-randomization clauses of p. 130, with no ties
read for distinct subjects. The assertion is false. -/
def printed_unbiasedness : Prop :=
  ∀ {Ω : Type u} {N : ℕ} (L : FiniteLaw Ω)
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (y : Outcomes N)
    (_hN : 0 < N) (_hlocal : PrintedLocal L X b S),
    (L.map (fun ω => threshold (X ω))).expect (differenceInMeans S y) =
      ((∑ i ∈ S, printedMean (L.map (fun ω => threshold (X ω))) y i true) -
        ∑ i ∈ S, printedMean (L.map (fun ω => threshold (X ω))) y i false) /
          S.card

/-- P014-T4: the printed unbiasedness assertion under uniform permutations
of distinct fixed local scores and all formal printed clauses (pp. 130--131).
The assertion is false even under this intended local-randomization reading. -/
def printed_unbiasedness_intended_local : Prop :=
  ∀ {Ω : Type u} {N : ℕ} (L : FiniteLaw Ω)
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (v : S → ℝ) (y : Outcomes N)
    (_hN : 0 < N) (_hv : Function.Injective v) (_hw : ∀ i, inWindow b (v i))
    (_hformal : PrintedLocal L X b S) (_hintended : FiniteCorrectedLocal L X b S v),
    (L.map (fun ω => threshold (X ω))).expect (differenceInMeans S y) =
      windowContrast S (printedMean (L.map (fun ω => threshold (X ω))) y)

end
end AronowAudit.P014.PrintedClaims
