import AronowAudit.P014.P014_LocalRandomization

namespace AronowAudit.P014.PrintedClaims
open scoped BigOperators
noncomputable section
universe u

/-- Exact universally quantified historical assertion; a proposition, not an axiom. -/
def printed_unbiasedness : Prop :=
  ∀ {Ω : Type u} {N : ℕ} (L : FiniteLaw Ω)
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (y : Outcomes N)
    (_hN : 0 < N) (_hlocal : PrintedLocal L X b S),
    (L.map (fun ω => threshold (X ω))).expect (differenceInMeans S y) =
      ((∑ i ∈ S, printedMean (L.map (fun ω => threshold (X ω))) y i true) -
        ∑ i ∈ S, printedMean (L.map (fun ω => threshold (X ω))) y i false) /
          S.card

/-- Exact universally quantified historical assertion; a proposition, not an axiom. -/
def printed_unbiasedness_intended_local : Prop :=
  ∀ {Ω : Type u} {N : ℕ} (L : FiniteLaw Ω)
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (v : S → ℝ) (y : Outcomes N)
    (_hN : 0 < N) (_hv : Function.Injective v) (_hw : ∀ i, inWindow b (v i))
    (_hformal : PrintedLocal L X b S) (_hintended : FiniteCorrectedLocal L X b S v),
    (L.map (fun ω => threshold (X ω))).expect (differenceInMeans S y) =
      windowContrast S (printedMean (L.map (fun ω => threshold (X ω))) y)

end
end AronowAudit.P014.PrintedClaims
