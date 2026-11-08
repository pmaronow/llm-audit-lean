import SAP.P042.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042

noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

def rationalMean {Ω : Type*} (s : Finset Ω) (X : Ω → ℚ) : ℚ :=
  (∑ ω ∈ s, X ω) / (s.card : ℚ)

def rationalVariance {Ω : Type*} (s : Finset Ω) (X : Ω → ℚ) : ℚ :=
  rationalMean s (fun ω => (X ω - rationalMean s X)^2)

def rationalCovariance {Ω : Type*} (s : Finset Ω) (X Y : Ω → ℚ) : ℚ :=
  rationalMean s (fun ω => (X ω - rationalMean s X) * (Y ω - rationalMean s Y))

def sixOutcome (i : Fin 6) (_g : Fin 3) : ℚ := if i.val < 3 then 1 else 0

def sixAllocations : Finset (Finset (Fin 6) × Finset (Fin 6)) :=
  ((Finset.univ.powersetCard 2) ×ˢ (Finset.univ.powersetCard 2)).filter
    (fun a => Disjoint a.1 a.2)

def sixControl (a : Finset (Fin 6) × Finset (Fin 6)) : Finset (Fin 6) :=
  Finset.univ \ (a.1 ∪ a.2)

def sixGroupMean (s : Finset (Fin 6)) : ℚ := (∑ i ∈ s, sixOutcome i 0) / 2

def sixD1 (a : Finset (Fin 6) × Finset (Fin 6)) : ℚ :=
  sixGroupMean a.1 - sixGroupMean (sixControl a)

def sixD2 (a : Finset (Fin 6) × Finset (Fin 6)) : ℚ :=
  sixGroupMean a.2 - sixGroupMean (sixControl a)

def binomialMass (n : ℕ) (x : Fin (n+1)) : ℚ := (Nat.choose n x.val:ℚ)/2^n

def binomialArmExpectation (f : Fin 101 → ℚ) : ℚ := ∑ x, binomialMass 100 x * f x

def binomialTripleExpectation (f : Fin 101 → Fin 101 → Fin 101 → ℚ) : ℚ :=
  ∑ x0, binomialMass 100 x0 *
    ∑ x1, binomialMass 100 x1 * ∑ x2, binomialMass 100 x2 * f x0 x1 x2

def binomialTripleVariance (f : Fin 101 → Fin 101 → Fin 101 → ℚ) : ℚ :=
  binomialTripleExpectation (fun x0 x1 x2 =>
    (f x0 x1 x2 - binomialTripleExpectation f)^2)

def binomialTripleCovariance (f g : Fin 101 → Fin 101 → Fin 101 → ℚ) : ℚ :=
  binomialTripleExpectation (fun x0 x1 x2 =>
    (f x0 x1 x2-binomialTripleExpectation f)*(g x0 x1 x2-binomialTripleExpectation g))

def binomialD1 (x0 x1 _x2 : Fin 101) : ℚ := ((x1.val:ℚ)-(x0.val:ℚ))/100

def binomialD2 (x0 _x1 x2 : Fin 101) : ℚ := ((x2.val:ℚ)-(x0.val:ℚ))/100

def binomialPooled (x0 x1 x2 : Fin 101) : ℚ := (binomialD1 x0 x1 x2 + binomialD2 x0 x1 x2)/2

def coversZero (estimate radius : ℝ) : Prop := estimate-radius ≤ 0 ∧ 0 ≤ estimate+radius

def coverageCount (r : ℕ) : ℕ :=
  ∑ x ∈ Finset.range 101, Nat.choose 100 x *
    ∑ t ∈ Finset.Icc (2*x-r) (min 200 (2*x+r)), Nat.choose 200 t

def binomialCoverage (r : ℕ) : ℚ := (coverageCount r:ℚ)/2^300

/-- Indicator of the integer count event under the independent-arm law. -/
def binomialCountEvent (r : ℕ) (x0 x1 x2 : Fin 101) : ℚ :=
  if |(x1.val:ℤ)+(x2.val:ℤ)-2*(x0.val:ℤ)| ≤ (r:ℤ) then 1 else 0

end
end SAP.P042
