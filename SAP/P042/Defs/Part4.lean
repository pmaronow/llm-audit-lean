import SAP.P042.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042

noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Classical

/-- Witness A: a sharp-null population and its uniform, three-arm randomization. -/
def SixVoterWitness : Prop :=
  (∀ (i : Fin 6) (g : Fin 3), sixOutcome i g = sixOutcome i 0) ∧
  sixAllocations.card = 90 ∧
  (Nat.choose 6 2 * Nat.choose 4 2 = 90) ∧
  (∀ a ∈ sixAllocations, a.1.card = 2 ∧ a.2.card = 2 ∧
    Disjoint a.1 a.2 ∧ (sixControl a).card = 2) ∧
  rationalMean sixAllocations sixD1 = 0 ∧
  rationalMean sixAllocations sixD2 = 0 ∧
  rationalVariance sixAllocations sixD1 = 3/10 ∧
  rationalVariance sixAllocations sixD2 = 3/10 ∧
  rationalCovariance sixAllocations sixD1 sixD2 = 3/20 ∧
  normalizedWeight (fun _ : Fin 2 => (3:ℝ)/10) 0 = 1/2 ∧
  normalizedWeight (fun _ : Fin 2 => (3:ℝ)/10) 1 = 1/2 ∧
  diagonalVariance (fun _ : Fin 2 => (3:ℝ)/10) = 3/20 ∧
  (totalWeight (fun _ : Fin 2 => (3:ℝ)/10))⁻¹ = 3/20 ∧
  rationalVariance sixAllocations (fun a => (sixD1 a + sixD2 a)/2) = 9/40 ∧
  rationalMean sixAllocations (fun a => ((sixD1 a + sixD2 a)/2)^2) = 9/40 ∧
  rationalVariance sixAllocations (fun a => (sixD1 a + sixD2 a)/2) =
    (3/2:ℚ)*(3/20) ∧
  (3/20:ℚ) < rationalVariance sixAllocations (fun a => (sixD1 a + sixD2 a)/2)

/-- Witness B: independent binomial arms, their shared-control contrasts, and
the exact coverage of the two intervals with multiplier 49/25. -/
def BinomialWitness : Prop :=
  (∀ x, 0 ≤ binomialMass 100 x) ∧
  binomialArmExpectation (fun _ => 1) = 1 ∧
  binomialTripleExpectation binomialD1 = 0 ∧
  binomialTripleExpectation binomialD2 = 0 ∧
  binomialTripleVariance binomialD1 = 1/200 ∧
  binomialTripleVariance binomialD2 = 1/200 ∧
  binomialTripleCovariance binomialD1 binomialD2 = 1/400 ∧
  binomialTripleVariance (fun x0 _ _ => (x0.val:ℚ)/100) = 1/400 ∧
  normalizedWeight (fun _ : Fin 2 => (1:ℝ)/200) 0 = 1/2 ∧
  normalizedWeight (fun _ : Fin 2 => (1:ℝ)/200) 1 = 1/2 ∧
  diagonalVariance (fun _ : Fin 2 => (1:ℝ)/200) = 1/400 ∧
  (totalWeight (fun _ : Fin 2 => (1:ℝ)/200))⁻¹ = 1/400 ∧
  (∀ x0 x1 x2, binomialPooled x0 x1 x2 =
    ((x1.val:ℚ)+(x2.val:ℚ)-2*(x0.val:ℚ))/200) ∧
  binomialTripleExpectation binomialPooled = 0 ∧
  binomialTripleVariance binomialPooled = 3/800 ∧
  binomialTripleVariance binomialPooled = (3/2:ℚ)*(1/400) ∧
  (1/400:ℚ) < binomialTripleVariance binomialPooled ∧
  (49/25:ℝ)*Real.sqrt (1/400) = 49/500 ∧
  (∀ x0 x1 x2 : Fin 101,
    let q : ℤ := (x1.val:ℤ)+(x2.val:ℤ)-2*(x0.val:ℤ)
    (coversZero (binomialPooled x0 x1 x2 : ℝ) (49/500) ↔ |q| ≤ 19) ∧
    (coversZero (binomialPooled x0 x1 x2 : ℝ)
      ((49/25)*Real.sqrt (3/800)) ↔ |q| ≤ 24)) ∧
  ((24:ℝ)^2 < 200^2*(49/25)^2*(3/800) ∧
    (200:ℝ)^2*(49/25)^2*(3/800) = 14406/25 ∧
    (200:ℝ)^2*(49/25)^2*(3/800) < 25^2) ∧
  binomialTripleExpectation (fun x0 x1 x2 =>
    if coversZero (binomialPooled x0 x1 x2 : ℝ)
      ((49/25)*Real.sqrt (1/400)) then 1 else 0) = binomialCoverage 19 ∧
  binomialTripleExpectation (fun x0 x1 x2 =>
    if coversZero (binomialPooled x0 x1 x2 : ℝ)
      ((49/25)*Real.sqrt (3/800)) then 1 else 0) = binomialCoverage 24 ∧
  binomialCoverage 19 =
    (56571224212801903286613058436266763680981055287737934836552182663205237639665445537726383:ℚ)
      /2^295 ∧
  Nat.Coprime
    56571224212801903286613058436266763680981055287737934836552182663205237639665445537726383
    (2^295) ∧
  (888:ℚ)/1000 < binomialCoverage 19 ∧
  binomialCoverage 19 < 889/1000 ∧
  (889:ℚ)/1000 < 95/100 ∧
  (95:ℚ)/100 < binomialCoverage 24

def T1Statement : Prop := SixVoterWitness ∧ BinomialWitness

end
end SAP.P042
