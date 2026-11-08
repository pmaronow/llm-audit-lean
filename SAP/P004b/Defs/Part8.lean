import SAP.P004b.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b

universe u

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

def HacExpansion : Prop :=
  ∀ {N : ℕ} (R : CircleTable N) (D : Fin N → Fin N → ℝ)
    (K : ℝ → ℝ) (b p : ℝ) (z : Assignment N) (hb : 0 < b)
    (hK : KernelConditions K) (hD : ∀ i j, D i j = D j i)
    (hdiag : ∀ i, D i i = 0) (hpos : ∀ i j, 0 ≤ D i j)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false),
    kernelVariance z (residual R z) (distanceKernel D K b) =
      (∑ i, bit (z i)*(residual R z i)^2)/(armCount z true)^2 +
      (∑ i, (1-bit (z i))*(residual R z i)^2)/(armCount z false)^2 +
      (∑ i, ∑ j ∈ Finset.univ.erase i, bit (z i)*bit (z j)*residual R z i*residual R z j*K (D i j/b))/(armCount z true)^2 -
      2*(∑ i, ∑ j ∈ Finset.univ.erase i, (1-bit (z i))*bit (z j)*residual R z i*residual R z j*K (D i j/b))/(armCount z true*armCount z false) +
      (∑ i, ∑ j ∈ Finset.univ.erase i, (1-bit (z i))*(1-bit (z j))*residual R z i*residual R z j*K (D i j/b))/(armCount z false)^2

def EpsilonProductDifference : Prop :=
  ∀ (z w : Bool) (N p yi yj h1 h0 b1 b0 : ℝ)
    (hN : N ≠ 0) (hp : p ≠ 0) (hq : 1-p ≠ 0),
    let E := fun a y c1 c0 => bit a*(y-c1)/(N*p)-(1-bit a)*(y-c0)/(N*(1-p))
    E z yi h1 h0 * E w yj h1 h0 - E z yi b1 b0 * E w yj b1 b0 =
      bit z*bit w/(N^2*p^2)*(-yi*(h1-b1)-yj*(h1-b1)+h1^2-b1^2) +
      (1-bit z)*(1-bit w)/(N^2*(1-p)^2)*(-yi*(h0-b0)-yj*(h0-b0)+h0^2-b0^2) -
      (1-bit z)*bit w/(N^2*p*(1-p))*(-yi*(h1-b1)-yj*(h0-b0)+h0*h1-b0*b1) -
      bit z*(1-bit w)/(N^2*p*(1-p))*(-yi*(h0-b0)-yj*(h1-b1)+h0*h1-b0*b1)

def EpsilonMeans : Prop :=
  ∀ {N : ℕ} (p : ℝ) (R : CircleTable N)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hN : 0 < N) (hp : 0 < p ∧ p < 1),
    let ε := nedEpsilon p R (barMu (fun _ => p) R true) (barMu (fun _ => p) R false)
    (∀ i, expect (fun _ => p) (ε i) = (nodeEffect (fun _ => p) R i-ame (fun _ => p) R)/N) ∧
    (∑ i, ∑ j, Q i j * (expect (fun _ => p) (fun z => ε i z*ε j z)-cov (fun _ => p) (ε i) (ε j))) =
      (∑ i, ∑ j, Q i j*(nodeEffect (fun _ => p) R i-ame (fun _ => p) R)*
        (nodeEffect (fun _ => p) R j-ame (fun _ => p) R))/(N : ℝ)^2

def FarCovarianceBound : Prop :=
  ∀ {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)],
  ∀ (P : PopulationSequence Space) (p d : ℝ) (K ψ : ℝ → ℝ)
    (bandwidth : ℕ → ℝ) (hp : 0 < p ∧ p < 1) (hb : BoundedOutcomes P)
    (hmetric : MetricNodeDistances P) (hspacing : QuadraticSpacing P) (hK : KernelConditions K)
    (hψ : ∀ s, 0 ≤ s → 0 ≤ ψ s) (hψanti : AntitoneOn ψ (Set.Ici 0))
    (hNED : ∃ G : ℝ, ∀ N i s, 0 ≤ s → l2Norm (fun _ => p)
      (fun z => circleAverage (P N) d i z-conditionOn (fun _ => p)
        (ball (nodeSeparation (P N)) i s) (circleAverage (P N) d i) z) ≤ G*ψ s)
    (hWD : ∀ N, WellDefined (P N) d) (hband : ∀ N, 1 ≤ bandwidth N),
    ∃ C : ℝ, ∀ᶠ N in atTop, ∀ i j, 3*bandwidth N < nodeSeparation (P N) i j →
      |cov (fun _ => p)
        (nedVRow p (circleAverage (P N) d) (nodeSeparation (P N)) K (bandwidth N)
          (barMu (fun _ => p) (circleAverage (P N) d) true)
          (barMu (fun _ => p) (circleAverage (P N) d) false) i)
        (nedVRow p (circleAverage (P N) d) (nodeSeparation (P N)) K (bandwidth N)
          (barMu (fun _ => p) (circleAverage (P N) d) true)
          (barMu (fun _ => p) (circleAverage (P N) d) false) j)| ≤
      C*(bandwidth N)^2/(N : ℝ)^4 * max
        (∑ k ∈ ball (nodeSeparation (P N)) i (bandwidth N), ψ (nodeSeparation (P N) i j/3-nodeSeparation (P N) i k))
        (∑ l ∈ ball (nodeSeparation (P N)) j (bandwidth N), ψ (nodeSeparation (P N) i j/3-nodeSeparation (P N) j l))

def T29Statement : Prop :=
  FarCovarianceBound.{u} ∧ HacExpansion ∧ EpsilonProductDifference ∧ EpsilonMeans

def T30Statement : Prop :=
  (∀ {N : ℕ} (n1 : ℕ) (hlo : 1 ≤ n1) (hhi : n1 ≤ N-1) (i : Fin N) (a : Bool),
  0 < ((completeSupport N n1).filter (fun z => z i = a)).card →
  0 < (remainderSupport n1 i a).card →
  ∀ u : {j : Fin N // j ≠ i} → Bool,
    (((completeSupport N n1).filter (fun z => z i = a ∧
      ∀ j : {j : Fin N // j ≠ i}, z j = u j)).card : ℝ) /
      (((completeSupport N n1).filter (fun z => z i = a)).card : ℝ) =
    if u ∈ remainderSupport n1 i a then 1/((remainderSupport n1 i a).card : ℝ) else 0) ∧
  (∀ {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (i : Fin N) (a : Bool),
    (∀ j, 0 < p j ∧ p j < 1) →
    marginal p R i a = expect p (fun z => R i (Function.update z i a))) ∧
  (∀ {N : ℕ} (p : ℝ) (R : CircleTable N), 0 < N → (0 < p ∧ p < 1) →
    (∀ z, linearHajek (fun _ => p) R z = linearFormula (fun _ => p) R z) ∧
    linearHajek (fun _ => p) R = augmented (fun _ => p) R (fun _ a => barMu (fun _ => p) R a) ∧
    (∀ z, augmented (fun _ => p) R (fun _ _ => barMu (fun _ => p) R true) z -
      linearHajek (fun _ => p) R z =
      (barMu (fun _ => p) R true-barMu (fun _ => p) R false) *
        (armCount z false/(N*(1-p))-1)))

end
end SAP.P004b
