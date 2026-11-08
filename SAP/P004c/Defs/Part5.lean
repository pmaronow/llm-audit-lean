import SAP.P004c.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
namespace SAP.P004c
open scoped BigOperators Classical
open MeasureTheory Filter
noncomputable section

/-- The denominator error on nonempty treated arms, extended by zero on empty arms. -/
def denominatorError (p : ℝ) (N : ℕ) (z : Assignment N) : ℝ :=
  if 0 < armCount z true then |(N : ℝ)^2/(armCount z true)^2-1/p^2| else 0

/-- T34 retains the exact corrected identities, finite kernel bound and denominator rate. -/
def T34Statement : Prop :=
  (∀ (N : ℕ) (z : Assignment N) (p S : ℝ), 0 < N →
    0 < armCount z true → (0 < p ∧ p < 1) →
    |N * ((N*S)/(armCount z true)^2 - (N*S)/((N : ℝ)^2*p^2))| =
      |(N : ℝ)^2/(armCount z true)^2 - 1/p^2| * |S| ∧
    |(N : ℝ)^2/(armCount z true)^2 - 1/p^2| =
      |((armCount z true/N-p)*(armCount z true/N+p))/(p^2*(armCount z true/N)^2)|) ∧
  (∀ (N : ℕ) (z : Assignment N) (e : Fin N → ℝ)
    (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ) (b Kmax : ℝ),
    0 < N → 0 < b → (∀ t, 0 ≤ t → |K t| ≤ Kmax) →
    (∀ t, 1 < t → K t = 0) → (∀ i j, 0 ≤ D i j) →
    |(∑ i, ∑ j ∈ Finset.univ.erase i,
      bit (z i)*bit (z j)*e i*e j*K (D i j/b))/N| ≤
        Kmax * (sSup (Set.range (fun i => |e i|)))^2 * maxDegree (fun i => ball D i b)) ∧
  (∀ p : ℝ, (0 < p ∧ p < 1) →
    BigOp (fun _ _ => p) (denominatorError p)
      (fun N => (Real.sqrt N)⁻¹)) ∧
  (|(8 : ℝ)^2/5^2 - 1/(1/2 : ℝ)^2| * |(-1/4 : ℝ)| = 9/25 ∧
    ((8 : ℝ)^2/5^2 - 1/(1/2 : ℝ)^2) * |(-1/4 : ℝ)| = -9/25 ∧
    ¬ (9/25 : ℝ) ≤ -9/25)

/-- Proposition 1, with the paper's forced-coordinate marginalization made explicit. -/
def T39Statement : Prop :=
  ∀ (N : ℕ) (p : ℝ) (R : CircleTable N), 0 < N → (0 < p ∧ p < 1) →
    expect (fun _ => p) (ht (fun _ => p) R) =
      (∑ i, (expect (fun _ => p) (fun z => R i (Function.update z i true)) -
        expect (fun _ => p) (fun z => R i (Function.update z i false)))) / N

def T40Statement : Prop :=
  ∀ (N : ℕ) {A : Type u} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (d : ℝ)
    (w : Fin N → Assignment N → ℝ) (g : Fin N → A → ℝ) (f : A → ℝ),
    0 < N → (∀ i, (∑ z, w i z) = 1) → (∀ i z, 0 ≤ w i z) →
    (∀ x z, P.outcome x z = (∑ j, bit (z j)*g j x)+f x) → WellDefined P d →
    (∀ i x, marginalLawEffect w (P.outcome x) i = g i x) ∧
    (∀ i, marginalLawEffect w (circleAverage P d i) i =
      (∫ x in region P i d, g i x ∂P.zeta)/(P.zeta (region P i d)).toReal) ∧
    (∑ i, marginalLawEffect w (circleAverage P d i) i)/N =
      (∑ i, (∫ x in region P i d, g i x ∂P.zeta)/(P.zeta (region P i d)).toReal)/N

def T41Statement : Prop :=
  ∀ {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ),
    (0 < p ∧ p < 1) → 0 ≤ d → SpatialLocalConditions P →
    (∀ᶠ N in atTop, WellDefined (P N) d) →
    Asymptotics.IsBigO atTop
      (fun N => variance (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)))
      (fun N => (N : ℝ)⁻¹) ∧
    (Nondegenerate (fun N => variance (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d))) →
      NormalLimit (fun _ _ => p) (fun N z =>
        (ht (fun _ => p) (circleAverage (P N) d) z - ame (fun _ => p) (circleAverage (P N) d)) /
          Real.sqrt (variance (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)))))

def T42Statement : Prop :=
  ∀ {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ),
    (0 < p ∧ p < 1) → 0 ≤ d → SpatialLocalConditions P →
    (∀ᶠ N in atTop, WellDefined (P N) d) →
    Nondegenerate (fun N => variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d))) →
    NormalLimit (fun _ _ => p) (fun N z =>
      (hajek (circleAverage (P N) d) z-ame (fun _ => p) (circleAverage (P N) d)) /
        Real.sqrt (variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d))))

def T44Statement : Prop :=
  ∀ {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ),
    (0 < p ∧ p < 1) → 0 ≤ d → BoundedOutcomes P →
    (∀ᶠ N in atTop, WellDefined (P N) d) → NEDConditions P p d →
    MetricNodeDistances P → QuadraticSpacing P →
    (∀ N, 0 < N → WellDefined (P N) d →
      expect (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)) =
        ame (fun _ => p) (circleAverage (P N) d)) ∧
    Asymptotics.IsBigO atTop
      (fun N => variance (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)))
      (fun N => (N : ℝ)⁻¹) ∧
    InProb (fun _ _ => p) (fun N z => Real.sqrt N *
      (linearHajek (fun _ => p) (circleAverage (P N) d) z - hajek (circleAverage (P N) d) z)) ∧
    (Nondegenerate (fun N => variance (fun _ => p)
        (linearHajek (fun _ => p) (circleAverage (P N) d))) →
      NormalLimit (fun _ _ => p) (fun N z =>
        (hajek (circleAverage (P N) d) z - ame (fun _ => p) (circleAverage (P N) d)) /
          Real.sqrt (variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d)))))

end
end SAP.P004c
