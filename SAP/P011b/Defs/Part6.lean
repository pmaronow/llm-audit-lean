import SAP.P011b.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

def T16Statement (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (p : ℕ) (j : Fin p) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (b : Fin p → ℝ)
    (hrank : ∀ k, ((D k)ᵀ*D k).det ≠ 0)
    (hmean : ∀ k, MeanModel (F.model k) (D k) b)
    (hθ : ∀ k i, (F.model k).theta i = olsTheta (D k) j i) : Prop :=
  (∀ k i, delta (F.model k) i = olsTheta (D k) j i*(D k*ᵥb) i-b j) ∧
  InProbability F (fun k y => scaledOracle F k y-scaledTrue F k)
    (fun k => meanBias (F.model k)) ∧
  (∀ k y c, fittedResidual (F.model k) (D k) (ols (D k)) (y+D k*ᵥc) =
    fittedResidual (F.model k) (D k) (ols (D k)) y ∧
    centered (weighted (F.model k) (y+D k*ᵥc)) =
      centered (weighted (F.model k) y) +
        (fun i => (F.model k).theta i*(D k*ᵥc) i-c j)) ∧
  ((∃ Bx By lambdaMin : ℝ, 0 < lambdaMin ∧ (∀ k i, l2 (D k i) ≤ Bx) ∧
    (∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |y i| ≤ By) ∧
    (∀ k z, lambdaMin*l2 z^2 ≤ quadratic ((1/(F.size k : ℝ)) • ((D k)ᵀ*D k)) z)) →
    Tight F (fun k y => Real.sqrt (F.size k : ℝ)*l2 (ols (D k) y-b)) ∧
    InProbability F (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (ols (D k)) y)) (scaledTrue F) ∧
    (∀ A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k), Valid F →
      (∀ k y, Maximizes (F.model k).R (F.model k).d
        (fun B => VResidual B (fittedResidual (F.model k) (D k) (ols (D k)) y)) (A k y)) →
      Conservative F (fun k y => VResidual (A k y)
        (fittedResidual (F.model k) (D k) (ols (D k)) y))))

def T17Statement
    {n : ℕ} (hn : 0 < n) (m : Model n) (i j k l : Fin n) : Prop :=
  (let E := expectation m
   let B := betaHat m
   let X : Fin n → (Fin n → ℝ) → ℝ := fun a y => weighted m y a
   let r : Fin n → (Fin n → ℝ) → ℝ := fun a y => X a y - B y
   let Q : Fin n → Fin n → ℝ := fun a b =>
     E (fun y => X a y*X b y) - E (fun y => X a y*B y) -
     E (fun y => X b y*B y) + E (fun y => (B y)^2)
   let v : Fin 4 → Fin n := ![i, j, k, l]
   let Y : Fin 4 → (Fin n → ℝ) → ℝ := fun a y => y (v a)
   let θ : Fin 4 → ℝ := fun a => m.theta (v a)
   let weightedPairs : Prop :=
     Integrable (fun y => (B y)^2) m.law ∧
     ∀ p ∈ ({(i,j), (k,l)} : Finset (Fin n × Fin n)),
       Integrable (fun y => X p.1 y*X p.2 y) m.law ∧
       Integrable (fun y => X p.1 y*B y) m.law ∧
       Integrable (fun y => X p.2 y*B y) m.law
   let weightedFourth : Prop :=
     ∀ s : Finset (Fin 4),
       Integrable (fun y => (∏ a ∈ s, X (v a) y) * (B y)^(4-s.card)) m.law
   let constantMoments : Prop :=
     ∀ s : Finset (Fin 4), s.Nonempty →
       Integrable (fun y => ∏ a ∈ s, X (v a) y) m.law
   let rawPairs : Prop :=
     Integrable (fun y => (B y)^2) m.law ∧
     ∀ p ∈ ({(i,j), (k,l)} : Finset (Fin n × Fin n)),
       Integrable (fun y => y p.1*y p.2) m.law ∧
       Integrable (fun y => y p.1*B y) m.law ∧
       Integrable (fun y => y p.2*B y) m.law
   let rawFourth : Prop :=
     ∀ s : Finset (Fin 4),
       Integrable (fun y => (∏ a ∈ s, Y a y) * (B y)^(4-s.card)) m.law
   (weightedPairs →
     (E (fun y => r i y*r j y) = Q i j ∧
      E (fun y => r k y*r l y) = Q k l)) ∧
   (weightedPairs → weightedFourth →
     (covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
        ProbabilityTheory.covariance (fun y => r i y*r j y)
          (fun y => r k y*r l y) m.law ∧
      covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
        E (fun y => r i y*r j y*r k y*r l y) - Q i j*Q k l ∧
      covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
        fourthMoment E (X i) (X j) (X k) (X l) B - Q i j*Q k l)) ∧
   (constantMoments → ∀ b : ℝ,
     covOf m (fun y => (X i y-b)*(X j y-b))
       (fun y => (X k y-b)*(X l y-b)) =
     covOf m (fun y => X i y*X j y) (fun y => X k y*X l y) -
     b*(covOf m (fun y => X i y*X j y) (X k) +
        covOf m (fun y => X i y*X j y) (X l) +
        covOf m (X i) (fun y => X k y*X l y) +
        covOf m (X j) (fun y => X k y*X l y)) +
     b^2*(covOf m (X i) (X k) + covOf m (X i) (X l) +
          covOf m (X j) (X k) + covOf m (X j) (X l))) ∧
   (rawPairs →
     (Q i j = pairMoment E (fun y => y i) (fun y => y j) B
        (m.theta i) (m.theta j) ∧
      Q k l = pairMoment E (fun y => y k) (fun y => y l) B
        (m.theta k) (m.theta l) ∧
      E (fun y => r i y*r j y) =
        pairMoment E (fun y => y i) (fun y => y j) B (m.theta i) (m.theta j) ∧
      E (fun y => r k y*r l y) =
        pairMoment E (fun y => y k) (fun y => y l) B (m.theta k) (m.theta l))) ∧
   (rawPairs → rawFourth →
     (covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
        ProbabilityTheory.covariance (fun y => r i y*r j y)
          (fun y => r k y*r l y) m.law ∧
      E (fun y => r i y*r j y*r k y*r l y) =
        rawFourthMoment E Y B θ ∧
      covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
        rawFourthMoment E Y B θ -
        pairMoment E (fun y => y i) (fun y => y j) B (m.theta i) (m.theta j) *
        pairMoment E (fun y => y k) (fun y => y l) B (m.theta k) (m.theta l))))

end
end SAP.P011b
