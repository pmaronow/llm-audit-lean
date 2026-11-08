import AronowAudit.P011.Wave1.Gap.Fid2P011

namespace AronowAudit.P011.Wave1.Fid2P011Contracts

open AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal
noncomputable section

/-- Approved statement: `~/lean-work/runs/map-fid2-P011/map.json`, record 0
(`P011-T17`, `proposed_statement_lean`), accepted without fixes by
`ref1-fid2-P011` and `ref2-fid2-P011`. -/
def approvedContract_T17 : Prop :=
  ∀
    {n : ℕ} (hn : 0 < n) (m : Model n) (i j k l : Fin n),
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
          AronowAudit.P011.Wave1.rawFourthMoment E Y B θ ∧
        covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
          AronowAudit.P011.Wave1.rawFourthMoment E Y B θ -
          pairMoment E (fun y => y i) (fun y => y j) B (m.theta i) (m.theta j) *
          pairMoment E (fun y => y k) (fun y => y l) B (m.theta k) (m.theta l))))

example : approvedContract_T17 := @AronowAudit.P011.Wave1.corrected_covariance_expansion_moments

/-- Approved definition body: `map-fid2-P011/map.json`, record 0,
`definition_body_lean`, copied verbatim. -/
example
    {Ω : Type} (E : (Ω → ℝ) → ℝ) (Y : Fin 4 → Ω → ℝ)
    (B : Ω → ℝ) (θ : Fin 4 → ℝ) :
    AronowAudit.P011.Wave1.rawFourthMoment E Y B θ =
  θ 0*θ 1*θ 2*θ 3 * E (fun y => Y 0 y*Y 1 y*Y 2 y*Y 3 y) -
  θ 0*θ 1*θ 2 * E (fun y => Y 0 y*Y 1 y*Y 2 y*B y) -
  θ 0*θ 1*θ 3 * E (fun y => Y 0 y*Y 1 y*Y 3 y*B y) -
  θ 0*θ 2*θ 3 * E (fun y => Y 0 y*Y 2 y*Y 3 y*B y) -
  θ 1*θ 2*θ 3 * E (fun y => Y 1 y*Y 2 y*Y 3 y*B y) +
  θ 0*θ 1 * E (fun y => Y 0 y*Y 1 y*(B y)^2) +
  θ 0*θ 2 * E (fun y => Y 0 y*Y 2 y*(B y)^2) +
  θ 0*θ 3 * E (fun y => Y 0 y*Y 3 y*(B y)^2) +
  θ 1*θ 2 * E (fun y => Y 1 y*Y 2 y*(B y)^2) +
  θ 1*θ 3 * E (fun y => Y 1 y*Y 3 y*(B y)^2) +
  θ 2*θ 3 * E (fun y => Y 2 y*Y 3 y*(B y)^2) -
  θ 0 * E (fun y => Y 0 y*(B y)^3) -
  θ 1 * E (fun y => Y 1 y*(B y)^3) -
  θ 2 * E (fun y => Y 2 y*(B y)^3) -
  θ 3 * E (fun y => Y 3 y*(B y)^3) + E (fun y => (B y)^4) := rfl

#print axioms AronowAudit.P011.Wave1.corrected_covariance_expansion_moments

end
end AronowAudit.P011.Wave1.Fid2P011Contracts
