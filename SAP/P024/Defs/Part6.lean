import SAP.P024.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024
open scoped BigOperators
open Filter
noncomputable section

/-- Corrected consistency for both designs and the equivalent no-dominance condition. -/
def T5Statement : Prop :=
  (∀ (P : (k : ℕ) → ClusterPopulation (k+2))
    (d : (k : ℕ) → Design (Finset (Fin (k+2)))) (p : ℕ → ℝ)
    (empty : (k : ℕ) → Finset (Fin (k+2)) → ℝ) (B η : ℝ),
    0 ≤ B → 0 < η →
    (∀ k j i, |(P k).y0 j i| ≤ B ∧ |(P k).y1 j i| ≤ B) →
    (∀ k, independentClusterLaw (d k) (p k) ∨
      ∃ m : ℕ, 0 < m ∧ m < k+2 ∧ p k = (m : ℝ)/(k+2) ∧ completeClusterLaw (d k) m) →
    (∀ k, η ≤ p k ∧ p k ≤ 1-η) →
    Tendsto (fun k => maxClusterWeight (P k)) atTop (nhds 0) →
    ∀ ε : ℝ, 0 < ε → Tendsto (fun k => probability (d k)
      (fun s => ε < |populationEstimator (P k) (empty k) s - populationEffect (P k)|))
      atTop (nhds 0)) ∧
  (∀ P : (k : ℕ) → ClusterPopulation (k+2),
    Tendsto (fun k => maxClusterWeight (P k)) atTop (nhds 0) ↔
    Tendsto (fun k => ∑ j, (clusterWeight (P k) j)^2) atTop (nhds 0))

/-- The corrected conditional T7 conclusions, retaining positivity instead of a closed event formula. -/
def T7Statement : Prop :=
  (∀ (k q : ℕ), 0 < q → ∀ (P : ClusterPopulation (k+2)),
    (∀ j, P.size j = q) → ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1),
    independentClusterLaw (bernoulliDesign (k+2) p hp.le hp1.le) p ∧
    0 < probability (bernoulliDesign (k+2) p hp.le hp1.le)
      (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) ∧
    (∀ s : NonemptyAllocations k, bernoulliConditionalMass k p s =
      (bernoulliDesign (k+2) p hp.le hp1.le).mass s.val /
        probability (bernoulliDesign (k+2) p hp.le hp1.le)
          (fun s => s ≠ ∅ ∧ s ≠ Finset.univ)) ∧
    (∀ empty : Finset (Fin (k+2)) → ℝ,
      bernoulliConditionalExpectation k p
        (fun s => populationEstimator P empty s.val) = populationEffect P) ∧
    (∀ s : NonemptyAllocations k,
      populationEstimator P (fun _ => 0) s.val =
        fixedDIM s.val.card (clusterMean0 P) (clusterMean1 P) (subsetExposure s.val))) ∧
  (let n : Fin 2 → ℝ := ![1,2]
   let y0 : Fin 2 → ℝ := ![0,0]
   let y1 : Fin 2 → ℝ := ![0,1]
   independentClusterLaw (uniformDesign (Finset (Fin 2))) (1/2) ∧
   probability (uniformDesign (Finset (Fin 2)))
     (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) = 1/2 ∧
   (∀ s : NonemptyAllocations 0, (conditionalNonemptyDesign 0).mass s =
     (uniformDesign (Finset (Fin 2))).mass s.val /
       probability (uniformDesign (Finset (Fin 2)))
         (fun s => s ≠ ∅ ∧ s ≠ Finset.univ)) ∧
   clusterEffect n y0 y1 = 2/3 ∧
   clusterDIM n y0 y1 (subsetExposure {0}) = 0 ∧
   clusterDIM n y0 y1 (subsetExposure {1}) = 1 ∧
   (∀ empty : Finset (Fin 2) → ℝ,
     expectation (conditionalNonemptyDesign 0)
       (fun s => if s.val = ∅ ∨ s.val = Finset.univ then empty s.val
         else clusterDIM n y0 y1 (subsetExposure s.val)) = 1/2) ∧
   expectation (conditionalNonemptyDesign 0)
     (fun s => clusterDIM n y0 y1 (subsetExposure s.val)) ≠ clusterEffect n y0 y1)

end
end SAP.P024
