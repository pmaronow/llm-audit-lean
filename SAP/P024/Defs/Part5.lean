import SAP.P024.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024
open scoped BigOperators
open Filter
noncomputable section

/-- The entire dominant-cluster counterexample, including both designs and K=6. -/
def T4Statement : Prop :=
  (∀ k, (∑ j, ((dominantPopulation k).size j : ℝ)) = (k+2 : ℝ)^2+(k+2)-1) ∧
  (∀ k j i, 0 < (dominantPopulation k).y0 j i ∧ (dominantPopulation k).y0 j i < 1 ∧
    0 < (dominantPopulation k).y1 j i ∧ (dominantPopulation k).y1 j i < 1 ∧
    (dominantPopulation k).y1 j i-(dominantPopulation k).y0 j i = 1/4) ∧
  (∀ k, populationEffect (dominantPopulation k) = 1/4) ∧
  (∀ k (s : Finset (Fin (k+2))), s ≠ ∅ → s ≠ Finset.univ →
    populationEstimator (dominantPopulation k) (fun _ => 0) s =
      dominantValue (k+2 : ℝ) s.card (decide ((0 : Fin (k+2)) ∈ s)) ∧
    (1/4)*(k+2 : ℝ)^2/((k+2 : ℝ)^2+(k+2)-2) ≤
      |populationEstimator (dominantPopulation k) (fun _ => 0) s-1/4| ∧
    (1/8 : ℝ) < (1/4)*(k+2 : ℝ)^2/((k+2 : ℝ)^2+(k+2)-2)) ∧
  (∀ k, independentClusterLaw (uniformDesign (Finset (Fin (k+2)))) (1/2)) ∧
  (∀ k, probability (uniformDesign (Finset (Fin (k+2))))
    (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) = 1-2/(2 : ℝ)^(k+2)) ∧
  (∀ (empty : (k : ℕ) → Finset (Fin (k+2)) → ℝ),
    (∀ k, 1-2/(2 : ℝ)^(k+2) ≤ probability (uniformDesign (Finset (Fin (k+2))))
      (fun s => (1/8 : ℝ) < |populationEstimator (dominantPopulation k) (empty k) s-
        populationEffect (dominantPopulation k)|)) ∧
    Tendsto (fun k => probability (uniformDesign (Finset (Fin (k+2))))
      (fun s => (1/8 : ℝ) < |populationEstimator (dominantPopulation k) (empty k) s-
        populationEffect (dominantPopulation k)|)) atTop (nhds 1) ∧
    ¬ Tendsto (fun k => probability (uniformDesign (Finset (Fin (k+2))))
      (fun s => (1/8 : ℝ) < |populationEstimator (dominantPopulation k) (empty k) s-
        populationEffect (dominantPopulation k)|)) atTop (nhds 0)) ∧
  (∀ k, expectation (conditionalNonemptyDesign k)
    (fun s => populationEstimator (dominantPopulation k) (fun _ => 0) s.val) = 1/4) ∧
  (∀ n,
    let d := halfClusterDesign n
    let X := fun s : {s : Finset (Fin (2*n+2)) // s.card=n+1} =>
      populationEstimator (dominantPopulation (2*n)) (fun _ => 0) s.val
    probability d (fun s => (0 : Fin (2*n+2)) ∈ s.val) = 1/2 ∧
    (∀ s, X s = if (0 : Fin (2*n+2)) ∈ s.val then 1/4+(1/4)*halfDominantRatio n
      else 1/4-(1/4)*halfDominantRatio n) ∧
    expectation d X = 1/4 ∧ variance d X = (halfDominantRatio n)^2/16 ∧
    (1/2 : ℝ) < halfDominantRatio n ∧
    probability d (fun s => (1/8 : ℝ) < |X s-1/4|) = 1) ∧
  Tendsto halfDominantRatio atTop (nhds 1) ∧
  Tendsto (fun n => variance (halfClusterDesign n)
    (fun s => populationEstimator (dominantPopulation (2*n)) (fun _ => 0) s.val))
    atTop (nhds (1/16)) ∧
  (∀ k, maxClusterWeight (dominantPopulation k) =
    (k+2 : ℝ)^2/((k+2 : ℝ)^2+(k+2)-1)) ∧
  Tendsto (fun k => maxClusterWeight (dominantPopulation k)) atTop (nhds 1) ∧
  dominantValue 6 3 true = 37/76 ∧ dominantValue 6 3 false = 1/76 ∧
  Fintype.card {s : Finset (Fin 6) // s.card=3} = 20 ∧
  (((Finset.univ : Finset (Fin 6)).powersetCard 3).filter (fun s => (0 : Fin 6) ∈ s)).card = 10 ∧
  Fintype.card (Finset (Fin 6)) = 64 ∧
  probability (uniformDesign (Finset (Fin 6)))
    (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) = 62/64 ∧
  (∀ j : Fin 6, (dominantPopulation 4).size j = if j=0 then 36 else 1) ∧
  variance (halfClusterDesign 2)
    (fun s => populationEstimator (dominantPopulation 4) (fun _ => 0) s.val) = 81/1444 ∧
  (∀ s : Finset (Fin 6), s ≠ ∅ → s ≠ Finset.univ →
    (9/40 : ℝ) ≤ |populationEstimator (dominantPopulation 4) (fun _ => 0) s-1/4|) ∧
  (∃ s : Finset (Fin 6), s ≠ ∅ ∧ s ≠ Finset.univ ∧
    |populationEstimator (dominantPopulation 4) (fun _ => 0) s-1/4| = 9/40)

end
end SAP.P024
