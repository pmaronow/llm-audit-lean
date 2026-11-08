import AronowAudit.P024.Wave1.Gap.DecisionT7

noncomputable section
open scoped BigOperators
open Filter
namespace AronowAudit.P024.Wave1

example : ∀
    (k q : ℕ) (hq : 0 < q) (P : ClusterPopulation (k + 2))
    (hsize : ∀ j, P.size j = q)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1),
    independentClusterLaw (bernoulliDesign (k + 2) p hp.le hp1.le) p ∧
    (0 < probability (bernoulliDesign (k + 2) p hp.le hp1.le)
      (fun s => s ≠ ∅ ∧ s ≠ Finset.univ)) ∧
    (∀ s : NonemptyAllocations k,
      (bernoulliNonemptyDesign k p hp hp1).mass s =
        (bernoulliDesign (k + 2) p hp.le hp1.le).mass s.val /
          probability (bernoulliDesign (k + 2) p hp.le hp1.le)
            (fun s => s ≠ ∅ ∧ s ≠ Finset.univ)) ∧
    (∀ empty : Finset (Fin (k + 2)) → ℝ,
      expectation (bernoulliNonemptyDesign k p hp hp1)
        (fun s => populationEstimator P empty s.val) = populationEffect P) :=
  AronowAudit.P024.Wave1.equal_cluster_independent_population_on_defined_domain

example :
    let n : Fin 2 → ℝ := ![1, 2]
    let y0 : Fin 2 → ℝ := ![0, 0]
    let y1 : Fin 2 → ℝ := ![0, 1]
    independentClusterLaw (uniformDesign (Finset (Fin 2))) (1 / 2) ∧
    probability (uniformDesign (Finset (Fin 2)))
      (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) = 1 / 2 ∧
    (∀ s : NonemptyAllocations 0,
      (conditionalNonemptyDesign 0).mass s =
        (uniformDesign (Finset (Fin 2))).mass s.val /
          probability (uniformDesign (Finset (Fin 2)))
            (fun s => s ≠ ∅ ∧ s ≠ Finset.univ)) ∧
    clusterEffect n y0 y1 = 2 / 3 ∧
    (∀ empty : Finset (Fin 2) → ℝ,
      expectation (conditionalNonemptyDesign 0)
        (fun s => if s.val = ∅ ∨ s.val = Finset.univ then empty s.val
          else clusterDIM n y0 y1 (subsetExposure s.val)) = 1 / 2) ∧
    expectation (conditionalNonemptyDesign 0)
      (fun s => clusterDIM n y0 y1 (subsetExposure s.val)) ≠
        clusterEffect n y0 y1 :=
  AronowAudit.P024.Wave1.independent_unequal_size_bias_on_defined_domain

end AronowAudit.P024.Wave1
