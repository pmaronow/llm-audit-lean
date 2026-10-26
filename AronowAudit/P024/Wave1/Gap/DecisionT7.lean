import AronowAudit.P024.P024_IndependentCompletion

/-! P024-T7 under the nonempty-arm conditional interpretation. -/
noncomputable section
open scoped BigOperators
open Filter
namespace AronowAudit.P024.Wave1

lemma DecisionT7_population_estimator_on_nonempty {k : ℕ}
    (P : ClusterPopulation (k + 2)) (empty : Finset (Fin (k + 2)) → ℝ)
    (s : NonemptyAllocations k) :
    populationEstimator P empty s.val =
      clusterDIM (fun j => (P.size j : ℝ)) (clusterMean0 P) (clusterMean1 P)
        (subsetExposure s.val) := by
  simp only [populationEstimator, s.property.1, s.property.2, or_self, if_false]

theorem equal_cluster_independent_population_on_defined_domain
    (k q : ℕ) (hq : 0 < q) (P : ClusterPopulation (k + 2))
    (hsize : ∀ j, P.size j = q)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
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
        (fun s => populationEstimator P empty s.val) = populationEffect P) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have h := equal_cluster_bernoulli_scope_repair k p hp hp1
    (q : ℝ) hqR (clusterMean0 P) (clusterMean1 P)
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro empty
  have hn : (fun j => (P.size j : ℝ)) = (fun _ => (q : ℝ)) := by
    funext j
    rw [hsize j]
  have he : (fun s : NonemptyAllocations k => populationEstimator P empty s.val) =
      (fun s => clusterDIM (fun _ => (q : ℝ)) (clusterMean0 P) (clusterMean1 P)
        (subsetExposure s.val)) := by
    funext s
    rw [DecisionT7_population_estimator_on_nonempty, hn]
  rw [he, populationEffect, hn]
  exact h.2.2.2

lemma DecisionT7_two_cluster_nonempty_probability :
    probability (uniformDesign (Finset (Fin 2)))
      (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) = 1 / 2 := by
  classical
  have hall : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by
    decide
  unfold probability expectation
  rw [hall]
  norm_num [uniformDesign, Finset.ext_iff, Fin.forall_fin_succ]

theorem independent_unequal_size_bias_on_defined_domain :
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
        clusterEffect n y0 y1 := by
  classical
  dsimp only
  have h := unequal_cluster_independent_bias
  dsimp only at h
  refine ⟨h.1, DecisionT7_two_cluster_nonempty_probability,
    h.2.2.2.2.2.2, h.2.1, ?_, h.2.2.2.2.1⟩
  intro empty
  have he : (fun s : NonemptyAllocations 0 =>
      if s.val = ∅ ∨ s.val = Finset.univ then empty s.val
      else clusterDIM (![1, 2] : Fin 2 → ℝ) ![0, 0] ![0, 1] (subsetExposure s.val)) =
      (fun s => clusterDIM (![1, 2] : Fin 2 → ℝ) ![0, 0] ![0, 1]
        (subsetExposure s.val)) := by
    funext s
    simp only [s.property.1, s.property.2, or_self, if_false]
  rw [he]
  exact h.2.2.2.1

end AronowAudit.P024.Wave1
