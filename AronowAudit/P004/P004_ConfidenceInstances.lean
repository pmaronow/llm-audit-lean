import AronowAudit.P004.P004_SpatialCLTCompletion

namespace AronowAudit.P004.ConfidenceInstances
open MeasureTheory ProbabilityTheory Filter CLTCompletion
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option autoImplicit false

def half (N : ℕ) : Fin N → ℝ := fun _ => 1/2
theorem half_admissible (N : ℕ) : ∀ i,0<half N i ∧ half N i<1 := by
  intro i
  norm_num [half]

def oneTable (N : ℕ) : CircleTable N := fun _ _ => 1
def selfNeighborhood (N : ℕ) (i : Fin N) : Finset (Fin N) := {i}
def halfLaw (N : ℕ) : Measure (Assignment N) := designMeasure (half N) (half_admissible N)
def summand (N : ℕ) : CircleTable N := centeredHT (half N) (oneTable N)
instance halfLaw_probability (N : ℕ) : IsProbabilityMeasure (halfLaw N) := by
  dsimp [halfLaw]
  infer_instance

theorem constant_interferes {N : ℕ} (i j : Fin N) : interferes (oneTable N) i j ↔ i=j := by
  simp [interferes,oneTable]

theorem constant_shared {N : ℕ} (i j : Fin N) : sharesSource (oneTable N) i j ↔ i=j := by
  simp only [sharesSource,constant_interferes]
  simp [eq_comm]

theorem raw_graph (N : ℕ) : FiniteDependencyGraph (half N)
    (fun i z => residualContrast (half N) (oneTable N) (fun _ _ => 0) i z)
    (selfNeighborhood N) := by
  apply design_dependency_graph _ _ _ _ (half_admissible N)
  · intro i
    simp [selfNeighborhood]
  · intro i j
    simp [selfNeighborhood,eq_comm]
  · intro i j hj
    rw [constant_shared]
    simpa [selfNeighborhood,eq_comm] using hj

theorem summand_graph (N : ℕ) : DependencyGraph (halfLaw N) (summand N) (selfNeighborhood N) :=
  centeredHT_graph _ _ _ (half_admissible N) (raw_graph N)

theorem one_effect {N : ℕ} (i : Fin N) : nodeEffect (half N) (oneTable N) i=0 := by
  unfold nodeEffect
  rw [marginal_is_marginalization _ _ _ _ (half_admissible N),
    marginal_is_marginalization _ _ _ _ (half_admissible N)]
  simp only [oneTable,expect_const,sub_self]

theorem summand_value {N : ℕ} (i : Fin N) (z : Assignment N) :
    summand N i z=if z i then 2 else -2 := by
  unfold summand centeredHT
  rw [one_effect]
  cases hz : z i <;> norm_num [residualContrast,half,oneTable,bit,hz]

theorem summand_mean {N : ℕ} (i : Fin N) : expect (half N) (summand N i)=0 :=
  centeredHT_mean _ _ (half_admissible N) i

theorem summand_square {N : ℕ} (i : Fin N) :
    expect (half N) (fun z => (summand N i z)^2)=4 := by
  have he : (fun z => (summand N i z)^2)=(fun _ => (4 : ℝ)) := by
    funext z
    rw [summand_value]
    cases z i <;> norm_num
  rw [he,expect_const]

theorem summand_cross {N : ℕ} (i j : Fin N) (hij : i≠j) :
    expect (half N) (fun z => summand N i z*summand N j z)=0 := by
  have hi : DependsOn (summand N i) ({i} : Set (Fin N)) := by
    intro z z' he
    simp only [summand_value]
    rw [he i (by simp)]
  have hj : DependsOn (summand N j) (({i} : Set (Fin N))ᶜ) := by
    intro z z' he
    simp only [summand_value]
    rw [he j (by simpa using hij.symm)]
  rw [GraphCompletion.expect_mul_of_disjoint_depends (half N) {i} _ _ hi hj,
    summand_mean,summand_mean,mul_zero]

theorem summand_covariance {N : ℕ} (i j : Fin N) :
    cov (half N) (summand N i) (summand N j)=if i=j then 4 else 0 := by
  unfold cov
  rw [summand_mean,summand_mean,mul_zero,sub_zero]
  by_cases hij : i=j
  · subst j
    simpa only [if_true,pow_two] using summand_square i
  · rw [if_neg hij]
    exact summand_cross i j hij

theorem ht_variance (N : ℕ) (hN : 0<N) :
    variance (half N) (ht (half N) (oneTable N))=4/(N : ℝ) := by
  have hn : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
  have he : ht (half N) (oneTable N)=(fun z => (∑ i,summand N i z)/(N : ℝ)) := by
    funext z
    simp only [summand,centeredHT,one_effect,sub_zero,ht,residualContrast]
  rw [he,variance_div,variance_sum]
  simp only [summand_covariance,Finset.sum_ite_eq,Finset.mem_univ,if_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

theorem summand_integral_second (N : ℕ) (hN : 0<N) :
    (∫ z,(∑ i,summand N i z)^2 ∂halfLaw N)=4*(N : ℝ) := by
  dsimp only [halfLaw]
  rw [designMeasure_integral]
  dsimp only [summand]
  rw [centeredHT_second _ _ (half_admissible N) hN,ht_variance N hN]
  have hn : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
  field_simp [hn]

/-- Every hypothesis of the corrected generic dependency CLT is simultaneously realized. -/
theorem dependency_clt_original_premises :
    (∀ N,IsProbabilityMeasure (halfLaw N)) ∧
    (∀ N i,Measurable (summand N i)) ∧
    (∀ N i,(∫ z,summand N i z ∂halfLaw N)=0) ∧
    (∃ M : ℝ,∀ N i,∀ᵐ z ∂halfLaw N,|summand N i z|≤M) ∧
    (∀ N,DependencyGraph (halfLaw N) (summand N) (selfNeighborhood N)) ∧
    (∃ D : ℕ,∀ N i,(selfNeighborhood N i).card≤D) ∧
    (∃ v : ℝ,0<v ∧ ∀ᶠ N : ℕ in atTop,
      v*N≤(∫ z,(∑ i,summand N i z)^2 ∂halfLaw N)) := by
  refine ⟨fun N => inferInstance,?_,?_,?_,summand_graph,?_,?_⟩
  · intro N i
    exact measurable_of_finite _
  · intro N i
    dsimp only [halfLaw]
    rw [designMeasure_integral]
    exact summand_mean i
  · refine ⟨2,?_⟩
    intro N i
    exact ae_of_all _ (fun z => by rw [summand_value]; cases z i <;> norm_num)
  · exact ⟨1,fun N i => by simp [selfNeighborhood]⟩
  · refine ⟨4,by norm_num,?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    rw [summand_integral_second N hN]

/-- Actual singleton nodes spread farther apart as the population grows. -/
def nodeLocation (N : ℕ) (i : Fin N) : ℝ := ((N+1 : ℕ) : ℝ)*(i : ℝ)

def population (N : ℕ) : SpatialPopulation N ℝ where
  node i := {nodeLocation N i}
  node_nonempty i := Set.singleton_nonempty _
  zeta := Measure.count
  outcome _ _ := 1
  bands _ := {0}

theorem population_region (N : ℕ) (i : Fin N) (d : ℝ) :
    region (population N) i d={nodeLocation N i} := by
  ext x
  simp [region,nodeDistance,population,Metric.infDist_singleton,dist_eq_zero]

theorem population_separation (N : ℕ) (i j : Fin N) :
    nodeSeparation (population N) i j=dist (nodeLocation N i) (nodeLocation N j) := by
  simp [nodeSeparation,population]

theorem population_wellDefined (N : ℕ) (d : ℝ) : WellDefined (population N) d := by
  intro i
  rw [population_region]
  refine ⟨measurableSet_singleton _,?_,?_,?_⟩
  · simp [population]
  · simp [population]
  · intro z
    exact integrableOn_const (by simp [population] :
      (population N).zeta ({nodeLocation N i})≠⊤)

theorem population_average (N : ℕ) (d : ℝ) : circleAverage (population N) d=oneTable N := by
  funext i z
  rw [circleAverage,population_region]
  simp [population,oneTable,integral_const,measureReal_def]

theorem separated_nodes {N : ℕ} (i j : Fin N) (hij : i≠j) :
    ((N+1 : ℕ) : ℝ)≤nodeSeparation (population N) i j := by
  rw [population_separation,Real.dist_eq]
  have hc : (0 : ℝ)≤((N+1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hval : (i : ℕ)≠(j : ℕ) := Fin.val_ne_of_ne hij
  have hd : (1 : ℝ)≤|(i : ℝ)-(j : ℝ)| := by
    rcases lt_or_gt_of_ne hval with hlt|hgt
    · have h : (i : ℕ)+1≤j := hlt
      have hr : (i : ℝ)+1≤j := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have h : (j : ℕ)+1 ≤ i := hgt
      have hr : (j : ℝ)+1≤ i := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  dsimp [nodeLocation]
  rw [← mul_sub,abs_mul,abs_of_nonneg hc]
  nlinarith

theorem spatial_local_conditions : SpatialLocalConditions population := by
  refine ⟨?_,?_,?_⟩
  · refine ⟨2,by norm_num,Filter.Eventually.of_forall ?_⟩
    intro N x z
    norm_num [population]
  · refine ⟨fun _ => 0,fun d hd => le_rfl,?_⟩
    intro d hd
    filter_upwards [] with N
    rw [population_average]
    intro i j hij hshare
    have heq : i=j := (constant_shared i j).mp hshare
    subst j
    simpa [population_separation] using hij
  · refine ⟨fun _ => 1,?_⟩
    intro r hr
    obtain ⟨K,hK⟩ := exists_nat_gt r
    filter_upwards [eventually_ge_atTop K] with N hN
    intro i
    have hnr : r<((N+1 : ℕ) : ℝ) := by
      have hKN : (K : ℝ)≤N := by exact_mod_cast hN
      push_cast
      linarith
    have heq : ball (nodeSeparation (population N)) i r={i} := by
      ext j
      simp only [ball,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      constructor
      · intro hji
        by_contra hne
        have hh := separated_nodes i j (Ne.symm hne)
        linarith
      · intro he
        subst j
        simpa [population_separation] using hr
    simp [heq]

theorem spatial_nondegenerate : Nondegenerate (fun N => variance (half N)
    (ht (half N) (circleAverage (population N) 0))) := by
  refine ⟨4,by norm_num,?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [population_average,ht_variance N hN]
  have hn : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
  field_simp [hn]
  <;> norm_num

/-- The actual spatial HT CLT's raw-outcome, locality, circle-integral,
probability, and nonvanishing variance premises all hold simultaneously. -/
theorem spatial_clt_original_premises :
    (0 : ℝ)<1/2 ∧ (1/2 : ℝ)<1 ∧ (0 : ℝ)≤0 ∧
    SpatialLocalConditions population ∧
    (∀ᶠ N : ℕ in atTop,WellDefined (population N) 0) ∧
    Nondegenerate (fun N => variance (fun _ : Fin N => (1/2 : ℝ))
      (ht (fun _ => (1/2 : ℝ)) (circleAverage (population N) 0))) := by
  refine ⟨by norm_num,by norm_num,le_rfl,spatial_local_conditions,?_,spatial_nondegenerate⟩
  exact Filter.Eventually.of_forall (fun N => population_wellDefined N 0)

/-- The actual spatial HT CLT applies to these genuine spatial integrals. -/
theorem spatial_clt_original_conclusion :
    NormalLimit (fun _ _ => (1/2 : ℝ)) (fun N z =>
      (ht (half N) (circleAverage (population N) 0) z-
        ame (half N) (circleAverage (population N) 0)) /
      Real.sqrt (variance (half N) (ht (half N) (circleAverage (population N) 0)))) := by
  exact ht_central_limit population (1/2) 0 (by norm_num) le_rfl spatial_local_conditions
    (Filter.Eventually.of_forall (fun N => population_wellDefined N 0)) spatial_nondegenerate

#print axioms dependency_clt_original_premises
#print axioms spatial_clt_original_premises
#print axioms spatial_clt_original_conclusion
end
end AronowAudit.P004.ConfidenceInstances
