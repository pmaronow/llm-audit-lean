import AronowAudit.P024.P024_Designs

/-! Actual independent assignment and explicit nonempty-arm domain repairs for P024-T7.
The parent assignment laws remain fully independent. Conditioning is represented
by normalized finite masses and proved positive, rather than silently assuming a
fixed number treated or assigning empirical meaning to empty-arm denominators. -/

noncomputable section
open scoped BigOperators
namespace AronowAudit.P024

abbrev NonemptyAllocations (k : ℕ) :=
  {s : Finset (Fin (k+2)) // s ≠ ∅ ∧ s ≠ Finset.univ}

def nonemptyPerm (k : ℕ) (π : Equiv.Perm (Fin (k+2))) :
    NonemptyAllocations k ≃ NonemptyAllocations k :=
  π.finsetCongr.subtypeEquiv (by
    intro s
    have hf : s.map π.toEmbedding = Finset.univ ↔ s = Finset.univ := by
      constructor
      · intro h
        apply Finset.map_injective π.toEmbedding
        exact h.trans (Finset.map_univ_equiv π).symm
      · rintro rfl
        exact Finset.map_univ_equiv π
    change (s ≠ ∅ ∧ s ≠ Finset.univ) ↔
      (s.map π.toEmbedding ≠ ∅ ∧ s.map π.toEmbedding ≠ Finset.univ)
    have he : s.map π.toEmbedding = ∅ ↔ s = ∅ := Finset.map_eq_empty
    exact and_congr (not_congr he).symm (not_congr hf).symm)

def subsetCoefficient {k : ℕ} (i : Fin (k+2)) (s : NonemptyAllocations k) : ℝ :=
  if i ∈ s.val then 1/(s.val.card : ℝ) else 0


lemma subset_coefficients_sum {k : ℕ} (s : NonemptyAllocations k) :
    ∑ i, subsetCoefficient i s = 1 := by
  classical
  have hc : (s.val.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr s.property.1))
  simp only [subsetCoefficient,← Finset.sum_filter]
  have hf : Finset.univ.filter (fun i => i ∈ s.val) = s.val := by ext i; simp
  rw [hf,Finset.sum_const]
  simp [hc]


def subsetMean {k : ℕ} (y : Fin (k+2) → ℝ) (s : NonemptyAllocations k) : ℝ :=
  ∑ j, subsetCoefficient j s * y j


lemma subset_mean_formula {k : ℕ} (y : Fin (k+2) → ℝ) (s : NonemptyAllocations k) :
    subsetMean y s = (∑ j ∈ s.val, y j)/(s.val.card : ℝ) := by
  classical
  unfold subsetMean subsetCoefficient
  simp_rw [ite_mul,zero_mul]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun i => i ∈ s.val) = s.val := by ext i; simp
  rw [hf,← Finset.mul_sum]
  ring


lemma equal_cluster_subset_formula {k : ℕ} (n : ℝ) (hn : 0 < n)
    (y0 y1 : Fin (k+2) → ℝ) (s : NonemptyAllocations k) :
    clusterDIM (fun _ => n) y0 y1 (subsetExposure s.val) =
      subsetMean y1 s - subsetMean y0 (nonemptyComplementEquiv k s) := by
  classical
  rw [subset_mean_formula,subset_mean_formula]
  have he : (nonemptyComplementEquiv k s).val = s.valᶜ := rfl
  rw [he]
  have hT (y : Fin (k+2) → ℝ) :
      (∑ j, if subsetExposure s.val j then n*y j else 0) = n*(∑ j ∈ s.val, y j) := by
    simp [subsetExposure,← Finset.sum_filter,Finset.mul_sum]
  have hC (y : Fin (k+2) → ℝ) :
      (∑ j, if subsetExposure s.val j then 0 else n*y j) = n*(∑ j ∈ s.valᶜ, y j) := by
    have hc : s.valᶜ = Finset.univ.filter (fun j => j ∉ s.val) := by ext j; simp
    rw [Finset.mul_sum,hc,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ s.val <;> simp [subsetExposure,hj]
  unfold clusterDIM
  rw [hT,hC]
  have hTN : (∑ j, if subsetExposure s.val j then n else 0) = n*s.val.card := by
    simpa using hT (fun _ => 1)
  have hCN : (∑ j, if subsetExposure s.val j then 0 else n) = n*(s.valᶜ).card := by
    simpa using hC (fun _ => 1)
  rw [hTN,hCN,mul_div_mul_left _ _ hn.ne',mul_div_mul_left _ _ hn.ne']


/-- The uniform nonempty allocation design is exactly the conditional law of
actual independent Bernoulli(1/2) assignment, with its positive denominator. -/
lemma conditional_nonempty_actual_mass (k : ℕ) :
    0 < probability (uniformDesign (Finset (Fin (k+2))))
      (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) ∧
    (∀ s : NonemptyAllocations k, (conditionalNonemptyDesign k).mass s =
      (uniformDesign (Finset (Fin (k+2)))).mass s.val /
        probability (uniformDesign (Finset (Fin (k+2))))
          (fun s => s ≠ ∅ ∧ s ≠ Finset.univ)) := by
  classical
  letI : Nonempty (NonemptyAllocations k) := ⟨⟨{0},by
    constructor
    · simp
    · intro h
      have hc := congrArg Finset.card h
      simp at hc⟩⟩
  have hA : (0 : ℝ) < Fintype.card (NonemptyAllocations k) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hΩ : (0 : ℝ) < Fintype.card (Finset (Fin (k+2))) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hp : probability (uniformDesign (Finset (Fin (k+2))))
      (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) =
      (Fintype.card (NonemptyAllocations k) : ℝ)/Fintype.card (Finset (Fin (k+2))) := by
    rw [uniform_probability_card]
    congr 1
    exact (congrArg Nat.cast (Fintype.card_subtype
      (fun s : Finset (Fin (k+2)) => s ≠ ∅ ∧ s ≠ Finset.univ))).symm
  refine ⟨by rw [hp]; exact div_pos hA hΩ,fun s => ?_⟩
  change 1/(Fintype.card (NonemptyAllocations k) : ℝ) =
    (1/(Fintype.card (Finset (Fin (k+2))) : ℝ)) / _
  rw [hp]
  field_simp

/-- Correct independent-assignment scope for the unequal-cluster bias witness.
The nonempty-arm result is obtained from the actual independent law by the
conditional-mass identity, rather than replacing independence by fixed counts. -/
theorem unequal_cluster_independent_bias :
    let n : Fin 2 → ℝ := ![1,2]
    let y0 : Fin 2 → ℝ := ![0,0]
    let y1 : Fin 2 → ℝ := ![0,1]
    independentClusterLaw (uniformDesign (Finset (Fin 2))) (1/2) ∧
    clusterEffect n y0 y1 = 2/3 ∧
    expectation (uniformDesign (Finset (Fin 2)))
      (fun s => clusterDIM n y0 y1 (subsetExposure s)) = 5/12 ∧
    expectation (conditionalNonemptyDesign 0)
      (fun s => clusterDIM n y0 y1 (subsetExposure s.val)) = 1/2 ∧
    expectation (conditionalNonemptyDesign 0)
      (fun s => clusterDIM n y0 y1 (subsetExposure s.val)) ≠ clusterEffect n y0 y1 ∧
    (0 < probability (uniformDesign (Finset (Fin 2)))
      (fun s => s ≠ ∅ ∧ s ≠ Finset.univ)) ∧
    (∀ s : NonemptyAllocations 0, (conditionalNonemptyDesign 0).mass s =
      (uniformDesign (Finset (Fin 2))).mass s.val /
        probability (uniformDesign (Finset (Fin 2)))
          (fun s => s ≠ ∅ ∧ s ≠ Finset.univ)) := by
  classical
  let a : NonemptyAllocations 0 := ⟨{0},by decide⟩
  let b : NonemptyAllocations 0 := ⟨{1},by decide⟩
  have huniv : (Finset.univ : Finset (NonemptyAllocations 0)) = {a,b} := by decide
  have hc : Fintype.card (NonemptyAllocations 0) = 2 := by
    have h := congrArg Finset.card huniv
    simpa [a,b] using h
  have hall : (Finset.univ : Finset (Finset (Fin 2))) = {∅,{0},{1},{0,1}} := by decide
  dsimp only
  refine ⟨uniform_subsets_independent 2,?_,?_,?_,?_,
    (conditional_nonempty_actual_mass 0).1,(conditional_nonempty_actual_mass 0).2⟩
  · norm_num [clusterEffect,Fin.sum_univ_two]
  · unfold expectation
    rw [hall]
    norm_num [uniformDesign,clusterDIM,subsetExposure,Fin.sum_univ_two,
      Finset.sum_insert,Finset.ext_iff,Fin.forall_fin_succ]
  · unfold expectation
    rw [huniv]
    norm_num [conditionalNonemptyDesign,uniformDesign,hc,a,b,clusterDIM,subsetExposure,Fin.sum_univ_two]
  · unfold expectation
    rw [huniv]
    norm_num [conditionalNonemptyDesign,uniformDesign,hc,a,b,clusterEffect,clusterDIM,subsetExposure,Fin.sum_univ_two]


def armCoefficient {k : ℕ} (upper : Bool) (i : Fin (k+2)) (s : NonemptyAllocations k) : ℝ :=
  subsetCoefficient i (if upper then nonemptyComplementEquiv k s else s)

lemma arm_coefficient_permutation {k : ℕ} (upper : Bool) (π : Equiv.Perm (Fin (k+2)))
    (i : Fin (k+2)) (s : NonemptyAllocations k) :
    armCoefficient upper (π i) (nonemptyPerm k π s) = armCoefficient upper i s := by
  classical
  cases upper
  · change (if π i ∈ s.val.map π.toEmbedding then 1/((s.val.map π.toEmbedding).card : ℝ) else 0) =
      (if i ∈ s.val then 1/(s.val.card : ℝ) else 0)
    simp
  · change (if π i ∈ (s.val.map π.toEmbedding)ᶜ then 1/(((s.val.map π.toEmbedding)ᶜ).card : ℝ) else 0) =
      (if i ∈ s.valᶜ then 1/((s.valᶜ).card : ℝ) else 0)
    simp [Finset.card_compl]

lemma arm_coefficients_sum {k : ℕ} (upper : Bool) (s : NonemptyAllocations k) :
    ∑ i, armCoefficient upper i s = 1 := by
  exact subset_coefficients_sum _

lemma exchangeable_arm_coefficient_expectation {k : ℕ} (d : Design (NonemptyAllocations k))
    (hsymm : ∀ π : Equiv.Perm (Fin (k+2)), ∀ s, d.mass (nonemptyPerm k π s) = d.mass s)
    (upper : Bool) (i : Fin (k+2)) :
    expectation d (armCoefficient upper i) = 1/(k+2) := by
  classical
  have hcoeff (j : Fin (k+2)) : expectation d (armCoefficient upper j) =
      expectation d (armCoefficient upper i) := by
    let π : Equiv.Perm (Fin (k+2)) := Equiv.swap j i
    let e := nonemptyPerm k π
    have ht (s : NonemptyAllocations k) : armCoefficient upper i (e s) = armCoefficient upper j s := by
      simpa only [e,π,Equiv.swap_apply_left] using arm_coefficient_permutation upper π j s
    have hp : expectation d (fun s => armCoefficient upper i (e s)) =
        expectation d (armCoefficient upper i) := by
      unfold expectation
      calc
        _ = ∑ s, d.mass (e s)*armCoefficient upper i (e s) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [hsymm π s]
        _ = _ := Equiv.sum_comp e (fun s => d.mass s*armCoefficient upper i s)
    simpa only [ht] using hp
  have hsum : (∑ j, expectation d (armCoefficient upper j)) = 1 := by
    rw [← expectation_sum]
    have he : (fun s : NonemptyAllocations k => ∑ j, armCoefficient upper j s) = fun _ => 1 :=
      funext (arm_coefficients_sum upper)
    rw [he,expectation_const]
  simp only [hcoeff,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_ofNat] at hsum
  apply (eq_div_iff (by positivity : (k+2 : ℝ) ≠ 0)).mpr
  nlinarith

lemma exchangeable_arm_mean_expectation {k : ℕ} (d : Design (NonemptyAllocations k))
    (hsymm : ∀ π : Equiv.Perm (Fin (k+2)), ∀ s, d.mass (nonemptyPerm k π s) = d.mass s)
    (upper : Bool) (y : Fin (k+2) → ℝ) :
    expectation d (fun s => ∑ i, armCoefficient upper i s*y i) = (∑ i,y i)/(k+2) := by
  classical
  rw [expectation_sum]
  simp_rw [expectation_mul,exchangeable_arm_coefficient_expectation d hsymm]
  simp only [one_div,div_eq_mul_inv,← Finset.mul_sum]
  ring

/-- Every permutation-invariant nonempty-arm law gives unbiased equal-cluster
means, without a fixed treatment count or a half-probability restriction. -/
lemma equal_cluster_exchangeable_nonempty {k : ℕ} (d : Design (NonemptyAllocations k))
    (hsymm : ∀ π : Equiv.Perm (Fin (k+2)), ∀ s, d.mass (nonemptyPerm k π s) = d.mass s)
    (n : ℝ) (hn : 0 < n) (y0 y1 : Fin (k+2) → ℝ) :
    expectation d (fun s => clusterDIM (fun _ => n) y0 y1 (subsetExposure s.val)) =
      clusterEffect (fun _ => n) y0 y1 := by
  have he : (fun s : NonemptyAllocations k => clusterDIM (fun _ => n) y0 y1 (subsetExposure s.val)) =
      fun s => subsetMean y1 s - subsetMean y0 (nonemptyComplementEquiv k s) :=
    funext (equal_cluster_subset_formula n hn y0 y1)
  rw [he,expectation_sub]
  have h1 : expectation d (subsetMean y1) = (∑ i,y1 i)/(k+2) := by
    exact exchangeable_arm_mean_expectation d hsymm false y1
  have h0 : expectation d (fun s => subsetMean y0 (nonemptyComplementEquiv k s)) = (∑ i,y0 i)/(k+2) := by
    exact exchangeable_arm_mean_expectation d hsymm true y0
  rw [h1,h0]
  unfold clusterEffect
  simp only [← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_ofNat]
  rw [mul_comm (k+2 : ℝ) n,mul_div_mul_left _ _ hn.ne',Finset.sum_sub_distrib]
  ring

def bernoulliNonemptyMass (k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : ℝ :=
  ∑ s : NonemptyAllocations k, (bernoulliDesign (k+2) p hp.le hp1.le).mass s.val

lemma bernoulli_nonempty_mass_positive (k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < bernoulliNonemptyMass k p hp hp1 := by
  classical
  let a : NonemptyAllocations k := ⟨{0},by
    constructor
    · simp
    · intro h
      have hc := congrArg Finset.card h
      simp at hc⟩
  have hmass : 0 < (bernoulliDesign (k+2) p hp.le hp1.le).mass a.val := by
    change 0 < (∏ j ∈ a.val, p)*(∏ j ∈ Finset.univ \ a.val, (1-p))
    apply mul_pos
    · exact Finset.prod_pos (fun _ _ => hp)
    · exact Finset.prod_pos (fun _ _ => sub_pos.mpr hp1)
  exact hmass.trans_le (Finset.single_le_sum
    (fun s _ => (bernoulliDesign (k+2) p hp.le hp1.le).nonneg s.val) (Finset.mem_univ a))

def bernoulliNonemptyDesign (k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Design (NonemptyAllocations k) where
  mass := fun s => (bernoulliDesign (k+2) p hp.le hp1.le).mass s.val /
    bernoulliNonemptyMass k p hp hp1
  nonneg := fun s => div_nonneg ((bernoulliDesign (k+2) p hp.le hp1.le).nonneg s.val)
    (bernoulli_nonempty_mass_positive k p hp hp1).le
  total := by
    rw [← Finset.sum_div]
    exact div_self (bernoulli_nonempty_mass_positive k p hp hp1).ne'

lemma bernoulli_nonempty_symmetric (k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (π : Equiv.Perm (Fin (k+2))) (s : NonemptyAllocations k) :
    (bernoulliNonemptyDesign k p hp hp1).mass (nonemptyPerm k π s) =
      (bernoulliNonemptyDesign k p hp hp1).mass s := by
  simp [bernoulliNonemptyDesign,bernoulliDesign,nonemptyPerm,
    Finset.prod_const,Finset.card_sdiff_of_subset]

/-- Equal-cluster unbiasedness for every common independent assignment
probability 0<p<1, on the actual nonempty-arm conditional law. -/
theorem equal_cluster_bernoulli_conditional_unbiased (k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (n : ℝ) (hn : 0 < n) (y0 y1 : Fin (k+2) → ℝ) :
    expectation (bernoulliNonemptyDesign k p hp hp1)
      (fun s => clusterDIM (fun _ => n) y0 y1 (subsetExposure s.val)) =
      clusterEffect (fun _ => n) y0 y1 :=
  equal_cluster_exchangeable_nonempty _ (bernoulli_nonempty_symmetric k p hp hp1) n hn y0 y1


lemma bernoulli_nonempty_mass_probability (k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    bernoulliNonemptyMass k p hp hp1 =
      probability (bernoulliDesign (k+2) p hp.le hp1.le)
        (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) := by
  classical
  unfold bernoulliNonemptyMass probability expectation
  simp only [mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype
    (Finset.univ.filter (fun s : Finset (Fin (k+2)) => s ≠ ∅ ∧ s ≠ Finset.univ))
    (by intro s; simp) (fun s => (bernoulliDesign (k+2) p hp.le hp1.le).mass s)).symm

/-- Full corrected independent-assignment domain: every common 0<p<1,
positive conditioning event, its actual normalized mass, and unbiasedness.
This explicitly repairs the undefined empty-arm case in the printed prose. -/
theorem equal_cluster_bernoulli_scope_repair (k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (n : ℝ) (hn : 0 < n) (y0 y1 : Fin (k+2) → ℝ) :
    independentClusterLaw (bernoulliDesign (k+2) p hp.le hp1.le) p ∧
    (0 < probability (bernoulliDesign (k+2) p hp.le hp1.le)
      (fun s => s ≠ ∅ ∧ s ≠ Finset.univ)) ∧
    (∀ s : NonemptyAllocations k, (bernoulliNonemptyDesign k p hp hp1).mass s =
      (bernoulliDesign (k+2) p hp.le hp1.le).mass s.val /
        probability (bernoulliDesign (k+2) p hp.le hp1.le)
          (fun s => s ≠ ∅ ∧ s ≠ Finset.univ)) ∧
    expectation (bernoulliNonemptyDesign k p hp hp1)
      (fun s => clusterDIM (fun _ => n) y0 y1 (subsetExposure s.val)) =
      clusterEffect (fun _ => n) y0 y1 := by
  refine ⟨fun s => rfl, ?_, ?_, equal_cluster_bernoulli_conditional_unbiased k p hp hp1 n hn y0 y1⟩
  · rw [← bernoulli_nonempty_mass_probability]
    exact bernoulli_nonempty_mass_positive k p hp hp1
  · intro s
    rw [← bernoulli_nonempty_mass_probability]
    rfl


end AronowAudit.P024

