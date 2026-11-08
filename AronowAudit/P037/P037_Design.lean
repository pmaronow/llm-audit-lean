import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace AronowAudit.P037
open scoped BigOperators
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- SI p. 5 and Fig. S1 p. 24: schools are in four-school blocks with
two treated per block. A school is indexed by (block,within-block position). -/
def blockedSchoolSupport (B : ℕ) : Finset (Finset (Fin B × Fin 4)) :=
  Finset.univ.powerset.filter (fun s => ∀ b, (s.filter (fun i => i.1=b)).card=2)

/-- Released script 1 line 58 (N031 v1 derivation): uniform selection
of m of n schools, with the block argument omitted. This is not P_B. -/
def unblockedSchoolSupport (n m : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powersetCard m

/-- T32(a): exact design mass 6^(-B) on assignments respecting every
four-school block, zero elsewhere. The uniform unblocked law is represented
by normalized sums over unblockedSchoolSupport. -/
noncomputable def blockedSchoolMass {B : ℕ} (s : Finset (Fin B × Fin 4)) : ℝ :=
  if s∈blockedSchoolSupport B then (6:ℝ)^(- (B:ℤ)) else 0

/-- Joint probabilities under uniform m-of-n selection, as finite counts. -/
noncomputable def uniformSchoolProbability (n m : ℕ)
    (E : Finset (Fin n) → Prop) : ℝ :=
  (((unblockedSchoolSupport n m).filter E).card:ℝ)/(Nat.choose n m:ℝ)

/-- T32(a),(b): complete support count/normalization and exact m-of-n
one- and two-school probabilities. n≥2 and m≤n avoid impossible designs. -/
theorem school_randomization_laws (B n m : ℕ) (hn : 2≤n) (hm : m≤n) :
    (blockedSchoolSupport B).card=6^B ∧
    (∑ s ∈ blockedSchoolSupport B, blockedSchoolMass s)=1 ∧
    (unblockedSchoolSupport n m).card=Nat.choose n m ∧
    (∀ h : Fin n, uniformSchoolProbability n m (fun s => h∈s)=(m:ℝ)/n) ∧
    (∀ h j : Fin n, h≠j →
      uniformSchoolProbability n m (fun s => h∈s ∧ j∈s)=
        ((m:ℝ)*(m-1))/(n*(n-1))) := by
  sorry

/-- T31(i),(iv): efficient factorial certificate for C(56,28), avoiding
exponential unfolding of the recursive binomial coefficient definition. -/
theorem school_support_count_arithmetic :
    (6:ℕ)^14=78364164096 ∧ Nat.choose 56 28=7648690600760440 ∧
    ((6:ℝ)^14)/(Nat.choose 56 28:ℝ)=9795520512/956086325095055 ∧
    Nat.choose 8 4=70 ∧ (Nat.choose 4 2)^2=36 ∧ (70:ℕ)-36=34 := by
  have hc : Nat.choose 56 28=7648690600760440 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    norm_num [Nat.factorial]
  refine ⟨by norm_num, hc, ?_, ?_, ?_, by norm_num⟩
  · rw [hc]; norm_num
  · norm_num [Nat.choose]
  · norm_num [Nat.choose]

/-- T31(ii),(iii),(iv): exact marginal/pair/covariance arithmetic.
These are coefficients derived from the design laws, not assumed iid schools. -/
theorem school_pair_probability_arithmetic :
    (28/56:ℝ)=1/2 ∧ (2/4:ℝ)=1/2 ∧
    (28*27/(56*55):ℝ)=27/110 ∧ (2*1/(4*3):ℝ)=1/6 ∧
    (1/6:ℝ)-1/4=-1/12 ∧ (27/110:ℝ)-1/4=-1/220 ∧
    (4*3/(8*7):ℝ)=3/14 ∧ (1/6:ℝ)≠27/110 ∧ (1/4:ℝ)≠27/110 := by
  norm_num

/-- T31(v): sharp-null difference in means variance from joint school
indicators. The expectation and variance below are actual finite sums over
the chosen support; the formula is not substituted for their definition. -/
theorem school_statistic_variance {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : Ω → ℝ) (hp : ∀ z, 0≤p z) (htotal : ∑ z, p z=1)
    (S : Ω → Fin n → Bool) (half : ∀ i, (∑ z, p z*(if S z i then 1 else 0))=1/2)
    (y : Fin n → ℝ) (m : ℕ) (hm : 0<m) :
    let T := fun z => (∑ i, ((if S z i then (1:ℝ) else -1)*y i))/(m:ℝ)
    (∑ z, p z*T z)=0 ∧
    (∑ z, p z*(T z)^2)=
      (∑ i, ∑ j, y i*y j*(if i=j then 1 else
        4*(∑ z, p z*(if S z i=true ∧ S z j=true then 1 else 0))-1))/(m:ℝ)^2 := by
  sorry

/-- T31(v): short variance certificates for the two 56-school outcomes
and their eight-school analogues. Removing blocks moves the variance
up for the block-constant outcome and down for the within-block contrast. -/
theorem school_variance_moves_both_ways :
    ((4+12*(-1/55:ℝ))/28^2)=13/2695 ∧ (13/2695:ℝ)>0 ∧
    ((2+2*(-1)*(-1/55:ℝ))/28^2)=1/385 ∧
    ((2+2*(-1)*(-1/3:ℝ))/28^2)=1/294 ∧ (1/385:ℝ)<1/294 ∧
    ((4+12*(-1/7:ℝ))/4^2)=1/7 ∧
    ((2+2*(-1)*(-1/7:ℝ))/4^2)=1/7 ∧
    ((2+2*(-1)*(-1/3:ℝ))/4^2)=1/6 ∧ (1/7:ℝ)<1/6 := by
  norm_num

/-- T31 full finite counterexample: the two supports and pair laws differ,
including the impossible blocked assignment (11110000); the two sharp-null
variance orderings use the actual distributions, not numerical placeholders. -/
theorem school_sampler_counterexample :
    (blockedSchoolSupport 14).card=78364164096 ∧
    (unblockedSchoolSupport 56 28).card=7648690600760440 ∧
    (unblockedSchoolSupport 8 4).card=70 ∧ (blockedSchoolSupport 2).card=36 ∧
    ({0,1,2,3} : Finset (Fin 8))∈unblockedSchoolSupport 8 4 ∧
    ({(0,0),(0,1),(0,2),(0,3)} : Finset (Fin 2 × Fin 4))∉blockedSchoolSupport 2 ∧
    uniformSchoolProbability 56 28 (fun s => (0 : Fin 56)∈s ∧ 1∈s)=27/110 ∧
    uniformSchoolProbability 4 2 (fun s => (0 : Fin 4)∈s ∧ 1∈s)=1/6 ∧
    (let varianceU := fun y : Fin 8 → ℝ =>
      (∑ s ∈ unblockedSchoolSupport 8 4,
        ((∑ i, (if i∈s then (1:ℝ) else -1)*y i)/4)^2)/70
     let varianceB := fun y : (Fin 2 × Fin 4) → ℝ =>
      (∑ s ∈ blockedSchoolSupport 2,
        ((∑ i, (if i∈s then (1:ℝ) else -1)*y i)/4)^2)/36
     varianceU ![1,1,1,1,0,0,0,0]=1/7 ∧
     varianceB (fun i => if i.1=0 then 1 else 0)=0 ∧
     varianceU ![2,0,1,1,1,1,1,1]=1/7 ∧
     varianceB (fun i => if i=(0,0) then 2 else if i=(0,1) then 0 else 1)=1/6) := by
  sorry

/-- T32(c): school-local exposure probabilities depend only on the 1/2
school marginal and independent within-school seed law. Thus any two school
laws with this marginal give exactly the same student probabilities even
though joint laws between schools differ (T31). -/
theorem school_local_exposure_invariance {Ω U K : Type*}
    [Fintype Ω] [Fintype U] [DecidableEq K]
    (p : Ω → ℝ) (q : U → ℝ) (S : Ω → Bool)
    (half : ∑ z, p z*(if S z then (1:ℝ) else 0)=1/2)
    (total : ∑ z, p z=1) (f : Bool → U → K) (k : K) :
    (∑ z, ∑ u, p z*q u*(if f (S z) u=k then (1:ℝ) else 0))=
      (1/2)*(∑ u, q u*(if f false u=k then (1:ℝ) else 0))+
      (1/2)*(∑ u, q u*(if f true u=k then (1:ℝ) else 0)) := by
  have hz : (∑ z, p z*(if S z then (0:ℝ) else 1))=1/2 := by
    have he : (∑ z, p z*(if S z then (0:ℝ) else 1))=
        (∑ z, p z)-(∑ z, p z*(if S z then (1:ℝ) else 0)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro z _
      cases h : S z <;> simp [h]
    rw [he,total,half]; ring
  have hu : ∀ u, (∑ z, p z*(if f (S z) u=k then (1:ℝ) else 0))=
      (1/2)*(if f false u=k then (1:ℝ) else 0)+
      (1/2)*(if f true u=k then (1:ℝ) else 0) := by
    intro u
    have he : (fun z => p z*(if f (S z) u=k then (1:ℝ) else 0))=
      (fun z => (p z*(if S z then (0:ℝ) else 1))*(if f false u=k then 1 else 0)+
        (p z*(if S z then (1:ℝ) else 0))*(if f true u=k then 1 else 0)) := by
      funext z; cases h : S z <;> simp [h]
    rw [he,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul,hz,half]
  rw [Finset.sum_comm]
  have he : (∑ u, ∑ z, p z*q u*(if f (S z) u=k then (1:ℝ) else 0))=
    ∑ u, q u*(∑ z, p z*(if f (S z) u=k then (1:ℝ) else 0)) := by
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
  rw [he]; simp_rw [hu]
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro u _ <;> ring

end AronowAudit.P037

#print axioms AronowAudit.P037.school_randomization_laws
#print axioms AronowAudit.P037.school_support_count_arithmetic
#print axioms AronowAudit.P037.school_pair_probability_arithmetic
#print axioms AronowAudit.P037.school_statistic_variance
#print axioms AronowAudit.P037.school_variance_moves_both_ways
#print axioms AronowAudit.P037.school_sampler_counterexample
#print axioms AronowAudit.P037.school_local_exposure_invariance
