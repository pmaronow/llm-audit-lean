import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace AronowAudit.P037
open scoped BigOperators
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- Main p. 567: students "nominate up to 10 students". B is directed;
released script 1 uses S_ij=I(B_ij+B_ji>0) for the primary exposure row.
Boolean OR counts a returned nomination once. Referent status uses B. -/
def eitherDirection {n : ℕ} (B : Fin n → Fin n → Bool) (i j : Fin n) : Bool :=
  B i j || B j i

/-- Directed indegree, main p. 567 and SI p. 17's referent definition. -/
def nominationIndegree {n : ℕ} (B : Fin n → Fin n → Bool) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => B i j=true)).card

/-- Empirical 90th percentile by type-7 linear
interpolation of sorted indegrees. Integer quotient/remainder give the
interpolation index and fraction exactly, without floating-point rounding. -/
noncomputable def indegreeNinety {n : ℕ} (B : Fin n → Fin n → Bool) : ℝ :=
  let sorted := (List.ofFn (nominationIndegree B)).mergeSort (·≤·)
  let h := 9*(n-1)
  ((10-h%10:ℕ):ℝ)/10*(sorted.getD (h/10) 0:ℝ)+
    ((h%10:ℕ):ℝ)/10*(sorted.getD (h/10+1) 0:ℝ)

/-- Referents are students whose directed indegree strictly exceeds the
interpolated 90th percentile of the roster’s indegrees. -/
noncomputable def networkReferents {n : ℕ} (B : Fin n → Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun j => indegreeNinety B<(nominationIndegree B j:ℝ))

/-- SI p. 17's two counts: seeds and referent seeds in the chosen row. -/
def networkSeedCount {n : ℕ} (B : Fin n → Fin n → Bool)
    (i : Fin n) (seeds : Finset (Fin n)) : ℕ :=
  (seeds.filter (fun j => B i j=true)).card
def networkReferentCount {n : ℕ} (B : Fin n → Fin n → Bool)
    (γ seeds : Finset (Fin n)) (i : Fin n) : ℕ :=
  (seeds.filter (fun j => B i j=true ∧ j∈γ)).card

/-- Main p. 568's three treated-nonseed conditions: labels S=0,NI=1,I=2. -/
def countExposure (t r : ℕ) : Fin 3 := if t=0 then 0 else if r=0 then 1 else 2
def rowExposure {n : ℕ} (B : Fin n → Fin n → Bool)
    (γ seeds : Finset (Fin n)) (i : Fin n) : Fin 3 :=
  countExposure (networkSeedCount B i seeds) (networkReferentCount B γ seeds i)

/-- T26(a): the code's either-direction matrix is binary, symmetric,
loop-free when B is, contains B, and its extra edges are exactly incoming
nominations that were not returned. -/
theorem either_direction_properties {n : ℕ} (B : Fin n → Fin n → Bool)
    (hdiag : ∀ i, B i i=false) :
    (∀ i j, eitherDirection B i j=eitherDirection B j i) ∧
    (∀ i, eitherDirection B i i=false) ∧
    (∀ i j, B i j=true → eitherDirection B i j=true) ∧
    (∀ i j, eitherDirection B i j=true ∧ B i j=false ↔
      B j i=true ∧ B i j=false) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j; simp [eitherDirection, Bool.or_comm]
  · intro i; simp [eitherDirection,hdiag]
  · intro i j h; simp [eitherDirection,h]
  · intro i j; cases h : B i j <;> cases h' : B j i <;> simp [eitherDirection,h,h']

/-- T26(b),(c): expansion of the two inner products as counts; the union
row equals the nomination row plus the incoming-only row, for every z,γ. -/
theorem either_direction_count_identities {n : ℕ}
    (B : Fin n → Fin n → Bool) (z γ : Fin n → Bool) (i : Fin n) :
    (∑ j : Fin n, (if eitherDirection B i j && z j then (1:ℕ) else 0))=
      (∑ j : Fin n, (if B i j && z j then (1:ℕ) else 0))+
      (∑ j : Fin n, (if !B i j && B j i && z j then (1:ℕ) else 0)) ∧
    (∑ j : Fin n, (if eitherDirection B i j && z j && γ j then (1:ℕ) else 0))=
      (∑ j : Fin n, (if B i j && z j && γ j then (1:ℕ) else 0))+
      (∑ j : Fin n, (if !B i j && B j i && z j && γ j then (1:ℕ) else 0)) := by
  constructor <;> rw [← Finset.sum_add_distrib] <;>
    apply Finset.sum_congr rfl <;> intro j _ <;>
    cases h : B i j <;> cases h' : B j i <;> cases hz : z j <;>
    cases hg : γ j <;> simp [eitherDirection,h,h',hz,hg]

/-- T26(d),(e): exact condition for equal treated-nonseed labels and
pointwise directions of change. r≤c and q≤b encode that referent seeds
are seeds. This characterizes label equality without requiring reciprocal
ties everywhere. -/
theorem exposure_rows_equal_iff (c b r q : ℕ) (hr : r≤c) (hq : q≤b) :
    (countExposure c r=countExposure (c+b) (r+q) ↔
      (0<c ∨ b=0) ∧ (0<r ∨ q=0)) ∧
    (countExposure (c+b) (r+q)=0 → countExposure c r=0) ∧
    (countExposure c r=2 → countExposure (c+b) (r+q)=2) := by
  unfold countExposure
  split_ifs <;> simp_all <;> omega

/-- T26(e): event monotonicity of union-graph school and referent exposure
probabilities, strict when any positive-mass supported draw changes that label. -/
theorem exposure_probability_monotone {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (hp : ∀ z, 0<p z) (c b r q : Ω → ℕ)
    (hr : ∀ z, r z≤c z) (hq : ∀ z, q z≤b z) :
    (∑ z, p z*(if countExposure (c z+b z) (r z+q z)=0 then (1:ℝ) else 0))≤
      (∑ z, p z*(if countExposure (c z) (r z)=0 then (1:ℝ) else 0)) ∧
    (∑ z, p z*(if countExposure (c z) (r z)=2 then (1:ℝ) else 0))≤
      (∑ z, p z*(if countExposure (c z+b z) (r z+q z)=2 then (1:ℝ) else 0)) ∧
    ((∃ z, countExposure (c z) (r z)=0 ∧ countExposure (c z+b z) (r z+q z)≠0) →
      (∑ z, p z*(if countExposure (c z+b z) (r z+q z)=0 then (1:ℝ) else 0))<
      (∑ z, p z*(if countExposure (c z) (r z)=0 then (1:ℝ) else 0))) ∧
    ((∃ z, countExposure (c z) (r z)≠2 ∧ countExposure (c z+b z) (r z+q z)=2) →
      (∑ z, p z*(if countExposure (c z) (r z)=2 then (1:ℝ) else 0))<
      (∑ z, p z*(if countExposure (c z+b z) (r z+q z)=2 then (1:ℝ) else 0))) := by
  have mono (E F : Ω → Prop) [DecidablePred E] [DecidablePred F] (hef : ∀ z, E z → F z) :
      (∑ z, p z*(if E z then (1:ℝ) else 0))≤
        (∑ z, p z*(if F z then (1:ℝ) else 0)) := by
    apply Finset.sum_le_sum; intro z _
    by_cases he : E z
    · simp [he,hef z he]
    · simp only [he,if_false,mul_zero]
      split_ifs <;> linarith [hp z]
  have strict (E F : Ω → Prop) [DecidablePred E] [DecidablePred F] (hef : ∀ z, E z → F z)
      (witness : ∃ z, F z ∧ ¬E z) :
      (∑ z, p z*(if E z then (1:ℝ) else 0))<
        (∑ z, p z*(if F z then (1:ℝ) else 0)) := by
    apply Finset.sum_lt_sum
    · intro z _
      by_cases he : E z
      · simp [he,hef z he]
      · simp only [he,if_false,mul_zero]
        split_ifs <;> linarith [hp z]
    · rcases witness with ⟨z,hf,he⟩
      exact ⟨z,Finset.mem_univ _,by simpa [hf,he] using hp z⟩
  have hS : ∀ z, countExposure (c z+b z) (r z+q z)=0 → countExposure (c z) (r z)=0 :=
    fun z => (exposure_rows_equal_iff (c z) (b z) (r z) (q z) (hr z) (hq z)).2.1
  have hI : ∀ z, countExposure (c z) (r z)=2 → countExposure (c z+b z) (r z+q z)=2 :=
    fun z => (exposure_rows_equal_iff (c z) (b z) (r z) (q z) (hr z) (hq z)).2.2
  refine ⟨mono _ _ hS,mono _ _ hI,strict _ _ hS,?_⟩
  rintro ⟨z,he,hf⟩
  exact strict _ _ hI ⟨z,hf,he⟩

/-- T25(W1),(W2): two nomination graphs with zero-based indices. -/
def nominationWitness10 (i j : Fin 10) : Bool :=
  decide ((i=1 ∧ j=0) ∨ ((i=2 ∨ i=3) ∧ j=1))
def nominationWitness20 (i j : Fin 20) : Bool :=
  decide ((i=1 ∧ j=0) ∨ (i=0 ∧ (j=2 ∨ j=4)) ∨
    (8≤i.val ∧ i.val≤13 ∧ j=1) ∨ (14≤i.val ∧ i.val≤19 ∧ j=2))
def graphEligible20 : Fin 6 → Fin 20 := ![1,2,4,5,6,7]
noncomputable def graphProbability20 (B : Fin 20 → Fin 20 → Bool) (k : Fin 4) : ℝ :=
  if k=0 then 1/2 else
    (((Finset.univ.powersetCard 3).filter (fun s : Finset (Fin 6) =>
      (rowExposure B (networkReferents nominationWitness20) (s.image graphEligible20) 0).val+1=k.val)).card:ℝ)/40


/-- SI p. 29: "mean of outcomes of peers of seeds ... peers of
seed-eligibles who were not selected". T36's released statistic counts
outgoing nomination occurrences, including seed recipients and duplicates.
E is the eligible origin set; M specifies observed recipient outcomes. -/
noncomputable def nominationStatistic {I : Type*} [Fintype I]
    (E : Finset I) (A : I → I → ℝ) (M z Y : I → ℝ) : ℝ :=
  (∑ i ∈ E, ∑ j, A i j*M j*z i*Y j)/(∑ i ∈ E, ∑ j, A i j*M j*z i) -
  (∑ i ∈ E, ∑ j, A i j*M j*(1-z i)*Y j)/(∑ i ∈ E, ∑ j, A i j*M j*(1-z i))

/-- T36(c): a homogeneous direct effect enters through δκ(z).
Binary assignments/missingness and nonnegative nomination multiplicities
are stated; both recipient-occurrence denominators are positive. -/
theorem nomination_statistic_direct_effect {I : Type*} [Fintype I]
    (E : Finset I) (A : I → I → ℝ) (M z baseline : I → ℝ) (δ : ℝ)
    (hA : ∀ i j, 0≤A i j) (hM : ∀ i, M i=0 ∨ M i=1)
    (hz : ∀ i, z i=0 ∨ z i=1) (hE : ∀ i, i∉E → z i=0)
    (hd1 : 0<∑ i ∈ E, ∑ j, A i j*M j*z i)
    (hd0 : 0<∑ i ∈ E, ∑ j, A i j*M j*(1-z i)) :
    nominationStatistic E A M z (fun j => baseline j+δ*z j)=
      nominationStatistic E A M z baseline+δ*nominationStatistic E A M z z := by
  unfold nominationStatistic
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [mul_left_comm _ δ, ← Finset.mul_sum]
  ring


/-- T35: five reciprocal pairs of eligibles; (pair,false/true) is the
zero-based student 2*pair+bit. Exactly five of ten are drawn uniformly. -/
def partner (i : Fin 5 × Bool) : Fin 5 × Bool := (i.1,!i.2)
def pairedSupport : Finset (Finset (Fin 5 × Bool)) := Finset.univ.powersetCard 5
def pairedObserved : Finset (Fin 5 × Bool) := {(0,false),(1,false),(2,false),(3,false),(4,false)}
noncomputable def directOnly (z : Finset (Fin 5 × Bool)) (i : Fin 5 × Bool) : ℝ :=
  if i∈z then 1 else 0
noncomputable def pairedStatistic (z : Finset (Fin 5 × Bool)) (Y : (Fin 5 × Bool) → ℝ) : ℝ :=
  (∑ i ∈ z, Y (partner i))/5-(∑ i ∈ Finset.univ \ z, Y (partner i))/5
noncomputable def pairedPValue (z : Finset (Fin 5 × Bool)) : ℝ :=
  (((pairedSupport.filter (fun z' =>
    |pairedStatistic z' (directOnly z)| ≥ |pairedStatistic z (directOnly z)|)).card:ℝ))/252

/-- T35(i): own assignment alone determines every outcome in the witness. -/
theorem paired_no_social_influence (z z' : Finset (Fin 5 × Bool)) (i : Fin 5 × Bool)
    (h : i∈z ↔ i∈z') : directOnly z i=directOnly z' i := by
  simp only [directOnly,h]


/-- T35(iii)--(vi): arithmetic certificate for the hypergeometric histogram
and rejection probabilities. The theorem verifies the displayed numerical
identities and inequalities; it does not identify them with probabilities
computed from the full permutation supports. -/
theorem paired_permutation_arithmetic :
    (∀ k : Fin 6, (Nat.choose 5 k.val)^2=(![1,25,100,100,25,1] : Fin 6 → ℕ) k) ∧
    (1+25+100+100+25+1:ℕ)=252 ∧ (2/252:ℝ)=1/126 ∧ (1/126:ℝ)<1/100 ∧
    (2:ℕ)^5=32 ∧ (32/252:ℝ)=8/63 ∧ (52/252:ℝ)=13/63 ∧
    (2/(252:ℝ)^4)<1/100 := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩
  intro k; fin_cases k <;> norm_num [Nat.choose]

end AronowAudit.P037

