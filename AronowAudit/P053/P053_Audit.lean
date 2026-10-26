import Mathlib.Tactic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Equiv.Fintype

/-!
Formalization of Aronow and Offer-Westort (2017), pp. 346–348.
The published comment imports Ding's notation without defining it. The definitions
below make the finite-population and asymptotic conventions explicit.
-/

namespace AronowAudit.P053

set_option autoImplicit false

open scoped BigOperators
open Filter

noncomputable section

/-- "Complete random assignment" (p. 347): all subsets with exactly k treated
units, with the uniform distribution. The support is not a selected subdesign. -/
def support {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) : Finset (Finset ι) :=
  Finset.univ.powersetCard k

/-- Binary sharp-null outcomes (p. 348): true means Y_i(1)=Y_i(0)=1;
false means Y_i(1)=Y_i(0)=0. These counts fix total successes across assignments. -/
def successes {ι : Type*} [DecidableEq ι] (y : ι → Bool) (s : Finset ι) : ℕ :=
  (s.filter (fun i => y i = true)).card

/-- Total observed successes M under the binary sharp null (Section 4, p. 348;
target T1). -/
def totalSuccesses {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → Bool) : ℕ :=
  successes y Finset.univ

/-- The two-by-two table: treated successes, treated failures, control successes,
control failures (clarification of "all test statistics", p. 348, target T1).
Integer subtraction keeps the four cells as integers; on support all are ≥0. -/
def countTable (n1 n0 M a : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  ((a : ℤ), (n1 : ℤ) - a, (M : ℤ) - a, (n0 : ℤ) - M + a)

/-- Binary difference in means, Section 4 p. 348, under a fixed sharp-null y:
a/N1 − (M−a)/N0. Arm sizes are fixed and positive in the theorems. -/
def binaryTau {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n1 n0 : ℕ) (y : ι → Bool) (s : Finset ι) : ℝ :=
  (successes y s : ℝ) / n1 -
    ((totalSuccesses y : ℝ) - successes y s) / n0

/-- The real reconstruction A(t) from T1(a), for the corrected claim in Section 4, p. 348. -/
def reconstruct (n1 n0 M : ℕ) (t : ℝ) : ℝ :=
  ((n1 : ℝ) * n0 * t + n1 * M) / ((n1 : ℝ) + n0)

/-- The correction's single function of tau-hat, T1(c), p. 348:
fixed arm sizes and total successes M determine the reconstruction; floor
extends it to all real arguments without any dependence on an assignment. -/
def tableFactor {S : Type*} (n1 n0 M : ℕ) (h : (ℤ × ℤ × ℤ × ℤ) → S) : ℝ → S :=
  fun t =>
    let a := Int.floor (reconstruct n1 n0 M t)
    h (a,(n1 : ℤ)-a,(M : ℤ)-a,(n0 : ℤ)-M+a)

/-- T1(a): the difference in means equals (Na−N1M)/(N1N0), and the
reconstruction recovers the treated success count. 
Auxiliary component of Section 4, p. 348, corrected table-statistic claim. -/
theorem binary_reconstruction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n1 n0 : ℕ) (h1 : 0 < n1) (h0 : 0 < n0)
    (y : ι → Bool) (s : Finset ι) :
    binaryTau n1 n0 y s =
      (((n1 : ℝ) + n0) * successes y s - n1 * totalSuccesses y) /
        ((n1 : ℝ) * n0) ∧
    reconstruct n1 n0 (totalSuccesses y) (binaryTau n1 n0 y s) =
      (successes y s : ℝ) := by
  have h1r : (n1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h1)
  have h0r : (n0 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h0)
  have hNr : (n1 : ℝ) + n0 ≠ 0 := by positivity
  constructor <;> simp only [binaryTau, reconstruct] <;> field_simp <;> ring

/-- T1(b): with fixed margins, equal differences are equivalent to equal
treated success counts and equal treatment-by-outcome tables (p. 348). -/
theorem binary_equal_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n1 n0 : ℕ) (h1 : 0 < n1) (h0 : 0 < n0)
    (y : ι → Bool) (s t : Finset ι) :
    (binaryTau n1 n0 y s = binaryTau n1 n0 y t ↔ successes y s = successes y t) ∧
    (successes y s = successes y t ↔
      countTable n1 n0 (totalSuccesses y) (successes y s) =
      countTable n1 n0 (totalSuccesses y) (successes y t)) := by
  constructor
  · constructor
    · intro h
      have hr := congrArg (reconstruct n1 n0 (totalSuccesses y)) h
      rw [(binary_reconstruction n1 n0 h1 h0 y s).2,
        (binary_reconstruction n1 n0 h1 h0 y t).2] at hr
      exact_mod_cast hr
    · intro h
      simp only [binaryTau, h]
  · constructor
    · intro h
      rw [h]
    · intro h
      have he := congrArg Prod.fst h
      simp only [countTable] at he
      exact_mod_cast he

/-- T1(a)–(b) with the paper's complete hypothesis list: positive fixed
arm sizes, N=N1+N0 binary sharp-null units, and every pair of assignments in
the full support. Tau-hat reconstructs the success count and identifies the table. 
Auxiliary component of Section 4, p. 348, corrected table-statistic claim. -/
theorem binary_support_identification (n1 n0 : ℕ) (h1 : 0 < n1) (h0 : 0 < n0)
    (y : Fin (n1+n0) → Bool) :
    (∀ s ∈ support n1,
      binaryTau n1 n0 y s=
        (((n1 : ℝ)+n0)*successes y s-n1*totalSuccesses y)/((n1 : ℝ)*n0) ∧
      reconstruct n1 n0 (totalSuccesses y) (binaryTau n1 n0 y s)=(successes y s : ℝ)) ∧
    (∀ s ∈ support n1, ∀ t ∈ support n1,
      (binaryTau n1 n0 y s=binaryTau n1 n0 y t ↔ successes y s=successes y t) ∧
      (successes y s=successes y t ↔
        countTable n1 n0 (totalSuccesses y) (successes y s)=
          countTable n1 n0 (totalSuccesses y) (successes y t))) := by
  exact ⟨fun s hs => binary_reconstruction n1 n0 h1 h0 y s,
    fun s hs t ht => binary_equal_iff n1 n0 h1 h0 y s t⟩

/-- T1(c)'s explicit population-independent choice: for fixed margins
N1,N0,M and h, the same tableFactor works for every sharp-null binary outcome
vector with M successes, and for every supported assignment (p. 348 repair). -/
theorem explicit_table_factor {S : Type*} (n1 n0 M : ℕ)
    (h1 : 0 < n1) (h0 : 0 < n0) (h : (ℤ × ℤ × ℤ × ℤ) → S) :
    ∀ y : Fin (n1+n0) → Bool, totalSuccesses y=M → ∀ s ∈ support n1,
      h (countTable n1 n0 M (successes y s))=
        tableFactor n1 n0 M h (binaryTau n1 n0 y s) := by
  intro y hM s hs
  unfold tableFactor
  rw [← hM,(binary_reconstruction n1 n0 h1 h0 y s).2]
  simp only [Int.floor_natCast,countTable]

/-- T1(c), the corrected printed replacement claim (Section 4, p. 348):
every statistic h of the integer table has one function of tau-hat for all
assignments. The explicit g depends on y only through M; monotonicity is absent.
Floor extends the inverse formula away from the attainable real values. -/
theorem table_statistic_factors {S : Type*}
    (n1 n0 : ℕ) (h1 : 0 < n1) (h0 : 0 < n0) (y : Fin (n1+n0) → Bool)
    (h : (ℤ × ℤ × ℤ × ℤ) → S) :
    ∃ g : ℝ → S, ∀ s ∈ support n1,
      h (countTable n1 n0 (totalSuccesses y) (successes y s)) =
        g (binaryTau n1 n0 y s) := by
  exact ⟨tableFactor n1 n0 (totalSuccesses y) h,
    fun s hs => explicit_table_factor n1 n0 (totalSuccesses y) h1 h0 h y rfl s hs⟩

/-- T1(e): an arbitrary statistic factors through the difference in means
exactly when it is constant on equal tables (Section 4 clarification).
The codomain may be any type, with no externally imposed inhabitation. 
Auxiliary component of Section 4, p. 348, corrected table-statistic claim. -/
theorem factor_iff_table_constant {S : Type*} (n1 n0 : ℕ)
    (h1 : 0 < n1) (h0 : 0 < n0) (y : Fin (n1 + n0) → Bool)
    (T : {s : Finset (Fin (n1 + n0)) // s.card = n1} → S) :
    (∃ g : ℝ → S, ∀ s, T s = g (binaryTau n1 n0 y s.val)) ↔
    (∀ s t, countTable n1 n0 (totalSuccesses y) (successes y s.val) =
      countTable n1 n0 (totalSuccesses y) (successes y t.val) → T s = T t) := by
  classical
  have hex : ∃ s : Finset (Fin (n1 + n0)), s.card = n1 := by
    obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin (n1 + n0)))) (n := n1) (by simp)
    exact ⟨s, hs⟩
  obtain ⟨s, hs⟩ := hex
  letI : Nonempty S := ⟨T ⟨s, hs⟩⟩
  constructor
  · rintro ⟨g, hg⟩ a b hab
    have hab' := (binary_equal_iff n1 n0 h1 h0 y a.val b.val).2.mpr hab
    rw [hg a, hg b, (binary_equal_iff n1 n0 h1 h0 y a.val b.val).1.mpr hab']
  · intro hc
    have hf : Function.FactorsThrough T (fun s => binaryTau n1 n0 y s.val) := by
      intro a b hab
      exact hc a b ((binary_equal_iff n1 n0 h1 h0 y a.val b.val).2.mp
        ((binary_equal_iff n1 n0 h1 h0 y a.val b.val).1.mp hab))
    obtain ⟨g, hg⟩ := (Function.factorsThrough_iff T).mp hf
    exact ⟨g, fun s => congrFun hg s⟩

/-- Canonical binary outcome sample: k ones followed by n−k zeros (T1(d),
the two-sample statistic class). -/
def canonical (n k : ℕ) : Fin n → Bool := fun i => decide (i.val < k)

/-- Finite lemma for T1(d): a binary sample's success count is unchanged
by a permutation of its indices. 
Auxiliary component of Section 4, p. 348, corrected table-statistic claim. -/
theorem successes_permutation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) (p : Equiv.Perm ι) : totalSuccesses (x ∘ p) = totalSuccesses x := by
  unfold totalSuccesses successes
  apply Finset.card_equiv p
  intro i
  simp [Function.comp_def]

/-- Finite lemma for T1(d): every binary outcome sample is a permutation
of the canonical sample with the same number of ones. 
Auxiliary component of Section 4, p. 348, corrected table-statistic claim. -/
theorem canonical_permutation (n : ℕ) (x : Fin n → Bool) :
    ∃ p : Equiv.Perm (Fin n), x ∘ p = canonical n (totalSuccesses x) := by
  classical
  let s := Finset.univ.filter (fun i => x i = true)
  let t := Finset.univ.filter (fun i => canonical n (totalSuccesses x) i = true)
  have hk : totalSuccesses x ≤ n := by
    simpa [totalSuccesses, successes] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => x i = true))
  have ht : t.card = totalSuccesses x := by
    simpa [t, canonical, Nat.min_eq_right hk] using
      (Fin.card_filter_val_lt (n := n) (m := totalSuccesses x))
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_map_finset_eq t s ht
  refine ⟨p, ?_⟩
  funext i
  have hm : p i ∈ s ↔ i ∈ t := by rw [← hp]; simp
  have hh : x (p i) = true ↔ canonical n (totalSuccesses x) i = true := by
    simpa [s, t] using hm
  change x (p i) = _
  cases hx : x (p i) <;> cases hc : canonical n (totalSuccesses x) i <;> simp_all

/-- T1(d), the sample-symmetry assertion: statistics of the two binary
samples that are invariant under independent permutations in each arm are
functions of their success counts, with the displayed canonical h_F. 
Auxiliary component of Section 4, p. 348, corrected table-statistic claim. -/
theorem symmetric_binary_samples {S : Type*} (n1 n0 : ℕ)
    (F : (Fin n1 → Bool) → (Fin n0 → Bool) → S)
    (hinv : ∀ x1 x0 (p1 : Equiv.Perm (Fin n1)) (p0 : Equiv.Perm (Fin n0)),
      F (x1 ∘ p1) (x0 ∘ p0) = F x1 x0) :
    ∀ x1 x0, F x1 x0 =
      F (canonical n1 (totalSuccesses x1)) (canonical n0 (totalSuccesses x0)) := by
  intro x1 x0
  obtain ⟨p1, hp1⟩ := canonical_permutation n1 x1
  obtain ⟨p0, hp0⟩ := canonical_permutation n0 x0
  calc
    F x1 x0 = F (x1 ∘ p1) (x0 ∘ p0) := (hinv x1 x0 p1 p0).symm
    _ = _ := by rw [hp1, hp0]

/-- The converse in T1(d): every function of the arm tables is invariant
under permutations of the binary samples (p. 348 clarification). -/
theorem table_samples_invariant {S : Type*} (n1 n0 : ℕ)
    (h : (ℤ × ℤ × ℤ × ℤ) → S) (x1 : Fin n1 → Bool) (x0 : Fin n0 → Bool)
    (p1 : Equiv.Perm (Fin n1)) (p0 : Equiv.Perm (Fin n0)) :
    h ((totalSuccesses (x1 ∘ p1) : ℤ), (n1 : ℤ) - totalSuccesses (x1 ∘ p1),
        (totalSuccesses (x0 ∘ p0) : ℤ), (n0 : ℤ) - totalSuccesses (x0 ∘ p0)) =
    h ((totalSuccesses x1 : ℤ), (n1 : ℤ) - totalSuccesses x1,
        (totalSuccesses x0 : ℤ), (n0 : ℤ) - totalSuccesses x0) := by
  rw [successes_permutation x1 p1, successes_permutation x0 p0]


/-- T1(d), exact description of the statistic class: independent permutation
invariance of the two binary samples is equivalent to being a table statistic.
This covers nonmonotone functions and fixes the scope of "all" on p. 348. -/
theorem symmetric_samples_table_iff {S : Type*} (n1 n0 : ℕ)
    (F : (Fin n1 → Bool) → (Fin n0 → Bool) → S) :
    (∀ x1 x0 (p1 : Equiv.Perm (Fin n1)) (p0 : Equiv.Perm (Fin n0)),
      F (x1 ∘ p1) (x0 ∘ p0)=F x1 x0) ↔
    (∃ h : (ℤ × ℤ × ℤ × ℤ) → S, ∀ x1 x0,
      F x1 x0 = h ((totalSuccesses x1 : ℤ), (n1 : ℤ)-totalSuccesses x1,
        (totalSuccesses x0 : ℤ), (n0 : ℤ)-totalSuccesses x0)) := by
  constructor
  · intro hi
    refine ⟨fun c => F (canonical n1 c.1.toNat) (canonical n0 c.2.2.1.toNat), ?_⟩
    intro x1 x0
    simpa using symmetric_binary_samples n1 n0 F hi x1 x0
  · rintro ⟨h, hh⟩ x1 x0 p1 p0
    rw [hh, hh]
    exact table_samples_invariant n1 n0 h x1 x0 p1 p0


/-- The binary outcome sample in increasing unit-label order, T1(d),
p. 348 correction: x1(z) and x0(z) list their own arm outcomes. The increasing
bijection implements the target's order convention explicitly. -/
def orderedBinarySample {N n : ℕ} (y : Fin N → Bool) (s : Finset (Fin N))
    (hs : s.card=n) : Fin n → Bool := fun j => y (s.orderEmbOfFin hs j)

/-- Increasingly listing a binary sample preserves its number of successes;
finite bridge between the population table and T1(d)'s sample statistic. 
Auxiliary component of Section 4, p. 348, corrected table-statistic claim. -/
theorem ordered_sample_successes {N n : ℕ} (y : Fin N → Bool)
    (s : Finset (Fin N)) (hs : s.card=n) :
    totalSuccesses (orderedBinarySample y s hs)=successes y s := by
  unfold totalSuccesses successes orderedBinarySample
  apply Finset.card_bij (fun j _ => s.orderEmbOfFin hs j)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨s.orderEmbOfFin_mem hs j,(Finset.mem_filter.mp hj).2⟩
  · intro i hi j hj hij
    exact (s.orderEmbOfFin hs).injective hij
  · intro i hi
    let j := (s.orderIsoOfFin hs).symm ⟨i,(Finset.mem_filter.mp hi).1⟩
    have hj : s.orderEmbOfFin hs j=i := by
      change ((s.orderIsoOfFin hs) ((s.orderIsoOfFin hs).symm
        ⟨i,(Finset.mem_filter.mp hi).1⟩)).val=i
      simp
    refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hj⟩
    rw [hj]
    exact (Finset.mem_filter.mp hi).2

/-- Control successes equal M minus treated successes under a fixed binary
sharp-null outcome schedule; table identity used in T1(d). 
Auxiliary component of Section 4, p. 348, corrected table-statistic claim. -/
theorem successes_compl {N : ℕ} (y : Fin N → Bool) (s : Finset (Fin N)) :
    successes y sᶜ=totalSuccesses y-successes y s := by
  have hh : successes y s+successes y sᶜ=totalSuccesses y := by
    simpa [successes,totalSuccesses] using
      Finset.sum_add_sum_compl s (fun i => if y i=true then (1 : ℕ) else 0)
  omega

/-- A supported binary experiment has exactly N0 control units (T1(d)). 
Auxiliary component of Section 4, p. 348, corrected table-statistic claim. -/
theorem binary_control_card (n1 n0 : ℕ) (s : Finset (Fin (n1+n0)))
    (hs : s ∈ support n1) : sᶜ.card=n0 := by
  have hcard : s.card=n1 := (Finset.mem_powersetCard.mp hs).2
  rw [Finset.card_compl, hcard, Fintype.card_fin]
  omega

/-- T1(d) in its assignment form: a separately permutation-invariant
statistic of the two outcome samples listed in increasing unit order equals
the canonical table statistic and factors through tau-hat on all assignments.
The same single g works throughout the complete randomization support. 
Auxiliary component of Section 4, p. 348, corrected table-statistic claim. -/
theorem ordered_sample_statistic_factors {S : Type*}
    (n1 n0 : ℕ) (h1 : 0 < n1) (h0 : 0 < n0) (y : Fin (n1+n0) → Bool)
    (F : (Fin n1 → Bool) → (Fin n0 → Bool) → S)
    (hinv : ∀ x1 x0 (p1 : Equiv.Perm (Fin n1)) (p0 : Equiv.Perm (Fin n0)),
      F (x1 ∘ p1) (x0 ∘ p0)=F x1 x0) :
    ∃ g : ℝ → S, ∀ (s : Finset (Fin (n1+n0))) (hs : s ∈ support n1),
      let x1 := orderedBinarySample y s (Finset.mem_powersetCard.mp hs).2
      let x0 := orderedBinarySample y sᶜ (binary_control_card n1 n0 s hs)
      F x1 x0=F (canonical n1 (successes y s))
        (canonical n0 (totalSuccesses y-successes y s)) ∧
      F x1 x0=g (binaryTau n1 n0 y s) := by
  let h : (ℤ × ℤ × ℤ × ℤ) → S := fun c =>
    F (canonical n1 c.1.toNat) (canonical n0 c.2.2.1.toNat)
  obtain ⟨g,hg⟩ := table_statistic_factors n1 n0 h1 h0 y h
  refine ⟨g,?_⟩
  intro s hs
  dsimp only
  have hc : F (orderedBinarySample y s (Finset.mem_powersetCard.mp hs).2)
      (orderedBinarySample y sᶜ (binary_control_card n1 n0 s hs)) =
      F (canonical n1 (successes y s)) (canonical n0 (totalSuccesses y-successes y s)) := by
    rw [symmetric_binary_samples n1 n0 F hinv,
      ordered_sample_successes, ordered_sample_successes, successes_compl]
  refine ⟨hc,?_⟩
  rw [hc]
  have hi : ((totalSuccesses y : ℤ)-(successes y s : ℤ)).toNat=
      totalSuccesses y-successes y s := by omega
  have hh : h (countTable n1 n0 (totalSuccesses y) (successes y s))=
      F (canonical n1 (successes y s)) (canonical n0 (totalSuccesses y-successes y s)) := by
    simp only [h,countTable,Int.toNat_natCast,hi]
  rw [← hh]
  exact hg s hs

/-- The concrete binary sharp-null population y=(1,1,0,0)
and fixed covariate x=(1,0,1,0), Section 4 unrestricted reading, T2. -/
def fourY : Fin 4 → Bool := ![true, true, false, false]
/-- Fixed pretreatment covariate x=(1,0,1,0) in target T2(iii), p. 348. -/
def fourX : Fin 4 → Bool := ![true, false, true, false]
/-- T2 assignment z_A=(1,0,1,0), p. 348 unrestricted-reading witness. -/
def fourA : Finset (Fin 4) := {0, 2}
/-- T2 assignment z_B=(0,1,1,0), p. 348 unrestricted-reading witness. -/
def fourB : Finset (Fin 4) := {1, 2}

/-- The labelled statistic L(z)=z_1 y_1 in T2; index 0 in Lean is paper unit 1. -/
def labelStatistic (s : Finset (Fin 4)) : ℝ := if 0 ∈ s then 1 else 0

/-- T2(i)–(iii): both assignments are on the full six-assignment support,
have tau-hat zero and table (1,1,1,1), but L=1 versus 0 and the
covariate-weighted difference is 1/2 versus −1/2. 
Auxiliary component of Section 4, p. 348, unrestricted-reading counterexample fixed in T2. -/
theorem four_counterexample_values :
    (support (ι := Fin 4) 2).card = 6 ∧
    fourA ∈ support 2 ∧ fourB ∈ support 2 ∧
    binaryTau 2 2 fourY fourA = 0 ∧ binaryTau 2 2 fourY fourB = 0 ∧
    countTable 2 2 (totalSuccesses fourY) (successes fourY fourA) = (1,1,1,1) ∧
    countTable 2 2 (totalSuccesses fourY) (successes fourY fourB) = (1,1,1,1) ∧
    labelStatistic fourA = 1 ∧ labelStatistic fourB = 0 ∧
    binaryTau 2 2 (fun i => fourX i && fourY i) fourA = 1/2 ∧
    binaryTau 2 2 (fun i => fourX i && fourY i) fourB = -1/2 := by
  have hc : (support (ι := Fin 4) 2).card = 6 := by decide
  have hM : totalSuccesses fourY = 2 := by decide
  have ha : successes fourY fourA = 1 := by decide
  have hb : successes fourY fourB = 1 := by decide
  have hxM : totalSuccesses (fun i => fourX i && fourY i) = 1 := by decide
  have hxa : successes (fun i => fourX i && fourY i) fourA = 1 := by decide
  have hxb : successes (fun i => fourX i && fourY i) fourB = 0 := by decide
  refine ⟨hc, by decide, by decide, ?_⟩
  simp only [binaryTau, countTable, hM, ha, hb, hxM, hxa, hxb]
  norm_num [labelStatistic, fourA, fourB]

/-- T2(iv): no single g(tau-hat) represents either labelled L or the
covariate-weighted statistic on the complete randomization support. This
refutes only the unrestricted literal "all test statistics" on p. 348. -/
theorem unrestricted_counterexample :
    (¬ ∃ g : ℝ → ℝ, ∀ s ∈ support (ι := Fin 4) 2,
      labelStatistic s = g (binaryTau 2 2 fourY s)) ∧
    (¬ ∃ g : ℝ → ℝ, ∀ s ∈ support (ι := Fin 4) 2,
      binaryTau 2 2 (fun i => fourX i && fourY i) s = g (binaryTau 2 2 fourY s)) := by
  rcases four_counterexample_values with ⟨_, hA, hB, hta, htb, _, _, hla, hlb, hxa, hxb⟩
  constructor
  · rintro ⟨g, hg⟩
    have h := (hg fourA hA).trans (hg fourB hB).symm
    rw [hla, hlb] at h
    norm_num at h
  · rintro ⟨g, hg⟩
    have h := (hg fourA hA).trans (hg fourB hB).symm
    rw [hxa, hxb] at h
    norm_num at h

/-- Inclusive upper-tail randomization p-value: # {w : T(w) ≥ T(z)}/#Ω.
This is the operational meaning specified for the p. 348 example, T3;
it does not compare two implementations of the same two-sided rule. -/
noncomputable def upperP {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (T : Finset ι → ℝ) (z : Finset ι) : ℝ :=
  by
  classical
  exact ((support (ι := ι) k).filter (fun w => T z ≤ T w)).card /
    ((support (ι := ι) k).card : ℝ)

/-- T3(c): a transformation strictly increasing on the attainable statistic
values leaves every inclusive upper-tail p-value unchanged. 
Auxiliary component of Section 4, p. 348, comparison of binary randomization inferences. -/
theorem increasing_same_p {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (T : Finset ι → ℝ) (g : ℝ → ℝ)
    (hg : StrictMonoOn g (T '' {z | z ∈ support k})) (z : Finset ι)
    (hz : z ∈ support k) : upperP k (g ∘ T) z = upperP k T z := by
  classical
  unfold upperP
  congr 2
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w hw
  exact hg.le_iff_le ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩

/-- T4's identity (p. 348): OLS's limit minus Neyman's limit has numerator
(S1²−S0²)(2p−1) over p(1−p). -/
theorem limit_difference_identity (p S1 S0 : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (S0^2/p + S1^2/(1-p)) - (S1^2/p + S0^2/(1-p)) =
      ((S1^2-S0^2)*(2*p-1))/(p*(1-p)) := by
  have h : p ≠ 0 := ne_of_gt hp
  have h' : 1-p ≠ 0 := by linarith
  field_simp <;> ring

/-- T4, the bracketed equivalence on p. 348: Neyman's asymptotic variance
is smaller precisely when p>1/2 and S1>S0, or p<1/2 and S1<S0.
S1,S0 are nonnegative standard deviations, not arbitrary signed reals. -/
theorem apparent_paradox_condition (p S1 S0 : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hS1 : 0 ≤ S1) (hS0 : 0 ≤ S0) :
    (S1^2/p + S0^2/(1-p) < S0^2/p + S1^2/(1-p)) ↔
      ((1/2 < p ∧ S0 < S1) ∨ (p < 1/2 ∧ S1 < S0)) := by
  have hd : 0 < p*(1-p) := by positivity
  rw [← sub_pos, limit_difference_identity p S1 S0 hp hp1, div_pos_iff_of_pos_right hd]
  constructor
  · intro h
    rcases (mul_pos_iff.mp h) with h | h
    · left
      constructor <;> nlinarith [h.1, h.2]
    · right
      constructor <;> nlinarith [h.1, h.2]
  · rintro (⟨hpp, hss⟩ | ⟨hpp, hss⟩)
    · exact mul_pos (by nlinarith) (by linarith)
    · exact mul_pos_of_neg_of_neg (by nlinarith) (by linarith)


/-- Finite algebra for T3(c): positive fixed arm sizes make the binary
difference in means strictly increasing in the treated success count. 
Auxiliary component of Section 4, p. 348, comparison of binary randomization inferences. -/
theorem binary_order_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n1 n0 : ℕ) (h1 : 0 < n1) (h0 : 0 < n0) (y : ι → Bool) (s t : Finset ι) :
    binaryTau n1 n0 y s ≤ binaryTau n1 n0 y t ↔ successes y s ≤ successes y t := by
  have hd : 0 < (n1 : ℝ)*n0 := by positivity
  have hn : 0 < (n1 : ℝ)+n0 := by positivity
  rw [(binary_reconstruction n1 n0 h1 h0 y s).1,
    (binary_reconstruction n1 n0 h1 h0 y t).1, div_le_div_iff_of_pos_right hd]
  constructor
  · intro h
    have hh : (successes y s : ℝ) ≤ successes y t := by nlinarith
    exact_mod_cast hh
  · intro h
    have hh : (successes y s : ℝ) ≤ successes y t := by exact_mod_cast h
    nlinarith

/-- T3's signed upper-tail probability can be counted by treated successes;
this uses the full uniform assignment support and includes ties. 
Auxiliary component of Section 4, p. 348, comparison of binary randomization inferences. -/
theorem binary_upperP_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n1 n0 : ℕ) (h1 : 0 < n1) (h0 : 0 < n0) (y : ι → Bool) (z : Finset ι) :
    upperP n1 (binaryTau n1 n0 y) z =
      (((support n1).filter (fun w => successes y z ≤ successes y w)).card : ℝ) /
        ((support (ι := ι) n1).card : ℝ) := by
  classical
  unfold upperP
  congr 2
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w hw
  exact binary_order_iff n1 n0 h1 h0 y z w

/-- A small certificate for T3: with two or three successes and equally
sized arms, the maximal absolute difference selects success count 0 or n.
This is proved by inequalities, not real-number computation. 
Auxiliary component of Section 4, p. 348, comparison of binary randomization inferences. -/
theorem balanced_absolute_tail (n : ℕ) (hn : 0 < n) (a : ℕ) (ha : a ≤ n) :
    (1 : ℝ) ≤ |(a : ℝ)/n-((n : ℝ)-a)/n| ↔ a=0 ∨ a=n := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have har : 0 ≤ (a : ℝ) := by positivity
  have han : (a : ℝ) ≤ n := by exact_mod_cast ha
  have he : ((a : ℝ)/n-((n : ℝ)-a)/n)*(n : ℝ) = 2*a-n := by
    field_simp <;> ring
  rw [le_abs]
  constructor
  · rintro (h | h)
    · right
      have hh := mul_le_mul_of_nonneg_right h hnr.le
      rw [he] at hh
      have : (a : ℝ) = n := by nlinarith
      exact_mod_cast this
    · left
      have hh := mul_le_mul_of_nonneg_right h hnr.le
      have : (a : ℝ)/n-((n : ℝ)-a)/n ≤ -1 := by linarith
      have hh' := mul_le_mul_of_nonneg_right this hnr.le
      rw [he] at hh'
      have : (a : ℝ) = 0 := by nlinarith
      exact_mod_cast this
  · rintro (rfl | rfl) <;> simp [ne_of_gt hnr]

/-- T3(a)'s fixed binary sharp-null population y=(1,1,1,0,0,0). -/
def sixY : Fin 6 → Bool := ![true,true,true,false,false,false]

/-- T3(a)'s observed assignment (1,1,1,0,0,0). -/
def sixTop : Finset (Fin 6) := {0,1,2}

/-- T3(a), p. 348 absolute-value example on six units:
20 equiprobable assignments, signed p=1/20, absolute p=1/10, and different
rejection decisions at alpha=1/20. -/
theorem six_upper_tail_difference :
    (support (ι := Fin 6) 3).card=20 ∧ sixTop ∈ support 3 ∧
    binaryTau 3 3 sixY sixTop=1 ∧
    upperP 3 (binaryTau 3 3 sixY) sixTop=1/20 ∧
    upperP 3 (fun w => |binaryTau 3 3 sixY w|) sixTop=1/10 ∧
    upperP 3 (binaryTau 3 3 sixY) sixTop ≤ 1/20 ∧
    ¬ upperP 3 (fun w => |binaryTau 3 3 sixY w|) sixTop ≤ 1/20 := by
  classical
  have hc : (support (ι := Fin 6) 3).card=20 := by decide
  have hM : totalSuccesses sixY=3 := by decide
  have ha : successes sixY sixTop=3 := by decide
  have ht : binaryTau 3 3 sixY sixTop=1 := by norm_num [binaryTau, hM, ha]
  have hs : upperP 3 (binaryTau 3 3 sixY) sixTop=1/20 := by
    rw [binary_upperP_count 3 3 (by decide) (by decide), ha]
    have hn : ((support (ι := Fin 6) 3).filter (fun w => 3 ≤ successes sixY w)).card=1 := by decide
    norm_num [hc, hn]
  have habs : upperP 3 (fun w => |binaryTau 3 3 sixY w|) sixTop=1/10 := by
    unfold upperP
    have he : (support (ι := Fin 6) 3).filter
        (fun w => |binaryTau 3 3 sixY sixTop| ≤ |binaryTau 3 3 sixY w|) =
        (support 3).filter (fun w => successes sixY w=0 ∨ successes sixY w=3) := by
      apply Finset.filter_congr
      intro w hw
      have hb : successes sixY w ≤ 3 := by
        exact (Finset.card_filter_le w _).trans_eq (Finset.mem_powersetCard.mp hw).2
      rw [ht, abs_one]
      simpa only [binaryTau, hM] using
        (balanced_absolute_tail 3 (by decide) (successes sixY w) hb)
    rw [he]
    have hn : ((support (ι := Fin 6) 3).filter
      (fun w => successes sixY w=0 ∨ successes sixY w=3)).card=2 := by decide
    norm_num [hc, hn]
  refine ⟨hc, by decide, ht, hs, habs, ?_, ?_⟩ <;> norm_num [hs, habs]

/-- T3(a)'s exact randomization distribution: treated successes 0,1,2,3
occur at 1,9,9,1 of the 20 assignments, and tau-hat=(2k−3)/3. 
Auxiliary component of Section 4, p. 348, comparison of binary randomization inferences. -/
theorem six_difference_distribution :
    ((support (ι := Fin 6) 3).filter (fun z => successes sixY z=0)).card=1 ∧
    ((support (ι := Fin 6) 3).filter (fun z => successes sixY z=1)).card=9 ∧
    ((support (ι := Fin 6) 3).filter (fun z => successes sixY z=2)).card=9 ∧
    ((support (ι := Fin 6) 3).filter (fun z => successes sixY z=3)).card=1 ∧
    (∀ z ∈ support 3, binaryTau 3 3 sixY z=(2*(successes sixY z : ℝ)-3)/3) := by
  have hM : totalSuccesses sixY=3 := by decide
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro z hz
  unfold binaryTau
  rw [hM]
  ring


/-- T3(b)'s maximal positive and negative assignments for the same four-unit
sharp-null population used in the unrestricted-reading counterexample. -/
def fourTop : Finset (Fin 4) := {0,1}
/-- T3(b) assignment (0,0,1,1), the lower endpoint with tau-hat=−1. -/
def fourBottom : Finset (Fin 4) := {2,3}

/-- The absolute-value endpoint p-value on four units, counted on the full
six-assignment support (finite lemma for T3(b)). 
Auxiliary component of Section 4, p. 348, comparison of binary randomization inferences. -/
theorem four_absolute_endpoint (z : Finset (Fin 4))
    (hz : binaryTau 2 2 fourY z=1 ∨ binaryTau 2 2 fourY z=-1) :
    upperP 2 (fun w => |binaryTau 2 2 fourY w|) z=1/3 := by
  classical
  have hM : totalSuccesses fourY=2 := by decide
  have hc : (support (ι := Fin 4) 2).card=6 := by decide
  have ht : |binaryTau 2 2 fourY z|=1 := by rcases hz with h | h <;> simp [h]
  unfold upperP
  have he : (support (ι := Fin 4) 2).filter
      (fun w => |binaryTau 2 2 fourY z| ≤ |binaryTau 2 2 fourY w|) =
      (support 2).filter (fun w => successes fourY w=0 ∨ successes fourY w=2) := by
    apply Finset.filter_congr
    intro w hw
    have hb : successes fourY w ≤ 2 :=
      (Finset.card_filter_le w _).trans_eq (Finset.mem_powersetCard.mp hw).2
    rw [ht]
    simpa only [binaryTau, hM] using
      (balanced_absolute_tail 2 (by decide) (successes fourY w) hb)
  rw [he]
  have hn : ((support (ι := Fin 4) 2).filter
    (fun w => successes fourY w=0 ∨ successes fourY w=2)).card=2 := by decide
  norm_num [hc, hn]


/-- T3(b), the full four-unit upper-tail comparison: signed p=1/6 at tau=1,
1 at tau=−1, 5/6 at tau=0; absolute-value p=1/3 at either extreme and 1
at the four central assignments. 
Auxiliary component of Section 4, p. 348, comparison of binary randomization inferences. -/
theorem four_upper_tail_difference :
    fourTop ∈ support 2 ∧ fourBottom ∈ support 2 ∧
    binaryTau 2 2 fourY fourTop=1 ∧ binaryTau 2 2 fourY fourBottom=-1 ∧
    upperP 2 (binaryTau 2 2 fourY) fourTop=1/6 ∧
    upperP 2 (fun w => |binaryTau 2 2 fourY w|) fourTop=1/3 ∧
    upperP 2 (binaryTau 2 2 fourY) fourBottom=1 ∧
    upperP 2 (fun w => |binaryTau 2 2 fourY w|) fourBottom=1/3 ∧
    (∀ z ∈ support 2, z ≠ fourTop → z ≠ fourBottom →
      binaryTau 2 2 fourY z=0 ∧ upperP 2 (binaryTau 2 2 fourY) z=5/6 ∧
        upperP 2 (fun w => |binaryTau 2 2 fourY w|) z=1) := by
  classical
  have hc : (support (ι := Fin 4) 2).card=6 := by decide
  have hM : totalSuccesses fourY=2 := by decide
  have ha : successes fourY fourTop=2 := by decide
  have hb : successes fourY fourBottom=0 := by decide
  have hta : binaryTau 2 2 fourY fourTop=1 := by norm_num [binaryTau, hM, ha]
  have htb : binaryTau 2 2 fourY fourBottom=-1 := by norm_num [binaryTau, hM, hb]
  have htP : upperP 2 (binaryTau 2 2 fourY) fourTop=1/6 := by
    rw [binary_upperP_count 2 2 (by decide) (by decide), ha]
    have hn : ((support (ι := Fin 4) 2).filter (fun w => 2 ≤ successes fourY w)).card=1 := by decide
    norm_num [hc, hn]
  have hbP : upperP 2 (binaryTau 2 2 fourY) fourBottom=1 := by
    rw [binary_upperP_count 2 2 (by decide) (by decide), hb]
    simp [hc]
  refine ⟨by decide, by decide, hta, htb, htP,
    four_absolute_endpoint fourTop (Or.inl hta), hbP,
    four_absolute_endpoint fourBottom (Or.inr htb), ?_⟩
  intro z hz hzt hzb
  have hcert : ∀ w ∈ support (ι := Fin 4) 2,
    w ≠ fourTop → w ≠ fourBottom → successes fourY w=1 := by decide
  have ha1 := hcert z hz hzt hzb
  have ht0 : binaryTau 2 2 fourY z=0 := by norm_num [binaryTau, hM, ha1]
  refine ⟨ht0, ?_, ?_⟩
  · rw [binary_upperP_count 2 2 (by decide) (by decide), ha1]
    have hn : ((support (ι := Fin 4) 2).filter (fun w => 1 ≤ successes fourY w)).card=5 := by decide
    norm_num [hc, hn]
  · unfold upperP
    simp [ht0, abs_nonneg, hc]

/-- The repeated sharp-null outcome and covariate schedules for T2(v),
blocks indexed by Fin m and units within a block by Fin 4. -/
def repeatY (m : ℕ) : Fin m × Fin 4 → Bool := fun i => fourY i.2
/-- T2(v) fixed pretreatment covariates repeat x in every block (p. 348 witness). -/
def repeatX (m : ℕ) : Fin m × Fin 4 → Bool := fun i => fourX i.2
/-- T2(v) assignment A repeats z_A, using 2m treated units of 4m (p. 348). -/
def repeatA (m : ℕ) : Finset (Fin m × Fin 4) := Finset.univ.product fourA
/-- T2(v) assignment B repeats z_B, using 2m treated units of 4m (p. 348). -/
def repeatB (m : ℕ) : Finset (Fin m × Fin 4) := Finset.univ.product fourB

/-- T2(v)'s labelled statistic at paper unit (1,1), with zero-based indices. -/
def repeatLabel (m : ℕ) (hm : 0 < m) (s : Finset (Fin m × Fin 4)) : ℝ :=
  if (⟨0, hm⟩, (0 : Fin 4)) ∈ s then 1 else 0

/-- A reusable exact count: repeating a binary block m times multiplies
every selected-sample success count by m. 
Auxiliary component of Section 4, p. 348, unrestricted-reading counterexample fixed in T2. -/
theorem product_successes (m : ℕ) (y : Fin 4 → Bool) (s : Finset (Fin 4)) :
    successes (fun i : Fin m × Fin 4 => y i.2) (Finset.univ.product s) =
      m * successes y s := by
  unfold successes
  have he : (Finset.univ.product s).filter (fun i : Fin m × Fin 4 => y i.2=true) =
      Finset.univ.product (s.filter (fun j => y j=true)) := by ext i; simp
  rw [he]
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin]

/-- Repetition multiplies the total number of successes by m (T2(v)). 
Auxiliary component of Section 4, p. 348, unrestricted-reading counterexample fixed in T2. -/
theorem repeated_total (m : ℕ) (y : Fin 4 → Bool) :
    totalSuccesses (fun i : Fin m × Fin 4 => y i.2) = m*totalSuccesses y := by
  unfold totalSuccesses
  simpa only [Finset.product_eq_sprod, Finset.univ_product_univ] using
    (product_successes m y Finset.univ)

/-- T2(v)'s exact witnesses at every m≥1: equal zero differences, tables
(m,m,m,m), labelled values 1 and 0, covariate differences ±1/2, and exact
allocation/success proportions 1/2. This uses all subsets of 2m of 4m units. 
Auxiliary component of Section 4, p. 348, unrestricted-reading counterexample fixed in T2. -/
theorem repeated_counterexample_values (m : ℕ) (hm : 0 < m) :
    repeatA m ∈ support (2*m) ∧ repeatB m ∈ support (2*m) ∧
    binaryTau (2*m) (2*m) (repeatY m) (repeatA m)=0 ∧
    binaryTau (2*m) (2*m) (repeatY m) (repeatB m)=0 ∧
    countTable (2*m) (2*m) (totalSuccesses (repeatY m))
      (successes (repeatY m) (repeatA m))=((m : ℤ),(m : ℤ),(m : ℤ),(m : ℤ)) ∧
    countTable (2*m) (2*m) (totalSuccesses (repeatY m))
      (successes (repeatY m) (repeatB m))=((m : ℤ),(m : ℤ),(m : ℤ),(m : ℤ)) ∧
    repeatLabel m hm (repeatA m)=1 ∧ repeatLabel m hm (repeatB m)=0 ∧
    binaryTau (2*m) (2*m) (fun i => repeatX m i && repeatY m i) (repeatA m)=1/2 ∧
    binaryTau (2*m) (2*m) (fun i => repeatX m i && repeatY m i) (repeatB m)=-1/2 ∧
    ((2*m : ℕ) : ℝ)/(4*m : ℕ)=1/2 ∧
    (totalSuccesses (repeatY m) : ℝ)/(4*m : ℕ)=1/2 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hM4 : totalSuccesses fourY=2 := by decide
  have ha4 : successes fourY fourA=1 := by decide
  have hb4 : successes fourY fourB=1 := by decide
  have hxM4 : totalSuccesses (fun i => fourX i && fourY i)=1 := by decide
  have hxa4 : successes (fun i => fourX i && fourY i) fourA=1 := by decide
  have hxb4 : successes (fun i => fourX i && fourY i) fourB=0 := by decide
  have hM : totalSuccesses (repeatY m)=2*m := by
    unfold repeatY
    rw [repeated_total, hM4]
    omega
  have ha : successes (repeatY m) (repeatA m)=m := by
    unfold repeatY repeatA
    rw [product_successes, ha4, mul_one]
  have hb : successes (repeatY m) (repeatB m)=m := by
    unfold repeatY repeatB
    rw [product_successes, hb4, mul_one]
  have hxM : totalSuccesses (fun i => repeatX m i && repeatY m i)=m := by
    simpa [repeatY, repeatX, hxM4] using repeated_total m (fun i => fourX i && fourY i)
  have hxa : successes (fun i => repeatX m i && repeatY m i) (repeatA m)=m := by
    simpa [repeatY, repeatX, repeatA, hxa4] using product_successes m (fun i => fourX i && fourY i) fourA
  have hxb : successes (fun i => repeatX m i && repeatY m i) (repeatB m)=0 := by
    simpa [repeatY, repeatX, repeatB, hxb4] using product_successes m (fun i => fourX i && fourY i) fourB
  have hAc : (repeatA m).card=2*m := by
    have hh : fourA.card=2 := by decide
    simp [repeatA, Finset.product_eq_sprod, Finset.card_product, hh, mul_comm]
  have hBc : (repeatB m).card=2*m := by
    have hh : fourB.card=2 := by decide
    simp [repeatB, Finset.product_eq_sprod, Finset.card_product, hh, mul_comm]
  have hta : binaryTau (2*m) (2*m) (repeatY m) (repeatA m)=0 := by
    simp only [binaryTau, hM, ha, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have htb : binaryTau (2*m) (2*m) (repeatY m) (repeatB m)=0 := by
    simp only [binaryTau, hM, hb, Nat.cast_mul, Nat.cast_ofNat]
    ring
  refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hAc⟩,
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hBc⟩,
    hta, htb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [countTable, hM, ha, Nat.cast_mul, Nat.cast_ofNat]
    ext <;> ring
  · simp only [countTable, hM, hb, Nat.cast_mul, Nat.cast_ofNat]
    ext <;> ring
  · simp [repeatLabel, repeatA, fourA, Finset.product_eq_sprod]
  · simp [repeatLabel, repeatB, fourB, Finset.product_eq_sprod]
  · simp only [binaryTau, hxM, hxa, Nat.cast_mul, Nat.cast_ofNat]
    field_simp <;> ring
  · simp only [binaryTau, hxM, hxb, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero]
    field_simp <;> ring
  · push_cast
    field_simp <;> ring
  · rw [hM]
    push_cast
    field_simp <;> ring

/-- T2(v): no single g represents the labelled or covariate statistic on
the unrestricted complete randomization support at any repeated block size. 
Auxiliary component of Section 4, p. 348, unrestricted-reading counterexample fixed in T2. -/
theorem unrestricted_repeated_counterexample (m : ℕ) (hm : 0 < m) :
    (¬ ∃ g : ℝ → ℝ, ∀ z ∈ support (ι := Fin m × Fin 4) (2*m),
      repeatLabel m hm z = g (binaryTau (2*m) (2*m) (repeatY m) z)) ∧
    (¬ ∃ g : ℝ → ℝ, ∀ z ∈ support (ι := Fin m × Fin 4) (2*m),
      binaryTau (2*m) (2*m) (fun i => repeatX m i && repeatY m i) z =
        g (binaryTau (2*m) (2*m) (repeatY m) z)) := by
  rcases repeated_counterexample_values m hm with
    ⟨ha, hb, hta, htb, _, _, hla, hlb, hxa, hxb, _, _⟩
  constructor
  · rintro ⟨g, hg⟩
    have hA := hg (repeatA m) ha
    have hB := hg (repeatB m) hb
    rw [hta, hla] at hA
    rw [htb, hlb] at hB
    linarith
  · rintro ⟨g, hg⟩
    have hA := hg (repeatA m) ha
    have hB := hg (repeatB m) hb
    rw [hta, hxa] at hA
    rw [htb, hxb] at hB
    linarith

/-- Conversion of the binary sharp-null schedule to real potential outcomes
0 and 1, used only for checking the standing moment conditions in T2(v). -/
def binaryReal (b : Bool) : ℝ := if b=true then 1 else 0

/-- T2(v)'s bounded fourth-moment certificate: at every repeated population,
N^{-1} sum(Y1^4+Y0^4)≤2, with Y1=Y0=binary y. Thus the counterexample is
not excluded by the standing fourth-moment condition on p. 347. -/
theorem repeated_fourth_moments (m : ℕ) (hm : 0 < m) :
    (∑ i : Fin m × Fin 4, ((binaryReal (repeatY m i))^4 +
      (binaryReal (repeatY m i))^4)) / (4*m : ℕ) ≤ 2 := by
  have hd : (0 : ℝ) < (4*m : ℕ) := by exact_mod_cast (by omega : 0 < 4*m)
  apply (div_le_iff₀ hd).mpr
  have hsum : (∑ i : Fin m × Fin 4, ((binaryReal (repeatY m i))^4 +
      (binaryReal (repeatY m i))^4)) ≤ ∑ i : Fin m × Fin 4, (2 : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    cases h : repeatY m i <;> norm_num [binaryReal, h]
  simpa [Fintype.card_prod, Nat.cast_mul, mul_comm] using hsum


/-- T2(v)'s standing asymptotic checks: repeated counterexamples have sizes
4(k+1)→∞, treatment and binary-success fractions tending to 1/2, and a
uniform fourth-moment bound. The exact counterexamples persist at every k. 
Auxiliary component of Section 4, p. 348, unrestricted-reading counterexample fixed in T2. -/
theorem repeated_counterexample_scaling :
    Tendsto (fun k : ℕ => 4*(k+1)) atTop atTop ∧
    Tendsto (fun k : ℕ => ((2*(k+1) : ℕ) : ℝ)/(4*(k+1) : ℕ)) atTop (nhds (1/2)) ∧
    Tendsto (fun k : ℕ => (totalSuccesses (repeatY (k+1)) : ℝ)/(4*(k+1) : ℕ))
      atTop (nhds (1/2)) ∧
    (∀ k : ℕ, (∑ i : Fin (k+1) × Fin 4,
      ((binaryReal (repeatY (k+1) i))^4+(binaryReal (repeatY (k+1) i))^4)) /
      (4*(k+1) : ℕ) ≤ 2) := by
  have hs : Tendsto (fun k : ℕ => 4*(k+1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    rw [Filter.eventually_atTop]
    refine ⟨b,?_⟩
    intro k hk
    omega
  have ha : ∀ k : ℕ, ((2*(k+1) : ℕ) : ℝ)/(4*(k+1) : ℕ)=1/2 := by
    intro k
    exact (repeated_counterexample_values (k+1) (by omega)).2.2.2.2.2.2.2.2.2.2.1
  have hq : ∀ k : ℕ, (totalSuccesses (repeatY (k+1)) : ℝ)/(4*(k+1) : ℕ)=1/2 := by
    intro k
    exact (repeated_counterexample_values (k+1) (by omega)).2.2.2.2.2.2.2.2.2.2.2
  refine ⟨hs,?_,?_,fun k => repeated_fourth_moments (k+1) (by omega)⟩
  · simpa only [ha] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (nhds (1/2)))
  · simpa only [hq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (nhds (1/2)))

/-- "Finite population of potential outcomes", the Ding notation used on
p. 347. The conventions are fixed real Y_i(1),Y_i(0), N=N1+N0.
Only the assignment is random; both potential-outcome vectors are fixed. -/
structure Population where
  n1 : ℕ
  n0 : ℕ
  Y1 : Fin (n1 + n0) → ℝ
  Y0 : Fin (n1 + n0) → ℝ

/-- Total population size N (notation imported on p. 347). -/
abbrev Population.size (P : Population) : ℕ := P.n1 + P.n0

/-- A finite sample mean, used for both potential and observed outcomes
("difference in means", pp. 346–348). -/
def sampleMean {ι : Type*} [DecidableEq ι] (s : Finset ι) (y : ι → ℝ) : ℝ :=
  (∑ i ∈ s, y i) / (s.card : ℝ)

/-- Sum of squared deviations around a finite sample's own mean
(the published comment gives no divisor convention). -/
def centeredSS {ι : Type*} [DecidableEq ι] (s : Finset ι) (y : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (y i - sampleMean s y)^2

/-- Sample variance with divisor sample size minus one. -/
def sampleVariance {ι : Type*} [DecidableEq ι] (s : Finset ι) (y : ι → ℝ) : ℝ :=
  centeredSS s y / ((s.card : ℝ) - 1)

/-- Finite-population mean Y-bar (tau=Y-bar_1−Y-bar_0 is printed p. 347). -/
def populationMean (P : Population) (y : Fin P.size → ℝ) : ℝ :=
  sampleMean Finset.univ y

/-- Finite-population variance S², divisor N−1. -/
def populationVariance (P : Population) (y : Fin P.size → ℝ) : ℝ :=
  sampleVariance Finset.univ y

/-- The finite average causal effect tau=Y-bar_1−Y-bar_0 (p. 347). -/
def averageEffect (P : Population) : ℝ := populationMean P P.Y1 - populationMean P P.Y0

/-- Unit causal effects Y_i(1)−Y_i(0) ("individual causal effects", p. 346). -/
def unitEffects (P : Population) : Fin P.size → ℝ := fun i => P.Y1 i - P.Y0 i

/-- Fisher's "sharp null of zero individual causal effects" (p. 346). -/
def SharpNull (P : Population) : Prop := ∀ i, P.Y1 i = P.Y0 i

/-- "Constant effects", pp. 346–348: all unit effects equal the population
average causal effect. The common effect need not be zero. -/
def ConstantEffects (P : Population) : Prop := ∀ i, unitEffects P i = averageEffect P

/-- Observed outcome Z_iY_i(1)+(1−Z_i)Y_i(0);
Z is represented by its treated subset of all units. -/
def observed (P : Population) (z : Finset (Fin P.size)) : Fin P.size → ℝ :=
  fun i => if i ∈ z then P.Y1 i else P.Y0 i

/-- Treated-minus-control means on a fixed outcome vector, pp. 346–348.
The complement is among every unit, not a selected control subsample. -/
def difference (P : Population) (z : Finset (Fin P.size)) (y : Fin P.size → ℝ) : ℝ :=
  sampleMean z y - sampleMean zᶜ y

/-- The realized difference-in-means estimator tau-hat, pp. 346–348. -/
def estimate (P : Population) (z : Finset (Fin P.size)) : ℝ := difference P z (observed P z)

/-- Expectation over all complete-randomization assignments, each weighted
1/#Ω. This is an actual finite probability distribution. -/
def randomizationMean (P : Population) (X : Finset (Fin P.size) → ℝ) : ℝ :=
  (∑ z ∈ support P.n1, X z) / ((support (ι := Fin P.size) P.n1).card : ℝ)

/-- Variance over the complete-randomization distribution, V(tau-hat) on
p. 347. It is the average squared centered random variable, not an axiom. -/
def randomizationVariance (P : Population) (X : Finset (Fin P.size) → ℝ) : ℝ :=
  randomizationMean P (fun z => (X z - randomizationMean P X)^2)

/-- Probability of an event under complete randomization. -/
def randomizationProbability (P : Population) (event : Finset (Fin P.size) → Prop) : ℝ := by
  classical
  exact ((support P.n1).filter event).card /
    ((support (ι := Fin P.size) P.n1).card : ℝ)

/-- SSR from the intercept-plus-treatment regression:
within-treated plus within-control centered sums of squares. -/
def residualSS (P : Population) (z : Finset (Fin P.size)) : ℝ :=
  centeredSS z (observed P z) + centeredSS zᶜ (observed P z)

/-- V-hat(OLS), "equivalent to a pooled-variance two-sample z-test", p. 346.
The conventional residual divisor is N−2. -/
def olsVariance (P : Population) (z : Finset (Fin P.size)) : ℝ :=
  residualSS P z / ((P.size : ℝ) - 2) * (1/(P.n1 : ℝ) + 1/(P.n0 : ℝ))

/-- V-hat(Neyman), "one of Neyman's variance estimators", p. 347:
s1²/N1+s0²/N0, with the sample variance conventions above. -/
def neymanVariance (P : Population) (z : Finset (Fin P.size)) : ℝ :=
  sampleVariance z (observed P z) / P.n1 +
    sampleVariance zᶜ (observed P z) / P.n0

/-- V-hat(Fisher), "variance of the FRT reference distribution", p. 347.
Represented by its standard closed form N*s²/(N1*N0).
`frt_reference_variance` separately states equality with the actual uniform
reference-distribution variance, so that equality is not silently assumed proved. -/
def fisherVariance (P : Population) (z : Finset (Fin P.size)) : ℝ :=
  (P.size : ℝ) * populationVariance P (observed P z) / ((P.n1 : ℝ) * P.n0)

/-- Generic finite lemma: centered sum of squares equals raw second moment
minus squared raw first moment divided by the sample size. Used for L1. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem centeredSS_raw {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (y : ι → ℝ) (hs : s.card ≠ 0) :
    centeredSS s y = (∑ i ∈ s, (y i)^2) - (∑ i ∈ s, y i)^2/(s.card : ℝ) := by
  have hsr : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
  calc
    centeredSS s y = ∑ i ∈ s,
        ((y i)^2 - 2 * sampleMean s y * y i + (sampleMean s y)^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ s, (y i)^2) - 2 * sampleMean s y * (∑ i ∈ s, y i) +
        (s.card : ℝ) * (sampleMean s y)^2 := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by unfold sampleMean; field_simp; ring

/-- Complete-randomization support really has positive cardinality, including
all feasible assignments; uniform expectations therefore normalize to one. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem support_positive (P : Population) : 0 < (support (ι := Fin P.size) P.n1).card := by
  change 0 < (Finset.univ.powersetCard P.n1 : Finset (Finset (Fin P.size))).card
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact Nat.choose_pos (by dsimp [Population.size]; omega)


/-- On the complete-randomization support, treated and control subsets have
their prescribed sizes, including every unit exactly once. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem arm_cards (P : Population) (z : Finset (Fin P.size)) (hz : z ∈ support P.n1) :
    z.card=P.n1 ∧ (zᶜ).card=P.n0 := by
  have hs := (Finset.mem_powersetCard.mp hz).2
  refine ⟨hs, ?_⟩
  rw [Finset.card_compl, hs, Fintype.card_fin]
  dsimp [Population.size]
  omega

/-- SSR is exactly (N1−1)s1²+(N0−1)s0² at every admissible assignment,
the residual degrees-of-freedom convention above (pp. 346–347). -/
theorem residualSS_sample_variances (P : Population) (h1 : 2 ≤ P.n1) (h0 : 2 ≤ P.n0)
    (z : Finset (Fin P.size)) (hz : z ∈ support P.n1) :
    residualSS P z = ((P.n1 : ℝ)-1)*sampleVariance z (observed P z) +
      ((P.n0 : ℝ)-1)*sampleVariance zᶜ (observed P z) := by
  obtain ⟨hz1, hz0⟩ := arm_cards P z hz
  have ha : (P.n1 : ℝ)-1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ P.n1 := by exact_mod_cast h1
    linarith
  have hb : (P.n0 : ℝ)-1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ P.n0 := by exact_mod_cast h0
    linarith
  unfold residualSS sampleVariance
  rw [hz1, hz0]
  field_simp <;> ring

/-- Adding a constant to every outcome shifts the sample mean by that
constant whenever the sample is nonempty; used for the constant-effect claim. 
Auxiliary component of Section 2, pp. 346–347, constant-effect and Wald-reference comparisons. -/
theorem sampleMean_add_constant {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (y : ι → ℝ) (c : ℝ) (hs : s.card ≠ 0) :
    sampleMean s (fun i => y i+c) = sampleMean s y+c := by
  have hsr : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
  unfold sampleMean
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp <;> ring

/-- Adding a constant to every outcome leaves a sample variance unchanged,
including empty samples where the finite-sum convention gives zero. 
Auxiliary component of Section 2, pp. 346–347, constant-effect and Wald-reference comparisons. -/
theorem sampleVariance_add_constant {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (y : ι → ℝ) (c : ℝ) :
    sampleVariance s (fun i => y i+c) = sampleVariance s y := by
  by_cases hs : s.card=0
  · have he : s=∅ := Finset.card_eq_zero.mp hs
    simp [he, sampleVariance, centeredSS]
  · unfold sampleVariance centeredSS
    rw [sampleMean_add_constant s y c hs]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    ring

/-- The sample variance of a constant vector is zero, for every sample size. 
Auxiliary component of Section 2, pp. 346–347, constant-effect and Wald-reference comparisons. -/
theorem sampleVariance_constant {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ℝ) : sampleVariance s (fun _ => c) = 0 := by
  have hz : sampleVariance s (fun _ : ι => (0 : ℝ))=0 := by
    simp [sampleVariance, centeredSS, sampleMean]
  simpa using (sampleVariance_add_constant s (fun _ : ι => (0 : ℝ)) c).trans hz

/-- The non-probabilistic content of L7 and T8(b), pp. 347–348: constant
effects force S1²=S0² and S_tau²=0 at every size; no asymptotic approximation. -/
theorem constant_effect_variances (P : Population) (hc : ConstantEffects P) :
    populationVariance P P.Y1=populationVariance P P.Y0 ∧
    populationVariance P (unitEffects P)=0 := by
  have hy : P.Y1 = fun i => P.Y0 i+averageEffect P := by
    funext i
    have hh := hc i
    unfold unitEffects at hh
    linarith
  have ht : unitEffects P = fun _ => averageEffect P := funext hc
  constructor
  · rw [hy]
    exact sampleVariance_add_constant _ _ _
  · rw [ht]
    exact sampleVariance_constant _ _


/-- Complete-randomization expectation of a constant is that constant;
the genuine uniform design is normalized (p. 347). -/
theorem randomizationMean_constant (P : Population) (c : ℝ) :
    randomizationMean P (fun _ => c)=c := by
  have hd : ((support (ι := Fin P.size) P.n1).card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (support_positive P))
  unfold randomizationMean
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- Probability one for the full complete-randomization space, verifying
that none of the convergence-in-probability statements uses a zero measure. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomizationProbability_univ (P : Population) :
    randomizationProbability P (fun _ => True)=1 := by
  have hd : ((support (ι := Fin P.size) P.n1).card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (support_positive P))
  simp [randomizationProbability, hd]

/-- Finite linearity of the actual complete-randomization expectation. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomizationMean_sub (P : Population) (X Y : Finset (Fin P.size) → ℝ) :
    randomizationMean P (fun z => X z-Y z)=randomizationMean P X-randomizationMean P Y := by
  simp only [randomizationMean, Finset.sum_sub_distrib, sub_div]

/-- A constant multiple pulls through the uniform finite expectation. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomizationMean_mul (P : Population) (c : ℝ) (X : Finset (Fin P.size) → ℝ) :
    randomizationMean P (fun z => c*X z)=c*randomizationMean P X := by
  simp only [randomizationMean, ← Finset.mul_sum]
  ring

/-- Finite sums commute with expectation over complete randomization. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomizationMean_sum (P : Population)
    (X : Fin P.size → Finset (Fin P.size) → ℝ) :
    randomizationMean P (fun z => ∑ i, X i z)=∑ i, randomizationMean P (X i) := by
  unfold randomizationMean
  rw [Finset.sum_comm, Finset.sum_div]

/-- A function equal on all supported assignments has the same finite
randomization expectation; off-support choices are irrelevant. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomizationMean_congr (P : Population) (X Y : Finset (Fin P.size) → ℝ)
    (h : ∀ z ∈ support P.n1, X z=Y z) : randomizationMean P X=randomizationMean P Y := by
  unfold randomizationMean
  congr 1
  exact Finset.sum_congr rfl h

/-- Each unit has marginal treatment probability N1/N under the full uniform
complete-randomization design. This is proved by binomial subset counting. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem marginal_treatment_mean (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (i : Fin P.size) :
    randomizationMean P (fun z => if i ∈ z then 1 else 0)=(P.n1 : ℝ)/P.size := by
  have hN : 0 < P.size := by dsimp [Population.size]; omega
  have hd : ((support (ι := Fin P.size) P.n1).card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (support_positive P))
  have hNr : (P.size : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hfilter : ((support (ι := Fin P.size) P.n1).filter (fun z => i ∈ z)).card =
      (P.size-1).choose (P.n1-1) := by
    simpa [support] using (Finset.card_filter_powersetCard_subset {i}
      (Finset.univ : Finset (Fin P.size)) P.n1 (by simp) (by simp; omega))
  have hsum : (∑ z ∈ support P.n1, if i ∈ z then (1 : ℝ) else 0) =
      (((support (ι := Fin P.size) P.n1).filter (fun z => i ∈ z)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  have hchoose := Nat.add_one_mul_choose_eq (P.size-1) (P.n1-1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ P.size), Nat.sub_add_cancel (by omega : 1 ≤ P.n1)] at hchoose
  unfold randomizationMean
  rw [hsum, hfilter]
  have hc : (support (ι := Fin P.size) P.n1).card=P.size.choose P.n1 := by
    simp [support]
  rw [hc] at hd ⊢
  field_simp
  have hr : (P.size : ℝ)*((P.size-1).choose (P.n1-1) : ℝ) =
    (P.size.choose P.n1 : ℝ)*P.n1 := by exact_mod_cast hchoose
  nlinarith [hr]

/-- The expected sum in the treated subset is N1/N times the population
sum, for any fixed real vector; finite ingredient of L5 and L2. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomization_sample_sum (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (y : Fin P.size → ℝ) :
    randomizationMean P (fun z => ∑ i ∈ z, y i) =
      (P.n1 : ℝ)/P.size * (∑ i, y i) := by
  have hfun : (fun z : Finset (Fin P.size) => ∑ i ∈ z, y i) =
      (fun z => ∑ i : Fin P.size, y i*(if i ∈ z then 1 else 0)) := by
    funext z
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    simp
  rw [hfun, randomizationMean_sum]
  simp_rw [randomizationMean_mul, marginal_treatment_mean P h1 h0]
  rw [← Finset.sum_mul]
  ring

/-- The actual observed estimator can be written as one treated subset sum
of Y1/N1+Y0/N0 minus the fixed population sum of Y0/N0 (L5, p. 347). -/
theorem estimate_sample_sum (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (z : Finset (Fin P.size)) (hz : z ∈ support P.n1) :
    estimate P z = (∑ i ∈ z, (P.Y1 i/(P.n1 : ℝ)+P.Y0 i/(P.n0 : ℝ))) -
      (∑ i : Fin P.size, P.Y0 i)/(P.n0 : ℝ) := by
  obtain ⟨hc1, hc0⟩ := arm_cards P z hz
  have hs1 : (∑ i ∈ z, observed P z i) = ∑ i ∈ z, P.Y1 i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [observed, hi]
  have hs0 : (∑ i ∈ zᶜ, observed P z i) = ∑ i ∈ zᶜ, P.Y0 i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [observed, Finset.mem_compl.mp hi]
  unfold estimate difference sampleMean
  rw [hs1, hs0, hc1, hc0]
  have hsum := (Finset.sum_add_sum_compl z P.Y0).symm
  simp only [Finset.sum_add_distrib, ← Finset.sum_div]
  rw [hsum]
  ring

/-- L5's unbiasedness, with the real finite complete-randomization
expectation: E[tau-hat]=tau (p. 347 variance comparisons). -/
theorem difference_in_means_unbiased (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0) :
    randomizationMean P (estimate P)=averageEffect P := by
  have ha : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h1)
  have hb : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h0)
  have hN : (P.size : ℝ) ≠ 0 := by dsimp [Population.size]; push_cast; positivity
  rw [randomizationMean_congr P _ _ (estimate_sample_sum P h1 h0),
    randomizationMean_sub, randomizationMean_constant, randomization_sample_sum P h1 h0]
  unfold averageEffect populationMean sampleMean
  simp only [Finset.card_univ, Fintype.card_fin, Finset.sum_add_distrib, ← Finset.sum_div]
  simp only [Population.size, Nat.cast_add] at hN ⊢
  field_simp <;> ring


/-- Distinct units are jointly treated with probability
N1(N1−1)/(N(N−1)); exact sampling without replacement, used for L2/L5/L6. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem joint_treatment_mean (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (i j : Fin P.size) (hij : i ≠ j) :
    randomizationMean P (fun z => if i ∈ z ∧ j ∈ z then 1 else 0) =
      ((P.n1 : ℝ)*((P.n1 : ℝ)-1))/((P.size : ℝ)*((P.size : ℝ)-1)) := by
  have hN : 2 ≤ P.size := by dsimp [Population.size]; omega
  have hNr : (P.size : ℝ) ≠ 0 := by exact_mod_cast (by omega : P.size ≠ 0)
  have hNr1 : (P.size : ℝ)-1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ P.size := by exact_mod_cast hN
    linarith
  by_cases hk : 2 ≤ P.n1
  · have hd : ((support (ι := Fin P.size) P.n1).card : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (support_positive P))
    have hfilter : ((support (ι := Fin P.size) P.n1).filter (fun z => i ∈ z ∧ j ∈ z)).card =
        (P.size-2).choose (P.n1-2) := by
      simpa [support, hij, Finset.insert_subset_iff, Finset.singleton_subset_iff] using (Finset.card_filter_powersetCard_subset {i,j}
        (Finset.univ : Finset (Fin P.size)) P.n1 (by simp) (by simp [hij]; omega))
    have hsum : (∑ z ∈ support P.n1, if i ∈ z ∧ j ∈ z then (1 : ℝ) else 0) =
        (((support (ι := Fin P.size) P.n1).filter (fun z => i ∈ z ∧ j ∈ z)).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp
    have hc : (support (ι := Fin P.size) P.n1).card=P.size.choose P.n1 := by simp [support]
    have hA := Nat.add_one_mul_choose_eq (P.size-1) (P.n1-1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ P.size),
      Nat.sub_add_cancel (by omega : 1 ≤ P.n1)] at hA
    have hB := Nat.add_one_mul_choose_eq (P.size-2) (P.n1-2)
    have hNN : P.size-2+1=P.size-1 := by omega
    have hKK : P.n1-2+1=P.n1-1 := by omega
    rw [hNN, hKK] at hB
    have hAr : (P.size : ℝ)*((P.size-1).choose (P.n1-1) : ℝ) =
        (P.size.choose P.n1 : ℝ)*P.n1 := by exact_mod_cast hA
    have hBr : ((P.size : ℝ)-1)*((P.size-2).choose (P.n1-2) : ℝ) =
        ((P.size-1).choose (P.n1-1) : ℝ)*((P.n1 : ℝ)-1) := by
      have hh : ((P.size-1 : ℕ) : ℝ)*((P.size-2).choose (P.n1-2) : ℝ) =
        ((P.size-1).choose (P.n1-1) : ℝ)*((P.n1-1 : ℕ) : ℝ) := by exact_mod_cast hB
      rw [Nat.cast_sub (by omega : 1 ≤ P.size), Nat.cast_sub (by omega : 1 ≤ P.n1)] at hh
      simpa only [Nat.cast_one] using hh
    unfold randomizationMean
    rw [hsum, hfilter, hc]
    rw [hc] at hd
    field_simp
    linear_combination (P.size : ℝ)*hBr + ((P.n1 : ℝ)-1)*hAr
  · have hk1 : P.n1=1 := by omega
    have hz0 : ∀ z ∈ support P.n1, (if i ∈ z ∧ j ∈ z then (1 : ℝ) else 0)=0 := by
      intro z hz
      have hcard := (arm_cards P z hz).1
      split_ifs with h
      · have hsub : ({i,j} : Finset (Fin P.size)) ⊆ z := by
          simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
          exact ⟨h.1, h.2⟩
        have hh := Finset.card_le_card hsub
        simp [hij, hcard, hk1] at hh
      · rfl
    rw [randomizationMean_congr P _ _ hz0, randomizationMean_constant]
    simp [hk1]

/-- The second inclusion moment, including the diagonal term, for the full
uniform design; used when expanding the square of a treated-sample sum. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem treatment_product_mean (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (i j : Fin P.size) :
    randomizationMean P (fun z => (if i ∈ z then 1 else 0)*(if j ∈ z then 1 else 0)) =
      if i=j then (P.n1 : ℝ)/P.size else
        ((P.n1 : ℝ)*((P.n1 : ℝ)-1))/((P.size : ℝ)*((P.size : ℝ)-1)) := by
  by_cases hij : i=j
  · subst j
    simp only [if_pos rfl]
    rw [randomizationMean_congr P _ (fun z => if i ∈ z then 1 else 0)
      (by intro z hz; by_cases hi : i ∈ z <;> simp [hi])]
    exact marginal_treatment_mean P h1 h0 i
  · rw [if_neg hij]
    rw [randomizationMean_congr P _ (fun z => if i ∈ z ∧ j ∈ z then 1 else 0)
      (by intro z hz; by_cases hi : i ∈ z <;> by_cases hj : j ∈ z <;> simp [hi,hj])]
    exact joint_treatment_mean P h1 h0 i j hij

/-- Raw second moment of a treated-sample sum, derived by diagonal and
off-diagonal inclusion probabilities; finite ingredient of L2/L5/L6. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomization_sample_square (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (y : Fin P.size → ℝ) :
    let r := (P.n1 : ℝ)/P.size
    let q := ((P.n1 : ℝ)*((P.n1 : ℝ)-1))/((P.size : ℝ)*((P.size : ℝ)-1))
    randomizationMean P (fun z => (∑ i ∈ z, y i)^2) =
      q*(∑ i, y i)^2+(r-q)*(∑ i, (y i)^2) := by
  dsimp only
  let r := (P.n1 : ℝ)/P.size
  let q := ((P.n1 : ℝ)*((P.n1 : ℝ)-1))/((P.size : ℝ)*((P.size : ℝ)-1))
  have hs : (fun z : Finset (Fin P.size) => (∑ i ∈ z, y i)^2) =
      (fun z => ∑ i : Fin P.size, ∑ j : Fin P.size,
        (y i*y j)*((if i ∈ z then 1 else 0)*(if j ∈ z then 1 else 0))) := by
    funext z
    have hsum : (∑ i ∈ z, y i) = ∑ i : Fin P.size, y i*(if i ∈ z then 1 else 0) := by
      simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
      simp
    rw [hsum, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hs, randomizationMean_sum]
  simp_rw [randomizationMean_sum, randomizationMean_mul, treatment_product_mean P h1 h0]
  change (∑ i : Fin P.size, ∑ j : Fin P.size, (y i*y j)*(if i=j then r else q)) =
    q*(∑ i, y i)^2+(r-q)*(∑ i, (y i)^2)
  have he : ∀ i j, (y i*y j)*(if i=j then r else q) =
      q*y i*y j+(if i=j then (r-q)*(y i)^2 else 0) := by
    intro i j
    split_ifs with h
    · subst j
      ring
    · ring
  simp_rw [he, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Variance equals E[X²]−E[X]² for the finite normalized randomization law.
This is proved from the squared-deviation definition, not stipulated. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomizationVariance_raw (P : Population) (X : Finset (Fin P.size) → ℝ) :
    randomizationVariance P X=randomizationMean P (fun z => (X z)^2)-(randomizationMean P X)^2 := by
  have he : (fun z => (X z-randomizationMean P X)^2) =
      (fun z => (X z)^2-2*randomizationMean P X*X z+(randomizationMean P X)^2) := by
    funext z
    ring
  unfold randomizationVariance
  rw [he]
  have hadd : ∀ A B : Finset (Fin P.size) → ℝ,
      randomizationMean P (fun z => A z+B z)=randomizationMean P A+randomizationMean P B := by
    intro A B
    simp only [randomizationMean, Finset.sum_add_distrib, add_div]
  rw [hadd, randomizationMean_sub, randomizationMean_mul, randomizationMean_constant]
  ring

/-- Exact variance of a sum over a simple random sample of size N1:
Var(sum_treated y)=N1*N0/N * S_y². All arm sizes may be one. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomization_sample_variance (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (y : Fin P.size → ℝ) :
    randomizationVariance P (fun z => ∑ i ∈ z, y i) =
      ((P.n1 : ℝ)*P.n0/P.size)*populationVariance P y := by
  have ha : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h1)
  have hb : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h0)
  have hNnat : 2 ≤ P.size := by dsimp [Population.size]; omega
  have hN : (P.size : ℝ) ≠ 0 := by exact_mod_cast (by omega : P.size ≠ 0)
  have hNm1 : (P.size : ℝ)-1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ P.size := by exact_mod_cast hNnat
    linarith
  rw [randomizationVariance_raw, randomization_sample_square P h1 h0,
    randomization_sample_sum P h1 h0]
  unfold populationVariance sampleVariance
  rw [centeredSS_raw Finset.univ y (by simpa using (by omega : P.size ≠ 0))]
  simp only [Finset.card_univ, Fintype.card_fin]
  simp only [Population.size, Nat.cast_add] at hN hNm1 ⊢
  field_simp <;> ring


/-- Finite sample means are linear, including empty samples under Lean's
zero-division convention (no theorem uses that case for an arm mean). 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem sampleMean_linear {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (y w : ι → ℝ) (a b : ℝ) :
    sampleMean s (fun i => a*y i+b*w i)=a*sampleMean s y+b*sampleMean s w := by
  unfold sampleMean
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Finite-population variances of a scaled vector scale by the square of
the coefficient, used to certify the heterogeneous witness (T8). 
Auxiliary component of Section 3, pp. 347–348, Neyman bound and constant/heterogeneous effects. -/
theorem sampleVariance_scale {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (y : ι → ℝ) (a : ℝ) :
    sampleVariance s (fun i => a*y i)=a^2*sampleVariance s y := by
  have hm : sampleMean s (fun i => a*y i)=a*sampleMean s y := by
    simpa using sampleMean_linear s y y a 0
  unfold sampleVariance centeredSS
  rw [hm]
  have he : (∑ i ∈ s, (a*y i-a*sampleMean s y)^2) =
      a^2*(∑ i ∈ s, (y i-sampleMean s y)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  ring

/-- Equality on all supported assignments implies equality of actual
randomization variances, including the equality of their finite means. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomizationVariance_congr (P : Population) (X Y : Finset (Fin P.size) → ℝ)
    (h : ∀ z ∈ support P.n1, X z=Y z) : randomizationVariance P X=randomizationVariance P Y := by
  unfold randomizationVariance
  rw [randomizationMean_congr P X Y h]
  apply randomizationMean_congr
  intro z hz
  rw [h z hz]

/-- Shifting every value of a randomization statistic by a constant does
not change its actual variance, an ingredient of L5 and the imputation claim. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomizationVariance_sub_constant (P : Population)
    (X : Finset (Fin P.size) → ℝ) (c : ℝ) :
    randomizationVariance P (fun z => X z-c)=randomizationVariance P X := by
  unfold randomizationVariance
  rw [randomizationMean_sub, randomizationMean_constant]
  congr 1
  funext z
  congr 1
  ring

/-- The deterministic quadratic identity translating a sample-sum variance
into Neyman's potential-outcome and effect-variance formula (L5). 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem weighted_potential_variance (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0) :
    ((P.n1 : ℝ)*P.n0/P.size)*
      populationVariance P (fun i => P.Y1 i/(P.n1 : ℝ)+P.Y0 i/(P.n0 : ℝ)) =
    populationVariance P P.Y1/P.n1+populationVariance P P.Y0/P.n0-
      populationVariance P (unitEffects P)/P.size := by
  have ha : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h1)
  have hb : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h0)
  have hN : (P.size : ℝ) ≠ 0 := by dsimp [Population.size]; push_cast; positivity
  have hm : sampleMean Finset.univ
      (fun i => P.Y1 i/(P.n1 : ℝ)+P.Y0 i/(P.n0 : ℝ)) =
      sampleMean Finset.univ P.Y1/P.n1+sampleMean Finset.univ P.Y0/P.n0 := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (sampleMean_linear Finset.univ P.Y1 P.Y0 (P.n1 : ℝ)⁻¹ (P.n0 : ℝ)⁻¹)
  have ht : sampleMean Finset.univ (unitEffects P)=
      sampleMean Finset.univ P.Y1-sampleMean Finset.univ P.Y0 := by
    unfold unitEffects
    simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using
      sampleMean_linear Finset.univ P.Y1 P.Y0 1 (-1)
  have he : ∀ i : Fin P.size,
      ((P.n1 : ℝ)*P.n0/P.size)*
        ((P.Y1 i/(P.n1 : ℝ)+P.Y0 i/(P.n0 : ℝ))-
          (sampleMean Finset.univ P.Y1/P.n1+sampleMean Finset.univ P.Y0/P.n0))^2 =
      (P.Y1 i-sampleMean Finset.univ P.Y1)^2/P.n1+
        (P.Y0 i-sampleMean Finset.univ P.Y0)^2/P.n0-
        ((P.Y1 i-P.Y0 i)-(sampleMean Finset.univ P.Y1-sampleMean Finset.univ P.Y0))^2/P.size := by
    intro i
    simp only [Population.size, Nat.cast_add] at hN ⊢
    field_simp <;> ring
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin P.size))) rfl
    (fun i hi => he i)
  unfold populationVariance sampleVariance centeredSS
  rw [hm, ht]
  simp only [unitEffects]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div] at hs
  simp only [Finset.card_univ, Fintype.card_fin]
  linear_combination (1/((P.size : ℝ)-1))*hs

/-- L5's full actual variance identity: the randomization variance of
tau-hat equals S1²/N1+S0²/N0−S_tau²/N for every positive-arm population. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem difference_in_means_variance (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0) :
    randomizationVariance P (estimate P)=
      populationVariance P P.Y1/P.n1+populationVariance P P.Y0/P.n0-
      populationVariance P (unitEffects P)/P.size := by
  rw [randomizationVariance_congr P _ _ (estimate_sample_sum P h1 h0),
    randomizationVariance_sub_constant, randomization_sample_variance P h1 h0]
  exact weighted_potential_variance P h1 h0


/-- Finite expectation also commutes with division by a fixed scalar;
the proof uses the actual normalized uniform finite sum. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomizationMean_div (P : Population) (X : Finset (Fin P.size) → ℝ) (c : ℝ) :
    randomizationMean P (fun z => X z/c)=randomizationMean P X/c := by
  simp only [randomizationMean, ← Finset.sum_div]
  ring

/-- Scaling a randomization statistic by c scales its actual variance by c². 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomizationVariance_scale (P : Population) (X : Finset (Fin P.size) → ℝ) (c : ℝ) :
    randomizationVariance P (fun z => c*X z)=c^2*randomizationVariance P X := by
  rw [randomizationVariance_raw, randomizationVariance_raw]
  have hs : (fun z => (c*X z)^2)=(fun z => c^2*(X z)^2) := by funext z; ring
  rw [hs, randomizationMean_mul, randomizationMean_mul]
  ring

/-- With fixed outcomes y, the reference difference equals a scaled treated
sum minus a fixed population-total term (finite ingredient of L2). 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem difference_sample_sum (P : Population) (z : Finset (Fin P.size))
    (hz : z ∈ support P.n1) (y : Fin P.size → ℝ) :
    difference P z y = (1/(P.n1 : ℝ)+1/(P.n0 : ℝ))*(∑ i ∈ z, y i)-
      (∑ i : Fin P.size, y i)/(P.n0 : ℝ) := by
  obtain ⟨hc1,hc0⟩ := arm_cards P z hz
  unfold difference sampleMean
  rw [hc1,hc0, (Finset.sum_add_sum_compl z y).symm]
  ring

/-- The reference difference has mean zero under the full uniform fresh
assignment distribution, for every fixed real outcome vector (L2). 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem reference_difference_mean (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (y : Fin P.size → ℝ) : randomizationMean P (fun z => difference P z y)=0 := by
  have ha : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h1)
  have hb : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h0)
  have hN : (P.size : ℝ) ≠ 0 := by dsimp [Population.size]; push_cast; positivity
  rw [randomizationMean_congr P _ _ (fun z hz => difference_sample_sum P z hz y),
    randomizationMean_sub, randomizationMean_mul, randomizationMean_constant,
    randomization_sample_sum P h1 h0]
  simp only [Population.size, Nat.cast_add] at hN ⊢
  field_simp <;> ring

/-- The actual FRT reference variance is N*S_y²/(N1*N0), proved by
sampling-without-replacement second moments for all fixed real y (L2). 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem reference_difference_variance (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (y : Fin P.size → ℝ) :
    randomizationVariance P (fun z => difference P z y)=
      (P.size : ℝ)*populationVariance P y/((P.n1 : ℝ)*P.n0) := by
  have ha : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h1)
  have hb : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h0)
  have hN : (P.size : ℝ) ≠ 0 := by dsimp [Population.size]; push_cast; positivity
  rw [randomizationVariance_congr P _ _ (fun z hz => difference_sample_sum P z hz y),
    randomizationVariance_sub_constant, randomizationVariance_scale,
    randomization_sample_variance P h1 h0]
  simp only [Population.size, Nat.cast_add] at hN ⊢
  field_simp <;> ring

/-- A sample variance depends only on the values at the sampled units;
used to replace observed outcomes by the appropriate potential outcomes. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem sampleVariance_congr {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (y w : ι → ℝ) (h : ∀ i ∈ s, y i=w i) : sampleVariance s y=sampleVariance s w := by
  have hm : sampleMean s y=sampleMean s w := by
    unfold sampleMean
    rw [Finset.sum_congr rfl h]
  unfold sampleVariance centeredSS
  rw [hm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i hi]

/-- Unbiasedness of a treated arm sample variance under the uniform fixed-size
design, divisor N1−1; exact first/second-moment ingredient of L6. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem treated_sample_variance_unbiased (P : Population) (h1 : 2 ≤ P.n1) (h0 : 0 < P.n0)
    (y : Fin P.size → ℝ) :
    randomizationMean P (fun z => sampleVariance z y)=populationVariance P y := by
  have ha : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : P.n1 ≠ 0)
  have ham1 : (P.n1 : ℝ)-1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ P.n1 := by exact_mod_cast h1
    linarith
  have hN : (P.size : ℝ) ≠ 0 := by dsimp [Population.size]; push_cast; positivity
  have hNm1 : (P.size : ℝ)-1 ≠ 0 := by
    have hh : (3 : ℝ) ≤ P.size := by exact_mod_cast (by dsimp [Population.size]; omega : 3 ≤ P.size)
    linarith
  have hp : ∀ z ∈ support P.n1, sampleVariance z y =
      ((∑ i ∈ z, (y i)^2)-(∑ i ∈ z, y i)^2/(P.n1 : ℝ))/((P.n1 : ℝ)-1) := by
    intro z hz
    have hc := (arm_cards P z hz).1
    unfold sampleVariance
    rw [centeredSS_raw z y (by omega), hc]
  rw [randomizationMean_congr P _ _ hp, randomizationMean_div, randomizationMean_sub,
    randomizationMean_div, randomization_sample_sum P (by omega) h0,
    randomization_sample_square P (by omega) h0]
  unfold populationVariance sampleVariance
  rw [centeredSS_raw Finset.univ y (by simpa using (by dsimp [Population.size]; omega : P.size ≠ 0))]
  simp only [Finset.card_univ, Fintype.card_fin]
  simp only [Population.size, Nat.cast_add] at hN hNm1 ⊢
  field_simp <;> ring


/-- Complementary-sample sum expectation: the control arm samples each
fixed vector with fraction N0/N, without any independent-Bernoulli model. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomization_control_sum (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (y : Fin P.size → ℝ) :
    randomizationMean P (fun z => ∑ i ∈ zᶜ, y i)=
      (P.n0 : ℝ)/P.size * (∑ i, y i) := by
  have hN : (P.size : ℝ) ≠ 0 := by dsimp [Population.size]; push_cast; positivity
  have he : ∀ z ∈ support P.n1, (∑ i ∈ zᶜ, y i)=(∑ i, y i)-(∑ i ∈ z, y i) := by
    intro z hz
    linear_combination (Finset.sum_add_sum_compl z y)
  rw [randomizationMean_congr P _ _ he, randomizationMean_sub,
    randomizationMean_constant, randomization_sample_sum P h1 h0]
  simp only [Population.size, Nat.cast_add] at hN ⊢
  field_simp <;> ring

/-- A control sample sum has the same variance as the complementary treated
sum; this follows from their sum being the fixed population total. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomization_control_variance (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (y : Fin P.size → ℝ) :
    randomizationVariance P (fun z => ∑ i ∈ zᶜ, y i)=
      ((P.n1 : ℝ)*P.n0/P.size)*populationVariance P y := by
  have he : ∀ z ∈ support P.n1, (∑ i ∈ zᶜ, y i)=
      (-1 : ℝ)*(∑ i ∈ z, y i)-(-(∑ i, y i)) := by
    intro z hz
    linear_combination (Finset.sum_add_sum_compl z y)
  rw [randomizationVariance_congr P _ _ he, randomizationVariance_sub_constant,
    randomizationVariance_scale]
  norm_num
  simpa only [Population.size, Nat.cast_add] using randomization_sample_variance P h1 h0 y

/-- Raw second moment of the control sum, deduced from its genuine variance
and mean, for the arm-variance unbiasedness lemma L6. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomization_control_square (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (y : Fin P.size → ℝ) :
    randomizationMean P (fun z => (∑ i ∈ zᶜ, y i)^2)=
      ((P.n1 : ℝ)*P.n0/P.size)*populationVariance P y+
      ((P.n0 : ℝ)/P.size*(∑ i, y i))^2 := by
  have hh := randomizationVariance_raw P (fun z => ∑ i ∈ zᶜ, y i)
  rw [randomization_control_variance P h1 h0, randomization_control_sum P h1 h0] at hh
  linarith

/-- The control arm sample variance is unbiased for the fixed vector's
population variance, divisor N0−1; L6 under complete randomization. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem control_sample_variance_unbiased (P : Population) (h1 : 0 < P.n1) (h0 : 2 ≤ P.n0)
    (y : Fin P.size → ℝ) :
    randomizationMean P (fun z => sampleVariance zᶜ y)=populationVariance P y := by
  have hb : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast (by omega : P.n0 ≠ 0)
  have hbm1 : (P.n0 : ℝ)-1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ P.n0 := by exact_mod_cast h0
    linarith
  have hN : (P.size : ℝ) ≠ 0 := by dsimp [Population.size]; push_cast; positivity
  have hNm1 : (P.size : ℝ)-1 ≠ 0 := by
    have hn : 3 ≤ P.size := by dsimp [Population.size]; omega
    have hh : (3 : ℝ) ≤ P.size := by exact_mod_cast hn
    linarith
  have hp : ∀ z ∈ support P.n1, sampleVariance zᶜ y =
      ((∑ i ∈ zᶜ, (y i)^2)-(∑ i ∈ zᶜ, y i)^2/(P.n0 : ℝ))/((P.n0 : ℝ)-1) := by
    intro z hz
    have hc := (arm_cards P z hz).2
    unfold sampleVariance
    rw [centeredSS_raw zᶜ y (by omega), hc]
  rw [randomizationMean_congr P _ _ hp, randomizationMean_div, randomizationMean_sub,
    randomizationMean_div, randomization_control_sum P h1 (by omega),
    randomization_control_square P h1 (by omega)]
  unfold populationVariance sampleVariance
  simp only [centeredSS_raw Finset.univ y (by simpa using
    (by dsimp [Population.size]; omega : P.size ≠ 0)), Finset.card_univ, Fintype.card_fin]
  simp only [Population.size, Nat.cast_add] at hN hNm1 ⊢
  field_simp <;> ring

/-- Observation restriction for the treated sample variance: at every
sampled unit Y_obs=Y1; finite modelling lemma for L6. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem treated_variance_observed (P : Population) (z : Finset (Fin P.size)) :
    sampleVariance z (observed P z)=sampleVariance z P.Y1 := by
  apply sampleVariance_congr
  intro i hi
  simp [observed, hi]

/-- Observation restriction for the control sample variance: at every
control unit Y_obs=Y0; finite modelling lemma for L6. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem control_variance_observed (P : Population) (z : Finset (Fin P.size)) :
    sampleVariance zᶜ (observed P z)=sampleVariance zᶜ P.Y0 := by
  apply sampleVariance_congr
  intro i hi
  simp [observed, Finset.mem_compl.mp hi]

/-- Additivity of finite randomization means, used to combine variance
estimators without introducing any independence hypothesis. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem randomizationMean_add (P : Population) (X Y : Finset (Fin P.size) → ℝ) :
    randomizationMean P (fun z => X z+Y z)=randomizationMean P X+randomizationMean P Y := by
  simp only [randomizationMean, Finset.sum_add_distrib, add_div]


/-- Nonnegative finite-population variance, supporting Neyman's bound.
The size hypothesis excludes the undefined divisor convention at N=1. 
Auxiliary component of Section 3, pp. 347–348, Neyman bound and constant/heterogeneous effects. -/
theorem populationVariance_nonnegative (P : Population) (hN : 2 ≤ P.size)
    (y : Fin P.size → ℝ) : 0 ≤ populationVariance P y := by
  unfold populationVariance sampleVariance centeredSS
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i hi => sq_nonneg _)
  · simp only [Finset.card_univ, Fintype.card_fin]
    have hh : (2 : ℝ) ≤ P.size := by exact_mod_cast hN
    linarith


/-- L1 (finite lemma behind Section 2, p. 347): decomposition of the combined
observed variance into within-arm SSR and the between-arm tau-hat term. -/
theorem combined_variance_decomposition (P : Population)
    (h1 : 2 ≤ P.n1) (h0 : 2 ≤ P.n0) (z : Finset (Fin P.size))
    (hz : z ∈ support P.n1) :
    ((P.size : ℝ)-1) * populationVariance P (observed P z) =
      residualSS P z + ((P.n1 : ℝ)*P.n0/(P.size : ℝ)) * (estimate P z)^2 := by
  obtain ⟨hz1, hz0⟩ := arm_cards P z hz
  have ha : (P.n1 : ℝ) ≠ 0 := by
    have hh : (2 : ℝ) ≤ P.n1 := by exact_mod_cast h1
    linarith
  have hb : (P.n0 : ℝ) ≠ 0 := by
    have hh : (2 : ℝ) ≤ P.n0 := by exact_mod_cast h0
    linarith
  have hN : (P.size : ℝ) ≠ 0 := by simp only [Population.size, Nat.cast_add]; positivity
  have hN1 : (P.size : ℝ)-1 ≠ 0 := by
    have hh1 : (2 : ℝ) ≤ P.n1 := by exact_mod_cast h1
    have hh0 : (2 : ℝ) ≤ P.n0 := by exact_mod_cast h0
    simp only [Population.size, Nat.cast_add]
    linarith
  have hs : ((P.size : ℝ)-1)*populationVariance P (observed P z) =
      centeredSS Finset.univ (observed P z) := by
    unfold populationVariance sampleVariance
    simp only [Finset.card_univ, Fintype.card_fin]
    field_simp
  rw [hs]
  unfold residualSS estimate difference
  have hU : (Finset.univ : Finset (Fin P.size)).card ≠ 0 := by
    simp only [Finset.card_univ, Fintype.card_fin]
    dsimp [Population.size]
    omega
  have hzN : z.card ≠ 0 := by omega
  have hcN : (zᶜ).card ≠ 0 := by omega
  rw [centeredSS_raw Finset.univ (observed P z) hU,
    centeredSS_raw z (observed P z) hzN, centeredSS_raw zᶜ (observed P z) hcN]
  have hy := (Finset.sum_add_sum_compl z (observed P z)).symm
  have hy2 := (Finset.sum_add_sum_compl z (fun i => (observed P z i)^2)).symm
  rw [hy, hy2]
  unfold sampleMean
  rw [hz1, hz0]
  simp only [Finset.card_univ, Fintype.card_fin]
  simp only [Population.size, Nat.cast_add] at hN ⊢
  field_simp <;> ring

/-- L2: for fixed real outcomes y and a fresh complete randomization, the
difference in means has reference mean zero and variance N*S_y²/(N1*N0).
This connects the closed-form Fisher object to its distribution (p. 347). -/
theorem frt_reference_variance (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (y : Fin P.size → ℝ) :
    randomizationMean P (fun z => difference P z y) = 0 ∧
    randomizationVariance P (fun z => difference P z y) =
      (P.size : ℝ)*populationVariance P y/((P.n1 : ℝ)*P.n0) := by
  exact ⟨reference_difference_mean P h1 h0 y, reference_difference_variance P h1 h0 y⟩

/-- L3's exact pooled-variance formula behind V-hat(OLS), pp. 346–347. -/
theorem ols_pooled_formula (P : Population) (h1 : 2 ≤ P.n1) (h0 : 2 ≤ P.n0)
    (z : Finset (Fin P.size)) :
    olsVariance P z = (P.size : ℝ)*residualSS P z/
      ((P.n1 : ℝ)*P.n0*((P.size : ℝ)-2)) := by
  unfold olsVariance Population.size
  have ha : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : P.n1 ≠ 0)
  have hb : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast (by omega : P.n0 ≠ 0)
  push_cast
  field_simp <;> ring

/-- L4: the exact Fisher–OLS difference is (tau-hat²−V-hat(OLS))/(N−1),
the finite identity underlying the Section 2 asymptotic comparison. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem fisher_ols_exact (P : Population) (h1 : 2 ≤ P.n1) (h0 : 2 ≤ P.n0)
    (z : Finset (Fin P.size)) (hz : z ∈ support P.n1) :
    fisherVariance P z = (P.size : ℝ)*residualSS P z /
        ((P.n1 : ℝ)*P.n0*((P.size : ℝ)-1)) + (estimate P z)^2/((P.size : ℝ)-1) ∧
    fisherVariance P z - olsVariance P z =
      ((estimate P z)^2 - olsVariance P z)/((P.size : ℝ)-1) := by
  have ha : (P.n1 : ℝ) ≠ 0 := by
    have hh : (2 : ℝ) ≤ P.n1 := by exact_mod_cast h1
    linarith
  have hb : (P.n0 : ℝ) ≠ 0 := by
    have hh : (2 : ℝ) ≤ P.n0 := by exact_mod_cast h0
    linarith
  have hN : (P.size : ℝ) ≠ 0 := by simp only [Population.size, Nat.cast_add]; positivity
  have hh1 : (2 : ℝ) ≤ P.n1 := by exact_mod_cast h1
  have hh0 : (2 : ℝ) ≤ P.n0 := by exact_mod_cast h0
  have hN1 : (P.size : ℝ)-1 ≠ 0 := by simp only [Population.size, Nat.cast_add]; linarith
  have hN2 : (P.size : ℝ)-2 ≠ 0 := by simp only [Population.size, Nat.cast_add]; linarith
  have hsvar : populationVariance P (observed P z) =
      (residualSS P z+((P.n1 : ℝ)*P.n0/P.size)*(estimate P z)^2)/((P.size : ℝ)-1) := by
    apply (eq_div_iff hN1).mpr
    nlinarith [combined_variance_decomposition P h1 h0 z hz]
  rw [ols_pooled_formula P (by omega) (by omega)]
  unfold fisherVariance
  rw [hsvar]
  constructor <;> field_simp <;> ring

/-- L5: complete-randomization unbiasedness of tau-hat and Neyman's exact
variance identity, used by the p. 347 limit bound. -/
theorem neyman_randomization_identity (P : Population)
    (h1 : 0 < P.n1) (h0 : 0 < P.n0) :
    randomizationMean P (estimate P) = averageEffect P ∧
    randomizationVariance P (estimate P) =
      populationVariance P P.Y1/P.n1 + populationVariance P P.Y0/P.n0 -
        populationVariance P (unitEffects P)/P.size := by
  exact ⟨difference_in_means_unbiased P h1 h0, difference_in_means_variance P h1 h0⟩

/-- L6: the arm sample variances are unbiased and Neyman's variance estimate
is conservative in expectation; finite basis for the Section 3 comparisons. 
Auxiliary component of Section 2, p. 347, unnumbered Fisher/OLS variance comparisons. -/
theorem arm_variances_unbiased (P : Population) (h1 : 2 ≤ P.n1) (h0 : 2 ≤ P.n0) :
    randomizationMean P (fun z => sampleVariance z (observed P z)) = populationVariance P P.Y1 ∧
    randomizationMean P (fun z => sampleVariance zᶜ (observed P z)) = populationVariance P P.Y0 ∧
    randomizationMean P (neymanVariance P) =
      populationVariance P P.Y1/P.n1 + populationVariance P P.Y0/P.n0 ∧
    randomizationVariance P (estimate P) ≤ randomizationMean P (neymanVariance P) := by
  have hs1 : randomizationMean P (fun z => sampleVariance z (observed P z)) =
      populationVariance P P.Y1 := by
    simp_rw [treated_variance_observed]
    exact treated_sample_variance_unbiased P h1 (by omega) P.Y1
  have hs0 : randomizationMean P (fun z => sampleVariance zᶜ (observed P z)) =
      populationVariance P P.Y0 := by
    simp_rw [control_variance_observed]
    exact control_sample_variance_unbiased P (by omega) h0 P.Y0
  have hn : randomizationMean P (neymanVariance P) =
      populationVariance P P.Y1/P.n1+populationVariance P P.Y0/P.n0 := by
    unfold neymanVariance
    rw [randomizationMean_add, randomizationMean_div, randomizationMean_div, hs1, hs0]
  refine ⟨hs1, hs0, hn, ?_⟩
  rw [difference_in_means_variance P (by omega) (by omega), hn]
  exact sub_le_self _ (div_nonneg
    (populationVariance_nonnegative P (by dsimp [Population.size]; omega) (unitEffects P))
    (by positivity))

/-- L7: constant effects imply equal potential-outcome variances, zero
effect variance, and unbiased pooled OLS variance; Section 3, pp. 347–348. -/
theorem constant_effect_finite (P : Population) (h1 : 2 ≤ P.n1) (h0 : 2 ≤ P.n0)
    (hc : ConstantEffects P) :
    populationVariance P P.Y1 = populationVariance P P.Y0 ∧
    populationVariance P (unitEffects P) = 0 ∧
    randomizationVariance P (estimate P) =
      populationVariance P P.Y0 * (1/(P.n1 : ℝ)+1/(P.n0 : ℝ)) ∧
    randomizationMean P (residualSS P) = ((P.size : ℝ)-2)*populationVariance P P.Y0 ∧
    randomizationMean P (olsVariance P) = randomizationVariance P (estimate P) := by
  obtain ⟨hv, ht⟩ := constant_effect_variances P hc
  have hactual : randomizationVariance P (estimate P) =
      populationVariance P P.Y0*(1/(P.n1 : ℝ)+1/(P.n0 : ℝ)) := by
    rw [difference_in_means_variance P (by omega) (by omega), hv, ht]
    ring
  obtain ⟨hs1, hs0, _, _⟩ := arm_variances_unbiased P h1 h0
  have hss : randomizationMean P (residualSS P) =
      ((P.size : ℝ)-2)*populationVariance P P.Y0 := by
    rw [randomizationMean_congr P _ _ (residualSS_sample_variances P h1 h0),
      randomizationMean_add, randomizationMean_mul, randomizationMean_mul, hs1, hs0, hv]
    simp only [Population.size, Nat.cast_add]
    ring
  have hNm2 : (P.size : ℝ)-2 ≠ 0 := by
    have hh1 : (2 : ℝ) ≤ P.n1 := by exact_mod_cast h1
    have hh0 : (2 : ℝ) ≤ P.n0 := by exact_mod_cast h0
    simp only [Population.size, Nat.cast_add]
    linarith
  refine ⟨hv, ht, hactual, hss, ?_⟩
  unfold olsVariance
  rw [show (fun z => residualSS P z/((P.size : ℝ)-2)*(1/(P.n1 : ℝ)+1/(P.n0 : ℝ))) =
      (fun z => (1/(P.n1 : ℝ)+1/(P.n0 : ℝ))*(residualSS P z/((P.size : ℝ)-2))) by
        funext z; ring,
    randomizationMean_mul, randomizationMean_div, hss, hactual]
  field_simp <;> ring


/-- Sample means agree when the outcome vectors agree at every sampled unit. 
Auxiliary component of Section 2, pp. 346–347, constant-effect and Wald-reference comparisons. -/
theorem sampleMean_congr {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (y w : ι → ℝ) (h : ∀ i ∈ s, y i=w i) : sampleMean s y=sampleMean s w := by
  unfold sampleMean
  rw [Finset.sum_congr rfl h]

/-- Centered sums of squares depend only on sampled outcomes. 
Auxiliary component of Section 2, pp. 346–347, constant-effect and Wald-reference comparisons. -/
theorem centeredSS_congr {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (y w : ι → ℝ) (h : ∀ i ∈ s, y i=w i) : centeredSS s y=centeredSS s w := by
  unfold centeredSS
  rw [sampleMean_congr s y w h]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i hi]

/-- Shifting all outcomes by a constant leaves centered sums of squares
unchanged; this exact observation supports the imputation claim on p. 346. -/
theorem centeredSS_add_constant {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (y : ι → ℝ) (c : ℝ) :
    centeredSS s (fun i => y i+c)=centeredSS s y := by
  by_cases hs : s.card=0
  · have he : s=∅ := Finset.card_eq_zero.mp hs
    simp [he, centeredSS]
  · unfold centeredSS
    rw [sampleMean_add_constant s y c hs]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    ring

/-- L1 for any fixed real vector, obtained by making both potential outcomes
that vector; this is the decomposition needed for the imputed reference. 
Auxiliary component of Section 2, pp. 346–347, constant-effect and Wald-reference comparisons. -/
theorem fixed_outcome_decomposition (P : Population) (h1 : 2 ≤ P.n1) (h0 : 2 ≤ P.n0)
    (z : Finset (Fin P.size)) (hz : z ∈ support P.n1) (y : Fin P.size → ℝ) :
    ((P.size : ℝ)-1)*populationVariance P y =
      centeredSS z y+centeredSS zᶜ y+
        ((P.n1 : ℝ)*P.n0/P.size)*(difference P z y)^2 := by
  let Q : Population := ⟨P.n1,P.n0,y,y⟩
  have hh := combined_variance_decomposition Q h1 h0 z hz
  have hob : observed Q z=y := by
    funext i
    simp [observed,Q]
  unfold residualSS estimate at hh
  rw [hob] at hh
  simpa only [Q, Population.size, Nat.cast_add, populationVariance, difference] using hh

/-- L8's imputed control outcomes r_i=y_i−t*z_i, with t=D(z,y), have
population variance SSR_y/(N−1). Equal imputed arm means make the between-arm
term vanish; no equality with the N−2 OLS divisor is asserted. 
Auxiliary component of Section 2, pp. 346–347, constant-effect and Wald-reference comparisons. -/
theorem imputation_population_variance (P : Population) (h1 : 2 ≤ P.n1) (h0 : 2 ≤ P.n0)
    (z : Finset (Fin P.size)) (hz : z ∈ support P.n1) (y : Fin P.size → ℝ) :
    populationVariance P (fun i => y i-difference P z y*(if i ∈ z then 1 else 0)) =
      (centeredSS z y+centeredSS zᶜ y)/((P.size : ℝ)-1) := by
  let t := difference P z y
  let r := fun i => y i-t*(if i ∈ z then 1 else 0)
  obtain ⟨hc1,hc0⟩ := arm_cards P z hz
  have hp : ∀ i ∈ z, r i=y i+(-t) := by intro i hi; simp [r,hi,sub_eq_add_neg]
  have hq : ∀ i ∈ zᶜ, r i=y i := by intro i hi; simp [r,Finset.mem_compl.mp hi]
  have hm1 : sampleMean z r=sampleMean z y-t := by
    rw [sampleMean_congr z r _ hp, sampleMean_add_constant z y (-t) (by omega)]
    ring
  have hm0 : sampleMean zᶜ r=sampleMean zᶜ y := sampleMean_congr _ _ _ hq
  have hD : difference P z r=0 := by
    unfold difference
    rw [hm1,hm0]
    dsimp [t,difference]
    ring
  have hSS1 : centeredSS z r=centeredSS z y := by
    rw [centeredSS_congr z r _ hp, centeredSS_add_constant]
  have hSS0 : centeredSS zᶜ r=centeredSS zᶜ y := centeredSS_congr _ _ _ hq
  have hN1 : (P.size : ℝ)-1 ≠ 0 := by
    have hh1 : (2 : ℝ) ≤ P.n1 := by exact_mod_cast h1
    have hh0 : (2 : ℝ) ≤ P.n0 := by exact_mod_cast h0
    simp only [Population.size,Nat.cast_add]
    linarith
  have hh := fixed_outcome_decomposition P h1 h0 z hz r
  rw [hD,hSS1,hSS0] at hh
  norm_num at hh
  change populationVariance P r = _
  apply (eq_div_iff hN1).mpr
  simp only [Population.size,Nat.cast_add] at hh ⊢
  nlinarith [hh]

/-- L8, p. 346: imputing a constant effect t=tau-hat,
the fresh randomization statistic has mean t and variance
N*SSR/(N1*N0*(N−1))=(N−2)/(N−1)*V-hat(OLS). Equality with OLS is asymptotic. -/
theorem imputed_reference_variance (P : Population) (h1 : 2 ≤ P.n1) (h0 : 2 ≤ P.n0)
    (z : Finset (Fin P.size)) (hz : z ∈ support P.n1) :
    let t := estimate P z
    let r := fun i => observed P z i - t * (if i ∈ z then 1 else 0)
    randomizationMean P (fun w => t + difference P w r) = t ∧
    randomizationVariance P (fun w => t + difference P w r) =
      (P.size : ℝ)*residualSS P z/((P.n1 : ℝ)*P.n0*((P.size : ℝ)-1)) ∧
    randomizationVariance P (fun w => t + difference P w r) =
      (((P.size : ℝ)-2)/((P.size : ℝ)-1))*olsVariance P z := by
  dsimp only
  let t := estimate P z
  let r := fun i => observed P z i-t*(if i ∈ z then 1 else 0)
  have hS : populationVariance P r=residualSS P z/((P.size : ℝ)-1) := by
    exact imputation_population_variance P h1 h0 z hz (observed P z)
  have hMean : randomizationMean P (fun w => t+difference P w r)=t := by
    rw [randomizationMean_add, randomizationMean_constant,
      reference_difference_mean P (by omega) (by omega)]
    ring
  have hVar : randomizationVariance P (fun w => t+difference P w r)=
      (P.size : ℝ)*residualSS P z/((P.n1 : ℝ)*P.n0*((P.size : ℝ)-1)) := by
    have he : (fun w => t+difference P w r)=(fun w => difference P w r-(-t)) := by
      funext w
      ring
    rw [he, randomizationVariance_sub_constant,
      reference_difference_variance P (by omega) (by omega), hS]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  refine ⟨hMean, hVar, ?_⟩
  rw [hVar, ols_pooled_formula P (by omega) (by omega)]
  have hNm2 : (P.size : ℝ)-2 ≠ 0 := by
    have hh1 : (2 : ℝ) ≤ P.n1 := by exact_mod_cast h1
    have hh0 : (2 : ℝ) ≤ P.n0 := by exact_mod_cast h0
    simp only [Population.size, Nat.cast_add]
    linarith
  field_simp <;> ring

/-- L9's deterministic first identity: the two Wald leading forms differ
by (S1²−S0²)(1/N0−1/N1); pp. 347–348. -/
theorem wald_leading_difference (n1 n0 u v : ℝ) :
    (u/n0+v/n1)-(u/n1+v/n0) = (u-v)*(1/n0-1/n1) := by ring

/-- L9's exact zero criterion, with positive arm sizes: equal Wald leading
forms iff equal variances or a balanced design (p. 347 necessary condition). -/
theorem wald_leading_zero_iff (n1 n0 u v : ℝ) (h1 : 0 < n1) (h0 : 0 < n0) :
    (u/n0+v/n1)-(u/n1+v/n0) = 0 ↔ u=v ∨ n1=n0 := by
  rw [wald_leading_difference, mul_eq_zero, sub_eq_zero]
  have hi : 1/n0 - 1/n1 = 0 ↔ n1=n0 := by
    constructor
    · intro h
      field_simp at h
      linarith
    · rintro rfl
      ring
  rw [hi]

/-- L9's exact algebra for arbitrary arm sample variances, the finite
coefficient responsible for the Section 3 OLS–Neyman difference. 
Auxiliary component of Section 3, p. 347, unnumbered OLS/Neyman comparison. -/
theorem pooled_minus_unpooled (n1 n0 u v : ℝ) (h1 : 2 ≤ n1) (h0 : 2 ≤ n0) :
    (((n1-1)*u+(n0-1)*v)/(n1+n0-2))*(1/n1+1/n0) - (u/n1+v/n0) =
      ((n1+n0-1)/(n1+n0-2))*(1/n0-1/n1)*(u-v) := by
  have ha : n1 ≠ 0 := by linarith
  have hb : n0 ≠ 0 := by linarith
  have hab : n1+n0-2 ≠ 0 := by linarith
  field_simp <;> ring

/-- L9 for the actual observations: the exact OLS–Neyman difference under
every complete-randomization assignment; Section 3, p. 347. -/
theorem ols_neyman_exact (P : Population) (h1 : 2 ≤ P.n1) (h0 : 2 ≤ P.n0)
    (z : Finset (Fin P.size)) (hz : z ∈ support P.n1) :
    olsVariance P z - neymanVariance P z =
      (((P.size : ℝ)-1)/((P.size : ℝ)-2)) * (1/(P.n0 : ℝ)-1/(P.n1 : ℝ)) *
        (sampleVariance z (observed P z)-sampleVariance zᶜ (observed P z)) := by
  unfold olsVariance neymanVariance
  rw [residualSS_sample_variances P h1 h0 z hz]
  have hh1 : (2 : ℝ) ≤ P.n1 := by exact_mod_cast h1
  have hh0 : (2 : ℝ) ≤ P.n0 := by exact_mod_cast h0
  simpa only [Population.size, Nat.cast_add] using
    (pooled_minus_unpooled (P.n1 : ℝ) (P.n0 : ℝ)
      (sampleVariance z (observed P z)) (sampleVariance zᶜ (observed P z)) hh1 hh0)

/-- Asymptotic allocation, variance-limit and moment assumptions.
Populations are indexed by k with N_k→∞, allowing subsequences such as N=10m.
Initial small populations are unrestricted; both arms eventually have ≥2 units.
The bounded fourth-moment assumption bounds both marginal fourth moments
uniformly, and therefore also their fourth cross moments. -/
structure Regularity (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ) : Prop where
  size_diverges : Tendsto (fun k => (E k).size) atTop atTop
  arm_sizes : ∀ᶠ k in atTop, 2 ≤ (E k).n1 ∧ 2 ≤ (E k).n0
  p_positive : 0 < p
  p_less_one : p < 1
  allocation : Tendsto (fun k => ((E k).n1 : ℝ)/(E k).size) atTop (nhds p)
  variance1 : Tendsto (fun k => populationVariance (E k) (E k).Y1) atTop (nhds v1)
  variance0 : Tendsto (fun k => populationVariance (E k) (E k).Y0) atTop (nhds v0)
  varianceEffect : Tendsto (fun k => populationVariance (E k) (unitEffects (E k))) atTop (nhds vt)
  average_effect : Tendsto (fun k => averageEffect (E k)) atTop (nhds tauInf)
  fourth_moments : ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ,
    (∑ i : Fin ((E k).n1+(E k).n0), (((E k).Y1 i)^4 + ((E k).Y0 i)^4)) /
      ((E k).size : ℝ) ≤ B

/-- Convergence in probability on the varying, genuine finite randomization
spaces: P(|X_k−c|>epsilon)→0 for every epsilon>0. -/
def InProbability (E : ℕ → Population)
    (X : (k : ℕ) → Finset (Fin (E k).size) → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun k => randomizationProbability (E k) (fun z => ε < |X k z-c|)) atTop (nhds 0)

/-- X=o_p(N^{-1}) means N*X converges to zero in probability (p. 347).
The normalization uses the population size, not the sequence index. -/
def LittleOInvSize (E : ℕ → Population)
    (X : (k : ℕ) → Finset (Fin (E k).size) → ℝ) : Prop :=
  InProbability E (fun k z => ((E k).size : ℝ)*X k z) 0

/-- The probability limit of N*V-hat(Neyman), pp. 347–348. Inputs are
variance limits v1=sigma1² and v0=sigma0², not standard deviations. -/
def neymanLimit (p v1 v0 : ℝ) : ℝ := v1/p + v0/(1-p)

/-- The probability limit of N*V-hat(OLS), pp. 347–348. -/
def olsLimit (p v1 v0 : ℝ) : ℝ := v1/(1-p) + v0/p

/-- T7(c)'s purely algebraic difference between the two scaled limits,
with no sampling theorem assumed (p. 347). -/
theorem wald_limit_identity (p v1 v0 : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    olsLimit p v1 v0-neymanLimit p v1 v0 = ((v1-v0)*(2*p-1))/(p*(1-p)) := by
  have ha : p ≠ 0 := ne_of_gt hp
  have hb : 1-p ≠ 0 := by linarith
  unfold olsLimit neymanLimit
  field_simp <;> ring

/-- T7(c)'s necessary conditions: unequal scaled limits require unequal
potential-outcome variance limits and an unbalanced allocation (p. 347).
For nonnegative standard deviations this also implies sigma1≠sigma0. -/
theorem unequal_wald_limits_necessary (p v1 v0 : ℝ)
    (h : olsLimit p v1 v0 ≠ neymanLimit p v1 v0) : v1 ≠ v0 ∧ p ≠ 1/2 := by
  constructor
  · rintro rfl
    apply h
    unfold olsLimit neymanLimit
    ring
  · rintro rfl
    apply h
    norm_num [olsLimit, neymanLimit] <;> ring

/-- L10's numeric comparison of limiting coefficients: the stated witness
has actual leading coefficient 81/4, OLS 10, and Neyman 85/4. This arithmetic
certificate is separate from the population and randomization assertions. 
Auxiliary component of Section 3, pp. 347–348, Neyman bound and constant/heterogeneous effects. -/
theorem witness_limit_numbers :
    olsLimit (1/5) 4 1=10 ∧ neymanLimit (1/5) 4 1=85/4 ∧
      (10 : ℝ) < 81/4 ∧ (81/4 : ℝ) < 85/4 := by
  norm_num [olsLimit, neymanLimit]


/-- Standard normal CDF, for the asymptotic Wald reference law in T6(c).
This is Mathlib's nondegenerate Gaussian probability measure of variance 1. -/
def standardNormalCDF (t : ℝ) : ℝ :=
  ((ProbabilityTheory.gaussianReal 0 1) (Set.Iic t)).toReal

/-- The upper standard-normal quantile z_{1−alpha/2}, T6(c). -/
def normalCritical (α : ℝ) : ℝ := sInf {t : ℝ | 1-α/2 ≤ standardNormalCDF t}

/-- Deterministic part of T8(a), pp. 347–348: the genuine scaled
randomization variance converges to S1²/p+S0²/(1−p)−S_tau² and is bounded by
Neyman's leading limit. This needs no variance-estimator consistency theorem. -/
theorem actual_variance_limit_bound (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ)
    (h : Regularity E p v1 v0 vt tauInf) :
    Tendsto (fun k => ((E k).size : ℝ)*randomizationVariance (E k) (estimate (E k)))
      atTop (nhds (neymanLimit p v1 v0-vt)) ∧
    neymanLimit p v1 v0-vt ≤ neymanLimit p v1 v0 := by
  have hp : p ≠ 0 := ne_of_gt h.p_positive
  have hp0 : 1-p ≠ 0 := by linarith [h.p_less_one]
  have halloc0 : Tendsto (fun k => ((E k).n0 : ℝ)/(E k).size) atTop (nhds (1-p)) := by
    apply (tendsto_const_nhds.sub h.allocation).congr'
    filter_upwards [h.arm_sizes] with k hk
    have hN : ((E k).size : ℝ) ≠ 0 := by
      have hh : 4 ≤ (E k).size := by dsimp [Population.size]; omega
      exact_mod_cast (by omega : (E k).size ≠ 0)
    simp only [Population.size,Nat.cast_add] at hN ⊢
    field_simp <;> ring
  have hlim := ((h.variance1.div h.allocation hp).add
    (h.variance0.div halloc0 hp0)).sub h.varianceEffect
  have hl : Tendsto (fun k => ((E k).size : ℝ)*
      randomizationVariance (E k) (estimate (E k)))
      atTop (nhds (neymanLimit p v1 v0-vt)) := by
    apply hlim.congr'
    filter_upwards [h.arm_sizes] with k hk
    have ha : ((E k).n1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : (E k).n1 ≠ 0)
    have hb : ((E k).n0 : ℝ) ≠ 0 := by exact_mod_cast (by omega : (E k).n0 ≠ 0)
    have hN : ((E k).size : ℝ) ≠ 0 := by
      exact_mod_cast (by dsimp [Population.size]; omega : (E k).size ≠ 0)
    dsimp only [Pi.div_apply]
    rw [difference_in_means_variance (E k) (by omega) (by omega)]
    field_simp <;> ring
  have hvt : 0 ≤ vt := by
    apply ge_of_tendsto h.varianceEffect
    filter_upwards [h.arm_sizes] with k hk
    exact populationVariance_nonnegative (E k)
      (by dsimp [Population.size]; omega) (unitEffects (E k))
  exact ⟨hl,sub_le_self _ hvt⟩

/-- Deterministic part of T8(b), pp. 347–348: constant effects force equal
variance limits and zero effect-variance limit, and the actual scaled
variance tends to the common Neyman/OLS leading coefficient. -/
theorem constant_effect_deterministic_limits (E : ℕ → Population)
    (p v1 v0 vt tauInf : ℝ) (h : Regularity E p v1 v0 vt tauInf)
    (hc : ∀ k, ConstantEffects (E k)) :
    (∀ k, populationVariance (E k) (E k).Y1=populationVariance (E k) (E k).Y0 ∧
      populationVariance (E k) (unitEffects (E k))=0) ∧
    v1=v0 ∧ vt=0 ∧
    Tendsto (fun k => ((E k).size : ℝ)*randomizationVariance (E k) (estimate (E k)))
      atTop (nhds (neymanLimit p v1 v0)) ∧ neymanLimit p v1 v0=olsLimit p v1 v0 := by
  have hfinite : ∀ k, populationVariance (E k) (E k).Y1=populationVariance (E k) (E k).Y0 ∧
      populationVariance (E k) (unitEffects (E k))=0 := by
    intro k
    exact constant_effect_variances (E k) (hc k)
  have hv : v1=v0 := tendsto_nhds_unique_of_forall h.variance1 h.variance0
    (fun k => (hfinite k).1)
  have ht : vt=0 := tendsto_nhds_unique_of_forall h.varianceEffect tendsto_const_nhds
    (fun k => (hfinite k).2)
  refine ⟨hfinite,hv,ht,?_,?_⟩
  · simpa only [ht,sub_zero] using (actual_variance_limit_bound E p v1 v0 vt tauInf h).1
  · rw [hv]
    unfold neymanLimit olsLimit
    ring

/-- T8(c)'s explicit population witness:
N=10m, N1=2m, N0=8m, half Y0=1 and half Y0=−1, Y1=2Y0.
Index k uses m=k+1, avoiding the empty population. -/
def heterogeneousWitness (k : ℕ) : Population where
  n1 := 2*(k+1)
  n0 := 8*(k+1)
  Y0 := fun i => if i.val < 5*(k+1) then 1 else -1
  Y1 := fun i => 2*(if i.val < 5*(k+1) then 1 else -1)


/-- Half the witness outcomes are +1 and half −1, so their population mean
is zero and their N−1-divisor variance is N/(N−1) (T8(c), L10). This proves
the moment assertions by counting units, without enumerating assignments. 
Auxiliary component of Section 3, pp. 347–348, Neyman bound and constant/heterogeneous effects. -/
theorem witness_potential_moments (k : ℕ) :
    let P := heterogeneousWitness k
    populationMean P P.Y0=0 ∧ populationMean P P.Y1=0 ∧
    averageEffect P=0 ∧
    populationVariance P P.Y0=(P.size : ℝ)/((P.size : ℝ)-1) ∧
    populationVariance P P.Y1=4*(P.size : ℝ)/((P.size : ℝ)-1) ∧
    populationVariance P (unitEffects P)=(P.size : ℝ)/((P.size : ℝ)-1) := by
  let P := heterogeneousWitness k
  have hsize : P.size=10*(k+1) := by dsimp [P,heterogeneousWitness,Population.size]; omega
  have hpos : (Finset.univ.filter (fun i : Fin P.size => i.val < 5*(k+1))).card=5*(k+1) := by
    rw [Fin.card_filter_val_lt, hsize]
    omega
  have hneg : (Finset.univ.filter (fun i : Fin P.size => ¬ i.val < 5*(k+1))).card=5*(k+1) := by
    have hh := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (p := fun i : Fin P.size => i.val < 5*(k+1))
    rw [hpos] at hh
    simp only [Finset.card_univ,Fintype.card_fin,hsize] at hh
    omega
  have hsum : (∑ i : Fin P.size, P.Y0 i)=0 := by
    change (∑ i : Fin P.size, if i.val < 5*(k+1) then (1 : ℝ) else -1)=0
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, hpos, hneg]
    ring
  have hm0 : populationMean P P.Y0=0 := by
    unfold populationMean sampleMean
    rw [hsum]
    simp
  have hm1 : populationMean P P.Y1=0 := by
    have hh : populationMean P P.Y1=2*populationMean P P.Y0 := by
      change sampleMean Finset.univ (fun i => 2*P.Y0 i)=2*sampleMean Finset.univ P.Y0
      simpa using sampleMean_linear Finset.univ P.Y0 P.Y0 2 0
    rw [hh,hm0]
    ring
  have hSS : centeredSS Finset.univ P.Y0=(P.size : ℝ) := by
    unfold centeredSS
    change (∑ i : Fin P.size, (P.Y0 i-populationMean P P.Y0)^2)=(P.size : ℝ)
    rw [hm0]
    have hh : ∀ i : Fin P.size, (P.Y0 i)^2=1 := by
      intro i
      dsimp [P,heterogeneousWitness]
      split_ifs <;> norm_num
    simp only [sub_zero,hh,Finset.sum_const,nsmul_eq_mul,
      Finset.card_univ,Fintype.card_fin,mul_one]
  have hv0 : populationVariance P P.Y0=(P.size : ℝ)/((P.size : ℝ)-1) := by
    unfold populationVariance sampleVariance
    rw [hSS]
    simp only [Finset.card_univ,Fintype.card_fin]
  have hv1 : populationVariance P P.Y1=4*(P.size : ℝ)/((P.size : ℝ)-1) := by
    change sampleVariance Finset.univ (fun i => 2*P.Y0 i)=_
    rw [sampleVariance_scale]
    change (2 : ℝ)^2*populationVariance P P.Y0=_
    rw [hv0]
    ring
  have hEffects : unitEffects P=P.Y0 := by
    funext i
    change 2*P.Y0 i-P.Y0 i=P.Y0 i
    ring
  refine ⟨hm0,hm1,?_,hv0,hv1,?_⟩
  · unfold averageEffect
    rw [hm1,hm0]
    ring
  · rw [hEffects,hv0]

/-- L10, each fixed m=k+1: the actual witness has Neyman's null tau=0,
variances 4N/(N−1), N/(N−1), N/(N−1), and randomization variance
81/(4(N−1)) greater than the OLS leading form 10/(N−1). 
Auxiliary component of Section 3, pp. 347–348, Neyman bound and constant/heterogeneous effects. -/
theorem heterogeneous_witness_finite (k : ℕ) :
    let P := heterogeneousWitness k
    averageEffect P = 0 ∧
    populationVariance P P.Y0 = (P.size : ℝ)/((P.size : ℝ)-1) ∧
    populationVariance P P.Y1 = 4*(P.size : ℝ)/((P.size : ℝ)-1) ∧
    populationVariance P (unitEffects P) = (P.size : ℝ)/((P.size : ℝ)-1) ∧
    randomizationVariance P (estimate P) = 81/(4*((P.size : ℝ)-1)) ∧
    populationVariance P P.Y1/P.n0+populationVariance P P.Y0/P.n1 = 10/((P.size : ℝ)-1) ∧
    populationVariance P P.Y1/P.n1+populationVariance P P.Y0/P.n0 = 85/(4*((P.size : ℝ)-1)) ∧
    10/((P.size : ℝ)-1) < randomizationVariance P (estimate P) := by
  let P := heterogeneousWitness k
  obtain ⟨hm0,hm1,ht,hv0,hv1,hvt⟩ := witness_potential_moments k
  have ha : 0 < P.n1 := by dsimp [P,heterogeneousWitness]; omega
  have hb : 0 < P.n0 := by dsimp [P,heterogeneousWitness]; omega
  have hactual : randomizationVariance P (estimate P)=81/(4*((P.size : ℝ)-1)) := by
    rw [difference_in_means_variance P ha hb,hv0,hv1,hvt]
    dsimp [P,heterogeneousWitness,Population.size]
    push_cast
    have hm : (k : ℝ)+1 ≠ 0 := by positivity
    field_simp <;> ring
  have hOLS : populationVariance P P.Y1/P.n0+populationVariance P P.Y0/P.n1 =
      10/((P.size : ℝ)-1) := by
    rw [hv1,hv0]
    dsimp [P,heterogeneousWitness,Population.size]
    push_cast
    have hm : (k : ℝ)+1 ≠ 0 := by positivity
    field_simp <;> ring
  have hNeyman : populationVariance P P.Y1/P.n1+populationVariance P P.Y0/P.n0 =
      85/(4*((P.size : ℝ)-1)) := by
    rw [hv1,hv0]
    dsimp [P,heterogeneousWitness,Population.size]
    push_cast
    have hm : (k : ℝ)+1 ≠ 0 := by positivity
    field_simp <;> ring
  refine ⟨ht,hv0,hv1,hvt,hactual,hOLS,hNeyman,?_⟩
  rw [hactual]
  have hd : 0 < (P.size : ℝ)-1 := by
    dsimp [P,heterogeneousWitness,Population.size]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have he : (81 : ℝ)/(4*((P.size : ℝ)-1))=(81/4)/((P.size : ℝ)-1) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]
  exact (div_lt_div_iff_of_pos_right hd).mpr (by norm_num)


/-- The explicit T8(c) witness sizes N=10(k+1) diverge. 
Auxiliary component of Section 3, pp. 347–348, Neyman bound and constant/heterogeneous effects. -/
theorem witness_size_diverges : Tendsto (fun k => (heterogeneousWitness k).size) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  rw [Filter.eventually_atTop]
  refine ⟨b,?_⟩
  intro k hk
  dsimp [heterogeneousWitness,Population.size]
  omega

/-- The witness's finite-population variance base N/(N−1) tends to one;
T8(c) needs this ordinary limit in addition to the finite moment certificate. 
Auxiliary component of Section 3, pp. 347–348, Neyman bound and constant/heterogeneous effects. -/
theorem witness_variance_base_limit :
    Tendsto (fun k => ((heterogeneousWitness k).size : ℝ)/
      (((heterogeneousWitness k).size : ℝ)-1)) atTop (nhds 1) := by
  have hN : Tendsto (fun k => ((heterogeneousWitness k).size : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp witness_size_diverges
  have hm : Tendsto (fun k => ((heterogeneousWitness k).size : ℝ)-1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hN
  have hi := tendsto_inv_atTop_zero.comp hm
  have hh : Tendsto (fun k => (1 : ℝ)+(((heterogeneousWitness k).size : ℝ)-1)⁻¹)
      atTop (nhds 1) := by simpa using tendsto_const_nhds.add hi
  apply hh.congr
  intro k
  have hden : ((heterogeneousWitness k).size : ℝ)-1 ≠ 0 := by
    dsimp [heterogeneousWitness,Population.size]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  field_simp <;> ring

/-- The T8(c) witness's fourth moments are uniformly bounded: the average
of Y1^4+Y0^4 is exactly 17. Thus the finite example satisfies the standing
moment condition for its entire diverging sequence, not just one population. 
Auxiliary component of Section 3, pp. 347–348, Neyman bound and constant/heterogeneous effects. -/
theorem witness_fourth_moments (k : ℕ) :
    (∑ i : Fin (heterogeneousWitness k).size,
      (((heterogeneousWitness k).Y1 i)^4+((heterogeneousWitness k).Y0 i)^4)) /
      ((heterogeneousWitness k).size : ℝ)=17 := by
  have hi : ∀ i : Fin (heterogeneousWitness k).size,
      ((heterogeneousWitness k).Y1 i)^4+((heterogeneousWitness k).Y0 i)^4=(17 : ℝ) := by
    intro i
    dsimp [heterogeneousWitness]
    split_ifs <;> norm_num
  simp only [hi,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]
  have hN : ((heterogeneousWitness k).size : ℝ) ≠ 0 := by
    exact_mod_cast (by dsimp [heterogeneousWitness,Population.size]; omega :
      (heterogeneousWitness k).size ≠ 0)
  field_simp

/-- The concrete heterogeneous Neyman-null sequence in T8(c) satisfies
every condition of Regularity, with p=1/5, variances (4,1,1), and tau limit 0. 
Auxiliary component of Section 3, pp. 347–348, Neyman bound and constant/heterogeneous effects. -/
theorem witness_regular : Regularity heterogeneousWitness (1/5) 4 1 1 0 := by
  have ha : ∀ k, ((heterogeneousWitness k).n1 : ℝ)/(heterogeneousWitness k).size=1/5 := by
    intro k
    dsimp [heterogeneousWitness,Population.size]
    push_cast
    have hm : (k : ℝ)+1 ≠ 0 := by positivity
    field_simp <;> ring
  refine {
    size_diverges := witness_size_diverges
    arm_sizes := Eventually.of_forall (fun k => by dsimp [heterogeneousWitness]; omega)
    p_positive := by norm_num
    p_less_one := by norm_num
    allocation := ?_
    variance1 := ?_
    variance0 := ?_
    varianceEffect := ?_
    average_effect := ?_
    fourth_moments := ?_
  }
  · simpa only [ha] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1/5 : ℝ)) atTop (nhds (1/5)))
  · have hh : Tendsto (fun k => (4 : ℝ)*((heterogeneousWitness k).size : ℝ)/
        (((heterogeneousWitness k).size : ℝ)-1)) atTop (nhds 4) := by
      simpa only [mul_one,mul_div_assoc] using witness_variance_base_limit.const_mul 4
    apply hh.congr
    intro k
    exact (witness_potential_moments k).2.2.2.2.1.symm
  · apply witness_variance_base_limit.congr
    intro k
    exact (witness_potential_moments k).2.2.2.1.symm
  · apply witness_variance_base_limit.congr
    intro k
    exact (witness_potential_moments k).2.2.2.2.2.symm
  · apply tendsto_const_nhds.congr
    intro k
    exact (witness_potential_moments k).2.2.1.symm
  · refine ⟨17,by norm_num,?_⟩
    intro k
    rw [witness_fourth_moments]

/-- For the actual complete-randomization variances of the T8(c) witness,
N*V(tau-hat) tends to 81/4, strictly above the OLS leading coefficient 10.

Auxiliary component of Section 3, pp. 347–348, Neyman bound and constant/heterogeneous effects. -/
theorem witness_actual_scaled_limit :
    Tendsto (fun k => ((heterogeneousWitness k).size : ℝ)*
      randomizationVariance (heterogeneousWitness k) (estimate (heterogeneousWitness k)))
      atTop (nhds (81/4)) ∧ (10 : ℝ)<81/4 := by
  have hh := (actual_variance_limit_bound heterogeneousWitness (1/5) 4 1 1 0 witness_regular).1
  norm_num [neymanLimit] at hh
  refine ⟨?_,by norm_num⟩
  simpa only [Population.size,Nat.cast_add] using hh

end
end AronowAudit.P053
