import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
namespace AronowAudit.P041

open scoped BigOperators

/-- "Uniformly distributed over ... sequences with m C's and m U's",
P041-T5, validator N011 "A complete exact counterexample". A finite set
records the cited ranks; ranks use zero-based Fin(2m). This is the type-sequence
law induced by a uniform permutation, conditional on any balanced assignment. -/
def balancedSequences (m : ℕ) : Finset (Finset (Fin (2*m))) :=
  Finset.univ.powersetCard m

/-- "Yᵣ(z)=1{∃s<r:zₛ=U}", P041-T5: the accelerated-schedule scrutiny
outcome, defined for all type sequences, balanced or not. An edit's own type
has no effect; scrutiny is triggered only by earlier uncited edits. -/
def scrutinyOutcome {n : ℕ} (z : Finset (Fin n)) (r : Fin n) : ℝ :=
  if ∃ s : Fin n, s < r ∧ s ∉ z then 1 else 0

/-- "D(z)=(1/m)∑C Yᵣ-(1/m)∑U Yᵣ", P041-T5: cited-minus-uncited
mean removal contrast. The same functional is used for the slow protocol
and for fixed calendar patterns. -/
def citationContrast (m : ℕ) (z : Finset (Fin (2*m)))
    (Y : Fin (2*m) → ℝ) : ℝ :=
  (∑ r ∈ z, Y r) / m - (∑ r ∈ Finset.univ \ z, Y r) / m

/-- Uniform finite expectation over the balanced type sequences, P041-T5.
Every sequence has weight 1/choose(2m,m); cardinality is checked below. -/
def balancedExpectation (m : ℕ) (f : Finset (Fin (2*m)) → ℝ) : ℝ :=
  (∑ z ∈ balancedSequences m, f z) / (balancedSequences m).card

/-- "K ... cited edits that precede the first uncited edit", P041-T5(iv).
Count ranks whose entire prefix, including themselves, is cited. -/
def leadingCited {n : ℕ} (z : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun r => ∀ s : Fin n, s ≤ r → s ∈ z)).card

/-- Finite probability of K=k under the actual balanced sequence law,
P041-T5(iv). This is a count of sequences, not an assumed binomial law. -/
def leadingCitedProbability (m k : ℕ) : ℝ :=
  ((balancedSequences m).filter (fun z => leadingCited z = k)).card /
    ((balancedSequences m).card : ℝ)

/-- P041-T5 setting: the sample space has choose(2m,m) equally weighted
type sequences and has positive cardinality. -/
theorem balanced_sequence_card (m : ℕ) :
    (balancedSequences m).card = (2*m).choose m ∧
    0 < (balancedSequences m).card := by
  rw [balancedSequences, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact ⟨rfl, Nat.choose_pos (by omega)⟩

/-- P041-T5(i): agreeing at all earlier ranks suffices for equal outcomes,
even on unbalanced sequences. Thus switching an edit's own citation status
with the other edits fixed has zero controlled direct effect. -/
theorem scrutiny_no_direct_effect {n : ℕ} (z z' : Finset (Fin n)) (r : Fin n)
    (hp : ∀ s, s < r → (s ∈ z ↔ s ∈ z')) :
    scrutinyOutcome z r = scrutinyOutcome z' r := by
  have he : (∃ s : Fin n, s < r ∧ s ∉ z) ↔ (∃ s : Fin n, s < r ∧ s ∉ z') := by
    constructor <;> rintro ⟨s, hs, hu⟩
    · exact ⟨s, hs, fun h => hu ((hp s hs).mpr h)⟩
    · exact ⟨s, hs, fun h => hu ((hp s hs).mp h)⟩
  simp only [scrutinyOutcome, he]

/-- P041-T5(ii): all outcomes under the planned slow protocol are zero,
so the contrast is zero for every order, without an assumption of balance. -/
theorem slow_schedule_zero (m : ℕ) (z : Finset (Fin (2*m))) :
    citationContrast m z (fun _ => 0) = 0 := by
  simp [citationContrast]

/-- P041-T5(iii): the six type sequences for one Study 1 block, m=2;
zero-based cited rank sets in the target's UUCC,UCUC,UCCU,CUUC,CUCU,CCUU order. -/
theorem block_two_sequences :
    balancedSequences 2 =
      {{2,3},{1,3},{1,2},{0,3},{0,2},{0,1}} := by
  decide

/-- P041-T5(iii): the explicit removal patterns in the six balanced orders. -/
theorem block_two_outcomes :
    scrutinyOutcome ({2,3} : Finset (Fin 4)) = ![0,1,1,1] ∧
    scrutinyOutcome ({1,3} : Finset (Fin 4)) = ![0,1,1,1] ∧
    scrutinyOutcome ({1,2} : Finset (Fin 4)) = ![0,1,1,1] ∧
    scrutinyOutcome ({0,3} : Finset (Fin 4)) = ![0,0,1,1] ∧
    scrutinyOutcome ({0,2} : Finset (Fin 4)) = ![0,0,1,1] ∧
    scrutinyOutcome ({0,1} : Finset (Fin 4)) = ![0,0,0,1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext r <;> fin_cases r <;>
    norm_num [scrutinyOutcome, Fin.exists_fin_succ]

/-- P041-T5(iii), the concrete counterexample: six contrasts
1/2,1/2,1/2,0,0,-1/2, uniformly averaged to 1/6 ≠ 0. Under the slow
schedule the expectation is zero. The no-direct-effect theorem applies to
all these sequences and all edits; this is not an estimate of actual bias. -/
theorem random_order_block_counterexample :
    citationContrast 2 {2,3} (scrutinyOutcome {2,3}) = 1/2 ∧
    citationContrast 2 {1,3} (scrutinyOutcome {1,3}) = 1/2 ∧
    citationContrast 2 {1,2} (scrutinyOutcome {1,2}) = 1/2 ∧
    citationContrast 2 {0,3} (scrutinyOutcome {0,3}) = 0 ∧
    citationContrast 2 {0,2} (scrutinyOutcome {0,2}) = 0 ∧
    citationContrast 2 {0,1} (scrutinyOutcome {0,1}) = -1/2 ∧
    balancedExpectation 2 (fun z => citationContrast 2 z (scrutinyOutcome z)) = 1/6 ∧
    balancedExpectation 2 (fun z => citationContrast 2 z (scrutinyOutcome z)) ≠ 0 ∧
    balancedExpectation 2 (fun z => citationContrast 2 z (fun _ => 0)) = 0 := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := block_two_outcomes
  norm_num [balancedExpectation, block_two_sequences, citationContrast,
    h1,h2,h3,h4,h5,h6, Finset.sum_insert, Finset.ext_iff, Fin.forall_fin_succ, Fin.sum_univ_succ]

/-- P041-T5(vi) / P041-T6(a), the validator's fixed calendar boundary check:
rank outcomes (0,0,1,1), independent of every treatment, give expectation zero. -/
theorem fixed_calendar_block_unbiased :
    balancedExpectation 2 (fun z => citationContrast 2 z ![0,0,1,1]) = 0 := by
  norm_num [balancedExpectation, block_two_sequences, citationContrast,
    Finset.sum_insert, Finset.ext_iff, Fin.forall_fin_succ, Fin.sum_univ_succ]

/-- The four zero-based ranks of one block, used to enumerate the independent
citation boundary in P041-T5(vii). -/
theorem univ_four : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide

/-- All sixteen fair independent citation assignments for P041-T5(vii). -/
theorem all_four_sequences :
    (Finset.univ : Finset (Fin 4)).powerset =
    {∅,{0},{1},{2},{3},{0,1},{0,2},{0,3},{1,2},{1,3},{2,3},
      {0,1,2},{0,1,3},{0,2,3},{1,2,3},{0,1,2,3}} := by decide

/-- P041-T5(vii): the Horvitz-Thompson contrast under independent fair
citation at each rank. The sample space is all 16 subsets, each with weight
1/16. The scrutiny rule has no direct effect under this design either. -/
def independentCitationExpectation : ℝ :=
  (∑ z ∈ (Finset.univ : Finset (Fin 4)).powerset,
    (∑ r : Fin 4, (if r ∈ z then (2:ℝ) else -2) * scrutinyOutcome z r) / 4) / 16

/-- P041-T5(vii): independent citation differs from fixed-count assignment;
with the same scrutiny rule its HT contrast has expectation zero. -/
theorem independent_citation_boundary : independentCitationExpectation = 0 := by
  unfold independentCitationExpectation
  rw [all_four_sequences]
  norm_num [independentCitationExpectation, scrutinyOutcome, Fin.exists_fin_succ,
    all_four_sequences, Finset.powerset_insert, Finset.sum_insert, Finset.ext_iff, Fin.forall_fin_succ, Fin.sum_univ_succ]

/-- P041-T5(iv)-(v), general m and Study 1 size m=50. This faithfully
states the counting identity on the actual balanced sample space, its expected
leading run, and the scrutiny contrasts; it is NOT yet proved. No enumeration
of choose(100,50) orders is attempted. -/
theorem balanced_scrutiny_general (m : ℕ) (hm : 1 ≤ m) :
    (∀ k ≤ m, leadingCitedProbability m k =
      (((2*m-k-1).choose (m-1) : ℝ) / ((2*m).choose m : ℝ))) ∧
    balancedExpectation m (fun z => (leadingCited z : ℝ)) = (m:ℝ)/(m+1) ∧
    (∀ z ∈ balancedSequences m,
      (∑ r ∈ z, scrutinyOutcome z r) = (m:ℝ) - leadingCited z ∧
      (∑ r ∈ Finset.univ \ z, scrutinyOutcome z r) = (m:ℝ)-1) ∧
    balancedExpectation m (fun z => (∑ r ∈ z, scrutinyOutcome z r) / m) =
      (m:ℝ)/(m+1) ∧
    balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) =
      1/((m:ℝ)*(m+1)) ∧
    0 < balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) := by
  sorry

/-- Exact 51-cell certificate for the binomial-count formula in P041-T5(v).
This avoids enumerating choose(100,50) type sequences. It certifies the
compressed formula, not the still-unproved identification with the actual K law. -/
def scrutinyCounts50 : Fin 51 → ℕ := ![50445672272782096667406248628,25477612258980856902730428600,12738806129490428451365214300,6303739115624129542943611200,3086205608690980088732809650,1494373242103000885070623620,715391445687606806682745350,338464770002738704236997800,158195490327367003067292450,73013303228015539877211900,33261615914984857055174310,14949040860667351485471600,6625143108704848953788550,2893740668169934025792700,1244981450259157662259650,527286261286231480486440,219702608869263116869350,89998659054878867151300,36218972546475641658450,14308729894903957198400,5544632834275283414380,2105556772509601296600,782835210292031251300,284667349197102273200,101131821425286333900,35059031427432595752,11844267374132633700,3894005712043605600,1243918491347262900,385439532530137800,115631859759041340,33516481089577200,9364899127970100,2515943049305400,648045936942300,159518999862720,37387265592825,8308281242850,1742058970275,342700125300,62828356305,10648873950,1652411475,231917400,28989675,3162510,292825,22100,1275,50,1]

/-- Each compressed cell is exactly choose(99-k,49), P041-T5(v). -/
theorem scrutiny_counts50_exact (k : Fin 51) :
    (99-k.val).choose 49 = scrutinyCounts50 k := by
  fin_cases k <;>
    norm_num [scrutinyCounts50, Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial, Nat.factorial]

/-- The compressed counts normalize and have first moment 50/51,
P041-T5(v), checked as small integer sufficient statistics. -/
theorem scrutiny_counts50_moments :
    (∑ k : Fin 51, scrutinyCounts50 k) = 100891344545564193334812497256 ∧
    (∑ k : Fin 51, k.val * scrutinyCounts50 k) = 98913082887808032681188722800 ∧
    (100).choose 50 = 100891344545564193334812497256 ∧
    51*98913082887808032681188722800 = 50*100891344545564193334812497256 := by
  norm_num [scrutinyCounts50, Fin.sum_univ_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]

/-- The proposed K-mass in the validator's m=50 calculation,
choose(99-k,49)/choose(100,50), P041-T5(v). Its equality to the full
permutation law is deliberately left in balanced_scrutiny_general. -/
def compressedScrutinyMass50 (k : Fin 51) : ℝ :=
  ((99-k.val).choose 49 : ℝ) / ((100).choose 50 : ℝ)

/-- P041-T5(v), the compressed finite certificate: mass 1, mean K=50/51,
and weighted accelerated contrast 1/2550. This proves the arithmetic of
the proposed law, without silently assuming its unproved counting bridge. -/
theorem compressed_scrutiny50_certificate :
    (∑ k : Fin 51, compressedScrutinyMass50 k) = 1 ∧
    (∑ k : Fin 51, (k.val:ℝ)*compressedScrutinyMass50 k) = 50/51 ∧
    (∑ k : Fin 51, ((50-(k.val:ℝ))/50-49/50)*compressedScrutinyMass50 k) = 1/2550 := by
  obtain ⟨hn,hw,hN,_⟩ := scrutiny_counts50_moments
  have rn : (∑ k : Fin 51, (scrutinyCounts50 k:ℝ)) = (100891344545564193334812497256:ℝ) := by exact_mod_cast hn
  have rwgt : (∑ k : Fin 51, (k.val:ℝ)*(scrutinyCounts50 k:ℝ)) = (98913082887808032681188722800:ℝ) := by exact_mod_cast hw
  have mass : (∑ k : Fin 51, compressedScrutinyMass50 k) = 1 := by
    unfold compressedScrutinyMass50
    simp_rw [scrutiny_counts50_exact, hN]
    rw [← Finset.sum_div, rn]
    norm_num
  have moment : (∑ k : Fin 51, (k.val:ℝ)*compressedScrutinyMass50 k) = 50/51 := by
    unfold compressedScrutinyMass50
    simp_rw [scrutiny_counts50_exact, hN, ← mul_div_assoc]
    rw [← Finset.sum_div, rwgt]
    norm_num
  refine ⟨mass,moment,?_⟩
  have ht (k : Fin 51) : ((50-(k.val:ℝ))/50-49/50)*compressedScrutinyMass50 k =
      compressedScrutinyMass50 k / 50 - ((k.val:ℝ)*compressedScrutinyMass50 k)/50 := by ring
  simp_rw [ht]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, mass, moment]
  norm_num

/-- P041-T5(v): specialization to m=50, on the full balanced sample space.
This inherits the unproved general counting result and is drafted only. -/
theorem study_one_size_scrutiny :
    balancedExpectation 50 (fun z => (leadingCited z : ℝ)) = 50/51 ∧
    balancedExpectation 50 (fun z => (∑ r ∈ z, scrutinyOutcome z r) / 50) = 50/51 ∧
    (∀ z ∈ balancedSequences 50,
      (∑ r ∈ Finset.univ \ z, scrutinyOutcome z r) / 50 = 49/50) ∧
    balancedExpectation 50 (fun z => citationContrast 50 z (scrutinyOutcome z)) = 1/2550 ∧
    balancedExpectation 50 (fun z => citationContrast 50 z (scrutinyOutcome z)) ≠ 0 := by
  obtain ⟨_,hk,hs,hc,hd,hpos⟩ := balanced_scrutiny_general 50 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ne_of_gt hpos⟩
  · norm_num at hk ⊢; exact hk
  · norm_num at hc ⊢; exact hc
  · intro z hz
    rw [(hs z hz).2]
    norm_num
  · norm_num at hd ⊢; exact hd

/-- P041-T6(a) counting lemma: exactly half the balanced assignments
cite any specified rank, because choose(2m-1,m-1) is half of choose(2m,m). -/
theorem balanced_rank_half (m : ℕ) (hm : 1 ≤ m) (r : Fin (2*m)) :
    2 * ((balancedSequences m).filter (fun z => r ∈ z)).card =
      (balancedSequences m).card := by
  have hfilter : (balancedSequences m).filter (fun z => r ∈ z) =
      (Finset.univ.powersetCard m).filter (fun z => ({r}:Finset (Fin (2*m))) ⊆ z) := by
    ext z; simp [balancedSequences]
  rw [hfilter, Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _)
    (by simpa using hm), Finset.card_univ, Fintype.card_fin, Finset.card_singleton,
    (balanced_sequence_card m).1]
  have hp := Nat.choose_succ_succ' (2*m-1) (m-1)
  have hn : 2*m-1+1 = 2*m := by omega
  have hk : m-1+1 = m := by omega
  have hs : (2*m-1).choose m = (2*m-1).choose (m-1) :=
    Nat.choose_symm_of_eq_add (by omega)
  rw [hn,hk,hs] at hp
  omega

/-- Finite algebra for P041-T6(a): write the two group means as a sum
over all ranks using their own citation status. -/
theorem contrast_as_rank_sum (m : ℕ) (z : Finset (Fin (2*m)))
    (g : Fin (2*m) → Bool → ℝ) :
    citationContrast m z (fun r => g r (decide (r ∈ z))) =
      (∑ r : Fin (2*m), if r ∈ z then g r true else -g r false) / m := by
  have hc : (∑ r ∈ z, g r (decide (r ∈ z))) = ∑ r ∈ z, g r true := by
    apply Finset.sum_congr rfl; intro r hr; simp [hr]
  have hu : (∑ r ∈ Finset.univ \ z, g r (decide (r ∈ z))) =
      ∑ r ∈ Finset.univ \ z, g r false := by
    apply Finset.sum_congr rfl; intro r hr; simp [(Finset.mem_sdiff.mp hr).2]
  have hfC : Finset.univ.filter (fun r : Fin (2*m) => r ∈ z) = z := by ext r; simp
  have hfU : Finset.univ.filter (fun r : Fin (2*m) => r ∉ z) = Finset.univ \ z := by
    ext r; simp
  unfold citationContrast
  rw [hc,hu,Finset.sum_ite,hfC,hfU,Finset.sum_neg_distrib]
  ring

/-- P041-T6(a), the corrected sufficient condition. Outcomes depend only
on rank and own citation status. The expected cited-minus-uncited contrast
equals the average direct effect over all ranks; no calendar restrictions
are imposed. This is stated for every m≥1, and is NOT yet proved. -/
theorem random_order_without_interference (m : ℕ) (hm : 1 ≤ m)
    (g : Fin (2*m) → Bool → ℝ) :
    balancedExpectation m (fun z => citationContrast m z
      (fun r => g r (decide (r ∈ z)))) =
    (∑ r : Fin (2*m), (g r true - g r false)) / (2*m) := by
  have rankSum (r : Fin (2*m)) :
      (∑ z ∈ balancedSequences m, if r ∈ z then g r true else -g r false) =
      ((balancedSequences m).card : ℝ)/2 * (g r true-g r false) := by
    have hh := balanced_rank_half m hm r
    have hc := Finset.card_filter_add_card_filter_not (s := balancedSequences m) (p := fun z => r ∈ z)
    have he : ((balancedSequences m).filter (fun z => r ∉ z)).card =
        ((balancedSequences m).filter (fun z => r ∈ z)).card := by omega
    have hcast : (2:ℝ) * (((balancedSequences m).filter (fun z => r ∈ z)).card : ℝ) =
        ((balancedSequences m).card : ℝ) := by exact_mod_cast hh
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, he]
    rw [← hcast]
    ring
  unfold balancedExpectation
  simp_rw [contrast_as_rank_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [rankSum]
  rw [← Finset.mul_sum]
  have hcard : ((balancedSequences m).card : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (balanced_sequence_card m).2
  have hmass : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp

/-- P041-T6(a), the general sufficient condition for a single m=2 block.
This finite lemma leaves g entirely arbitrary and verifies the direct-effect
identity by the six orders; fixed-calendar unbiasedness follows by gC=gU. -/
theorem block_without_interference (g : Fin 4 → Bool → ℝ) :
    balancedExpectation 2 (fun z => citationContrast 2 z
      (fun r => g r (decide (r ∈ z)))) =
    (∑ r : Fin 4, (g r true - g r false)) / 4 := by
  norm_num [balancedExpectation, block_two_sequences, citationContrast,
    Finset.sum_insert, Finset.ext_iff, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  ring

/-- P041-T6(b)-(c): in the concrete scrutiny system the implemented
expectation is 1/6 and the planned expectation and every direct effect are
zero. The repaired assurance must distinguish these quantities. -/
theorem adaptive_protocol_estimands_differ :
    balancedExpectation 2 (fun z => citationContrast 2 z (scrutinyOutcome z)) = 1/6 ∧
    balancedExpectation 2 (fun z => citationContrast 2 z (fun _ => 0)) = 0 ∧
    (∀ z z' : Finset (Fin 4), ∀ r : Fin 4,
      (∀ s, s ≠ r → (s ∈ z ↔ s ∈ z')) → scrutinyOutcome z r - scrutinyOutcome z' r = 0) := by
  obtain ⟨_,_,_,_,_,_,he,_,hs⟩ := random_order_block_counterexample
  refine ⟨he, hs, ?_⟩
  intro z z' r h
  rw [scrutiny_no_direct_effect z z' r (fun s hs => h s (ne_of_lt hs))]
  ring

/-- P041-T6(b)-(c): slow-protocol expectation is zero for every m. -/
theorem slow_expectation_zero (m : ℕ) :
    balancedExpectation m (fun z => citationContrast m z (fun _ => 0)) = 0 := by
  simp [balancedExpectation, slow_schedule_zero]

/-- P041-T6(b)-(c), for all m≥1: every controlled direct effect is zero,
the planned-protocol expectation is zero and the implemented-protocol
expectation is 1/(m(m+1))>0. The last part depends on the still-drafted
general scrutiny counting theorem, so this corollary is drafted as well. -/
theorem adaptive_protocol_estimands_general (m : ℕ) (hm : 1 ≤ m) :
    (∀ z z' : Finset (Fin (2*m)), ∀ r : Fin (2*m),
      (∀ s, s ≠ r → (s ∈ z ↔ s ∈ z')) → scrutinyOutcome z r - scrutinyOutcome z' r = 0) ∧
    balancedExpectation m (fun z => citationContrast m z (fun _ => 0)) = 0 ∧
    balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) = 1/((m:ℝ)*(m+1)) ∧
    0 < balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) := by
  obtain ⟨_,_,_,_,he,hp⟩ := balanced_scrutiny_general m hm
  refine ⟨?_,slow_expectation_zero m,he,hp⟩
  intro z z' r h
  rw [scrutiny_no_direct_effect z z' r (fun s hs => h s (ne_of_lt hs))]
  ring

end AronowAudit.P041

#print axioms AronowAudit.P041.balanced_sequence_card
#print axioms AronowAudit.P041.scrutiny_no_direct_effect
#print axioms AronowAudit.P041.slow_schedule_zero
#print axioms AronowAudit.P041.block_two_sequences
#print axioms AronowAudit.P041.block_two_outcomes
#print axioms AronowAudit.P041.random_order_block_counterexample
#print axioms AronowAudit.P041.fixed_calendar_block_unbiased
#print axioms AronowAudit.P041.univ_four
#print axioms AronowAudit.P041.all_four_sequences
#print axioms AronowAudit.P041.independent_citation_boundary
#print axioms AronowAudit.P041.balanced_scrutiny_general
#print axioms AronowAudit.P041.scrutiny_counts50_exact
#print axioms AronowAudit.P041.scrutiny_counts50_moments
#print axioms AronowAudit.P041.compressed_scrutiny50_certificate
#print axioms AronowAudit.P041.study_one_size_scrutiny
#print axioms AronowAudit.P041.balanced_rank_half
#print axioms AronowAudit.P041.contrast_as_rank_sum
#print axioms AronowAudit.P041.random_order_without_interference
#print axioms AronowAudit.P041.block_without_interference
#print axioms AronowAudit.P041.adaptive_protocol_estimands_differ
#print axioms AronowAudit.P041.slow_expectation_zero
#print axioms AronowAudit.P041.adaptive_protocol_estimands_general
