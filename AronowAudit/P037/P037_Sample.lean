import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Ring.Pow
import Lean.Elab.Tactic.Omega

namespace AronowAudit.P037
open scoped BigOperators
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- SI pp. 16--17: Ω={z:p_z>0}, "Pr(Z=z)=p_z".
Here Ω is the finite support itself, so every retained state's mass is
strictly positive. This permits conclusions about every supported draw. -/
structure SupportedDesign (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  positive : ∀ z, 0 < mass z
  total : ∑ z, mass z=1

/-- SI p. 18 exposure probabilities: sum p_z I(f(z,theta_i)=d).
The same finite sum gives probabilities of selection and permutation events. -/
noncomputable def sampleProb {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (E : Ω → Prop) : ℝ :=
  ∑ z, P.mass z * (if E z then 1 else 0)

/-- Finite expectation over the support specified by the publication. -/
noncomputable def sampleMean {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (Y : Ω → ℝ) : ℝ := ∑ z, P.mass z*Y z

/-- T20, released script 4 lines 151--153:
a school's conflict outcome enters iff its recorded mean exceeds 0.02.
This threshold is not a definition supplied by the publication.
The Lean definitions specify what the published software computes. -/
def conflictIncluded (Y : ℝ) : Prop := Y>1/50

/-- T19's uniform two-of-four block (SI p. 5, Fig. S1), the six pairs. -/
def selectionPair (z : Fin 6) : Finset (Fin 4) :=
  ![{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}] z

/-- T19's fixed synthetic potential means: (0,.03,.06,.09)+.03 D.
These are exact counts out of 100 students, not values from the public data. -/
noncomputable def selectionPotential (i : Fin 4) (treated : Bool) : ℝ :=
  (3/100)*(i.val:ℝ)+(if treated then 3/100 else 0)
noncomputable def selectionOutcome (z : Fin 6) (i : Fin 4) : ℝ :=
  selectionPotential i (decide (i∈selectionPair z))
noncomputable def selectionKept (z : Fin 6) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => conflictIncluded (selectionOutcome z i))
noncomputable def selectedTreated (z : Fin 6) := selectionKept z ∩ selectionPair z
noncomputable def selectedControl (z : Fin 6) := selectionKept z \ selectionPair z
noncomputable def selectedDelta (z : Fin 6) : ℝ :=
  (∑ i ∈ selectedTreated z, selectionOutcome z i)/(selectedTreated z).card -
  (∑ i ∈ selectedControl z, selectionOutcome z i)/(selectedControl z).card
noncomputable def selectedWeight (z : Fin 6) : ℝ :=
  ((selectedTreated z).card:ℝ)*(selectedControl z).card /
    ((selectedTreated z).card+(selectedControl z).card)

/-- T19(i)--(iv), finite part of (v): every constant effect is .03,
yet exact averaging of the selected differences gives .015; the expected
block-regression numerator/denominator gives .012. All outcomes are complete. -/
theorem outcome_selection_finite_counterexample :
    (∀ i, selectionPotential i true-selectionPotential i false=3/100) ∧
    (∀ z i, i∈selectionKept z ↔ i≠0 ∨ 0∈selectionPair z) ∧
    (∀ z, (selectedTreated z).card=2 ∧
      (selectedControl z).card=(![2,2,2,1,1,1] : Fin 6 → ℕ) z) ∧
    (∀ z, selectedDelta z=(![-3/100,0,3/100,-3/200,3/100,3/40] : Fin 6 → ℝ) z) ∧
    (∀ z, selectedWeight z=(![1,1,1,2/3,2/3,2/3] : Fin 6 → ℝ) z) ∧
    (∑ z, selectedDelta z)/6=3/200 ∧ (3/200:ℝ)≠3/100 ∧
    (∑ z, selectedWeight z)/6=5/6 ∧
    (∑ z, selectedWeight z*selectedDelta z)/6=1/100 ∧
    ((1/100:ℝ)/(5/6))=3/250 ∧ (3/250:ℝ)≠3/100 := by
  have hu : (Finset.univ : Finset (Fin 4))={0,1,2,3} := by
    ext i; fin_cases i <;> simp
  have hd : ∀ z, selectedDelta z=
      (![-3/100,0,3/100,-3/200,3/100,3/40] : Fin 6 → ℝ) z := by
    intro z; fin_cases z <;>
      norm_num [selectedDelta, selectedTreated, selectedControl, selectionKept,
        conflictIncluded, selectionOutcome, selectionPotential, selectionPair, Finset.sdiff_insert, Finset.sdiff_singleton_eq_erase,
        Fin.sum_univ_succ, Finset.filter_insert, Finset.filter_singleton, hu]
  have hw : ∀ z, selectedWeight z=(![1,1,1,2/3,2/3,2/3] : Fin 6 → ℝ) z := by
    intro z; fin_cases z <;>
      norm_num [selectedWeight, selectedTreated, selectedControl, selectionKept,
        conflictIncluded, selectionOutcome, selectionPotential, selectionPair, Finset.sdiff_insert, Finset.sdiff_singleton_eq_erase,
        hu, Finset.filter_insert, Finset.filter_singleton]
  refine ⟨?_, ?_, ?_, hd, hw, ?_, by norm_num, ?_, ?_, by norm_num, by norm_num⟩
  · intro i; simp [selectionPotential]
  · intro z i; fin_cases z <;> fin_cases i <;>
      norm_num [selectionKept, conflictIncluded, selectionOutcome, selectionPotential,
        selectionPair]
  · intro z; fin_cases z <;>
      norm_num [selectedTreated, selectedControl, selectionKept, conflictIncluded,
        selectionOutcome, selectionPotential, selectionPair, hu, Finset.sdiff_insert, Finset.sdiff_singleton_eq_erase, Finset.filter_insert, Finset.filter_singleton]
  · simp_rw [hd]; norm_num [Fin.sum_univ_succ]
  · simp_rw [hw]; norm_num [Fin.sum_univ_succ]
  · simp_rw [hw, hd]; norm_num [Fin.sum_univ_succ]

/-- T19(v): actual OLS after block profiling, written as ΣwΔ/Σw.
This targets the probability limit over independent copies, not E[finite OLS]. -/
noncomputable def selectedBlockCoefficient (B : ℕ) (z : Fin B → Fin 6) : ℝ :=
  (∑ b, selectedWeight (z b)*selectedDelta (z b))/(∑ b, selectedWeight (z b))


/-- T19(v), finite block-centering identities behind the probability limit. -/
theorem selected_block_crossproducts (nT nC yT yC : ℝ)
    (ht : 0<nT) (hc : 0<nC) :
    nT*(1-nT/(nT+nC))^2+nC*(nT/(nT+nC))^2=nT*nC/(nT+nC) ∧
    (1-nT/(nT+nC))*yT-(nT/(nT+nC))*yC=
      (nT*nC/(nT+nC))*(yT/nT-yC/nC) := by
  have hn : nT+nC≠0 := by linarith
  constructor <;> field_simp <;> ring

/-- T20(a),(b), correcting the selection description
at main p. 567 and SI p. 10: for every exposure, fixed inclusion is IPW-unbiased
where that unit has positive exposure probability; the kept-population average
requires positivity only for kept units and a nonempty kept set. Arbitrary
assignment-dependent inclusion introduces its conditional inclusion factor.
The potential-outcome schedule y_i(d) and exposure type are unrestricted. -/
theorem selection_ipw_identities {Ω I K : Type*} [Fintype Ω] [Fintype I]
    [DecidableEq K] (P : SupportedDesign Ω) (D : Ω → I → K)
    (A : Ω → I → Bool) (y : I → K → ℝ) (a : I → Bool) :
    (∀ d i, 0<sampleProb P (fun z => D z i=d) →
      sampleMean P (fun z =>
        (if a i then 1 else 0)*(if D z i=d then 1 else 0)*y i d /
          sampleProb P (fun z => D z i=d))=(if a i then y i d else 0)) ∧
    (∀ d, (∀ i, a i=true → 0<sampleProb P (fun z => D z i=d)) →
      0<(Finset.univ.filter (fun i => a i=true)).card →
      sampleMean P (fun z =>
        (∑ i, (if a i then 1 else 0)*(if D z i=d then 1 else 0)*y i d /
          sampleProb P (fun z => D z i=d)) /
        (Finset.univ.filter (fun i => a i=true)).card)=
        (∑ i ∈ Finset.univ.filter (fun i => a i=true), y i d)/
          (Finset.univ.filter (fun i => a i=true)).card) ∧
    (∀ d i, 0<sampleProb P (fun z => D z i=d) →
      sampleMean P (fun z =>
        (if A z i then 1 else 0)*(if D z i=d then 1 else 0)*y i d /
          sampleProb P (fun z => D z i=d))=
        y i d*(sampleProb P (fun z => A z i=true ∧ D z i=d) /
          sampleProb P (fun z => D z i=d))) := by
  have fixed (d : K) (i : I)
      (hp : a i=true → 0<sampleProb P (fun z => D z i=d)) :
      sampleMean P (fun z =>
        (if a i then 1 else 0)*(if D z i=d then 1 else 0)*y i d /
          sampleProb P (fun z => D z i=d))=(if a i then y i d else 0) := by
    cases ha : a i with
    | false => simp [sampleMean, ha]
    | true =>
      have hn := (hp ha).ne'
      simp only [ha, Bool.true_eq, ite_true, one_mul, sampleMean]
      calc
        _ = (sampleProb P (fun z => D z i=d)*y i d) /
            sampleProb P (fun z => D z i=d) := by
          unfold sampleProb
          rw [Finset.sum_mul, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro z _
          ring
        _ = y i d := mul_div_cancel_left₀ _ hn
  refine ⟨?_, ?_, ?_⟩
  · intro d i hp
    exact fixed d i (fun _ => hp)
  · intro d hp _hna
    unfold sampleMean
    calc
      _ = (∑ i, sampleMean P (fun z =>
          (if a i then 1 else 0)*(if D z i=d then 1 else 0)*y i d /
            sampleProb P (fun z => D z i=d))) /
          (Finset.univ.filter (fun i => a i=true)).card := by
        simp only [sampleMean, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
      _ = (∑ i, if a i then y i d else 0) /
          (Finset.univ.filter (fun i => a i=true)).card := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => fixed d i (hp i))
      _ = _ := by rw [Finset.sum_filter]
  · intro d i _hp
    simp only [sampleMean, sampleProb]
    rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z _
    by_cases ha : A z i=true <;> by_cases hd : D z i=d <;>
      simp [ha, hd, Bool.eq_false_of_not_eq_true] <;> ring

/-- T20(c): lying on the same side of the code's threshold on every
supported assignment makes inclusion assignment-invariant. This includes
the sharp null but does not follow from complete reporting alone (T19). -/
theorem threshold_assignment_invariant {Ω I : Type*}
    (Y : Ω → I → ℝ)
    (h : ∀ i, (∀ z, 1/50<Y z i) ∨ (∀ z, Y z i≤1/50)) :
    ∀ z z' i, conflictIncluded (Y z i) ↔ conflictIncluded (Y z' i) := by
  intro z z' i
  rcases h i with hi | hi
  · exact iff_of_true (hi z) (hi z')
  · exact iff_of_false (not_lt_of_ge (hi z)) (not_lt_of_ge (hi z'))

/-- The seed blocks of SI p. 6: uniform m-element subsets of n eligibles.
This is a fixed-count draw without replacement, not independent Bernoulli seeds. -/
def seedChoices (n m : ℕ) : Finset (Finset (Fin n)) := Finset.univ.powersetCard m

/-- Cardinal count used by T21,T29,T30: excluding a specified set of
peers leaves choose(n-number excluded,m) uniform seed selections. -/
theorem count_avoiding_seeds (n m : ℕ) (peers : Finset (Fin n)) :
    ((seedChoices n m).filter (fun s => Disjoint s peers)).card=
      Nat.choose (n-peers.card) m := by
  have he : (seedChoices n m).filter (fun s => Disjoint s peers)=
      (Finset.univ \ peers).powersetCard m := by
    ext s
    simp only [seedChoices, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hs,hcard⟩,hd⟩
      refine ⟨?_,hcard⟩
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        fun hp => Finset.disjoint_left.mp hd hi hp⟩
    · rintro ⟨hs,hcard⟩
      refine ⟨⟨Finset.subset_univ _,hcard⟩,Finset.disjoint_left.mpr ?_⟩
      intro i hi hp
      exact (Finset.mem_sdiff.mp (hs hi)).2 hp
  rw [he, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset (Finset.subset_univ peers)]
  simp

/-- Main p. 568's four conditions, plus the direct-seed condition of SI
p. 17: indices C=0,S=1,NI=2,I=3,D=4. Self is ∅ for an ineligible student
and a singleton for an eligible student. Referent peers are a subset of peers. -/
def treatedSeedExposure {n : ℕ} (self peers refs seeds : Finset (Fin n)) : Fin 5 :=
  if ¬Disjoint seeds self then 4 else if Disjoint seeds peers then 1
  else if Disjoint seeds refs then 2 else 3

/-- Conditional seed counts are combined with the school's treatment
probability 1/2. The unaffected other seed blocks have integrated out. -/
noncomputable def localExposureProbability (n m : ℕ)
    (self peers refs : Finset (Fin n)) (k : Fin 5) : ℝ :=
  if k=0 then 1/2 else
    (((seedChoices n m).filter (fun s => treatedSeedExposure self peers refs s=k)).card:ℝ) /
      (2*(Nat.choose n m:ℝ))


/-- T22: the publication's positivity set P and the code's estimated
probability screen. k ranges over C,S,NI,I; direct seeds are the fifth label.
The Lean definitions specify what the published software computes. -/
def positivityPopulation {I : Type*} (π : I → Fin 4 → ℝ) : Set I :=
  {i | ∀ k, 0<π i k ∧ π i k<1}
def probabilityScreen {I : Type*} (π : I → Fin 4 → ℝ) (cutoff : ℝ) : Set I :=
  {i | ∀ k, cutoff<π i k}

/-- T22, released script 3 line 195: outcome-specific analysis and
prediction set M_o: estimated π>.01, realized nonseed, outcome and
preprocessed baseline available, and the conflict school screen if required.
The Lean definitions specify what the published software computes. -/
def codeAnalysisSet {Ω I : Type*} (estimated : I → Fin 4 → ℝ)
    (seed outcomeAvailable baselineAvailable schoolPasses : Ω → I → Prop)
    (z : Ω) : Set I :=
  {i | i∈probabilityScreen estimated (1/100) ∧ ¬seed z i ∧
    outcomeAvailable z i ∧ baselineAvailable z i ∧ schoolPasses z i}


/-- T22(d), finite .01 rule: with 10,000 draws, count≥101 and
the inverse estimated probability is ≤10000/101<100. -/
theorem cutoff_integer_rule (r : ℕ) (hr : r≤10000) :
    ((r:ℝ)/10000>1/100 ↔ 101≤r) ∧
    (101≤r → 1/((r:ℝ)/10000)≤10000/101 ∧ (10000/101:ℝ)<100) := by
  constructor
  · constructor <;> intro h
    · have : (100:ℝ)<r := by linarith
      exact_mod_cast this
    · have : (101:ℝ)≤r := by exact_mod_cast h
      linarith
  · intro h
    have hp : (0:ℝ)<r := by exact_mod_cast (by omega : 0<r)
    have hq : (101:ℝ)≤r := by exact_mod_cast h
    constructor
    · apply (div_le_iff₀ (by positivity : (0:ℝ)<(r:ℝ)/10000)).mpr
      nlinarith
    · norm_num

/-- T29,T30(e), blocked seed school-exposure probability for an ineligible
focal student: 1/2 times independent avoidance probabilities in every block.
For m_b≤n_b, truncation n_b-m_b is the true count of nonpeers. -/
noncomputable def blockedSchoolExposure {b : ℕ}
    (n t m : Fin b → ℕ) : ℝ :=
  (1/2)*∏ h, (Nat.choose (n h-m h) (t h):ℝ)/(Nat.choose (n h) (t h):ℝ)

/-- T29(i),(ii), T30(e): exact rational count/probability certificates.
The four patterns illustrate why total degree alone does not determine π(S). -/
theorem blocked_school_probability_examples :
    Nat.choose 10 5=252 ∧ Nat.choose 9 4=126 ∧
    (252:ℕ)^2=63504 ∧ 126*252=31752 ∧
    blockedSchoolExposure (fun _ : Fin 4 => 10) (fun _ => 5) ![2,2,2,2]=8/6561 ∧
    blockedSchoolExposure (fun _ : Fin 4 => 10) (fun _ => 5) ![5,3,0,0]=1/6048 ∧
    blockedSchoolExposure (fun _ : Fin 4 => 10) (fun _ => 5) ![6,2,0,0]=0 ∧
    blockedSchoolExposure (fun _ : Fin 4 => 10) (fun _ => 5) ![5,5,0,0]=1/127008 ∧
    (∑ k : Fin 4, (![1/2,1/127008,31751/127008,1/4] : Fin 4 → ℝ) k)=1 ∧
    (∀ k : Fin 4, 0<(![1/2,1/127008,31751/127008,1/4] : Fin 4 → ℝ) k ∧
      (![1/2,1/127008,31751/127008,1/4] : Fin 4 → ℝ) k<1) := by
  norm_num [blockedSchoolExposure, Fin.prod_univ_succ, Fin.sum_univ_succ,
    Nat.choose]; intro k; fin_cases k <;> norm_num

/-- T30(b): finite frequency resolution alone precludes error below p
when 0<p<1/(2J); the lemma needs no independence of simulated assignments. -/
theorem frequency_resolution (J r : ℕ) (hJ : 0<J) (p : ℝ)
    (hp : 0<p) (hsmall : p<1/(2*(J:ℝ))) :
    p≤ |(r:ℝ)/J-p| := by
  have hj : (0:ℝ)<J := by exact_mod_cast hJ
  have h2 : 2*(J:ℝ)*p<1 := by
    have hx := (lt_div_iff₀ (by positivity : (0:ℝ)<2*(J:ℝ))).mp hsmall
    nlinarith
  by_cases hr : r=0
  · simp [hr, abs_of_pos hp]
  · have hr1 : (1:ℝ)≤r := by exact_mod_cast (by omega : 1≤r)
    have hq : 2*p<(r:ℝ)/J := (lt_div_iff₀ hj).mpr (by nlinarith)
    rw [abs_of_pos (by linarith : 0<(r:ℝ)/J-p)]
    linarith

/-- T29(iii),(iv),(v): no possible 10,000-draw outcome estimates the rare
exposure within half its size, and its variance and relative variance have
the target's exact values. The zero-hit probability bound is separate. -/
theorem rare_exposure_frequency_counterexample :
    (∀ r : ℕ, (1/127008:ℝ)≤ |(r:ℝ)/10000-1/127008| ∧
      (1/254016:ℝ)< |(r:ℝ)/10000-1/127008|) ∧
    (10000:ℝ)/127008=625/7938 ∧
    ((1/127008:ℝ)*(1-1/127008)/10000)=127007/161310320640000 ∧
    ((1/127008:ℝ)*(1-1/127008)/10000)/(1/127008)^2=127007/10000 ∧
    ((1/2:ℝ)*(1-1/2)/10000)=1/40000 ∧ (1/200:ℝ)^2=1/40000 := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  intro r
  have h := frequency_resolution 10000 r (by omega) (1/127008) (by norm_num) (by norm_num)
  exact ⟨h, lt_of_lt_of_le (by norm_num) h⟩

/-- T29(iv): exact probability of zero hits under independent draws,
bounded by short rational inequalities, without expanding 10,000th powers. -/
theorem rare_zero_hit_probability :
    (9/10:ℝ)<(127007/127008:ℝ)^10000 ∧
    (127007/127008:ℝ)^10000<19/20 := by
  let a : ℝ := 127007/127008
  let b : ℝ := 127008/127007
  have ha : 0<a := by dsimp [a]; norm_num
  have hab : a*b=1 := by dsimp [a,b]; norm_num
  have hlo := one_add_mul_sub_le_pow (a := a) (by dsimp [a]; norm_num : -1≤a) 10000
  have hhi := one_add_mul_sub_le_pow (a := b) (by dsimp [b]; norm_num : -1≤b) 10000
  have hlower : (9/10:ℝ)<1+(10000:ℝ)*(a-1) := by dsimp [a]; norm_num
  have hmul := mul_le_mul_of_nonneg_left hhi (pow_nonneg ha.le 10000)
  rw [← mul_pow,hab,one_pow] at hmul
  have hc : 0<1+(10000:ℝ)*(b-1) := by dsimp [b]; norm_num
  have hright : (1:ℝ)<(19/20)*(1+(10000:ℝ)*(b-1)) := by dsimp [b]; norm_num
  exact ⟨lt_of_lt_of_le hlower hlo,
    by
      have hlt := lt_of_le_of_lt hmul hright
      exact lt_of_mul_lt_mul_right hlt hc.le⟩


/-- T22(e): realized seeds are excluded with at least their direct-exposure
probability, irrespective of their probabilities of the four indirect exposures. -/
theorem code_analysis_seed_exclusion {Ω I : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (estimated : I → Fin 4 → ℝ)
    (seed outcome baseline screen : Ω → I → Prop) (i : I) :
    sampleProb P (fun z => seed z i)≤
      sampleProb P (fun z => i∉codeAnalysisSet estimated seed outcome baseline screen z) := by
  unfold sampleProb
  apply Finset.sum_le_sum; intro z _
  by_cases hz : seed z i
  · have hnot : i∉codeAnalysisSet estimated seed outcome baseline screen z := by
      intro h; exact h.2.1 hz
    simp [hz,hnot]
  · simp only [hz, if_false, mul_zero]
    split_ifs <;> linarith [(P.positive z)]


/-- T29's actual 40-eligible seed law: one Boolean school assignment
and four independent uniform five-of-ten subsets. The focal student is
ineligible, has peers 0--4 in blocks 0 and 1, and its sole referent peer
is student 0 in block 0. Blocks 2 and 3 have no focal peer. -/
abbrev RareSeedState := Bool × ((h : Fin 4) → {s : Finset (Fin 10) // s.card=5})
def rareDesignExposure (z : RareSeedState) : Fin 4 :=
  if !z.1 then 0 else
    if Disjoint (z.2 0).val {0,1,2,3,4} ∧ Disjoint (z.2 1).val {0,1,2,3,4} then 1
    else if (0 : Fin 10)∈(z.2 0).val then 3 else 2
noncomputable def rareDesignMass (_ : RareSeedState) : ℝ := 1/(2*252^4)
noncomputable def rareDesignProbability (k : Fin 4) : ℝ :=
  ∑ z : RareSeedState, rareDesignMass z*(if rareDesignExposure z=k then 1 else 0)


end AronowAudit.P037

