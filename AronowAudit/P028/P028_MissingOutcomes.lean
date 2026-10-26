import Mathlib.Tactic
import Mathlib.Data.Fintype.BigOperators

namespace AronowAudit.P028
open scoped BigOperators
noncomputable section
open Classical

/-- A latent unit's two treatment potentials, two binary outcome potentials, and two
response potentials. Section 2, p. 678: “let Dᵢ(z) be the potential treatment”.
Exclusion is built in: Y(d,z) = Y(d). R(z) represents outcome recording. -/
structure BinaryAtom where
  d0 : Bool
  d1 : Bool
  y0 : Bool
  y1 : Bool
  r0 : Bool
  r1 : Bool
  deriving DecidableEq

/-- Rational representation of a binary variable's value in {0,1}. -/
def bit (b : Bool) : ℚ := if b then 1 else 0

/-- Seventeen latent atoms with rational weights, without normalization or positivity
constraints. The predicate `finiteValid` imposes these constraints for the witnesses.
The independent assignment coin is added by `jointMass`. -/
structure BinaryLaw where
  atom : Fin 17 → BinaryAtom
  mass : Fin 17 → ℚ

/-- P[Z=0]=99/200, P[Z=1]=101/200; the two witnesses use the same coin. -/
def assignmentMass (z : Bool) : ℚ := if z then 101/200 else 99/200

/-- Product weights on Fin 17 × Bool: latent atom and independent assignment.
For a `finiteValid` law, these are probability masses implementing Section 2
assumption (i). -/
def jointMass (M : BinaryLaw) (i : Fin 17) (z : Bool) : ℚ :=
  M.mass i * assignmentMass z

/-- Sum of latent weights over an event; a probability when `finiteValid M` holds. -/
def fprob (M : BinaryLaw) (E : Fin 17 → Prop) : ℚ :=
  ∑ i, if E i then M.mass i else 0

/-- Weighted sum of a function over the latent atoms; a population expectation
when `finiteValid M` holds. -/
def fexpect (M : BinaryLaw) (f : Fin 17 → ℚ) : ℚ := ∑ i, M.mass i * f i

/-- Ordinary event conditional mean, used only together with positive event mass.
Section 2's expectations and proof of Proposition 1, p. 678. -/
def fmean (M : BinaryLaw) (f : Fin 17 → ℚ) (E : Fin 17 → Prop) : ℚ :=
  (∑ i, if E i then M.mass i * f i else 0) / fprob M E

/-- Observed treatment D=D(Z), implicit in Section 2, p. 678. -/
def fd (a : BinaryAtom) (z : Bool) : Bool := if z then a.d1 else a.d0
/-- Observed outcome Y=Y(D(Z)), implicit in Section 2, p. 678. -/
def fy (a : BinaryAtom) (z : Bool) : Bool := if fd a z then a.y1 else a.y0
/-- Outcome-recording indicator R=R(Z). -/
def fr (a : BinaryAtom) (z : Bool) : Bool := if z then a.r1 else a.r0

/-- Complier event “D(1)>D(0)”, Section 2, p. 678. -/
def fc (a : BinaryAtom) : Prop := a.d0 = false ∧ a.d1 = true
/-- P_c ≡ Pr[D(1)>D(0)], Section 2, p. 678. -/
def fpc (M : BinaryLaw) : ℚ := fprob M (fun i => fc (M.atom i))
/-- EY_z ≡ E[Y|Z=z], Section 2, p. 678; independent assignment cancels
from the ordinary event-conditional expectation. -/
def fey (M : BinaryLaw) (z : Bool) : ℚ := fexpect M (fun i => bit (fy (M.atom i) z))
/-- EY_c(d) ≡ E[Y(d)|D(1)>D(0)], Proposition 1 proof, p. 678. -/
def fcy (M : BinaryLaw) (d : Bool) : ℚ :=
  fmean M (fun i => bit (if d then (M.atom i).y1 else (M.atom i).y0))
    (fun i => fc (M.atom i))

/-- Joint probability of a recorded outcome cell, conditional on assignment. -/
def recordedCell (M : BinaryLaw) (z d v : Bool) : ℚ :=
  fprob M (fun i => fd (M.atom i) z = d ∧ fr (M.atom i) z = true ∧ fy (M.atom i) z = v)
/-- Joint probability of a missing-outcome cell, conditional on assignment. -/
def missingCell (M : BinaryLaw) (z d : Bool) : ℚ :=
  fprob M (fun i => fd (M.atom i) z = d ∧ fr (M.atom i) z = false)

/-- Complete observed-data law on (Z,D,R,R·Y), with binary R·Y represented
by Boolean conjunction. Outcomes with R=0 are never revealed. -/
def observedLaw (M : BinaryLaw) (o : Bool × Bool × Bool × Bool) : ℚ :=
  assignmentMass o.1 * fprob M (fun i => fd (M.atom i) o.1 = o.2.1 ∧
    fr (M.atom i) o.1 = o.2.2.1 ∧
    (fr (M.atom i) o.1 && fy (M.atom i) o.1) = o.2.2.2)

/-- Full causal assumptions for the finite binary witnesses: positive normalized
masses, monotonicity, and nonzero first stage. Exclusion and boundedness are built
into BinaryAtom; random assignment is the product law `jointMass`. -/
def finiteValid (M : BinaryLaw) : Prop :=
  (∀ i, 0 < M.mass i) ∧ (∑ i, M.mass i) = 1 ∧
  (∀ i, bit (M.atom i).d0 ≤ bit (M.atom i).d1) ∧
  fexpect M (fun i => bit (M.atom i).d1 - bit (M.atom i).d0) = fpc M ∧
  0 < fpc M

/-- The lower witness on 17 latent atoms. -/
def lowerLaw : BinaryLaw where
  atom := ![⟨true, true, false, false, true, false⟩,
    ⟨true, true, false, false, true, true⟩,
    ⟨false, false, false, false, false, true⟩,
    ⟨false, false, false, false, true, true⟩,
    ⟨true, true, false, true, false, true⟩,
    ⟨true, true, false, true, true, true⟩,
    ⟨false, false, true, false, true, false⟩,
    ⟨false, false, true, false, true, true⟩,
    ⟨false, true, false, false, false, false⟩,
    ⟨false, true, false, false, false, true⟩,
    ⟨false, true, false, false, true, false⟩,
    ⟨false, true, false, false, true, true⟩,
    ⟨false, true, false, true, false, true⟩,
    ⟨false, true, false, true, true, true⟩,
    ⟨false, true, true, false, true, false⟩,
    ⟨false, true, true, false, true, true⟩,
    ⟨false, true, true, true, true, true⟩]
  mass := ![104/12375,
    871/12375,
    738/15655,
    4346/15655,
    1/495,
    8/99,
    26/505,
    26/101,
    40958176/44062954375,
    343024724/44062954375,
    2170783328/396566589375,
    18180310372/396566589375,
    29736094/1762518175,
    1576012982/15862663575,
    13228208/12792470625,
    110786242/12792470625,
    9603827/511698825]

/-- The upper witness on 17 latent atoms. -/
def upperLaw : BinaryLaw where
  atom := ![⟨true, true, false, false, false, true⟩,
    ⟨true, true, false, false, true, true⟩,
    ⟨false, false, false, false, true, false⟩,
    ⟨false, false, false, false, true, true⟩,
    ⟨true, true, false, true, true, false⟩,
    ⟨true, true, false, true, true, true⟩,
    ⟨false, false, true, false, false, true⟩,
    ⟨false, false, true, false, true, true⟩,
    ⟨false, true, false, false, true, true⟩,
    ⟨false, true, false, true, true, false⟩,
    ⟨false, true, false, true, true, true⟩,
    ⟨false, true, true, false, false, true⟩,
    ⟨false, true, true, false, true, true⟩,
    ⟨false, true, true, true, false, false⟩,
    ⟨false, true, true, true, false, true⟩,
    ⟨false, true, true, true, true, false⟩,
    ⟨false, true, true, true, true, true⟩]
  mass := ![1/495,
    13/165,
    26/505,
    164/505,
    32/5841,
    40/531,
    936/20503,
    4342/20503,
    6746986/511698825,
    79537936/30190230675,
    19884484/548913285,
    79169476/11541651275,
    3305325623/103874861475,
    933302176/680957425225,
    233325544/12381044095,
    38965365848/6128616827025,
    9741341462/111429396855]

/-- Random assignment is independent of every latent event, including the response
potentials. This is stronger than the paper requires, not an omitted hypothesis. 
Reference (P028-T1): Section 4, p. 679. -/
theorem finite_assignment_independent (M : BinaryLaw) (E : Fin 17 → Prop) (z : Bool) :
    (∑ i, if E i then jointMass M i z else 0) = fprob M E * assignmentMass z := by
  classical
  unfold fprob jointMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- T1: both explicit laws have positive normalized masses, monotonic treatment
potentials, and first stage P_c=2047/9999>0. Binary potentials imply boundedness. 
Reference (P028-T1): Section 4, p. 679. -/
theorem missing_witness_assumptions :
    finiteValid lowerLaw ∧ finiteValid upperLaw ∧
    fpc lowerLaw = 2047/9999 ∧ fpc upperLaw = 2047/9999 ∧
    assignmentMass false = 99/200 ∧ assignmentMass true = 101/200 ∧
    0 < assignmentMass false ∧ 0 < assignmentMass true := by
  norm_num [finiteValid, lowerLaw, upperLaw, fpc, fc, fprob, fexpect,
    assignmentMass, bit, Fin.sum_univ_succ]
  repeat' apply And.intro
  all_goals intro i; fin_cases i <;> norm_num [bit]

/-- The recorded source counts. -/
def recordedCount (z d v : Bool) : ℚ :=
  if z then (if d then (if v then 110 else 67) else (if v then 130 else 164))
  else (if d then (if v then 40 else 39) else (if v then 167 else 212))
/-- The missing source counts. -/
def missingCount (z d : Bool) : ℚ := if z then (if d then 8 else 26) else (if d then 1 else 36)
/-- Assignment-arm denominators (all units): 495 and 505. -/
def armCount (z : Bool) : ℚ := if z then 505 else 495

/-- T1: each law exactly reproduces every recorded-outcome and missing-outcome
cell of the source table, conditional on assignment. 
Reference (P028-T1): Section 4, p. 679. -/
theorem missing_witness_observed_cells :
    (∀ z d v, recordedCell lowerLaw z d v = recordedCount z d v / armCount z ∧
                recordedCell upperLaw z d v = recordedCount z d v / armCount z) ∧
    (∀ z d, missingCell lowerLaw z d = missingCount z d / armCount z ∧
              missingCell upperLaw z d = missingCount z d / armCount z) := by
  constructor
  · intro z d v; cases z <;> cases d <;> cases v <;>
      norm_num [recordedCell, recordedCount, armCount, fprob, lowerLaw, upperLaw,
        fd, fr, fy, Fin.sum_univ_succ]
  · intro z d; cases z <;> cases d <;>
      norm_num [missingCell, missingCount, armCount, fprob, lowerLaw, upperLaw,
        fd, fr, Fin.sum_univ_succ]

/-- T1: the entire law of everything observed agrees in the two witnesses. 
Reference (P028-T1): Section 4, p. 679. -/
theorem missing_witness_same_observed_law : observedLaw lowerLaw = observedLaw upperLaw := by
  funext ⟨z, d, r, v⟩
  cases z <;> cases d <;> cases r <;> cases v <;>
    norm_num [observedLaw, assignmentMass, fprob, lowerLaw, upperLaw,
      fd, fr, fy, Fin.sum_univ_succ]

/-- T1: the lower and upper laws have the different complier mean pairs
(1423/10235,6749/10235) and (7633/10235,7642/10235). 
Reference (P028-T1): Section 4, p. 679. -/
theorem missing_witness_complier_means :
    fcy lowerLaw false = 1423/10235 ∧ fcy lowerLaw true = 6749/10235 ∧
    fcy upperLaw false = 7633/10235 ∧ fcy upperLaw true = 7642/10235 := by
  norm_num [fcy, fmean, fprob, fc, lowerLaw, upperLaw, bit, Fin.sum_univ_succ]

/-- T1: two concrete laws satisfy all standing causal assumptions and agree on
(Z,D,R,R·Y), but differ in both complier average potential outcomes. Thus incomplete
recording alone does not justify Section 4's point-identification inference. 
Reference (P028-T1): Section 4, p. 679. -/
theorem missing_outcome_counterexample :
    finiteValid lowerLaw ∧ finiteValid upperLaw ∧
    observedLaw lowerLaw = observedLaw upperLaw ∧
    fcy lowerLaw false = 1423/10235 ∧ fcy lowerLaw true = 6749/10235 ∧
    fcy upperLaw false = 7633/10235 ∧ fcy upperLaw true = 7642/10235 ∧
    fcy lowerLaw false ≠ fcy upperLaw false ∧ fcy lowerLaw true ≠ fcy upperLaw true := by
  rcases missing_witness_assumptions with ⟨hl, hu, _⟩
  rcases missing_witness_complier_means with ⟨h0, h1, h2, h3⟩
  refine ⟨hl, hu, missing_witness_same_observed_law, h0, h1, h2, h3, ?_, ?_⟩
  · rw [h0, h2]; norm_num
  · rw [h1, h3]; norm_num

/-- T1 consequence: for either potential outcome, no function of the observed law
can return its complier mean in every admissible finite law (and hence in every
probability model allowed by the paper). 
Reference (P028-T1): Section 4, p. 679. -/
theorem missing_outcome_not_identified (d : Bool) :
    ¬ ∃ F : (Bool × Bool × Bool × Bool → ℚ) → ℚ,
      ∀ M : BinaryLaw, finiteValid M → F (observedLaw M) = fcy M d := by
  rintro ⟨F, hF⟩
  have h := missing_outcome_counterexample
  have he : fcy lowerLaw d = fcy upperLaw d := by
    rw [← hF lowerLaw h.1, ← hF upperLaw h.2.1, h.2.2.1]
  cases d
  · exact h.2.2.2.2.2.2.2.1 he
  · exact h.2.2.2.2.2.2.2.2 he

/-- Respondent assignment-arm means E[Y|Z=z,R=1]. -/
def respondentArmMean (M : BinaryLaw) (z : Bool) : ℚ :=
  fmean M (fun i => bit (fy (M.atom i) z)) (fun i => fr (M.atom i) z = true)
/-- Respondent cell means E[Y|D=d,Z=z,R=1]. -/
def respondentCellMean (M : BinaryLaw) (d z : Bool) : ℚ :=
  fmean M (fun i => bit (fy (M.atom i) z))
    (fun i => fd (M.atom i) z = d ∧ fr (M.atom i) z = true)
/-- Full-population take-up Pr[D=d|Z=z], Corollary 1. -/
def ftakeup (M : BinaryLaw) (d z : Bool) : ℚ :=
  fprob M (fun i => fd (M.atom i) z = d)
/-- Full-population cell outcome mean E[Y|D=d,Z=z], Corollary 1. -/
def fcellmean (M : BinaryLaw) (d z : Bool) : ℚ :=
  fmean M (fun i => bit (fy (M.atom i) z)) (fun i => fd (M.atom i) z = d)
/-- The two expressions printed in Corollary 1, parameterized by the arm and
pure-cell means. This distinguishes full moments from respondent moments. -/
def corollaryPair (p q r e0 e1 a n : ℚ) : ℚ × ℚ :=
  ((e0-q*a-r*n)/p, (e0-q*a-r*n)/p + (e1-e0)/p)
/-- Applying the population identity to each witness's full-outcome law. -/
def fullCorollary (M : BinaryLaw) : ℚ × ℚ :=
  corollaryPair (fpc M) (ftakeup M true false) (ftakeup M false true)
    (fey M false) (fey M true) (fcellmean M true false) (fcellmean M false true)
/-- The mixed available-case plug-in: take-up from every
unit, means from respondents, without any response assumption. -/
def respondentCorollary (M : BinaryLaw) : ℚ × ℚ :=
  corollaryPair (fpc M) (ftakeup M true false) (ftakeup M false true)
    (respondentArmMean M false) (respondentArmMean M true)
    (respondentCellMean M true false) (respondentCellMean M false true)

/-- T1: take-up and respondent means coincide with the exact source table,
while the full-population arm means differ between the witnesses. 
Reference (P028-T1): Section 4, p. 679. -/
theorem missing_witness_reported_moments :
    (∀ M ∈ [lowerLaw, upperLaw],
      ftakeup M true false = 16/99 ∧ ftakeup M false true = 64/101 ∧
      respondentArmMean M false = 207/458 ∧ respondentArmMean M true = 240/471 ∧
      respondentCellMean M true false = 40/79 ∧ respondentCellMean M false true = 130/294) ∧
    fey lowerLaw false = 208/495 ∧ fey lowerLaw true = 266/505 ∧
    fey upperLaw false = 27/55 ∧ fey upperLaw true = 248/505 := by
  constructor
  · intro M hM
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
    rcases hM with rfl | rfl <;>
      norm_num [ftakeup, respondentArmMean, respondentCellMean, fmean, fprob,
        lowerLaw, upperLaw, fd, fr, fy, bit, Fin.sum_univ_succ]
  · norm_num [fey, fexpect, lowerLaw, upperLaw, fd, fy, bit, Fin.sum_univ_succ]

/-- T1: Corollary 1 returns the correct pair at full-population moments.
The respondent plug-in is the same in both laws and is correct in neither. 
Reference (P028-T1): Section 4, p. 679. -/
theorem missing_witness_corollary_comparison :
    fullCorollary lowerLaw = (1423/10235,6749/10235) ∧
    fullCorollary upperLaw = (7633/10235,7642/10235) ∧
    respondentCorollary lowerLaw = (1594452863/3629163146,896530960/1244058109) ∧
    respondentCorollary upperLaw = (1594452863/3629163146,896530960/1244058109) ∧
    respondentCorollary lowerLaw ≠ (fcy lowerLaw false,fcy lowerLaw true) ∧
    respondentCorollary upperLaw ≠ (fcy upperLaw false,fcy upperLaw true) := by
  have hf : fullCorollary lowerLaw = (1423/10235,6749/10235) ∧
      fullCorollary upperLaw = (7633/10235,7642/10235) := by
    norm_num [fullCorollary, corollaryPair, ftakeup, fcellmean, fpc, fey,
      fmean, fprob, fexpect, fc, lowerLaw, upperLaw, fd, fy, bit, Fin.sum_univ_succ]
  have hr : respondentCorollary lowerLaw = (1594452863/3629163146,896530960/1244058109) ∧
      respondentCorollary upperLaw = (1594452863/3629163146,896530960/1244058109) := by
    norm_num [respondentCorollary, corollaryPair, ftakeup, respondentArmMean,
      respondentCellMean, fpc, fmean, fprob, fc, lowerLaw, upperLaw, fd, fr, fy,
      bit, Fin.sum_univ_succ]
  refine ⟨hf.1, hf.2, hr.1, hr.2, ?_, ?_⟩
  · rw [hr.1, missing_witness_complier_means.1, missing_witness_complier_means.2.1]
    norm_num
  · rw [hr.2, missing_witness_complier_means.2.2.1, missing_witness_complier_means.2.2.2]
    norm_num

/-- The full-compliance witness has a single constant potential vector and two
assignment atoms, each of probability 1/2. -/
def fullPotential : BinaryAtom := ⟨false,true,false,true,true,true⟩
/-- Probability on the two assignment atoms of the full-compliance witness. -/
def twoAtomProb (E : Bool → Prop) : ℚ := ∑ z : Bool, if E z then 1/2 else 0
/-- Conditional expectation in the two-atom witness, used only on positive events. -/
def twoAtomMean (f : Bool → ℚ) (E : Bool → Prop) : ℚ :=
  (∑ z : Bool, if E z then (1/2)*f z else 0) / twoAtomProb E

/-- T7: the constant potential vector is independent of the assignment coin.
The equality holds for every potential-vector event and both assignments. 
Reference (P028-T7): Proposition 1 proof, p. 678. -/
theorem full_compliance_independent (E : BinaryAtom → Prop) (z : Bool) :
    twoAtomProb (fun b => E fullPotential ∧ b = z) =
      twoAtomProb (fun _ => E fullPotential) * twoAtomProb (fun b => b = z) := by
  by_cases h : E fullPotential <;> cases z <;> norm_num [twoAtomProb, Fintype.sum_bool, h]

/-- T7: an explicit two-atom law satisfies every standing assumption,
has P_c=1 and complier means (0,1), but the noncomplier conditioning event is
null and the proof's division has numerator and denominator zero. Both pure
noncomplier cells are also null, so Corollary 1's positive-cell premise fails. 
Reference (P028-T7): Proposition 1 proof, p. 678. -/
theorem full_compliance_counterexample :
    twoAtomProb (fun _ => True) = 1 ∧
    twoAtomProb (fun z => z = false) = 1/2 ∧ twoAtomProb (fun z => z = true) = 1/2 ∧
    bit fullPotential.d0 ≤ bit fullPotential.d1 ∧
    (0 ≤ bit fullPotential.y0 ∧ bit fullPotential.y0 ≤ 1) ∧
    (0 ≤ bit fullPotential.y1 ∧ bit fullPotential.y1 ≤ 1) ∧
    (∑ _ : Bool, (1/2:ℚ)*(bit fullPotential.d1-bit fullPotential.d0)) = 1 ∧
    twoAtomProb (fun _ => fc fullPotential) = 1 ∧
    twoAtomMean (fun z => bit (fy fullPotential z)) (fun z => z = false) = 0 ∧
    twoAtomMean (fun z => bit (fy fullPotential z)) (fun z => z = true) = 1 ∧
    twoAtomMean (fun _ => bit fullPotential.y0) (fun _ => fc fullPotential) = 0 ∧
    twoAtomMean (fun _ => bit fullPotential.y1) (fun _ => fc fullPotential) = 1 ∧
    twoAtomProb (fun _ => fullPotential.d1 = fullPotential.d0) = 0 ∧
    (1-(twoAtomProb (fun _ => fc fullPotential))) = 0 ∧
    ((1:ℚ)-(twoAtomProb (fun _ => fc fullPotential))*1) = 0 ∧
    twoAtomProb (fun z => fd fullPotential z = true ∧ z = false) = 0 ∧
    twoAtomProb (fun z => fd fullPotential z = false ∧ z = true) = 0 ∧
    (∀ n : ℝ, 1*0+(1-1)*n = 0 ∧ 1*1+(1-1)*n = 1) ∧
    (∀ a n : ℝ, 0*a+0*n = 0) := by
  norm_num [twoAtomProb, twoAtomMean, fullPotential, fc, fd, fy, bit, Fintype.sum_bool]

/-- Multiplying latent weights that sum to one by the independent assignment coin
gives joint weights that sum to one on the 34 sample-space atoms. Nonnegativity
is separate; `missing_witness_joint_probability` proves strict positivity for
both witnesses.
Reference (P028-T1): Section 4, p. 679. -/
theorem finite_joint_normalized (M : BinaryLaw) (h : (∑ i, M.mass i) = 1) :
    (∑ i : Fin 17, ∑ z : Bool, jointMass M i z) = 1 := by
  have hi : ∀ i, (∑ z : Bool, jointMass M i z) = M.mass i := by
    intro i
    norm_num [jointMass,assignmentMass,Fintype.sum_bool]
    <;> ring
  simp_rw [hi]
  exact h

/-- T1: the complete product laws have total mass one and strictly positive
mass at every atom. This certifies the probability laws, not just their moments. 
Reference (P028-T1): Section 4, p. 679. -/
theorem missing_witness_joint_probability :
    (∑ i : Fin 17, ∑ z : Bool, jointMass lowerLaw i z) = 1 ∧
    (∑ i : Fin 17, ∑ z : Bool, jointMass upperLaw i z) = 1 ∧
    (∀ i z, 0 < jointMass lowerLaw i z) ∧ (∀ i z, 0 < jointMass upperLaw i z) := by
  have hl := missing_witness_assumptions.1
  have hu := missing_witness_assumptions.2.1
  refine ⟨finite_joint_normalized lowerLaw hl.2.1,finite_joint_normalized upperLaw hu.2.1,?_,?_⟩
  · intro i z
    unfold jointMass
    apply mul_pos (hl.1 i)
    cases z <;> norm_num [assignmentMass]
  · intro i z
    unfold jointMass
    apply mul_pos (hu.1 i)
    cases z <;> norm_num [assignmentMass]

end
end AronowAudit.P028



