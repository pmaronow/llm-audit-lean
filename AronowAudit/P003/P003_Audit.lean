import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log

/-! P003: exact finite-population objects and target statements.
    All probabilities below are actual finite design sums, not abstract probability oracles.
    Unit labels are zero based; count coordinates are always (11,10,01,00).
    Empty accepted sets have empty interval hulls. -/

namespace AronowAudit.P003

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-- "v = (v₁₁,v₁₀,v₀₁,v₀₀), v_ab = ∑ 1{w_j=(a,b)}", (2.2), p. 5.
    The same four coordinates encode observed counts n_zy in (2.8). -/
@[ext] structure Counts where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- "v₁₁ + v₁₀ + v₀₁ + v₀₀ = n", (4.2), p. 8. -/
def Counts.total (v : Counts) : ℕ := v.a + v.b + v.c + v.d

/-- "v₁₀ − v₀₁ = nτ₀", (4.2), p. 8; subtraction is in ℤ. -/
def Counts.effect (v : Counts) : ℤ := (v.b : ℤ) - v.c

/-- "τ(w) = (1/n)∑(w_j(1)−w_j(0))", (2.6), p. 5, in count form (4.2). -/
def tauQ (v : Counts) : ℚ := (v.effect : ℚ) / v.total

/-- The real-valued SATE of (2.6), represented by the exact rational count formula. -/
def tau (v : Counts) : ℝ := (tauQ v : ℝ)

/-- "T(n) = n₁₁/m − n₀₁/(n−m)", below (2.8), p. 5. -/
def estimateQ (o : Counts) : ℚ := (o.a : ℚ) / (o.a + o.b) -
  (o.c : ℚ) / (o.c + o.d)

/-- The real Neyman estimate (2.7)-(2.8), p. 5. -/
def estimate (o : Counts) : ℝ := (estimateQ o : ℝ)

/-- Uniform complete randomization (2.4), p. 5, compressed by potential-outcome
    type: q_ab counts treated subjects of type (a,b). The fourth coordinate is
    m minus the first three; every admissible vector appears exactly once. -/
def randomStates (v : Counts) (m : ℕ) : List Counts :=
  (List.range (min v.a m + 1)).flatMap fun a =>
  (List.range (min v.b (m-a) + 1)).flatMap fun b =>
  (List.range (min v.c (m-a-b) + 1)).filterMap fun c =>
    let d := m-a-b-c
    if d ≤ v.d then some ⟨a,b,c,d⟩ else none

/-- The same binomial coefficient as choose(n,k), (2.4), p. 5, evaluated
    by descending factorials so kernel checking avoids exponential Pascal recursion. -/
def binomial (n k : ℕ) : ℕ := Nat.fast_choose n k

/-- The computational binomial is exactly Mathlib's standard choose(n,k).
    This identity certifies the representation used in every finite numerical sum. -/
theorem binomial_eq_choose (n k : ℕ) : binomial n k = n.choose k := by
  exact congrFun (congrFun Nat.choose_eq_fast_choose.symm n) k


/-- Number of labeled assignments inducing q: ∏_ab choose(v_ab,q_ab),
    divided by choose(n,m) for its probability. This is (2.4)'s uniform law. -/
def multiplicity (v q : Counts) : ℕ :=
  binomial v.a q.a * binomial v.b q.b * binomial v.c q.c * binomial v.d q.d

/-- Observed counts (2.5), (2.8), p. 5, produced by a type-count assignment. -/
def observed (v q : Counts) : Counts :=
  ⟨q.a+q.b, q.c+q.d, v.a-q.a+v.c-q.c, v.b-q.b+v.d-q.d⟩

/-- A finite weighted probability over the complete-randomization distribution (2.4).
    The weights count labeled assignments, including multiplicities. -/
noncomputable def designProb (v : Counts) (m : ℕ) (event : Counts → Prop) : ℝ :=
  ((randomStates v m).map fun q =>
    if event q then (multiplicity v q : ℝ) else 0).sum / v.total.choose m

/-- Finite expectation over the same uniform randomization distribution, p. 5. -/
noncomputable def designMean (v : Counts) (m : ℕ) (f : Counts → ℝ) : ℝ :=
  ((randomStates v m).map fun q => (multiplicity v q : ℝ) * f q).sum /
    v.total.choose m

/-- "|T(Ỹ,Z̃)−τ(w)| ≥ |T(Y,Z)−τ(w)|", (2.12), p. 6.
    Multiplying both deviations by the positive common denominator n m(n−m)
    gives this integer numerator; it avoids rounding in exact enumeration. -/
def deviationNumerator (v o : Counts) (m : ℕ) : ℤ :=
  (v.total : ℤ) * (((v.total : ℤ)-m) * o.a - (m : ℤ) * o.c) -
  (m : ℤ) * ((v.total : ℤ)-m) * v.effect

/-- Numerator of the permutation probability (2.12): count the assignments
    whose absolute centered estimator is at least the observed one. -/
def tailCount (v o : Counts) : ℕ :=
  let m := o.a+o.b
  ((randomStates v m).map fun q =>
    if (deviationNumerator v (observed v q) m).natAbs ≥
        (deviationNumerator v o m).natAbs then multiplicity v q else 0).sum

/-- "p(v,n) = p(w,Y,Z)", Definition 2.1, p. 6: an exact rational finite sum. -/
def pValue (v o : Counts) : ℚ := (tailCount v o : ℚ) / binomial v.total (o.a+o.b)

/-- Exact acceptance comparison for (2.12), performed with integer cross
    products to avoid repeatedly normalizing fractions during enumeration.
    The zero-denominator branch preserves Lean's total rational division. -/
def levelAccepted (α : ℚ) (v o : Counts) : Bool :=
  let D := binomial v.total (o.a+o.b)
  if D = 0 then decide (α ≤ 0) else
    decide (α.num*(D : ℤ) ≤ (tailCount v o : ℤ)*(α.den : ℤ))

/-- The integer computation is equivalent to the paper's p≥α rule for every
    input, including the totalized zero-denominator case. -/
theorem level_accepted_spec (α : ℚ) (v o : Counts) :
    levelAccepted α v o = true ↔ α ≤ pValue v o := by
  unfold levelAccepted pValue
  by_cases hD : binomial v.total (o.a+o.b) = 0
  · simp [hD]
  · simp only [if_neg hD,decide_eq_true_eq]
    have hd : (0 : ℚ) < binomial v.total (o.a+o.b) := by
      exact_mod_cast Nat.pos_of_ne_zero hD
    have ha : (0 : ℚ) < α.den := by exact_mod_cast α.den_pos
    conv_rhs => rw [← α.num_div_den]
    rw [div_le_div_iff₀ ha hd]
    norm_cast


/-- "T(n) = {(i,j,k,l): 0≤i≤n₁₁, …, 0≤l≤n₀₀}", (2.13),
    and "v(i,j,k,l)=(i+k,n₁₁−i+l,n₀₁−k+j,n₁₀+n₀₀−j−l)",
    (2.14), p. 6. Repetitions of the same vector are harmless. -/
def possibleTables (o : Counts) : List Counts :=
  (List.range (o.a+1)).flatMap fun i =>
  (List.range (o.b+1)).flatMap fun j =>
  (List.range (o.c+1)).flatMap fun k =>
  (List.range (o.d+1)).map fun l =>
    ⟨i+k, o.a-i+l, o.c-k+j, o.b+o.d-j-l⟩

/-- "A count vector is possible if it arises from some possible table", p. 5;
    (2.13)-(2.14) enumerate precisely those vectors. -/
def Possible (o v : Counts) : Prop := v ∈ possibleTables o

instance possibleDecidable (o v : Counts) : Decidable (Possible o v) :=
  inferInstanceAs (Decidable (v ∈ possibleTables o))

/-- "K(n)={τ(v(i,j,k,l)): … Algorithm 2.2 accepts}", (2.15), p. 6. -/
noncomputable def accepted (α : ℝ) (o : Counts) : Finset ℝ := by
  classical
  exact ((possibleTables o).filter fun v => α ≤ (pValue v o : ℝ)).toFinset.image tau

/-- "Iα(n)=[min K,max K]", Algorithm 2.3, p. 6. The existential hull
    is exactly this closed interval for nonempty K, and is empty for empty K. -/
noncomputable def exactInterval (α : ℝ) (o : Counts) : Set ℝ :=
  {t | ∃ l ∈ accepted α o, ∃ u ∈ accepted α o, l ≤ t ∧ t ≤ u}

/-- Endpoints "Lα=min K, Uα=max K", Algorithm 2.3, p. 6.
    The paper leaves empty K undefined; endpoint-based assertions below carry
    nonemptiness, except (6.2), where the convention is made explicit. -/
noncomputable def lower (α : ℝ) (o : Counts) : ℝ := sInf (↑(accepted α o) : Set ℝ)
/-- "Uα=max K", Algorithm 2.3, p. 6, whenever K is nonempty. -/
noncomputable def upper (α : ℝ) (o : Counts) : ℝ := sSup (↑(accepted α o) : Set ℝ)

/-- Exact rational specialization of (2.15), used for certified numerical examples. -/
def acceptedEffectsQ (α : ℚ) (o : Counts) : List ℤ :=
  ((possibleTables o).dedup.filter fun v => levelAccepted α v o).map Counts.effect

/-- Deduplication and integer comparisons preserve exactly the accepted
    possible-table effects of (2.15), rather than introducing a surrogate set. -/
theorem accepted_effects_spec (α : ℚ) (o : Counts) (d : ℤ) :
    d ∈ acceptedEffectsQ α o ↔
      ∃ v, Possible o v ∧ α ≤ pValue v o ∧ v.effect = d := by
  simp only [acceptedEffectsQ,List.mem_map,List.mem_filter,List.mem_dedup,
    level_accepted_spec,Possible]
  simp only [and_assoc]


/-- Rational endpoints of Algorithm 2.3, with none for empty K. -/
def intervalQ (α : ℚ) (o : Counts) : Option (ℚ × ℚ) :=
  match acceptedEffectsQ α o with
  | [] => none
  | d :: ds => some ((ds.foldl min d : ℚ) / o.total,
                     (ds.foldl max d : ℚ) / o.total)

/-- Missingness (6.1), p. 13, compressed to the number of missing outcomes
    in each observed (Z,Y) cell. Arbitrary dependence of J on Y and Z is allowed. -/
def missingMasks (o : Counts) : List Counts :=
  (List.range (o.a+1)).flatMap fun a =>
  (List.range (o.b+1)).flatMap fun b =>
  (List.range (o.c+1)).flatMap fun c =>
  (List.range (o.d+1)).map fun d => ⟨a,b,c,d⟩

/-- "Y⁺=1 if J=1,Z=1; Y⁺=0 if J=1,Z=0; Y⁺=M if J=0",
    Definition 6.1, p. 14, in observed-count form. -/
def plusCompletion (o r : Counts) : Counts :=
  ⟨o.a+r.b, o.b-r.b, o.c-r.c, o.d+r.c⟩

/-- "Y⁻=0 if J=1,Z=1; Y⁻=1 if J=1,Z=0; Y⁻=M if J=0",
    Definition 6.1, p. 14. -/
def minusCompletion (o r : Counts) : Counts :=
  ⟨o.a-r.a, o.b+r.a, o.c+r.d, o.d-r.d⟩

/-- "Y(M) consists of all … outcomes compatible with … M", (D.2), p. 29.
    Completions vary the numbers of successes among the missing treated/control units. -/
def completions (o r : Counts) : List Counts :=
  (List.range (r.a+r.b+1)).flatMap fun t =>
  (List.range (r.c+r.d+1)).map fun c =>
    ⟨o.a-r.a+t, o.b-r.b+(r.a+r.b-t),
      o.c-r.c+c, o.d-r.d+(r.c+r.d-c)⟩

/-- "Iα°=[min(Lα(Y⁻),T(Y⁻)),max(Uα(Y⁺),T(Y⁺))]", (6.2), p. 14.
    For an empty K, the extremum is omitted and the estimate alone is used.
    This agrees with (6.2) whenever both printed endpoints exist. -/
noncomputable def missingInterval (α : ℝ) (o r : Counts) : Set ℝ :=
  let lo := minusCompletion o r
  let hi := plusCompletion o r
  Set.Icc (if (accepted α lo).Nonempty then min (lower α lo) (estimate lo)
           else estimate lo)
          (if (accepted α hi).Nonempty then max (upper α hi) (estimate hi)
           else estimate hi)

/-- The completion union Jα, (D.2), p. 29; empty inversions contribute no points. -/
noncomputable def completionUnion (α : ℝ) (o r : Counts) : Set ℝ :=
  {t | ∃ c ∈ completions o r, t ∈ exactInterval α c}

/-- Corrected arbitrary-allocation interval Hα (target T3): the closed interval
    hull of the union of all accepted effect sets over the completions. -/
noncomputable def completionHull (α : ℝ) (o r : Counts) : Set ℝ :=
  {t | ∃ l ∈ completionUnion α o r, ∃ u ∈ completionUnion α o r, l ≤ t ∧ t ≤ u}

/-- Any joint law of Z and J, Section 6, p. 13: nonnegative masses on the
    randomization type counts and missing-cell counts, with the prescribed
    complete-randomization marginal. No independence restriction is imposed. -/
def IsMissingLaw (v : Counts) (m : ℕ) (μ : Counts → Counts → ℝ) : Prop :=
  (∀ q ∈ randomStates v m, ∀ r ∈ missingMasks (observed v q), 0 ≤ μ q r) ∧
  (∀ q ∈ randomStates v m,
    ((missingMasks (observed v q)).map (μ q)).sum =
      (multiplicity v q : ℝ) / v.total.choose m)

/-- Joint finite probability for the missingness law; Section 6 and corrected (6.3). -/
noncomputable def missingProb (v : Counts) (m : ℕ) (μ : Counts → Counts → ℝ)
    (E : Counts → Counts → Prop) : ℝ :=
  ((randomStates v m).map fun q =>
    ((missingMasks (observed v q)).map fun r => if E q r then μ q r else 0).sum).sum

/-- Rational version of (6.2), with estimates used if an extremal inversion is empty. -/
def missingIntervalQ (α : ℚ) (o r : Counts) : ℚ × ℚ :=
  let lo := minusCompletion o r
  let hi := plusCompletion o r
  (match intervalQ α lo with
    | none => estimateQ lo
    | some (l,_) => min l (estimateQ lo),
   match intervalQ α hi with
    | none => estimateQ hi
    | some (_,u) => max u (estimateQ hi))

/-- Explicit potential outcomes of target T1: 11 always-one, 3 (0,1), 6 always-zero. -/
def badPopulation : Counts := ⟨11,0,3,6⟩

/-- Target T1's missingness in count form: one control success is missing
precisely when all three (0,1) units and no other units are treated. -/
def badMask (q : Counts) : Counts :=
  if q = ⟨0,0,3,0⟩ then ⟨0,0,1,0⟩ else ⟨0,0,0,0⟩

/-- T1: the concrete missingness mask is legal on every realized observation,
    as required by (6.1), p. 13, including the exceptional treated set. -/
theorem bad_mask_legal (q : Counts) :
    badMask q ∈ missingMasks (observed badPopulation q) := by
  by_cases hq : q = ⟨0,0,3,0⟩
  · subst q
    decide +kernel
  · simp only [badMask,if_neg hq,missingMasks,List.mem_flatMap,List.mem_map,List.mem_range]
    refine ⟨0,by omega,0,by omega,0,by omega,0,by omega,rfl⟩


/-- Exact coverage of (6.2) in the concrete T1 experiment, using its deterministic J. -/
def badCoverage : ℚ :=
  ((randomStates badPopulation 3).map fun q =>
    let I := missingIntervalQ (109/500) (observed badPopulation q) (badMask q)
    if I.1 ≤ tauQ badPopulation ∧ tauQ badPopulation ≤ I.2
    then multiplicity badPopulation q else 0).sum / (1140 : ℚ)

/-! Small exact endpoint certificates for the missing-data counterexample.
These skip interior permutation tails, verify bounds without quadratic
list deduplication, and transfer integer extrema to the unchanged rational
interval implementation. The eleven inversions are used in the
printed and corrected coverage sums. -/
section MissingCounterexampleCompletion
set_option maxHeartbeats 2000000

/-- Endpoint certification only evaluates permutation tails for possible tables
outside the claimed effect bounds. Interior tables require no tail calculation. -/
def endpointBoundsCheck (α : ℚ) (o : Counts) (lo hi : ℤ) : Bool :=
  (possibleTables o).all fun v =>
    decide (lo ≤ v.effect ∧ v.effect ≤ hi) || !(levelAccepted α v o)

/-- The short-circuit Boolean certificate verifies bounds for every accepted
effect of the exact randomization inversion. -/
theorem endpointBoundsCheck_sound (α : ℚ) (o : Counts) (lo hi : ℤ)
    (hcheck : endpointBoundsCheck α o lo hi = true) :
    ∀ d ∈ acceptedEffectsQ α o, lo ≤ d ∧ d ≤ hi := by
  intro d hd
  obtain ⟨v, hv, ha, he⟩ := (accepted_effects_spec α o d).mp hd
  have h := List.all_eq_true.mp hcheck v hv
  have hacc : levelAccepted α v o = true := (level_accepted_spec α v o).mpr ha
  simpa only [hacc, Bool.not_true, Bool.or_false, decide_eq_true_eq, he] using h

/-- Accepted endpoint witnesses and the verified global bounds determine the
fold-based rational interval without evaluating every accepted tail. -/
theorem intervalQ_eq_of_endpoint_certificate (α : ℚ) (o : Counts) (lo hi : ℤ)
    (hbounds : endpointBoundsCheck α o lo hi = true)
    (hlo : ∃ v, Possible o v ∧ α ≤ pValue v o ∧ v.effect = lo)
    (hhi : ∃ v, Possible o v ∧ α ≤ pValue v o ∧ v.effect = hi) :
    intervalQ α o = some ((lo : ℚ)/o.total, (hi : ℚ)/o.total) := by
  have hb := endpointBoundsCheck_sound α o lo hi hbounds
  have hl := (accepted_effects_spec α o lo).mpr hlo
  have hu := (accepted_effects_spec α o hi).mpr hhi
  have hmin : (acceptedEffectsQ α o).min? = some lo :=
    List.min?_eq_some_iff.mpr ⟨hl, fun d hd => (hb d hd).1⟩
  have hmax : (acceptedEffectsQ α o).max? = some hi :=
    List.max?_eq_some_iff.mpr ⟨hu, fun d hd => (hb d hd).2⟩
  cases he : acceptedEffectsQ α o with
  | nil => simp only [he, List.not_mem_nil] at hl
  | cons d ds =>
    have hl' : ds.foldl min d = lo := by
      simpa only [he, List.min?_cons', Option.some.injEq] using hmin
    have hu' : ds.foldl max d = hi := by
      simpa only [he, List.max?_cons', Option.some.injEq] using hmax
    have hlq : (ds.map (fun x : ℤ => (x:ℚ))).foldl min (d:ℚ) = (lo:ℚ) := by
      simpa only [hl'] using (List.foldl_map_hom (g := fun x : ℤ => (x:ℚ))
        (f := min) (f' := min) (a := d) (l := ds) (fun x y => Int.cast_min.symm))
    have huq : (ds.map (fun x : ℤ => (x:ℚ))).foldl max (d:ℚ) = (hi:ℚ) := by
      simpa only [hu'] using (List.foldl_map_hom (g := fun x : ℤ => (x:ℚ))
        (f := max) (f' := max) (a := d) (l := ds) (fun x y => Int.cast_max.symm))
    simp only [intervalQ, he, bind_pure_comp]
    change some (((ds.map (fun x : ℤ => (x:ℚ))).foldl min (d:ℚ))/o.total,
      ((ds.map (fun x : ℤ => (x:ℚ))).foldl max (d:ℚ))/o.total) = _
    rw [hlq, huq]


/-- Critical observation: only 126 out-of-range possible tables require tails. -/
theorem critical_bounds : endpointBoundsCheck (109/500) ⟨0,3,11,6⟩ (-14) (-3) = true := by
  decide +kernel

theorem critical_interval : intervalQ (109/500) ⟨0,3,11,6⟩ = some (-7/10,-3/20) := by
  have h := intervalQ_eq_of_endpoint_certificate (109/500) ⟨0,3,11,6⟩ (-14) (-3) critical_bounds
    ⟨⟨0,0,14,6⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
    ⟨⟨11,0,3,6⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
  norm_num [Counts.total] at h
  convert h using 1 <;> norm_num

/-- Rejection certificate for possible tables outside the proposed interval. -/
theorem bounds_obs_0_3_14_3 : endpointBoundsCheck (109/500) ⟨0,3,14,3⟩ (-17) (-8) = true := by
  decide +kernel

theorem interval_obs_0_3_14_3 : intervalQ (109/500) ⟨0,3,14,3⟩ = some (-17/20,-2/5) := by
  have h := intervalQ_eq_of_endpoint_certificate (109/500) ⟨0,3,14,3⟩ (-17) (-8) bounds_obs_0_3_14_3
    ⟨⟨0,0,17,3⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
    ⟨⟨7,2,10,1⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
  norm_num [Counts.total] at h
  convert h using 1 <;> norm_num

/-- Rejection certificate for possible tables outside the proposed interval. -/
theorem bounds_obs_0_3_13_4 : endpointBoundsCheck (109/500) ⟨0,3,13,4⟩ (-16) (-7) = true := by
  decide +kernel

theorem interval_obs_0_3_13_4 : intervalQ (109/500) ⟨0,3,13,4⟩ = some (-4/5,-7/20) := by
  have h := intervalQ_eq_of_endpoint_certificate (109/500) ⟨0,3,13,4⟩ (-16) (-7) bounds_obs_0_3_13_4
    ⟨⟨0,0,16,4⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
    ⟨⟨7,2,9,2⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
  norm_num [Counts.total] at h
  convert h using 1 <;> norm_num

/-- Rejection certificate for possible tables outside the proposed interval. -/
theorem bounds_obs_0_3_12_5 : endpointBoundsCheck (109/500) ⟨0,3,12,5⟩ (-15) (-6) = true := by
  decide +kernel

theorem interval_obs_0_3_12_5 : intervalQ (109/500) ⟨0,3,12,5⟩ = some (-3/4,-3/10) := by
  have h := intervalQ_eq_of_endpoint_certificate (109/500) ⟨0,3,12,5⟩ (-15) (-6) bounds_obs_0_3_12_5
    ⟨⟨0,0,15,5⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
    ⟨⟨8,0,6,6⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
  norm_num [Counts.total] at h
  convert h using 1 <;> norm_num

theorem interval_obs_0_3_11_6 : intervalQ (109/500) ⟨0,3,11,6⟩ = some (-7/10,-3/20) := critical_interval

/-- Rejection certificate for possible tables outside the proposed interval. -/
theorem bounds_obs_1_2_13_4 : endpointBoundsCheck (109/500) ⟨1,2,13,4⟩ (-13) (-1) = true := by
  decide +kernel

theorem interval_obs_1_2_13_4 : intervalQ (109/500) ⟨1,2,13,4⟩ = some (-13/20,-1/20) := by
  have h := intervalQ_eq_of_endpoint_certificate (109/500) ⟨1,2,13,4⟩ (-13) (-1) bounds_obs_1_2_13_4
    ⟨⟨1,1,14,4⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
    ⟨⟨9,3,4,4⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
  norm_num [Counts.total] at h
  convert h using 1 <;> norm_num

/-- Rejection certificate for possible tables outside the proposed interval. -/
theorem bounds_obs_1_2_12_5 : endpointBoundsCheck (109/500) ⟨1,2,12,5⟩ (-12) (0) = true := by
  decide +kernel

theorem interval_obs_1_2_12_5 : intervalQ (109/500) ⟨1,2,12,5⟩ = some (-3/5,0) := by
  have h := intervalQ_eq_of_endpoint_certificate (109/500) ⟨1,2,12,5⟩ (-12) (0) bounds_obs_1_2_12_5
    ⟨⟨2,0,12,6⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
    ⟨⟨9,3,3,5⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
  norm_num [Counts.total] at h
  convert h using 1 <;> norm_num

/-- Rejection certificate for possible tables outside the proposed interval. -/
theorem bounds_obs_1_2_11_6 : endpointBoundsCheck (109/500) ⟨1,2,11,6⟩ (-11) (1) = true := by
  decide +kernel

theorem interval_obs_1_2_11_6 : intervalQ (109/500) ⟨1,2,11,6⟩ = some (-11/20,1/20) := by
  have h := intervalQ_eq_of_endpoint_certificate (109/500) ⟨1,2,11,6⟩ (-11) (1) bounds_obs_1_2_11_6
    ⟨⟨2,0,11,7⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
    ⟨⟨8,4,3,5⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
  norm_num [Counts.total] at h
  convert h using 1 <;> norm_num

/-- Rejection certificate for possible tables outside the proposed interval. -/
theorem bounds_obs_2_1_12_5 : endpointBoundsCheck (109/500) ⟨2,1,12,5⟩ (-8) (4) = true := by
  decide +kernel

theorem interval_obs_2_1_12_5 : intervalQ (109/500) ⟨2,1,12,5⟩ = some (-2/5,1/5) := by
  have h := intervalQ_eq_of_endpoint_certificate (109/500) ⟨2,1,12,5⟩ (-8) (4) bounds_obs_2_1_12_5
    ⟨⟨5,1,9,5⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
    ⟨⟨10,6,2,2⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
  norm_num [Counts.total] at h
  convert h using 1 <;> norm_num

/-- Rejection certificate for possible tables outside the proposed interval. -/
theorem bounds_obs_2_1_11_6 : endpointBoundsCheck (109/500) ⟨2,1,11,6⟩ (-7) (5) = true := by
  decide +kernel

theorem interval_obs_2_1_11_6 : intervalQ (109/500) ⟨2,1,11,6⟩ = some (-7/20,1/4) := by
  have h := intervalQ_eq_of_endpoint_certificate (109/500) ⟨2,1,11,6⟩ (-7) (5) bounds_obs_2_1_11_6
    ⟨⟨6,0,7,7⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
    ⟨⟨10,6,1,3⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
  norm_num [Counts.total] at h
  convert h using 1 <;> norm_num

/-- Rejection certificate for possible tables outside the proposed interval. -/
theorem bounds_obs_3_0_11_6 : endpointBoundsCheck (109/500) ⟨3,0,11,6⟩ (-2) (8) = true := by
  decide +kernel

theorem interval_obs_3_0_11_6 : intervalQ (109/500) ⟨3,0,11,6⟩ = some (-1/10,2/5) := by
  have h := intervalQ_eq_of_endpoint_certificate (109/500) ⟨3,0,11,6⟩ (-2) (8) bounds_obs_3_0_11_6
    ⟨⟨10,1,3,6⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
    ⟨⟨10,9,1,0⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
  norm_num [Counts.total] at h
  convert h using 1 <;> norm_num

/-- Rejection certificate for possible tables outside the proposed interval. -/
theorem bounds_obs_0_3_10_7 : endpointBoundsCheck (109/500) ⟨0,3,10,7⟩ (-13) (-4) = true := by
  decide +kernel

theorem interval_obs_0_3_10_7 : intervalQ (109/500) ⟨0,3,10,7⟩ = some (-13/20,-1/5) := by
  have h := intervalQ_eq_of_endpoint_certificate (109/500) ⟨0,3,10,7⟩ (-13) (-4) bounds_obs_0_3_10_7
    ⟨⟨0,0,13,7⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
    ⟨⟨5,1,5,9⟩, by decide +kernel,
      (level_accepted_spec _ _ _).mp (by decide +kernel), by norm_num [Counts.effect]⟩
  norm_num [Counts.total] at h
  convert h using 1 <;> norm_num


theorem bad_random_states_certificate : randomStates badPopulation 3 = [⟨0,0,0,3⟩,⟨0,0,1,2⟩,⟨0,0,2,1⟩,⟨0,0,3,0⟩,⟨1,0,0,2⟩,⟨1,0,1,1⟩,⟨1,0,2,0⟩,⟨2,0,0,1⟩,⟨2,0,1,0⟩,⟨3,0,0,0⟩] := by
  decide +kernel

theorem bad_multiplicities_certificate :
    ((randomStates badPopulation 3).map (multiplicity badPopulation)).sum = 1140 := by
  decide +kernel

theorem critical_missing_interval_certificate :
    missingIntervalQ (109/500) ⟨0,3,11,6⟩ ⟨0,0,1,0⟩ = (-7/10,-1/5) := by
  norm_num [missingIntervalQ, minusCompletion, plusCompletion,
    interval_obs_0_3_11_6, interval_obs_0_3_10_7, estimateQ]

theorem critical_completions_certificate : completions ⟨0,3,11,6⟩ ⟨0,0,1,0⟩ =
    [⟨0,3,10,7⟩,⟨0,3,11,6⟩] := by decide +kernel

theorem zero_mask_completions_certificate (o : Counts) :
    completions o ⟨0,0,0,0⟩ = [o] := by
  cases o
  simp [completions, List.range_succ]

theorem badCoverage_certificate : badCoverage = 297/380 := by
  unfold badCoverage
  rw [bad_random_states_certificate]
  norm_num [observed, badMask,
    missingIntervalQ, minusCompletion, plusCompletion,
    interval_obs_0_3_14_3,
    interval_obs_0_3_13_4,
    interval_obs_0_3_12_5,
    interval_obs_0_3_11_6,
    interval_obs_1_2_13_4,
    interval_obs_1_2_12_5,
    interval_obs_1_2_11_6,
    interval_obs_2_1_12_5,
    interval_obs_2_1_11_6,
    interval_obs_3_0_11_6,
    interval_obs_0_3_10_7,
    estimateQ, tauQ, badPopulation, Counts.effect, Counts.total, multiplicity, binomial, Nat.fast_choose]

end MissingCounterexampleCompletion

/-- T1: the complete counterexample to Proposition 6.2, including both
    extremal inversions, the noncovering imputation interval and actual coverage.
    n=20, m=3, α=109/500 satisfy every standing design hypothesis. -/
theorem missing_counterexample :
    badPopulation.total = 20 ∧ (20 : ℕ).choose 3 = 1140 ∧ 0 < (3 : ℕ) ∧ (3 : ℕ) < 20 ∧
    (0 : ℚ) < 109/500 ∧ (109/500 : ℚ) < 1 ∧
    tauQ badPopulation = -3/20 ∧
    intervalQ (109/500) ⟨0,3,11,6⟩ = some (-7/10, -3/20) ∧
    intervalQ (109/500) ⟨0,3,10,7⟩ = some (-13/20, -1/5) ∧
    missingIntervalQ (109/500) ⟨0,3,11,6⟩ ⟨0,0,1,0⟩ = (-7/10,-1/5) ∧
    badCoverage = 297/380 ∧ badCoverage < 1 - (109/500 : ℚ) ∧
    ((randomStates badPopulation 3).map (multiplicity badPopulation)).sum = 1140 ∧
    (∀ q, badMask q ∈ missingMasks (observed badPopulation q)) := by
  refine ⟨rfl, by decide +kernel, by omega, by omega, by norm_num, by norm_num,
    ?_, critical_interval, interval_obs_0_3_10_7, critical_missing_interval_certificate,
    badCoverage_certificate, ?_, bad_multiplicities_certificate, bad_mask_legal⟩
  · norm_num [tauQ, badPopulation, Counts.effect, Counts.total]
  · rw [badCoverage_certificate]
    norm_num


/-- T3's pointwise union-to-hull inclusion, corrected (D.2). -/
theorem completion_union_subset_hull (α : ℝ) (o r : Counts) :
    completionUnion α o r ⊆ completionHull α o r := by
  intro t ht
  exact ⟨t, ht, t, ht, le_rfl, le_rfl⟩


/-- "c=⌊(a+b)/2⌋; if f(c)=0 set a=c; otherwise b=c", Algorithm B.1, p. 20.
    true means rejection (the printed value 1). -/
def searchStep (f : ℤ → Bool) (a b : ℤ) : ℤ × ℤ :=
  let c := (a+b)/2
  if f c then (a,c) else (c,b)

/-- Printed Step 3, p. 20, with return ending the algorithm and clauses in printed order. -/
def printedReturn (k₁ k₂ a b : ℤ) (f : ℤ → Bool) : Option ℤ :=
  if b = a+1 then
    if a > k₁ ∧ b < k₂ then some a
    else if a = k₁ then some (if f k₁ then k₁-1 else k₁)
    else if b = k₂ then some (if f k₂ then k₂-1 else k₂)
    else none
  else none

/-- Iterate the printed Step 2, including the post-step termination test of Step 3. -/
def printedSearch (fuel : ℕ) (k₁ k₂ : ℤ) (f : ℤ → Bool) (a b : ℤ) : Option ℤ :=
  match fuel with
  | 0 => none
  | t+1 =>
    let s := searchStep f a b
    match printedReturn k₁ k₂ s.1 s.2 f with
    | some r => some r
    | none => printedSearch t k₁ k₂ f s.1 s.2

/-- T4(A,B): legal two-point domains: all-accept returns 1 instead of 2;
    all-reject reaches the absorbing (1,1) state and never terminates. -/
theorem printed_search_counterexample :
    (0 : ℤ) < 1 ∧ (1 : ℤ) < 2 ∧
    (∀ x : ℤ, 1 ≤ x → x ≤ 2 → ((fun _ => false) x = false ↔ x ≤ 2)) ∧
    (∀ x : ℤ, 1 ≤ x → x ≤ 2 → ((fun _ => true) x = false ↔ x ≤ 0)) ∧
    printedSearch 1 1 2 (fun _ => false) 1 2 = some 1 ∧
    printedSearch 1 1 2 (fun _ => false) 1 2 ≠ some 2 ∧
    searchStep (fun _ => true) 1 2 = (1,1) ∧
    (∀ fuel, printedSearch fuel 1 2 (fun _ => true) 1 1 = none) ∧
    (∀ fuel, printedSearch fuel 1 2 (fun _ => true) 1 2 = none) := by
  have habs : ∀ fuel, printedSearch fuel 1 2 (fun _ => true) 1 1 = none := by
    intro fuel
    induction fuel with
    | zero => rfl
    | succ fuel ih => simpa [printedSearch,searchStep,printedReturn] using ih
  refine ⟨by norm_num,by norm_num,?_,?_,by decide,by decide,by decide,habs,?_⟩
  · intro x hx hx'
    simp only [Bool.false_eq_true, not_false_eq_true, true_iff]
    exact hx'
  · intro x hx hx'
    simp only [Bool.true_eq_false, false_iff]
    omega
  · intro fuel
    cases fuel with
    | zero => rfl
    | succ fuel => simpa [printedSearch,searchStep,printedReturn] using habs fuel


/-- Corrected B.1 (T5): while b>a+1 use the interior midpoint, otherwise return a.
    The fuel bounds only the representation; starting with width d+1, d+1 fuel suffices. -/
def sentinelSearch (fuel : ℕ) (f : ℤ → Bool) (a b : ℤ) : ℤ × List ℤ :=
  match fuel with
  | 0 => (a,[])
  | t+1 =>
    if b ≤ a+1 then (a,[]) else
      let c := (a+b)/2
      let next := if f c then sentinelSearch t f a c else sentinelSearch t f c b
      (next.1, c :: next.2)

/-- T5/T23 finite invariant of the repaired search, at every fuel bound:
    all queries are interior and distinct, and a rejected query cuts off itself
    and every larger query. No threshold or probability assumption is needed. -/
theorem sentinel_search_invariants (fuel : ℕ) (f : ℤ → Bool) (a b : ℤ)
    (hab : a < b) :
    let s := sentinelSearch fuel f a b
    a ≤ s.1 ∧ s.1 < b ∧ s.2.Nodup ∧
    (∀ c ∈ s.2, a < c ∧ c < b ∧ (f c = true → s.1 < c)) ∧
    s.2.Pairwise (fun c d => f c = true → d < c) := by
  induction fuel generalizing a b with
  | zero =>
    simpa [sentinelSearch] using
      (show a ≤ a ∧ a < b ∧ ([] : List ℤ).Nodup ∧
        (∀ c ∈ ([] : List ℤ), a < c ∧ c < b ∧ (f c = true → a < c)) ∧
        ([] : List ℤ).Pairwise (fun c d => f c = true → d < c) from
        ⟨le_rfl,hab,by simp,by simp,by simp⟩)
  | succ fuel ih =>
    by_cases hstop : b ≤ a+1
    · simpa [sentinelSearch,hstop] using
        (show a ≤ a ∧ a < b ∧ ([] : List ℤ).Nodup ∧
          (∀ c ∈ ([] : List ℤ), a < c ∧ c < b ∧ (f c = true → a < c)) ∧
          ([] : List ℤ).Pairwise (fun c d => f c = true → d < c) from
          ⟨le_rfl,hab,by simp,by simp,by simp⟩)
    · let c := (a+b)/2
      have hac : a < c := by dsimp [c]; omega
      have hcb : c < b := by dsimp [c]; omega
      by_cases hf : f c = true
      · have hi := ih a c hac
        simp only [sentinelSearch,if_neg hstop,show (a+b)/2 = c from rfl,if_pos hf]
        refine ⟨hi.1,lt_trans hi.2.1 hcb,?_,?_,?_⟩
        · apply List.nodup_cons.mpr
          refine ⟨?_,hi.2.2.1⟩
          intro hc
          have hh := (hi.2.2.2.1 c hc).2.1
          exact (lt_irrefl c) hh
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact ⟨hac,hcb,fun _ => hi.2.1⟩
          · have hh := hi.2.2.2.1 d hd
            exact ⟨hh.1,lt_trans hh.2.1 hcb,hh.2.2⟩
        · apply List.pairwise_cons.mpr
          exact ⟨fun d hd _ => (hi.2.2.2.1 d hd).2.1,hi.2.2.2.2⟩
      · have hi := ih c b hcb
        simp only [sentinelSearch,if_neg hstop,show (a+b)/2 = c from rfl,if_neg hf]
        refine ⟨le_trans hac.le hi.1,hi.2.1,?_,?_,?_⟩
        · apply List.nodup_cons.mpr
          refine ⟨?_,hi.2.2.1⟩
          intro hc
          have hh := (hi.2.2.2.1 c hc).1
          exact (lt_irrefl c) hh
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact ⟨hac,hcb,fun he => False.elim (hf he)⟩
          · have hh := hi.2.2.2.1 d hd
            exact ⟨lt_trans hac hh.1,hh.2.1,hh.2.2⟩
        · apply List.pairwise_cons.mpr
          exact ⟨fun d hd he => False.elim (hf he),hi.2.2.2.2⟩


/-- Correctness of the repaired B.1 search from its finite width invariant,
for thresholds `a ≤ r < b`, including the lower unevaluated sentinel, target T5. -/
theorem sentinel_threshold_return (fuel : ℕ) (f : ℤ → Bool) (a b r : ℤ)
    (hab : a < b) (hw : (b-a).toNat ≤ fuel+1) (hr : a ≤ r ∧ r < b)
    (hf : ∀ x, a < x → x < b → (f x = false ↔ x ≤ r)) :
    (sentinelSearch fuel f a b).1 = r := by
  induction fuel generalizing a b with
  | zero =>
    have har : a = r := by omega
    simpa [sentinelSearch] using har
  | succ fuel ih =>
    by_cases hstop : b ≤ a+1
    · have har : a = r := by omega
      simpa [sentinelSearch,hstop] using har
    · let c := (a+b)/2
      have hac : a < c := by dsimp [c]; omega
      have hcb : c < b := by dsimp [c]; omega
      by_cases hfc : f c = true
      · have hrc : r < c := by
          have hn : ¬ f c = false := by simp [hfc]
          exact lt_of_not_ge (fun h => hn ((hf c hac hcb).mpr h))
        simp only [sentinelSearch,if_neg hstop,show (a+b)/2 = c from rfl,if_pos hfc]
        exact ih a c hac (by omega) ⟨hr.1,hrc⟩
          (fun x hax hxc => hf x hax (lt_trans hxc hcb))
      · have hcr : c ≤ r := (hf c hac hcb).mp (Bool.eq_false_iff.mpr hfc)
        simp only [sentinelSearch,if_neg hstop,show (a+b)/2 = c from rfl,if_neg hfc]
        exact ih c b hcb (by omega) ⟨hcr,hr.2⟩
          (fun x hcx hxb => hf x (lt_trans hac hcx) hxb)


/-- Each repaired B.1 query halves the sentinel width: a width at most 2^q
    permits at most q evaluations, even for arbitrary Monte Carlo decisions (T5). -/
theorem sentinel_queries_le_pow (q fuel : ℕ) (f : ℤ → Bool) (a b : ℤ)
    (hw : b-a ≤ (2 : ℤ)^q) :
    (sentinelSearch fuel f a b).2.length ≤ q := by
  induction q generalizing fuel a b with
  | zero =>
    have hs : b ≤ a+1 := by simp only [pow_zero] at hw; omega
    cases fuel <;> simp [sentinelSearch,hs]
  | succ q ih =>
    cases fuel with
    | zero => simp [sentinelSearch]
    | succ fuel =>
      by_cases hs : b ≤ a+1
      · simp [sentinelSearch,hs]
      · let c := (a+b)/2
        have hp : (2 : ℤ)^(q+1) = 2*(2 : ℤ)^q := by ring
        rw [hp] at hw
        have hl : c-a ≤ (2 : ℤ)^q := by dsimp [c]; omega
        have hr : b-c ≤ (2 : ℤ)^q := by dsimp [c]; omega
        by_cases hf : f c = true
        · simpa only [sentinelSearch,if_neg hs,show (a+b)/2 = c from rfl,
            if_pos hf,List.length_cons] using Nat.succ_le_succ (ih fuel a c hl)
        · simpa only [sentinelSearch,if_neg hs,show (a+b)/2 = c from rfl,
            if_neg hf,List.length_cons] using Nat.succ_le_succ (ih fuel c b hr)


/-- The real base-2 logarithm, "log₂" (notation paragraph p. 5). -/
noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- T5: query validity, termination and the same logarithmic count hold for
    arbitrary noisy decisions as well; no threshold hypothesis is imposed. -/
theorem noisy_search_budget (k₁ k₂ : ℤ) (f : ℤ → Bool) (hk : k₁ ≤ k₂) :
    let d := (k₂-k₁+1).toNat
    let s := sentinelSearch (d+1) f (k₁-1) (k₂+1)
    s.2.Nodup ∧ (∀ x ∈ s.2, k₁ ≤ x ∧ x ≤ k₂) ∧
      (s.2.length : ℝ) ≤ (⌊logTwo d⌋ : ℤ) + 1 ∧ k₁-1 ≤ s.1 ∧ s.1 ≤ k₂ := by
  dsimp only
  let d := (k₂-k₁+1).toNat
  have hd : 0 < d := by dsimp [d]; omega
  have hcast : (d : ℤ) = k₂-k₁+1 := by dsimp [d]; omega
  have hi := sentinel_search_invariants (d+1) f (k₁-1) (k₂+1) (by omega)
  have hpowN := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) d
  have hpow : (d : ℤ) < (2 : ℤ)^(Nat.log 2 d+1) := by exact_mod_cast hpowN
  have hlen := sentinel_queries_le_pow (Nat.log 2 d+1) (d+1) f
    (k₁-1) (k₂+1) (by omega)
  have hfloor : ⌊logTwo (d : ℝ)⌋ = (Nat.log 2 d : ℤ) := by
    change ⌊Real.logb (2 : ℝ) (d : ℝ)⌋ = _
    simpa only [Nat.cast_ofNat,Int.log_natCast] using
      (Real.floor_logb_natCast (b := 2) (r := (d : ℝ)) (by positivity))
  refine ⟨hi.2.2.1,?_,?_,hi.1,?_⟩
  · intro x hx
    have hb := hi.2.2.2.1 x hx
    omega
  · rw [hfloor]
    exact_mod_cast hlen
  · change (sentinelSearch (d+1) f (k₁-1) (k₂+1)).1 ≤ k₂
    have hb := hi.2.1
    omega


/-- T5: correctness, integer/singleton domains, no repeated queries, the sharp
    floor(log₂ d)+1 query bound, for the sentinel correction of B.1. -/
theorem corrected_search (k₁ k₂ r : ℤ) (f : ℤ → Bool)
    (hk : k₁ ≤ k₂) (hr : k₁-1 ≤ r ∧ r ≤ k₂)
    (hf : ∀ x, k₁ ≤ x → x ≤ k₂ → (f x = false ↔ x ≤ r)) :
    let d := (k₂-k₁+1).toNat
    let s := sentinelSearch (d+1) f (k₁-1) (k₂+1)
    s.1 = r ∧ s.2.Nodup ∧ (∀ x ∈ s.2, k₁ ≤ x ∧ x ≤ k₂) ∧
      (s.2.length : ℝ) ≤ (⌊logTwo d⌋ : ℤ) + 1 := by
  dsimp only
  let d := (k₂-k₁+1).toNat
  have hb := noisy_search_budget k₁ k₂ f hk
  have he := sentinel_threshold_return (d+1) f (k₁-1) (k₂+1) r
    (by omega) (by dsimp [d]; omega) ⟨hr.1,by omega⟩
    (fun x h₁ h₂ => hf x (by omega) (by omega))
  exact ⟨he,hb.1,hb.2.1,hb.2.2.1⟩


/-- T11: in the n=2,m=1, all-zero population the exact real tail q(x)
    is 1 on x≤0 and 0 on x>0; the rejecting real half-line has no minimum. -/
theorem real_threshold_counterexample :
    let q : ℝ → ℝ := fun x => if x ≤ 0 then 1 else 0
    (∀ x, q x < 1/2 ↔ 0 < x) ∧
    (∃ x, q x < 1/2) ∧ ¬ ∃ x, q x < 1/2 ∧ ∀ u, q u < 1/2 → x ≤ u := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ≤ 0
    · simp only [if_pos hx]
      constructor
      · intro h; norm_num at h
      · intro h; linarith
    · simp only [if_neg hx]
      constructor
      · intro h; exact lt_of_not_ge hx
      · intro h; norm_num
  · exact ⟨1, by norm_num⟩
  · rintro ⟨x, hx, hmin⟩
    have hpos : 0 < x := by
      by_contra h
      have hx0 : x ≤ 0 := le_of_not_gt h
      norm_num [hx0] at hx
    have hu : (if x/2 ≤ 0 then (1 : ℝ) else 0) < 1/2 := by
      rw [if_neg (by linarith : ¬ x/2 ≤ 0)]
      norm_num
    have := hmin (x/2) hu
    linarith


/-- Tail of a real statistic on a finite probability space, repaired (A.9)-(A.10), p. 19. -/
noncomputable def finiteTail {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (D : Ω → ℝ)
    (x : ℝ) : ℝ := ∑ i, if x ≤ D i then w i else 0

/-- T12 supporting bound: choose the smallest rejecting attained value, including the empty case;
    the exact rejection event is a support tail and its probability is < α. -/
theorem finite_tail_repair {Ω : Type*} [Fintype Ω] (w D : Ω → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1) (α : ℝ) (hα : 0 < α ∧ α < 1) :
    ((∀ i, α ≤ finiteTail w D (D i)) ∨
      ∃ i, finiteTail w D (D i) < α ∧
        (∀ j, finiteTail w D (D j) < α ↔ D i ≤ D j) ∧
        (∑ j, if finiteTail w D (D j) < α then w j else 0) = finiteTail w D (D i)) ∧
    (∑ j, if finiteTail w D (D j) < α then w j else 0) < α := by
  classical
  let s := Finset.univ.filter (fun i => finiteTail w D (D i) < α)
  have mono : ∀ x y : ℝ, x ≤ y → finiteTail w D y ≤ finiteTail w D x := by
    intro x y hxy
    unfold finiteTail
    apply Finset.sum_le_sum
    intro i hi
    by_cases hy : y ≤ D i
    · have hx : x ≤ D i := le_trans hxy hy
      simp [hy,hx]
    · simp only [if_neg hy]
      by_cases hx : x ≤ D i
      · simp [hx,hw i]
      · simp [hx]
  by_cases hs : s.Nonempty
  · obtain ⟨i, hi, hmin⟩ := s.exists_min_image D hs
    have hir : finiteTail w D (D i) < α := (Finset.mem_filter.mp hi).2
    have heq : ∀ j, finiteTail w D (D j) < α ↔ D i ≤ D j := by
      intro j
      constructor
      · intro hj
        exact hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
      · intro hj
        exact lt_of_le_of_lt (mono _ _ hj) hir
    have hsum : (∑ j, if finiteTail w D (D j) < α then w j else 0) =
        finiteTail w D (D i) := by
      change (∑ j, if finiteTail w D (D j) < α then w j else 0) =
        ∑ j, if D i ≤ D j then w j else 0
      apply Finset.sum_congr rfl
      intro j hj
      simp only [heq j]
    exact ⟨Or.inr ⟨i,hir,heq,hsum⟩, hsum ▸ hir⟩
  · have hnone : ∀ i, ¬ finiteTail w D (D i) < α := by
      intro i hi
      exact hs ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    refine ⟨Or.inl (fun i => le_of_not_gt (hnone i)), ?_⟩
    simpa only [if_neg (hnone _), Finset.sum_const_zero] using hα.1


/-- T12: repaired (A.10), p. 19, on the actual finite support. Each represented
    atom has positive mass, so the smallest rejecting attained statistic is a
    genuine support value. No rejection gives the empty event; otherwise that
    event equals a support tail with probability strictly below α. -/
theorem finite_tail_support_repair {Ω : Type*} [Fintype Ω] (w D : Ω → ℝ)
    (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1) (α : ℝ) (hα : 0 < α ∧ α < 1) :
    ((∀ i, α ≤ finiteTail w D (D i)) ∨
      ∃ i, 0 < w i ∧ finiteTail w D (D i) < α ∧
        (∀ j, finiteTail w D (D j) < α ↔ D i ≤ D j) ∧
        (∑ j, if finiteTail w D (D j) < α then w j else 0) = finiteTail w D (D i)) ∧
    (∑ j, if finiteTail w D (D j) < α then w j else 0) < α := by
  have h := finite_tail_repair w D (fun i => (hw i).le) hn α hα
  rcases h.1 with hnone | ⟨i,hi,he,hs⟩
  · exact ⟨Or.inl hnone,h.2⟩
  · exact ⟨Or.inr ⟨i,hw i,hi,he,hs⟩,h.2⟩

/-- "w∈{(0,0),(0,1),(1,0),(1,1)}ⁿ", (2.1), p. 5. -/
abbrev PotentialTable (n : ℕ) := Fin n → Bool × Bool

/-- Binary outcomes are represented by Bool and interpreted as 0 or 1. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- Unit-level count definition (2.2), p. 5. -/
def tableCounts {n : ℕ} (w : PotentialTable n) : Counts :=
  ⟨(Finset.univ.filter fun i => w i = (true,true)).card,
   (Finset.univ.filter fun i => w i = (true,false)).card,
   (Finset.univ.filter fun i => w i = (false,true)).card,
   (Finset.univ.filter fun i => w i = (false,false)).card⟩

/-- The unit-level average treatment effect (2.6), p. 5. -/
noncomputable def tableTau {n : ℕ} (w : PotentialTable n) : ℝ :=
  (∑ i, (bit (w i).1 - bit (w i).2)) / n

/-- Corrected θ of (5.6), p. 11, is the SATE, with numerator v₁₀−v₀₁. -/
theorem corrected_sate {n : ℕ} (w : PotentialTable n) (hn : 0 < n) :
    (tableCounts w).total = n ∧
    (∑ i, bit (w i).1) = (tableCounts w).a + (tableCounts w).b ∧
    (∑ i, bit (w i).2) = (tableCounts w).a + (tableCounts w).c ∧
    tableTau w = tau (tableCounts w) := by
  classical
  have h1 : (∑ i, bit (w i).1) = (tableCounts w).a + (tableCounts w).b := by
    calc
      _ = ∑ i, ((if w i = (true,true) then (1 : ℝ) else 0) +
          (if w i = (true,false) then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rcases h : w i with ⟨a,b⟩
        cases a <;> cases b <;> simp [bit,h]
      _ = _ := by simp [Finset.sum_add_distrib,tableCounts]
  have h0 : (∑ i, bit (w i).2) = (tableCounts w).a + (tableCounts w).c := by
    calc
      _ = ∑ i, ((if w i = (true,true) then (1 : ℝ) else 0) +
          (if w i = (false,true) then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rcases h : w i with ⟨a,b⟩
        cases a <;> cases b <;> simp [bit,h]
      _ = _ := by simp [Finset.sum_add_distrib,tableCounts]
  have ht : ((tableCounts w).total : ℝ) = n := by
    calc
      _ = ∑ i, ((if w i = (true,true) then (1 : ℝ) else 0) +
          (if w i = (true,false) then (1 : ℝ) else 0) +
          (if w i = (false,true) then (1 : ℝ) else 0) +
          (if w i = (false,false) then (1 : ℝ) else 0)) := by
        simp [Finset.sum_add_distrib,tableCounts,Counts.total]
      _ = ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rcases h : w i with ⟨a,b⟩
        cases a <;> cases b <;> simp [h]
      _ = _ := by simp
  have htn : (tableCounts w).total = n := by exact_mod_cast ht
  refine ⟨htn,h1,h0,?_⟩
  simp only [tableTau,Finset.sum_sub_distrib,h1,h0,tau,tauQ,Counts.effect,
    Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,Rat.cast_sub,Int.cast_sub,Int.cast_natCast,htn]
  congr 1
  push_cast
  ring


/-- T13's two concrete witnesses to the wrong printed numerator. -/
theorem printed_sate_witnesses :
    tauQ ⟨10,0,0,10⟩ = 0 ∧ ((10 : ℚ)-0)/20 = 1/2 ∧
    tauQ ⟨0,20,0,0⟩ = 1 ∧ ((0 : ℚ)-0)/20 = 0 := by
  norm_num [tauQ,Counts.effect,Counts.total]


/-- Corrected (A.2)-(A.3), p. 18. c₂ is twice the centre; restricting
    c₂≤2i puts comparisons on the right of the centre, including half-integers. -/
def SDShape (f : ℤ → ℝ) (c₂ : ℤ) : Prop :=
  (∀ i, f (c₂-i) = f i) ∧ (∀ i j, c₂ ≤ 2*i → i ≤ j → f j ≤ f i)

/-- "Let f : ℤ → ℝ≥0 be a probability mass function", Definition A.1, p. 18.
    This predicate imposes no first-moment assumption; the paper adds that only for SD. -/
def IsPMF (f : ℤ → ℝ) : Prop :=
  (∀ i, 0 ≤ f i) ∧ Summable f ∧ (∑' i, f i) = 1

/-- "f is a probability mass function" and "the mean … exists", Definition A.1,
    p. 18: real nonnegative masses summing to 1, with absolutely summable first moment. -/
def IsMass (f : ℤ → ℝ) : Prop :=
  (∀ i, 0 ≤ f i) ∧ Summable f ∧ (∑' i, f i) = 1 ∧
    Summable (fun i : ℤ => (i : ℝ) * f i)

/-- "SD … symmetric about k₀=∑ k f(k) and decreasing away from k₀",
    corrected Definition A.1, p. 18. The centre may be a half-integer. -/
def IsSD (f : ℤ → ℝ) : Prop :=
  IsMass f ∧ ∃ c₂ : ℤ, (∑' i : ℤ, (i : ℝ) * f i) = (c₂ : ℝ)/2 ∧ SDShape f c₂

/-- The uniform law on {0,1}, used in Lemma B.5 and targets T9,T10,T14. -/
noncomputable def fairMass (i : ℤ) : ℝ :=
  (if i = 0 then 1/2 else 0) + (if i = 1 then 1/2 else 0)

/-- T9(A): on two equiprobable atoms X₁=X₂∈{0,1}, so their sum has masses
    1/2 at 0 and 2, with a hole at its mean 1. -/
noncomputable def dependentSumMass (i : ℤ) : ℝ :=
  (if i = 0 then 1/2 else 0) + (if i = 2 then 1/2 else 0)

/-- Corrected A.1 example: the fair {0,1} distribution has mean 1/2 and is SD. -/
theorem fair_mass_sd : IsSD fairMass ∧ (∑' i : ℤ, (i : ℝ)*fairMass i) = 1/2 := by
  have hp : ∀ i, 0 ≤ fairMass i := by
    intro i
    unfold fairMass
    split_ifs <;> norm_num
  have hs : HasSum fairMass 1 := by
    convert (hasSum_ite_eq (0 : ℤ) (1/2 : ℝ)).add
      (hasSum_ite_eq (1 : ℤ) (1/2 : ℝ)) using 1
    · rfl
    · norm_num
  have hfun : (fun i : ℤ => (i : ℝ)*fairMass i) =
      (fun i => if i = 1 then (1/2 : ℝ) else 0) := by
    funext i
    by_cases h0 : i = 0
    · subst i; norm_num [fairMass]
    by_cases h1 : i = 1
    · subst i; norm_num [fairMass]
    simp [fairMass,h0,h1]
  have hm : HasSum (fun i : ℤ => (i : ℝ)*fairMass i) (1/2) := by
    rw [hfun]
    exact hasSum_ite_eq (1 : ℤ) (1/2 : ℝ)
  refine ⟨⟨⟨hp,hs.summable,hs.tsum_eq,hm.summable⟩,1,?_,?_⟩,hm.tsum_eq⟩
  · simpa using hm.tsum_eq
  · constructor
    · intro i
      by_cases h0 : i = 0
      · subst i; norm_num [fairMass]
      by_cases h1 : i = 1
      · subst i; norm_num [fairMass]
      have h0' : 1-i ≠ 0 := by omega
      have h1' : 1-i ≠ 1 := by omega
      simp [fairMass,h0,h1,h0',h1']
    · intro i j hi hij
      by_cases hj : j = 1
      · have hi' : i = 1 := by omega
        subst i; subst j; exact le_rfl
      have hj0 : j ≠ 0 := by omega
      simpa [fairMass,hj,hj0] using hp i


/-- T9: both printed marginals satisfy Lemma B.5 (m=1), but their dependent sum
    is not SD. The joint law is explicitly {(0,0):1/2,(1,1):1/2}. -/
theorem dependent_convolution_counterexample :
    IsSD fairMass ∧ (∑' i : ℤ, (i : ℝ)*fairMass i) = 1/2 ∧
    IsMass dependentSumMass ∧ (∑' i : ℤ, (i : ℝ)*dependentSumMass i) = 1 ∧
    dependentSumMass 1 = 0 ∧ dependentSumMass 2 = 1/2 ∧
    ¬ IsSD dependentSumMass := by
  have hp : ∀ i, 0 ≤ dependentSumMass i := by
    intro i
    unfold dependentSumMass
    split_ifs <;> norm_num
  have hs : HasSum dependentSumMass 1 := by
    convert (hasSum_ite_eq (0 : ℤ) (1/2 : ℝ)).add
      (hasSum_ite_eq (2 : ℤ) (1/2 : ℝ)) using 1
    · rfl
    · norm_num
  have hfun : (fun i : ℤ => (i : ℝ)*dependentSumMass i) =
      (fun i => if i = 2 then (1 : ℝ) else 0) := by
    funext i
    by_cases h0 : i = 0
    · subst i; norm_num [dependentSumMass]
    by_cases h2 : i = 2
    · subst i; norm_num [dependentSumMass]
    simp [dependentSumMass,h0,h2]
  have hm : HasSum (fun i : ℤ => (i : ℝ)*dependentSumMass i) 1 := by
    rw [hfun]
    exact hasSum_ite_eq (2 : ℤ) (1 : ℝ)
  refine ⟨fair_mass_sd.1,fair_mass_sd.2,⟨hp,hs.summable,hs.tsum_eq,hm.summable⟩,
    hm.tsum_eq,by norm_num [dependentSumMass],by norm_num [dependentSumMass],?_⟩
  rintro ⟨hf,c,hmean,hshape⟩
  have hcR : (c : ℝ) = 2 := by rw [hm.tsum_eq] at hmean; linarith
  have hc : c = 2 := by exact_mod_cast hcR
  subst c
  have h := hshape.2 1 2 (by norm_num) (by norm_num)
  norm_num [dependentSumMass] at h


/-- Product-law convolution for independent X₁ and a fair {0,1} variable,
    the corrected B.5 proof (p. 23): g(x)=(f(x)+f(x−1))/2. Applying it
    to mX₁ gives exactly the result on m⁻¹ℤ, for every positive m. -/
noncomputable def smoothMass (f : ℤ → ℝ) (i : ℤ) : ℝ := (f i + f (i-1))/2

/-- The finite shape argument in corrected (B.43), p. 23, valid for every
    half-integer centre: independent fair smoothing shifts twice the centre by one. -/
theorem independent_convolution_shape (f : ℤ → ℝ) (c : ℤ) (hf : SDShape f c) :
    SDShape (smoothMass f) (c+1) := by
  constructor
  · intro i
    have h₁ := hf.1 (i-1)
    have h₀ := hf.1 i
    have he₁ : c-(i-1) = c+1-i := by ring
    have he₀ : c+1-i-1 = c-i := by ring
    rw [he₁] at h₁
    unfold smoothMass
    rw [he₀,h₁,h₀]
    ring
  · have hstep : ∀ b : ℤ, c+1 ≤ 2*b →
        smoothMass f (b+1) ≤ smoothMass f b := by
      intro b hb
      have hmass : f (b+1) ≤ f (b-1) := by
        by_cases hright : c ≤ 2*(b-1)
        · exact hf.2 (b-1) (b+1) hright (by omega)
        · have hmirror : f (c-(b-1)) = f (b-1) := hf.1 (b-1)
          have hm := hf.2 (c-(b-1)) (b+1) (by omega) (by omega)
          rwa [hmirror] at hm
      unfold smoothMass
      rw [show b+1-1 = b by ring]
      linarith
    intro i j hi hij
    exact Int.leInduction (motive := fun j _ => smoothMass f j ≤ smoothMass f i)
      le_rfl (fun j hji hval => le_trans (hstep j (by omega)) hval) j hij


/-- Corrected Lemma B.5, T10: independence is encoded by the product-law convolution. -/
theorem independent_convolution_sd (f : ℤ → ℝ) (hf : IsSD f) :
    IsSD (smoothMass f) := by
  rcases hf with ⟨⟨hp,hs,ht,hm⟩,c,hmean,hshape⟩
  let e : ℤ ≃ ℤ :=
    { toFun := fun i => i-1
      invFun := fun i => i+1
      left_inv := by intro i; dsimp; omega
      right_inv := by intro i; dsimp; omega }
  have hshift : Summable (fun i : ℤ => f (i-1)) := by
    simpa only [Function.comp_def,e,Equiv.coe_fn_mk] using hs.comp_injective e.injective
  have hmshift : Summable (fun i : ℤ => ((i-1 : ℤ) : ℝ)*f (i-1)) := by
    simpa only [Function.comp_def,e,Equiv.coe_fn_mk] using hm.comp_injective e.injective
  have hshiftSum : (∑' i : ℤ, f (i-1)) = 1 := by
    have he : (∑' i : ℤ, f (i-1)) = ∑' i : ℤ, f i := by simpa [e] using e.tsum_eq f
    exact he.trans ht
  have hmshiftSum : (∑' i : ℤ, ((i-1 : ℤ) : ℝ)*f (i-1)) =
      ∑' i : ℤ, (i : ℝ)*f i := by
    simpa [e] using e.tsum_eq (fun i : ℤ => (i : ℝ)*f i)
  have hshiftMomentFun : (fun i : ℤ => (i : ℝ)*f (i-1)) =
      (fun i => ((i-1 : ℤ) : ℝ)*f (i-1)+f (i-1)) := by
    funext i
    push_cast
    ring
  have hmshift' : Summable (fun i : ℤ => (i : ℝ)*f (i-1)) := by
    rw [hshiftMomentFun]
    exact hmshift.add hshift
  have hmshiftSum' : (∑' i : ℤ, (i : ℝ)*f (i-1)) =
      (∑' i : ℤ, (i : ℝ)*f i)+1 := by
    rw [hshiftMomentFun,hmshift.tsum_add hshift,hmshiftSum,hshiftSum]
  have hMomentFun : (fun i : ℤ => (i : ℝ)*smoothMass f i) =
      (fun i : ℤ => ((i : ℝ)*f i+(i : ℝ)*f (i-1))/2) := by
    funext i
    unfold smoothMass
    ring
  refine ⟨⟨?_,(hs.add hshift).div_const 2,?_,?_⟩,c+1,?_,
    independent_convolution_shape f c hshape⟩
  · intro i
    exact div_nonneg (add_nonneg (hp i) (hp (i-1))) (by norm_num)
  · change (∑' i : ℤ, (f i+f (i-1))/2) = 1
    rw [tsum_div_const,hs.tsum_add hshift,ht,hshiftSum]
    norm_num
  · rw [hMomentFun]
    exact (hm.add hmshift').div_const 2
  · rw [hMomentFun,tsum_div_const,hm.tsum_add hmshift',hmshiftSum',hmean]
    push_cast
    ring


/-- The auxiliary parity-lattice convolution at B.9, pp. 24-25: every coarse
    mass at p+2k is repeated with half its size at p+2k and p+2k+1. -/
noncomputable def paritySmooth (f : ℤ → ℝ) (p : ℤ) (i : ℤ) : ℝ := f ((i-p)/2)/2


/-- The erroneous unrestricted (A.3) is global nonincrease on all of ℤ. -/
def PrintedDecrease (f : ℤ → ℝ) : Prop := ∀ i j, i < j → f j ≤ f i

/-- Unit mass at zero, which must be SD under the corrected Definition A.1. -/
def zeroMass (i : ℤ) : ℝ := if i = 0 then 1 else 0

/-- T14: the unrestricted printed condition excludes every pmf, whereas the
    corrected definition includes unit mass at 0 and the fair {0,1} mass. -/
theorem corrected_sd_definition :
    (∀ f, IsPMF f → ¬ PrintedDecrease f) ∧ IsSD zeroMass ∧ IsSD fairMass ∧
      ¬ PrintedDecrease zeroMass := by
  have hz : IsSD zeroMass := by
    have hs : HasSum zeroMass 1 := by exact hasSum_ite_eq (0 : ℤ) (1 : ℝ)
    have hm : (fun i : ℤ => (i : ℝ)*zeroMass i) = 0 := by
      funext i
      by_cases h : i = 0
      · subst i; norm_num [zeroMass]
      · simp [zeroMass,h]
    refine ⟨⟨?_,hs.summable,hs.tsum_eq,?_⟩,0,?_,?_⟩
    · intro i; unfold zeroMass; split_ifs <;> norm_num
    · rw [hm]; exact summable_zero
    · rw [hm]
      simp only [Int.cast_zero,zero_div]
      change (∑' _i : ℤ, (0 : ℝ)) = 0
      exact tsum_zero
    · constructor
      · intro i; simp [zeroMass]
      · intro i j hi hij
        by_cases hj : j = 0
        · have hi' : i = 0 := by omega
          subst i; subst j; exact le_rfl
        · simp only [zeroMass,if_neg hj]
          split_ifs <;> norm_num
  refine ⟨?_,hz,fair_mass_sd.1,?_⟩
  · intro f hf hdec
    have hzero : f = 0 := by
      funext k
      have hinj : Function.Injective (fun n : ℕ => k-(n : ℤ)) := by
        intro a b hab
        dsimp at hab
        omega
      have hs : Summable (fun n : ℕ => f (k-(n : ℤ))) := hf.2.1.comp_injective hinj
      have hle : f k ≤ 0 := ge_of_tendsto' hs.tendsto_atTop_zero (fun n => by
        by_cases hn : n = 0
        · subst n; simp
        · exact hdec _ _ (by omega))
      exact le_antisymm hle (hf.1 k)
    have heq := hf.2.2
    rw [hzero] at heq
    simpa using heq
  · intro h
    have hh := h (-1) 0 (by norm_num)
    norm_num [zeroMass] at hh


/-- Corrected rescaling "g(j)=f(j/k)" in Definition A.1, p. 18.
    The lattice is indexed bijectively by integers, so a function on it is an
    integer-indexed pmf, and its physical mean is ∑(j/k)g(j). -/
noncomputable def latticeMean (k : ℕ) (g : ℤ → ℝ) : ℝ :=
  ∑' j : ℤ, ((j : ℝ)/(k : ℝ))*g j

/-- T14: rescaling preserves total probability and scales the mean by 1/k;
    k=2,X=1/2 shows the printed f(kj) samples only zero masses. -/
theorem corrected_lattice_rescaling (k : ℕ) (hk : 0 < k) (g : ℤ → ℝ)
    (hg : IsMass g) :
    (∑' j, g j) = 1 ∧ latticeMean k g = (∑' j : ℤ, (j : ℝ)*g j)/(k : ℝ) ∧
    (∀ j : ℤ, (if (2 : ℚ)*j = 1/2 then (1 : ℝ) else 0) = 0) := by
  refine ⟨hg.2.2.1,?_,?_⟩
  · unfold latticeMean
    simp_rw [div_mul_eq_mul_div]
    exact tsum_div_const
  · intro j
    apply if_neg
    intro h
    have hjQ : (4 : ℚ)*j = 1 := by linarith
    have hj : (4 : ℤ)*j = 1 := by exact_mod_cast hjQ
    omega


/-- pmf of mT, the integer lattice variable in Lemma B.12, pp. 25-26.
    The law is still the genuine weighted complete-randomization law (2.4). -/
noncomputable def scaledEstimatorMass (v : Counts) (m : ℕ) (j : ℤ) : ℝ :=
  designProb v m (fun q => (m : ℚ)*estimateQ (observed v q) = (j : ℚ))


/-- T15: the corrected induction covers d≥3 without requiring both discordant
    counts positive; removing any listed pair preserves at least one discordant unit. -/
theorem corrected_induction_counts (b c ab ac : ℕ) (hd : 3 ≤ b+c)
    (hab : ab ≤ b) (hac : ac ≤ c) (ha : ab+ac ≤ 2) :
    (2 ≤ b ∨ 2 ≤ c) ∧ 1 ≤ (b-ab)+(c-ac) := by
  omega


/-- The corrected signed contribution of a pair to mT, (B.47),(B.49), p. 24.
    true means the first unit is treated and the second is controlled. -/
def pairContribution (w₁ w₂ : Bool × Bool) (z : Bool) : ℤ :=
  if z then (if w₁.1 then 1 else 0) - (if w₂.2 then 1 else 0)
  else (if w₂.1 then 1 else 0) - (if w₁.2 then 1 else 0)

/-- T16: all six corrected pair laws; the two entries have probability 1/2 each. -/
theorem corrected_pair_laws :
    (pairContribution (true,false) (true,true) true,
      pairContribution (true,false) (true,true) false) = (0,1) ∧
    (pairContribution (true,false) (true,false) true,
      pairContribution (true,false) (true,false) false) = (1,1) ∧
    (pairContribution (true,false) (false,true) true,
      pairContribution (true,false) (false,true) false) = (0,0) ∧
    (pairContribution (true,false) (false,false) true,
      pairContribution (true,false) (false,false) false) = (1,0) ∧
    (pairContribution (true,true) (true,true) true,
      pairContribution (true,true) (true,true) false) = (0,0) ∧
    (pairContribution (true,true) (false,false) true,
      pairContribution (true,true) (false,false) false) = (1,-1) := by
  decide +kernel


/-- Unit-level Neyman estimator (2.7), p. 5; z is the set of treated labels.
    It is defined even at invalid designs, but theorem hypotheses exclude those. -/
noncomputable def tableEstimator {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) : ℝ :=
  (∑ i, if i ∈ z then bit (w i).1 else 0) / z.card -
    (∑ i, if i ∈ z then 0 else bit (w i).2) / (n-z.card)

/-- Corrected (B.50) including signs and normalization 1/m, T16. -/
theorem corrected_signed_sum {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n))
    (m : ℕ) (hm : 0 < m) (hn : n = 2*m) (hz : z.card = m) :
    tableEstimator w z = (∑ i, if i ∈ z then bit (w i).1 else -bit (w i).2)/(m : ℝ) := by
  unfold tableEstimator
  rw [hz]
  have hsub : (n : ℝ)-(m : ℝ) = (m : ℝ) := by rw [hn]; push_cast; ring
  rw [hsub, ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp


/-- Variance estimate "σ² = Q₁/m² + Q₀/(n−m)²", (5.9)-(5.11), p. 11,
    simplified for binary outcomes. The HC1 correction in T8 is separate. -/
noncomputable def varianceEstimate (o : Counts) : ℝ :=
  (o.a : ℝ)*o.b / ((o.a : ℝ)+o.b)^3 +
    (o.c : ℝ)*o.d / ((o.c : ℝ)+o.d)^3

/-- The standard error σ of (5.8)-(5.9), p. 11. -/
noncomputable def standardError (o : Counts) : ℝ := Real.sqrt (varianceEstimate o)

/-- Corrected studentized statistic, T17: fix C before testing, and use this
    same total real function on observed, simulated and reused assignments. -/
noncomputable def studentized (C : ℝ) (o v : Counts) : ℝ :=
  if standardError o = 0 then C else (estimate o-tau v)/standardError o

/-- T17: nonnegative variance, its exact zero condition, and the fixed extension. -/
theorem studentized_extension (C : ℝ) (o v : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) :
    0 ≤ varianceEstimate o ∧
    (standardError o = 0 ↔ o.a*o.b = 0 ∧ o.c*o.d = 0) ∧
    (standardError o = 0 → studentized C o v = C) ∧
    (0 < standardError o → studentized C o v = (estimate o-tau v)/standardError o) := by
  have ht : (0 : ℝ) < (o.a : ℝ)+o.b := by exact_mod_cast ho.1
  have hc : (0 : ℝ) < (o.c : ℝ)+o.d := by exact_mod_cast ho.2
  have h₁ : 0 ≤ (o.a : ℝ)*o.b/((o.a : ℝ)+o.b)^3 := by positivity
  have h₀ : 0 ≤ (o.c : ℝ)*o.d/((o.c : ℝ)+o.d)^3 := by positivity
  have hv : 0 ≤ varianceEstimate o := add_nonneg h₁ h₀
  refine ⟨hv,?_,?_,?_⟩
  · rw [standardError,Real.sqrt_eq_zero hv]
    constructor
    · intro hz
      have hz₁ : (o.a : ℝ)*o.b/((o.a : ℝ)+o.b)^3 = 0 := by
        dsimp [varianceEstimate] at hz
        linarith
      have hz₀ : (o.c : ℝ)*o.d/((o.c : ℝ)+o.d)^3 = 0 := by
        dsimp [varianceEstimate] at hz
        linarith
      have ht' : ((o.a : ℝ)+o.b)^3 ≠ 0 := ne_of_gt (pow_pos ht _)
      have hc' : ((o.c : ℝ)+o.d)^3 ≠ 0 := ne_of_gt (pow_pos hc _)
      have hp₁ := (div_eq_zero_iff.mp hz₁).resolve_right ht'
      have hp₀ := (div_eq_zero_iff.mp hz₀).resolve_right hc'
      constructor
      · exact_mod_cast hp₁
      · exact_mod_cast hp₀
    · rintro ⟨hz₁,hz₀⟩
      have hp₁ : (o.a : ℝ)*o.b = 0 := by exact_mod_cast hz₁
      have hp₀ : (o.c : ℝ)*o.d = 0 := by exact_mod_cast hz₀
      simp [varianceEstimate,hp₁,hp₀]
  · intro hz
    simp [studentized,hz]
  · intro hz
    simp [studentized,ne_of_gt hz]


/-- T17's zero-denominator experiment: all-zero observation with n=5,m=2. -/
theorem studentized_zero_witness (C : ℝ) :
    varianceEstimate ⟨0,2,0,3⟩ = 0 ∧ standardError ⟨0,2,0,3⟩ = 0 ∧
    estimate ⟨0,2,0,3⟩ - tau ⟨0,0,1,4⟩ = 1/5 ∧
    studentized C ⟨0,2,0,3⟩ ⟨0,0,1,4⟩ = C := by
  norm_num [varianceEstimate,standardError,estimate,estimateQ,tau,tauQ,
    Counts.effect,Counts.total,studentized]


/-- T21: footnote 9 corrected: accepted SATE numerators are exactly 0 and 1,
    so I=[0,1/9] and the observed estimate 1/7 is excluded. -/
theorem unbalanced_footnote_corrected :
    (acceptedEffectsQ (17/18) ⟨1,6,0,2⟩).toFinset = {0,1} ∧
    intervalQ (17/18) ⟨1,6,0,2⟩ = some (0,1/9) ∧
    estimateQ ⟨1,6,0,2⟩ = 1/7 ∧
    ¬ ((0 : ℚ) ≤ 1/7 ∧ (1/7 : ℚ) ≤ 1/9) ∧
    pValue ⟨1,0,1,7⟩ ⟨1,6,0,2⟩ = 29/36 ∧ (29/36 : ℚ) < 17/18 := by
  decide +kernel


/-- All candidate effect numerators "n C(n)=[n₁₁−n₀₁−m,…,+n]", (2.10), p. 6. -/
def candidateNumerators (o : Counts) : List ℤ :=
  (List.range (o.total+1)).map fun k : ℕ =>
    (o.a : ℤ)-(o.c : ℤ)-((o.a+o.b : ℕ) : ℤ)+(k : ℤ)

/-- Candidate lattice C(n), (2.10), p. 6, as real values. -/
def candidateLattice (o : Counts) : Set ℝ :=
  {t | ∃ d ∈ candidateNumerators o, t = (d : ℝ)/o.total}


/-- Possible tables with effect numerator `x` and `v₁₁ + v₁₀ = j`,
used in the corrected loop of Algorithm 5.3. -/
def lineGroup (o : Counts) (x : ℤ) (j : ℕ) : List Counts :=
  (possibleTables o).filter fun v => v.effect = x ∧ v.a+v.b = j

/-- Step 2(b)'s smallest possible v₁₀, Algorithms 4.3/5.3, pp. 8,11-12. -/
def minimumB : List Counts → Option Counts
  | [] => none
  | v::vs => match minimumB vs with
    | none => some v
    | some u => some (if v.b ≤ u.b then v else u)

/-- The finite minimum used for Step 2(b) is absent exactly on an empty list;
    every returned vector belongs to the list and has its smallest v₁₀. -/
theorem minimum_b_spec (xs : List Counts) :
    (minimumB xs = none ↔ xs = []) ∧
    (∀ v, minimumB xs = some v → v ∈ xs ∧ ∀ u ∈ xs, v.b ≤ u.b) := by
  induction xs with
  | nil => simp [minimumB]
  | cons a xs ih =>
    cases h : minimumB xs with
    | none =>
      have hnil : xs = [] := ih.1.mp h
      subst xs
      simp [minimumB]
    | some b =>
      have hb := ih.2 b h
      by_cases hab : a.b ≤ b.b
      · constructor
        · simp [minimumB,h,hab]
        · intro v hv
          simp only [minimumB,h,if_pos hab,Option.some.injEq] at hv
          subst v
          refine ⟨by simp,?_⟩
          intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact le_rfl
          · exact le_trans hab (hb.2 u hu)
      · constructor
        · simp [minimumB,h,hab]
        · intro v hv
          simp only [minimumB,h,if_neg hab,Option.some.injEq] at hv
          subst v
          refine ⟨List.mem_cons_of_mem _ hb.1,?_⟩
          intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact (Nat.le_of_lt (lt_of_not_ge hab))
          · exact hb.2 u hu

/-- "Choose the smallest v₁₀ such that v is possible", Step 2(b), Algorithms
    4.3/5.3, pp. 8,11-12. The structural finite minimum is kernel-computable. -/
def firstOnLine (o : Counts) (x : ℤ) (j : ℕ) : Option Counts :=
  minimumB (lineGroup o x j)

/-- The selected Step 2(b) table is possible, lies on the prescribed line,
    and minimizes v₁₀ among every possible table on that line, pp. 8,11-12. -/
theorem first_on_line_spec (o : Counts) (x : ℤ) (j : ℕ) (v : Counts)
    (hv : firstOnLine o x j = some v) :
    Possible o v ∧ v.effect = x ∧ v.a+v.b = j ∧
    ∀ u, Possible o u → u.effect = x → u.a+u.b = j → v.b ≤ u.b := by
  have hs := (minimum_b_spec (lineGroup o x j)).2 v hv
  have hv' := hs.1
  simp only [lineGroup,List.mem_filter,decide_eq_true_eq] at hv'
  refine ⟨hv'.1,hv'.2.1,hv'.2.2,?_⟩
  intro u hu hx hj
  apply hs.2 u
  simp only [lineGroup,List.mem_filter,decide_eq_true_eq]
  exact ⟨hu,hx,hj⟩

/-- The draw-reuse line v_k=(v₁₁−k,v₁₀+k,v₀₁+k,v₀₀−k), (5.17)-(5.18), p. 12. -/
def reuseVector (v : Counts) (k : ℕ) : Counts := ⟨v.a-k,v.b+k,v.c+k,v.d-k⟩

/-- T22's explicit witness: processing only the first feasible j misses (0,1,1,0). -/
theorem omitted_loop_witness :
    (possibleTables ⟨0,1,0,1⟩).toFinset =
      {⟨0,0,0,2⟩,⟨0,0,1,1⟩,⟨0,1,0,1⟩,⟨0,1,1,0⟩} ∧
    firstOnLine ⟨0,1,0,1⟩ 0 0 = some ⟨0,0,0,2⟩ ∧
    firstOnLine ⟨0,1,0,1⟩ 0 1 = some ⟨0,1,1,0⟩ := by
  decide +kernel


/-- T23: any rejection at c forces the sentinel search's return below c.
    The threshold u represents the exact nUα, not the noisy returned endpoint. -/
theorem rejected_query_cuts_endpoint (k₁ k₂ u : ℤ) (f : ℤ → Bool) (hk : k₁ ≤ k₂) :
    let s := sentinelSearch ((k₂-k₁+1).toNat+1) f (k₁-1) (k₂+1)
    (∀ c ∈ s.2, f c = true → s.1 < c) ∧
    (u ≤ s.1 → ∀ c ∈ s.2, c ≤ u → f c = false) ∧
    (∀ i j, i < j → j < s.2.length → f (s.2[i]!) = true → s.2[j]! < s.2[i]!) := by
  dsimp
  have h := sentinel_search_invariants ((k₂-k₁+1).toNat+1) f (k₁-1) (k₂+1)
    (by omega)
  refine ⟨?_,?_,?_⟩
  · intro c hc hf
    exact (h.2.2.2.1 c hc).2.2 hf
  · intro hu c hc hcu
    by_cases hf : f c = true
    · have hh := (h.2.2.2.1 c hc).2.2 hf
      omega
    · exact Bool.eq_false_iff.mpr hf
  · intro i j hij hj hf
    have hi : i < (sentinelSearch ((k₂-k₁+1).toNat+1) f (k₁-1) (k₂+1)).2.length := by
      omega
    have hh := h.2.2.2.2.rel_getElem_of_lt hi hj hij
    rw [getElem!_pos (sentinelSearch ((k₂-k₁+1).toNat+1) f (k₁-1) (k₂+1)).2 i hi] at hf
    rw [getElem!_pos (sentinelSearch ((k₂-k₁+1).toNat+1) f (k₁-1) (k₂+1)).2 j hj,
      getElem!_pos (sentinelSearch ((k₂-k₁+1).toNat+1) f (k₁-1) (k₂+1)).2 i hi]
    exact hh hf


/-- T24's corrected (A.4): complementing treatment swaps all units and the
    two estimates average exactly to the SATE; no mismatched summation index. -/
theorem complement_estimator_identity {n : ℕ} (w : PotentialTable n)
    (z : Finset (Fin n)) (m : ℕ) (hm : 0 < m) (hn : n = 2*m) (hz : z.card = m) :
    zᶜ.card = m ∧ tableEstimator w z + tableEstimator w zᶜ = 2*tableTau w := by
  have hzc : zᶜ.card = m := by
    rw [Finset.card_compl,Fintype.card_fin,hz,hn]
    omega
  refine ⟨hzc,?_⟩
  rw [corrected_signed_sum w z m hm hn hz,
    corrected_signed_sum w zᶜ m hm hn hzc,← add_div,← Finset.sum_add_distrib]
  have hsum :
      (∑ i, ((if i ∈ z then bit (w i).1 else -bit (w i).2) +
        (if i ∈ zᶜ then bit (w i).1 else -bit (w i).2))) =
      ∑ i, (bit (w i).1-bit (w i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hz' : i ∈ z <;> simp [hz'] <;> ring
  rw [hsum,tableTau]
  have hnR : (n : ℝ) = 2*(m : ℝ) := by exact_mod_cast hn
  rw [hnR]
  push_cast
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  field_simp <;> ring


/-- T25's concrete distinction between possible tables, arbitrary tables,
    a lattice set and a real interval: n=4,m=2, all-zero observation, α=1/2. -/
theorem lattice_interval_witness :
    (acceptedEffectsQ (1/2) ⟨0,2,0,2⟩).toFinset = {-1,0,1} ∧
    intervalQ (1/2) ⟨0,2,0,2⟩ = some (-1/4,1/4) ∧
    pValue ⟨1,0,2,1⟩ ⟨0,2,0,2⟩ = 2/3 ∧
    ¬ Possible ⟨0,2,0,2⟩ ⟨1,0,2,1⟩ ∧
    ((-1/4 : ℚ) ≤ 1/8 ∧ (1/8 : ℚ) ≤ 1/4) ∧
    ¬ ∃ d : ℤ, d ∈ candidateNumerators ⟨0,2,0,2⟩ ∧ (d : ℚ)/4 = 1/8 := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · norm_num
  · rintro ⟨d,hd,h⟩
    have : d = -2 ∨ d = -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 := by
      simpa [candidateNumerators,Counts.total,List.range_succ] using hd
    rcases this with rfl | rfl | rfl | rfl | rfl <;> norm_num at h


/-- Wald HC1 variance in Table 2's first scenario (T8), p. 15: 2m units,
    m always-one and m always-zero, equal allocation, k treated successes. -/
def waldVarianceQ (m k : ℕ) : ℚ :=
  ((2*m : ℕ) : ℚ) / ((2*m : ℕ) - 2) *
    (2*(k : ℚ)*((m : ℚ)-k)/(m : ℚ)^3)

/-- Difference of means (2.7) in Table 2's first scenario. -/
def waldEstimateQ (m k : ℕ) : ℚ := (2*(k : ℚ)-m)/(m : ℚ)

/-- The normal-quantile Wald interval, Table 2 caption, p. 15, with HC1 variance.
    z is a real parameter. -/
noncomputable def waldInterval (z : ℝ) (m k : ℕ) : Set ℝ :=
  Set.Icc ((waldEstimateQ m k : ℝ)-z*Real.sqrt (waldVarianceQ m k))
    ((waldEstimateQ m k : ℝ)+z*Real.sqrt (waldVarianceQ m k))

/-- Wald length from the same interval, Table 2, p. 15. -/
noncomputable def waldWidth (z : ℝ) (m k : ℕ) : ℝ := 2*z*Real.sqrt (waldVarianceQ m k)

/-- Uniform assignment weight of k treated always-one units, Table 2 scenario:
    choose(m,k)^2 labeled assignments out of choose(2m,m). -/
def waldCoverageQ (m : ℕ) (lo hi : ℕ) : ℚ :=
  ((List.range (m+1)).map fun k => if lo ≤ k ∧ k ≤ hi
    then (binomial m k : ℚ)^2 else 0).sum / binomial (2*m) m

/-- Median convention for Table 2: middle value for odd sample size,
    average of the two middle ordered lengths for even size. -/
noncomputable def median (xs : List ℝ) : ℝ :=
  let ys := xs.mergeSort (fun x y => x ≤ y)
  if ys = [] then 0 else (ys[(ys.length-1)/2]! + ys[ys.length/2]!)/2


/-- T8: exact arithmetic for the n=50 design probability and HC1 variance;
    these are population quantities. -/
theorem wald_exact_arithmetic :
    waldCoverageQ 25 10 15 = 14399081696900/15801325804719 ∧
    waldVarianceQ 25 11 = 77/3750 ∧ waldVarianceQ 25 10 = 1/50 ∧
    waldCoverageQ 50 21 29 = 3816125510529753382833452/4109292299835622081085553 ∧
    waldVarianceQ 50 23 = 621/61250 := by
  decide +kernel


/-- All four-cell count vectors of total n, footnote 16 (corrected), p. 17. -/
def allCounts (n : ℕ) : Finset Counts := (randomStates ⟨n,n,n,n⟩ n).toFinset

/-- Two fixed binary-covariate strata have known sizes N₀,N₁, so admissible
    eight-cell vectors are pairs of four-cell vectors with those two totals. -/
def stratifiedCounts (N₀ N₁ : ℕ) : Finset (Counts × Counts) :=
  (allCounts N₀).product (allCounts N₁)


/-- T19's explicit n=4, N₀=N₁=2 discrepancy: 100 admissible counts, 330
    total-only counts, and a total-four vector violating its first stratum size. -/
theorem stratum_count_witness :
    (stratifiedCounts 2 2).card = 100 ∧ (11 : ℕ).choose 7 = 330 ∧
    (⟨3,0,0,0⟩ : Counts).total + (⟨1,0,0,0⟩ : Counts).total = 4 ∧
    (⟨3,0,0,0⟩ : Counts).total ≠ 2 := by
  decide +kernel


/-- T20(b,c,d): corrected maximum/minimum comparison in (B.8), correct line
    index j=u₁₁+u₁₀ in (B.13), and the parity of v₀₀ in B.10 Case II. -/
theorem symbol_corrections (n n₁₁ n₁₀ n₀₁ j b x : ℤ)
    (u₁₁ u₁₀ u₀₁ u₀₀ : ℤ)
    (hu : u₁₁+u₁₀+u₀₁+u₀₀ = n) (hx : u₁₀-u₀₁ = x) :
    ((j-b-n₀₁ ≤ j-b ↔ 0 ≤ n₀₁) ∧
     (j-b-n₀₁ ≤ n₁₁ ↔ j-n₁₁-n₀₁ ≤ b) ∧
     (j-b-n₀₁ ≤ j-x-n₀₁ ↔ x ≤ b) ∧
     (j-b-n₀₁ ≤ n-b-n₁₀-n₀₁ ↔ j+n₁₀ ≤ n)) ∧
    ((u₁₁+u₁₀-b, b, b-x, n-(u₁₁+u₁₀)-b+x) =
     (u₁₁+(u₁₀-b),u₁₀-(u₁₀-b),u₀₁-(u₁₀-b),u₀₀+(u₁₀-b))) ∧
    (∀ a d : ℤ, (a+2+d)%2 = 0 → d%2 = a%2) := by
  constructor
  · omega
  constructor
  · ext <;> dsimp <;> omega
  · intro a d he
    omega


/-- T20(a): corrected four-coordinate update (-1,1,1,-1), below (5.20), p. 12. -/
theorem corrected_update (v : Counts) (ha : 1 ≤ v.a) (hd : 1 ≤ v.d) :
    ((reuseVector v 1).a : ℤ) = (v.a : ℤ)-1 ∧
    ((reuseVector v 1).b : ℤ) = (v.b : ℤ)+1 ∧
    ((reuseVector v 1).c : ℤ) = (v.c : ℤ)+1 ∧
    ((reuseVector v 1).d : ℤ) = (v.d : ℤ)-1 := by
  unfold reuseVector
  simp only
  omega


/-- Finite uniform assignments "Z∈{0,1}ⁿ, ∑ Z_i=m", (2.3)-(2.4), p. 5.
    Using a set of treated indices fixes the repeated Z₁ typo in (2.3). -/
abbrev Assignment (n m : ℕ) := {z : Finset (Fin n) // z.card = m}






/-- Printed B.1's execution with the actual number of f evaluations, including
    one extra boundary query exactly when that branch is taken (p. 20). -/
def printedExecution (fuel : ℕ) (k₁ k₂ : ℤ) (f : ℤ → Bool)
    (a b : ℤ) : Option (ℤ × ℕ) :=
  match fuel with
  | 0 => none
  | t+1 =>
    let s := searchStep f a b
    if s.2 = s.1+1 then
      if s.1 > k₁ ∧ s.2 < k₂ then some (s.1,1)
      else if s.1 = k₁ then some ((if f k₁ then k₁-1 else k₁),2)
      else if s.2 = k₂ then some ((if f k₂ then k₂-1 else k₂),2)
      else none
    else (printedExecution t k₁ k₂ f s.1 s.2).map fun p => (p.1,p.2+1)





/-- Finite sample variance of binary outcomes (A.12)-(A.14), p. 19. -/
noncomputable def binarySampleVariance (n successes : ℕ) : ℝ :=
  ((successes : ℝ)-(successes : ℝ)^2/n)/(n-1 : ℕ)

/-- Finite sample variance of unit effects, used in the Neyman identity
    underlying (A.11), p. 19. Effects have squares 1 precisely on discordant units. -/
noncomputable def effectSampleVariance (v : Counts) : ℝ :=
  ((v.b : ℝ)+v.c-((v.effect : ℝ)^2/v.total))/(v.total-1 : ℕ)

/-- Actual design variance: the weighted squared deviation from the design mean. -/
noncomputable def designVariance (v : Counts) (m : ℕ) : ℝ :=
  designMean v m (fun q =>
    (estimate (observed v q)-designMean v m (fun q' => estimate (observed v q')))^2)


/-- The canonical table "w̃_j=(1,1), …, (0,0)" of (4.5), p. 9;
    natural labels are zero based, so the threshold comparisons are strict. -/
def canonicalPair (v : Counts) (i : ℕ) : Bool × Bool :=
  if i < v.a then (true,true)
  else if i < v.a+v.b then (true,false)
  else if i < v.a+v.b+v.c then (false,true) else (false,false)

/-- Observed n for a labeled assignment of the canonical table, (4.7)/(5.2). -/
def canonicalObserved {n : ℕ} (v : Counts) (z : Finset (Fin n)) : Counts :=
  ⟨(Finset.univ.filter fun i => i ∈ z ∧ (canonicalPair v i.val).1 = true).card,
   (Finset.univ.filter fun i => i ∈ z ∧ (canonicalPair v i.val).1 = false).card,
   (Finset.univ.filter fun i => i ∉ z ∧ (canonicalPair v i.val).2 = true).card,
   (Finset.univ.filter fun i => i ∉ z ∧ (canonicalPair v i.val).2 = false).card⟩

/-- The ordered candidate list tested in Step 2 of Algorithm 4.3, p. 8.
    For each j use the minimum b; if b=c=0 also try b=c=1 when possible. -/
def candidates (o : Counts) (x : ℤ) : List Counts :=
  (List.range (o.total+1)).flatMap fun j =>
    match firstOnLine o x j with
    | none => []
    | some v =>
      if v.b = 0 ∧ v.c = 0 ∧ 1 ≤ v.a ∧ 1 ≤ v.d ∧
          Possible o ⟨v.a-1,1,1,v.d-1⟩ then [v,⟨v.a-1,1,1,v.d-1⟩] else [v]

/-- A compatibility query stops at its first accepted table, Algorithms 4.3/4.5.
    trace entries true are rejections; idx counts table tests actually performed. -/
structure QueryResult where
  compatible : Bool
  idx : ℕ
  trace : List (Counts × Bool)
  deriving Repr

/-- Adaptive table-testing at one effect value, Algorithms 4.3 and 4.5, p. 8-9. -/
def runTests (reject : Counts → ℕ → Bool) (idx : ℕ) : List Counts → QueryResult
  | [] => ⟨false,idx,[]⟩
  | v::vs =>
    if reject v idx then
      let r := runTests reject (idx+1) vs
      ⟨r.compatible,r.idx,(v,true)::r.trace⟩
    else ⟨true,idx+1,[(v,false)]⟩

/-- An endpoint computation can fail to return under the literal printed search. -/
structure EndpointResult where
  value : Option ℤ
  trace : List (Counts × Bool)
  deriving DecidableEq, Repr

/-- Adaptive binary search with the exact ordered table lists. corrected=true
    implements T5's unevaluated sentinels; false implements the literal printed
    post-step adjacency test and boundary clauses, with None on exhausted fuel. -/
def adaptiveSearch (fuel : ℕ) (corrected : Bool) (o : Counts)
    (k₁ k₂ : ℤ) (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ) : EndpointResult :=
  if corrected ∧ b ≤ a+1 then ⟨some a,[]⟩ else
  match fuel with
  | 0 => ⟨none,[]⟩
  | t+1 =>
    let c := (a+b)/2
    let q := runTests reject idx (candidates o c)
    let a' := if q.compatible then c else a
    let b' := if q.compatible then b else c
    if ¬corrected ∧ b' = a'+1 then
      if a' > k₁ ∧ b' < k₂ then ⟨some a',q.trace⟩
      else if a' = k₁ then
        let e := runTests reject q.idx (candidates o k₁)
        ⟨some (if e.compatible then k₁ else k₁-1),q.trace++e.trace⟩
      else if b' = k₂ then
        let e := runTests reject q.idx (candidates o k₂)
        ⟨some (if e.compatible then k₂ else k₂-1),q.trace++e.trace⟩
      else ⟨none,q.trace⟩
    else
      let r := adaptiveSearch t corrected o k₁ k₂ reject a' b' q.idx
      ⟨r.value,q.trace++r.trace⟩

/-- Upper endpoint search on [2(n₁₁−n₀₁),n₁₁−n₀₁+m], Algorithm 4.3,
    with the corrected or printed boundary rule explicitly selected. -/
def upperRun (corrected : Bool) (o : Counts) (reject : Counts → ℕ → Bool)
    (idx : ℕ := 0) : EndpointResult :=
  let k₁ := 2*((o.a : ℤ)-o.c)
  let k₂ := (o.a : ℤ)-o.c+(o.a+o.b)
  adaptiveSearch (o.total+3) corrected o k₁ k₂ reject
    (if corrected then k₁-1 else k₁) (if corrected then k₂+1 else k₂) idx

/-- Outcome complementation used for the lower search in Algorithms 4.3/4.5. -/
def complementObserved (o : Counts) : Counts := ⟨o.b,o.a,o.d,o.c⟩

/-- The exact rejection decision of Algorithm 2.2, p. 6. -/
def exactRejectQ (α : ℚ) (o v : Counts) (_idx : ℕ) : Bool := !(levelAccepted α v o)

/-- Exact upper-endpoint implementation of Algorithm 4.3 (T32). -/
noncomputable def exactUpperRun (α : ℝ) (o : Counts) : EndpointResult :=
  upperRun true o (fun v _ => decide ((pValue v o : ℝ) < α))

/-- S of (4.8), with K independent assignments; exact integer comparisons
    implement the Bernoulli variables (4.6). -/
def monteMean {n K : ℕ} (v o : Counts) (draws : Fin K → Finset (Fin n)) : ℚ :=
  (∑ i, if (deviationNumerator v (canonicalObserved v (draws i)) (o.a+o.b)).natAbs ≥
    (deviationNumerator v o (o.a+o.b)).natAbs then (1 : ℚ) else 0)/(K : ℚ)

/-- D=(n+1)floor(log₂(n+1)+3), (B.82), pp. 27-28. Nat.log2 is the exact
    integer floor for positive integer n+1. Two D table tests suffice for both endpoints. -/
def testBudget (n : ℕ) : ℕ := (n+1)*(Nat.log2 (n+1)+3)

/-- Finite joint space for the observed uniform assignment and fresh independent
    Monte Carlo draws, Algorithms 4.4/4.5. One spare batch is harmless; every
    actual test below budget uses a different pre-generated batch. -/
abbrev MonteSpace (n m K : ℕ) :=
  Assignment n m × (Fin (2*testBudget n+1) → Fin K → Assignment n m)

/-- Uniform probability on a finite product space; it is precisely the uniform
    design and independent Monte Carlo law used by the paper. -/
noncomputable def uniformProb {Ω : Type*} [Fintype Ω] (E : Ω → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ)/Fintype.card Ω

/-- Access each performed test's fresh batch. Legal searches never wrap around;
    the modular fallback makes the function total even for invalid inputs. -/
def batch {n m K : ℕ} (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m)
    (idx : ℕ) (i : Fin K) : Finset (Fin n) :=
  (pool ⟨idx % (2*testBudget n+1), Nat.mod_lt _ (by omega)⟩ i).val

/-- Algorithm 4.4 accepts iff S+ε≥α, p. 9. This same decision function is
    used at every performed test, including levels α−ε in Proposition 4.6. -/
noncomputable def approximateReject {n m K : ℕ} (α ε : ℝ) (o : Counts)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m)
    (v : Counts) (idx : ℕ) : Bool :=
  decide ((monteMean v o (batch pool idx) : ℝ)+ε < α)

/-- Algorithm 4.5's two endpoints, with fresh batches continued after the upper
    search. The lower search is the upper search on complemented outcomes. -/
noncomputable def monteEndpoints {n m K : ℕ} (corrected : Bool) (α ε : ℝ)
    (o : Counts) (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m) :
    EndpointResult × EndpointResult :=
  let hi := upperRun corrected o (approximateReject α ε o pool)
  let lo := upperRun corrected (complementObserved o)
    (approximateReject α ε (complementObserved o) pool) hi.trace.length
  (lo,hi)

/-- The Monte Carlo interval of Algorithm 4.5, p. 9. A nonterminating literal
    search is represented by the empty set and is additionally reported through
    the endpoint Option; corrected searches terminate under the stated design. -/
noncomputable def monteInterval {n m K : ℕ} (corrected : Bool) (α ε : ℝ)
    (o : Counts) (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m) : Set ℝ :=
  let e := monteEndpoints corrected α ε o pool
  match e.1.value, e.2.value with
  | some lo, some hi => Set.Icc (-(lo : ℝ)/o.total) ((hi : ℝ)/o.total)
  | _, _ => ∅






/-- Product of the K=1 reply probabilities along a fixed list of table decisions.
For a valid chronological path in the T6 setting, where acceptance is exactly a
successful tail indicator, fresh independent draws identify this product with the
path probability conditional on the data. This definition does not check path validity. -/
def traceProbabilityQ (o : Counts) (trace : List (Counts × Bool)) : ℚ :=
  (trace.map fun t => if t.2 then 1-pValue t.1 o else pValue t.1 o).prod

/-- Target T6's observed n=30,m=15 experiment. -/
def adaptiveData : Counts := ⟨2,13,1,14⟩

/-- T6's data and Monte Carlo parameters satisfy the printed hypotheses, and
    these observed counts have positive probability 45/116 in a genuine n=30
    experiment with potential counts (3,0,0,27). K=1 accepts exactly S=1. -/
theorem adaptive_data_valid :
    adaptiveData.total = 30 ∧ adaptiveData.a+adaptiveData.b = 15 ∧
    estimateQ adaptiveData = 1/15 ∧
    (0 : ℚ) < 1/200 ∧ (1/200 : ℚ) < 1/20 ∧ (1/20 : ℚ) < 1 ∧
    (((randomStates ⟨3,0,0,27⟩ 15).map fun q =>
      if observed ⟨3,0,0,27⟩ q = adaptiveData then multiplicity ⟨3,0,0,27⟩ q
      else 0).sum : ℚ)/binomial 30 15 = 45/116 ∧
    (0 : ℚ) < 45/116 ∧
    (∀ s : Bool, ((if s then (1 : ℚ) else 0)+1/200 ≥ 1/20 ↔ s = true)) := by
  repeat' apply And.intro
  all_goals first
    | (intro s; cases s <;> norm_num)
    | decide +kernel


set_option maxHeartbeats 6000000


set_option maxHeartbeats 1200000


set_option maxHeartbeats 1200000


/-- A permutation vector (5.19), p. 12, can be represented by its treated
    four-cell counts q; the control counts are v−q coordinatewise. -/
def treatedCounts {n : ℕ} (v : Counts) (z : Finset (Fin n)) : Counts :=
  ⟨(z.filter fun i => canonicalPair v i.val = (true,true)).card,
   (z.filter fun i => canonicalPair v i.val = (true,false)).card,
   (z.filter fun i => canonicalPair v i.val = (false,true)).card,
   (z.filter fun i => canonicalPair v i.val = (false,false)).card⟩

/-- Exact random update (5.21)-(5.26), p. 12: choose one (0,0) unit and one
    (1,1) unit uniformly and independently, changing their types. A uniform
    factorial-sized seed samples each group exactly via a residue (every
    positive group size ≤n divides n!). true in the inequalities means control. -/
def updateTreated (v q : Counts) (s₀ s₁ : ℕ) : Counts :=
  let control₀ := s₀ % v.d < v.d-q.d
  let control₁ := s₁ % v.a < v.a-q.a
  ⟨if control₁ then q.a else q.a-1,
   if control₁ then q.b else q.b+1,
   if control₀ then q.c else q.c+1,
   if control₀ then q.d else q.d-1⟩

/-- Independent initial draws and independent random-update seeds for every
    (τ₀,j) line, Algorithm 5.3, pp. 11-13, with the corrected j loop.
    Factorial seeds give precisely the Bernoulli probabilities (5.21),(5.24). -/
abbrev GeneralSpace (n m K : ℕ) := Assignment n m ×
  (((Fin (n+1) × Fin (n+1)) → Fin K → Assignment n m) ×
   ((Fin (n+1) × Fin (n+1)) → Fin n → Fin K →
      (Fin n.factorial × Fin n.factorial)))

/-- Reused draws along v_k, (5.17)-(5.26). Seed t is read only on the t-th
    update; there are at most n updates, and each of the K draws has its own seed. -/
def reusedSamples {n m K : ℕ} (v : Counts) (initial : Fin K → Assignment n m)
    (seeds : Fin n → Fin K → (Fin n.factorial × Fin n.factorial)) :
    ℕ → Fin K → Counts
  | 0, i => treatedCounts v (initial i).val
  | t+1, i =>
    let s := if h : t < n then seeds ⟨t,h⟩ i else
      (⟨0,Nat.factorial_pos n⟩,⟨0,Nat.factorial_pos n⟩)
    updateTreated (reuseVector v t) (reusedSamples v initial seeds t i) s.1.val s.2.val

/-- "S=(1+∑V_i)/(K+1)", (5.1),(5.3), p. 10. R is any real-valued
    statistic and absolute-value ties are included. Algorithm 5.1 accepts iff S>α. -/
noncomputable def rankValue {K : ℕ} (R : Counts → Counts → ℝ) (o v : Counts)
    (samples : Fin K → Counts) : ℝ :=
  (1+∑ i, if |R (observed v (samples i)) v| ≥ |R o v| then (1 : ℝ) else 0)/(K+1)

/-- "J={θ(v):v∈V}", (5.27), p. 13, for corrected Algorithm 5.3: visit
    every descending effect numerator and every j=0,…,n, testing the minimum
    b base and all possible reuse vectors v_k with the plus-one rank (5.3).
    n is fixed before randomization, and every legal observed vector has total n. -/
noncomputable def generalSet {n m K : ℕ} (α : ℝ)
    (θ : Counts → ℝ) (R : Counts → Counts → ℝ) (o : Counts)
    (initial : (Fin (n+1) × Fin (n+1)) → Fin K → Assignment n m)
    (seeds : (Fin (n+1) × Fin (n+1)) → Fin n → Fin K →
      (Fin n.factorial × Fin n.factorial)) : Set ℝ :=
  {t | ∃ ij : Fin (n+1) × Fin (n+1), ∃ v : Counts,
    firstOnLine o ((candidateNumerators o).reverse[ij.1.val]!) ij.2.val = some v ∧
    ∃ k ≤ n, k ≤ v.a ∧ k ≤ v.d ∧ Possible o (reuseVector v k) ∧
      t = θ (reuseVector v k) ∧
      α < rankValue R o (reuseVector v k)
        (reusedSamples v (initial ij) (seeds ij) k)}


/-- T17(iv): changing the fixed extension can change the exact test;
    the two p-values in the n=5,m=2 population are 1 and 2/5. -/
theorem extension_changes_test :
    designProb ⟨0,0,1,4⟩ 2 (fun q =>
      |studentized 0 (observed ⟨0,0,1,4⟩ q) ⟨0,0,1,4⟩| ≥
        |studentized 0 ⟨0,2,0,3⟩ ⟨0,0,1,4⟩|) = 1 ∧
    designProb ⟨0,0,1,4⟩ 2 (fun q =>
      |studentized (10^6) (observed ⟨0,0,1,4⟩ q) ⟨0,0,1,4⟩| ≥
      |studentized (10^6) ⟨0,2,0,3⟩ ⟨0,0,1,4⟩|) = 2/5 := by
  classical
  have hs : standardError ⟨0,2,1,2⟩ = Real.sqrt (2/27) := by
    norm_num [standardError,varianceEstimate]
  have hsp : (0 : ℝ) < Real.sqrt (2/27) := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt (2/27))^2 = (2/27 : ℝ) := Real.sq_sqrt (by norm_num)
  have hlo : (1/10 : ℝ) < Real.sqrt (2/27) := by nlinarith
  have hR : studentized (10^6) ⟨0,2,1,2⟩ ⟨0,0,1,4⟩ =
      (-2/15 : ℝ)/Real.sqrt (2/27) := by
    rw [studentized,hs,if_neg (ne_of_gt hsp)]
    norm_num [estimate,estimateQ,tau,tauQ,Counts.total,Counts.effect]
  have hsmall : |studentized (10^6) ⟨0,2,1,2⟩ ⟨0,0,1,4⟩| < (10^6 : ℝ) := by
    rw [hR,abs_div,abs_of_pos hsp]
    rw [show |(-2/15 : ℝ)| = 2/15 by norm_num]
    apply (div_lt_iff₀ hsp).mpr
    nlinarith
  have hrandom : randomStates ⟨0,0,1,4⟩ 2 = [⟨0,0,0,2⟩,⟨0,0,1,1⟩] := by
    decide +kernel
  have ho0 : observed ⟨0,0,1,4⟩ ⟨0,0,0,2⟩ = ⟨0,2,1,2⟩ := rfl
  have ho1 : observed ⟨0,0,1,4⟩ ⟨0,0,1,1⟩ = ⟨0,2,0,3⟩ := rfl
  have hzero0 := (studentized_zero_witness 0).2.2.2
  have hzeroC := (studentized_zero_witness (10^6)).2.2.2
  constructor
  · unfold designProb
    rw [hzero0]
    simp only [abs_zero,if_pos (abs_nonneg _)]
    norm_num [hrandom,multiplicity,binomial_eq_choose,Nat.choose,Counts.total]
  · have hnot : ¬ |studentized (10^6) ⟨0,2,1,2⟩ ⟨0,0,1,4⟩| ≥
        |studentized (10^6) ⟨0,2,0,3⟩ ⟨0,0,1,4⟩| := by
      rw [hzeroC]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 10^6)]
      exact not_le_of_gt hsmall
    simp only [designProb,hrandom,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ho0,ho1]
    simp only [if_neg hnot,if_pos le_rfl]
    norm_num [multiplicity,binomial_eq_choose,Nat.choose,Counts.total]


/-- Reuse line length in Algorithm 5.3: k=1,…,n, feasible coordinates and
    possibility as required by (5.18). -/
def reuseLine (o v : Counts) : List ℕ :=
  ((List.range o.total).map (fun k => k+1)).filter fun k =>
    k ≤ v.a ∧ k ≤ v.d ∧ Possible o (reuseVector v k)

/-- Actual number of fresh assignment draws in Algorithm 5.3 (corrected loop).
    Each feasible (τ₀,j) base uses exactly K draws. -/
def generalDrawCount (o : Counts) (K : ℕ) : ℕ :=
  ((candidateNumerators o).map fun x =>
    ((List.range (o.total+1)).map fun j =>
      if (firstOnLine o x j).isSome then K else 0).sum).sum

/-- Actual number of permutation-vector updates (and reused indicator evaluations)
    in Algorithm 5.3's corrected loop, proof of Theorem 5.5, p. 28. -/
def generalUpdateCount (o : Counts) (K : ℕ) : ℕ :=
  ((candidateNumerators o).map fun x =>
    ((List.range (o.total+1)).map fun j =>
      match firstOnLine o x j with
      | none => 0
      | some v => K*(reuseLine o v).length).sum).sum

/-- Operation count in the paper's cost model (p. 4, p. 28): c₀ per loop
    bookkeeping slot, c₁ n per draw or fresh indicator, c₂ per reuse update
    or indicator. θ and R evaluations are included in these constant costs. -/
def generalOperations (o : Counts) (K : ℕ) (c₀ c₁ c₂ : ℝ) : ℝ :=
  c₀*(o.total+1)^2 + 2*c₁*o.total*generalDrawCount o K +
    2*c₂*generalUpdateCount o K

/-- Exact operation envelope in T36's finite lemmas, with constant bookkeeping included. -/
def generalEnvelope (n K : ℕ) (c₀ c₁ c₂ : ℝ) : ℝ :=
  ((n : ℝ)+1)^2*(c₀+2*(c₁+c₂)*K*n)

/-- A finite counting lemma: bounded cost per element bounds the list total. -/
theorem list_sum_bound (xs : List ℕ) (f : ℕ → ℕ) (M : ℕ)
    (hf : ∀ x ∈ xs, f x ≤ M) : (xs.map f).sum ≤ xs.length*M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith


/-- The same counting lemma for lists with an arbitrary element type. -/
theorem list_cost_bound {A : Type*} (xs : List A) (f : A → ℕ) (M : ℕ)
    (hf : ∀ x ∈ xs, f x ≤ M) : (xs.map f).sum ≤ xs.length*M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith


/-- T36: finite counts behind O(Kn³): at most (n+1)² bases, (n+1)²K fresh
    assignments, and (n+1)²nK updates, before passing to any asymptotic filter. -/
theorem general_finite_counts (o : Counts) (K : ℕ) (c₀ c₁ c₂ : ℝ)
    (hc : 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂) :
    generalDrawCount o K ≤ (o.total+1)^2*K ∧
    generalUpdateCount o K ≤ (o.total+1)^2*o.total*K ∧
    generalOperations o K c₀ c₁ c₂ ≤ generalEnvelope o.total K c₀ c₁ c₂ := by
  have hc0 := hc.1
  have hc1 := hc.2.1
  have hc2 := hc.2.2
  have hd : generalDrawCount o K ≤ (o.total+1)^2*K := by
    unfold generalDrawCount
    have h := list_cost_bound (candidateNumerators o) (fun x =>
      ((List.range (o.total+1)).map fun j =>
        if (firstOnLine o x j).isSome then K else 0).sum) ((o.total+1)*K) (by
          intro x hx
          have hi := list_sum_bound (List.range (o.total+1)) (fun j =>
            if (firstOnLine o x j).isSome then K else 0) K (by
              intro j hj
              split_ifs <;> omega)
          simpa using hi)
    simpa [candidateNumerators,pow_two,Nat.mul_assoc] using h
  have hu : generalUpdateCount o K ≤ (o.total+1)^2*o.total*K := by
    have hl : ∀ v, (reuseLine o v).length ≤ o.total := by
      intro v
      unfold reuseLine
      exact le_trans (List.length_filter_le _ _) (by simp)
    unfold generalUpdateCount
    have h := list_cost_bound (candidateNumerators o) (fun x =>
      ((List.range (o.total+1)).map fun j =>
        match firstOnLine o x j with
        | none => 0
        | some v => K*(reuseLine o v).length).sum) ((o.total+1)*(K*o.total)) (by
          intro x hx
          have hi := list_sum_bound (List.range (o.total+1)) (fun j =>
            match firstOnLine o x j with
            | none => 0
            | some v => K*(reuseLine o v).length) (K*o.total) (by
              intro j hj
              cases hbase : firstOnLine o x j with
              | none => simp
              | some v => exact Nat.mul_le_mul_left K (hl v))
          simpa using hi)
    simpa [candidateNumerators,pow_two,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
  refine ⟨hd,hu,?_⟩
  have hdR : (generalDrawCount o K : ℝ) ≤ ((o.total : ℝ)+1)^2*K := by
    exact_mod_cast hd
  have huR : (generalUpdateCount o K : ℝ) ≤ ((o.total : ℝ)+1)^2*o.total*K := by
    exact_mod_cast hu
  unfold generalOperations generalEnvelope
  have hm1 := mul_le_mul_of_nonneg_left hdR (show 0 ≤ 2*c₁*o.total by positivity)
  have hm2 := mul_le_mul_of_nonneg_left huR (show 0 ≤ 2*c₂ by positivity)
  nlinarith [hc.1,hc.2.1,hc.2.2]


/-- T36's exact polynomial envelope is uniformly bounded by a constant times Kn³. -/
theorem general_envelope_bound (n K : ℕ) (hn : 1 ≤ n) (hK : 1 ≤ K)
    (c₀ c₁ c₂ : ℝ) (hc : 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂) :
    generalEnvelope n K c₀ c₁ c₂ ≤ 4*(c₀+2*(c₁+c₂))*K*(n : ℝ)^3 := by
  have hc0 := hc.1
  have hc1 := hc.2.1
  have hc2 := hc.2.2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hkn : (1 : ℝ) ≤ (K : ℝ)*n := by nlinarith
  have hs : ((n : ℝ)+1)^2 ≤ 4*(n : ℝ)^2 := by nlinarith
  have hi : c₀+2*(c₁+c₂)*K*n ≤ (c₀+2*(c₁+c₂))*K*n := by
    nlinarith [mul_nonneg hc.1 (show 0 ≤ (K : ℝ)*n-1 by linarith)]
  unfold generalEnvelope
  calc
    _ ≤ 4*(n : ℝ)^2*((c₀+2*(c₁+c₂))*K*n) :=
      mul_le_mul hs hi (by positivity) (by positivity)
    _ = _ := by ring


/-- T36: Theorem 5.5 part 2 as a uniform joint filter statement about actual
    operation counts. n and K may tend to infinity in any manner; observed
    vectors (and hence arm sizes) can vary arbitrarily with (n,K). -/
theorem general_complexity (c₀ c₁ c₂ : ℝ) (hc : 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂)
    (o : ℕ × ℕ → Counts) (ho : ∀ p, (o p).total = p.1)
    (hdesign : ∀ᶠ p in Filter.atTop,
      0 < (o p).a+(o p).b ∧ 0 < (o p).c+(o p).d) :
    (fun p : ℕ × ℕ => generalOperations (o p) p.2 c₀ c₁ c₂) =O[Filter.atTop]
      (fun p : ℕ × ℕ => (p.2 : ℝ)*(p.1 : ℝ)^3) := by
  have hc0 := hc.1
  have hc1 := hc.2.1
  have hc2 := hc.2.2
  apply Asymptotics.IsBigO.of_bound (4*(c₀+2*(c₁+c₂)))
  apply Filter.eventually_atTop.mpr
  refine ⟨(1,1),?_⟩
  intro p hp
  have hn : 1 ≤ p.1 := hp.1
  have hK : 1 ≤ p.2 := hp.2
  have hcost := (general_finite_counts (o p) p.2 c₀ c₁ c₂ hc).2.2
  rw [ho p] at hcost
  have hb := general_envelope_bound p.1 p.2 hn hK c₀ c₁ c₂ hc
  have hpos : 0 ≤ generalOperations (o p) p.2 c₀ c₁ c₂ := by
    unfold generalOperations
    positivity
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hpos,abs_of_nonneg (by positivity)]
  nlinarith [hcost,hb]


/-- Corrected recommended integer K, (4.9), p. 9 and Remark 5.7, p. 13 (T18). -/
noncomputable def recommendedK (ε : ℝ) (n : ℕ) : ℕ :=
  ⌈Real.log (4*(n : ℝ)*logTwo n/ε)/(2*ε^2)⌉₊

/-- For fixed positive ε, the integer Monte Carlo budget in (4.9), p. 9,
    is eventually at most a constant times log n; the ceiling contributes at most one.
    This finite eventual inequality is used in corrected Remark 5.7 (T18). -/
theorem recommended_k_log_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (recommendedK ε n : ℝ) ≤ C*Real.log n := by
  let A : ℝ := 4/(ε*Real.log 2)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  have hden : 0 < 2*ε^2 := by positivity
  let C : ℝ := (|Real.log A|+2)/(2*ε^2)+1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  have hnR : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hln : Filter.Tendsto (fun n : ℕ => Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hnR
  filter_upwards [hln.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    hnR.eventually (Filter.eventually_ge_atTop (1/A))] with n hl hn
  have hnp : (0 : ℝ) < n := lt_of_lt_of_le (by positivity : 0 < 1/A) hn
  have hlp : 0 < Real.log n := by linarith
  have hAn : 1 ≤ A*(n : ℝ) := by
    have hh := (div_le_iff₀ hA).mp hn
    nlinarith
  have harg : 4*(n : ℝ)*logTwo n/ε = A*(n : ℝ)*Real.log n := by
    dsimp [A,logTwo]
    ring
  have harg1 : 1 ≤ A*(n : ℝ)*Real.log n := by nlinarith
  have hlog : Real.log (A*(n : ℝ)*Real.log n) =
      Real.log A+Real.log n+Real.log (Real.log n) := by
    rw [Real.log_mul (mul_ne_zero hA.ne' hnp.ne') hlp.ne',
      Real.log_mul hA.ne' hnp.ne']
  have hlogupper : Real.log (A*(n : ℝ)*Real.log n) ≤
      (|Real.log A|+2)*Real.log n := by
    rw [hlog]
    have hconst := mul_le_mul_of_nonneg_left hl (abs_nonneg (Real.log A))
    nlinarith [le_abs_self (Real.log A),Real.log_le_self hlp.le]
  have hceil := (Nat.ceil_lt_add_one (div_nonneg
    (Real.log_nonneg harg1) hden.le)).le
  change (⌈Real.log (4*(n : ℝ)*logTwo n/ε)/(2*ε^2)⌉₊ : ℝ) ≤ C*Real.log n
  rw [harg]
  calc
    _ ≤ Real.log (A*(n : ℝ)*Real.log n)/(2*ε^2)+1 := hceil
    _ ≤ ((|Real.log A|+2)/(2*ε^2))*Real.log n+1 := by
      calc
        _ ≤ ((|Real.log A|+2)*Real.log n)/(2*ε^2)+1 := by
          simpa only [add_comm] using
            add_le_add_right (div_le_div_of_nonneg_right hlogupper hden.le) 1
        _ = _ := by ring
    _ ≤ C*Real.log n := by dsimp [C]; nlinarith


/-- Operation bound after multiplying 4n log₂ n tests, K draws and c n
    operations per draw, corrected Remark 5.7, target T18. -/
noncomputable def balancedEnvelope (ε c : ℝ) (n : ℕ) : ℝ :=
  4*c*recommendedK ε n*(n : ℝ)^2*logTwo n

/-- T18(i): exact finite arithmetic distinguishing operation count from draw count. -/
theorem balanced_cost_multiplication (n K : ℕ) (c : ℝ) :
    (4*(n : ℝ)*logTwo n)*(K : ℝ)*(c*n) =
      4*c*K*(n : ℝ)^2*logTwo n := by
  ring


/-- T18(i): supporting O(n² log² n) bound for the cost envelope at fixed
    positive tolerance, with the actual ceil choice of K in (4.9), p. 9. -/
theorem balanced_complexity (ε c : ℝ) (hε : 0 < ε) (hc : 0 ≤ c) :
    balancedEnvelope ε c =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ)^2*(Real.log n)^2) := by
  obtain ⟨C,hC,hK⟩ := recommended_k_log_bound ε hε
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Asymptotics.IsBigO.of_bound (4*c*C/Real.log 2)
  filter_upwards [hK] with n hn
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hb : 0 ≤ logTwo n := div_nonneg hlog h2.le
  have henv : 0 ≤ balancedEnvelope ε c n := by
    unfold balancedEnvelope
    positivity
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg henv,
    abs_of_nonneg (by positivity)]
  calc
    balancedEnvelope ε c n =
        (4*c*(n : ℝ)^2*logTwo n)*(recommendedK ε n : ℝ) := by
      unfold balancedEnvelope
      ring
    _ ≤ (4*c*(n : ℝ)^2*logTwo n)*(C*Real.log n) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (4*c*C/Real.log 2)*((n : ℝ)^2*(Real.log n)^2) := by
      unfold logTwo
      ring


/-- T18(i), corrected Remark 5.7, p. 13: if the balanced algorithm uses
    at most 4n log₂ n tests, K draws per test with the prescribed ceiling (4.9),
    and at most c n operations per draw, its total operations are O(n² log² n).
    The quantified nonnegative operation counts retain all three cost premises. -/
theorem balanced_algorithm_complexity (α ε c : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε < α) (hc : 0 ≤ c)
    (tests : ℕ → ℕ) (operations : ℕ → ℝ) (hops : ∀ n, 0 ≤ operations n)
    (htests : ∀ᶠ n in Filter.atTop, (tests n : ℝ) ≤ 4*(n : ℝ)*logTwo n)
    (hcost : ∀ᶠ n in Filter.atTop, operations n ≤ (tests n : ℝ)*recommendedK ε n*(c*n)) :
    operations =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^2*(Real.log n)^2) := by
  have henv := balanced_complexity ε c hε.1 hc
  have hdom : operations =O[Filter.atTop] balancedEnvelope ε c := by
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [htests,hcost] with n ht hcostn
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog : 0 ≤ logTwo n := div_nonneg (Real.log_natCast_nonneg n) h2.le
    have hpos : 0 ≤ balancedEnvelope ε c n := by unfold balancedEnvelope; positivity
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (hops n),abs_of_nonneg hpos]
    calc
      operations n ≤ (tests n : ℝ)*recommendedK ε n*(c*n) := hcostn
      _ ≤ (4*(n : ℝ)*logTwo n)*recommendedK ε n*(c*n) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ht (by positivity)) (by positivity)
      _ = balancedEnvelope ε c n := by unfold balancedEnvelope; ring
  exact hdom.trans henv


/-- T18(iii): the printed squared natural logarithm leads to conservative
    oversampling, because log² n ≥ log₂ n for n≥15. -/
theorem squared_log_dominates (n : ℕ) (hn : 15 ≤ n) :
    logTwo n ≤ (Real.log n)^2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h9n : (9 : ℝ) ≤ n := by exact_mod_cast (show 9 ≤ n by omega)
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 9) h9n
  have h9 : Real.log (9 : ℝ) = 2*Real.log 3 := by
    rw [show (9 : ℝ) = 3^2 by norm_num,Real.log_pow]
    norm_num
  rw [h9] at hmono
  have hnlog : 2 ≤ Real.log n := by nlinarith [Real.log_three_gt_d9]
  have hp : 1 ≤ Real.log n*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_right hnlog h2.le
    nlinarith [Real.log_two_gt_d9]
  unfold logTwo
  rw [div_le_iff₀ h2]
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ Real.log n by linarith)
  nlinarith


/-- T1: the two tails in the final (D.7) inequality equal 83/380>109/500;
    the true table is possible only at the complete-data completion. -/
theorem missing_critical_tail_counterexample :
    pValue badPopulation ⟨0,3,11,6⟩ = 83/380 ∧
    pValue badPopulation ⟨0,3,10,7⟩ = 83/380 ∧
    (109/500 : ℚ) < 83/380 ∧
    Possible ⟨0,3,11,6⟩ badPopulation ∧
    ¬ Possible ⟨0,3,10,7⟩ badPopulation ∧
    estimateQ ⟨0,3,11,6⟩ = -11/17 ∧ estimateQ ⟨0,3,10,7⟩ = -10/17 := by
  decide +kernel


/-- T4(C): the same endpoint defect occurs within Theorem 4.1's legal n=16
    balanced experiment, not only in the isolated abstract binary search. -/
theorem balanced_search_counterexample :
    let o : Counts := ⟨7,1,0,8⟩
    estimateQ o = 7/8 ∧ Possible o ⟨0,14,0,2⟩ ∧ Possible o ⟨0,15,0,1⟩ ∧
    pValue ⟨0,14,0,2⟩ o = 1 ∧ pValue ⟨0,15,0,1⟩ o = 1 ∧
    intervalQ (1/20) o = some (1/2,15/16) ∧
    (upperRun false o (exactRejectQ (1/20) o)).value = some 14 := by
  decide +kernel


/-- T11: the piecewise tail in real_threshold_counterexample is exactly the
    paper's randomization tail for n=2,m=1, both potential outcomes (0,0). -/
theorem zero_population_tail (x : ℝ) :
    designProb ⟨0,0,0,2⟩ 1 (fun q => x ≤
      |estimate (observed ⟨0,0,0,2⟩ q)-tau ⟨0,0,0,2⟩|) =
      if x ≤ 0 then 1 else 0 := by
  have hrandom : randomStates ⟨0,0,0,2⟩ 1 = [⟨0,0,0,1⟩] := by decide +kernel
  by_cases hx : x ≤ 0 <;>
    norm_num [designProb,hrandom,multiplicity,binomial_eq_choose,Nat.choose,observed,estimate,estimateQ,
      tau,tauQ,Counts.effect,Counts.total,hx]


/-- A list/finite-sum identity used to normalize the complete-randomization
    distribution (2.4), p. 5. -/
theorem range_sum_eq (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [List.sum_range_succ,Finset.sum_range_succ,ih]


/-- Truncated Vandermonde identity for the actual binomial weights in (2.4).
    Truncating the first type at its population size removes only zero weights. -/
theorem bounded_vandermonde (a b m : ℕ) :
    ((List.range (min a m+1)).map fun i =>
      binomial a i*binomial b (m-i)).sum = binomial (a+b) m := by
  rw [range_sum_eq]
  simp_rw [binomial_eq_choose]
  calc
    _ = ∑ i ∈ Finset.range (m+1), a.choose i*b.choose (m-i) := by
      apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (Nat.min_le_right _ _) 1))
      intro i him hin
      have hiM : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp him)
      have hai : a < i := by
        by_contra h
        have hiA : i ≤ a := Nat.le_of_not_gt h
        have hi : i ≤ min a m := le_min hiA hiM
        exact hin (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi))
      simp [Nat.choose_eq_zero_of_lt hai]
    _ = _ := by rw [Nat.add_choose_eq,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]


/-- Finite list sums through the optional count-state enumeration in (2.4). -/
theorem filterMap_sum {A B : Type*} (xs : List A) (f : A → Option B) (g : B → ℕ) :
    ((xs.filterMap f).map g).sum =
      (xs.map fun x => match f x with | none => 0 | some y => g y).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : f x <;> simp [List.filterMap_cons,h,ih]


/-- Finite sums over the successive potential-type loops in (2.4), p. 5. -/
theorem flatMap_sum {A B : Type*} (xs : List A) (f : A → List B) (g : B → ℕ) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons,List.map_append,List.sum_append,ih]


/-- Normalization of the actual finite design sums (2.4), rather than an
    assumption hidden inside the probability definitions. -/
theorem design_weight_total (v : Counts) (m : ℕ) (hm : m ≤ v.total) :
    ((randomStates v m).map (multiplicity v)).sum = v.total.choose m := by
  have inner (a b : ℕ) :
      (((List.range (min v.c (m-a-b)+1)).filterMap fun c =>
        if m-a-b-c ≤ v.d then some (⟨a,b,c,m-a-b-c⟩ : Counts) else none).map
        (multiplicity v)).sum =
      binomial v.a a*binomial v.b b*binomial (v.c+v.d) (m-a-b) := by
    rw [filterMap_sum]
    calc
      _ = ((List.range (min v.c (m-a-b)+1)).map fun c =>
          (binomial v.a a*binomial v.b b)*(binomial v.c c*binomial v.d (m-a-b-c))).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro c _hc
        by_cases hc : m-a-b-c ≤ v.d
        · simp [hc,multiplicity,Nat.mul_assoc]
        · have hz : binomial v.d (m-a-b-c) = 0 := by
            rw [binomial_eq_choose]
            exact Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hc)
          simp [hc,hz]
      _ = _ := by rw [List.sum_map_mul_left,bounded_vandermonde]
  unfold randomStates
  simp only [flatMap_sum,inner]
  simp_rw [Nat.mul_assoc,List.sum_map_mul_left,bounded_vandermonde]
  simp [Counts.total,Nat.add_assoc,binomial_eq_choose]


/-- Realized outcomes "Y_j=Z_j w_j(1)+(1-Z_j)w_j(0)", (2.5), p. 5. -/
def unitOutcomes {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ z then (w i).1 else (w i).2

/-- "Possible given the observed data", Section 2.1, p. 5, at labeled-unit level. -/
def PossibleTable {n : ℕ} (y : Fin n → Bool) (z : Finset (Fin n))
    (w : PotentialTable n) : Prop := unitOutcomes w z = y

/-- Neyman's observed-outcome estimator (2.7), p. 5, for a labeled binary vector. -/
noncomputable def outcomeEstimator {n : ℕ} (y : Fin n → Bool)
    (z : Finset (Fin n)) : ℝ :=
  (∑ i, if i ∈ z then bit (y i) else 0)/z.card -
    (∑ i, if i ∈ z then 0 else bit (y i))/(n-z.card)

/-- "Y⁺=1 if J=1,Z=1; Y⁺=0 if J=1,Z=0", Definition 6.1, p. 14.
    The set r consists of labels with J=1; off r the observed outcome is retained. -/
def unitPlus {n : ℕ} (y : Fin n → Bool) (z r : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ r then decide (i ∈ z) else y i

/-- The possibility-preserving repaired D.5-D.7 coupling (T2): replace only
    each originally observed coordinate by its plus-completion outcome. -/
def coupledPlus {n : ℕ} (w : PotentialTable n) (yPlus : Fin n → Bool)
    (z : Finset (Fin n)) : PotentialTable n :=
  fun i => if i ∈ z then (yPlus i,(w i).2) else ((w i).1,yPlus i)

/-- The labeled-table permutation p-value, Definition 2.1, (2.12), p. 6.
    This is uniform over every set of z.card treated units, independently of z. -/
noncomputable def unitPValue {n : ℕ} (w : PotentialTable n) (y : Fin n → Bool)
    (z : Finset (Fin n)) : ℝ :=
  uniformProb (fun q : Assignment n z.card =>
    |tableEstimator w q.val-tableTau w| ≥ |outcomeEstimator y z-tableTau w|)

/-- "n_zy = ∑ 1{Z_j=z,Y_j=y}", (2.8), p. 5, for labeled observed
    outcomes and a treatment set. This connects the coupling to its endpoints. -/
def unitObserved {n : ℕ} (y : Fin n → Bool) (z : Finset (Fin n)) : Counts :=
  ⟨(Finset.univ.filter fun i => i ∈ z ∧ y i = true).card,
   (Finset.univ.filter fun i => i ∈ z ∧ y i = false).card,
   (Finset.univ.filter fun i => i ∉ z ∧ y i = true).card,
   (Finset.univ.filter fun i => i ∉ z ∧ y i = false).card⟩


/-- T8: design median of the discrete Wald length distribution in Table 2.
    Both tails have probability at least one half under choose(m,k)² weights. -/
noncomputable def IsWaldMedian (L : ℕ → ℝ) (m : ℕ) (d : ℝ) : Prop :=
  ((∑ k ∈ Finset.range (m+1), if L k ≤ d then ((m.choose k : ℝ)^2) else 0) /
    ((2*m).choose m : ℝ) ≥ 1/2) ∧
  ((∑ k ∈ Finset.range (m+1), if d ≤ L k then ((m.choose k : ℝ)^2) else 0) /
    ((2*m).choose m : ℝ) ≥ 1/2)


/-- T9's two equiprobable atoms have X₁=X₂=0 or X₁=X₂=1; this finite sum
    explicitly supplies both marginals and the dependent sum distribution. -/
theorem dependent_joint_law (i : ℤ) :
    (∑ b : Bool, if (if b then (1 : ℤ) else 0) = i then (1/2 : ℝ) else 0) =
      fairMass i ∧
    (∑ b : Bool, if (if b then (1 : ℤ) else 0)+(if b then (1 : ℤ) else 0) = i
      then (1/2 : ℝ) else 0) = dependentSumMass i := by
  simp only [Fintype.sum_bool, Bool.false_eq_true,  ite_false, ite_true]
  constructor <;> simp [fairMass,dependentSumMass,eq_comm,add_comm]


/-- T18(ii): Fisher-Yates iterations of Algorithm 4.5's actual upper search
    with T5's search repair. Every table test uses K shuffles of n-1 iterations;
    the first midpoint is the same as the printed search in the witness family. -/
noncomputable def upperShuffleCost {n K : ℕ} (α ε : ℝ) (o : Counts)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n (n/2)) : ℕ :=
  (upperRun true o (approximateReject α ε o pool)).trace.length*K*(n-1)

/-- Expected upper-search shuffle iterations under the independent finite
    Monte Carlo law, T18(ii); data is fixed, so no observed assignment is sampled. -/
noncomputable def expectedUpperShuffleCost (α ε : ℝ) (n K : ℕ) (o : Counts) : ℝ :=
  (∑ pool : Fin (2*testBudget n+1) → Fin K → Assignment n (n/2),
    (upperShuffleCost α ε o pool : ℝ)) /
      Fintype.card (Fin (2*testBudget n+1) → Fin K → Assignment n (n/2))


/-- T6(E): first chronological table-decision mismatch, zero based; N denotes
    the no-mismatch sentinel corresponding to the paper's J=N+1, pp. 27-28. -/
def firstMismatch (a b : List (Counts × Bool)) : ℕ :=
  match (a.zip b).findIdx? (fun p => p.1.2 != p.2.2) with
  | some i => i
  | none => a.length


/-- T3's rational interval hull of all nonempty completion inversions.
    This is the count-enumeration form of the corrected Hα, Appendix D, p. 29. -/
def completionHullQ (α : ℚ) (o r : Counts) : Option (ℚ × ℚ) :=
  match (completions o r).filterMap (intervalQ α) with
  | [] => none
  | I::Is => some (Is.foldl (fun l J => min l J.1) I.1,
                  Is.foldl (fun u J => max u J.2) I.2)

/-- Exact design coverage of the repaired completion hull in T1's experiment. -/
def badHullCoverage : ℚ :=
  ((randomStates badPopulation 3).map fun q =>
    match completionHullQ (109/500) (observed badPopulation q) (badMask q) with
    | none => 0
    | some (l,u) => if l ≤ tauQ badPopulation ∧ tauQ badPopulation ≤ u
        then multiplicity badPopulation q else 0).sum / (1140 : ℚ)

theorem critical_hull_certificate :
    completionHullQ (109/500) ⟨0,3,11,6⟩ ⟨0,0,1,0⟩ = some (-7/10,-3/20) := by
  unfold completionHullQ
  rw [critical_completions_certificate]
  norm_num [List.filterMap_cons, List.filterMap_nil, List.foldl_cons, List.foldl_nil,
    interval_obs_0_3_11_6, interval_obs_0_3_10_7]

theorem hull_zero_mask_certificate (α : ℚ) (o : Counts) :
    completionHullQ α o ⟨0,0,0,0⟩ = intervalQ α o := by
  unfold completionHullQ
  rw [zero_mask_completions_certificate]
  cases h : intervalQ α o <;> simp [List.filterMap_cons, h]

theorem badHullCoverage_certificate : badHullCoverage = 892/1140 := by
  unfold badHullCoverage
  rw [bad_random_states_certificate]
  norm_num [observed, badMask,
    hull_zero_mask_certificate, critical_hull_certificate,
    interval_obs_0_3_14_3,
    interval_obs_0_3_13_4,
    interval_obs_0_3_12_5,
    interval_obs_0_3_11_6,
    interval_obs_1_2_13_4,
    interval_obs_1_2_12_5,
    interval_obs_1_2_11_6,
    interval_obs_2_1_12_5,
    interval_obs_2_1_11_6,
    interval_obs_3_0_11_6,
    interval_obs_0_3_10_7,
    tauQ, badPopulation, Counts.effect, Counts.total, multiplicity, binomial, Nat.fast_choose]

/-- T3(d): the repaired hull covers the missing observation and has actual
    coverage 892/1140≥391/500 in the counterexample to the printed interval. -/
theorem repaired_hull_example :
    completionHullQ (109/500) ⟨0,3,11,6⟩ ⟨0,0,1,0⟩ = some (-7/10,-3/20) ∧
    badHullCoverage = 892/1140 ∧ (391/500 : ℚ) ≤ badHullCoverage := by
  refine ⟨critical_hull_certificate, badHullCoverage_certificate, ?_⟩
  rw [badHullCoverage_certificate]
  norm_num


/-- Every enumerated randomization state has legal type counts and exactly m
    treated units, for the complete-randomization law (2.4), p. 5. -/
theorem random_state_facts (v : Counts) (m : ℕ) (q : Counts)
    (hq : q ∈ randomStates v m) :
    q.a ≤ v.a ∧ q.b ≤ v.b ∧ q.c ≤ v.c ∧ q.d ≤ v.d ∧ q.total = m := by
  simp only [randomStates,List.mem_flatMap,List.mem_filterMap] at hq
  rcases hq with ⟨a,ha,b,hb,c,hc,hret⟩
  have ha' := Nat.le_of_lt_succ (List.mem_range.mp ha)
  have hb' := Nat.le_of_lt_succ (List.mem_range.mp hb)
  have hc' := Nat.le_of_lt_succ (List.mem_range.mp hc)
  have hav := le_trans ha' (Nat.min_le_left _ _)
  have ham := le_trans ha' (Nat.min_le_right _ _)
  have hbv := le_trans hb' (Nat.min_le_left _ _)
  have hbm := le_trans hb' (Nat.min_le_right _ _)
  have hcv := le_trans hc' (Nat.min_le_left _ _)
  have hcm := le_trans hc' (Nat.min_le_right _ _)
  by_cases hd : m-a-b-c ≤ v.d
  · simp only [if_pos hd,Option.some.injEq] at hret
    subst q
    dsimp [Counts.total]
    omega
  · simp [hd] at hret


/-- The true potential table is possible under every actual assignment, the
    pointwise finite fact used in Proposition 3.2, (A.7)-(A.8), p. 19. -/
theorem observed_population_possible (v : Counts) (m : ℕ) (q : Counts)
    (hq : q ∈ randomStates v m) : Possible (observed v q) v := by
  rcases random_state_facts v m q hq with ⟨ha,hb,hc,hd,ht⟩
  simp only [Possible,possibleTables,observed,List.mem_flatMap,List.mem_map,List.mem_range]
  refine ⟨q.a,?_,q.c,?_,v.a-q.a,?_,v.b-q.b,?_,?_⟩
  · omega
  · omega
  · omega
  · omega
  · ext <;> dsimp <;> omega


/-- Every imputation count vector has the observed total and an effect in the
    full n+1 candidate lattice, (2.10),(2.13)-(2.14), p. 6. -/
theorem possible_table_facts (o v : Counts) (hv : Possible o v) :
    v.total = o.total ∧ v.effect ∈ candidateNumerators o := by
  simp only [Possible,possibleTables,List.mem_flatMap,List.mem_map,List.mem_range] at hv
  rcases hv with ⟨i,hi,j,hj,k,hk,l,hl,rfl⟩
  constructor
  · dsimp [Counts.total]
    omega
  · simp only [candidateNumerators,List.mem_map,List.mem_range]
    refine ⟨(o.a-i)+(o.b-j)+k+l,?_,?_⟩
    · dsimp [Counts.total]
      omega
    · dsimp [Counts.effect]
      omega


/-- T22: with the corrected j continuation, every possible vector belongs to
    the initial table or its reuse line; no possible null is silently skipped. -/
theorem corrected_general_loop (o u : Counts) (hu : Possible o u) :
    u.effect ∈ candidateNumerators o ∧ u.a+u.b ≤ o.total ∧
    ∃ v, firstOnLine o u.effect (u.a+u.b) = some v ∧
      ∃ k ≤ o.total, k ≤ v.a ∧ k ≤ v.d ∧ u = reuseVector v k := by
  have hut := possible_table_facts o u hu
  have hub : u.a+u.b ≤ o.total := by
    rw [←hut.1]
    unfold Counts.total
    omega
  have humem : u ∈ lineGroup o u.effect (u.a+u.b) := by
    simp [lineGroup]
    exact hu
  have hex : ∃ v, firstOnLine o u.effect (u.a+u.b) = some v := by
    cases h : firstOnLine o u.effect (u.a+u.b) with
    | none =>
      have hn := (minimum_b_spec (lineGroup o u.effect (u.a+u.b))).1.mp h
      rw [hn] at humem
      simp at humem
    | some v => exact ⟨v,rfl⟩
  obtain ⟨v,hv⟩ := hex
  have hvs := first_on_line_spec o u.effect (u.a+u.b) v hv
  have hvt := (possible_table_facts o v hvs.1).1
  have hb := hvs.2.2.2 u hu rfl rfl
  have he := hvs.2.1
  have hj := hvs.2.2.1
  let k := u.b-v.b
  refine ⟨hut.2,hub,v,hv,k,?_,?_,?_,?_⟩
  · dsimp [k]
    omega
  · dsimp [k]
    omega
  · dsimp [k]
    unfold Counts.effect at he
    unfold Counts.total at hut hvt
    omega
  · apply Counts.ext <;> dsimp [reuseVector,k]
    · omega
    · omega
    · unfold Counts.effect at he
      omega
    · unfold Counts.effect at he
      unfold Counts.total at hut hvt
      omega


/-- A possible table with p≥α contributes its actual SATE to K, (2.15), p. 6.
    This is the acceptance-to-inversion step of Proposition 3.2. -/
theorem accepted_of_possible (α : ℝ) (o v : Counts) (hv : Possible o v)
    (hp : α ≤ (pValue v o : ℝ)) : tau v ∈ accepted α o := by
  classical
  unfold accepted
  apply Finset.mem_image.mpr
  refine ⟨v,?_,rfl⟩
  simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
  exact ⟨hv,hp⟩


/-- The accepted set K lies in its interval hull I, Algorithms 2.3 and (2.16),
    p. 6, including the empty-set convention. -/
theorem accepted_subset_interval (α : ℝ) (o : Counts) :
    (↑(accepted α o) : Set ℝ) ⊆ exactInterval α o := by
  intro t ht
  exact ⟨t,ht,t,ht,le_rfl,le_rfl⟩


/-- Pointwise finite inversion fact in (A.7)-(A.8), p. 19: if the true table's
    actual randomization p-value is accepted, the exact interval covers its SATE. -/
theorem true_table_acceptance_covers (v : Counts) (m : ℕ) (q : Counts) (α : ℝ)
    (hq : q ∈ randomStates v m) (hp : α ≤ (pValue v (observed v q) : ℝ)) :
    tau v ∈ exactInterval α (observed v q) := by
  exact accepted_subset_interval α (observed v q)
    (accepted_of_possible α (observed v q) v (observed_population_possible v m q hq) hp)


/-- Finite indexing of a list sum, used for the actual randomization sums
    in Proposition 3.2, Appendix A.2, p. 19. -/
theorem list_sum_as_fin {A : Type*} (xs : List A) (f : A → ℝ) :
    (xs.map f).sum = ∑ i : Fin xs.length, f xs[i.val] := by
  rw [← List.ofFn_getElem_eq_map xs f,List.sum_ofFn]


/-- Dividing a finite event sum gives the sum of its atom probabilities;
    this algebraic identity is used with the actual positive choose(n,m) normalizer. -/
theorem list_event_ratio {A : Type*} (xs : List A) (f : A → ℝ) (d : ℝ) (E : A → Prop)
    [DecidablePred E] :
    (xs.map fun x => if E x then f x else 0).sum/d =
      ∑ i : Fin xs.length, if E xs[i.val] then f xs[i.val]/d else 0 := by
  calc
    _ = (xs.map fun x => if E x then f x/d else 0).sum := by
      induction xs with
      | nil => simp
      | cons x xs ih =>
        by_cases hx : E x <;> simp [hx,List.map_cons,List.sum_cons,add_div,ih]
    _ = _ := list_sum_as_fin xs (fun x => if E x then f x/d else 0)


/-- The genuine finite design probability (2.4) as an indexed sum of event
    masses. It uses the same weights and denominator as designProb. -/
theorem design_prob_as_fin (v : Counts) (m : ℕ) (E : Counts → Prop) :
    designProb v m E =
      ∑ i : Fin (randomStates v m).length,
        if E (randomStates v m)[i.val]
        then (multiplicity v (randomStates v m)[i.val] : ℝ)/v.total.choose m else 0 := by
  exact list_event_ratio (randomStates v m) (fun q => (multiplicity v q : ℝ))
    (v.total.choose m) E


/-- Actual complete-randomization atom masses sum to one, (2.4), p. 5.
    No normalization or zero-measure hypothesis is assumed. -/
theorem design_mass_total (v : Counts) (m : ℕ) (hm : m ≤ v.total) :
    (∑ i : Fin (randomStates v m).length,
      (multiplicity v (randomStates v m)[i.val] : ℝ)/v.total.choose m) = 1 := by
  have hw : ((randomStates v m).map fun q => (multiplicity v q : ℝ)).sum =
      (v.total.choose m : ℝ) := by
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using
      congrArg (fun k : ℕ => (k : ℝ)) (design_weight_total v m hm)
  have hd : (v.total.choose m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hm))
  have he := design_prob_as_fin v m (fun _ => True)
  simp only [if_true] at he
  rw [← he]
  unfold designProb
  simp only [if_true]
  rw [hw]
  exact div_self hd


/-- The true-table p-value is its actual finite randomization tail, (A.9),
    p. 19. Integer deviations are scaled by the same positive n*m*(n-m).
    This theorem identifies the implemented probability with the weighted tail;
    it does not posit a probability law as an additional hypothesis. -/
theorem design_tail_at_state (v : Counts) (m : ℕ) (q : Counts)
    (hq : q ∈ randomStates v m) :
    let xs := randomStates v m
    let w : Fin xs.length → ℝ := fun i => (multiplicity v xs[i.val] : ℝ)/v.total.choose m
    let D : Fin xs.length → ℝ := fun i =>
      ((deviationNumerator v (observed v xs[i.val]) m).natAbs : ℝ)
    (pValue v (observed v q) : ℝ) =
      finiteTail w D ((deviationNumerator v (observed v q) m).natAbs : ℝ) := by
  dsimp
  have hmObs : (observed v q).a+(observed v q).b = m := by
    have ht := (random_state_facts v m q hq).2.2.2.2
    simpa [observed,Counts.total,Nat.add_assoc] using ht
  unfold pValue tailCount
  simp only [hmObs,Rat.cast_div,Rat.cast_natCast,binomial_eq_choose]
  rw [Nat.cast_list_sum]
  simp only [List.map_map,Function.comp_def]
  have hmap :
      (fun t : Counts => ((if (deviationNumerator v (observed v t) m).natAbs ≥
        (deviationNumerator v (observed v q) m).natAbs then multiplicity v t else 0 : ℕ) : ℝ)) =
      (fun t => if (deviationNumerator v (observed v t) m).natAbs ≥
        (deviationNumerator v (observed v q) m).natAbs then (multiplicity v t : ℝ) else 0) := by
    funext t
    split_ifs <;> simp
  rw [hmap]
  refine (list_event_ratio (randomStates v m) (fun t => (multiplicity v t : ℝ))
    (v.total.choose m) (fun t => (deviationNumerator v (observed v t) m).natAbs ≥
      (deviationNumerator v (observed v q) m).natAbs)).trans ?_
  unfold finiteTail
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.cast_le]


/-- Missing-cell counts are bounded by the corresponding observed cells,
    the exact count form of the mask J in (6.1), p. 13. -/
theorem missing_mask_facts (o r : Counts) (hr : r ∈ missingMasks o) :
    r.a ≤ o.a ∧ r.b ≤ o.b ∧ r.c ≤ o.c ∧ r.d ≤ o.d := by
  simp only [missingMasks,List.mem_flatMap,List.mem_map,List.mem_range] at hr
  rcases hr with ⟨a,ha,b,hb,c,hc,d,hd,rfl⟩
  dsimp
  omega


/-- The true complete observation is one of the possible completions,
    Appendix D's pointwise inclusion (D.2), p. 29, for any legal missingness. -/
theorem true_observation_is_completion (o r : Counts) (hr : r ∈ missingMasks o) :
    o ∈ completions o r := by
  rcases missing_mask_facts o r hr with ⟨ha,hb,hc,hd⟩
  simp only [completions,List.mem_flatMap,List.mem_map,List.mem_range]
  refine ⟨r.a,by omega,r.c,by omega,?_⟩
  ext <;> dsimp <;> omega


/-- T3: the actual complete data is a completion, and the number of distinct
    completed observed count vectors is exactly (r₁+1)(r₀+1), Appendix D. -/
theorem completion_finite_facts (o r : Counts) (hr : r ∈ missingMasks o) :
    o ∈ completions o r ∧
    (completions o r).Nodup ∧
    (completions o r).length = (r.a+r.b+1)*(r.c+r.d+1) := by
  let f : ℕ × ℕ → Counts := fun tc =>
    ⟨o.a-r.a+tc.1, o.b-r.b+(r.a+r.b-tc.1),
      o.c-r.c+tc.2, o.d-r.d+(r.c+r.d-tc.2)⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Prod.ext
    · have hh := congrArg Counts.a h
      dsimp [f] at hh
      omega
    · have hh := congrArg Counts.c h
      dsimp [f] at hh
      omega
  have he : completions o r =
      ((List.range (r.a+r.b+1)).product (List.range (r.c+r.d+1))).map f := by
    simp [completions,List.product,List.map_flatMap,List.map_map,Function.comp_def,f]
  refine ⟨true_observation_is_completion o r hr,?_,?_⟩
  · rw [he]
    exact (List.nodup_range.product List.nodup_range).map hinj
  · rw [he,List.length_map]
    have hprod (xs ys : List ℕ) : (xs.product ys).length = xs.length*ys.length := by
      induction xs with
      | nil => simp [List.product]
      | cons x xs ih =>
        simpa only [List.product,List.flatMap_cons,List.length_append,List.length_map,
          List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using
          congrArg (fun k => ys.length+k) ih
    rw [hprod,List.length_range,List.length_range]


/-- The true complete-data interval is included in the completion union,
    the first pointwise step of repaired Proposition 6.2, Appendix D, p. 29. -/
theorem complete_interval_subset_union (α : ℝ) (o r : Counts)
    (hr : r ∈ missingMasks o) : exactInterval α o ⊆ completionUnion α o r := by
  intro t ht
  exact ⟨o,true_observation_is_completion o r hr,ht⟩


/-- Monotonicity of actual finite real sums, used for the arbitrary joint
    randomization/missingness law in the repaired Proposition 6.2. -/
theorem list_real_sum_le {A : Type*} (xs : List A) (f g : A → ℝ)
    (hfg : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hfg x (by simp)
    have ht := ih (fun y hy => hfg y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons]
    linarith


/-- A pointwise completion inclusion preserves the complete-data event's
    probability under every joint law with the prescribed design marginal,
    the corrected joint-probability argument for Proposition 6.2, p. 14. -/
theorem missing_probability_of_pointwise (v : Counts) (m : ℕ)
    (μ : Counts → Counts → ℝ) (hμ : IsMissingLaw v m μ)
    (E₀ : Counts → Prop) (E : Counts → Counts → Prop)
    (hinc : ∀ q ∈ randomStates v m, ∀ r ∈ missingMasks (observed v q), E₀ q → E q r) :
    designProb v m E₀ ≤ missingProb v m μ E := by
  classical
  rw [design_prob_as_fin]
  unfold missingProb
  rw [list_sum_as_fin]
  apply Finset.sum_le_sum
  intro i hi
  let q := (randomStates v m)[i.val]
  have hq : q ∈ randomStates v m := List.getElem_mem i.isLt
  by_cases hc : E₀ q
  · simp only [show (randomStates v m)[i.val] = q from rfl,if_pos hc]
    rw [← hμ.2 q hq]
    apply list_real_sum_le
    intro r hr
    rw [if_pos (hinc q hq r hr hc)]
  · simp only [show (randomStates v m)[i.val] = q from rfl,if_neg hc]
    have hnon := list_real_sum_le (missingMasks (observed v q)) (fun _ => (0 : ℝ))
      (fun r => if E q r then μ q r else 0) (by
        intro r hr
        split_ifs
        · exact hμ.1 q hq r hr
        · exact le_rfl)
    simpa using hnon


/-- Proposition 3.2, T29, p. 7: exact finite-sample coverage for every allocation. -/
theorem exact_coverage (v : Counts) (m : ℕ) (α : ℝ)
    (hm : 0 < m ∧ m < v.total) (hα : 0 < α ∧ α < 1) :
    designProb v m (fun q => tau v ∈ exactInterval α (observed v q)) ≥ 1-α := by
  let xs := randomStates v m
  let w : Fin xs.length → ℝ := fun i => (multiplicity v xs[i.val] : ℝ)/v.total.choose m
  let D : Fin xs.length → ℝ := fun i =>
    ((deviationNumerator v (observed v xs[i.val]) m).natAbs : ℝ)
  have hw : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; positivity
  have hn : ∑ i, w i = 1 := design_mass_total v m (Nat.le_of_lt hm.2)
  have hp (i : Fin xs.length) :
      (pValue v (observed v xs[i.val]) : ℝ) = finiteTail w D (D i) := by
    exact design_tail_at_state v m xs[i.val] (List.getElem_mem i.isLt)
  have hrej := (finite_tail_repair w D hw hn α hα).2
  let C : Fin xs.length → ℝ := fun i =>
    if tau v ∈ exactInterval α (observed v xs[i.val]) then w i else 0
  let R : Fin xs.length → ℝ := fun i => if finiteTail w D (D i) < α then w i else 0
  have hpoint (i : Fin xs.length) : w i ≤ C i+R i := by
    by_cases hc : tau v ∈ exactInterval α (observed v xs[i.val])
    · have hR : 0 ≤ R i := by dsimp [R]; split_ifs <;> positivity
      simp only [C,if_pos hc]
      linarith
    · have hr : finiteTail w D (D i) < α := by
        by_contra h
        have hαp : α ≤ (pValue v (observed v xs[i.val]) : ℝ) := by
          rw [hp i]
          exact le_of_not_gt h
        exact hc (true_table_acceptance_covers v m xs[i.val] α
          (List.getElem_mem i.isLt) hαp)
      simp [C,R,hc,hr]
  have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin xs.length))) => hpoint i)
  rw [Finset.sum_add_distrib,hn] at hsum
  have hc : designProb v m (fun q => tau v ∈ exactInterval α (observed v q)) = ∑ i, C i :=
    design_prob_as_fin v m (fun q => tau v ∈ exactInterval α (observed v q))
  rw [hc]
  change (∑ i, C i) ≥ 1-α
  change (∑ i, R i) < α at hrej
  linarith


/-- T3: arbitrary allocation, corrected to the completion union and its interval hull. -/
theorem completion_coverage (v : Counts) (m : ℕ) (α : ℝ)
    (hm : 0 < m ∧ m < v.total) (hα : 0 < α ∧ α < 1)
    (μ : Counts → Counts → ℝ) (hμ : IsMissingLaw v m μ) :
    missingProb v m μ (fun q r => tau v ∈ completionUnion α (observed v q) r) ≥ 1-α ∧
    missingProb v m μ (fun q r => tau v ∈ completionHull α (observed v q) r) ≥ 1-α := by
  have hcover := exact_coverage v m α hm hα
  constructor
  · apply le_trans hcover
    apply missing_probability_of_pointwise v m μ hμ
      (fun q => tau v ∈ exactInterval α (observed v q))
      (fun q r => tau v ∈ completionUnion α (observed v q) r)
    intro q hq r hr ht
    exact complete_interval_subset_union α (observed v q) r hr ht
  · apply le_trans hcover
    apply missing_probability_of_pointwise v m μ hμ
      (fun q => tau v ∈ exactInterval α (observed v q))
      (fun q r => tau v ∈ completionHull α (observed v q) r)
    intro q hq r hr ht
    exact completion_union_subset_hull α (observed v q) r
      (complete_interval_subset_union α (observed v q) r hr ht)


/-- Lemma 3.1, T30, p. 7: the balanced interval contains the observed estimate.
    Nonemptiness is a conclusion, not an added hypothesis. -/
theorem balanced_estimate_in_interval (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : 0 < α ∧ α < 1) :
    estimate o ∈ accepted α o ∧ estimate o ∈ exactInterval α o ∧
    lower α o ≤ estimate o ∧ estimate o ≤ upper α o := by
  let v : Counts := ⟨0,o.a+o.d,o.c+o.b,0⟩
  have hv : Possible o v := by
    simp only [Possible,possibleTables,List.mem_flatMap,List.mem_map,List.mem_range]
    refine ⟨0,by omega,o.b,by omega,0,by omega,o.d,by omega,?_⟩
    ext <;> dsimp [v] <;> omega
  have htot : v.total = o.total := (possible_table_facts o v hv).1
  have hn : v.total = 2*(o.a+o.b) := by
    rw [htot]
    unfold Counts.total
    omega
  have hQ : (o.a : ℚ)+o.b = (o.c : ℚ)+o.d := by exact_mod_cast ho.2
  have hden : (o.a : ℚ)+o.b ≠ 0 := by
    have hp : (0 : ℚ) < o.a+o.b := by exact_mod_cast ho.1
    exact ne_of_gt hp
  have heQ : tauQ v = estimateQ o := by
    dsimp [tauQ,estimateQ,v,Counts.effect,Counts.total]
    push_cast
    have htotal : (o.a : ℚ)+o.d+(o.c+o.b) = 2*(o.a+o.b) := by linarith
    simp only [zero_add]
    rw [htotal,←hQ]
    field_simp
    linarith
  have he : tau v = estimate o := by
    exact congrArg (fun x : ℚ => (x : ℝ)) heQ
  have hdev : deviationNumerator v o (o.a+o.b) = 0 := by
    have hd : (o.d : ℤ) = o.a+o.b-o.c := by
      have hb : (o.a : ℤ)+o.b = (o.c : ℤ)+o.d := by exact_mod_cast ho.2
      omega
    dsimp [deviationNumerator,v,Counts.total,Counts.effect]
    push_cast
    rw [hd]
    ring
  have htail : tailCount v o = v.total.choose (o.a+o.b) := by
    simp only [tailCount,hdev,Int.natAbs_zero,Nat.zero_le,ite_true]
    exact design_weight_total v (o.a+o.b) (by omega)
  have hp : pValue v o = 1 := by
    rw [pValue,htail,binomial_eq_choose]
    apply div_self
    exact_mod_cast (Nat.choose_pos (show o.a+o.b ≤ v.total by omega)).ne'
  have hacc : estimate o ∈ accepted α o := by
    rw [←he]
    apply accepted_of_possible α o v hv
    rw [hp]
    simpa only [Rat.cast_one] using hα.2.le
  refine ⟨hacc,accepted_subset_interval α o hacc,?_,?_⟩
  · exact csInf_le (accepted α o).finite_toSet.bddBelow hacc
  · exact le_csSup (accepted α o).finite_toSet.bddAbove hacc


end AronowAudit.P003

