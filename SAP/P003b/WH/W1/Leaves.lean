import SAP.P003b.WH.W1.ProbabilityGlue
import SAP.P003b.WH.W1.T6Exports
import SAP.P003b.WH.W1.T35Exports

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W1
open SAP.P003b SAP.P003b.Bridge
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000

/-- Draw-count rate at fixed positive tolerance. Use recommended_k_log_bound to bound
K by C log n eventually. Multiply the actual test bound and rewrite logTwo; an
IsBigO.of_bound proof with constant 4C/log 2 finishes. No concentration argument. -/
def T18_L1 : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (tests : ℕ → ℕ),
    (∀ᶠ n in Filter.atTop, (tests n : ℝ) ≤ 4*(n : ℝ)*logTwo n) →
    (fun n => (tests n : ℝ)*recommendedK ε n) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ)*(Real.log n)^2)

/-- The fixed-epsilon displayed (1.6) rate dominates n² log² n. Eventually n≥1
and log n≥ε>0, so log(n log n/ε)≥log n by log monotonicity. Use an eventual
norm bound with constant ε²; the limit of log along naturals supplies the threshold. -/
def T18_L2 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun n : ℕ => (n : ℝ)^2*(Real.log n)^2) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ)^2*Real.log n/ε^2*
        Real.log ((n : ℝ)*Real.log n/ε))

/-- First-feasible-line costs are bounded by full-j costs, for all counts and K.
For each candidate numerator, a nonempty literal base is one actual firstOnLine
entry in range(n+1). Its fresh K draws and K times its reuseLine length are a
single nonnegative summand of the full-j sum. Prove that membership from
filterMap/head?, apply single_le_sum (or a list-sum bound), then sum over x. -/
def T18_L3 : Prop :=
  ∀ (o : Counts) (K : ℕ),
    w1LiteralDrawCount o K ≤ generalDrawCount o K ∧
    w1LiteralUpdateCount o K ≤ generalUpdateCount o K

/-- Instrumented corrected search budget. Induct on the shrinking integer bracket:
a queried midpoint is strictly interior and becomes a boundary, so it cannot recur.
The next width is at most ceil(width/2), giving ceil(logTwo(n+2)) queries.
Sum queryCosts over the instrumentation; only the unique zero query gets an extra
(n+1) block. Convert the logarithmic ceiling with natural power bounds and combine
with allStartBudget. All starts idx and all decision functions are included. -/
def T7_L1 : Prop := W1T7Budget

/-- Conditional upper-test law for every positive-mass raw preceding history.
Use GLP0032B6_upperRun_prefix to show the chosen table and performed indicator
are fixed by earlier batches (peek drops the current decision). A history fiber
is a cylinder in the first i product coordinates. Split off coordinate i with
Equiv.funSplitAt, count that fiber, and apply GLP0032B6_fixed_errors to its fixed
possible table. Unreached positions contribute zero. This proves both errors and
the exact conditional uniform-batch law, hence conditional iid draws. -/
def T7_L2 : Prop := W1T7Conditional false

/-- Conditional reflected lower-test law, including the completed upper history.
First show that the upper test count is a stopping time for the batch prefix,
using GLP0032B6_upperRun_prefix. On a w1History true i fiber its length fixes the
upper stopping index; completing any unused suffix preserves that stop and the
selected lower table. The fiber is consequently a cylinder of that fixed length.
Split off its next coordinate and apply the same finite counting and fixed_errors
argument as for the upper endpoint. The D+D budget prevents modulo wraparound.
Do not assume independence of the two endpoint lengths or of reused decisions. -/
def T7_L3 : Prop := W1T7Conditional true

/-- Exactly 896 distinct possible count vectors for the fixed n=30 data.
Count (possibleTables adaptiveData).toFinset, not the duplicated four-index list.
A kernel computation with decide +kernel (increase maxRecDepth locally if needed),
or a verified deduplication/count certificate, proves this finite identity. -/
def T6_L1 : Prop := (possibleTables adaptiveData).toFinset.card = 896

/-- The four actual conditional probabilities round to the printed five-place
approximations. Identify events 0/2 with api5_probability_value_actual and the
below/above certificates, and events 1/3 with api5_probability_actual and the bad
rejection/acceptance certificates. Transport with the Counts and trace bridges.
Each mass is api5_weight over the corresponding api5_result_0,...,_3 tree.
Exact rational comparisons give the strict radius 1/200000; cast to reals.
Enumeration of the assignment pool is unnecessary. -/
def T6_L2 : Prop := W1T6Rounding

/-- Literal Algorithm 5.3 misses the true vector on the all-zero observation and
includes it on the all-one observation, for every draw path and every positive K.
Use rankZero to remove every random sample from the membership predicate. Expand
w1LiteralBase at the three candidate numerators and three j slots of each n=2
observation. All selected bases have a=0 or d=0, so only k=0 can be legal.
The remaining finite memberships are decidable; the missed feasible line is also
exhibited by AronowAudit.P003.omitted_loop_witness. -/
def T35_L1 : Prop :=
  ∀ (K : ℕ), 0 < K →
  ∀ (initial : (Fin 3 × Fin 3) → Fin K → Assignment 2 1)
    (seeds : (Fin 3 × Fin 3) → Fin 2 → Fin K → (Fin (Nat.factorial 2) × Fin (Nat.factorial 2))),
    w1T35Theta w1T35Population ∉
      w1LiteralSet (1/4) w1T35Theta (fun _ _ => 0) ⟨0,1,0,1⟩ initial seeds ∧
    w1T35Theta w1T35Population ∈
      w1LiteralSet (1/4) w1T35Theta (fun _ _ => 0) ⟨1,0,1,0⟩ initial seeds

/-- Assemble the full corrected runtime claim, including the literal unbalanced charge. -/
theorem T18_assembly (h1 : T18_L1) (h2 : T18_L2) (h3 : T18_L3) : T18WholeStatement := by
  have hrates : W1T18Rates := by
    refine ⟨h1,?_⟩
    intro ε c hε hc
    have he : balancedEnvelope ε c =O[Filter.atTop]
        (fun n : ℕ => (n : ℝ)^2*(Real.log n)^2) :=
      AronowAudit.P003.balanced_complexity ε c hε hc
    exact ⟨he,he.trans (h2 ε hε)⟩
  have hliteral : W1T18LiteralBound := by
    intro o K c₀ c₁ c₂ hc hn hK
    have hd := (h3 o K).1
    have hu := (h3 o K).2
    have hdr : (w1LiteralDrawCount o K : ℝ) ≤ generalDrawCount o K := by exact_mod_cast hd
    have hur : (w1LiteralUpdateCount o K : ℝ) ≤ generalUpdateCount o K := by exact_mod_cast hu
    have hc₁ := hc.2.1
    have hc₂ := hc.2.2
    have hb : w1LiteralOperations o K c₀ c₁ c₂ ≤ generalOperations o K c₀ c₁ c₂ := by
      have hdraw := mul_le_mul_of_nonneg_left hdr (show 0 ≤ 2*c₁*o.total by positivity)
      have hupdate := mul_le_mul_of_nonneg_left hur (show 0 ≤ 2*c₂ by positivity)
      unfold w1LiteralOperations generalOperations
      linarith
    exact ⟨hd,hu,hb,hb.trans ((t18General.1 o K c₀ c₁ c₂ hc).2.2.2 hn hK)⟩
  exact ⟨T18_base,t18Finite,hrates,t18General,hliteral,t18Budgets,t18AllExponents⟩

/-- All exact-oracle, endpoint and B.10 clauses are already proved donors. -/
theorem T32_assembly : T32WholeStatement := by
  refine ⟨T32_base,t32Oracle,queryCosts,budgetFloor,?_⟩
  intro n hn
  simpa only [testBudget_eq,logTwo_eq] using
    AronowAudit.P003.Wave1.GP0032B1b_two_budget_le n hn

/-- Finite-history averaging and the union bound are proved in endpointErrors. -/
theorem T7_assembly (h1 : T7_L1) (h2 : T7_L2) (h3 : T7_L3) : T7WholeStatement := by
  exact ⟨T7_base,budgetFloor,queryCosts,h1,h2,h3,endpointErrors h2 h3,
    t7Comparisons,conditionalInclusions,t7Labeled⟩

/-- Existing exact certificates supply every transcript and p-value; expose the
actual aggregate sum by its second nonnegative summand. -/
theorem T6_assembly (h1 : T6_L1) (h2 : T6_L2) : T6WholeStatement := by
  exact ⟨T6_base,t6Range,by norm_num [adaptiveData],by norm_num [adaptiveData],
    h1,t6Candidates,t6PValues,t6Traces,h2,t6Aggregate⟩

/-- The deterministic two-observation calculation gives coverage exactly one half
under all fresh draws and reuse seeds; their independent coordinate cancels. -/
theorem T35_assembly (h1 : T35_L1) : T35WholeStatement := by
  refine ⟨rfl,t35Support.1,t35Support.2.1,t35Support.2.2.1,t35Support.2.2.2,rankZero,?_⟩
  intro K hK
  letI : Nonempty (Assignment 2 1) := ⟨⟨{0},by simp⟩⟩
  let B := ((Fin 3 × Fin 3) → Fin K → Assignment 2 1) ×
    ((Fin 3 × Fin 3) → Fin 2 → Fin K → (Fin (Nat.factorial 2) × Fin (Nat.factorial 2)))
  letI : Nonempty B := ⟨(fun _ _ => ⟨{0},by simp⟩),
    (fun _ _ _ => (⟨0,by decide⟩,⟨0,by decide⟩))⟩
  have he : (fun ω : GeneralSpace 2 1 K => w1T35Theta w1T35Population ∈
      w1LiteralSet (1/4) w1T35Theta (fun _ _ => 0)
        (canonicalObserved w1T35Population ω.1.val) ω.2.1 ω.2.2) =
      (fun ω => canonicalObserved w1T35Population ω.1.val = ⟨1,0,1,0⟩) := by
    funext ω
    apply propext
    have hh := h1 K hK ω.2.1 ω.2.2
    rcases t35Observations ω.1 with hz | hz
    · rw [hz]
      simp only [hh.1,Counts.mk.injEq,false_and,and_false,not_false_eq_true]
      decide
    · rw [hz]
      simp only [hh.2]
  have hp : uniformProb (fun ω : GeneralSpace 2 1 K => w1T35Theta w1T35Population ∈
      w1LiteralSet (1/4) w1T35Theta (fun _ _ => 0)
        (canonicalObserved w1T35Population ω.1.val) ω.2.1 ω.2.2) = 1/2 := by
    rw [he]
    exact (probability_first
      (B := B)
      (fun z : Assignment 2 1 => canonicalObserved w1T35Population z.val = (⟨1,0,1,0⟩ : Counts))).trans
        t35ObservationProbability
  exact ⟨hp,by rw [hp]; norm_num⟩

end
end SAP.P003b.WH.W1
