import Mathlib
import SAP.P045a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a
noncomputable section

/-- The five possible coded terminal centre sets, using vertex labels 0 through 3. -/
def fourPathCodedCentreSets : Finset (Finset (Fin 4)) :=
  {{0, 1}, {0, 2}, {0, 3}, {1}, {2}}

/-- The three possible repaired terminal centre sets. -/
def fourPathRepairedCentreSets : Finset (Finset (Fin 4)) :=
  {{0, 3}, {1}, {2}}

/-- The length component of the terminal-centre series, including every retry trace. -/
def fourPathLengthMass (coded : Bool) (S : Finset (Fin 4)) (t : ℕ) : ℝ :=
  ∑ z : Fin t → Fin 4,
    if (List.ofFn z).toFinset = S then traceMass pathDistance 3 coded (List.ofFn z) else 0

/-- The actual nearest-centre partition, as an unordered collection of vertex sets. -/
def nearestPartition {n : ℕ} (d : Fin n → Fin n → ℕ∞)
    (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  S.image (fun s => univ.filter (fun v => nearestCentre d S v = some s))

/-- The four treatment vectors supported by repaired four-path clustering. -/
def fourPathRepairedVectors : Finset (Assignment 4) :=
  {![false, false, false, false], ![true, true, true, true],
    ![true, true, false, false], ![false, false, true, true]}

/-- P045-T10; p. 305 (PDF p. 17); staged package R/make_tr_vec_bernoulli.R,
lines 76–82 and 122–128.
On the four-path, use labels 0 through 3, nearest-centre clusters with ties to the smallest
label, and independent fair cluster treatment. The radius-two balls are {0,1,2}, all vertices,
all vertices, and {1,2,3}. Each initial centre has probability 1/4. After initial centre 0,
each retry draw is uniform on all four vertices and each eventual second distinct centre
has conditional probability 1/3; initial centre 3 forces 0, and centres 1 or 2 finish at once.
The coded terminal law is {0,1}:1/12, {0,2}:1/12, {0,3}:1/3, {1}:1/4, {2}:1/4, zero
elsewhere, and normalized; separation fails with probability 1/6. The cluster partitions
{0}|{1,2,3}, {0,1}|{2,3}, and {0,1,2,3} have masses 1/12, 5/12, 1/2 and exhaust the law.
The coded treatment law is 0000:3/8, 1111:3/8, 1100:5/48, 0011:5/48, 1000:1/48,
0111:1/48, zero elsewhere. The repaired terminal law is {0,3}:1/2, {1}:1/4, {2}:1/4,
zero elsewhere; these are exactly the separated covering three-nets. Its treatment law is
0000:3/8, 1111:3/8, 1100:1/8, 0011:1/8, zero elsewhere. All terminal series converge,
and the treatment distributions differ. The usual measure-theoretic conditions are assumed. -/
def T10WholeStatement : Prop :=
  T10Statement ∧
  (marked (pathDistance (n := 4)) 3 ∅ = ∅ ∧
    marked (pathDistance (n := 4)) 3 {0} = {0, 1, 2} ∧
    marked (pathDistance (n := 4)) 3 {1} = univ ∧
    marked (pathDistance (n := 4)) 3 {2} = univ ∧
    marked (pathDistance (n := 4)) 3 {3} = {1, 2, 3}) ∧
  ((∀ v : Fin 4, centreDraw pathDistance 3 true ∅ v = 1/4 ∧
      centreDraw pathDistance 3 true {0} v = 1/4) ∧
    (∀ v : Fin 4, centreDraw pathDistance 3 true {3} v = if v = 0 then 1 else 0) ∧
    (∀ j : Fin 4, j ≠ 0 →
      (∀ r : ℕ, traceMass pathDistance 3 true
        (List.replicate (r+1) (0 : Fin 4) ++ [j]) = (1/4 : ℝ)^(r+2)) ∧
      Summable (fun r : ℕ => traceMass pathDistance 3 true
        (List.replicate (r+1) (0 : Fin 4) ++ [j])) ∧
      (∑' r : ℕ, traceMass pathDistance 3 true
        (List.replicate (r+1) (0 : Fin 4) ++ [j])) /
          centreDraw pathDistance 3 true ∅ (0 : Fin 4) = 1/3)) ∧
  (∀ coded : Bool, ∀ S : Finset (Fin 4), Summable (fourPathLengthMass coded S)) ∧
  (∀ S : Finset (Fin 4), S ∉ fourPathCodedCentreSets →
    terminalCentres pathDistance 3 true S = 0) ∧
  (∀ S : Finset (Fin 4), S ∉ fourPathRepairedCentreSets →
    terminalCentres pathDistance 3 false S = 0) ∧
  (prob (terminalCentres (pathDistance (n := 4)) 3 true)
      (fun S => nearestPartition pathDistance S = {{0}, {1, 2, 3}}) = 1/12 ∧
    prob (terminalCentres (pathDistance (n := 4)) 3 true)
      (fun S => nearestPartition pathDistance S = {{0, 1}, {2, 3}}) = 5/12 ∧
    prob (terminalCentres (pathDistance (n := 4)) 3 true)
      (fun S => nearestPartition pathDistance S = {{0, 1, 2, 3}}) = 1/2 ∧
    prob (terminalCentres (pathDistance (n := 4)) 3 true)
      (fun S => nearestPartition pathDistance S ∉
        ({{{0}, {1, 2, 3}}, {{0, 1}, {2, 3}}, {{0, 1, 2, 3}}} :
          Finset (Finset (Finset (Fin 4))))) = 0) ∧
  (∀ S : Finset (Fin 4), epsilonNet pathDistance 3 S ↔ S ∈ fourPathRepairedCentreSets) ∧
  ((∑ S : Finset (Fin 4), terminalCentres pathDistance 3 false S) = 1 ∧
    (∀ z : Assignment 4, z ∉ fourPathRepairedVectors →
      clusteredTreatment pathDistance false (1/2) z = 0) ∧
    clusteredTreatment (pathDistance (n := 4)) true (1/2) ≠
      clusteredTreatment pathDistance false (1/2))

/-- Own-treatment marginal under the uniform law on the 45 sorted treatment pairs. -/
def cycleOwnProb (i : Fin 10) : ℝ :=
  average treatmentPairs (fun e => if pairAssignment e i = true then 1 else 0)

/-- Correct exposure-specific HT mean for d11 in the ten-cycle witness. -/
def cycleHTMean (e : Fin 10 × Fin 10) : ℝ :=
  mean (fun i => if exposure cycle10 (pairAssignment e) i = .d11 then
    2 / pairExposureProb cycle10 i .d11 else 0)

/-- Mean under the all-treated assignment in the correctly specified ten-cycle witness. -/
def cycleAllTreatedMean : ℝ :=
  mean (fun i : Fin 10 => cycleOut i (exposure cycle10 (fun _ => true) i))

/-- P045-T12; p. 301 (PDF p. 13).
The ten-cycle with exactly two uniformly chosen treated units and exposure outcomes (2,1,1,0)
is the exact counterexample to the printed second equality. Each own-treatment probability
is 1/5; the d11, d10, d01, d00 probabilities are 2/45, 7/45, 1/3, 7/15. All five are
positive and the two treated-exposure probabilities sum to 1/5. Of the 45 assignments,
ten treat adjacent units and give (L,R,H)=(2,9,9); the other 35 give (1,9/7,0), where
L and R are the two printed sides and H is the correct d11 HT mean. Thus L differs from
R on every assignment. The all-treated mean and mu(d11) are 2, and mu(d10)=1.
E[L]=11/9, E[R]=3=mu(d11)+mu(d10), and E[H]=2. The bias of L is 11/9-2=-7/9,
also exactly the negative mean of (pi(d10)/pi)(y(d11)-y(d10)). The usual measure-theoretic
conditions are assumed. -/
def T12WholeStatement : Prop :=
  T12Statement ∧
  ((∀ i j : Fin 10, cycle10 i j = cycle10 j i) ∧
    (∀ i : Fin 10, cycle10 i i = false ∧
      (univ.filter (fun j => cycle10 i j = true)).card = 2)) ∧
  (∀ i : Fin 10,
    cycleOwnProb i = 1/5 ∧ 0 < cycleOwnProb i ∧
    (∀ d : Exposure, 0 < pairExposureProb cycle10 i d) ∧
    cycleOwnProb i = pairExposureProb cycle10 i .d11 + pairExposureProb cycle10 i .d10) ∧
  (∀ e : Fin 10 × Fin 10, cycleL e =
    mean (fun i => if pairAssignment e i then
      cycleOut i (exposure cycle10 (pairAssignment e) i) / cycleOwnProb i else 0)) ∧
  (treatmentPairs.filter (fun e => cycle10 e.1 e.2 = false)).card = 35 ∧
  (∀ e ∈ treatmentPairs, cycleHTMean e = if cycle10 e.1 e.2 then 9 else 0) ∧
  (cycleAllTreatedMean = 2 ∧ mean (fun i : Fin 10 => cycleOut i .d11) = 2 ∧
    mean (fun i : Fin 10 => cycleOut i .d10) = 1 ∧
    average treatmentPairs cycleR =
      mean (fun i : Fin 10 => cycleOut i .d11) + mean (fun i : Fin 10 => cycleOut i .d10) ∧
    average treatmentPairs cycleHTMean = cycleAllTreatedMean) ∧
  (average treatmentPairs cycleL - cycleAllTreatedMean = (11/9 : ℝ) - 2 ∧
    (11/9 : ℝ) - 2 = -7/9 ∧
    average treatmentPairs cycleL - cycleAllTreatedMean =
      -mean (fun i : Fin 10 => (pairExposureProb cycle10 i .d10 / cycleOwnProb i) *
        (cycleOut i .d11 - cycleOut i .d10)))

/-- P045-T13; p. 301 (PDF p. 13); lead-in on p. 300 (PDF p. 12).
For any positive finite population, fixed undirected loopless network, correctly specified
first-degree outcomes and design with positive own-treatment probabilities, the two
treated-exposure indicators partition own treatment. The corrected pointwise expansion
uses the common own-treatment denominator. Its expectation is the unitwise mixture of
y(d11) and y(d10), with nonnegative weights pi(d11)/pi and pi(d10)/pi summing to one.
Its bias for mu(d11) is the negative mean of (pi(d10)/pi)(y(d11)-y(d10)). Nonnegative
spillovers give nonpositive bias, strictly negative exactly when some unit has both
pi(d10)>0 and strictly positive spillover; nonpositive spillovers give nonnegative bias.
When both treated-exposure probabilities are positive, the individual d11 HT mean has
expectation mu(d11), and the sum of the d11 and d10 means has expectation mu(d11)+mu(d10).
With no isolated units, the all-treated mean equals mu(d11). Two adjacent independently
fair-treated units with y(d11)=(2,1), y(d10)=(1,2), and untreated outcomes zero give
naive estimates 0,2,1,3 and mean 3/2=mu(d11), despite unequal treated-exposure outcomes
at both units. The usual measure-theoretic conditions are assumed. -/
def T13WholeStatement : Prop :=
  T13Statement ∧
  (∀ {n : ℕ} (_hn : 0 < n) (p : Design (Assignment n))
    (A : Network n) (y : Fin n → Exposure → ℝ) (_hp : ∀ i, 0 < ownProb p.mass i),
    (∀ (z : Assignment n) (i : Fin n),
      (if z i then (1 : ℝ) else 0) =
        (if exposure A.adj z i = .d11 then 1 else 0) +
        (if exposure A.adj z i = .d10 then 1 else 0)) ∧
    (∀ i : Fin n,
      0 ≤ exposureProb p.mass (exposure A.adj) i .d11 / ownProb p.mass i ∧
      0 ≤ exposureProb p.mass (exposure A.adj) i .d10 / ownProb p.mass i ∧
      exposureProb p.mass (exposure A.adj) i .d11 / ownProb p.mass i +
        exposureProb p.mass (exposure A.adj) i .d10 / ownProb p.mass i = 1) ∧
    ((∀ i : Fin n, 0 < exposureProb p.mass (exposure A.adj) i .d11 ∧
        0 < exposureProb p.mass (exposure A.adj) i .d10) →
      expect p.mass (fun z => htTotal p.mass (exposure A.adj) y .d11 z / n) =
        mean (fun i => y i .d11)) ∧
    ((∀ i : Fin n, ∃ j : Fin n, A.adj i j = true) →
      mean (fun i => y i (exposure A.adj (fun _ => true) i)) = mean (fun i => y i .d11)))

/-- P045-T15; p. 312 (PDF p. 24); setting on p. 311 (PDF p. 23).
The own-psi groups are the disjoint union of those with psi partners and those with phi
partners, for any finite group population and tract pairing. Counts and sums partition
accordingly. With positive total count, the selected-group mean is the pooled ratio;
with both subclass counts positive, its positive group shares sum to one and give the
weighted mixture of subclass means. An empty first subclass has zero numerator and leaves
the other mean. The scalar pooling identities and the complete normalized 450-unit
two-stage witness are included: the two group direct effects are 7/8 and 3/4, the psi-psi target
is 7/8, expected shares are 2/5 and 3/5, and the mean estimator is 4/5 with bias -3/40.
The usual measure-theoretic conditions are assumed. -/
def T15WholeStatement : Prop :=
  T15Statement ∧
  (∀ (G : Type) [DecidableEq G] (H : Finset G) (partner : G → G) (m : G → ℝ),
    let P := H.filter (fun g => partner g ∈ H)
    let Q := H.filter (fun g => partner g ∉ H)
    let a := P.card
    let b := Q.card
    let A := ∑ g ∈ P, m g
    let B := ∑ g ∈ Q, m g
    Disjoint P Q ∧ P ∪ Q = H ∧ H.card = a+b ∧ (∑ g ∈ H, m g) = A+B ∧
    (0 < a+b → average H m = (A+B)/(a+b : ℕ) ∧
      pooledMean a b A B = some (average H m)) ∧
    (0 < a → 0 < b →
      0 < (a : ℝ)/(a+b : ℕ) ∧ 0 < (b : ℝ)/(a+b : ℕ) ∧
      (a : ℝ)/(a+b : ℕ) + (b : ℝ)/(a+b : ℕ) = 1 ∧
      average H m = (a : ℝ)/(a+b : ℕ)*(A/a) + (b : ℝ)/(a+b : ℕ)*(B/b)) ∧
    (a = 0 → 0 < b → A = 0 ∧ average H m = B/b)) ∧
  ((9/4 : ℝ) - 11/8 = 7/8 ∧ (2 : ℝ) - 5/4 = 3/4 ∧
    expect tractTwoStageMass (fun ω => tractDirectEstimator ω.1 ω.2) =
      (2/5 : ℝ)*(7/8) + (3/5 : ℝ)*(3/4))

end
end SAP.P045a
