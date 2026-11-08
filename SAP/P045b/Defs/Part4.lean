import SAP.P045b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P045b
open Finset
open scoped BigOperators
noncomputable section

/-- Empty cells are retained in HT estimation; the ratio estimator has an explicit domain. -/
def T17Statement : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ {Δ : Type*} [Fintype Δ] [DecidableEq Δ],
  ∀ (p : Design (Assignment n)) (D : Assignment n → Fin n → Δ)
    (y : Fin n → Δ → ℝ) (k l : Δ), k ≠ l →
    (∀ i, 0 < exposureProb p.mass D i k) →
    (∀ i, 0 < exposureProb p.mass D i l) →
    (∀ z, (∀ i, D z i ≠ k) →
      htTotal p.mass D y k z = 0 ∧
      htContrast p.mass D y k l z = -htTotal p.mass D y l z / n ∧
      (∑ i, if D z i = k then (1 : ℝ) / exposureProb p.mass D i k else 0) = 0 ∧
      hajek p.mass D y k z = none ∧
      exposureSampleMean D y k z = none) ∧
    expect p.mass (htTotal p.mass D y k) = ∑ i, y i k ∧
    expect p.mass (htContrast p.mass D y k l) = effect y k l ∧
    (0 < prob p.mass (fun z => ∃ i, D z i = k) →
      condMean p.mass (fun z => ∃ i, D z i = k) (htTotal p.mass D y k) =
        (∑ i, y i k) / prob p.mass (fun z => ∃ i, D z i = k)) ∧
    (0 < prob p.mass (fun z => ∃ i, D z i = k) →
      0 < prob p.mass (fun z => ∀ i, D z i ≠ k) → (∑ i, y i k) ≠ 0 →
      condMean p.mass (fun z => ∃ i, D z i = k) (htTotal p.mass D y k) ≠ ∑ i, y i k) ∧
    (20 / (20/45) : ℝ) = 45

def T18Statement : Prop :=
  (∀ {n : ℕ} (i : Fin (n+1)),
    (∀ z : Assignment (n+1), ∀ j : Fin n,
      withoutCoordinate i z j = if j.val < i.val then z j.castSucc else z j.succ) ∧
    (∀ z z' : Assignment (n+1), (∀ j, j ≠ i → z j=z' j) →
      withoutCoordinate i z=withoutCoordinate i z') ∧
    Function.Bijective (fun z : Assignment (n+1) => (z i, withoutCoordinate i z)) ∧
    (∀ y : Assignment (n+1) → ℝ,
      ∃! f : Bool × Assignment n → ℝ, ∀ z, f (z i, withoutCoordinate i z)=y z)) ∧
  (∀ z : Assignment 4, withoutCoordinate 2 z = ![z 0,z 1,z 3])

def T19General : Prop :=
  ∀ {n K : ℕ} (hn : 2 ≤ n) (ψ : ℝ)
    (hψ : 0 < ψ) (hψ1 : ψ < 1) (hK : (K : ℝ)=ψ*n)
    (z : Assignment n) (hz : treatedCount z=K) (i : Fin n),
    coMembers i z = (K : ℝ)-bit (z i) ∧
    (z i=true → coMembers i z=ψ*n-1 ∧ ψ*(n-1)-coMembers i z=1-ψ ∧
      coMembers i z < ψ*(n-1)) ∧
    (z i=false → coMembers i z=ψ*n)

def T19Statement : Prop :=
  T19General ∧
  (∀ (z : Assignment 3), treatedCount z = 2 → ∀ i,
    (z i = true → coMembers i z = 1) ∧
    (z i = false → coMembers i z = 2)) ∧
  ((2/3 : ℝ)*(3-1) = 4/3)

def T20Statement : Prop :=
  (∀ S : Finset (Fin 9), ¬(withinThree S ∧ covers pathDistance 3 S)) ∧
    (univ.filter (fun S : Finset (Fin 9) => epsilonNet pathDistance 3 S)).card = 13 ∧
    (∀ S : Finset (Fin 9), epsilonNet pathDistance 3 S ↔
      S ∈ ({ {1,6}, {2,6}, {2,7}, {0,3,6}, {0,3,7}, {0,3,8},
        {0,4,7}, {0,4,8}, {0,5,8}, {1,4,7}, {1,4,8}, {1,5,8}, {2,5,8} } : Finset (Finset (Fin 9))))

def T21Statement : Prop :=
  (∀ {n ε : ℕ} (hε : 1 ≤ ε) (G : SimpleGraph (Fin n)),
    (∀ S : Finset (Fin n), separated G.edist ε S →
      (covers G.edist ε S ↔ ∀ v ∉ S, ¬separated G.edist ε (insert v S))) ∧
    (∀ cs : List (Fin n), greedyRun G.edist ε cs →
      cs.Nodup ∧ cs.length ≤ n ∧ separated G.edist ε cs.toFinset ∧
      (marked G.edist ε cs.toFinset = univ → epsilonNet G.edist ε cs.toFinset)) ∧
    (∃ cs : List (Fin n), greedyRun G.edist ε cs ∧ marked G.edist ε cs.toFinset = univ) ∧
    (∃ S : Finset (Fin n), epsilonNet G.edist ε S)) ∧
  (univ.filter (fun S : Finset (Fin 9) => epsilonNet pathDistance 3 S)).card = 13 ∧
  (∀ S : Finset (Fin 9), epsilonNet pathDistance 3 S ↔
    S ∈ ({ {1,6}, {2,6}, {2,7}, {0,3,6}, {0,3,7}, {0,3,8},
      {0,4,7}, {0,4,8}, {0,5,8}, {1,4,7}, {1,4,8}, {1,5,8}, {2,5,8} } :
      Finset (Finset (Fin 9))))

def T22Core : Prop :=
  (∀ n : ℕ,
      expect (bernoulli (1/2)) (signMean (n := n+1)) = 0 ∧
      variance (bernoulli (1/2)) (signMean (n := n+1)) = 1/(n+1 : ℕ) ∧
      (∀ ε : ℝ, 0 < ε → prob (bernoulli (1/2))
        (fun z : Assignment (n+1) => ε < |signMean z|) ≤ 1/((n+1 : ℕ)*ε^2)) ∧
      expect (bernoulli (1/2)) (varianceFactor (n := n)) = 1 ∧
      expect (bernoulli (1/2)) (fun z : Assignment (n+1) => (varianceFactor z)^2) = 5/4 ∧
      (∀ z : Assignment (n+1), seWitness n z=varianceFactor z/Real.sqrt (n+1 : ℕ)) ∧
      expect (bernoulli (1/2)) (seWitness n) = 1/Real.sqrt (n+1 : ℕ) ∧
      expect (bernoulli (1/2)) (varianceWitness n)-1/(n+1 : ℕ) = 1/(4*(n+1 : ℕ)) ∧
      prob (bernoulli (1/2)) (fun z : Assignment (n+1) =>
        1/2 < |varianceWitness n z/(1/(n+1 : ℕ))-1|) = 1 ∧
      (∀ z : Assignment (n+1), |varianceWitness n z-1/(n+1 : ℕ)| ≤ 5/(4*(n+1 : ℕ)))) ∧
    InProbability (fun n => bernoulli (n := n+1) (1/2)) (fun _ z => signMean z) (fun _ => 0) ∧
    ¬InProbability (fun n => bernoulli (n := n+1) (1/2))
      (fun n z => varianceWitness n z/(1/(n+1 : ℕ))) (fun _ => 1) ∧
    InProbability (fun n => bernoulli (n := n+1) (1/2)) varianceWitness (fun n => 1/(n+1 : ℕ))

def T22Statement : Prop :=
  T22Core ∧
  (∀ n : ℕ,
    prob (bernoulli (1/2)) (fun z : Assignment (n+1) =>
      varianceWitness n z / (1/(n+1 : ℕ)) = 1/4) = 1/2 ∧
    prob (bernoulli (1/2)) (fun z : Assignment (n+1) =>
      varianceWitness n z / (1/(n+1 : ℕ)) = 9/4) = 1/2 ∧
    (∀ z : Assignment (n+1),
      varianceWitness n z / (1/(n+1 : ℕ)) = (varianceFactor z)^2 ∧
      |varianceWitness n z - 1/(n+1 : ℕ)| =
        |(varianceFactor z)^2-1|/(n+1 : ℕ)) ∧
    (0 : ℝ) < 1/(4*(n+1 : ℕ))) ∧
  Filter.Tendsto (fun n : ℕ => (5 : ℝ)/(4*(n+1 : ℕ))) Filter.atTop (nhds 0) ∧
  (∀ n : ℕ,
    expect (bernoulli (1/2)) (seWitness n) =
      Real.sqrt (variance (bernoulli (1/2)) (signMean (n := n+1))) ∧
    (∀ z : Assignment (n+1),
      varianceWitness n z / (1/(n+1 : ℕ)) ∈ ({1/4, 9/4} : Finset ℝ)))

def T23Statement : Prop :=
  ((3311/2660 : ℝ)=473/380 ∧
    (∀ r ∈ ({4594/4532,1033/1045,3407/3666,841/838} : Finset ℝ),
      1-71/1000 ≤ r ∧ r ≤ 1+71/1000) ∧
    (244/1000 : ℝ) < 473/380-1 ∧ (473/380 : ℝ)-1 < 245/1000 ∧
    (164/1000 : ℝ) < 2509/2155-1 ∧ (2509/2155 : ℝ)-1 < 165/1000) ∧
  T22Statement ∧
  (∀ {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (p : (n : ℕ) → Design (Ω n)) (T Vhat : (n : ℕ) → Ω n → ℝ)
    (hV : ∀ n, 0 < variance (p n).mass (T n)) (hhat : ∀ n w, 0 ≤ Vhat n w)
    (hvanish : Filter.Tendsto (fun n => variance (p n).mass (T n)) Filter.atTop (nhds 0))
    (hse : Filter.Tendsto (fun n => expect (p n).mass (fun w => Real.sqrt (Vhat n w)) -
      Real.sqrt (variance (p n).mass (T n))) Filter.atTop (nhds 0)),
    InProbability (fun n => (p n).mass) Vhat (fun n => variance (p n).mass (T n))) ∧
  (variance (fun _ : Bool => (1/2 : ℝ)) sign=1 ∧
    expect (fun _ : Bool => (1/2 : ℝ)) (fun b => Real.sqrt ((if b then (3/2 : ℝ) else 1/2)^2))=1 ∧
    prob (fun _ : Bool => (1/2 : ℝ)) (fun b => 1/2 < |(if b then (3/2 : ℝ) else 1/2)^2-1|)=1 ∧
    ¬InProbability (fun (_n : ℕ) (_b : Bool) => (1/2 : ℝ))
      (fun _ b => (if b then (3/2 : ℝ) else 1/2)^2) (fun _ => 1)) ∧
  (∀ {M : ℕ} (hM : 0 < M) (s : Fin M → ℝ) (hs : ∀ i, 0 ≤ s i),
    (mean s)^2 ≤ mean (fun i => (s i)^2)) ∧
  (∀ {M : ℕ}, 0 < M → ∀ s : Fin M → ℝ, (∀ i, 0 ≤ s i) →
    ∀ sd : ℝ, 0 < sd → (mean s / sd)^2 ≤ mean (fun i => (s i)^2) / sd^2)

def T24Statement : Prop :=
  (∀ {G : ℕ} (hG : 0 < G) (n : Fin G → ℕ)
    (hn : ∀ g, 0 < n g) (b : (g : Fin G) → Fin (n g) → ℝ),
    let μ := regimeMean (dilatedMarginal b)
    let B := baselineMean b
    let Dψ := μ true true-μ false true
    let Dφ := μ true false-μ false false
    let I := μ false true-μ false false
    let To := μ true true-μ false false
    let O := (2/3)*μ true true+(1/3)*μ false true - ((1/3)*μ true false+(2/3)*μ false false)
    Dψ=(3/4)*B ∧ Dφ=(1/2)*B ∧ I=(1/4)*B ∧ To=B ∧ O=(7/12)*B ∧
    (0 < B → Dφ/Dψ=2/3 ∧ Dφ < Dψ) ∧ To=Dψ+I ∧
    (B ≠ 0 → To-I ≠ Dφ)) ∧
  (∀ {G : ℕ} (hG : 0 < G) (n : Fin G → ℕ)
    (hn : ∀ g, 0 < n g) (y : (g : Fin G) → Fin (n g) → Bool → Bool → ℝ),
    regimeMean y true true-regimeMean y false false =
      (regimeMean y true true-regimeMean y false true) +
      (regimeMean y false true-regimeMean y false false)) ∧
  (∀ {G : ℕ}, 0 < G → ∀ n : Fin G → ℕ, (∀ g, 0 < n g) →
    ∀ b : (g : Fin G) → Fin (n g) → ℝ,
    let μ := regimeMean (dilatedMarginal b)
    let B := baselineMean b
    (2/3)*μ true true + (1/3)*μ false true = (7/4)*B ∧
    (1/3)*μ true false + (2/3)*μ false false = (7/6)*B ∧
    (μ true true - μ false false) - (μ false true - μ false false) = (3/4)*B)

end
end SAP.P045b
