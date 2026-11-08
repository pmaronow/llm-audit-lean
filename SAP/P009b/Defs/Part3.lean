import Mathlib
import SAP.P009b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b
noncomputable section
attribute [local instance] Classical.propDecidable

def T18CoreStatement : Prop :=
  ∀ {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (i : Fin n)
    (hc : incoming E i ≤ min m (n-m)),
    let r := incoming E i - 1
    (∀ t, t ≤ r → prob E.design (fun z => treatedIncoming E i z = t) =
      hypergeomMass n m r t) ∧
    (∀ t b, t ≤ r → cmean E.design (fun z => z i = b)
      (fun z => if treatedIncoming E i z = t then 1 else 0) =
      hypergeomMass (n-1) (m-(if b then 1 else 0)) r t) ∧
    (r = 0 → ∀ b, cmean E.design (fun z => z i = b)
      (fun z => if treatedIncoming E i z = 0 then 1 else 0) /
        prob E.design (fun z => treatedIncoming E i z = 0) = 1) ∧
    (∀ t b, t ≤ r → 0 < r →
      cmean E.design (fun z => z i = b)
        (fun z => if treatedIncoming E i z = t then 1 else 0) /
        prob E.design (fun z => treatedIncoming E i z = t) - 1 =
          (r:ℝ)/(marginal E i b*((n:ℝ)-r)) *
            (marginal E i b - bit b*(t:ℝ)/r - (1-bit b)*((r:ℝ)-t)/r)) ∧
    (∀ t b, t ≤ r → 0 < r →
      -1 < marginal E i b-bit b*(t:ℝ)/r-(1-bit b)*((r:ℝ)-t)/r ∧
      marginal E i b-bit b*(t:ℝ)/r-(1-bit b)*((r:ℝ)-t)/r < 1 ∧
      |cmean E.design (fun z => z i = b)
        (fun z => if treatedIncoming E i z = t then 1 else 0) /
        prob E.design (fun z => treatedIncoming E i z = t)-1| ≤
          (r:ℝ)/(marginal E i b*((n:ℝ)-r)) ∧
      (r:ℝ)/(marginal E i b*((n:ℝ)-r)) ≤
        (incoming E i:ℝ)/(marginal E i b*((n:ℝ)-incoming E i)) ∧
      (incoming E i:ℝ)/(marginal E i b*((n:ℝ)-incoming E i)) ≤
        (incoming E i:ℝ)/(marginal E i b*(min m (n-m):ℝ))) ∧
    (∀ w b, 0 < prob E.design (fun z => maskedOthers E i z = w) →
      |cmean E.design (fun z => z i = b) (fun z => if maskedOthers E i z = w then 1 else 0) /
        prob E.design (fun z => maskedOthers E i z = w) - 1| ≤
        (incoming E i : ℝ)/(marginal E i b * (min m (n-m):ℝ)))

def T19CoreStatement : Prop :=
    let E := fairExperiment 6 sixOutcome
    d E 0 1 = 0 ∧ e E sixPairing 0 1 = 1 ∧
    (∑ ℓ, (1-d E 0 1)*I E ℓ 0*I E (sixPairing.partner ℓ) 1) = 3 ∧ (1:ℝ) ≠ 3

def T20CoreStatement : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (E : Experiment n) (ρ : Pairing n),
    (∀ i j, e E ρ i j ≤ ∑ ℓ, (1-d E i j)*I E ℓ i*I E (ρ.partner ℓ) j) ∧
    (∀ i j, (∑ ℓ, (1-d E i j)*I E ℓ i*I E (ρ.partner ℓ) j) ≤
      ∑ ℓ, I E ℓ i*I E (ρ.partner ℓ) j) ∧
    eAvg E ρ ≤ C2 E ^ 2

def T21CoreStatement : Prop :=
  ∀ (x ε : Fin 6 → ℝ) (_hSupport : UniformBaselineSupport6 x ε),
    let c := fun i => x i + ε i
    let E := fairExperiment 6 (oneSourceOutcome 4 c)
    Bernoulli E ∧ dAvg E = 3 ∧ msq E = 1 ∧
    B1 E = (1 + 2 * c 0) / 3 ∧ B2 E = 1/3 ∧
    B2 E ≠ (4:ℝ)*3/(6+4*3) ∧
    (6:ℝ)/dAvg E * (mean E.design (vBER E) - var E.design (ht E)) =
      -(1 + 2 * c 0) / 3

def T22FiniteStatement : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (b : ℕ)
    (hb : 1 ≤ b ∧ b ≤ n) (c : Fin n → ℝ),
    let E := fairExperiment n (oneSourceOutcome b c)
    (n:ℝ)*dAvg E = n+(b:ℝ)*((b:ℝ)-1) ∧ msq E = 1 ∧
    B2 E = ((b:ℝ)-1)*((b:ℝ)-2)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) ∧
    B1 E = (2+4*c ⟨0,hn⟩)*((b:ℝ)-1)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) ∧
    (n:ℝ)^2*(mean E.design (vBER E)-var E.design (ht E)) =
      n-2*((b:ℝ)-1)*(1+2*c ⟨0,hn⟩)-((b:ℝ)-1)*((b:ℝ)-2) ∧
    (c ⟨0,hn⟩ = -1/4 →
      msq E/dAvg E-B1 E-B2 E = ((n:ℝ)-((b:ℝ)-1)^2)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) ∧
      (n:ℝ)/dAvg E*(mean E.design (vBER E)-var E.design (ht E)) =
        ((n:ℝ)-((b:ℝ)-1)^2)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1))) ∧
    0 ≤ 2*((b:ℝ)-1)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) ∧
    2*((b:ℝ)-1)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1)) ≤ 1/Real.sqrt n

def T22LimitStatement : Prop :=
  ∀ (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hQ : 4 ≤ q)
    (b : ℕ → ℕ) (hb : ∀ t, 1 ≤ b t ∧ b t ≤ S.N t)
    (c : (t : ℕ) → Fin (S.N t) → ℝ)
    (hSource : ∀ t, c t ⟨0,S.positive t⟩ = -1/4)
    (hLaw : ∀ t, (S.experiment t).design = fairLaw (S.N t))
    (hOutcome : ∀ t, (S.experiment t).outcome = oneSourceOutcome (b t) (c t)),
    InProbability S (fun t z => size S t/dAvg (S.experiment t)*
      (vBER (S.experiment t) z-var (S.experiment t).design (ht (S.experiment t))) -
        (size S t-((b t:ℝ)-1)^2)/(size S t+(b t:ℝ)*((b t:ℝ)-1)))

def T23CoreStatement : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (heven : Even n)
    (P : Law (Assignment n))
    (hCR : Complete (⟨P, fullOutcome (fun _ => 0)⟩ : Experiment n) (n/2))
    (ρ : (Fin n → ℝ) → Pairing n) (hRank : ∀ x, AdjacentRanks x (ρ x))
    (Q : (Fin n → ℝ) → Law (Assignment n))
    (hPair : ∀ x, Paired (⟨Q x, fullOutcome (fun _ => 0)⟩ : Experiment n) (ρ x))
    (_hIntegrable : SimulationIntegrable P Q),
    let cr := fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
      (⟨P, fullOutcome (fun i => b.1 i+b.2 i)⟩ : Experiment n)
    let pair := fun b : (Fin n → ℝ) × (Fin n → ℝ) =>
      (⟨Q b.1, fullOutcome (fun i => b.1 i+b.2 i)⟩ : Experiment n)
    (∫ b, mean (cr b).design (ht (cr b))-eate (cr b) ∂uniformBaselines n) = -1 ∧
    (∫ b, mean (pair b).design (ht (pair b))-eate (pair b) ∂uniformBaselines n) = -1 ∧
    (∫ b, mean (cr b).design (hajek (cr b))-eate (cr b) ∂uniformBaselines n) = -1 ∧
    (∫ b, mean (pair b).design (hajek (pair b))-eate (pair b) ∂uniformBaselines n) = -1 ∧
    (∫ b, var (cr b).design (ht (cr b)) ∂uniformBaselines n) = 58/(3*(n:ℝ)) ∧
    (∫ b, var (pair b).design (ht (pair b)) ∂uniformBaselines n) =
      49/(3*(n:ℝ))+36/((n:ℝ)*((n:ℝ)+1)*((n:ℝ)+2)) ∧
    (∫ b, var (cr b).design (hajek (cr b)) ∂uniformBaselines n) = 58/(3*(n:ℝ)) ∧
    (∫ b, var (pair b).design (hajek (pair b)) ∂uniformBaselines n) =
      49/(3*(n:ℝ))+36/((n:ℝ)*((n:ℝ)+1)*((n:ℝ)+2)) ∧
    (∫ b, mean (cr b).design (fun z => (ht (cr b) z-eate (cr b))^2)
      ∂uniformBaselines n) = 58/(3*(n:ℝ))+1 ∧
    (∫ b, mean (pair b).design (fun z => (ht (pair b) z-eate (pair b))^2)
      ∂uniformBaselines n) = 49/(3*(n:ℝ))+36/((n:ℝ)*((n:ℝ)+1)*((n:ℝ)+2))+1 ∧
    (∫ b, mean (cr b).design (fun z => (hajek (cr b) z-eate (cr b))^2)
      ∂uniformBaselines n) = 58/(3*(n:ℝ))+1 ∧
    (∫ b, mean (pair b).design (fun z => (hajek (pair b) z-eate (pair b))^2)
      ∂uniformBaselines n) = 49/(3*(n:ℝ))+36/((n:ℝ)*((n:ℝ)+1)*((n:ℝ)+2))+1 ∧
    1/(58/(3*(n:ℝ))) = 3*(n:ℝ)/58

def T24CoreStatement : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (heven : Even n)
    (E : Experiment n) (b : Fin n → ℝ) (hy : E.outcome = fullOutcome b)
    (hDesign : Complete E (n/2) ∨ ∃ ρ : Pairing n, Paired E ρ),
    eate E = 1 ∧
    (∀ z, 0 < E.design.mass z →
      (∀ i, E.outcome i z = b i ∧ effect E i z = 2*(1-bit (z i))) ∧
      ateAt E z = 1 ∧ ht E z = hajek E z ∧
      ht E z = 2/(n:ℝ)*(∑ i, (2*bit (z i)-1)*b i)) ∧
    mean E.design (ht E) = 0 ∧ mean E.design (hajek E) = 0 ∧
    mean E.design (ht E)-eate E = -1 ∧ mean E.design (hajek E)-eate E = -1 ∧
    mean E.design (fun z => (ht E z-eate E)^2) = var E.design (ht E)+1 ∧
    mean E.design (fun z => (hajek E z-eate E)^2) = var E.design (hajek E)+1

def T25CaptionStatement : Prop :=
  ∀ (R : ℕ) (hR : 0 < R) (estimates : Fin R → ℝ),
    0 ≤ reportedBias R estimates ∧ reportedBias R estimates = |empiricalBias R estimates| ∧
    |(-1:ℝ)| = 1 ∧ (-1:ℝ) ≠ 1

def T25PopulationStatement : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (heven : Even n)
    (E : Experiment n) (b : Fin n → ℝ) (hy : E.outcome = fullOutcome b)
    (hDesign : Complete E (n/2) ∨ ∃ ρ : Pairing n, Paired E ρ),
    mean E.design (ht E)-eate E = -1 ∧ mean E.design (hajek E)-eate E = -1 ∧
    |mean E.design (ht E)-eate E| = 1 ∧ |mean E.design (hajek E)-eate E| = 1

def T26CoreStatement : Prop :=
  ∀ (S : Study) (p : ℝ) (hp : 0 < p ∧ p < 1)
    (hNo : ∀ t, NoInterference (S.experiment t))
    (hCommon : ∀ t z, (S.experiment t).design.mass z =
      if z = (fun _ => true) then p else if z = (fun _ => false) then 1-p else 0),
    (∀ t,
      (∀ i j, i ≠ j → alpha (S.experiment t).design
        (masked (S.experiment t) i) (masked (S.experiment t) j) = p*(1-p)) ∧
      (∀ θ : ℝ, alphaExt (S.experiment t) θ =
        (size S t-1)*Real.rpow (p*(1-p)) θ) ∧
      alphaExt (S.experiment t) 1 = (size S t-1)*p*(1-p)) ∧
    Tendsto (fun t => alphaExt (S.experiment t) 1/size S t)
      atTop (nhds (p*(1-p))) ∧
    ¬ LittleO (fun t => alphaExt (S.experiment t) 1) (size S)

def T27AtomsStatement : Prop :=
  ∀ {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) (hBER : Bernoulli E) (G : Finset (Fin n))
    (a : Assignment n),
    k⁻¹ ^ G.card ≤ prob E.design (fun z => ∀ i ∈ G, z i = a i) ∧
    prob E.design (fun z => ∀ i ∈ G, z i = a i) ≤ (1-k⁻¹)^G.card

def T27ApproximationStatement : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (δ α : ℝ) (hδ : ∀ ω, P.mass ω ≤ δ) (hα : 0 < α ∧ α < 1),
    ∃ f : Ω → ℝ, (∀ ω, f ω = -1 ∨ f ω = 0 ∨ f ω = 1) ∧
      |prob P (fun ω => f ω = 1)-α/2| ≤ δ ∧
      |prob P (fun ω => f ω = -1)-α/2| ≤ δ

def T27MinimizerStatement : Prop :=
  ∀ (S : Study) (k q s α : ℝ)
    (hReg : RegularSequence S k q s) (hBER : ∀ t, Bernoulli (S.experiment t))
    (hα : 0 < α ∧ α < 1) (b : ℕ → ℕ) (hb : ∀ t, b t ≤ S.N t)
    (hbInfinity : Tendsto b atTop atTop)
    (f : (t : ℕ) → Assignment (b t) → ℝ)
    (hf : ∀ t z, f t z = -1 ∨ f t z = 0 ∨ f t z = 1)
    (hmin : ∀ t (g : Assignment (b t) → ℝ),
      (∀ z, g z = -1 ∨ g z = 0 ∨ g z = 1) →
      approximationError (S.experiment t).design α
        (fun z => f t (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb t)⟩)) ≤
      approximationError (S.experiment t).design α
        (fun z => g (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb t)⟩))),
    (∀ t, approximationError (S.experiment t).design α
      (fun z => f t (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb t)⟩)) ≤
        2*(1-k⁻¹)^b t) ∧
    (∀ a : Bool, Tendsto (fun t => prob (S.experiment t).design (fun z =>
      f t (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (hb t)⟩) = if a then 1 else -1))
      atTop (nhds (α/2)))

def T28FiniteStatement : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] (P : Law Ω) (F : Ω → ℝ)
    (hF : ∀ ω, F ω = -1 ∨ F ω = 0 ∨ F ω = 1)
    (x : ℝ) (hx : x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1)
    (hshift : |mean P F| < threePointDistance x),
    prob P (fun ω => F ω-mean P F ≤ x) = prob P (fun ω => F ω ≤ x)

def T28EventualStatement : Prop :=
  ∀ (μ : ℕ → ℝ) (hμ : Tendsto μ atTop (nhds 0))
    (x : ℝ) (hx : x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1),
    ∀ᶠ t in atTop, |μ t| < threePointDistance x

def T29CoreStatement : Prop :=
  ∀ {n : ℕ} (E : Experiment n) (k q : ℝ)
    (hk : 0 < k) (hq : 2 ≤ q)
    (hMoment : ∀ ℓ, mean E.design (fun z => Real.rpow |E.outcome ℓ z| q) ≤ Real.rpow k q)
    (a : ℕ) (hqa : 2*a ≤ q)
    (i j : Fin n) (b : Bool),
    |cov E.design (armVariable E b a i) (armVariable E b a j)| ≤
      Real.sqrt (var E.design (armVariable E b a i)*var E.design (armVariable E b a j)) ∧
    Real.sqrt (var E.design (armVariable E b a i)*var E.design (armVariable E b a j)) ≤
      Real.sqrt (mean E.design (fun z => |E.outcome i z|^(2*a)) *
        mean E.design (fun z => |E.outcome j z|^(2*a))) ∧
    Real.sqrt (mean E.design (fun z => |E.outcome i z|^(2*a)) *
        mean E.design (fun z => |E.outcome j z|^(2*a))) ≤
      Real.sqrt (Real.rpow (mean E.design (fun z => Real.rpow |E.outcome i z| q))
        (2*(a:ℝ)/q) * Real.rpow
        (mean E.design (fun z => Real.rpow |E.outcome j z| q)) (2*(a:ℝ)/q)) ∧
    Real.sqrt (Real.rpow (mean E.design (fun z => Real.rpow |E.outcome i z| q))
        (2*(a:ℝ)/q) * Real.rpow
        (mean E.design (fun z => Real.rpow |E.outcome j z| q)) (2*(a:ℝ)/q)) ≤
      Real.sqrt (Real.rpow (Real.rpow k q) (2*(a:ℝ)/q) *
        Real.rpow (Real.rpow k q) (2*(a:ℝ)/q)) ∧
    Real.sqrt (Real.rpow (Real.rpow k q) (2*(a:ℝ)/q) *
        Real.rpow (Real.rpow k q) (2*(a:ℝ)/q)) = Real.sqrt (k^(4*a)) ∧
    Real.sqrt (k^(4*a)) = k^(2*a) ∧
    |cov E.design (armVariable E b a i) (armVariable E b a j)| ≤ k^(2*a)

end
end SAP.P009b
