import Mathlib
import SAP.P009b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b
noncomputable section
attribute [local instance] Classical.propDecidable

def T30CoreStatement : Prop :=
  ∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n)
    (_hOverlap : ∀ i, 0 < marginal E i true ∧ 0 < marginal E i false) (z : Assignment n),
    vMAX E z = dMax E*vBER E z ∧ vSR E z = lambdaMax E*vBER E z ∧
    (vAVG E z = dMax E*vBER E z ↔ dAvg E = dMax E ∨ vBER E z = 0) ∧
    (vAVG E z = lambdaMax E*vBER E z ↔ dAvg E = lambdaMax E ∨ vBER E z = 0)

def T31FiniteStatement : Prop :=
  ∀ (α : ℝ) (hα : 0 < α ∧ α < 1) (x : ℝ),
    prob (sharpLaw α hα) (fun i => sharpValue i ≤ x) = sharpCDF α x

def T31LimitStatement : Prop :=
  ∀ (Ω : ℕ → Type*) [∀ t, Fintype (Ω t)]
    (P : (t : ℕ) → Law (Ω t)) (F : (t : ℕ) → Ω t → ℝ)
    (hF : ∀ t ω, F t ω = -1 ∨ F t ω = 0 ∨ F t ω = 1) (α : ℝ)
    (hα : 0 < α ∧ α < 1)
    (hminus : Tendsto (fun t => prob (P t) (fun ω => F t ω = -1))
      atTop (nhds (α/2)))
    (hplus : Tendsto (fun t => prob (P t) (fun ω => F t ω = 1))
      atTop (nhds (α/2))),
    ∀ x, Tendsto (fun t => prob (P t) (fun ω => F t ω ≤ x))
      atTop (nhds (sharpCDF α x))

def T32UpdateStatement : Prop :=
  ∀ {n : ℕ} (G : Finset (Fin n)) (i : Fin n)
    (z : Assignment n) (b : Bool),
    balance G (Function.update z i b)-balance G z =
      if i ∈ G then 2*(bit b-bit (z i)) else 0

def T32CrossingsStatement : Prop :=
  ∀ (b : ℤ),
    (multiplier ((b:ℝ)+2) ≠ multiplier b ↔ b = -2 ∨ b = -1 ∨ b = 0) ∧
    (multiplier ((b:ℝ)-2) ≠ multiplier b ↔ b = 0 ∨ b = 1 ∨ b = 2)

def T32PairedStatement : Prop :=
  ∀ {n : ℕ} (G : Finset (Fin n)) (i j : Fin n)
    (hij : i ≠ j) (z : Assignment n) (hi : z i = false) (hj : z j = true),
    balance G (Function.update (Function.update z i true) j false) - balance G z =
      (if i ∈ G then 2 else 0) - (if j ∈ G then 2 else 0)

def T33CoreStatement : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (b : ℕ)
    (hb : 1 ≤ b ∧ b ≤ n) (c : Fin n → ℝ),
    let E := fairExperiment n (oneSourceOutcome b c)
    (∀ i j, i ≠ j → xi E i j false = 0 ∧
      xi E i j true = (if 0 < i.val ∧ i.val < b ∧ j.val = 0 then 2 else 0) ∧
      xiBreve E i j*xiBreve E j i = 0) ∧
    yBreve E ⟨0,hn⟩ = 1/2+c ⟨0,hn⟩ ∧
    B1 E = (2+4*c ⟨0,hn⟩)*((b:ℝ)-1)/((n:ℝ)+(b:ℝ)*((b:ℝ)-1))

def T34CoreStatement : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (ρ : Pairing n) (hPair : Paired E ρ) (k q s : ℝ) (hReg : Regular E k q s),
    (∀ i b, |cmean E.design (fun z => z i = b) (potential E i b) -
      mean E.design (potential E i b)| =
      (1/2)*|cmean E.design (fun z => z i = b) (potential E i b) -
        cmean E.design (fun z => z i = !b) (potential E i b)| ∧
      |cmean E.design (fun z => z i = b) (potential E i b) -
        mean E.design (potential E i b)| ≤ k) ∧
    2 ≤ k ∧ 2*k ≤ 2*k^2 ∧ |adse E-eate E| ≤ 2*k^2*rSum E ρ/(n:ℝ)

end
end SAP.P009b
