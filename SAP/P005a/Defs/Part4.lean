import SAP.P005a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P005a

noncomputable section
open Finset Filter
open scoped BigOperators Matrix Topology

def signX : Fin 6 → ℝ := ![-8/5, -1, 0, 3/5, 4/5, 6/5]

def signPopulation : Population 6 1 where
  x := fun i _ => signX i
  yT := fun i => signX i^2
  yC := fun i => 2*signX i^2 + 3

def weightA : Fin 6 → ℝ := ![-3, -2, -1, 0, 1, 5]

def weightY : Fin 6 → ℝ := fun i => weightA i^2

def weightScale : ℝ := Real.sqrt (3/20)

def weightPopulation : Population 6 1 := scalarPopulation weightA weightY (fun _ => 0) weightScale

def weightX (i : Fin 6) : ℝ := weightScale * weightA i

def leverageA : Fin 16 → ℝ := ![8,-8,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1]

def leverageY : Fin 16 → ℝ := fun i => if i.val < 2 then 1/64 else 1

def leveragePopulation : Population 16 1 :=
  scalarPopulation leverageA leverageY (fun _ => 0) (Real.sqrt (8/71))

def spikeV (n : ℕ) (i : Fin n) : ℝ :=
  if i.val = 0 then 0 else -1 + 2*(i.val-1 : ℕ)/(n-2 : ℝ)

def spikeA (n : ℕ) (i : Fin n) : ℝ :=
  if i.val = 0 then 1 else spikeV n i/(n : ℝ)^2

def spikeZ (n : ℕ) (i : Fin n) : ℝ := spikeA n i - 1/(n : ℝ)

def spikeQ (n : ℕ) : ℝ := popMean (fun i => spikeZ n i^2)

def spikePopulation (n : ℕ) : Population n 1 where
  x := fun i _ => spikeZ n i / Real.sqrt (spikeQ n)
  yT := spikeV n
  yC := spikeV n

end
end SAP.P005a
