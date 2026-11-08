import SAP.P028.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

structure BinaryAtom where
  d0 : Bool
  d1 : Bool
  y0 : Bool
  y1 : Bool
  r0 : Bool
  r1 : Bool
  deriving DecidableEq

def bit (b : Bool) : ℚ := if b then 1 else 0

structure BinaryLaw where
  atom : Fin 17 → BinaryAtom
  mass : Fin 17 → ℚ

def assignmentMass (z : Bool) : ℚ := if z then 101/200 else 99/200

def jointMass (M : BinaryLaw) (i : Fin 17) (z : Bool) : ℚ :=
  M.mass i * assignmentMass z

def fprob (M : BinaryLaw) (E : Fin 17 → Prop) : ℚ :=
  ∑ i, if E i then M.mass i else 0

def fexpect (M : BinaryLaw) (f : Fin 17 → ℚ) : ℚ := ∑ i, M.mass i * f i

def fmean (M : BinaryLaw) (f : Fin 17 → ℚ) (E : Fin 17 → Prop) : ℚ :=
  (∑ i, if E i then M.mass i * f i else 0) / fprob M E

def fd (a : BinaryAtom) (z : Bool) : Bool := if z then a.d1 else a.d0

def fy (a : BinaryAtom) (z : Bool) : Bool := if fd a z then a.y1 else a.y0

def fr (a : BinaryAtom) (z : Bool) : Bool := if z then a.r1 else a.r0

def fc (a : BinaryAtom) : Prop := a.d0 = false ∧ a.d1 = true

def fpc (M : BinaryLaw) : ℚ := fprob M (fun i => fc (M.atom i))

def fey (M : BinaryLaw) (z : Bool) : ℚ := fexpect M (fun i => bit (fy (M.atom i) z))

def fcy (M : BinaryLaw) (d : Bool) : ℚ :=
  fmean M (fun i => bit (if d then (M.atom i).y1 else (M.atom i).y0))
    (fun i => fc (M.atom i))

def recordedCell (M : BinaryLaw) (z d v : Bool) : ℚ :=
  fprob M (fun i => fd (M.atom i) z = d ∧ fr (M.atom i) z = true ∧ fy (M.atom i) z = v)

def missingCell (M : BinaryLaw) (z d : Bool) : ℚ :=
  fprob M (fun i => fd (M.atom i) z = d ∧ fr (M.atom i) z = false)

def observedLaw (M : BinaryLaw) (o : Bool × Bool × Bool × Bool) : ℚ :=
  assignmentMass o.1 * fprob M (fun i => fd (M.atom i) o.1 = o.2.1 ∧
    fr (M.atom i) o.1 = o.2.2.1 ∧
    (fr (M.atom i) o.1 && fy (M.atom i) o.1) = o.2.2.2)

def finiteValid (M : BinaryLaw) : Prop :=
  (∀ i, 0 < M.mass i) ∧ (∑ i, M.mass i) = 1 ∧
  (∀ i, bit (M.atom i).d0 ≤ bit (M.atom i).d1) ∧
  fexpect M (fun i => bit (M.atom i).d1 - bit (M.atom i).d0) = fpc M ∧
  0 < fpc M

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

def recordedCount (z d v : Bool) : ℚ :=
  if z then (if d then (if v then 110 else 67) else (if v then 130 else 164))
  else (if d then (if v then 40 else 39) else (if v then 167 else 212))

def missingCount (z d : Bool) : ℚ := if z then (if d then 8 else 26) else (if d then 1 else 36)

def armCount (z : Bool) : ℚ := if z then 505 else 495

def respondentArmMean (M : BinaryLaw) (z : Bool) : ℚ :=
  fmean M (fun i => bit (fy (M.atom i) z)) (fun i => fr (M.atom i) z = true)

def respondentCellMean (M : BinaryLaw) (d z : Bool) : ℚ :=
  fmean M (fun i => bit (fy (M.atom i) z))
    (fun i => fd (M.atom i) z = d ∧ fr (M.atom i) z = true)

def ftakeup (M : BinaryLaw) (d z : Bool) : ℚ :=
  fprob M (fun i => fd (M.atom i) z = d)

def fcellmean (M : BinaryLaw) (d z : Bool) : ℚ :=
  fmean M (fun i => bit (fy (M.atom i) z)) (fun i => fd (M.atom i) z = d)

def corollaryPair (p q r e0 e1 a n : ℚ) : ℚ × ℚ :=
  ((e0-q*a-r*n)/p, (e0-q*a-r*n)/p + (e1-e0)/p)

def fullCorollary (M : BinaryLaw) : ℚ × ℚ :=
  corollaryPair (fpc M) (ftakeup M true false) (ftakeup M false true)
    (fey M false) (fey M true) (fcellmean M true false) (fcellmean M false true)

def respondentCorollary (M : BinaryLaw) : ℚ × ℚ :=
  corollaryPair (fpc M) (ftakeup M true false) (ftakeup M false true)
    (respondentArmMean M false) (respondentArmMean M true)
    (respondentCellMean M true false) (respondentCellMean M false true)

def fullPotential : BinaryAtom := ⟨false,true,false,true,true,true⟩

def twoAtomProb (E : Bool → Prop) : ℚ := ∑ z : Bool, if E z then 1/2 else 0

def twoAtomMean (f : Bool → ℚ) (E : Bool → Prop) : ℚ :=
  (∑ z : Bool, if E z then (1/2)*f z else 0) / twoAtomProb E

end
end SAP.P028
