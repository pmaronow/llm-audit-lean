import SAP.P039.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory

/- Measures are numbered 0 through 4, corresponding to paper measures (1) through (5).
Each deposited decimal is its exact rational value. Values outside extremismElections
are placeholders and are never optimized over. Winner years and margins are explicit. -/

abbrev ExtremismMeasure := Fin 5

noncomputable def relativeExtremism (incumbent challenger reference : ℝ) : ℝ :=
  (|incumbent - reference| - |challenger - reference|) / 2

noncomputable def extremismElections : ExtremismMeasure → Finset ℕ
  | 0 => {1948, 1952, 1956, 1960, 1964, 1968, 1972, 1976, 1980, 1984, 1988, 1992, 1996, 2000, 2004, 2008, 2012}
  | 1 => {1972, 1976, 1980, 1984, 1988, 1992, 1996, 2000, 2004, 2008, 2012}
  | 2 => {1948, 1952, 1956, 1960, 1964, 1968, 1972, 1976, 1980, 1984, 1988, 1992, 1996, 2000, 2004, 2008, 2012}
  | 3 => {1972, 1976, 1980, 1984, 1988, 1992, 1996, 2000, 2004, 2008, 2012}
  | 4 => {1960, 1964, 1968, 1972, 1984, 1996, 2004, 2008}

noncomputable def depositedExtremism (j : ExtremismMeasure) (t : ℕ) : ℝ :=
  match j with
  | 0 =>
    if t = 1948 then (186449401704861 / 1000000000000000 : ℝ) else
    if t = 1952 then (34178139300207 / 500000000000000 : ℝ) else
    if t = 1956 then (-39661945232703 / 1000000000000000 : ℝ) else
    if t = 1960 then (-1291245001547 / 31250000000000 : ℝ) else
    if t = 1964 then (-24728138844441 / 100000000000000 : ℝ) else
    if t = 1968 then (21313513173683 / 125000000000000 : ℝ) else
    if t = 1972 then (-365450440554801 / 1000000000000000 : ℝ) else
    if t = 1976 then (22321319108051 / 500000000000000 : ℝ) else
    if t = 1980 then (-498138285011637 / 1000000000000000 : ℝ) else
    if t = 1984 then (235890938802093 / 1000000000000000 : ℝ) else
    if t = 1988 then (153129340875841 / 1000000000000000 : ℝ) else
    if t = 1992 then (133646079679683 / 1000000000000000 : ℝ) else
    if t = 1996 then (-104467146002477 / 1000000000000000 : ℝ) else
    if t = 2000 then (-171942930345359 / 2000000000000000 : ℝ) else
    if t = 2004 then (9745517486293 / 200000000000000 : ℝ) else
    if t = 2008 then (-12363873861033 / 200000000000000 : ℝ) else
    if t = 2012 then (294616125544001 / 10000000000000000 : ℝ) else
    0
  | 1 =>
    if t = 1972 then (-51177218671487 / 100000000000000 : ℝ) else
    if t = 1976 then (-115844246379719 / 500000000000000 : ℝ) else
    if t = 1980 then (-85731054060753 / 500000000000000 : ℝ) else
    if t = 1984 then (-71228875084027 / 2000000000000000 : ℝ) else
    if t = 1988 then (-74126802891113 / 250000000000000 : ℝ) else
    if t = 1992 then (-61530236247573 / 1000000000000000 : ℝ) else
    if t = 1996 then (42109491513391 / 125000000000000 : ℝ) else
    if t = 2000 then (237764496391801 / 1000000000000000 : ℝ) else
    if t = 2004 then (-42533500234007 / 125000000000000 : ℝ) else
    if t = 2008 then (-30311773910617 / 100000000000000 : ℝ) else
    if t = 2012 then (16577130166183 / 50000000000000 : ℝ) else
    0
  | 2 =>
    if t = 1948 then (239968577629729 / 1000000000000000 : ℝ) else
    if t = 1952 then (175955071969269 / 2000000000000000 : ℝ) else
    if t = 1956 then (-1595208354199 / 31250000000000 : ℝ) else
    if t = 1960 then (-106360901712767 / 2000000000000000 : ℝ) else
    if t = 1964 then (-63652403833659 / 200000000000000 : ℝ) else
    if t = 1968 then (109725714189791 / 500000000000000 : ℝ) else
    if t = 1972 then (-227917425434853 / 500000000000000 : ℝ) else
    if t = 1976 then (101692388889377 / 2000000000000000 : ℝ) else
    if t = 1980 then (-310511999936889 / 500000000000000 : ℝ) else
    if t = 1984 then (6845007275751 / 25000000000000 : ℝ) else
    if t = 1988 then (34639145815011 / 200000000000000 : ℝ) else
    if t = 1992 then (48128903307363 / 250000000000000 : ℝ) else
    if t = 1996 then (-14605008654561 / 100000000000000 : ℝ) else
    if t = 2000 then (-42411239115459 / 250000000000000 : ℝ) else
    if t = 2004 then (49898136705373 / 200000000000000 : ℝ) else
    if t = 2008 then (-4760060756913 / 40000000000000 : ℝ) else
    if t = 2012 then (403303265691201 / 10000000000000000 : ℝ) else
    0
  | 3 =>
    if t = 1972 then (-60215659702977 / 100000000000000 : ℝ) else
    if t = 1976 then (-4509698730617 / 20000000000000 : ℝ) else
    if t = 1980 then (-294347822983647 / 1000000000000000 : ℝ) else
    if t = 1984 then (114745734296501 / 50000000000000000 : ℝ) else
    if t = 1988 then (-55288164673047 / 200000000000000 : ℝ) else
    if t = 1992 then (-53214053956201 / 20000000000000000 : ℝ) else
    if t = 1996 then (147646495781997 / 500000000000000 : ℝ) else
    if t = 2000 then (30818201020529 / 200000000000000 : ℝ) else
    if t = 2004 then (-27900981155331 / 200000000000000 : ℝ) else
    if t = 2008 then (-36029988872383 / 100000000000000 : ℝ) else
    if t = 2012 then (17120565866919 / 50000000000000 : ℝ) else
    0
  | 4 =>
    if t = 1960 then (-17 / 250 : ℝ) else
    if t = 1964 then (-11 / 50 : ℝ) else
    if t = 1968 then (29 / 250 : ℝ) else
    if t = 1972 then (-41 / 1000 : ℝ) else
    if t = 1984 then (77 / 2000 : ℝ) else
    if t = 1996 then (83 / 2000 : ℝ) else
    if t = 2004 then (13 / 250 : ℝ) else
    if t = 2008 then (-9 / 2000 : ℝ) else
    0

noncomputable def magnitudeWinner : ExtremismMeasure → ℕ
  | 0 => 1980
  | 1 => 1972
  | 2 => 1980
  | 3 => 1972
  | 4 => 1964

noncomputable def signedWinner : ExtremismMeasure → ℕ
  | 0 => 1984
  | 1 => 1996
  | 2 => 1984
  | 3 => 2012
  | 4 => 1968

noncomputable def magnitudeMargin : ExtremismMeasure → ℝ
  | 0 => 33171961114209 / 250000000000000
  | 1 => 85752092421407 / 500000000000000
  | 2 => 20648643625509 / 125000000000000
  | 3 => 12092835415297 / 50000000000000
  | 4 => 13 / 125

noncomputable def closestCompetitor : ExtremismMeasure → ℕ
  | 0 => 1972
  | 1 => 2004
  | 2 => 1972
  | 3 => 2008
  | 4 => 1968

noncomputable def modelElections (j : ExtremismMeasure) (breadAndPeace : Bool) : Finset ℕ :=
  if breadAndPeace && (j == 0 || j == 2) then (extremismElections j).erase 1948
  else extremismElections j

noncomputable def maximumEffect (β : ℝ) (j : ExtremismMeasure) : ℝ :=
  β * depositedExtremism j (magnitudeWinner j)

/-- Exact scores at the five signed maxima, in the paper's measure order. -/
noncomputable def signedMaximumScore : ExtremismMeasure → ℝ :=
  ![0.235890938802093, 0.336875932107128, 0.27380029103004, 0.34241131733838, 0.116]

/-- Exact scores selected by the corrected magnitude rule, in the paper's measure order. -/
noncomputable def magnitudeMaximumScore : ExtremismMeasure → ℝ :=
  ![-0.498138285011637, -0.51177218671487, -0.621023999873778, -0.60215659702977, -0.22]

/-- The voter-centered counterexamples and all five positive signed maxima refute the literal rule. -/
def T5Statement : Prop :=
  (1972 ∈ extremismElections 1 ∧ 1980 ∈ extremismElections 1 ∧
    1972 ∈ extremismElections 3 ∧ 1980 ∈ extremismElections 3 ∧
    |depositedExtremism 1 1972| - |depositedExtremism 1 1980| =
      (85077519648341 / 250000000000000 : ℝ) ∧
    |depositedExtremism 3 1972| - |depositedExtremism 3 1980| =
      (307808774046123 / 1000000000000000 : ℝ) ∧
    |depositedExtremism 1 1980| < |depositedExtremism 1 1972| ∧
    |depositedExtremism 3 1980| < |depositedExtremism 3 1972|) ∧
  (1980 ∈ extremismElections 2 ∧ 1984 ∈ extremismElections 2 ∧
    depositedExtremism 2 1980 < 0 ∧ 0 < depositedExtremism 2 1984 ∧
    (-2.23 : ℝ) * depositedExtremism 2 1984 =
      (-1526436622492473 / 2500000000000000 : ℝ) ∧
    (-2.23 : ℝ) * depositedExtremism 2 1984 < 0 ∧
    (-2.23 : ℝ) * depositedExtremism 2 1984 ≠ (1.38 : ℝ) ∧
    (∀ t ∈ extremismElections 2,
      depositedExtremism 2 t ≤ depositedExtremism 2 1984)) ∧
  (∀ j : ExtremismMeasure,
signedWinner j ∈ extremismElections j ∧
    0 < depositedExtremism j (signedWinner j) ∧
    ∀ t ∈ extremismElections j, t ≠ signedWinner j →
      depositedExtremism j t < depositedExtremism j (signedWinner j)) ∧
  (∀ j : ExtremismMeasure, depositedExtremism j (signedWinner j) = signedMaximumScore j)

/-- Unique magnitude selections, attained margins, both samples, and the signed fitted contribution. -/
def T6Statement : Prop :=
  (∀ j : ExtremismMeasure,
magnitudeWinner j ∈ extremismElections j ∧
    depositedExtremism j (magnitudeWinner j) < 0 ∧
    ∀ t ∈ extremismElections j, t ≠ magnitudeWinner j →
      |depositedExtremism j t| < |depositedExtremism j (magnitudeWinner j)|) ∧
  (∀ j : ExtremismMeasure,
0 < magnitudeMargin j ∧
    closestCompetitor j ∈ extremismElections j ∧
    closestCompetitor j ≠ magnitudeWinner j ∧
    |depositedExtremism j (magnitudeWinner j)| -
      |depositedExtremism j (closestCompetitor j)| = magnitudeMargin j ∧
    ∀ t ∈ extremismElections j, t ≠ magnitudeWinner j →
      magnitudeMargin j ≤ |depositedExtremism j (magnitudeWinner j)| -
        |depositedExtremism j t|) ∧
  (∀ (j : ExtremismMeasure) (bp : Bool),
magnitudeWinner j ∈ modelElections j bp ∧
    (∀ t ∈ modelElections j bp, t ≠ magnitudeWinner j →
      |depositedExtremism j t| < |depositedExtremism j (magnitudeWinner j)|) ∧
    (modelElections j false).card - 5 = (if j == 0 || j == 2 then 12 else if j == 4 then 3 else 6) ∧
    (modelElections j true).card - 6 = (if j == 0 || j == 2 then 10 else if j == 4 then 2 else 5)) ∧
  (∀ (β g : ℝ) (j : ExtremismMeasure),
(∀ x : ℝ, (g + β * x) - (g + β * 0) = β * x) ∧
    ∀ t ∈ extremismElections j, |β * depositedExtremism j t| ≤ |maximumEffect β j|) ∧
  (∀ (β : ℝ) (j : ExtremismMeasure),
(0 < maximumEffect β j ↔ β < 0) ∧
    (maximumEffect β j = 0 ↔ β = 0) ∧
    (maximumEffect β j < 0 ↔ 0 < β)) ∧
  ((-2.23 : ℝ) * (-0.62) = 1.3826 ∧
    (1.375 : ℝ) ≤ (-2.23 : ℝ) * (-0.62) ∧ (-2.23 : ℝ) * (-0.62) < 1.385 ∧
    (-0.625 : ℝ) ≤ depositedExtremism 2 1980 ∧ depositedExtremism 2 1980 < -0.615) ∧
  (∀ j : ExtremismMeasure, depositedExtremism j (magnitudeWinner j) = magnitudeMaximumScore j)

end SAP.P039
