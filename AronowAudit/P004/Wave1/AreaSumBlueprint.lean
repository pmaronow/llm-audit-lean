import AronowAudit.P004.P004_SpatialAlgebraCompletion

/-! # Euclidean area integrals for P004-T5

The spatial averages for radius-one closed-disk nodes at `(0,0)` and `(100,0)`,
planar Lebesgue measure, and binary angular-sector outcomes equal the finite
case-B table for every assignment. The six bins partition the radius-six
region.

Distance to a closed unit disk is `max(ρ−1,0)`. Polar integration gives the
sector integral `qπ(b²−a²)` on `a<ρ≤b` for `0≤q≤1/2`. Dividing by the bin area
gives the bin averages, and additivity over the partition gives the region average.

Euclidean space is not linearly isometric to the sup-norm product `ℝ × ℝ`.
Volume is transported to `ℂ` through the volume-preserving coordinate maps
before applying polar integration.
-/

namespace AronowAudit.P004.Wave1.AreaSum

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- The `j`-th distance bin about a disk center `c`: the closed unit disk for `j = 0`, and
the half-open annulus `j < ρ ≤ j+1` for `j ≥ 1` (`ρ = dist x c`). -/
def bin (c : EuclideanSpace ℝ (Fin 2)) (j : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  if j = 0 then Metric.closedBall c 1 else {x | (j : ℝ) < dist x c ∧ dist x c ≤ j + 1}

/-- The case-B share `q_j(a)`: treated `1/50` in the node disk and `273/2500` outside it,
control `1/10`. -/
def binShare (j : Fin 6) (a : Bool) : ℝ :=
  if a then (if j = 0 then 1/50 else 273/2500) else 1/10

/-- The area-measure case-B statement: all-assignment table equality,
the exact region partition, binary outcomes, well-defined averages, bin volumes,
and the contrasting bin-sum and whole-region effects. -/
def Target : Prop :=
  (∀ j : Fin 6, circleAverage areaBinaryPopulation (j : ℝ) = areaWitnessTable j) ∧
  (∀ i : Fin 2, region areaBinaryPopulation i 6 =
    ⋃ j : Fin 6, region areaBinaryPopulation i (j : ℝ)) ∧
  (∀ i : Fin 2, Pairwise (fun j k : Fin 6 =>
    Disjoint (region areaBinaryPopulation i (j : ℝ))
      (region areaBinaryPopulation i (k : ℝ)))) ∧
  (∀ x z, areaBinaryPopulation.outcome x z = 0 ∨ areaBinaryPopulation.outcome x z = 1) ∧
  (∀ j : Fin 6, WellDefined areaBinaryPopulation j) ∧
  WellDefined areaBinaryPopulation 6 ∧
  (∀ i (j : Fin 6), (volume (region areaBinaryPopulation i j)).toReal =
    Real.pi*(2*(j : ℝ)+1)) ∧
  (∑ j : Fin 6, hajek (circleAverage areaBinaryPopulation j) areaWitnessAssignment) =
    -(17/500 : ℝ) ∧
  (∑ j : Fin 6, ame (fun _ => 1/2) (circleAverage areaBinaryPopulation j)) = -(17/500 : ℝ) ∧
  ame (fun _ => 1/2) (circleAverage areaBinaryPopulation 6) = (121/18000 : ℝ) ∧
  (0 : ℝ) < 121/18000 ∧ -(17/500 : ℝ) ≠ 121/18000

/-- Distance from a point at radial distance ρ to the closed unit disk is
max(ρ−1,0). For ρ>1, the point c+(x−c)/ρ realizes the distance ρ−1. -/
def A1 : Prop :=
  ∀ c x : EuclideanSpace ℝ (Fin 2),
    Metric.infDist x (Metric.closedBall c 1) = max (dist x c - 1) 0

/-- At either node, bin j=0 is the closed radius-one disk, bins j=1,…,5 are
the annuli j<ρ≤j+1, and the whole-region band d=6 is ρ≤6. These are the regions
for the bands `{0}`, `Ioc (d-1) d`, and `Icc 0 5` at `d = 6`. -/
def A2 : Prop :=
  (∀ (i : Fin 2) (j : Fin 6),
    region areaBinaryPopulation i (j : ℝ) = bin (areaBinaryCenter i) j) ∧
  (∀ i : Fin 2, region areaBinaryPopulation i 6 = Metric.closedBall (areaBinaryCenter i) 6)

/-- The six bins are pairwise disjoint and their union is the whole region,
including all radial boundary conventions. This reduces to real inequalities. -/
def A3 : Prop :=
  ∀ c : EuclideanSpace ℝ (Fin 2),
    Metric.closedBall c 6 = (⋃ j : Fin 6, bin c j) ∧
    Pairwise (fun j k : Fin 6 => Disjoint (bin c j) (bin c k))

/-- Sector measure of a half-open annulus, for `0 ≤ q ≤ 1/2`.
Polar change of variables, with Jacobian r, gives
∫_A 1{angularFraction(c,x)<q} dx = ∫_a^b∫_0^(2πq) r dθ dr = πq(b²−a²).
Volume is transported from Euclidean space to the complex plane through
volume-preserving coordinate maps and translation before polar integration. -/
def A4 : Prop :=
  ∀ (c : EuclideanSpace ℝ (Fin 2)) (a b q : ℝ), 0 ≤ a → a ≤ b → 0 ≤ q → q ≤ 1/2 →
    volume ({x | a < dist x c ∧ dist x c ≤ b} ∩ {x | angularFraction c x < q}) =
      ENNReal.ofReal (q * Real.pi * (b^2 - a^2))

/-- Bin areas and the closed-disk sector: a₀=π and
a_j=π((j+1)²−j²)=π(2j+1). The center and radial boundaries have zero area. -/
def A5 : Prop :=
  (∀ (c : EuclideanSpace ℝ (Fin 2)) (j : ℕ),
    volume (bin c j) = ENNReal.ofReal (Real.pi * (2 * (j : ℝ) + 1))) ∧
  (∀ (c : EuclideanSpace ℝ (Fin 2)) (q : ℝ), 0 ≤ q → q ≤ 1/2 →
    volume (Metric.closedBall c 1 ∩ {x | angularFraction c x < q}) =
      ENNReal.ofReal (q * Real.pi))

/-- Outcomes are globally either 0 or 1 by the nested conditional definition.
The relevant indicators are measurable because the argument map is Borel measurable. -/
def A6 : Prop :=
  (∀ x z, areaBinaryPopulation.outcome x z = 0 ∨ areaBinaryPopulation.outcome x z = 1) ∧
  (∀ z, Measurable (fun x => areaBinaryPopulation.outcome x z)) ∧
  (∀ c : EuclideanSpace ℝ (Fin 2), Measurable (angularFraction c))

/-- Every mass is positive and finite since π>0. The binary field is
integrable on each bin and the whole disk, so the averages are well-defined
for all seven bands. -/
def A7 : Prop :=
  (∀ j : Fin 6, WellDefined areaBinaryPopulation j) ∧ WellDefined areaBinaryPopulation 6

/-- Dividing each numerator q_j(z_i)a_j by a_j gives the bin average
q_j(z_i) for every i,z. On bin j of node i, the outcome is the indicator of
the sector with angular fraction below q_j(z_i). The other node's region
is at distance at least 94>6, and the radial share is constant on the bin. -/
def A8 : Prop :=
  ∀ (j : Fin 6) (i : Fin 2) (z : Assignment 2),
    circleAverage areaBinaryPopulation (j : ℝ) i z = binShare j (z i)

/-- The finite table realizes precisely the same shares. The three atom masses
in bin j sum to 2j+1, which cancels in the normalized average. -/
def A9 : Prop :=
  ∀ (j : Fin 6) (i : Fin 2) (z : Assignment 2), areaWitnessTable j i z = binShare j (z i)

/-- The bins partition the radius-six disk with total mass
π(1+3+5+7+9+11)=36π. Additivity of integrals over these disjoint measurable bins
gives the whole-region mean Σ_j(a_j/(36π))q_j(z_i). -/
def A10 : Prop :=
  ∀ (i : Fin 2) (z : Assignment 2),
    circleAverage areaBinaryPopulation 6 i z =
      ∑ j : Fin 6, (2 * (j : ℝ) + 1) / 36 * binShare j (z i)

/-- The own-treatment effect, and then the node mean, is
[1·(−2/25)+(3+5+7+9+11)·23/2500]/36=121/18000.
This is finite arithmetic over the four assignments. -/
def A11 : Prop :=
  ame (fun _ => 1/2) (fun (i : Fin 2) (z : Assignment 2) =>
    ∑ j : Fin 6, (2 * (j : ℝ) + 1) / 36 * binShare j (z i)) = (121/18000 : ℝ)

/-- The bin identities and integrability statements imply the case-B result.
The two bin-sum clauses follow from `finite_area_sum_certificate` after the table equality. -/
theorem assemble (hA2 : A2) (hA3 : A3) (hA6 : A6) (hA7 : A7) (hA8 : A8) (hA9 : A9)
    (hA10 : A10) (hA11 : A11) (hvol : ∀ (i : Fin 2) (j : Fin 6),
      (volume (region areaBinaryPopulation i j)).toReal = Real.pi*(2*(j : ℝ)+1)) :
    Target := by
  have htab : ∀ j : Fin 6, circleAverage areaBinaryPopulation (j : ℝ) = areaWitnessTable j := by
    intro j
    funext i z
    rw [hA8, hA9]
  obtain ⟨-, -, hsum, hame, -⟩ := finite_area_sum_certificate
  refine ⟨htab, fun i => ?_, fun i => ?_, hA6.1, hA7.1, hA7.2, hvol, ?_, ?_, ?_,
    by norm_num, by norm_num⟩
  · rw [hA2.2 i, (hA3 (areaBinaryCenter i)).1]
    exact Set.iUnion_congr fun j => (hA2.1 i j).symm
  · intro j k hjk
    rw [hA2.1 i j, hA2.1 i k]
    exact (hA3 (areaBinaryCenter i)).2 hjk
  · simp_rw [htab]
    exact hsum
  · simp_rw [htab]
    exact hame
  · have h6 : circleAverage areaBinaryPopulation 6 = fun (i : Fin 2) (z : Assignment 2) =>
        ∑ j : Fin 6, (2 * (j : ℝ) + 1) / 36 * binShare j (z i) := by
      funext i z
      exact hA10 i z
    rw [h6]
    exact hA11

/-- The volume clause used by `assemble`, from A2 and A5. -/
theorem volumes (hA2 : A2) (hA5 : A5) : ∀ (i : Fin 2) (j : Fin 6),
    (volume (region areaBinaryPopulation i j)).toReal = Real.pi*(2*(j : ℝ)+1) := by
  intro i j
  rw [hA2.1 i j, hA5.1, ENNReal.toReal_ofReal (by positivity)]


end
end AronowAudit.P004.Wave1.AreaSum
