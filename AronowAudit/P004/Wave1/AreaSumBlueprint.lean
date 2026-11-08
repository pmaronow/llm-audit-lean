import AronowAudit.P004.P004_SpatialAlgebraCompletion

/-! # Blueprint: the Euclidean area-integral bridge for `finite_area_sum_certificate` (P004-T5)

Dossier group P004, record 8. The held record `AronowAudit.P004.finite_area_sum_certificate`
is a proved finite weighted-bin calculation; it does not evaluate any Euclidean area integral,
and the frozen full spatial declaration `spatial_area_sum_counterexample` (and its alias
`area_sum_counterexample`) still depend on `sorry`. Resolution: `bridge` with new Lean
(map-P004; both referees accept, no fixes): prove that the actual spatial averages of the
existing `areaBinaryPopulation` (radius-one closed-disk nodes at `(0,0)` and `(100,0)`, planar
Lebesgue measure, binary angular-sector outcomes, bands `{0}`, `(d-1,d]`, `[0,5]`) equal the
finite table `areaWitnessTable` for EVERY assignment, that the six bins partition the
radius-six region, and all conclusions of the frozen full counterexample (case B of E008).

Paper proof: map-P004 REPORT, record 8 (distance to a closed unit disk is `max(ρ−1,0)`; the
polar sector integral `∫_{a<ρ≤b} 1{angularFraction<q} = qπ(b²−a²)` for `0≤q≤1/2`; division
by the bin area; aggregation over the partition by the proved `area_partition_identity`).
Implementation caution (referee 2): EuclideanSpace is not linearly isometric to the sup-norm
product `ℝ × ℝ`; transport volume to `ℂ` through `PiLp.volume_preserving_ofLp` and
`Complex.volume_preserving_equiv_pi`, then use `Complex.lintegral_comp_polarCoord_symm`.

The final declaration (writer) is `AronowAudit.P004.Wave1.area_sum_spatial_caseB` in
`AronowAudit/P004/Wave1/AreaSum.lean`. Do not use `annulus_radial_measure`,
`spatial_area_sum_counterexample` or `area_sum_counterexample` (sorry drafts) as premises.
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

/-- Frozen target: the full area-measure case-B bridge (mapper's `area_sum_spatial_caseB`):
the all-assignment table equality, the exact region partition, and every conclusion of the
frozen `spatial_area_sum_counterexample`. -/
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

/-- A1 (paper proof: "For a point at radial distance ρ from a center c, distance to its closed
unit disk is max(ρ−1,0) ... the point c+(x−c)/ρ lies on the unit circle and realizes distance
ρ−1"). Use `Metric.infDist_le_dist_of_mem`, `Metric.le_infDist`, `dist_triangle`. -/
def A1 : Prop :=
  ∀ c x : EuclideanSpace ℝ (Fin 2),
    Metric.infDist x (Metric.closedBall c 1) = max (dist x c - 1) 0

/-- A2 (paper proof: "at either node bin j=0 is the closed radius-one disk; bins j=1,…,5 are
the annuli j<ρ≤j+1; the whole-region band d=6 is ρ≤6"): the actual regions, using A1 and the
band definition of `areaBinaryPopulation` (`{0}`, `Ioc (d-1) d`, and `Icc 0 5` at `d = 6`). -/
def A2 : Prop :=
  (∀ (i : Fin 2) (j : Fin 6),
    region areaBinaryPopulation i (j : ℝ) = bin (areaBinaryCenter i) j) ∧
  (∀ i : Fin 2, region areaBinaryPopulation i 6 = Metric.closedBall (areaBinaryCenter i) 6)

/-- A3 (paper proof: "These six sets are pairwise disjoint and their union is that whole
region, including all radial boundary conventions"). Pure real inequalities. -/
def A3 : Prop :=
  ∀ c : EuclideanSpace ℝ (Fin 2),
    Metric.closedBall c 6 = (⋃ j : Fin 6, bin c j) ∧
    Pairwise (fun j k : Fin 6 => Disjoint (bin c j) (bin c k))

/-- A4 (standard input made explicit, proved from Mathlib; paper proof: "polar change of
variables, with Jacobian r, gives ∫_A 1{angularFraction(c,x)<q} dx=∫_a^b∫_0^(2πq)r dθ dr=
πq(b²−a²)"). The sector measure of a half-open annulus, for `0 ≤ q ≤ 1/2`. HARD node: transport
`EuclideanSpace ℝ (Fin 2)` to `ℂ` (`PiLp.volume_preserving_ofLp`,
`Complex.volume_preserving_equiv_pi`, translation invariance `measure_preimage_add_right`), then
`Complex.lintegral_comp_polarCoord_symm`, `Complex.arg_mul_cos_add_sin_mul_I`,
`lintegral_prod`, `Real.volume_Ico`. -/
def A4 : Prop :=
  ∀ (c : EuclideanSpace ℝ (Fin 2)) (a b q : ℝ), 0 ≤ a → a ≤ b → 0 ≤ q → q ≤ 1/2 →
    volume ({x | a < dist x c ∧ dist x c ≤ b} ∩ {x | angularFraction c x < q}) =
      ENNReal.ofReal (q * Real.pi * (b^2 - a^2))

/-- A5 (paper proof: "a₀=π ... area a_j=π((j+1)²−j²)=π(2j+1)"; the center and radial
boundaries are null). Plain bin areas and the closed-disk sector, from A4 and
`EuclideanSpace.volume_closedBall_fin_two`, `measure_sdiff`, `measure_singleton`. -/
def A5 : Prop :=
  (∀ (c : EuclideanSpace ℝ (Fin 2)) (j : ℕ),
    volume (bin c j) = ENNReal.ofReal (Real.pi * (2 * (j : ℝ) + 1))) ∧
  (∀ (c : EuclideanSpace ℝ (Fin 2)) (q : ℝ), 0 ≤ q → q ≤ 1/2 →
    volume (Metric.closedBall c 1 ∩ {x | angularFraction c x < q}) =
      ENNReal.ofReal (q * Real.pi))

/-- A6 (paper proof: "Outcomes are globally either 0 or 1 by the nested if-definition";
"The relevant indicators are measurable: the argument map is Borel"). Use
`Complex.measurable_arg`, `Measurable.ite`, `measurableSet_lt`, `measurable_dist`. -/
def A6 : Prop :=
  (∀ x z, areaBinaryPopulation.outcome x z = 0 ∨ areaBinaryPopulation.outcome x z = 1) ∧
  (∀ z, Measurable (fun x => areaBinaryPopulation.outcome x z)) ∧
  (∀ c : EuclideanSpace ℝ (Fin 2), Measurable (angularFraction c))

/-- A7 (paper proof: "Every mass is positive and finite since π>0. The binary field is
integrable on each bin and the whole disk, so WellDefined holds for all seven used bands").
Use A2, A5, A6, `Measure.integrableOn_of_bounded`. -/
def A7 : Prop :=
  (∀ j : Fin 6, WellDefined areaBinaryPopulation j) ∧ WellDefined areaBinaryPopulation 6

/-- A8 (paper proof: "Divide each computed numerator q_j(z_i)a_j by a_j to obtain
circleAverage(areaBinaryPopulation,j)i z=q_j(z_i) for every i,z"). On bin `j` of node `i` the
outcome is the indicator of the sector `{angularFraction < binShare j (z i)}` (the other node's
region is at distance `≥ 94 > 6`, so the correct branch is used, and the share's radial branch
is constant on the bin); integrate by A4/A5 and divide by A5's area. -/
def A8 : Prop :=
  ∀ (j : Fin 6) (i : Fin 2) (z : Assignment 2),
    circleAverage areaBinaryPopulation (j : ℝ) i z = binShare j (z i)

/-- A9 (paper proof: "The finite table areaWitnessTable realizes precisely these same shares
... Each list sums to one"). Pure arithmetic: `fin_cases j`, `cases z i`, `norm_num`
[`areaWitnessTable`, `finiteAverage`, `areaWitnessMass`, `areaWitnessOutcome`,
`Fin.sum_univ_succ`]. -/
def A9 : Prop :=
  ∀ (j : Fin 6) (i : Fin 2) (z : Assignment 2), areaWitnessTable j i z = binShare j (z i)

/-- A10 (paper proof: "The bins partition the actual radius-six disk with total mass
π(1+3+5+7+9+11)=36π. Additivity of the integrals over these disjoint measurable bins yields
whole-region mean Σ_j(a_j/(36π))q_j(z_i)"). Apply the proved `area_partition_identity`
(`P004_SpatialAlgebraCompletion.lean`) with the bins, using A2, A3, A5, A7, A8. -/
def A10 : Prop :=
  ∀ (i : Fin 2) (z : Assignment 2),
    circleAverage areaBinaryPopulation 6 i z =
      ∑ j : Fin 6, (2 * (j : ℝ) + 1) / 36 * binShare j (z i)

/-- A11 (paper proof: "Its own-treatment effect, and then the node mean, is
[1·(−2/25)+(3+5+7+9+11)·23/2500]/36=121/18000"). Pure arithmetic over the four assignments:
`norm_num` [`ame`, `nodeEffect`, `marginal`, `expect`, `designWeight`, `coin`,
`assignment_two_univ`, `binShare`, `Fin.sum_univ_succ`]. -/
def A11 : Prop :=
  ame (fun _ => 1/2) (fun (i : Fin 2) (z : Assignment 2) =>
    ∑ j : Fin 6, (2 * (j : ℝ) + 1) / 36 * binShare j (z i)) = (121/18000 : ℝ)

/-- The nodes suffice (proved). Clauses 8 and 9 come from the proved finite certificate
`finite_area_sum_certificate` after the table equality. -/
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

/-- The volume clause used by `assemble`, from A2 and A5 (proved). -/
theorem volumes (hA2 : A2) (hA5 : A5) : ∀ (i : Fin 2) (j : Fin 6),
    (volume (region areaBinaryPopulation i j)).toReal = Real.pi*(2*(j : ℝ)+1) := by
  intro i j
  rw [hA2.1 i j, hA5.1, ENNReal.toReal_ofReal (by positivity)]

/-- The final assembly from the eleven nodes (A1 and A4 are inputs of A2 and A5 respectively,
and are kept as nodes for the writers; they are not needed again here). -/
theorem assemble_all (_hA1 : A1) (hA2 : A2) (hA3 : A3) (_hA4 : A4) (hA5 : A5) (hA6 : A6)
    (hA7 : A7) (hA8 : A8) (hA9 : A9) (hA10 : A10) (hA11 : A11) : Target :=
  assemble hA2 hA3 hA6 hA7 hA8 hA9 hA10 hA11 (volumes hA2 hA5)

end
end AronowAudit.P004.Wave1.AreaSum
