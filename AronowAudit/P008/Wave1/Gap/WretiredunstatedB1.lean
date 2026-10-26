import AronowAudit.P008.P008_Audit
import AronowAudit.P012.P012_Identification

/-! P008-T23: equality of toy HAC expressions at cutoffs 2/5 and zero.
P012-T20: refutation of the printed table intervals, including rounding tolerance. -/

namespace AronowAudit.P008.Wave1

open scoped BigOperators
open MeasureTheory Filter

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- P008-T23 helper: separation at 2/5 also excludes every distinct pair at zero. -/
theorem T23_toy_hac_zero (g : Fin 4 → ℝ) :
    hac g (fun i j => dist (toyNode i) (toyNode j)) 0 =
      ∑ i, (g i) ^ 2 := by
  have hsep : ∀ i j : Fin 4, i ≠ j →
      (2 / 5 : ℝ) < dist (toyNode i) (toyNode j) :=
    (toy_cutoff_is_hc0 g).1
  have hzero : ∀ i j : Fin 4, i ≠ j →
      (0 : ℝ) < dist (toyNode i) (toyNode j) := by
    intro i j hij
    exact lt_trans (by norm_num : (0 : ℝ) < 2 / 5) (hsep i j hij)
  exact hac_equals_hc0 g (fun i j => dist (toyNode i) (toyNode j))
    0 le_rfl (fun i => dist_self (toyNode i)) hzero

/-- P008-T23: the reconstructed toy has identical HAC expressions at 2/5 and zero. -/
theorem toy_cutoff_equals_zero (g : Fin 4 → ℝ) :
    (∀ i j : Fin 4, i ≠ j →
      (2 / 5 : ℝ) < dist (toyNode i) (toyNode j)) ∧
    hac g (fun i j => dist (toyNode i) (toyNode j)) (2 / 5) =
      hac g (fun i j => dist (toyNode i) (toyNode j)) 0 ∧
    hac g (fun i j => dist (toyNode i) (toyNode j)) 0 =
      ∑ i, (g i) ^ 2 := by
  obtain ⟨hsep, hcutoff⟩ := toy_cutoff_is_hc0 g
  have hzero := T23_toy_hac_zero g
  exact ⟨hsep, hcutoff.trans hzero.symm, hzero⟩

end

end AronowAudit.P008.Wave1

namespace AronowAudit.P012.Wave1

open Finset
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
set_option linter.unusedVariables false

/-- P012-T20 helper: even the rounding tolerance cannot accommodate the sex lower bound. -/
theorem T20_printed_sex_lower_impossible (D : Data) (hD : Admissible D)
    (hn : D.sampled.card = 527) (hM : D.seeds.card = 6)
    (hd : ∑ i ∈ D.sampled, D.degree i = 4487)
    (L U : ℝ) (hregion : FullHomophilyRegion D L U)
    (hround : |L - (-7027 / 10000)| ≤ 1 / 20000) : False := by
  classical
  obtain ⟨hcompat, _hspare, _hcounts, hdefined, _hvalue, hbound,
      _hint, _hsex, _hcrack, _hhome⟩ := table_counterexample D hD hn hM hd
  have hmem : hValue (leafCompletion D false) ∈ hValues D := by
    refine ⟨leafCompletion D false, hcompat, ?_⟩
    simp only [homophily, if_pos hdefined]
  have hleast : IsLeast (hValues D) L := hregion.2.1
  have hle : L ≤ hValue (leafCompletion D false) := hleast.2 hmem
  have hlower : L ≤ (-1462 / 1983 : ℝ) := le_trans hle hbound
  have hround_lower : -(1 / 20000 : ℝ) ≤ L - (-7027 / 10000) :=
    (abs_le.mp hround).1
  have hgap : (-1462 / 1983 : ℝ) < -7027 / 10000 - 1 / 20000 := by
    norm_num
  linarith only [hlower, hround_lower, hgap]

/-- P012-T20: refutation of the printed pointwise predicate, including its rounding tolerance. -/
theorem printed_table_intervals_refuted
    (Dsex Dcrack Dhome : Data) :
    ¬ printed_table_intervals Dsex Dcrack Dhome := by
  intro hprinted
  rcases hprinted with ⟨hdata, _hshared, hends⟩
  have hsexdata : Admissible Dsex ∧
      Dsex.sampled.card = 527 ∧ Dsex.seeds.card = 6 ∧
      (∑ i ∈ Dsex.sampled, Dsex.degree i) = 4487 :=
    hdata Dsex (by simp)
  rcases hsexdata with ⟨hD, hn, hM, hd⟩
  rcases hends with ⟨Ls, Us, _Lc, _Uc, _Lh, _Uh, hsexregion,
      _hcrackregion, _hhomeregion, hsexround, _hremaining⟩
  exact T20_printed_sex_lower_impossible Dsex hD hn hM hd Ls Us
    hsexregion hsexround

end

end AronowAudit.P012.Wave1
