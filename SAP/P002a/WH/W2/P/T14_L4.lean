import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P002a.WH.W2.P.T14_L4

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

lemma probability_mono {n : ℕ} (P : Population n) (E F : Finset (Fin n) → Prop)
    (hEF : ∀ T ∈ assignments P, E T → F T) : probability P E ≤ probability P F := by
  unfold probability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (by
    intro T hT
    rcases Finset.mem_filter.mp hT with ⟨hTA, hE⟩
    exact Finset.mem_filter.mpr ⟨hTA, hEF T hTA hE⟩)

lemma q_sq_markov {m : ℕ} (hm : 2 ≤ m) (hfinite : W2T14Finite)
    (t : ℝ) (ht : 0 < t) :
    probability (signModel m) (fun T => t ≤ W2q m T ^ 2) ≤
      (1 / ((2*m : ℕ) - (1 : ℝ))) / t := by
  have hmark := AronowAudit.P002.Wave1.DecisionLemma12_markov (toPopulation (signModel m))
    (fun T => t ≤ W2q m T ^ 2) (fun T => W2q m T ^ 2) t
    (fun _ _ => sq_nonneg _) (fun _ _ h => h)
  have hmark' : t * probability (signModel m) (fun T => t ≤ W2q m T ^ 2) ≤
      expectation (signModel m) (fun T => W2q m T ^ 2) := by
    simpa only [SAP.P002a.Bridge.probability_eq, SAP.P002a.Bridge.expectation_eq] using hmark
  have hexp := (hfinite m hm).2.1
  rw [hexp] at hmark'
  exact (le_div_iff₀ ht).2 (by simpa [mul_comm] using hmark')

lemma inv_size_tendsto (ms : ℕ → ℕ) (hms : StrictMono ms) :
    Tendsto (fun j => 1 / (ms j : ℝ)) atTop (nhds 0) := by
  have htop : Tendsto (fun j => (ms j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hms.tendsto_atTop
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp htop

lemma q_sq_tail_bound {m : ℕ} (hm : 2 ≤ m) (hfinite : W2T14Finite)
    (t : ℝ) (ht : 0 < t) :
    probability (signModel m) (fun T => t ≤ W2q m T ^ 2) ≤
      (1/t) * (1/(m : ℝ)) := by
  have hq := q_sq_markov hm hfinite t ht
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < (2*m : ℕ) - 1 := by
    have : (4 : ℝ) ≤ (2*m : ℕ) := by exact_mod_cast (show 4 ≤ 2*m by omega)
    linarith
  have hden : (m : ℝ) ≤ ((2*m : ℕ) : ℝ) - 1 := by
    have hdenNat : m+1 ≤ 2*m := by omega
    have hcast : (m : ℝ)+1 ≤ (2*m : ℕ) := by exact_mod_cast hdenNat
    linarith
  have hrec : 1 / ((2*m : ℕ) - 1) ≤ 1 / (m : ℝ) :=
    one_div_le_one_div_of_le hmR hden
  calc
    _ ≤ (1 / ((2*m : ℕ) - (1 : ℝ))) / t := hq
    _ ≤ (1 / (m : ℝ)) / t := div_le_div_of_nonneg_right hrec ht.le
    _ = (1/t) * (1/(m : ℝ)) := by ring

lemma normalized_error_bound {m : ℕ} (hm : 2 ≤ m) (hfinite : W2T14Finite)
    (T : Finset (Fin (2*m))) (hT : T ∈ assignments (signModel m)) :
    |W2U m T / Real.sqrt (2*m : ℕ)-2| ≤
      2 / ((2*m : ℕ) : ℝ) + 2*W2q m T^2 := by
  let N : ℝ := ((2*m : ℕ) : ℝ)
  let x : ℝ := W2q m T^2
  have hN : 0 < N := by dsimp [N]; positivity
  have hNm : 0 < N-1 := by
    dsimp [N]
    have hm4 : 4 ≤ 2*m := by omega
    have hm4R : (4 : ℝ) ≤ (2*m : ℕ) := by exact_mod_cast hm4
    linarith
  rcases hfinite m hm with ⟨_, _, _, hforall, _⟩
  rcases hforall T hT with ⟨_, _, hU, hR, _, _, hRlo, _⟩
  have hRmul : W2R m T * N = (N-1)*(1-x) := by
    rw [hR]
    dsimp [N, x]
    field_simp
  have hprod : 0 ≤ (N-1)*(1-x) := by
    rw [← hRmul]
    exact mul_nonneg hRlo hN.le
  have hx : x ≤ 1 := by
    have hy := (mul_nonneg_iff_of_pos_left hNm).mp hprod
    dsimp [x] at hy ⊢
    linarith
  let s : ℝ := Real.sqrt (1-x)
  let c : ℝ := (N-1)/N
  have hx0 : 0 ≤ x := by positivity
  have h1x : 0 ≤ 1-x := by linarith
  have hs0 : 0 ≤ s := by dsimp [s]; exact Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by
    dsimp [s]
    apply Real.sqrt_le_one.mpr
    linarith
  have hslo : 1-x ≤ s := by
    dsimp [s]
    apply (Real.le_sqrt h1x h1x).2
    nlinarith [mul_nonneg h1x hx0]
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (by linarith) hN.le
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_iff₀ hN).2
    linarith
  have hnorm : W2U m T / Real.sqrt (2*m : ℕ) = 2*c*s := by
    rw [hU]
    dsimp [N, c, s]
    have hsqrtne : Real.sqrt ((2*m : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
    field_simp [hsqrtne]
    rw [Real.sq_sqrt hN.le]
    ring
  have hcid : 1-c = 1/N := by
    dsimp [c]
    field_simp [ne_of_gt hN]
    ring
  have hscomp : 0 ≤ 1-s := by linarith
  have hprod2 : c*(1-s) ≤ 1-s := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hscomp
  have herr : 1-c*s ≤ 1/N+x := by
    have hdecomp : 1-c*s = (1-c)+c*(1-s) := by ring
    rw [hdecomp, hcid]
    linarith
  have hcs : c*s ≤ 1 := by
    calc
      c*s ≤ 1*s := mul_le_mul_of_nonneg_right hc1 hs0
      _ ≤ 1 := by simpa using hs1
  rw [hnorm]
  have herr2 := mul_le_mul_of_nonneg_left herr (by norm_num : (0:ℝ) ≤ 2)
  calc
    |2*c*s-2| = 2*(1-c*s) := by
      rw [abs_of_nonpos (by nlinarith [hcs])]
      ring
    _ ≤ 2*(1/N+x) := herr2
    _ = 2/N+2*x := by ring

lemma deficit_tail_bound {m : ℕ} (hm : 2 ≤ m) (hfinite : W2T14Finite)
    (κ : ℝ) (hκ : 0 < κ) :
    probability (signModel m) (fun T => κ ≤ 1-W2R m T) ≤
      (1/κ)*(1/(m : ℝ)) := by
  rcases hfinite m hm with ⟨_, _, _, hall, hdef⟩
  have hmark := AronowAudit.P002.Wave1.DecisionLemma12_markov
    (toPopulation (signModel m)) (fun T => κ ≤ 1-W2R m T)
    (fun T => 1-W2R m T) κ
    (fun T hT => by
      rcases hall T hT with ⟨_, _, _, _, _, _, _, hhi⟩
      linarith)
    (fun _ _ h => h)
  have hmark' : κ*probability (signModel m) (fun T => κ ≤ 1-W2R m T) ≤
      expectation (signModel m) (fun T => 1-W2R m T) := by
    simpa only [SAP.P002a.Bridge.probability_eq, SAP.P002a.Bridge.expectation_eq] using hmark
  rw [hdef] at hmark'
  have hprob : probability (signModel m) (fun T => κ ≤ 1-W2R m T) ≤
      (2/((2*m : ℕ) : ℝ))/κ :=
    (le_div_iff₀ hκ).2 (by simpa [mul_comm] using hmark')
  have hmR : (m : ℝ) ≠ 0 := by
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    exact hmpos.ne'
  have hcast : ((2*m : ℕ) : ℝ) = 2*(m : ℝ) := by norm_num
  calc
    _ ≤ (2/((2*m : ℕ) : ℝ))/κ := hprob
    _ = (1/κ)*(1/(m : ℝ)) := by rw [hcast]; field_simp [hmR, hκ.ne']

end
end SAP.P002a.WH.W2.P.T14_L4

open Filter MeasureTheory SAP.P002a SAP.P002a.WH.W2 SAP.P002a.Bridge AronowAudit.P002 SAP.P002a.WH.W2.P.T14_L4
open scoped BigOperators ENNReal Matrix Classical Topology
attribute [local instance] Classical.propDecidable

theorem SAP.P002a.WH.W2.T14_L4_proof : SAP.P002a.WH.W2.T14_L4 := by
  intro hfinite ms hms hlarge
  let N : ℕ → ℝ := fun j => 2*(ms j : ℝ)
  have hms2 : StrictMono (fun j => 2*ms j) := by
    intro a b hab
    exact Nat.mul_lt_mul_of_pos_left (hms hab) (by omega)
  have hMtop : Tendsto (fun j => (ms j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hms.tendsto_atTop
  have hN : Tendsto N atTop atTop := by
    simpa [N] using hMtop.const_mul_atTop (by norm_num : (0:ℝ) < 2)
  have hinv := inv_size_tendsto ms hms
  have hvalid (m : ℕ) (hm : 2 ≤ m) : ValidDesign (signModel m) := by
    dsimp [ValidDesign, signModel]
    omega
  have hprobCompl (m : ℕ) (hm : 2 ≤ m) (E : Finset (Fin (2*m)) → Prop) :
      probability (signModel m) E +
        probability (signModel m) (fun T => ¬ E T) = 1 := by
    have hv := hvalid m hm
    have hv' : AronowAudit.P002.ValidDesign (toPopulation (signModel m)) := by
      simpa only [SAP.P002a.Bridge.validDesign_eq] using hv
    have hd := AronowAudit.P002.Wave1.T2C_probability_complement
      (toPopulation (signModel m)) hv' E
    simpa only [SAP.P002a.Bridge.probability_eq] using hd
  have hprobNonneg (m : ℕ) (E : Finset (Fin (2*m)) → Prop) :
      0 ≤ probability (signModel m) E := by
    have hd := AronowAudit.P002.Wave1.DecisionLemma12_probability_nonneg
      (toPopulation (signModel m)) E
    simpa only [SAP.P002a.Bridge.probability_eq] using hd
  have hprobLeOne (m : ℕ) (hm : 2 ≤ m) (E : Finset (Fin (2*m)) → Prop) :
      probability (signModel m) E ≤ 1 := by
    have hv := hvalid m hm
    have hv' : AronowAudit.P002.ValidDesign (toPopulation (signModel m)) := by
      simpa only [SAP.P002a.Bridge.validDesign_eq] using hv
    have hd := AronowAudit.P002.Wave1.DecisionLemma12_probability_le_one
      (toPopulation (signModel m)) hv' E
    simpa only [SAP.P002a.Bridge.probability_eq] using hd
  have hfirst : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun j => probability (signModel (ms j))
        (fun T => |W2U (ms j) T / Real.sqrt (2*ms j : ℕ)-2| ≥ ε))
        atTop (nhds 0) := by
    intro ε hε
    have hbound : Tendsto (fun j => (6/ε)*(1/(ms j : ℝ)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hinv
    apply squeeze_zero
      (fun j => hprobNonneg (ms j) _)
      _ hbound
    intro j
    have hmj := hlarge j
    by_cases hsmall : 2 / N j ≤ ε/2
    · have hincl : ∀ T ∈ assignments (signModel (ms j)),
          |W2U (ms j) T / Real.sqrt (2*ms j : ℕ)-2| ≥ ε →
            ε/4 ≤ W2q (ms j) T ^ 2 := by
        intro T hT htail
        have hb := normalized_error_bound hmj hfinite T hT
        have hNcast : ((2*ms j : ℕ) : ℝ) = N j := by simp [N]
        rw [← hNcast] at hsmall
        linarith
      calc
        _ ≤ probability (signModel (ms j)) (fun T => ε/4 ≤ W2q (ms j) T ^ 2) :=
          probability_mono _ _ _ hincl
        _ ≤ (1/(ε/4))*(1/(ms j : ℝ)) :=
          q_sq_tail_bound hmj hfinite (ε/4) (by linarith)
        _ ≤ (6/ε)*(1/(ms j : ℝ)) := by
          have hmpos : 0 < (ms j : ℝ) := by exact_mod_cast (show 0 < ms j by omega)
          have hcoef : 1/(ε/4) ≤ 6/ε := by
            rw [show 1/(ε/4) = 4/ε by field_simp]
            exact div_le_div_of_nonneg_right (by norm_num : (4:ℝ) ≤ 6) (by positivity)
          exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    · have hNpos : 0 < N j := by positivity
      have hNeq : 2/N j = 1/(ms j : ℝ) := by
        have hmpos : (ms j : ℝ) ≠ 0 := by
          exact (by exact_mod_cast (show 0 < ms j by omega) : 0 < (ms j : ℝ)).ne'
        dsimp [N]
        field_simp [hmpos]
      have hrec : ε/2 < 1/(ms j : ℝ) := by rw [← hNeq]; exact lt_of_not_ge hsmall
      have hmpos : 0 < (ms j : ℝ) := by exact_mod_cast (show 0 < ms j by omega)
      have hfactor : 0 < 2/ε := by positivity
      have hlarge' := mul_lt_mul_of_pos_left hrec hfactor
      have hprod : 1 < (2/ε)*(1/(ms j : ℝ)) := by
        have heq : (2/ε)*(ε/2) = 1 := by field_simp
        rw [heq] at hlarge'
        exact hlarge'
      have hcoef : (2/ε)*(1/(ms j : ℝ)) ≤ (6/ε)*(1/(ms j : ℝ)) := by
        have hcoef' : 2/ε ≤ 6/ε :=
          div_le_div_of_nonneg_right (by norm_num : (2:ℝ) ≤ 6) (by positivity)
        exact mul_le_mul_of_nonneg_right hcoef' (by positivity)
      calc
        _ ≤ 1 := hprobLeOne (ms j) hmj _
        _ ≤ (2/ε)*(1/(ms j : ℝ)) := le_of_lt hprod
        _ ≤ (6/ε)*(1/(ms j : ℝ)) := hcoef
  have hsecond : ∀ M : ℝ, Tendsto (fun j => probability (signModel (ms j))
      (fun T => M < W2U (ms j) T)) atTop (nhds 1) := by
    intro M
    have hbad := hfirst 1 (by norm_num)
    have hlow : Tendsto (fun j => 1-probability (signModel (ms j))
        (fun T => |W2U (ms j) T/Real.sqrt (2*ms j : ℕ)-2| ≥ 1))
        atTop (nhds 1) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hbad
    have hroot : Tendsto (fun j => Real.sqrt (N j)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hN
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    · filter_upwards [hroot.eventually_gt_atTop M] with j hjroot
      have hmj := hlarge j
      have hcompl := hprobCompl (ms j) hmj (fun T => M < W2U (ms j) T)
      have hnotle : probability (signModel (ms j))
          (fun T => ¬ M < W2U (ms j) T) ≤
          probability (signModel (ms j))
            (fun T => |W2U (ms j) T/Real.sqrt (2*ms j : ℕ)-2| ≥ 1) := by
        apply probability_mono
        intro T hT hnot
        have hu : W2U (ms j) T ≤ M := le_of_not_gt hnot
        have hNpos : 0 < N j := by positivity
        have hrootpos : 0 < Real.sqrt (N j) := Real.sqrt_pos.mpr hNpos
        have hratio : W2U (ms j) T / Real.sqrt (N j) ≤ M / Real.sqrt (N j) :=
          div_le_div_of_nonneg_right hu hrootpos.le
        have hjroot' : M < 1 * Real.sqrt (N j) := by simpa using hjroot
        have hratioM : M / Real.sqrt (N j) < 1 := (div_lt_iff₀ hrootpos).2 hjroot' 
        have hnorm : W2U (ms j) T / Real.sqrt (N j) < 1 := hratio.trans_lt hratioM
        have hbadpt : 1 ≤ |W2U (ms j) T / Real.sqrt (N j)-2| := by
          have hdiff : W2U (ms j) T / Real.sqrt (N j)-2 ≤ 0 := by linarith
          rw [abs_of_nonpos hdiff]
          linarith
        have hNcast : ((2*ms j : ℕ) : ℝ) = N j := by simp [N]
        rw [← hNcast] at hbadpt
        exact hbadpt
      have hp := hcompl
      linarith
    · exact Eventually.of_forall (fun j => hprobLeOne (ms j) (hlarge j) _)
  have hthird : ∀ κ : ℝ, 0 < κ →
      Tendsto (fun j => probability (signModel (ms j))
        (fun T => |W2R (ms j) T-1| ≥ κ)) atTop (nhds 0) := by
    intro κ hκ
    have hbound : Tendsto (fun j => (1/κ)*(1/(ms j : ℝ)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hinv
    apply squeeze_zero
      (fun j => hprobNonneg (ms j) _)
      _ hbound
    intro j
    have hmj := hlarge j
    have htail : probability (signModel (ms j))
        (fun T => |W2R (ms j) T-1| ≥ κ) ≤
        probability (signModel (ms j)) (fun T => κ ≤ 1-W2R (ms j) T) := by
      apply probability_mono
      intro T hT he
      rcases hfinite (ms j) hmj with ⟨_, _, _, hall, _⟩
      rcases hall T hT with ⟨_, _, _, hR, _, _, _, hRhi⟩
      rw [abs_of_nonpos (by linarith)] at he
      have hEq : -(W2R (ms j) T-1) = 1-W2R (ms j) T := by ring
      rw [hEq] at he
      exact he
    exact htail.trans (deficit_tail_bound hmj hfinite κ hκ)
  exact ⟨hfirst, hsecond, hthird⟩
