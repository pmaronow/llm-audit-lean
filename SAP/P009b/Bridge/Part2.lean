import SAP.P009b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Bridge

theorem T27Minimizer_transport (h : type_of% @AronowAudit.P009.corrected_three_point_minimizer) :
    T27MinimizerStatement := by
  intro S k q s α hReg hBER hα b hb hbInfinity f hf hmin
  exact h (toStudy S) k q s α hReg hBER hα b hb hbInfinity f hf hmin

theorem T28Finite_transport (h : type_of% @AronowAudit.P009.three_point_centering.{u}) :
    T28FiniteStatement.{u} := by
  intro Ω inst P F hF x hx hshift
  exact h (toLaw P) F hF x hx hshift

theorem T28Eventual_transport (h : type_of% @AronowAudit.P009.centering_shift_eventually) :
    T28EventualStatement := by
  exact h

theorem T29Core_transport (h : type_of% @AronowAudit.P009.corrected_moment_covariance) :
    T29CoreStatement := by
  intro n E k q hk hq hMoment a hqa i j b
  exact h (toExperiment E) k q hk hq hMoment a hqa i j b

theorem T30Core_transport (h : type_of% @AronowAudit.P009.corrected_inflated_estimator_names) :
    T30CoreStatement := by
  intro n hn E hOverlap z
  exact h (toExperiment E) z

theorem T31Finite_transport (h : type_of% @AronowAudit.P009.corrected_three_point_CDF) :
    T31FiniteStatement := by
  exact h

theorem T31Limit_transport (h : type_of% @AronowAudit.P009.three_point_CDF_limit.{u}) :
    T31LimitStatement.{u} := by
  intro Ω inst P F hF α hα hminus hplus
  exact h Ω (fun t => toLaw (P t)) F hF α hα hminus hplus

theorem T32Update_transport (h : type_of% @AronowAudit.P009.balance_update) :
    T32UpdateStatement := by
  exact h

theorem T32Crossings_transport (h : type_of% @AronowAudit.P009.multiplier_crossings) :
    T32CrossingsStatement := by
  exact h

theorem T32Paired_transport (h : type_of% @AronowAudit.P009.balance_paired_flip) :
    T32PairedStatement := by
  exact h

theorem T33Core_transport (h : type_of% @AronowAudit.P009.corrected_one_source_spillover) :
    T33CoreStatement := by
  exact h

theorem T34Core_transport (h : type_of% @AronowAudit.P009.corrected_paired_bias_bound) :
    T34CoreStatement := by
  intro n hn E ρ hPair k q s hReg
  exact h hn (toExperiment E) (toPairing ρ) hPair k q s hReg

end Bridge

end
end SAP.P009b
