import AronowAudit.P018.Wave1.Gap.TailBSignExtra
import AronowAudit.P018.Wave1.Gap.TailBSignInference

/-! P018-T7: the exact bounded-sign degenerate-inference counterexample. -/

namespace AronowAudit.P018.Wave1
open TailBSign

theorem TailB_degenerate_inference_counterexample :
    type_of% @AronowAudit.P018.degenerate_inference_counterexample := by
  exact ⟨tb05_standing, tb05_proposition_extra, tb05_population_gram, tb05_population_beta,
    tb05_projection_gamma, tb05_limiting_target, fun N hN => tb05_true_target hN,
    tb05_negative_variance_probability, tb05_pivot_not_normal, tb05_absolute_consistency⟩

example : type_of% @AronowAudit.P018.degenerate_inference_counterexample :=
  AronowAudit.P018.Wave1.TailB_degenerate_inference_counterexample

end AronowAudit.P018.Wave1
