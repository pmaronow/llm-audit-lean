/-
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import AronowAudit.External.Causalean.Experimentation.DesignBased.Risk

/-!
# Treatment indicator for Boolean assignments

The treatment indicator is one when the Boolean assignment treats the unit and zero otherwise.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

section Group

variable {n : ℕ}

/-- For [a population of `n` units](hyp:n) and [a unit](hyp:j), the [treatment indicator](goal)
is one when the Boolean assignment treats that unit and zero otherwise. -/
noncomputable def T (j : Fin n) : (Fin n → Bool) → ℝ :=
  FiniteDesign.ind (fun w => w j = true)


variable (K : ℕ) (a b : Fin n → ℝ)


end Group

end DesignBased
end Experimentation
end Causalean
