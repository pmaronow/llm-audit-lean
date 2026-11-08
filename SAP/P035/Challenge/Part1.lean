import SAP.P035.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P035-T1; Abstract Conclusions, p. 2/6, and Results and conclusions, p. 5/6.
The validator's two finite worlds reproduce all six frequencies and every
observed choice, but have the specified zero versus positive campaign effects,
so the observed law does not identify the campaign effect.
This is a witness about identification, not a decision about the initiative's
actual effect; its overall mixture uses raw enrollment shares. -/
theorem SAP.P035.T1 : SAP.P035.T1Statement := by sorry

/-- P035-T2; corrected Abstract Conclusions, p. 2/6, and campaign wording, p. 5/6.
Two calibrated models with the same observed law have zero versus positive
campaign effects, and full campaign enablement of the porch contrast is possible.
Restricted to mathematical clauses (a)-(b): this does not assert the retained
empirical estimate that porch assignment increased raisin choice, and it does
not formalize the instruction to replace the campaign wording on p. 5/6.
The counterfactual is initiative presence, with no separate health-message
mediator. -/
theorem SAP.P035.T2 : SAP.P035.T2Statement := by sorry
