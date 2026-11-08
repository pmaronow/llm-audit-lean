import SAP.P013b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P013-T20; Proposition 3.1, p. 1917 (PDF p. 6), Appendix A.1, p. 1938 (PDF p. 27).
On a fixed finite population, an infinite sequence of mutually independent
replicate assignments, each drawn from the exact design law, gives almost surely,
simultaneously for every exposure `d_k` and every entry, convergence of the
smoothed same-exposure matrix `(Î_kÎ_k' + ι_N)/(R+1)` to `I_kPI_k'` and, for every
exposure `d_l ≠ d_k`, of the cross-exposure matrix `Î_kÎ_l'/R` to `I_kPI_l'`.
Both limits hold on one probability-one event for every exposure and entry,
including the same-exposure limit when there is only one exposure. The usual
measure-theoretic conditions are assumed: measurable replicates on a probability
space and measurable singletons in the finite assignment space. The zero-replicate
cross ratio has no effect on the limit; its denominator is positive for every R ≥ 1. -/
theorem SAP.P013b.T20 : SAP.P013b.T20Statement := by sorry
