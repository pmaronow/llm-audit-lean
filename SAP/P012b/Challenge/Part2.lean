import SAP.P012b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P012-T24; Web Appendix 1, p. 2, display (1); set-up on p. 1.
The objective is positive and has attained scalar maximum 1/epsilon on the square,
and its value at any ordinary binary graph correlation is positive and bounded by 1/epsilon.
Restriction: Retains only display (1)'s positive scalar objective bound and sharp maximum 1/epsilon on [-1,1]^2, attained at (-1,0), and the resulting objective and homophily range estimates for finite simple binary-trait graphs with positive all-vertex degree totals in both trait classes. Omits annealing convergence, certification of the printed proposals and cooling schedule, all communication-depth assertions (including existence of D*, its bound by the compatible-space maximum and D*epsilon<=1), existence or attainment of a maximum on an arbitrary compatible space, the cited convergence implication, and display (2)'s divergence assertion for D*. The graph estimate evaluates the inactive second argument at zero; it asserts no defined preferential recruitment value or attainment of 1/epsilon by a compatible graph. -/
theorem SAP.P012b.T24 : SAP.P012b.T24Statement := by sorry
