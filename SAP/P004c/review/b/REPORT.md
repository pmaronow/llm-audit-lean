# Palomar statement audit: P004c

All nine supplied statements are correct on this audit: seven cover their canonical claims and two have accurate, disclosed restrictions. Four further targets are justifiably omitted on the supplied evidence. No statement was found false, vacuous, or unfaithful, and no restriction was found inaccurate.

| Verdict | Count |
| --- | ---: |
| correct_whole | 7 |
| correct_restricted | 2 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 4 |
| omission_questionable | 0 |
| **Total targets** | **13** |

There are no items outside correct_* and omission_ok. All severities are none. No correction is requested.

## Procedure and scope

The definitions and Challenge were read first, including the Mathlib meanings of spatial distance infima, restricted integrals and integrability, Gaussian variance, positive semidefiniteness, matrix inversion, finite maxima, coordinate updates, and deterministic big-O. The blind mathematical expansion was saved in [reading.md](/home/ubuntu/sap/tasks/CHFID-P004c-b/reading.md) before opening claims.json. The nine comparisons were saved in [claim-stage.json](/home/ubuntu/sap/tasks/CHFID-P004c-b/claim-stage.json) before opening record.json. No step-2 verdict changed after reading the record. Later repairs to inline mathematical delimiters in the reading were formatting only.

The theorem-to-target mapping agrees with the record. The seven whole statements are T31, T32, T33, T39, T40, T41, and T42. General real tables and arbitrary metric measurable spaces in positive universal assertions include the paper's cases; they do not narrow these claims. Conversely, a refutation of a universal assertion on a larger class need not refute its restriction to the paper's domain. This distinction matters for the omissions.

This is a statement audit. Only the allowed definitions, Challenge, claims, record, relevant Mathlib sources, and the audit's own scratch files were used. The recorded source declarations and their proofs were not independently inspected. Omission judgments therefore concern the logical adequacy of the supplied record and canonical claims, not unseen source bodies. No web search was needed.

## Accepted restrictions

**T34.** [Challenge/Part1.lean:28](/home/ubuntu/sap/tasks/CHFID-P004c-b/SAP/P004c/Challenge/Part1.lean:28) explicitly omits both the composed bandwidth rate

\[
 O_p(N^{-1/2}b_N^2)=o_p(1)
\]

and a certified eight-node assignment, arm-centered residuals, and kernel realizing \(S=-1/4\). The theorem retains the finite identities, finite kernel bound, denominator rate, and scalar arithmetic. Scalar arithmetic alone is not a refutation of the printed kernel inequality; the docstring makes that limitation clear. Positive sample size and bandwidth and the zero extension of the denominator error on empty treated arms are also disclosed. The retained scalar calculation is correct.

**T44.** [Challenge/Part1.lean:61](/home/ubuntu/sap/tasks/CHFID-P004c-b/SAP/P004c/Challenge/Part1.lean:61) explicitly replaces the printed radiuswise-eventual \(C_b s^2\) condition with \(C_b(1+s^2)\) and one eventual sample-size threshold valid for every radius. Repairing the zero-radius bound is necessary because a node belongs to its own ball. Requiring a common threshold for all radii is a substantive additional premise, correctly disclosed rather than presented as the original quantifier order. Finite unbiasedness, the HT variance rate, the root-\(N\) approximation, and the nondegenerate Hajek normal limit all remain in the theorem.

The retained NED conclusions are mathematically credible under these stronger hypotheses. For example, with NED exponent \(q>4\), truncate conditional expectations at \(s_N=N^a\), where \(1/(2q)<a<1/8\). The normalized sum's crude \(L^2\) approximation error is \(O(\sqrt N\,s_N^{-q})=o(1)\); uniform quadratic spacing and the metric give a dependency graph of degree \(O(s_N^2)\) for the bounded truncated summands. The bounded-summand dependency-graph normal approximation has error controlled by \(s_N^4/\sqrt N=o(1)\). No normal-limit conclusion is assumed as a hypothesis.

## Accepted omissions

| Target | Why omission is justified on the supplied evidence |
| --- | --- |
| T35 | The recorded negative rows concern arbitrary metric measurable spaces and export no witness in the canonical two-dimensional spatial domain. A larger-domain negation alone is insufficient. No positive component of the printed logistic-IPW proposition is supplied by those rows. |
| T36 | The canonical printed numerator is Hajek; the available row concerns fitted IPW. Refuting the latter does not refute the former. Fourth-power variance algebra alone establishes neither coverage assertion. |
| T37 | A negated identity over arbitrary real tables and positive weights does not supply a binary spatial potential-outcome field and ordered distance-bin partition. The record exports no such realization. This omission does not endorse the printed area interpretation. |
| T43 | Finite oracle bounds do not establish coverage or existence of the printed ordinary limits. The recorded negative row also lacks an exported canonical-domain witness. A liminf lower bound would be a different assertion requiring disclosure. |

## Nonvacuity and verification

[scratch/Nonvacuity.lean](/home/ubuntu/sap/tasks/CHFID-P004c-b/scratch/Nonvacuity.lean) compiled successfully with the command

    /home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean

It imports only the SAP definitions and their Mathlib dependencies, contains no sorry, and does not invoke a Challenge theorem. It checks a two-node table

\[
 R_i(z)=(-1)^i+z_i,\qquad p=\tfrac12,\qquad B_i=\{i\},
\]

with two nonempty arms in a mixed assignment, symmetric center-containing neighborhoods, no shared sources outside those neighborhoods, strictly bounded outcomes, \(E[\mathrm{HT}]=1\), \(\operatorname{Var}(\mathrm{HT})=5/2\), and \(\operatorname{Var}(L)=2\). It also constructs a spatial population with a positive finite Dirac-measured region, proves WellDefined, and evaluates the actual SAP circle integral to the nonzero-effect outcome \(z_0\). Thus neither inconsistent premises nor zeroed nonintegrable integrals explain these examples.

A single sequence also satisfies all the asymptotic hypotheses, including both nondegeneracy requirements, in the paper's two-dimensional domain. For every \(N\), take \(X_N=\mathbb R^2\) with the Euclidean metric and Borel measurable sets, nodes

\[
 x_i=(i,0),\quad 0\le i<N,\qquad
 \zeta_N=\sum_{i<N}\delta_{x_i},\qquad
 \Omega_d=[0,d]\quad(d\ge0),
\]

and the common potential-outcome field

\[
 Y_N(x,z)=\cos(\pi x_1)+\sum_{i<N}z_i\,1_{\{x_i\}}(x).
\]

At most one indicator is nonzero at any point, so \(|Y_N(x,z)|\le2<3\). Every nonnegative-radius disk region contains its center, is measurable, and has positive finite measure; every potential outcome is integrable on it. A radius-\(d\) circle table depends only on assignments within distance \(d\), so \(h(d)=2d\) ensures no shared source beyond the cutoff. The ball count is at most \(2\lfloor r\rfloor+1\le2r+1\), giving C4 and, simultaneously for all \(r\ge0\),

\[
 |B(i;r)|\le2r+1\le2(1+r^2).
\]

For the tested radius \(d=0\), \(R_i(z)=c_i+z_i\), \(c_i=(-1)^i\), and \(\mathrm{AME}=1\). With independent Bernoulli-\(1/2\) assignments,

\[
 N\operatorname{Var}(\mathrm{HT})
   =5+\frac4N\sum_{i<N}c_i\ge5,\qquad
 N\operatorname{Var}(L)=4(1-\bar c_N^2)\ge\frac{32}{9}
 \quad(N\ge2).
\]

The NED conditional expectation equals \(R_i\) for every \(s\ge0\), since the conditioning ball contains its own coordinate. Therefore \(\psi=0\), \(g_{N,i}=G=1\), any decay exponent \(q>4\), and \(C_b=2\) satisfy T44's strengthened premises. This sequence has actual treatment effects and positive sampling variance. It verifies joint satisfiability analytically; the entire asymptotic construction was not formalized in the scratch file.

[scratch/check_finite.py](/home/ubuntu/sap/tasks/CHFID-P004c-b/scratch/check_finite.py) independently enumerates assignments with exact rational arithmetic; [scratch/finite-results.json](/home/ubuntu/sap/tasks/CHFID-P004c-b/scratch/finite-results.json) records all nine passing cases. These checks include nonlinear neighbor interference for \(N=2,3,4,5\) at \(p=1/2,2/5\), the HT and linearized variance expansions, corrected finite bounds, forced-coordinate unbiasedness, and homophily identities. A three-node example has homophily \(-2/3\), variance \(2/3\), and second-moment expression \(4/9\): the C5 equivalence correctly detects failure of the bound. The script also independently realizes the eight-node scalar witness omitted from T34; this audit calculation does not expand what its theorem certifies.

The asymptotic definitions use ordinary tail probabilities and the actual standard Gaussian CDF. Conditional denominators are positive for the stipulated interior probabilities. Pair-conditionals occur only off the diagonal. Spatial denominators have positive finite measure and their numerators are integrable at the tested radius. Degree-minus-one is real subtraction, not truncated natural subtraction. There is no unbounded limsup or empty index type supplying a conclusion.

All JSON output files were parsed and checked with Python, including exact coverage of the thirteen target IDs.
