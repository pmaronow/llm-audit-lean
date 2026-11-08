All four declarations are faithful, with severity `none`. The record's four
`whole` decisions are correct, and the docstrings describe their statements
accurately. No step-2 conclusion changed after reading the record.

The blind reading, including every dependency and relevant totalization, was
saved in `reading.md` before opening the canonical claims. The comparison was
then saved in `claim-stage.json` before opening `record.json`. Audit-history
notes and unused support rows supplied no additional premises or exceptions.

**T7.** The printed proof step attempts to define the ordinary noncomplier
mean and divide by `1-Pc` under Section 2 without assuming `Pc<1`. Its conditions
are random assignment, exclusion, monotonicity, nonzero first stage, bounded
outcomes and positive assignment arms. The constant potential vector is
independent of the fair assignment; exclusion is encoded; `(D0,D1)=(0,1)` is
monotone with first stage one; potentials are `(0,1)`; and both arms have mass
one half. The witness therefore satisfies every condition. It establishes
null conditioning events, zero proof denominators and numerators, and the
undetermined mixture parameter while retaining valid singleton intervals.
It neither assigns an ordinary mean to a null event nor refutes the
proposition or the corollary's ordinary premise. The `whole` label correctly
describes this canonical witness.

**T8.** The three strata encode exactly the monotone binary treatment pairs.
All four endpoints match the printed formulas. The theorem gives universal
validity and genuine model attainment of every coordinate value at every
compatible triple, including full compliance. Sharpness preserves precisely
the three reported numbers. It does not incorrectly preserve the entire
observed law or let the two complier means vary independently.

**T9.** The canonical definitions require all four ordinary cell means to
exist. Positive cells therefore express the claim's own premise. The theorem
reconstructs the arm means, complier probability, noncomplier ratio and both
complier means from the eight summaries, and gives identification across
models. It assumes only the observed moments needed, with no integrability
requirement on unused counterfactuals.

**T10.** Finite observed arm moments suffice for the reduced form and both
LATE ratios; the theorem derives the complier moments. Its sample clause
defines measurable sample analogues and proves the Wald/centered-IV identity
with valid denominators. No sampling law or convergence claim is inferred.
The two bounded models genuinely show that the three figures alone do not
identify the levels, without claiming failure of identification at every
possible triple.

`scratch/Nonvacuity.lean` independently constructs and verifies the instances
described in `findings.json`, using only the definitions and Mathlib, with no
Challenge theorem or `sorry`. The final compilation with
`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` exited successfully
with no diagnostics; `scratch/Nonvacuity.log` is empty. No unguarded junk value
affects an ordinary population mean or IV identity. The sample statistic's
totalized values on degenerate samples are explicitly distinguished from
the ordinary-ratio assertion.
