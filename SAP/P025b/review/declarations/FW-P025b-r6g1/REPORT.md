All five declarations are faithful, with severity `none`. Each `whole` decision
in `record.json` is justified. No claim-stage conclusion changed after reading
the record. Both earlier T16 documentation issues are fixed.

`reading.md` was saved before opening claims or review history. I read every
closure declaration, including the generated declarations printed in
`scratch/ClosurePrint.log`. `claim-stage.json` records the independent comparison
with the canonical statements, definitions, and standing assumptions.

For T12, the printed reading tested is: under the allowed probability bounds,
a nonpositive adjacent threshold increment implies the next-outcome inequality,
the two least stopping indices agree, and the Supplement's strict-comparison
equivalences hold. Its conditions and witness checks are:

- A nonempty, ordered finite sample: the census has two observations, 0<1.
- Bounds 0<α≤πᵢ≤β≤1 and γ≥1: α=β=πᵢ=γ=1 is allowed.
- Threshold indices in their defined ranges: the failed implication uses k=0,
  the stopping rules range over {0,1}, and the last threshold vector uses k=2.
- Distinct nonempty outcome classes and positive denominators: both classes
  are singletons with total 1, and every objective denominator is 2.

The current theorem states the failed implication, both least indices, both
failed equivalences, and the preserved singleton box, optimizers, and endpoints.
It agrees with the canonical counterexample, so `whole` is correct.

For T13, the statement includes both almost-sure convergences without separation
and the implication with separation over exactly the valid finite index range.
It explicitly supplies eventual pooled nonemptiness. A finite outcome type adds
no design restriction: any sampling design on a finite population induces a law
on its finite set of subsets. The countable product gives the required iid
replication and permits arbitrary dependence within each sample. The canonical
`finite_lemmas` describe proof steps rather than additional target clauses.

For T14, the printed reading tested is: Assumption 2 is necessary for convergence
under independent Brewer replication. The witness satisfies every relevant
condition: six units with real outcomes (0,0,2,2,3,3); valid bounds
α=1/4≤πᵢ=1/2≤β=1/2; independent fair choices within all three pairs;
independent replicate draws with those same marginals; and nonempty pooled
samples for every positive h. Separation fails at k=1. All pooled endpoints
nevertheless equal 5/4 and 2. The theorem also states every polynomial
certificate, specified optimizer evaluation, class-weight formula, normalization,
and onto-box assertion in the canonical counterexample.

For T15, the explicit compatible-population existence premise is canonical,
including its rational-share qualification at γ=1. Positive integer counts,
positive scaling, and unrestricted size correctly define shares-only
compatibility. The statement covers sharp infimum/supremum, the complete
proportion region and its rational population points, endpoint attainment,
actual design realization, integer calibration and outer bounds with richer
information. Concrete failures cover both retained totals and retained size.
The limiting shares are given data here; this target does not require a separate
convergence theorem.

For T16, the reading tested is: retaining absolute class totals, and also size
in the second example, leaves the continuous box endpoints sharp. Conditions
are finite populations with exactly the stated outcome classes, fixed valid
probability bounds, class totals supplied by genuine designs, independent
replication, and positive integer class sizes; example B also fixes N=1000.
The omit-one design supplies example A with all πᵢ=2/3 and satisfies
separation. Example B uses independent uniform quota draws of 50 zeros and
100 ones for every admissible integer class size. Both quota spaces are
nonempty, their marginal probabilities satisfy the bounds, and replication is
iid. Thus both witnesses satisfy the specified reading. The exact compatible
mean sets and strict gaps are asserted, together with the four optimizer
evaluations and the preserved outer bounds and shares-only sharpness. The
current Challenge and definition docstrings identify this reading explicitly;
the earlier issues at their lines 47 and 239 are both fixed.

`scratch/Nonvacuity.lean` compiled successfully with `sap-lean`, independently
of Challenge and Solution results. It checks concrete data satisfying every
T13 and T15 main premise, the equal-bound compatibility case, the counterexample
designs and arithmetic, iid product laws, integer endpoint witnesses, and actual
quota subsets. Infimum/supremum on empty real sets are totalized to zero;
unbounded cases have the same defaults. No audited endpoint depends on these
defaults. Empty pooled samples have endpoint zero only before the explicit
eventual domain condition, and the quota range prevents truncated subtraction
or reciprocal-zero cardinalities. All audited finite expectations exist and
all sampling spaces are discrete. No additional measure-theoretic restriction
is needed.

The final JSON files were parsed with Python and checked against the five
closure names and fingerprints. No source statement or proof was changed.
