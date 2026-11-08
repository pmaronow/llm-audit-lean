All five declarations are faithful at their declared scope. No adverse finding
was identified. The blind reading was saved in `reading.md` before opening
`claims.json`; `claim-stage.json` was saved before opening `record.json`.
The record required no revision of any claim-stage judgment.

| Declaration | Canonical coverage | Record and docstring assessment |
| --- | --- | --- |
| `SAP.P045a.T11` | Restricted | Correctly retains the deterministic graph guarantees and completion, and discloses omission of the uniform four-path laws and software changes. Marking and admissible choices are correctly specified by definition. |
| `SAP.P045a.T12` | Whole | Includes all probability, assignment-value, target, expectation and bias clauses of the canonical counterexample. The docstring accurately describes it. |
| `SAP.P045a.T13` | Whole | Includes the partitions, corrected expansion, mixture weights, exact bias and signs, HT expectations, all-treated interpretation and independent cancellation witness. The docstring accurately states their domains. |
| `SAP.P045a.T14` | Restricted | Includes the genuine 450-unit witness, numerical discrepancy, empty subclasses and general identity; precisely discloses the three separately omitted conclusions. |
| `SAP.P045a.T15` | Whole | Includes the general partition and pooling identities and the normalized two-stage instance with its identified conditional target, expected shares and exact bias. The docstring accurately describes both portions. |

Every SAP declaration in the five closures was inspected, including generated
auxiliaries: 123 distinct declarations in total. Their elaborated forms are in
`scratch/ClosurePrint.out`. None is a placeholder or assumes its conclusion.
The finite probability masses, exposure maps, observed outcomes, group means
and target averages correctly implement the canonical notions.

For T12, the printed reading is: the own-treatment HT mean equals the displayed
sum with two exposure-specific denominators. Its conditions are a finite
population of ten, an undirected loopless first-degree network, uniform
two-treated assignments, exposure-consistent outcomes and positive denominators.
The cycle witness meets each condition: every vertex has two neighbours, all 45
pairs have equal weight, the schedule is (2,1,1,0), and the five marginal
probabilities are positive. Its sides differ on every supported assignment.

For T14, the printed reading is: the pooled selected-group mean equals the sum
of the two separately normalized subclass means. Its conditions are six equal
75-unit groups paired in three tracts, three own-psi groups, the stated
tract-stratified schedule, and actual observed group arm means. The witness
selects groups {0,1,2}, treats 50 individuals in each selected group and 25 in
each other group, has positive assignment probability, and gives positive
subclass counts 2 and 1. Its sides disagree for both treatment arms. Among the
20 allowed first-stage assignments, eight instead have counts 0 and 3, where
the printed expression is undefined and the pooled mean exists. These are
genuine witnesses for the canonical counterexample claims; neither is a
refutation of its own canonical assertion. The record correctly uses `whole`
and `restricted`, respectively, rather than `refuted`.

The domain audit found no misuse of junk values. T11's natural subtraction
is 3-1=2 and its infinite distance means disconnectedness. T12 and T13 use
positive denominators on every asserted domain. T14 represents undefined
ratios explicitly with `Option.none`. T15's interpreted averages and conditional
means have positive denominators; totalized empty arms occur only at zero-mass
assignments and do not affect expectations. All probability spaces are finite.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0.
The checks import only `SAP.P045a.Defs`, contain no `sorry`, and construct a
completed greedy run, the genuine two-treated support, a normalized independent
fair two-unit design and a complete supported 450-unit assignment with positive
mass. `python3 scratch/check_witnesses.py` independently verified the cycle and
tract calculations with exact rational arithmetic; results are saved in
`scratch/witness-results.json`. The 450-unit calculation uses the proved fixed
counts and constant arm outcomes, rather than enumerating all second-stage
assignments. `findings.json` contains exactly the five requested declarations,
with fingerprints copied from `closure.json`.
