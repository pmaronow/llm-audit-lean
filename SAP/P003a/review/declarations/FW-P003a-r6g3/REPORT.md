# Declaration review

All five declarations are **faithful**, severity **none**. The record's five
`whole` decisions are accurate. No step-2 assessment changed after reading
`record.json`, and no statement or docstring correction is needed.

The blind reading in `reading.md` was saved before opening the canonical claims;
`claim-stage.json` was saved before opening the record. Every closure declaration
was read, including the generated numeral proofs inspected in
`scratch/PrintClosure.lean`. The review used the supplied sources and canonical
paper transcriptions; it did not inspect any external audit or proof files.

| Declaration | Assessment |
| --- | --- |
| T9 | Both complete dependent joint-law counterexamples, their SD marginals, means and failures of SD match the canonical assertion. |
| T10 | The normalized independent convolution, half-integer center shift and both parity-lattice convolution formulas state the complete corrected claim. |
| T15 | The general SD law, all seven base populations, corrected case coverage, feasible residual laws and four proof-gap witnesses are present. |
| T16 | The sampler has the stated uniform and conditional product laws. The signed pair, full and remaining normalized sums, relabelings, and all twelve pair laws match. |
| T17 | The variance algebra, fixed-C extension, two full examples, independent-draw rank bound and two exact p-values match every canonical clause. |

For T9, the printed reading is: an SD X1 on (1/m)Z plus a variable X2
uniform on {0,1/m} has an SD sum, without an independence premise.
Its conditions are positive m, the stated supports and marginal laws, corrected
SD including a finite mean, and defined probabilities and expectations. Both
witnesses use m=1 and normalized finite probability spaces. The first X1 is
fair on {0,1}, with mean 1/2; the second is uniform on {-1,0,1}, with mean
zero. In each case X2 is fair on {0,1}; every variable is measurable and has
all moments. Their respective sum laws violate decrease at 1 and 2. Dependence
violates no condition of this printed reading. This refutes the assertion
quoted in the canonical T9 claim itself. The record correctly uses `whole`
because the canonical target requests these counterexamples.

The probability encodings preserve the relevant joint laws. The treated-state
weights count labeled assignments; the partner sampler explicitly establishes
the conditional independent fair orientation and uniform residual law. T17's
validity probability is uniform over all functions from Fin(K+1) to the
assignment type, hence its coordinates are independent uniform assignments.
The separate reuse identity imposes no probability assertion on dependent
inputs.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully
without using any of the five Challenge theorem proofs. It independently
constructs the SD fair law and the SD three-point law, checks the second joint
witness's marginal identities and proves both T9 failures of SD. It also
constructs admissible T10 inputs, legal T15 designs and removals, T16 sources
and relabeling equivalences at m=1 and m=2, and both T17 variance branches
with positive observed arms. These checks establish nonvacuity; general proof
certification is supplied by the Comparator as stipulated in the task.

No substantive conclusion depends on a junk value. Positive designs and
feasibility guard all estimator and probability denominators and natural
subtractions. SD includes summable first moments. T10's integer floor division
implements the two parity classes exactly. T16 handles the empty residual at
m=1 explicitly. T17 deliberately defines the zero-standard-error value using
the fixed C; its arbitrary-input rank identity is also well-defined outside
legal experiments, without using those inputs for a validity assertion.
