# Statement referee report

Six targets were audited: **2 correct_whole, 3 correct_restricted,
1 omission_ok**. All other verdict counts are zero; there are no adverse
findings and no requested fixes.

| Target | Theorem | Verdict |
|---|---|---|
| P043-T1 | SAP.P043.T1 | correct_restricted |
| P043-T2 | SAP.P043.T2 | correct_whole |
| P043-T3 | — | omission_ok |
| P043-T4 | SAP.P043.T4 | correct_restricted |
| P043-T5 | SAP.P043.T5 | correct_restricted |
| P043-T6 | SAP.P043.T6 | correct_whole |

The blind expansion was saved in `reading.md` before `claims.json` was
opened. The five theorem-versus-claim decisions were saved in
`claim-stage.json` before `record.json` was opened. No step-2 decision was
changed after reading the record. The canonical statements,
`definitions_needed`, and standing assumptions determine the scope; audit
notes were not used to remove clauses or license the finite-population
restriction.

The three restricted decisions are accurate and disclosed in both the
Challenge docstrings and the record:

* **T1:** The exported conjunction omits the separate A4 statewise observed
  cancellation identity, B1 statewise knowledge equalities, and B3 conditional
  observed-support arm means of 59/25. The exact defining models, intervention
  means, complete support laws and both counterexamples remain. These are
  omissions of separately stated conclusions; the omitted identities are
  recoverable from the retained definitions and facts. Both witnesses have
  negative direct effect and refute the unconditional extension of the
  comparison. The contextual comparison with nonnegative direct effect is
  expressly preserved.
* **T4:** The universal assertion about every normalized nonnegative average
  of increasers' crossed increments and the exact five-type increaser
  probabilities are not separate conclusions. Their stated effects, positive
  conditioning probabilities, both observable laws and full-law
  nonidentification remain. The docstring describes the reading of the
  printed guidance that is refuted.
* **T5:** The population has finitely many types with arbitrary nonnegative
  real weights summing to one. General probability laws, including nonatomic
  laws, are outside this theorem. The identification and covariance
  conclusions inherit the outer monotonicity and positive-first-stage
  premises. Also omitted are arbitrary-nonmonotone signed-crossing value-set
  membership, the particular T4 down-type value at margin 9, and the separate
  nonidentification assertion without monotonicity. Arbitrary-model bounded
  signed telescoping and the general downward-crossing implication remain.

T3's omission is justified on the visible canonical content: the target
contains empirical findings, claims about statistical power and substantive
interpretation. It does not supply a separate exact mathematical proposition
that these Lean statements could certify. Its contextual sign comparison is
covered by T2, and the negative-direct-effect witnesses do not refute that
conditional comparison. This also matches the paper's conditional discussion
and backward reference in the [full-text paper, pp. 473–474](https://www.researchgate.net/publication/231786216_Does_Knowledge_of_Constitutional_Principles_Increase_Support_for_Civil_Liberties_Results_from_a_Randomized_Field_Experiment).

T2's product law represents independent assignment on an arbitrary probability
space. The five integrability hypotheses match the five finite expectations
in the canonical claim. The general mediation decomposition, strict and weak
sign equivalences, null implications, linear and ratio formulas, and finite
net-channel condition are all present. T6 implements the corrected indicators
and both requested identities, with the harmless relabeling K=q+1; it includes
the legitimate single-reference-stratum case.

`scratch/RefereeCheck.lean` compiled successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/RefereeCheck.lean`, importing only
Defs and its Mathlib dependencies. It checks nonempty populations, actual
integrable T2 models with either direct-effect sign, T4's positive conditional
event probabilities, a two-type/two-margin T5 instance with first stage 3/2
and IV ratio 4/3, and occupied-stratum T6 examples. It contains no `sorry` and
does not use Challenge stubs. `scratch/referee-enumerate.py` independently
enumerates the four- and 500-type mediation models and all IV models using
exact rational arithmetic; results are in `scratch/referee-enumeration.json`.

No conclusion is assumed by a hypothesis. Probability normalization rules out
empty finite populations; nondegenerate assignment guards arm denominators;
all conditional-effect denominators used are positive; and the IV formula
filters out zero-probability margins. The general-law integrals are integrable
under their explicit hypotheses. Natural predecessor subtraction occurs only
at positive margins in the telescoping formulas. No out-of-domain integral,
division-by-zero convention, or empty index type supplies the asserted result.
The proof certification itself remains the Comparator's responsibility.
