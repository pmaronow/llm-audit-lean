# T11 review

`SAP.P061a.T11`: **faithful**, severity **none**, as an explicitly disclosed
finite-support restriction. The blind reading and full closure audit were saved
in `reading.md` before opening the claim or record. `claim-stage.json` records
the independently reached comparison as `narrower`; that conclusion is unchanged
after reading the record.

The added hypothesis is finiteness of the positive-mass support
(`SAP/P061a/Defs/Part9.lean:24`). The canonical setup also permits infinite
positive support, including designs with existing moments. The challenge
docstring accurately excludes all such designs while retaining arbitrary
zero-mass feasible assignments (`SAP/P061a/Challenge/Part1.lean:80–82`), and the
record correctly selects `restricted`.

On this domain, all canonical clauses (a)–(d) are retained: the supported-atom
probability formula, ordinary conditional exposure means, population averages,
unit contrasts, and both population-contrast identities. The conditional mean
is expressed directly through the normalized atomic probabilities of the
positive-probability conditioning event. Every dependent definition is the
appropriate weighted sum or contrast. No stability, independence, or global
outcome bound is added. Finite support guarantees absolute summability, and
positivity and N > 0 exclude zero denominators. No totalized junk value affects
the result. Some identities are definitional, as are the corresponding formulas
in the claim; ordinary-mean existence is separately established.

`scratch/Check.lean` compiled successfully using the permitted `sap-lean`
command. Its feasible set is ℕ with masses 1/3 at 0, 1, 2 and zero elsewhere,
N = 1, exposure 0 at assignment 0 and exposure 1 otherwise, and response y(z) = z.
It proves every hypothesis for the distinct targets 1 and 0, disproves
within-exposure support stability, and computes both exposure-one mean formulas
as 3/2. This checks nonvacuity and the conditional-mean interpretation without
using the challenge theorem. There are no findings requiring a fix.
