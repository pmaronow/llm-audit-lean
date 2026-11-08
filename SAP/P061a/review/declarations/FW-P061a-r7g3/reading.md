# Blind reading of SAP.P061a.T11

This reading was saved before opening `claims.json` or `record.json`.

## SAP.P061a.T11

Source: `SAP/P061a/Challenge/Part1.lean:77–83`; its proposition is defined at
`SAP/P061a/Defs/Part9.lean:20–35`.

### Objects, quantifiers, and assumptions

The theorem asserts a universally quantified proposition. In order, it quantifies
over an arbitrary type Ω, a natural number N, a normalized atomic design D on Ω,
an exposure schedule g, a response schedule y, and two real exposure labels d and
d′. It then assumes, in order, N > 0, positivity for d, positivity for d′, and
finiteness of the positive-mass support. There are no further hypotheses.

Unfolding the SAP objects, D consists of a function p : Ω → ℝ with

1. p(z) ≥ 0 for every z;
2. `Summable p`;
3. the Mathlib unordered sum `∑' z, p(z)` equal to 1.

`AtomicDesign.mk` is the structure constructor from this function and these three
proofs; `AtomicDesign.mass` is its projection p. Both `Exposures Ω N` and
`Responses Ω N` are abbreviations for `Fin N → Ω → ℝ`. Thus g_i(z) and y_i(z)
are arbitrary real numbers at each unit i and assignment z. Neither schedule is
assumed to factor through the other, and neither stability nor SUTVA is imposed.

Write S = {z : Ω | 0 < p(z)}; this unfolds `supported`. The finiteness hypothesis
is `Set.Finite S`, not finiteness of Ω. Zero-mass assignments are retained in Ω
and their g and y values remain unrestricted.

For any predicate A : Ω → Prop, `eventProbability D A` is
`∑' z, if A(z) then p(z) else 0`. In particular, introduce only as mathematical
notation

    P_i(e) = ∑' z, if g_i(z) = e then p(z) else 0.

This is exactly `exposureProbability D g i e`. The positivity hypotheses are
separate existential statements: there is a real c_d > 0 with c_d ≤ P_i(d) for
every i, and there is a real c_d′ > 0 with c_d′ ≤ P_i(d′) for every i. The
constants need not agree. Since `Fin N` is finite and nonempty, each statement is
equivalent to positivity of every respective cell probability. The labels d and
d′ are not required to be distinct.

For a real function f on Ω, `mean D f` is the unordered real sum
`∑' z, p(z) * f(z)`. `HasMean D f` means precisely
`Summable (fun z => p(z) * |f(z)|)`; it is absolute integrability with respect to
the atomic weights.

Unfold all remaining SAP definitions using the following displayed expressions:

    M_i(e) = (∑' z, p(z) * (if g_i(z) = e then y_i(z) else 0)) / P_i(e)
    C_i(e) = ∑' z, if g_i(z) = e then (p(z) / P_i(e)) * y_i(z) else 0
    A(e)   = (N : ℝ)⁻¹ * ∑ i : Fin N, M_i(e)
    U_i    = M_i(d) - M_i(d′)
    T      = A(d) - A(d′).

Here M, C, A, U, and T denote respectively `exposureMean`,
`conditionalExposureMean`, `populationExposureMean`, `unitContrast`, and
`populationContrast`. Every sum over i is the ordinary finite sum over all
elements of `Fin N`; every primed sum is Mathlib's `tsum` over Ω.

### Conclusion, in its full conjunction order

For every data set and labels satisfying the above assumptions, all of the
following hold:

1. For every i, `Summable (fun z => p(z) * |if g_i(z) = d then y_i(z) else 0|)`.
   The same assertion holds for d′. These are the two `targetMoment`
   conclusions, with `HasMean` unfolded.
2. For every i and every real e, if e = d or e = d′, then
   `P_i(e) = ∑' z, if 0 < p(z) ∧ g_i(z) = e then p(z) else 0`.
3. For every i, both M_i(d) = C_i(d) and M_i(d′) = C_i(d′).
4. For every real e, if e = d or e = d′, then
   `A(e) = (N : ℝ)⁻¹ * ∑ i : Fin N, C_i(e)`.
5. For every i, `U_i = C_i(d) - C_i(d′)`.
6. `T = A(d) - A(d′)`. This conjunct is also the definition of T.
7. `T = (N : ℝ)⁻¹ * ∑ i : Fin N, U_i`.

The displayed mathematical notation above expands every symbol here to real
arithmetic, finite sums, Mathlib `tsum`/`Summable`, predicates, and set finiteness.
There is no random sampling construction, asymptotic claim, or assertion about
an estimator in this declaration.

### Docstring reading

The docstring describes ordinary conditional exposure means and their unit and
population identities under positivity and finite positive-probability support.
It explicitly says that the feasible set can be infinite with zero-mass points,
that all infinite positive-support designs are excluded even when their targeted
moments exist, and that finite support supplies the targeted absolute moments.
This matches the proposition as read in isolation. No comparison with the
canonical claim or architect's record has yet been made.

### Totalization and junk-value audit

* Real `tsum` is total: a nonsummable real family receives the default value 0.
  `mean` and `conditionalExposureMean` therefore need hypotheses to have their
  ordinary meanings. Here p is summable and nonnegative, and all families that
  occur in the conclusion vanish outside the finite set S. Responses take
  finite real values. Consequently all relevant sums, including their absolute
  counterparts, are summable; the default cannot affect this theorem.
* Event and exposure probability sums are summable already from domination by
  p. Restricting them to S discards only zero terms.
* Real division and inversion are total, with inverse of 0 equal to 0. Each
  P_i(d) and P_i(d′) is strictly positive by hypothesis, and N > 0 makes
  `(N : ℝ)` nonzero. Any auxiliary e used in the conclusion equals one of these
  labels. Thus no division or inversion uses a zero denominator.
* `Fin 0` would be empty and a population average would use the inverse of 0;
  N > 0 excludes that case. Ω cannot be empty because its masses sum to 1.
  The positive-mass support cannot be empty either. Positivity further ensures
  that each targeted exposure event has a positive-mass assignment.
* N is cast exactly from ℕ to ℝ. There is no natural or integer subtraction;
  contrasts use ordinary real subtraction. Summands at zero-mass assignments
  are exactly zero, even when their arbitrary responses are nonzero.
* No logarithms, square roots, real powers, Bochner integrals, extended-real
  `toReal`, infima/suprema, limsups/liminfs, or default-valued partial functions
  occur in this statement's dependency closure.

### Closure coverage

Read every entry in `closure.json`: `AtomicDesign` (including its constructor,
projection, and all three probability-law fields), `Exposures`, `Responses`,
`supported`, `eventProbability`, `mean`, `HasMean`, `exposureProbability`,
`positiveExposure`, `targetMoment`, `exposureMean`, `conditionalExposureMean`,
`populationExposureMean`, `unitContrast`, `populationContrast`, and
`T11Statement`. Their complete source definitions are in `Defs/Part1.lean` and
`Defs/Part9.lean`; the challenge docstring and theorem were also read.
