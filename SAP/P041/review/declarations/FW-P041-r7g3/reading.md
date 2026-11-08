# Blind reading

This file was written before opening `claims.json`, `record.json`, `earlier.json`, or `architect-report.md`. Sources read: the two Challenge declarations and their docstrings; every declaration listed in `closure.json`, including the generated auxiliary proofs printed in `scratch/BlindPrint.lean`; and the relevant Mathlib definitions of `Real.log`, `ProbabilityTheory.cdf`, and `ProbabilityTheory.gaussianReal`. The following describes only the current formal statements and documentation, without comparing them with the canonical claims.

## SAP.P041.T11

Location: `SAP/P041/Challenge/Part1.lean:94–98`; its proposition is `SAP/P041/Defs/Part13.lean:12–27`.

All numerical variables and all decimal constants below are real numbers. Decimals are exact rationals, not floating point numbers. Write

\[
Z(h,s)=\frac{h\log h}{s},\qquad
P(h,s)=2\Phi(-|h\log h/s|),
\]

where `log` is Mathlib's real logarithm and \(\Phi(x)=N(0,1)((-\infty,x])\). More precisely, Mathlib's probability measure `gaussianReal 0 1` has real mean zero and nonnegative-real variance one; `cdf` of this probability measure at a real point equals the real value of its measure of `Set.Iic` of that point. Thus the formula is the ordinary two-sided standard-normal reference probability. These formulas fully replace `hazardWald` and `normalTwoSided` in what follows.

For each row in the following table, the statement has a separate universally quantified clause: for every real \(h\), then every real \(s\), if \(h_0-0.0005\le h\le h_0+0.0005\) and \(s_0-0.0005\le s\le s_0+0.0005\), then \(p_{\min}\le 2\Phi(-|h\log h/s|)\le p_{\max}\). Both rectangle endpoints are included. These inequalities fully unfold `printedInterval`.

| \(h_0\) | \(s_0\) | \(p_{\min}\) | \(p_{\max}\) |
| --- | --- | --- | --- |
| 0.691 | 0.318 | 0.4205 | 0.4232 |
| 0.775 | 0.503 | 0.6936 | 0.6954 |
| 0.627 | 0.406 | 0.4700 | 0.4720 |

The statement also conjoins six closed assertions, one pair per row:

| \((h_0,s_0)\) | central absolute-statistic assertion | central probability assertion |
| --- | --- | --- |
| (0.691,0.318) | \(\big||0.691\log(0.691)/0.318|-0.8032\big|\le0.00005\) | \(|2\Phi(-|0.691\log(0.691)/0.318|)-0.4219|\le0.00005\) |
| (0.775,0.503) | \(\big||0.775\log(0.775)/0.503|-0.3927\big|\le0.00005\) | \(|2\Phi(-|0.775\log(0.775)/0.503|)-0.6945|\le0.00005\) |
| (0.627,0.406) | \(\big||0.627\log(0.627)/0.406|-0.7209\big|\le0.00005\) | \(|2\Phi(-|0.627\log(0.627)/0.406|)-0.4710|\le0.00005\) |

Finally, for each of the same three rectangles there is another separate clause: for every real \(h\), then every real \(s\), the two rectangle-membership hypotheses imply \(|h\log h/s|<1\). All these assertions are conjoined; none is a premise for the other assertions. There are no global parameters, random observations, fitted models, hypotheses of independence, existential conclusions, subgroup-comparison conclusions, or population/mechanism conclusions.

The Challenge docstring describes the numerical enclosures and central approximations and explicitly calls the theorem a restriction. It says that the living-subgroup compatibility existence assertion, all P2 confinement/mechanism inferences and their refutation, and comparison with active-senator relative effects are omitted. It explicitly does not claim that the central living-subgroup probability rounds to 0.70.

### Conventions and potential junk values

- Real division uses the field convention \(x/0=0\). `hazardWald` has no positivity guards in its definition, but every use here lies in one of the rectangles, whose smallest \(h\) is 0.6265 and smallest \(s\) is 0.3175. All central inputs are positive as well. Division by zero cannot affect any clause.
- `Real.log 0=0`; for negative inputs Mathlib sets `log x = log |x|`. These extensions do not occur here, since all relevant \(h\) are strictly positive.
- `cdf` is implemented through a conditional-CDF construction and is only assured to represent the input measure's cumulative probabilities for probability measures. Its sole input here is the genuine probability measure \(N(0,1)\). The `measure.real` representation involves `ENNReal.toReal`, which maps infinity to zero, but all these measures of half-lines are at most one, so no infinite value is converted.
- `gaussianReal` uses a Dirac measure when variance is zero. The fixed variance here is one, so the ordinary Gaussian branch applies.
- The closure's `positiveHazard._proof_1` is only the proof that the natural numeral 2 has `AtLeastTwo`; it contributes no hazard model or extra assumption.
- There is no natural-number subtraction, empty index type, sum/mean, Bochner integral, conditional law to select, `sqrt`, `rpow`, supremum/infimum, sequence limit, or partial-function default in this statement. Integer/natural literal encodings give exact real constants and impose no data restrictions.

The hypotheses are visibly satisfiable: the center of each rectangle lies in that rectangle. This will be checked in Lean during the claim comparison.

## SAP.P041.T12

Location: `SAP/P041/Challenge/Part1.lean:100–109`. The proposition is `SAP/P041/Defs/WholeW1.lean:365–375`, which includes `SAP/P041/Defs/Part14.lean:12–23`.

This is a closed conjunction of exact real arithmetic and real inequalities. There are no universally or existentially quantified data and no antecedent hypotheses. To give its full expansion, define the following mathematical abbreviations (each only stands for the displayed real arithmetic, not an additional assumption):

\[
\begin{aligned}
A_1&=100\frac{|75-52|}{(75+52)/2},&
D_1&=100\left(\frac{75/150}{52/150}-1\right),\\
A_2&=100\frac{|92-69|}{(92+69)/2},&
D_2&=100\left(\frac{92/150}{69/150}-1\right),\\
A_3&=100\frac{|62-32|}{(62+32)/2},&
D_3&=100\left(\frac{62/100}{32/100}-1\right).
\end{aligned}
\]

The \(A_i\) formulas unfold `symmetricDifference`. The \(D_i\) formulas unfold `relativeIncrease`. `roundsWhole x k`, for real \(x\) and integer \(k\), means exactly \(k-1/2\le x<k+1/2\), with an exact integer-to-real cast. With these arithmetic abbreviations substituted, the entire conjunction says:

1. \(A_1=4600/127\), \(A_2=200/7\), and \(A_3=3000/47\).
2. \(35.5\le A_1<36.5\), \(28.5\le A_2<29.5\), and \(63.5\le A_3<64.5\).
3. \(52/150<75/150\), \(69/150<92/150\), and \(32/100<62/100\).
4. It is not the case that all three of \(35.5\le D_1<36.5\), \(28.5\le D_2<29.5\), and \(63.5\le D_3<64.5\) hold together.
5. \(D_1=575/13\), \(D_2=100/3\), and \(D_3=375/4\).
6. Each separate assertion in item 4 is false: \(\neg(35.5\le D_1<36.5)\), \(\neg(28.5\le D_2<29.5)\), and \(\neg(63.5\le D_3<64.5)\).
7. \(43.5\le D_1<44.5\), \(32.5\le D_2<33.5\), and \(93.5\le D_3<94.5\).

Items 1–4 form the older embedded `T12Statement`; items 5–7 are the extra clauses of `T12WholeStatement`. In particular, the current theorem proves three individual failures, not just failure of their conjunction. The real counts/probabilities are fixed constants; their interpretation as removal counts/probabilities is supplied by documentation, not a stochastic model inside this proposition.

Both the Challenge docstring and the defining docstring say “The printed claim is false,” qualify this as the stated directional reading of “more likely than,” give the three corrected exact percentages and roundings, note the symmetric alternative and three directions, and say that the usual measure-theoretic conditions are assumed. Whether this is a refutation of the canonical assertion cannot be decided at this blind stage.

### Conventions and potential junk values

- `relativeIncrease` would use \(p_A/0=0\), giving -100, if its second argument were zero. Here the second arguments are \(52/150\), \(69/150\), and \(32/100\), all strictly positive.
- `symmetricDifference` would divide by zero for \(a+b=0\), and would return zero under Lean's field convention. Its three denominators here are 127/2, 161/2, and 47, all strictly positive.
- Every other denominator (150, 100, 127, 7, 47, 13, 3, 4, and the rounding denominator 2) is a positive exact real numeral.
- `roundsWhole` uses half-open intervals: ties at the lower endpoint are included and ties at the upper endpoint excluded. The integer-to-real casts are exact. None of these fixed values is a tie.
- There are no logarithms, powers outside domains, square roots, measure/integral operations, infinity conversions, subtraction on naturals, empty index types, extrema/limits, or partial functions in this statement.

### Complete auxiliary-proof audit

Besides the mathematical definitions above, the T12 closure lists auto-generated proofs for numeric literal elaboration. Every one was printed. Each has the form `Nat.instAtLeastTwoHAddOfNat n`, proving `(n+1).AtLeastTwo` (the special shared literal 2 is printed as `(1+1).AtLeastTwo`). They are closed theorems, not assumptions or model definitions:

- `CitationFitW1._proof_5`: numeral 100; `FormerDesignFactsW1._proof_2`: 75; `PositiveDesignFactsW1._proof_2`: 150; `Student197ConstantW1._proof_1`: 4.
- `SuppliedEvidenceImpliesNullW1._proof_1` and `._proof_2`: 3 and 52; `T11WholeStatement._proof_8`: 13; `positiveHazard._proof_1`: 2.
- `T12Statement._proof_1` through `._proof_14`, in numeric suffix order: 75, 52, 4600, 127, 92, 69, 200, 7, 62, 32, 3000, 47, 150, 100.
- `T12WholeStatement._proof_1` through `._proof_6`: 575, 92, 69, 32, 62, 375.
- `relativeIncrease._proof_1`: 100.

The names mentioning citation fits, designs, Student reference distributions, or an evidence-to-null implication do not import those mathematical definitions into T12: only these closed numeral proofs occur in the elaborated closure. There are consequently no hidden linear-model, distributional, or evidence-sufficiency hypotheses in T12.
