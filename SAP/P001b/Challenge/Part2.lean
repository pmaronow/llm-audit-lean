import SAP.P001b.Defs.WholeW2
import SAP.P001b.Defs.WholeW1
import SAP.P001b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b

/-- P001-T30. Location: p. 24 (PDF p. 42), sentence after Definition 1.2.14;
p. 25 (PDF p. 43), Definition 1.2.15 and Theorem 1.2.16; p. 36 (PDF p. 54),
Definitions 1.3.10 and 1.3.11; p. 38 (PDF p. 56), Definition 1.3.16;
p. 39 (PDF p. 57), Theorem 1.3.17.
Nonnegative Lebesgue integral PDF versions agree almost everywhere, equal the CDF
derivative almost everywhere, and integrate to one. The CDF has a nonnegative
derivative wherever it is differentiable. Every nonnegative almost-everywhere
replacement is another PDF. Joint integral PDF versions agree almost everywhere.
The product uniform law has CDF xy on the unit square, but its mixed derivative,
first in the second variable, fails at (0,y) for every 0 < y < 1, even though
the inner derivative exists. Continuous independence is equivalent both to
almost-everywhere PDF factorization and to the product being a joint PDF version.
For discrete real random variables, PMF factorization is pointwise.
-/
theorem T30 : SAP.P001b.T30WholeStatement := by sorry

/-- The printed claim is false: P001-T31. Location: p. 24 (PDF p. 42), paragraph before Definition 1.2.14.
The specified fat-Cantor subtype carries a continuous random variable with range and positive-density support containing no nondegenerate interval.
Scope: Retains the specified recursive fat-Cantor set, its measure one half, the normalized subtype probability law, its density, literal range and positive-density support, and exclusion of every nondegenerate interval. Omits the removed-length geometric-series calculation and the quantitative bounds on the lengths of the stage components.
-/
theorem T31 : T31Statement := by sorry

/-- P001-T32. Location: p. 24 (PDF p. 42), paragraph before Definition 1.2.14.
Every random variable with a density is atomless with uncountable range and sample space, and a continuous variable can have interval-free range.
-/
theorem T32 : T32Statement := by sorry

/-- P001-T33. Location: p. 32 (PDF p. 50). Definition 1.3.1: p. 31 (PDF p. 49). Definition 1.2.2: p. 16 (PDF p. 34).
Pointwise equality of functions of a random variable is equivalent to equality of those functions on its actual range.
-/
theorem T33 : T33Statement := by sorry

/-- The printed claim is false: P001-T34. Location: p. 37 (PDF p. 55), sentence and display after Theorem 1.3.12.
The normalized negative-rectangle density gives mass one to the printed event and zero to its printed iterated integral.
Scope: Retains only counterexample (a), the normalized density on (0,1) times (-1,0), with event mass one and printed iterated integral zero. Omits counterexample (b), the independent uniform law on [-1,1] squared and the values three eighths and one eighth.
-/
theorem T34 : T34Statement := by sorry

/-- P001-T35. Location: p. 37 (PDF p. 55), sentence and display after Theorem 1.3.12.
The triangular integral computes the event with nonnegative Y, and the printed formula holds exactly when its omitted negative-Y portion has zero probability.
-/
theorem T35 : T35Statement := by sorry

/-- P001-T36. Restricted density and extended-integral facts about the canonical
function for Theorem 1.3.13.
Location: p. 37 (PDF p. 55), Theorem 1.3.13.
A real analytic strictly positive normalized joint density has an infinite extended
nonnegative slice integral at zero and integrable slices elsewhere. The zero slice
lies outside the finite-real existence domain of the pointwise marginal-PDF identity.
Scope: Retains real analyticity (and hence smoothness), strict positivity, integrability, total mass one, the infinite nonnegative slice integral at zero, and integrability of every nonzero slice. Omits boundedness; the logistic slice formula and its separate normalization; the joint CDF and everywhere mixed-derivative assertions; the limiting value of the zero-slice integrand; positivity of the nonzero slice integrals; and the marginal CDF assertion of no finite derivative at zero. States only these density and extended-integral facts; it does not establish a refutation of the pointwise marginal-PDF identity under the usual assumption that its real slice integral exists finitely.
-/
theorem T36 : T36Statement := by sorry

/-- P001-T37. Location: p. 37 (PDF p. 55), Theorem 1.3.13, and p. 38
(PDF p. 56), Definition 1.3.14.
The extended nonnegative marginal slice integral is finite almost everywhere.
Every finite nonnegative version agreeing with it almost everywhere is a marginal
PDF and gives the CDF at every threshold, without a Borel measurability premise
on the version. At every selected integrable slice with strictly positive integral,
the conditional ratio is integrable, nonnegative and normalized. This last assertion
needs no global measurability assumption on the joint function beyond the existence
of that selected integral. The usual measure-theoretic conditions are assumed.
-/
theorem T37 : SAP.P001b.T37WholeStatement := by sorry

/-- P001-T38. Formalization of the canonical counterexamples to the quoted
unrestricted normal-combination assertion and to using the printed bivariate PDF
formula at correlation plus or minus one.
Location: p. 56 (PDF p. 74), sentence after Theorem 2.1.21; p. 66 (PDF p. 84), footnote 13. Definition 2.1.19: p. 55 (PDF p. 73).
The zero normal combination has an atom and no density or positive-variance normal law, and both printed correlation endpoints have zero denominators.
-/
theorem T38 : T38Statement := by sorry

end SAP.P001b
