import SAP.P001c.Defs.WholeW2
import SAP.P001c.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P001-T39; Theorem 2.1.21 and following sentence, p. 56 (PDF p. 74),
Definition 2.1.19 and Theorem 2.1.20, pp. 55–56 (PDF pp. 73–74), and footnote 13,
p. 66 (PDF p. 84).
Normal variables have their specified mean and standard deviation. Every nontrivial finite
affine combination of mutually independent normal variables is normal, including the affine
and two-variable sum cases. The displayed bivariate density is a probability density with
its specified moments, marginal normal laws and correlation, and gives independence and
pointwise density factorization at zero correlation. These conclusions transfer to every
pair with that joint law. Normal marginals and zero correlation alone do not imply
independence: the equal mixture with correlations 3/5 and −3/5 is a counterexample.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P001c.T39 : SAP.P001c.T39WholeStatement := by sorry

/-- P001-T40; Figure 2.1.1, p. 59 (PDF p. 77); Theorems 2.1.23–24 and
Example 2.1.25, pp. 57–58 (PDF pp. 75–76).
MSE decomposes into variance and squared mean error, and the fair-coin loss has the
stated unique minimum and corrected factor-two plotting values.
Restriction: Omit the example's first-order differentiation calculation and any assertion
that the actual drawn curve follows the stated formula; retain all displayed loss values,
the unique minimizer, the coin's mean and variance, and the general MSE theorems. -/
theorem SAP.P001c.T40 {Ω : Type*} [mΩ : MeasurableSpace Ω] : SAP.P001c.T40Statement Ω := by sorry

/-- P001-T41; Theorem 2.2.6, p. 63 (PDF p. 81); Definitions 2.2.5 and 1.3.1,
pp. 62 and 31 (PDF pp. 80 and 49).
The specified three-outcome PMF establishes the canonical counterexample to the second
and third bullets' forward implications, with equality at every outcome as in
Definition 1.3.1: it has the stated moments, both perfect correlations and probability-one
affine relations, while neither corresponding pointwise affine representation exists. -/
theorem SAP.P001c.T41 : SAP.P001c.T41Statement := by sorry

/-- P001-T42; Theorem 2.2.6, p. 63 (PDF p. 81), with the same qualification
on pp. 62 and 78 (PDF pp. 80 and 96).
For square-integrable variables with positive variances, correlation lies in [-1, 1],
and its values 1 and -1 characterize the corresponding almost-sure affine relations. -/
theorem SAP.P001c.T42 {Ω : Type*} [mΩ : MeasurableSpace Ω] : SAP.P001c.T42Statement Ω := by sorry

/-- P001-T43; Theorem 2.2.21, proof and footnotes 18–19, pp. 76–78
(PDF pp. 94–96); corollaries, p. 78 (PDF p. 96); Theorem 2.2.22, p. 79 (PDF p. 97).
For measurable square-integrable X,Y, affine prediction risk is jointly smooth with the
corrected first partials, all second partials and Hessian determinant 4 Var(X). A Borel CEF
version exists, and every such version is square integrable. Positive regressor variance
gives exactly the BLP coefficients as the unique normal-equation solution and unique risk
minimizer; the BLP best approximates every CEF version and has all three residual
orthogonalities. If a CEF version is affine, the BLP agrees almost surely with every
CEF version. At zero regressor variance, every function
sending E[X] to E[Y] minimizes MSE, and all affine minimizers and their residuals are described.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P001c.T43 : SAP.P001c.T43WholeStatement := by sorry

/-- The printed claim is false: the covariance equation does not uniquely determine
an affine predictor.
P001-T44; footnote 21, p. 78 (PDF p. 96); Theorem 2.2.21, p. 76
(PDF p. 94); Example 2.2.23, pp. 79–81 (PDF pp. 97–99).
The symmetric two-point example has distinct affine predictors with the same covariance
and respective squared prediction errors zero and one.
Restriction: Retain only counterexample (a); omit the uniform/Gaussian counterexample (b)
and the general formula Cov(X,a+bX)=b Var(X). -/
theorem SAP.P001c.T44 : SAP.P001c.T44Statement := by sorry

/-- P001-T45; footnote 21, p. 78 (PDF p. 96).
The covariance equation fixes the affine slope, and adding the mean equation gives
exactly the coefficients that uniquely minimize affine prediction risk. -/
theorem SAP.P001c.T45 {Ω : Type*} [mΩ : MeasurableSpace Ω] : SAP.P001c.T45Statement Ω := by sorry

/-- P001-T46; Examples 2.2.23–24, pp. 79–82 (PDF pp. 97–100);
Theorems 2.2.21 and 2.2.25, pp. 76 and 82–83 (PDF pp. 94 and 100–101).
For independent uniform X and standard normal W, Y=10X²+W has CEF 10X². The conditional
square equals X², the conditional noise mean is zero, and conditional linearity gives the
displayed calculation. The stated moments yield slope 10, intercept −5/3 and the unique
affine minimum. In general the covariance/variance BLP coefficients uniquely minimize
risk at positive regressor variance, and independent integrable outcomes have constant CEFs.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P001c.T46 : SAP.P001c.T46WholeStatement := by sorry

/-- P001-T47; Theorem 2.2.25, pp. 82–83 (PDF pp. 100–101), with sub-bullet (a)
corrected to E[h(Y)|g(X)]=E[h(Y)]; Theorems 1.3.17, 2.2.8 and 2.2.21, pp. 39, 64
and 76 (PDF pp. 57, 82 and 94).
The usual measure-theoretic conditions are assumed; in particular, functions of random
variables are measurable functions. Independence is equivalent to independence of every
pair of measurable transformations. Independent variables have constant conditional mean
and conditional variance, factorized product expectation, zero covariance and correlation,
and additive variance. The constant outcome mean is a best affine predictor, uniquely so
in coefficients at positive regressor variance. The corrected transformed conditional-mean
and BLP conclusions hold with the same clause-specific existence conditions. The general
positive-variance BLP coefficient and unique-minimum theorem is included. -/
theorem SAP.P001c.T47 : SAP.P001c.T47WholeStatement := by sorry

/-- P001-T48; Definition 2.3.1 and Theorem 2.3.2, p. 84 (PDF p. 102).
The covariance matrix has the corrected entries, is symmetric with variance diagonal,
and its entries sum to the variance of the sum of the coordinates.
The usual measure-theoretic conditions are assumed: each coordinate is square integrable,
so every variance and covariance exists. -/
theorem SAP.P001c.T48 {Ω : Type*} [mΩ : MeasurableSpace Ω] : SAP.P001c.T48Statement Ω := by sorry
