import SAP.P001e.Defs
import SAP.P001e.Defs.WholeW1
import SAP.P001e.Defs.WholeW2
import SAP.P001e.Defs.DoseIdentification
import SAP.P001e.Defs.WholeW4

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

/-- P001-T77; p. 186 (PDF p. 204), footnote 5 after Definition 5.2.1.
The realized finite nonnegative likelihood is a function on the parameter set in
real coordinate space of the parameter's arity. A normal PDF at its mean equals
1/(s sqrt(2 pi)) for positive standard deviation s, and exceeds one whenever
s < 1/sqrt(2 pi). Thus PDF likelihood values need not lie in [0,1]. -/
theorem SAP.P001e.T77 : SAP.P001e.T77WholeStatement := by sorry

/-- P001-T78; p. 191 (PDF p. 209), footnote 10 in Example 5.2.4.
For a nonempty regression sample with an intercept, any least-squares minimizer
with positive residual sum Q jointly maximizes the normal log likelihood at
scale sqrt(Q/n). Its squared scale is Q/n. The residual sum and mean are zero,
so Q/n equals both the centered residual second moment and the plug-in variance.
No rank or uniqueness assumption is required. -/
theorem SAP.P001e.T78 : SAP.P001e.T78WholeStatement := by sorry

/-- P001-T79; pp. 197–198 (PDF pp. 215–216), Definition 5.2.10.
The population joint CDF is the expectation of the covariate lower-orthant
indicator times the conditional lower-tail probability, expressed by a PMF sum
or PDF integral for the appropriate conditional-law version. Replacing that
expectation by the sample mean and using one attained ML parameter gives the
corrected fitted PMF and PDF displays. Each fitted display is a joint CDF of a
probability law, so applying any real statistical functional T defines T(Fhat).
Samples are nonempty; conditional laws and densities are read as versions. -/
theorem SAP.P001e.T79 : SAP.P001e.T79WholeStatement := by sorry

/-- P001-T80; Example 6.1.2, pp. 209–210 (PDF pp. 227–228);
Theorem 6.1.3, pp. 210–211 (PDF pp. 228–229); sharpness prose, pp. 209 and 212.
An almost-surely [a,b]-valued outcome with binary response has mean between
respondent mean times response probability plus a or b times missingness
probability. The endpoints are the expectations of the lowest and highest
completions. Every value between them is attained with the same observable
joint law. Both response values have positive probability. The six printed
observations give completion vectors (1,0,1,0,1,0) and (1,1,1,0,1,1), with means
1/2 and 5/6; repeating the lowest-value instruction gives 1/2, unequal to 5/6. -/
theorem SAP.P001e.T80 : SAP.P001e.T80WholeStatement := by sorry

/-- P001-T81; Example 6.2.5: pp. 224–225 (PDF pp. 242–243). Paragraph after it: p. 225 (PDF p. 243).
The corrected propensity distances select the two hot deck donors, identify the second donor and its gap, and give completed mean 16/3. -/
theorem SAP.P001e.T81 : SAP.P001e.T81Statement := by sorry

/-- P001-T82; p. 225 (PDF p. 243), Section 6.2.4, first paragraph, last sentence on the page.
A binary response has a bounded conditional-probability version equal to its conditional mean, and impossible real predictions are precisely those outside [0,1]. -/
theorem SAP.P001e.T82 : SAP.P001e.T82Statement.{u,v} := by sorry

/-- P001-T83; Theorem 6.2.6, p. 226 (PDF p. 244), proof pp. 226–227.
For an integrable outcome and almost-surely binary response with both values
of positive probability, MAR given the covariates means conditional
independence and an almost-sure uniform positive lower bound on the true
response propensity. Then the recorded-outcome inverse-propensity weighted
variable is integrable, and its expectation equals both the population mean
and the expectation of the weighted uncensored outcome. Propensities are
measurable conditional-mean versions; all version bounds are almost sure. -/
theorem SAP.P001e.T83 : SAP.P001e.T83WholeStatement := by sorry

/-- P001-T84; p. 228 (PDF p. 246), first paragraph. Definition 6.2.7: p. 227 (PDF p. 245). Section 6.2.1 plug-in estimator: p. 219 (PDF p. 237). Section 6.2.4: pp. 225–226 (PDF pp. 243–244).
The explicit twelve-unit example refutes the reading of "logically equivalent" as exact finite-sample equality of IPW and post-stratification plug-in estimators for arbitrary ML binary-choice propensity fits.
Its three-cell logit likelihood has the stated unique ML fit, IPW mean 3/7, plug-in mean 5/12 and gap 1/84. -/
theorem SAP.P001e.T84 : SAP.P001e.T84Statement := by sorry

/-- P001-T85; p. 228 (PDF p. 246), first paragraph.
For every positive finite sample with binary responses, a respondent in each
observed cell and positive fitted probabilities, grouping gives both cell formulas
and their difference. Equality for every outcome vector is equivalent to fitting
the observed response fraction in every cell. Under this saturation condition the
mean weight is one and the stabilized, ordinary IPW and plug-in estimates agree. -/
theorem SAP.P001e.T85 : SAP.P001e.T85WholeStatement := by sorry

/-- P001-T86; p. 228 (PDF p. 246), Definition 6.2.8 and the paragraph after it.
Response-weighted inverse propensities have conditional and unconditional mean one, while reciprocal propensities have mean at least one with the stated equality case.
Restriction: Uses pointwise binary response and pointwise uniform positive propensity bounded above by one. Retains the one-unit conditional and unconditional mean-one identities and the reciprocal-weight lower bound with its equality criterion. Omits the finite-sample mean-one conclusion, the finite-sample stabilized-estimator formula, convergence with fitted propensities and the efficiency discussion. -/
theorem SAP.P001e.T86 : SAP.P001e.T86Statement.{u,v} := by sorry

/-- P001-T87; p. 233 (PDF p. 251), first paragraph below Table 6.3.1.
For integrable outcomes and almost surely binary responses, a measurable respondent
conditional-mean function exists. Every such version is also the respondent CEF
of the recorded outcome. On nonresponse the recorded CEF is minus 99; the full
CEF given (R,X) is R m(X) minus 99(1-R). Under MAR and almost sure uniform
positive propensity every respondent version is integrable in the population and
is its outcome CEF. The linear and squared-covariate working specifications target
this respondent function; no exact approximation or numerical-fit assertion is made. -/
theorem SAP.P001e.T87 : SAP.P001e.T87WholeStatement := by sorry

/-- P001-T88; Theorem 7.1.8 and the first part of the proof: p. 243 (PDF p. 261); rest of the proof: p. 244 (PDF p. 262).
Both sharp ATE endpoints have the stated observable formulas, attain every compatible effect mean and have unbiased, consistent sample-average estimators. -/
theorem SAP.P001e.T88 : SAP.P001e.T88Statement.{u} := by sorry

/-- P001-T89; pp. 253–254 (PDF pp. 271–272).
The specified uniform six-atom latent law randomizes treatment with respect to all
potential variables. Treatment has zero outcome effect everywhere but changes the
covariate with probability one third. The complete corrected observable PMF has
four masses one sixth and one mass one third, and total one; the printed function
on five distinct cells has total five sixths. The stated covariate marginals,
conditioning-cell masses, four conditional means and contrast minus one quarter
hold. Conditional outcome probabilities one half and zero witness the loss of
conditional independence after adjusting for this post-treatment covariate. -/
theorem SAP.P001e.T89 : SAP.P001e.T89WholeStatement := by sorry

/-- The printed claim is false: deterministic zero and spike response processes have identical observable laws under uniform dose and different effects at both stated dose pairs.
P001-T90; p. 255 (PDF p. 273), first paragraph; Definition 7.1.18 and the generalized conditional independence assumption: p. 254 (PDF p. 272). Definition 6.0.1: p. 207 (PDF p. 225). -/
theorem SAP.P001e.T90 : SAP.P001e.T90Statement := by sorry

/-- P001-T91; p. 255 (PDF p. 273), first paragraph; generalized potential
outcomes and process independence: p. 254 (PDF p. 272).
Positive conditional dose masses identify potential means and their contrast;
an independent measurable curve state with jointly measurable evaluation gives
an observed conditional-mean version and unique values of continuous observed
versions at neighborhood-supported doses, identifying the standardized contrast.
Restriction: Clause (a) requires measurability and integrability at every real
dose, separate measurability and integrability of the observed diagonal, and
independence of the entire real-indexed process, including unsupported doses.
Clause (b) requires a measurable curve state, jointly measurable evaluation,
injective state-to-curve encoding, state-treatment conditional independence,
and integrability at every real dose and of the observed evaluation. It retains
the observed conditional-mean construction, potential-mean standardization,
continuous-version uniqueness at the two selected doses and their contrast.
It does not establish clause (b) from supported-cylinder independence alone.
The intermediate conditional mean of the unobserved potential outcome given
both X and D, a separate support-wide any-dose statement, and an explicit
two-model equal-observable-law identification statement are omitted. -/
theorem SAP.P001e.T91 : SAP.P001e.T91IdentificationStatement.{u,v,w} := by sorry

/-- The printed claim is false: the actual six-unit OLS fit makes the two printed imputation estimates differ by -253/4874.
P001-T92; p. 259 (PDF p. 277), the data table and the two imputation tables. -/
theorem SAP.P001e.T92 : SAP.P001e.T92Statement := by sorry

/-- P001-T93; Example 7.2.2, pp. 258–259 (PDF pp. 276–277), corrected.
Both imputation tables use unit 3's covariates (10,3). For any pooled OLS
minimizer, imputing all potential outcomes and imputing only missing outcomes
give the same difference of completed-column means, the treatment coefficient;
the residual normal equations and the displayed filtered-sum correction hold.
The six-unit coefficients are (13563,6178,-759,-1778)/2437 and both estimates
are 6178/2437. Under strong ignorability with uniform overlap and an exact
linear observed CEF, the conditional ATE equals the armwise observed CEF
contrast and the treatment coefficient almost everywhere in the covariate law,
and the ATE equals that coefficient. The fitted contrast is that coefficient
at every covariate value. The usual measure-theoretic conditions are assumed.
“More straightforward to implement” describes the two displayed algorithms;
it makes no mathematical comparison of computational costs. -/
theorem SAP.P001e.T93 : SAP.P001e.T93WholeStatement_W4 := by sorry

/-- P001-T94; p. 261 (PDF p. 279), the population identity and last display;
the ATE plug-in formula is on p. 262 (PDF p. 280).
Under binary strong ignorability and almost sure overlap, a correct conditional
density identifies both potential-outcome conditional means and their population
means. The latter are integrals over the covariate law, or the printed iterated
Lebesgue integral when that law has a density, and agree across models with the
same observable law. For any existing ML maximizer and finite displayed integrals,
the corrected estimator averages at the observed covariates; the ATE estimator
averages fitted contrasts. The printed free-covariate average collapses to the
single fitted conditional mean at that covariate. -/
theorem SAP.P001e.T94 : SAP.P001e.T94WholeStatement := by sorry

/-- P001-T95; Example 7.2.4: pp. 262–263 (PDF pp. 280–281). Paragraph after it: pp. 263–264 (PDF pp. 281–282).
The exact distances select all opposite-arm donors and give the completed-column means 22/6 and 15/6 and matching estimate 7/6. -/
theorem SAP.P001e.T95 : SAP.P001e.T95Statement := by sorry

