import SAP.P003a.Defs
import SAP.P003a.Defs.WholeW1
import SAP.P003a.Defs.WholeW2
import SAP.P003a.Defs.WholeW3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P003-T14; p. 18 (PDF p. 18).
Unrestricted printed decrease excludes every integer pmf; corrected SD includes
the point mass at zero and the fair zero-one law of mean one half. For a positive
lattice denominator k, the source law f on k⁻¹Z gives the pmf g(j)=f(j/k) of kX,
without a moment assumption. Absolute first moments exist simultaneously; when
they exist, the source mean is the integer mean divided by k, with the equivalent
half-integer center assertion. At physical center c₂/(2k), lattice symmetry
is the reflection identity for g, and lattice SD is exactly IsSD g.
For the point mass at one half with k=2 the correct image is unit mass at one,
whereas the printed f(2j) is identically zero and is not a pmf. -/
theorem SAP.P003a.T14 : SAP.P003a.T14WholeStatement := by sorry

/-- P003-T9; p. 23 (PDF p. 23).
The printed claim is false: with corrected SD and lattice denominator one,
dependent variables can have an SD first marginal and a fair zero-one second
marginal while their sum fails SD. The identical fair pair gives masses one half
at zero and two and mean one. The four atoms (-1,0),(0,0),(0,1),(1,1) with weights
one third, one sixth, one sixth, one third give a uniform first marginal on
{-1,0,1} of mean zero and a fair second marginal. Their sum has those four masses
at -1,0,1,2, is symmetric about its mean one half, and fails decrease and SD. -/
theorem SAP.P003a.T9 : SAP.P003a.T9WholeStatement := by sorry

/-- P003-T10; p. 23 (PDF p. 23); proof of Lemma B.9, pp. 24-25 (PDF pp. 24-25).
Independent fair smoothing preserves SD, shifts half-integer symmetry centers, and gives the asserted
parity-lattice convolution masses. -/
theorem SAP.P003a.T10 : SAP.P003a.T10Statement := by sorry

/-- P003-T15; p. 25 (PDF p. 25).
For every positive balanced design with a discordant unit, mT has an SD mass on the
integers, equivalently T is SD on the lattice with spacing 1/m. The seven admissible
two-subject populations have the stated constant or consecutive-two-point laws.
The cases with one or two discordant units satisfy the same conclusion. Each removal
in (B.45) or (B.46) removes two subjects and at most two discordant units; when there
are at least three discordant units, one discordant count is at least two and every
feasible listed residual is a positive balanced design with an SD estimator law.
The four printed-proof gap witnesses have the stated arithmetic and complete sampling
laws, including zero probability away from their listed values. -/
theorem SAP.P003a.T15 : SAP.P003a.T15WholeStatement := by sorry

/-- P003-T16; p. 24 (PDF p. 24).
In a positive balanced experiment the estimator is the signed sum divided by m.
Choose a partner uniformly from the other labels, a fair orientation, and independently
a uniform size-(m-1) treatment subset of the remaining labels. This construction gives
the uniform size-m assignment law; its conditional product law is explicit. The pair
contribution to mT is the corrected signed pair expression, and T is that expression
divided by m plus the remaining signed sum divided by m. Every ordering of the remaining
labels gives (B.51); for m>1 it is (m-1)/m times their estimator, and for m=1 it is zero.
The six corrected pair laws and the six different printed plus-sign laws hold under
the same fair orientations, conditional on the chosen partner, relabeled as subject 2. -/
theorem SAP.P003a.T16 : SAP.P003a.T16WholeStatement := by sorry

/-- P003-T17; p. 11 (PDF p. 11); footnote 13 on the same page.
For two positive observed arms, the printed Q expressions simplify to ab/(a+b) and
cd/(c+d), and the printed variance equals the nonnegative binary variance formula.
Its standard error vanishes exactly when both within-arm products vanish. Fixing one
real C before testing defines the same real statistic on every observed, fresh, and
reused input. The all-zero five-subject population has ten zero-variance assignments;
the population with one (0,1) subject has the stated four versus six assignments,
observations, numerator 1/5, and other variance 2/27. Under every fixed null table the
plus-one Monte Carlo rank satisfies P(S≤alpha)≤alpha. In the second population with
the zero observation, the exact tail probability is 1 for C=0 and 2/5 for C=10^6. -/
theorem SAP.P003a.T17 : SAP.P003a.T17WholeStatement := by sorry

/-- P003-T21; p. 7 (PDF p. 7), footnote 9, corrected.
In the legal nine-unit, seven-treated experiment, the 42 possible vectors have the
ten stated attained maximum p-values. Exactly zero and one ninth are accepted;
the interval is [0,1/9] and excludes the observed one seventh. The complete
negative-effect fiber and both possible p-equals-one witnesses are certified. -/
theorem SAP.P003a.T21 : SAP.P003a.T21WholeStatement := by sorry

/-- P003-T22; pp. 11-12 (PDF pp. 11-12), Algorithm 5.3, corrected.
Continuing with the next j after every processed line gives a finite traversal
of exactly every possible vector, using its minimum base and valid reuse line.
The returned set uses the actual plus-one tests and correlated reuse updates.
For the two-unit example and the constant statistic, every test accepts:
the literal first-line reading returns {0,1}, while the correction returns
{0,1,2}. The omitted value two is realized by the stated labeled experiment. -/
theorem SAP.P003a.T22 : SAP.P003a.T22WholeStatement := by sorry

/-- P003-T23; p. 13 (PDF p. 13), Remark 5.6, corrected.
A rejected query in the corrected T5 search forces the returned numerator and
every later query strictly below it, for arbitrary decisions. This applies
pointwise to Algorithm 4.5's chronological fresh Monte Carlo batches and whole
compatibility blocks. The exact balanced endpoint exists on the effect lattice.
Returning at least that endpoint requires accepting every queried effect at or
below it, with no accuracy or monotonicity assumption on Monte Carlo decisions. -/
theorem SAP.P003a.T23 : SAP.P003a.T23WholeStatement := by sorry

