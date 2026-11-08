# Blind reading of the Challenge

This file was written after reading only the Defs and Challenge Lean sources and relevant Mathlib definitions, before opening claims.json or record.json. The declarations are theorem stubs; this reading concerns their types, not evidence from their proofs.

## Common mathematical dictionary

All four-cell vectors have nonnegative **integer** entries. Write v=(a,b,c,d), n(v)=a+b+c+d, e(v)=b-c (integer subtraction), and tau(v)=(b-c)/n(v). Population entries represent binary potential-outcome types (11,10,01,00), in treatment/control order. Observed vectors o=(a,b,c,d) instead represent assignment/outcome types (11,10,01,00); their treatment and control sizes are m=a+b and n-m=c+d, and h(o)=a/(a+b)-c/(c+d). Rational computations are embedded exactly into the reals where needed.

For v and m, Q(v,m)=randomStates v m is the list of all q=(q_a,q_b,q_c,q_d) with 0<=q_i<=v_i and sum q_i=m, enumerated in increasing a, then b, then c; q_d is the remaining count. Its weight is W(v,q)=product_i binomial(v_i,q_i). Mathlib Nat.fast_choose is the usual Nat.choose, implemented by descending factorial divided by factorial. The observed vector is O(v,q)=(q_a+q_b,q_c+q_d,v_a-q_a+v_c-q_c,v_b-q_b+v_d-q_d). For admissible q all these natural-number subtractions have their ordinary nonnegative values. designProb(v,m,E)=sum_{q in Q(v,m)} W(v,q)1_E(q)/binomial(n(v),m). Thus this is uniform complete randomization on labeled m-subsets, aggregated by type counts whenever 0<=m<=n.

The integer deviation numerator is H(v,o,m)=n(v)((n(v)-m)o_a-m o_c)-m(n(v)-m)e(v), with all arithmetic here in Z. For m=o_a+o_b, tailCount(v,o) sums W(v,q) over q in Q(v,m) satisfying |H(v,O(v,q),m)|>=|H(v,o,m)|. The rational p-value is that count divided by binomial(n(v),m). When totals agree and both arms are positive this is precisely P(|h(O)-tau(v)|>=|h(o)-tau(v)|), including ties. levelAccepted(alpha,v,o) implements p>=alpha by cross multiplication; when the denominator is zero it instead returns alpha<=0, agreeing with the field's zero-division convention.

possibleTables(o) enumerates, for 0<=i<=o_a, 0<=j<=o_b, 0<=k<=o_c, 0<=l<=o_d, the vectors (i+k,o_a-i+l,o_c-k+j,o_b+o_d-j-l). Possible(o,v) means membership in that list: a potential-outcome vector compatible with the observations. A_alpha(o) is the finite **set** of tau(v) for these vectors with p(v,o)>=alpha. I_alpha(o)=exactInterval alpha o consists of all real t for which there exist l,u in A_alpha(o) with l<=t<=u. It is the closed interval hull, and is empty if A is empty. lower and upper are Mathlib's real sInf and sSup of A; on a nonempty finite A these are its minimum and maximum. acceptedEffectsQ is the list of accepted integer e(v), after deduplicating the possible vectors. intervalQ is none if that list is empty, otherwise some(min e/n(o),max e/n(o)).

A mask r in missingMasks(o) is any four-cell integer vector with 0<=r_i<=o_i. It records how many outcomes are missing within each true observed cell. The plus completion is o+=(o_a+r_b,o_b-r_b,o_c-r_c,o_d+r_c); the minus completion is o-=(o_a-r_a,o_b+r_a,o_c+r_d,o_d-r_d). All completions are (o_a-r_a+t,o_b-r_b+r_a+r_b-t,o_c-r_c+s,o_d-r_d+r_c+r_d-s), for 0<=t<=r_a+r_b and 0<=s<=r_c+r_d. These enumerate count completions, not individually labeled completions.

J_alpha(o,r)=missingInterval is the real closed interval whose lower endpoint is min(lower(A_alpha(o-)),h(o-)) when A_alpha(o-) is nonempty, otherwise h(o-), and whose upper endpoint is max(upper(A_alpha(o+)),h(o+)) when A_alpha(o+) is nonempty, otherwise h(o+). missingIntervalQ computes these endpoints rationally with the same empty-set guards. U_alpha(o,r)=completionUnion is the union of I_alpha(c) over count completions c. completionHull is the existential interval hull of U, empty if U is empty. completionHullQ takes minimum/maximum endpoints of all nonempty rational completion intervals, or none if there are none.

IsMissingLaw(v,m,mu) requires mu(q,r)>=0 for every admissible q and legal mask r, and, for every such q, sum_r mu(q,r)=W(v,q)/binomial(n(v),m). It places no conditions outside this finite domain. missingProb is the sum of mu over the event in that domain. There is no independence assumption on q and r.

The fixed bad population is v_bad=(11,0,3,6). badMask(q)=(0,0,1,0) only for q=(0,0,3,0), and is zero otherwise. badCoverage is the weighted rational probability of tau(v_bad) in J at level 109/500 and m=3, with denominator 1140. badHullCoverage uses completionHullQ instead.

For searches f:Z->Bool, true means reject and false accept. A step at integer bracket (a,b) tests c=floor((a+b)/2), and replaces (a,b) by (a,c) on rejection or (c,b) on acceptance. printedReturn returns only on b=a+1: first return a if a>k1 and b<k2; otherwise if a=k1 test k1 and return k1-1 on rejection or k1 on acceptance; otherwise if b=k2 test k2 and return k2-1 or k2; otherwise none. printedSearch makes a step BEFORE this adjacency/return check, recurses on failure, and returns none after fuel runs out. sentinelSearch instead checks b<=a+1 BEFORE testing, returns (a,[]) there or at zero fuel, and otherwise recurses on the updated bracket and prepends c to the trace. logTwo(d)=Real.log(d)/Real.log(2).

candidateNumerators(o) is the ordered list o_a-o_c-(o_a+o_b)+k, 0<=k<=n(o). lineGroup(o,x,j) filters possibleTables(o) to e(v)=x and v_a+v_b=j. firstOnLine returns a vector in that group with minimal b (or none); minimumB resolves ties in favor of the earlier list entry. reuseVector(v,k)=(v_a-k,v_b+k,v_c+k,v_d-k), using truncated natural subtraction unless k<=v_a,v_d.

The executed upper search uses candidates(o,x): visit j=0,...,n(o), take firstOnLine when it exists, and, if that base has b=c=0, a,d>=1 and (a-1,1,1,d-1) is possible, append that extra vector immediately after the base. runTests tests these in order, increasing a global test index, continuing on rejection and stopping at the first acceptance. It returns compatibility, the next index, and the table/rejection trace. adaptiveSearch repeats midpoint compatibility queries; in printed mode it applies the printed endpoint boundary checks after each step and may make an endpoint compatibility query. In corrected mode it stops on adjacent/reversed brackets before a step. Zero fuel yields endpoint none. upperRun sets k1=2(o_a-o_c), k2=o_a-o_c+o_a+o_b, uses fuel n(o)+3 and index zero; printed mode starts at (k1,k2), corrected mode at (k1-1,k2+1). exactRejectQ is the negation of levelAccepted and ignores the test index.

A PotentialTable(n) is an arbitrary function w:{0,...,n-1}->Bool x Bool. bit(false)=0 and bit(true)=1. tableCounts counts its four potential types; tableTau(w)=sum_i(w_i(1)-w_i(0))/n. Assignment(n,m) is the finite type of m-element subsets z of these labels. tableEstimator(w,z)=sum_{i in z}w_i(1)/|z|-sum_{i notin z}w_i(0)/(n-|z|). unitOutcomes chooses treatment potential in z, control potential outside. PossibleTable(y,z,w) means these outcomes equal y. outcomeEstimator(y,z) is the analogous treatment-minus-control mean of y. unitObserved(y,z) counts its assignment/outcome cells. unitPlus(y,z,r) replaces missing outcomes i in r by 1 on z and 0 outside z, keeping all other y. coupledPlus(w,yPlus,z) replaces only each unit's potential that is observed under z by yPlus, leaving its other potential unchanged. unitPValue(w,y,z) is uniform probability over Assignment(n,|z|) of |tableEstimator(w,q)-tableTau(w)|>=|outcomeEstimator(y,z)-tableTau(w)|.

For integer-indexed real sequences, IsPMF(f) means f>=0 pointwise, f is summable, and sum_Z f=1. IsMass adds Summable(i*f(i)), i.e. a finite absolute first moment. Mathlib sums here are unordered real tsums, and real summability gives absolute summability. SDShape(f,c2) means f(c2-i)=f(i) for every integer i, and f(j)<=f(i) whenever c2<=2i and i<=j. IsSD(f) means IsMass(f), together with an integer c2 for which its mean sum_i i f(i)=c2/2 and SDShape(f,c2). Thus symmetry centers are integer or half-integer and decrease is only on the right half of the integer lattice. PrintedDecrease means decrease on all of Z: i<j implies f(j)<=f(i).

zeroMass is delta_0; fairMass has weights 1/2 at 0 and 1; dependentSumMass has weights 1/2 at 0 and 2. smoothMass(f)(i)=(f(i)+f(i-1))/2. paritySmooth(f,p)(i)=f(floor((i-p)/2))/2 (integer Euclidean division by positive 2, including at negative indices). latticeMean(k,g)=sum_j (j/k)g(j). scaledEstimatorMass(v,m)(j)=designProb(v,m,m*h(O)=j), with the equality computed in Q. pairContribution(w1,w2,true)=w1(1)-w2(0), and pairContribution(...,false)=w2(1)-w1(0), as integers. finiteTail(w,D,x)=sum_i w(i)1_{x<=D(i)} on any finite index type.

varianceEstimate(o)=o_a o_b/(o_a+o_b)^3+o_c o_d/(o_c+o_d)^3, with real arithmetic. standardError is its nonnegative real square root. studentized(C,o,v) is C if the standard error is zero, otherwise (h(o)-tau(v))/standardError(o). canonicalPair(v,i) places the four types in consecutive blocks of lengths a,b,c,d. canonicalObserved and treatedCounts respectively count observed cells and treated potential types for a subset of labels; their theorems use exactly n(v) labels. uniformProb(E)=number(E)/card(Omega). rankValue(R,o,v,samples)=(1+number of K samples with |R(O(v,q_i),v)|>=|R(o,v)|)/(K+1).

Mathlib operations are total: real/rational division by zero gives zero; natural subtraction truncates at zero; Int.toNat truncates negative integers; real tsum of a nonsummable family defaults to zero. The interpretations above use ordinary probabilities, extrema and means only where positivity, finiteness, normalization, or summability in the statement/definitions justify them. Empty finite index types are allowed syntactically, but positive weights summing to one prohibit emptiness. List sums count multiplicity, Finset operations remove duplication, Option.none is a failure/empty flag, and trace indexing [i]! uses an Inhabited default outside the list; T23's hypotheses ensure its indices are in range.

## Individual theorem types

### SAP.P003a.T29

For every v:Counts, then m:N, then alpha:R, assuming 0<m<n(v), then 0<alpha<1, designProb(v,m,{q:tau(v) in I_alpha(O(v,q))})>=1-alpha. There are no other hypotheses.

### SAP.P003a.T1

A closed conjunction with no hypotheses or externally quantified parameters:

- n(v_bad)=20; binomial(20,3)=1140; 0<3<20; 0<109/500<1; tau(v_bad)=-3/20.
- intervalQ(109/500,(0,3,11,6))=some(-7/10,-3/20), and intervalQ(109/500,(0,3,10,7))=some(-13/20,-1/5).
- missingIntervalQ at original o=(0,3,11,6) and r=(0,0,1,0) is (-7/10,-1/5).
- badCoverage=297/380<1-109/500; the weights of Q(v_bad,3) sum to 1140; for every Counts q (even outside that state list), badMask(q) is legal for O(v_bad,q).
- p(v_bad,(0,3,11,6))=p(v_bad,(0,3,10,7))=83/380>109/500. The population is possible for the first observation and impossible for the second. Their observed estimators are -11/17 and -10/17 respectively.

### SAP.P003a.T2

Conjunction of three separately universally quantified statements:

1. For every v,m,alpha, assuming m>0, n(v)=2m, and 0<alpha<1, then every mu with IsMissingLaw(v,m,mu), missingProb(tau(v) in J_alpha(O(v,q),r))>=1-alpha.
2. For every o,r,alpha, assuming 0<alpha<1, 0<o_a+o_b=o_c+o_d, and legal r, U_alpha(o,r) is a subset of J_alpha(o,r).
3. For every natural n (implicit), m, assumptions m>0 and n=2m, then y,y':Fin n->Bool, z,r finite subsets of Fin n, assumption |z|=m, assumption y'=y outside r, then w with PossibleTable(y',z,w), then alpha with 0<alpha<1 and alpha<=unitPValue(w,y',z), and assumption h(unitPlus(y,z,r),z)<tableTau(w): define yPlus=unitPlus(y,z,r), D={i:y'(i)!=yPlus(i)}, d=|D|, wPlus=coupledPlus(w,yPlus,z). The conclusions are all of:
   - wPlus is possible for yPlus under z;
   - tableTau(wPlus)=tableTau(w)+d/n;
   - h(yPlus,z)=h(y',z)+2d/n;
   - for every assignment q in Assignment(n,m), with N=|{i in D:(i in q iff i in z)}|, N<=d, tableEstimator(wPlus,q)=tableEstimator(w,q)+2N/n, and the change in centered estimator has absolute value <=d/n;
   - |h(yPlus,z)-tableTau(wPlus)|=|h(y',z)-tableTau(w)|-d/n;
   - unitPValue(w,y',z)<=unitPValue(wPlus,yPlus,z), and alpha<=the latter;
   - upper(A_alpha(unitObserved(yPlus,z)))>=tableTau(wPlus)>=tableTau(w).

### SAP.P003a.T3

Conjunction of six components:

1. For every v,m,alpha with 0<m<n(v), 0<alpha<1, then every mu with IsMissingLaw(v,m,mu), both missing probabilities for tau(v) belonging to U_alpha(O,r) and to its hull are >=1-alpha.
2. For every alpha:R,o,r, assuming both observed arms positive and r legal, I_alpha(o) is a subset of U_alpha(o,r). No restriction on alpha here.
3. Under exactly the same quantified parameters and hypotheses as (2), U_alpha(o,r) is a subset of its hull.
4. For every o,r with r legal, o belongs to its completion list, that list has no duplicates, and its length is (r_a+r_b+1)(r_c+r_d+1). No arm or alpha hypotheses.
5. The full universally quantified T29 coverage statement (with the same order and hypotheses).
6. completionHullQ(109/500,(0,3,11,6),(0,0,1,0))=some(-7/10,-3/20); badHullCoverage=892/1140>=391/500.

### SAP.P003a.T4

A closed conjunction:

- Integer 0<1<2. For every integer x with 1<=x<=2, the constant-false test accepts iff x<=2, and the constant-true test accepts iff x<=0.
- printedSearch with one unit of fuel, domain [1,2], constant-false test and initial bracket (1,2) returns some 1 and does not return some 2.
- One constant-true step on (1,2) gives (1,1). For every natural fuel, the constant-true printedSearch on domain [1,2], starting at (1,1), returns none; also, for every fuel, starting at (1,2) returns none.
- For o=(7,1,0,8), h(o)=7/8; v=(0,14,0,2) and (0,15,0,1) are both possible for o and both have p-value one; intervalQ(1/20,o)=some(1/2,15/16). The value field of upperRun(false,o,exactRejectQ(1/20,o)), with its specified fuel n(o)+3 and test index zero, is some 14.

### SAP.P003a.T5

1. For every integers k1,k2,r, then f:Z->Bool, assuming k1<=k2, k1-1<=r<=k2, and for every x in [k1,k2], f(x)=false iff x<=r: define d=(k2-k1+1).toNat, s=sentinelSearch(d+1,f,k1-1,k2+1). Then s.endpoint=r, its trace has no duplicates, each trace query is in [k1,k2], and its length as a real is <=floor(logTwo(d))+1.
2. For every k1,k2,f with only k1<=k2, use the same d,s. Its trace has no duplicates, all queries are in [k1,k2], the same length bound holds, and k1-1<=s.endpoint<=k2. No monotonicity hypothesis in this component. It does not explicitly assert final adjacency or unused fuel.

### SAP.P003a.T11

Let q(x)=1 for x<=0 and 0 for x>0. For every real x, q(x)<1/2 iff x>0. Some such x exists; there does not exist a rejecting x which is <=every other rejecting real u. Separately, for every real x, the n=2,m=1 population (0,0,0,2) has design probability of x<=|h(O)-tau| equal to that q(x).

### SAP.P003a.T12

For every type Omega equipped with Fintype, then functions w,D:Omega->R, assumptions w(i)>0 for all i and sum_i w(i)=1, then alpha:R with 0<alpha<1: either every i has alpha<=finiteTail(w,D,D(i)), or there exists i with w(i)>0 and finiteTail(w,D,D(i))<alpha such that for every j rejection finiteTail(w,D,D(j))<alpha holds iff D(i)<=D(j), and the sum of rejecting weights equals finiteTail(w,D,D(i)). In either alternative the sum of rejecting weights is strictly below alpha. D is an arbitrary real statistic; no distinctness or nonnegativity is required. There is no experiment-specific inversion conclusion.

### SAP.P003a.T13

For every implicit natural n, then table w, assuming n>0: tableCounts(w) has total n; sum_i bit(w_i.1)=a+b, sum_i bit(w_i.2)=a+c for those counts; and tableTau(w)=tau(tableCounts(w)). In addition, without hypotheses, tauQ(10,0,0,10)=0 while (10-0)/20=1/2, and tauQ(0,20,0,0)=1 while (0-0)/20=0 (all displayed fractions rational).

### SAP.P003a.T14

Conjunction of: (i) for every f:Z->R, IsPMF(f) implies not PrintedDecrease(f); zeroMass and fairMass are IsSD; zeroMass fails PrintedDecrease; (ii) fairMass is IsSD and its mean is 1/2; (iii) for every k:N, assuming k>0, then every g:Z->R with IsMass(g), sum_j g(j)=1, latticeMean(k,g)=(sum_j j*g(j))/k, and for every integer j the real-valued indicator of the rational equality 2*j=1/2 is zero. The normalization conclusion repeats a conjunct of IsMass. There is no separately defined rescaled law or asserted coordinate-correspondence equality in this type. The last indicator fact is independent of k and g.

### SAP.P003a.T9

fairMass is IsSD with mean 1/2; dependentSumMass is IsMass with mean 1, its value at 1 is zero and at 2 is 1/2, and it is not IsSD. For every integer i, summing over the two Boolean values b with weight 1/2 gives fairMass(i) for the variable 1_b and dependentSumMass(i) for 1_b+1_b. The same Boolean is used twice, so this is an explicitly dependent joint law, not an independent convolution.

### SAP.P003a.T10

1. For every f:Z->R with IsSD(f), smoothMass(f) is IsSD.
2. For every f:Z->R, then integer c, assuming only SDShape(f,c), smoothMass(f) has SDShape at c+1 (twice-center notation). There is no normalization, moment or positivity assumption in this component.
3. For every f with IsSD(f), then integer p with p=0 or p=1, paritySmooth(f,p) is IsSD and, for every integer k, both its value at p+2k and at p+2k+1 are f(k)/2.

### SAP.P003a.T15

For every v:Counts, then m:N, assuming m>0, n(v)=2m, and v_b+v_c>=1, scaledEstimatorMass(v,m) is IsSD. This includes nonnegative summable mass of total one, a summable integer first moment, and right-decreasing symmetry about an integer/half-integer mean. No proof-by-induction assertions or special cases are included separately.

### SAP.P003a.T16

For every implicit natural n, then w:PotentialTable(n), z a subset of labels, then m:N, assumptions m>0, n=2m, |z|=m: tableEstimator(w,z)=sum_i (if i in z then bit(w_i.1) else -bit(w_i.2))/m. Separately, the (true orientation,false orientation) ordered pair of pairContribution is: ((10),(11)) -> (0,1); ((10),(10)) -> (1,1); ((10),(01)) -> (0,0); ((10),(00)) -> (1,0); ((11),(11)) -> (0,0); ((11),(00)) -> (1,-1). These are deterministic two-outcome formulas; this type assigns no explicit orientation probability or partner-sampling law.

### SAP.P003a.T17

1. For every C:R, then observed o and population v, assuming both arms of o positive and n(v)=n(o): varianceEstimate(o)>=0; standardError(o)=0 iff o_a*o_b=0 and o_c*o_d=0 (products of naturals); zero standard error implies studentized(C,o,v)=C; positive standard error implies it equals (h(o)-tau(v))/standardError(o). Possibility of v for o is not required.
2. For every C:R, o=(0,2,0,3) has variance and standard error zero; h(o)-tau(0,0,1,4)=1/5; and its studentized value is C.
3. For v=(0,0,1,4), m=2 and this same observed o, the exact absolute-studentized upper-tail probability is one for extension C=0, and 2/5 for extension C=10^6, always using the same C in simulated and observed statistics.
4. For every v, then m,K:N, alpha:R, C:R, assumptions 0<m<n(v), K>0, 0<=alpha<=1, take the uniform law on Assignment(n(v),m) x (Fin K -> Assignment(n(v),m)). The first coordinate supplies canonicalObserved(v,z); the independent other coordinates supply treatedCounts(v,z_i). The probability rankValue(studentized C,observed,v,samples)<=alpha is <=alpha. This is unconditional rank validity for the observed randomization and all Monte Carlo draws.

### SAP.P003a.T21

A closed conjunction at alpha=17/18 and o=(1,6,0,2): the set of accepted integer effect numerators is exactly {0,1}; intervalQ is some(0,1/9); h(o)=1/7; it is false that 0<=1/7<=1/9; p((1,0,1,7),o)=29/36<17/18. The statement does not separately assert that this last witness vector is possible, nor give its effect or maximality.

### SAP.P003a.T22

1. For every o,u:Counts, assuming Possible(o,u): e(u) occurs in candidateNumerators(o), u_a+u_b<=n(o), and there exists v for which firstOnLine(o,e(u),u_a+u_b)=some v and there exists natural k<=n(o) with k<=v_a, k<=v_d and u=reuseVector(v,k). No positive-arm assumption is imposed.
2. For o=(0,1,0,1), the set of possible vectors is exactly {(0,0,0,2),(0,0,1,1),(0,1,0,1),(0,1,1,0)}. firstOnLine(o,0,0)=some(0,0,0,2), and firstOnLine(o,0,1)=some(0,1,1,0). No executed confidence-set inequality is asserted.

### SAP.P003a.T23

For every integers k1,k2,u, then arbitrary f:Z->Bool, assuming k1<=k2, let s=sentinelSearch((k2-k1+1).toNat+1,f,k1-1,k2+1). Every c in its trace with f(c)=true has s.endpoint<c. If u<=s.endpoint, every trace c<=u has f(c)=false. For every natural indices i,j with i<j and j<trace.length, if f(trace[i])=true, then trace[j]<trace[i]. No monotonicity, distributional, coverage, independence or error-probability assumptions or conclusions occur.
