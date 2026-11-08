# Blind reading

This file was written before opening `claims.json` or `record.json`. I read all five Challenge docstrings and statements, all entries of `closure.json`, and the source of every named definition. The 75 distinct generated `._proof_` declarations in the closures were printed in `scratch/Inspect.lean`; their bodies are in `scratch/Inspect.out`. They are numeral-instance, nonzero-finite-type, scalar-tower, or the proof that 1/2 is in [0,1]; none supplies a substantive statistical hypothesis or conclusion.

## SAP.P028.T1

The theorem is a closed conjunction, with no external hypotheses. It asserts facts about two particular rational probability tables, then a universal impossibility of identifying either complier mean from recorded observations.

### Objects and finite definitions

A latent atom is a six-tuple of Booleans `(d0,d1,y0,y1,r0,r1)`. Booleans below are identified with 0 and 1 by the function taking false to 0 and true to 1. A table consists of an atom `a_i` and a rational weight `w_i` for every `i : Fin 17` (the integers 0 through 16). The type of tables itself does not impose normalization or positivity.

For any such table, let `P(E) = sum_{i=0}^{16} w_i 1_E(i)`, `E(f) = sum_i w_i f_i`, and `m(f;E) = sum_i w_i f_i 1_E(i) / P(E)`, all in the rationals. Write `D_z(i)=d_z(i)`, `Y_z(i)=y_{D_z(i)}(i)`, `R_z(i)=r_z(i)`, and `C={i:d0(i)=0 and d1(i)=1}`. Thus `p=P(C)`, `e_z=E(Y_z)`, and `c_d=m(y_d;C)`. Validity means: every weight is strictly positive, their sum is one, `d0<=d1` for every atom, `E(d1-d0)=p`, and `p>0`.

Assignment has the fixed rational law `pi_0=99/200`, `pi_1=101/200`. The joint weight of `(i,z)` is `w_i pi_z`. A recorded outcome is `(z,D_z,R_z,R_z AND Y_z)`; its mass at `(z,d,r,v)` is `pi_z P(D_z=d,R_z=r,R_z AND Y_z=v)`. A missing response is encoded by recording outcome 0 together with `R=0`, so this encoding does not conflate missing outcomes and observed zeros. Recorded-cell probabilities are `P(D_z=d,R_z=1,Y_z=v)` and missing-cell probabilities are `P(D_z=d,R_z=0)`, conditional on assignment through the independent product construction.

The two exact latent tables are as follows (six bits in the order above):

| i | lower atom | lower weight | upper atom | upper weight |
|---|---|---|---|---|
|0|110010|104/12375|110001|1/495|
|1|110011|871/12375|110011|13/165|
|2|000001|738/15655|000010|26/505|
|3|000011|4346/15655|000011|164/505|
|4|110101|1/495|110110|32/5841|
|5|110111|8/99|110111|40/531|
|6|001010|26/505|001001|936/20503|
|7|001011|26/101|001011|4342/20503|
|8|010000|40958176/44062954375|010011|6746986/511698825|
|9|010001|343024724/44062954375|010110|79537936/30190230675|
|10|010010|2170783328/396566589375|010111|19884484/548913285|
|11|010011|18180310372/396566589375|011001|79169476/11541651275|
|12|010101|29736094/1762518175|011011|3305325623/103874861475|
|13|010111|1576012982/15862663575|011100|933302176/680957425225|
|14|011010|13228208/12792470625|011101|233325544/12381044095|
|15|011011|110786242/12792470625|011110|38965365848/6128616827025|
|16|011111|9603827/511698825|011111|9741341462/111429396855|

The source counts, also defined as rationals, are:

| z | d | recorded Y=0 | recorded Y=1 | missing | arm total |
|---|---|---|---|---|---|
|0|0|212|167|36|495|
|0|1|39|40|1|495|
|1|0|164|130|26|505|
|1|1|67|110|8|505|

For the lower completion, the numbers of missing successes in these four rows are `(0,1,26,0)`; for the upper completion they are `(36,0,0,8)`. The completion function has integer values. A completed success count is recorded successes plus missing successes; a completed failure count is recorded failures plus missing count minus missing successes. Call the resulting count `N^u_zdv` for `u=0,1`.

Set `A_u=N^u_011/80`, `B_u=N^u_101/320`,
`mu_u0=(N^u_001/495-N^u_101/505)/(2047/9999)`, and
`mu_u1=(N^u_111/505-N^u_011/495)/(2047/9999)`.
Set `q^u_zdv=recordedCount_zdv/N^u_zdv` and `b(t,x)=t` if `x=1`, `1-t` if `x=0`.
The constructed mass of a six-bit atom is the following latent-outcome factor times `b(q^u_{0,D_0,Y_0},r0) b(q^u_{1,D_1,Y_1},r1)` (here Y_z denotes the observed potential outcome under assignment z):

- Always-taker `(d0,d1)=(1,1)`: `(16/99) 1_{y0=0} b(A_u,y1)`.
- Complier `(0,1)`: `(2047/9999) b(mu_u0,y0) b(mu_u1,y1)`.
- Never-taker `(0,0)`: `(64/101) 1_{y1=0} b(B_u,y0)`.
- Defier `(1,0)`: zero.

This specifies independent Bernoulli complier outcomes conditional on their stratum, and independent response-potential Bernoulli draws conditional on the latent treatment/outcome tuple. It fixes unused always-taker control outcomes and never-taker treated outcomes to zero.

### All conjuncts and quantifiers

1. Both fixed tables are valid; both have `p=2047/9999`; both assignment probabilities have the stated positive values. Joint weights sum to one and are all positive.
2. For each table, every response-arm event, treatment-assignment cell event, and respondent treatment-assignment cell event has positive `P`. For each of the two tables, every predicate `E : Fin 17 -> Prop` and every Boolean `z`, `sum_i 1_E(i) w_i pi_z=P(E)pi_z`. This is independence of assignment and all latent variables, including both response potentials.
3. For every `z,d,v`, both tables' recorded probabilities equal the recorded count divided by the arm count; for every `z,d`, both tables' missing probabilities equal the missing count divided by the arm count.
4. The entire recorded mass functions of the two tables are equal, but their complier means are `(1423/10235,6749/10235)` and `(7633/10235,7642/10235)` respectively, with both coordinates unequal.
5. For each of the two tables, `P(D_0=1)=16/99`, `P(D_1=0)=64/101`. Respondent arm means are `207/458` and `240/471`; the respondent means in the pure always and never cells are `40/79` and `130/294`. Full arm means are `(208/495,266/505)` for lower and `(27/55,248/505)` for upper.
6. For any seven rational inputs, define the corollary pair by `((e0-q*a-r*n)/p, (e0-q*a-r*n)/p+(e1-e0)/p)`. Its full-data version uses the full arm means and full pure-cell means with `q=P(D_0=1)`, `r=P(D_1=0)`; its respondent version substitutes respondent arm and respondent pure-cell means, retaining the full p,q,r. Full versions equal their respective true complier pairs. Both respondent versions equal `(1594452863/3629163146,896530960/1244058109)`, unequal to either true pair.
7. For each Boolean treatment `d`, there is no function from rational recorded mass functions to a rational number which, for every valid 17-atom rational table, returns `c_d`. The same impossibility is also asserted for real-valued functions with rational-to-real cast output `c_d`. The function quantifier is inside `forall d` and precedes the universal table quantifier; no continuity or measurability is assumed of the proposed identifying function.
8. Every completion is between zero and the missing count, every completed outcome count is strictly positive, every q is in [0,1], and A,B,mu are in [0,1]. The lower parameter quadruple is `(41/80,39/80,1423/10235,6749/10235)`; the upper is `(1/2,13/32,7633/10235,7642/10235)`.
9. The four treatment/assignment totals are 415,80,320,185, the arm totals 495,505, the full total 1000, and the missing total 71.
10. The two respondent estimates differ from 0.4393 and 0.7207 by less than 0.00005 respectively.
11. For each Boolean `u`, selecting lower or upper, and every six-bit atom `a`, the sum of weights of table rows equal to `a` is exactly the product mass defined above. Its always-taker and never-taker probabilities are respectively 16/99 and 64/101. For each selected table, the map from `Fin 17` to six-bit atoms is injective.

### Junk-value and domain audit

Rational division uses inverse zero = zero. Raw `m` and the raw corollary expressions are total even on zero-probability cells or p=0. In this theorem all fixed-law means are protected by the positive-event and positive-p conjuncts; all denominators 495,505,80,320,9999,10235 and every completed count are positive. The universal identifying-function clause uses only `finiteValid`, which forces p>0, and its target uses only the complier mean, so zero pure cells in other valid tables cause no undefined target. Integer completion subtraction is in Z or Q, not truncated natural subtraction, and the count bounds make the completed values positive. Integer/rational/real casts are exact. All sums are over nonempty finite fixed types. There is no integral, `toReal` infinity, logarithm, square root, rpow, infimum, supremum, limit, or partial-function default in this statement. Its displayed missing-outcome zero is an intentional recording code accompanied by the response bit, not a statistical assertion that the unobserved outcome is zero.

## SAP.P028.T2

This is a closed conjunction of universal causal-model implications, a cellwise-ignorability counterexample, equality of observable bounds for equal observation laws, source-data endpoint attainment and sharpness, and exact arithmetic/rounding.

### Causal and response objects, unfolded

Universally quantify a type `Omega : Type` and a measurable-space structure on it. A model consists of a measure mu with mu(Omega)=1; measurable `S:Omega -> Fin 3`, `Y_0,Y_1:Omega -> R`, and `Z:Omega -> Bool`; both Y functions are Bochner integrable. The joint random variable `(S,Y_0,Y_1)` is independent of Z in Mathlib's `IndepFun` sense. Both events `Z=z` have strictly positive real probability. Treatment potentials are `(D_0,D_1)=(1,1)` at S=0, `(0,0)` at S=1, and `(0,1)` at S=2. The integral of `D_1-D_0` is nonzero. These are hypotheses carried by the model constructor, even where not repeated as theorem arrows. A response consists of a measurable Boolean function R with no independence condition built in.

For a measurable set E, define `m(f;E)=(integral_E f dmu)/(mu(E).toReal)`. Let C={S=2}, A={S=0}, N={S=1}, B_z={Z=z}, H={R=1}. Observed D is D_Z and observed Y is Y_D. Write `p=mu(C).toReal`, `e_z=m(Y;B_z)`, `c_d=m(Y_d;C)`, `t_dz=mu(D=d,Z=z).toReal/mu(B_z).toReal`, and `v_dz=m(Y;{D=d,Z=z})`. Respondent means are `er_z=m(Y;B_z intersect H)` and `vr_dz=m(Y;{D=d,Z=z} intersect H)`.

Let `J_dz=m(1_{D=d}Y;B_z)`, `K_dz=m(R*1_{D=d}Y;B_z)`, and `h_dz=mu(R=0,D=d,Z=z).toReal/mu(B_z).toReal`. The conditional assignment law is `mu(B_z)^(-1) * (mu restricted to B_z)`, with scalar multiplication and reciprocal in the extended nonnegative reals. The reweighted cell moment is `W_dz=t_dz*vr_dz` if `t_dz>0`, and zero otherwise. The bound functions are

`L_0=(K_00-K_01-h_01)/p`, `U_0=(K_00+h_00-K_01)/p`,
`L_1=(K_11-K_10-h_10)/p`, `U_1=(K_11+h_11-K_10)/p`.

The observation is `(Z,D,R,R*Y)` in `Bool x Bool x Bool x R`; its law is the Mathlib pushforward `Measure.map` of mu. The reference source law is a finite sum of Dirac measures: at each of the sixteen Boolean `(z,d,r,v)` tuples put mass equal to the rational recorded mass of T1's lower table, converted by Q->R->ENNReal.ofReal, at `(z,d,r,v_as_real)`. The finite table, its weights, independent assignment distribution and recorded mass function are exactly the explicit T1 definitions above, not free parameters.

### Universal clauses and their order

For every Omega and measurable structure:

1. For every model M and response R, if both potential outcomes are pointwise in [0,1], then p>0, `p=1-t_10-t_01`, `p*c_0=J_00-J_01`, and `p*c_1=J_11-J_10`.
2. Under that same boundedness premise, if the two pure-cell probabilities `t_10,t_01` are positive, both response-arm events and both respondent pure-cell events are positive, and `er_z=e_z` for each z and `vr_10=v_10`, `vr_01=v_01`, then
   `c_0=(er_0-t_10*vr_10-t_01*vr_01)/p` and `c_1=c_0+(er_1-er_0)/p`.
3. Under boundedness, if response-arm probabilities are positive and R is independent of `(Y,D)` separately under each normalized assignment law, then `er_z=e_z` for both z. If in addition both pure cells are positive, then all of the equalities, response positivity, and mixed-identification conclusions in item 2 hold.
4. Under boundedness, if for every d,z with `t_dz>0` the corresponding respondent cell has positive probability and `vr_dz=v_dz`, then `e_z=sum_{d:Bool} W_dz` for each z, `c_0=(W_00-W_01)/p`, and `c_1=(W_11-W_10)/p`.
5. Under boundedness with no response assumptions, `L_d<=c_d<=U_d` for d=0,1.
6. For every model M (without needing the boundedness premise), `m(D;B_1)-m(D;B_0)=p`.

The exact source-table arithmetic is also a conjunct, repeated for each Omega but with no data dependence: the four bound formulas with source counts give `1423/10235,7633/10235,6749/10235,7642/10235`. The mixed formula using `207/458,240/471,16/99,64/101,40/79,130/294,p=2047/9999` gives the respondent pair in T1. The reweighted source formulas are

`((415/495)*(167/379)-(320/505)*(130/294))/p=16568969/38014837`,
`((185/505)*(110/177)-(80/495)*(40/79))/p=295510/414829`.

There exists a model and response on `Fin 3 x Bool x Bool`, satisfying all model-constructor assumptions and boundedness, such that: every positive cell has positive respondent mass and respondent mean equal to its full cell mean; both respondent arm events and respondent pure-cell events are positive; `t_10=t_01=p=1/3`; `(e_0,e_1)=(1/3,2/3)`; `(er_0,er_1)=(1/2,4/5)`; `(c_0,c_1)=(0,1)`; both arm respondent means differ from their full means; and the mixed-identification pair of equations in item 2 fails. This contradicts sufficiency of cellwise mean ignorability for those mixed formulas, while preserving cell reweighting.

For any two measurable spaces, models and responses (quantified before hypotheses), boundedness of both and equality of observation pushforward laws imply equal p, equal all K and h, and equal all L and U. This is a comparison of the bounds, not a claim that the complier levels themselves are determined by an arbitrary response law.

There exist two bounded models and two responses on `Fin 17 x Bool`, both with observation law the reference source law, whose c_d equal respectively `l_d` and `u_d` for both treatments, where `(l_0,l_1)=(1423/10235,6749/10235)` and `(u_0,u_1)=(7633/10235,7642/10235)`. For every bounded model on every type with that source observation law, the computed L,U equal those same endpoints. Finally, for every d and real l,u, if every bounded model with that observation law satisfies `l<=c_d<=u`, then `l<=l_d` and `u_d<=u`. This is coordinatewise interval sharpness; it does not assert arbitrary pairs of levels fill a rectangle.

All six additional decimal approximations have absolute error <1/20000: reweighted estimates 0.4359,0.7124 and the four source endpoints 0.1390,0.7458,0.6594,0.7467. The mixed estimates also have the T1 rounding 0.4393,0.7207.

### Junk-value and domain audit

Real division is total with inverse zero zero. An unrestricted event mean on a null event is zero; unrestricted Bochner integration returns zero on non-integrable functions. In the model all potential outcomes are measurable and integrable, hence observed and selected outcomes are integrable; boundedness further protects every relevant moment. Probability measures are finite (and sigma finite); `mu.real` means ENNReal.toReal, whose value at infinity is zero, but infinity never occurs here. Positive arms and nonzero monotone first stage yield positive finite arm and complier denominators. Conditional assignment laws never take the reciprocal of zero or infinity. The mixed formula and mean-equality claims about pure cells are guarded by their positivity and respondent positivity. Empty treatment cells can have raw v or vr equal to the totalized zero, but W explicitly takes zero in this case and J is a joint moment with a positive arm denominator. K,h and sensitivity bounds likewise need no positive treatment or response cell. The existential counterexample has the positivity clauses required for its ordinary means. In the source law ENNReal.ofReal truncates negative reals at zero, but all the actual reference masses are nonnegative probability masses. The universal-type range includes empty types, on which no probability model with positive arms exists; other types have models and the existential clauses explicitly prevent global vacuity. Finite index types 3 and 17 and Bool are nonempty. There are no logs, roots, rpow, infima, suprema, sequence limits, natural subtractions, or partial-function defaults.

## SAP.P028.T4

This is a closed conjunction of an algebraic universally quantified implication and one explicit counterexample. Every scalar below is real. Define `delta=(e1-e0)/p`,

`L0=max(max(0,-delta),1-(1-e0)/p)`, `U0=min(min(1,1-delta),e0/p)`,
`L1=max(max(0,delta),1-(1-e1)/p)`, `U1=min(min(1,1+delta),e1/p)`.

For the five real inputs `(p,e0,e1,x0,x1)`, the mixture condition is existence of a real n such that `p*x0+(1-p)*n=e0`, `p*x1+(1-p)*n=e1`, and x0,x1,n each belong to [0,1]. The corrected condition is `p*x0+e1-p*x1=e0`, x0,x1 in [0,1], and `0<=e1-p*x1<=1-p`. The printed condition has the same constraints except its upper residual bound is 1.

For every p,e0,e1,x0,x1, if `0<p` and `p<1`, the following all hold:

1. The mixture and corrected conditions are equivalent.
2. For every real n, the treated mixture equation implies `n=(e1-p*x1)/(1-p)` (this clause needs no other constraints on n).
3. `p*x0+e1-p*x1=e0` iff `x0=x1-delta`.
4. If `x0=x1-delta`, then x0 in [0,1] iff `delta<=x1<=1+delta`.
5. `0<=e1-p*x1<=1-p` iff `(e1+p-1)/p<=x1<=e1/p`, and `(e1+p-1)/p=1-(1-e1)/p`.
6. The mixture condition is equivalent to `x0=x1-delta` and `L1<=x1<=U1`.
7. `L1-delta=L0` and `U1-delta=U0`.
8. The printed residual condition is equivalent to `(e1-1)/p<=x1<=e1/p`.
9. If `e1<=1` and `0<=x1`, then `(e1-1)/p<=x1`, and the printed residual condition is equivalent just to `x1<=e1/p`.
10. The mixture condition implies the printed condition.

Independently of those quantifiers, the candidate `(p,e0,e1,x0,x1)=(1/2,3/4,3/4,0,0)` satisfies the printed condition and does not satisfy the mixture condition. This asserts strict weakening somewhere, not at every input.

There are no model, measurability, feasibility-of-input-triple or boundedness-of-e0,e1 hypotheses. The equivalences remain formal algebra for incompatible input triples, in which both sides can be false.

Junk audit: all divisions use real inverse, but p and 1-p are strictly positive under the universal hypotheses, and 1/2 is positive in the explicit conjunct. Subtraction is real, not truncated. Max/min are binary real max/min, never sSup/sInf. No set or sequence limit, empty index type, integral, infinity conversion, logarithm, root, power-domain issue or partial function occurs. Generated numeric instance proofs merely support exact real numerals.

## SAP.P028.T5

This is a closed conjunction with fixed real input p=1/2,e0=e1=3/4 and a separate existential causal realization. The mixture, corrected and printed conditions and four endpoints have exactly the expanded real-algebra meanings in the T4 section (in particular residual upper bounds 1-p and 1, and a bounded existential n). No extra assumption is placed on the candidate x0=x1=0.

The theorem asserts: the candidate satisfies the printed system; it satisfies neither the mixture nor the corrected system; the number `(3/4-(1/2)*0)/(1-1/2)` is 3/2; the printed residual lower endpoint `(3/4-1)/(1/2)` is -1/2, the corrected endpoint `(3/4+1/2-1)/(1/2)` is 1/2; and `(L0,U0,L1,U1)=(1/2,1,1/2,1)`. Also `3/4>1/2` and `3/2>1`.

For all real x0,x1, the printed condition iff `x0=x1` and `0<=x1<=1`. For all real x0,x1 the mixture condition iff `x0=x1` and `1/2<=x1<=1`. For each Boolean d, form the set of real x for which there exist real x0,x1 satisfying the condition and `(if d then x1 else x0)=x`. These coordinate projection sets are [0,1] for the printed condition and [1/2,1] for the mixture condition.

There exists a causal model M on `Bool x Bool` with its usual measurable structure. Unfolding that model means a probability measure, measurable S,Y0,Y1,Z, both potential outcomes integrable, joint independence of `(S,Y0,Y1)` and Z, positive assignment arms, and nonzero integral of monotone D1-D0, with treatment `(1,1)` for S=0, `(0,0)` for S=1, `(0,1)` for S=2. This existential is further constrained as follows:

- mu is the product of two fair Bernoulli measures assigning 1/2 to each Boolean in each coordinate; equivalently, each of the four pairs has mass 1/4.
- `S(s,z)=2` if s=true and 1 otherwise; `Y_d(s,z)=1` if s=true and 1/2 otherwise for either d; `Z(s,z)=z`.
- All Y are in [0,1]. The real probability of S=2 is 1/2 and of S=1 is 1/2. Each assignment arm has probability 1/2.
- Observed D is the selected monotone treatment D_Z, observed Y is Y_D, `e_z=integral_{Z=z}Y/mu(Z=z).toReal=3/4` for both z, and `c_d=integral_{S=2}Y_d/mu(S=2).toReal=1` for both d.

The realization demonstrates compatibility of the **input triple** (p,e0,e1). It does not assert that the invalid candidate pair (0,0) is the true complier-mean pair in the realized model.

Junk audit: the fixed p,1-p and all assignment and complier conditioning probabilities are positive. There is no appeal to a zero-probability noncomplier mean or pure treatment-cell mean. The Bernoulli parameter includes a proof of `0<=1/2<=1`. Probability measures are finite, so real measure never converts infinity. The explicit bounded finite functions are integrable. Real coordinate projections of feasible sets are defined by existential quantification, not infimum/supremum of an empty set. Fin 3 numerals encode three distinct strata without wraparound; there is no natural subtraction, limiting operation, log/root/rpow or partial default.

## SAP.P028.T6

This is a closed conjunction of a universal bounded-causal-model theorem, universal endpoint arithmetic, and one full-compliance model existence assertion.

For every type Omega and measurable-space structure and every causal model M: mu is a probability measure; S:Omega->Fin 3 and Z:Omega->Bool and both Y_d:Omega->R are measurable; both Y_d are integrable; `(S,Y0,Y1)` and Z are independent; both assignment arms have positive real probability; treatment is `(1,1)` for S=0 (A), `(0,0)` for S=1 (N), `(0,1)` for S=2 (C); and the integral of D1-D0 is nonzero. Observed D=D_Z, observed Y=Y_D. Add the premise `forall d,omega, 0<=Y_d(omega)<=1`.

Write `p=mu(C).toReal`, `e_z=integral_{Z=z}Y/mu(Z=z).toReal`, and `c_d=integral_C Y_d/mu(C).toReal`. Let NC be the complement of C and `n=integral_NC Y/mu(NC).toReal`. Let

`K=integral_A Y_1 + integral_N Y_0`.

For treatment d and assignment z let `t_dz=mu(D=d,Z=z).toReal/mu(Z=z).toReal`, `v_dz=integral_{D=d,Z=z}Y/mu(D=d,Z=z).toReal`, and `J_dz=integral_{Z=z}(1_{D=d}Y)/mu(Z=z).toReal`. Let delta=(e1-e0)/p and L0,U0,L1,U1 be the real max/min endpoint expressions displayed in T4.

Under the boundedness premise, all of the following are conclusions:

1. `0<p<=1`, `0<=K<=1-p`, `e_z=p*c_z+K` for each Boolean z, and `K=J_10+J_01`.
2. If p<1, then `mu(NC).toReal=1-p>0`, `K=(1-p)*n`, and `0<=n<=1`.
3. If p=1, then K=0 and `c_0=e_0`, `c_1=e_1`.
4. For each Boolean z, `c_z=(e_z-K)/p`.
5. For each treatment d, `0<=c_d<=1`.
6. For each z, `0<=e_z-p*c_z<=1-p`, and `1-(1-e_z)/p<=c_z<=e_z/p`.
7. `L0<=c_0<=U0`, `L1<=c_1<=U1`, and `c_1=c_0+delta`.
8. If p=1, mu-almost every omega is a complier.
9. If `t_10>0` and `t_01>0`, then `K=t_10*v_10+t_01*v_01`.
10. For every d,z, if `t_dz=0`, then `J_dz=0`.

There is a separate universal assertion, with no model involved: for every real e0,e1 in [0,1], the endpoint expressions at p=1 equal `(e0,e0,e1,e1)` respectively. It appears inside the all-Omega conjunction via the intermediate statement, which does not change its logical force.

Finally there exists a causal model on `Bool x Bool`, satisfying all the constructor conditions above, bounded potential outcomes, p=1, `(c_0,c_1)=(0,1)`, and `mu(Z=z).toReal=1/2` for each z. The statement does not prescribe its pointwise S,Y,Z or measure, beyond these conditions.

Junk audit: event means are totalized ratios and Bochner integrals; raw n is zero on the null noncomplier event at full compliance, but every assertion identifying or bounding the ordinary noncomplier conditional mean is confined to p<1. At p=1 the operative quantity is K, a sum of genuine integrals, not a ratio. Positive arms and the model's monotone nonzero first stage yield positive p, so all bound and complier-mean denominators are nonzero. Empty cell means v are totalized zero, but the probability-times-mean claim is explicitly guarded by positive pure cells; the empty-cell clause instead states vanishing J with its positive arm denominator. Integrability and measurability follow from model fields and boundedness; probability finiteness rules out ENNReal.toReal at infinity. No truncated subtraction, empty finite sum, unbounded supremum/infimum or limit, log, root, rpow, or default partial function occurs. The universal range includes types with no such model, but the final existential supplies a nonempty full-compliance case.
