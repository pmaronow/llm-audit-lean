# Blind reading

Saved at step 1, before opening `claims.json` or `record.json`. Sources are the seven stubs in `SAP/P037c/Challenge/Part1.lean` and all six imported definition files. The statements below are readings of the propositions, independently of their docstrings' claims about scope.

## Common conventions and Mathlib endpoints

All scalars are real unless explicitly natural. `Fin n` is the set of integers from 0 through n−1. All sums/products over a type run over its entire finite universe. Finsets are sets without multiplicity. `powersetCard m` enumerates exactly the m-element subsets (`Mathlib/Data/Finset/Powerset.lean:198,201`); `Nat.choose` is the ordinary binomial coefficient. Images are set images; a backslash is set difference. `PairSplit` means exactly one member of every specified pair is selected.

`dotProduct u v = sum_i u_i v_i` and `(X.mulVec b)_i = sum_j X_ij b_j` (`Mathlib/Data/Matrix/Mul.lean:72,698`). Matrix multiplication, diagonal weights, transpose, and the identity matrix have their usual meanings. Function injectivity of `X.mulVec` means full column rank over the reals. `castAdd` and `castSucc` preserve an index's numerical value, so they select the leading exposure columns, rather than shifting the index.

For a finite population J, define

* `Min(w,X,y,b)` to mean **for every** real coefficient vector c, sum_i w_i(y_i−(Xb)_i)^2 ≤ sum_i w_i(y_i−(Xc)_i)^2. This is `regressionMinimum`, with no hidden normal-equation assumption.
* `L(w,X) = (X' diag(w) X)^−1 X' diag(w)` (`regressionMap`). Mathlib's inverse is the genuine inverse for invertible matrices and the zero matrix otherwise (`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:169–184`). Rank and weight conditions must therefore be read where this map is used.
* For D:J→{0,1,2,3} and p covariates x_i, `X(D,x)` has four indicator columns 1{D_i=k}, followed by the p covariate columns. `S(x)` has an intercept followed by x. The natural subtractions in their indexing are only used in branches where the subtracted number is no larger than the index.
* `Aug(D,w,y,f;k) = |J|^−1 sum_i [1{D_i=k}w_i(y_i−f_i)+f_i]` (`augmentedExposureMean`).

Real division is total in Lean: a/0=0 (`Mathlib/Algebra/GroupWithZero/Basic.lean:402`). No analytic integral, limit, or limsup occurs. The percentile calculation below uses natural subtraction, integer quotient/remainder, sorted list lookup with default zero, and linear interpolation; its concrete indices and sizes are specified below.

## SAP.P037c.T35

This is an unconditional, concrete conjunction, not an implication with data supplied as hypotheses. Let U={0,…,4}×{false,true}, let P flip the Boolean coordinate, let H be all five-element subsets of U, and let z0={(b,false):0≤b<5}. For every subset z of U, y_z(i)=1{i∈z}. For a subset z and arbitrary outcome vector y, set

`S(z,y) = (1/5) sum_{i∈z} y(Pi) − (1/5) sum_{i∈U\z} y(Pi)`.

Set `q(z) = #{z'∈H: |S(z',y_z)| ≥ |S(z,y_z)|}/252`; the outcome vector is held fixed at y_z when z' varies. The theorem states all of the following:

1. |H|=252, z0∈H, and S(z0,y_z0)=−1.
2. For each k∈{0,…,5}, exactly choose(5,k)^2 assignments z∈H have S(z,y_z0)=(2k−5)/5. These six counts are respectively 1,25,100,100,25,1.
3. q(z0)=1/126=2/252<1/100.
4. For every z∈H, if exactly one member of each pair is in z, then q(z)=1/126. For every z∈H not satisfying this condition, q(z)≥13/63.
5. Exactly 32 members of H split every pair, 2^5=32, and #{z∈H:q(z)<1/100}/252=8/63.
6. For every two subsets z,z'⊆U and every i∈U, agreement on membership of i implies y_z(i)=y_z'(i). This quantification is not restricted to H.
7. For every z∈H, S(z,y_z0)=(2|z∩P(z0)|−5)/5.
8. For every b, y_z0(b,false)=1 and y_z0(b,true)=0. The partner outcomes average to 0 among z0 and to 1 among its complement. P(z0)=U\z0 and P(U\z0)=z0.

## SAP.P037c.T36

For **every** finite assignment type Ω and finite unit type I, the theorem conjoins three propositions. No nonempty typeclass is assumed; the following hypotheses provide nonempty instances when their corresponding conclusions are applied.

Define, for E⊆I and arrays A,M,z,y,

`N(E,A,M,z,y) = [sum_{i∈E,j∈I} A_ij M_j z_i y_j]/[sum_{i∈E,j∈I} A_ij M_j z_i] − [sum_{i∈E,j∈I} A_ij M_j(1−z_i)y_j]/[sum_{i∈E,j∈I} A_ij M_j(1−z_i)]`.

First, for **every**, in order, E⊆I, real A:I×I→R, M:I→R, assignment indicators Z:Ω×I→R, weights p:Ω→R, outcomes Y:Ω×I→R, reference assignment z0∈Ω, and real α, assume:

1. A_ij≥0 for all i,j;
2. every M_i is 0 or 1;
3. every Z_zi is 0 or 1;
4. for all z,i, i∉E implies Z_zi=0;
5. for each assignment z, both denominators in N(E,A,M,Z_z,·) are strictly positive;
6. p_z>0 for every z and sum_z p_z=1;
7. Y_zi=Y_z'i for all z,z',i (the global sharp null);
8. 0≤α≤1.

Define `q_z = sum_z' p_z' 1{|N(E,A,M,Z_z',Y_z0)| ≥ |N(E,A,M,Z_z,Y_z0)|}`. The conclusion is `sum_z p_z 1{q_z≤α}≤α`. In particular rejection uses ≤, whereas the concrete pair rejection calculation uses <1/100.

Second, for **every**, in order, E⊆I, A, M, z, baseline:I→R, and δ∈R, assume A≥0, M and z binary, z_i=0 outside E, and both recipient denominators strictly positive. Then

`N(E,A,M,z,baseline+δz) = N(E,A,M,z,baseline)+δ N(E,A,M,z,z)`.

Third, independently of Ω and I, instantiate U,H,P,z0,y_z,S,q as in T35 and A_ij=1{j=Pi}, E=U, M≡1. For every z∈H and **every** real outcome vector y, N(U,A,1,y_z,y)=S(z,y). The schedule y_z depends only on own membership, for every pair of subsets and every unit, as in T35. It is **not** constant across all z,z'∈H and all units. Its observed nomination statistic is −1, q(z0)=1/126, and its strict 1% rejection probability under uniform H is 8/63. `pairedAlternative` is defined but does not appear in this proposition.

## SAP.P037c.T27

An unconditional conjunction about twelve units J={0,…,3}×{0,1,2}. Write i=(k,j), x_i=k+j, y_i(d)=(2 if d=3, else 1)x_i, D0_i=k, and y_i=y_i(k).

The six-school construction is as follows. Units (0,j) are focal student 6 in schools j=0,1,2; units (k,j) with k>0 are focal student 6+j in school k+2. School sizes are 7 for schools 0,1,2 and 9 for schools 3,4,5. All students are the dependent disjoint union of these six finite schools. Directed nominations within a school are i→0 and i→2 for i≥6, together with 4→0 and 5→0. Indegree counts all incoming nominations. Sort the indegrees ascending; with h=9(N−1), q=h div 10 and r=h mod 10, the school threshold is (10−r)/10 times sorted[q] plus r/10 times sorted[q+1]. Lookup defaults are zero, although all these concrete indices are in range.

Each school's two Boolean seed bits select exactly one of {0,1} and exactly one of {2,3}: first bit true selects 0, false selects 1; second true selects 2, false selects 3. An assignment is a three-element school subset H⊆{0,…,5} and six independently indexed pairs of bits. Each such assignment has mass 1/(20·4^6). For any student u, exposure is 0 if its school is outside H, otherwise 4 if u is a seed, otherwise 3 if u is adjacent in either direction to a seed whose indegree is strictly above threshold, otherwise 2 if adjacent to any seed, otherwise 1. Marginal probabilities π_u(d) are the finite sum of this mass over assignments yielding d.

The design certificate asserts:

1. Every school's indegrees are N−4 at student 0, N−6 at student 2, and zero elsewhere. Thresholds are 9/5 in size-7 schools and 17/5 in size-9 schools; **for every** school and student, being strictly above threshold is equivalent to being student 0.
2. **For every** school and bit pair, its seed set has size two and contains exactly one member of each of the two specified strata. The focal-student map from J into all students is injective.
3. **For every** school subset (not only subsets of size three), bit assignment and focal unit, focal exposure is 0 outside the selected schools; inside it is 3 when the first bit is true, otherwise 2 when the second is true, otherwise 1. This agrees with the full student exposure definition.
4. **For every** focal i and d∈{0,1,2,3}, π_i(d)=(1/2,1/8,1/8,1/4)_d. **For every** student u, all four of these probabilities lie strictly between zero and one if and only if u is one of the twelve focal students.
5. Summing assignment mass over bit assignments, with selected school set fixed to {3,4,5}, the event that **all** focal units i=(k,j) have exposure k has probability 1/640. This is a joint assignment event, including the probability of that selected school set, not a conditional probability given the set.

For a category weight vector v, let β_v=(v0+v1+v2+2v3)/(sum_k v_k) and B_v=(1−β_v,2−2β_v,3−3β_v,8−4β_v,β_v). Let m_v(k)=(B_v)_k+(5/2)(B_v)_4. For **each** v in the two-element set {(4,4,4,4),(2,8,8,4)}, the theorem states:

* The four separate category regressions have minimizing coefficients (0,1) for k<3 and (0,2) for k=3, using weights 1{D0_i=k}v_k. For **every** b∈R^5, Min(v_D0,X(D0,x),y,b) holds if and only if b=B_v.
* For **every** category k the weighted residual sum in that category is zero, and the weighted sum of x_i times pooled residuals over all twelve units is zero.
* The separate augmented mean Aug(D0,v_D0,y,(2 if k=3 else 1)x;k) is 5/2 for k<3 and 5 for k=3; its category-3 minus category-2 contrast is 5/2.

Further, the population mean of x is 5/2; B_(4,4,4,4)=(−1/4,−1/2,−3/4,3,5/4), with m=(23/8,21/8,19/8,49/8), and B_(2,8,8,4)=(−2/11,−4/11,−6/11,36/11,13/11), with m=(61/22,57/22,53/22,137/22). The pooled category-3 minus category-2 contrasts are respectively 15/4 and 42/11, both unequal to 5/2, with discrepancies 5/4 and 29/22. **For every** category the population average of y_i(d) equals its stated separate mean; **for every** i the separate observed residual is zero. Finally, **for every** focal i, 1/π_i(D0_i)=(2,8,8,4)_D0_i.

## SAP.P037c.T28

For **every** finite type I, this is a conjunction of the following independent universal statements.

First, **for every**, in order, number p of covariates, proof n=|I|>0, category map D:I→{0,1,2,3}, real vectors w,y, proof w_i>0 for all i, covariates x:I→R^p, pooled coefficients b∈R^(4+p), separate coefficients s_k∈R^(1+p), assume:

* X(D,x) has full column rank;
* **for every** k, the matrix S(x) restricted to {i:D_i=k} has full column rank;
* Min(w,X(D,x),y,b);
* **for every** k, Min(1{D_i=k}w_i,S(x),y,s_k).

Write f^P_ki=b_k+sum_j x_ij b_(4+j), and f^S_ki=s_k0+sum_j x_ij s_k,(1+j). Then **for every** k both category weighted residual sums are zero; both corresponding augmented means equal n^−1 sum_i f_ki over the same whole population I; and **for every** k,l, the difference between the pooled prediction averages is b_k−b_l.

Second, **for every**, in order, proof |I|>0, D, real w,x,y, with all w_i>0, define W_k=sum_{D_i=k}w_i, weighted means xb_k=sum_{D_i=k}w_ix_i/W_k and yb_k similarly, Sxx_k=sum_{D_i=k}w_i(x_i−xb_k)^2, Sxy_k=sum_{D_i=k}w_i(x_i−xb_k)(y_i−yb_k), b_k=Sxy_k/Sxx_k, β=sum_k Sxy_k/sum_k Sxx_k, and xbar=|I|^−1 sum_i x_i. **If every Sxx_k>0**, then:

* **for every** k and two-component coefficient vector c, Min(1{D_i=k}w_i,[1,x],y,c) iff c=(yb_k−b_k xb_k,b_k);
* **for every** five-component vector c, Min(w,X(D,x),y,c) iff c=(yb_0−βxb_0,…,yb_3−βxb_3,β);
* **for every** k, (yb_k−b_k xb_k+b_k xbar)−(yb_k−βxb_k+βxbar)=(b_k−β)(xbar−xb_k).

Third, **for every** five real numbers yb,bk,beta,xb,xbar, the same algebraic difference identity holds without statistical premises; and equality of its two means is equivalent to bk=beta **or** xbar=xb.

Fourth, **for every**, in order, p, proof |I|>0, α∈R^4, β∈R^p, x:I→R^p and k, the average over I of α_k+sum_j x_ij β_j is α_k+sum_j (|I|^−1 sum_i x_ij)β_j.

Finally, (2−5/4)(5/2−4)=−9/8 and 5−49/8=−9/8. Neither minimizing coefficients nor zero residual sums are premises of the one-covariate equivalences; the first component does take fitted minimizers as input.

## SAP.P037c.T33

This is an unconditional conjunction about eight units i=(j,l)∈{0,…,3}×{0,1}. There are 96 assignment states z=(H,b): H is one of the six unordered two-element subsets of {0,…,3}; b assigns a Boolean to each j. Let r=(1/10,1/5,3/10,2/5). State mass is (1/6) times, over j∈H, r_j if b_j=true and 1−r_j otherwise, and over j∉H, 1/2. Unit (j,0) is the indicated member if b_j=true; unit (j,1) is indicated if b_j=false. Exposure D_z is 3 for indicated members of H, 2 for the other members of H, 0 for indicated members outside H, and 1 for the others outside H.

Let c_(j,0)=r_j/2 and c_(j,1)=(1−r_j)/2. The specified marginal π_i(k) is 1/4 for k=0,1; 1/2−c_i for k=2; c_i for k=3. At the observed map D0, pairs 0,1 have exposures (3,2) and pairs 2,3 have exposures (0,1). Outcomes by pair are (0,2),(1,0),(3,1),(2,4). For **any** map D define w_i(D)=1/π_i(D_i), full design X(D,c), observed b0=L(w(D0),X(D0,c))y, m_k=b0_k+b0_4/4, and residual e=y−X(D0,c)b0. For **every** state z and outcome vector v, full contrast F_z(v) is coefficient 3 minus coefficient 2 from L(w(D_z),X(D_z,c))v; collapsed contrast G_z(v) uses just the four indicator columns. For a function f on states, V(f)=sum_z mass_z f_z^2−(sum_z mass_z f_z)^2.

The conjunction asserts:

1. There are 96 states; their masses sum to one and **every** mass is positive. **For every** z,k, exactly two units have exposure k. **For every** i,k, summing the state masses of D_z(i)=k gives π_i(k).
2. **For every** z, X(D_z,c) has full column rank; X(D0,c) does too. **For every** z the four-column collapsed design also has full column rank. **For every** map D and i, w_i(D)>0. **For every** i, π_i(2)+π_i(3)=1/2.
3. b0=(1/13,−2,−14/3,−23/39,180/13), m=(46/13,19/13,−47/39,112/39), and e by pair is (−4/39,17/39),(8/39,−34/39),(11/13,−24/13),(−11/13,24/13).
4. Put v_z(i)=y_i+m_(D_z(i))−m_(D0_i). **For every** z, F_z(v_z)=F_z(e)+m_3−m_2.
5. V(z↦F_z(e))=V(z↦F_z(v_z))=A, where

   A = 1574066925743604937750798623088231315086040632174801225920729815316988109390788379330079414475192929 / 171796363313262196427951740421954806512514436622177625713808591915692887084446808987770465290240000.

6. V(z↦G_z(e))=B=1453114769225810453/621302156766720000. Also 9<A<37/4, 2<B<5/2, and the actual full and collapsed residual contrast variances are unequal.

There is no assertion here about the shift of each individual refitted full-control exposure mean.

## SAP.P037c.T34

For **every** finite type Ω, both following universal conclusions have identical premises. Quantify, in order, naturals n,p, proof n>0, D0:{0,…,n−1}→{0,1,2,3}, D:Ω×{0,…,n−1}→{0,1,2,3}, a fixed real covariate matrix C with p columns, observed weights w0 and assignment weights w_z, proofs all those weights are positive, proof X(D0,C) has full column rank and **every** X(D_z,C) has full column rank, outcome vector y, state masses prob, proof prob_z≥0 and sum_z prob_z=1. No constraint forces the weights to be inverse probabilities.

Define b0=L(w0,X(D0,C))y; cbar_j=n^−1 sum_i C_ij; row_k=(four category indicators for category k,cbar); m_k=row_k·b0; e=y−X(D0,C)b0; v_z(i)=y_i+m_(D_z(i))−m_(D0_i); and L_z=L(w_z,X(D_z,C)). For any real random scalar f, use V(f)=sum_z prob_z f_z^2−(sum_z prob_z f_z)^2.

The first conjunct (`SameControlCertificate`) concludes:

* **for every** k,l, m_k−m_l=b0_k−b0_l;
* **for every** z, L_z X(D_z,C)=identity and L_z v_z=L_z e+b0;
* **for every** z,k, row_k·L_z v_z=row_k·L_z e+m_k;
* **for every** k,l, V(z↦(row_k−row_l)·L_z v_z)=V(z↦(row_k−row_l)·L_z e).

The second conjunct (`SameControlExtra`), with a fresh universal quantification of all the same inputs and hypotheses, concludes:

* **for every** z,i, v_z(i)=y_i−b0_(D0_i)+b0_(D_z(i));
* **for every** z, v_z=e+X(D_z,C)b0;
* **for every** k, V(z↦row_k·L_z v_z)=V(z↦row_k·L_z e).

All covariance/variance equalities concern the finite law prob on Ω. There is no fewer-control comparison in this proposition.

## SAP.P037c.T43

For **every** finite assignment type Ω and finite covariate index type K, the theorem conjoins two statements. A `FiniteDesign Ω` is a function d_z≥0 with sum_z d_z=1. It is not allowed to have zero total mass. Write E[f]=sum_z d_z f_z, inner(u,v)=sum_i u_i v_i, and ⟨u,v⟩=E[sum_i u_zi v_zi] (`cross`).

The first statement universally quantifies, in order: a natural B; a finite design d on Ω; real arrays T,C,Y on Ω×({0,…,B−1}×{0,1,2,3}); fixed covariates X_k on the 4B units; fixed real unit arrays a,η,μ; a real vector λ indexed by K; scalars p,τ0,β,τ,b; and a real vector g indexed by K. Define block demeaning Hx_(h,j)=x_(h,j)−(1/4)sum_{l=0}^3 x_(h,l). Put t_z=H(T_z), z_z=H(T_z C_z) (the latter product is componentwise), V_k=HX_k, q=⟨z,t⟩/⟨t,t⟩, and r_z=z_z−q t_z−p sum_k λ_k V_k. Its hypotheses, in order, are:

1. **for every** unit i, E[T_i]=p;
2. **for every** unit i, E[T_i C_i]=pμ_i;
3. **for every** unit i, (Hμ)_i=sum_k λ_k (HX_k)_i;
4. **for every** assignment and unit, Y_zi=a_i+T_zi(τ0+η_i+β C_zi);
5. ⟨t,t⟩≠0;
6. ⟨r,r⟩>0;
7. the **given** coefficients (τ,g,b) satisfy expected normal equations: with u_z=H(Y_z)−τt_z−sum_k g_k V_k−b z_z, one has ⟨t,u⟩=0, ⟨V_k,u⟩=0 for every k, and ⟨z,u⟩=0.

Conclusion: `b−β = ⟨r,(T_zi η_i)⟩/⟨r,r⟩`. The numerator uses the un-demeaned Tη; r itself is block-demeaned by its definition. The coefficients solving the normal equations are quantified before their equation hypothesis; their existence is not a conclusion.

The second statement universally quantifies the same inputs in the same order, omitting η, with the same first-moment, span, treatment-second-moment, positive residual-second-moment, and normal-equation hypotheses. Replace the response model by Y_zi=a_i+T_zi(τ0+βC_zi). Its conclusion is b=β.

No binary-T restriction, treatment-count restriction, p∈(0,1) condition, independence condition, or rank condition on the fixed covariates is encoded. B=0 is syntactically allowed, but the two strict/nonzero second-moment premises cannot then hold. K may be empty; Ω cannot support a finite design if empty. The theorem does not separately conclude mean-zero r or its orthogonality identities and does not contain a concrete four-state certificate.
