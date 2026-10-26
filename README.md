<!-- Generated from the audit's records; machine-readable index: catalog/index.json (schemas in catalog/schema/). -->

# llm-audit-lean

**Lean 4 formalizations from a self-audit of P. M. Aronow's published work, carried out with AI agents.**

> **Disclosure.** This repository is entirely machine-generated: its Lean code, documentation and catalog were produced by AI agents, apart from code adapted from third-party projects (Causalean, StatLean and others credited in the source files and in [NOTICE](NOTICE)). It has not undergone human review.

This repository holds Lean 4 formalizations of mathematical claims from 50 published works by P. M. Aronow and coauthors: a book, journal articles, book chapters and commentaries in statistics, causal inference and political methodology. Claims selected from the works (*targets*) were broken into components, and each credited component is a Lean theorem that proves the component as recorded, proves a corrected version of it, or proves a counterexample to the claim as recorded in its target (where the target states a specific reading of the printed text, the counterexample applies to that reading). Credit applies to a component under its stated assumptions; it does not certify a whole claim or a whole work.

Lean is a proof assistant: it checks every proof against its formal statement. Whether a formal statement faithfully captures the paper's claim was judged by AI reviewers, not by human referees, and 10 credited results assume a named published theorem as an explicit hypothesis. See [How the results were produced and checked](#how-the-results-were-produced-and-checked).

Along the way the formalization built general results that are useful in their own right, among them a combinatorial central limit theorem, Le Cam's first lemma, local asymptotic normality from quadratic mean differentiability, U-statistic limit theorems, sharp covariance bounds, unequal-probability sampling designs and identification results. A guide to them follows.

| At a glance | |
| --- | --- |
| Works with formalized claims | 50 |
| Claims with credited Lean results (targets) | 1000 |
| Credited Lean results | 4795 target–declaration pairs: 4314 proved results, 481 counterexample results |
| Results that assume a published theorem | 10, each naming the theorem it assumes |
| Lean source | 1400 library modules plus the root import module, about 463,345 lines; Lean 4.34.1 with Mathlib 4.34.1 |
| Axioms of every credited result | only `propext`, `Classical.choice` and `Quot.sound` |
| `sorry` in the source | none |
| Machine-readable index | [`catalog/index.json`](catalog/index.json) |

The counts are of target–declaration pairs (*component results*), not of distinct theorems: one theorem can serve several targets, and one target can need several theorems.

## Start here

- **Looking for a result to use or cite?** Read [the most helpful results](#the-most-helpful-results) below, then [docs/HIGHLIGHTS.md](docs/HIGHLIGHTS.md) for exact statements, hypotheses and relations to Mathlib.
- **Interested in one paper?** [docs/works/](docs/works/README.md) has a page for each work: an overview, its key results, its corrections, and every target with its Lean results.
- **Using the Lean code?** See [Using the Lean code](#using-the-lean-code).
- **Writing a script, or an AI agent?** Start at [`catalog/index.json`](catalog/index.json); see [Machine-readable files](#machine-readable-files).
- **Deciding how far to rely on a result?** Read [What the labels mean](#what-the-labels-mean) and [How the results were produced and checked](#how-the-results-were-produced-and-checked).

## The most helpful results

The 25 results below were selected from the whole development for their generality and their likely use beyond the papers they were written for. Many are supporting lemmas, stated without any paper-specific objects. The full guide, [docs/HIGHLIGHTS.md](docs/HIGHLIGHTS.md), gives the exact statement of each, its hypotheses, how it relates to Mathlib, and companion declarations.

| Rank | Result | Use |
| --- | --- | --- |
| 1 | [Combinatorial central limit theorem for permutation arrays](docs/HIGHLIGHTS.md#h001) | Uniform permutation sums of doubly centered arrays have a standard normal limit when normalized entries vanish. |
| 2 | [Lindeberg CLT on changing probability spaces](docs/HIGHLIGHTS.md#h002) | Independent centered triangular arrays converge to the standard normal law under variance normalization and the Lindeberg condition. |
| 3 | [Le Cam’s first lemma, four equivalent forms](docs/HIGHLIGHTS.md#h003) | Contiguity is equivalent to transfer of negligible statistics and two subsequential likelihood-ratio criteria under mutual absolute continuity. |
| 4 | [One-sided nondominated QMD gives score regularity and a local likelihood expansion](docs/HIGHLIGHTS.md#h004) | One-sided quadratic-mean differentiability yields a centered square-integrable score and a local likelihood expansion without a common dominator. |
| 5 | [Scalar outer Hadamard delta method](docs/HIGHLIGHTS.md#h005) | Tangential Hadamard differentiability transfers outer weak convergence to a scalar limit and controls the actual linearization remainder. |
| 6 | [Attained Fréchet covariance bounds for square-integrable marginals](docs/HIGHLIGHTS.md#h006) | Quantile couplings attain the largest and smallest covariances compatible with two square-integrable marginal laws. |
| 7 | [Order-two U-statistic CLT under only second moments](docs/HIGHLIGHTS.md#h007) | Centered symmetric pairwise averages have a Gaussian limit under square integrability, including zero projection variance. |
| 8 | [Nearest positive-semidefinite matrix in Frobenius norm](docs/HIGHLIGHTS.md#h008) | Clipping negative eigenvalues gives a Frobenius projection inequality that yields the unique nearest positive-semidefinite matrix. |
| 9 | [Exponential tilting of possibly singular Gaussian laws](docs/HIGHLIGHTS.md#h009) | A normalized linear exponential tilt shifts a finite-dimensional Gaussian mean by its covariance times the tilt vector. |
| 10 | [Hellinger error tensorization for product experiments](docs/HIGHLIGHTS.md#h010) | The square-root density error for independent repeated observations grows at most with the square root of sample size. |
| 11 | [Multivariate iid CLT allowing singular covariance](docs/HIGHLIGHTS.md#h011) | Sums of centered iid vectors with finite second moments converge after square-root normalization to a Gaussian law with the specified covariance, which may be singular. |
| 12 | [Sharp bounded-weight means with explicit threshold optimizers](docs/HIGHLIGHTS.md#h012) | Threshold weights attain the extreme bounded-weight means, and feasible weights attain every value between them. |
| 13 | [Causal IPW and double-robust identification](docs/HIGHLIGHTS.md#h013) | Identifies the average treatment effect by inverse weighting and gives the two alternatives for double robustness. |
| 14 | [MAR reweighting identifies the entire outcome law](docs/HIGHLIGHTS.md#h014) | Shows that inverse-response weighting recovers the entire outcome distribution under missingness at random. |
| 15 | [Quadratic-form sampling bound for doubly centered matrices](docs/HIGHLIGHTS.md#h015) | Bounds the variance of a principal matrix sum under sampling without replacement when every row and column sums to zero. |
| 16 | [Conservative HT contrast variance with zero joint exposure probabilities](docs/HIGHLIGHTS.md#h016) | Bounds the design variance of an exposure contrast by the expectation of a zero-joint-corrected variance estimator. |
| 17 | [Exact HC2 conservativeness gap and equality condition](docs/HIGHLIGHTS.md#h017) | Gives the exact expected HC2 variance gap and characterizes equality by constant treatment effects. |
| 18 | [Exact prediction-covariance bias of regression-assisted contrasts](docs/HIGHLIGHTS.md#h018) | Expresses regression-assisted contrast bias exactly through covariances of treatment indicators and fitted predictions. |
| 19 | [Sharp ATE interval with unchanged observable law](docs/HIGHLIGHTS.md#h019) | Constructs every bounded-outcome average treatment effect compatible with the same observed outcome and treatment law. |
| 20 | [Exchangeable Monte Carlo p-values, with ties and floor bounds](docs/HIGHLIGHTS.md#h020) | Establishes finite-sample validity of corrected exchangeable Monte Carlo tails and their doubled minimum. |
| 21 | [Dense quadratic variance bound under a genuine dependency graph](docs/HIGHLIGHTS.md#h021) | Bounds the variance of dense quadratic forms of centered bounded variables with a dependency graph. |
| 22 | [Exactly which means nonnegative reweighting can represent](docs/HIGHLIGHTS.md#h022) | Characterizes attainable nonnegative weighted means by an atom at the target or positive probability on both sides. |
| 23 | [Fixed-size systematic sampling with prescribed inclusion probabilities](docs/HIGHLIGHTS.md#h023) | Systematic sampling realizes any strictly positive admissible inclusion vector with an exactly fixed sample size. |
| 24 | [Unknown-propensity impossibility for arbitrary randomized procedures](docs/HIGHLIGHTS.md#h024) | With unrestricted measurable propensity and outcome-regression classes, no procedure, even a randomized one, estimates the average treatment effect uniformly or gives uniformly honest intervals that shrink. |
| 25 | [Exact dyadic sandwich decomposition with repeated dyads](docs/HIGHLIGHTS.md#h025) | A finite-sum identity decomposes the dyadic sandwich exactly when dyads may repeat. |

The full guide describes 71 results in five sections; a result can appear in more than one:

- [The most helpful results](docs/HIGHLIGHTS.md#the-most-helpful-results): 25 results.
- [Reusable libraries](docs/HIGHLIGHTS.md#reusable-libraries): 35 results.
- [Counterexamples and corrections](docs/HIGHLIGHTS.md#counterexamples-and-corrections): 10 results.
- [Candidates for Mathlib](docs/HIGHLIGHTS.md#candidates-for-mathlib): 27 results.
- [Further useful results](docs/HIGHLIGHTS.md#further-useful-results): 24 results.

### By area

| Area | Highlights |
| --- | --- |
| Probability | [H001](docs/HIGHLIGHTS.md#h001), [H002](docs/HIGHLIGHTS.md#h002), [H003](docs/HIGHLIGHTS.md#h003), [H004](docs/HIGHLIGHTS.md#h004), [H005](docs/HIGHLIGHTS.md#h005), [H006](docs/HIGHLIGHTS.md#h006), [H007](docs/HIGHLIGHTS.md#h007), [H009](docs/HIGHLIGHTS.md#h009), [H010](docs/HIGHLIGHTS.md#h010), [H011](docs/HIGHLIGHTS.md#h011), [H014](docs/HIGHLIGHTS.md#h014), [H015](docs/HIGHLIGHTS.md#h015), [H020](docs/HIGHLIGHTS.md#h020), [H021](docs/HIGHLIGHTS.md#h021), [H022](docs/HIGHLIGHTS.md#h022), [H026](docs/HIGHLIGHTS.md#h026), [H027](docs/HIGHLIGHTS.md#h027), [H028](docs/HIGHLIGHTS.md#h028), [H030](docs/HIGHLIGHTS.md#h030), [H031](docs/HIGHLIGHTS.md#h031), [H032](docs/HIGHLIGHTS.md#h032), [H035](docs/HIGHLIGHTS.md#h035), [H036](docs/HIGHLIGHTS.md#h036), [H040](docs/HIGHLIGHTS.md#h040), [H042](docs/HIGHLIGHTS.md#h042), [H043](docs/HIGHLIGHTS.md#h043), [H046](docs/HIGHLIGHTS.md#h046), [H050](docs/HIGHLIGHTS.md#h050), [H051](docs/HIGHLIGHTS.md#h051), [H061](docs/HIGHLIGHTS.md#h061), [H065](docs/HIGHLIGHTS.md#h065), [H066](docs/HIGHLIGHTS.md#h066), [H069](docs/HIGHLIGHTS.md#h069), [H071](docs/HIGHLIGHTS.md#h071) |
| Asymptotic statistics | [H002](docs/HIGHLIGHTS.md#h002), [H003](docs/HIGHLIGHTS.md#h003), [H004](docs/HIGHLIGHTS.md#h004), [H005](docs/HIGHLIGHTS.md#h005), [H007](docs/HIGHLIGHTS.md#h007), [H009](docs/HIGHLIGHTS.md#h009), [H010](docs/HIGHLIGHTS.md#h010), [H011](docs/HIGHLIGHTS.md#h011), [H024](docs/HIGHLIGHTS.md#h024), [H027](docs/HIGHLIGHTS.md#h027), [H028](docs/HIGHLIGHTS.md#h028), [H029](docs/HIGHLIGHTS.md#h029), [H030](docs/HIGHLIGHTS.md#h030), [H032](docs/HIGHLIGHTS.md#h032), [H035](docs/HIGHLIGHTS.md#h035), [H038](docs/HIGHLIGHTS.md#h038), [H039](docs/HIGHLIGHTS.md#h039), [H041](docs/HIGHLIGHTS.md#h041), [H047](docs/HIGHLIGHTS.md#h047), [H049](docs/HIGHLIGHTS.md#h049), [H050](docs/HIGHLIGHTS.md#h050), [H053](docs/HIGHLIGHTS.md#h053), [H060](docs/HIGHLIGHTS.md#h060), [H061](docs/HIGHLIGHTS.md#h061), [H065](docs/HIGHLIGHTS.md#h065), [H066](docs/HIGHLIGHTS.md#h066), [H068](docs/HIGHLIGHTS.md#h068), [H071](docs/HIGHLIGHTS.md#h071) |
| Randomization inference | [H001](docs/HIGHLIGHTS.md#h001), [H017](docs/HIGHLIGHTS.md#h017), [H018](docs/HIGHLIGHTS.md#h018), [H020](docs/HIGHLIGHTS.md#h020), [H026](docs/HIGHLIGHTS.md#h026), [H045](docs/HIGHLIGHTS.md#h045), [H049](docs/HIGHLIGHTS.md#h049) |
| Experimental design and estimation | [H015](docs/HIGHLIGHTS.md#h015), [H016](docs/HIGHLIGHTS.md#h016), [H017](docs/HIGHLIGHTS.md#h017), [H018](docs/HIGHLIGHTS.md#h018), [H023](docs/HIGHLIGHTS.md#h023), [H033](docs/HIGHLIGHTS.md#h033), [H034](docs/HIGHLIGHTS.md#h034), [H045](docs/HIGHLIGHTS.md#h045), [H047](docs/HIGHLIGHTS.md#h047), [H051](docs/HIGHLIGHTS.md#h051), [H054](docs/HIGHLIGHTS.md#h054), [H067](docs/HIGHLIGHTS.md#h067), [H068](docs/HIGHLIGHTS.md#h068) |
| Survey sampling | [H012](docs/HIGHLIGHTS.md#h012), [H015](docs/HIGHLIGHTS.md#h015), [H023](docs/HIGHLIGHTS.md#h023), [H032](docs/HIGHLIGHTS.md#h032), [H033](docs/HIGHLIGHTS.md#h033), [H048](docs/HIGHLIGHTS.md#h048), [H049](docs/HIGHLIGHTS.md#h049), [H054](docs/HIGHLIGHTS.md#h054), [H063](docs/HIGHLIGHTS.md#h063) |
| Interference and networks | [H007](docs/HIGHLIGHTS.md#h007), [H016](docs/HIGHLIGHTS.md#h016), [H021](docs/HIGHLIGHTS.md#h021), [H025](docs/HIGHLIGHTS.md#h025), [H033](docs/HIGHLIGHTS.md#h033), [H041](docs/HIGHLIGHTS.md#h041), [H047](docs/HIGHLIGHTS.md#h047), [H051](docs/HIGHLIGHTS.md#h051), [H064](docs/HIGHLIGHTS.md#h064) |
| Causal identification | [H013](docs/HIGHLIGHTS.md#h013), [H014](docs/HIGHLIGHTS.md#h014), [H019](docs/HIGHLIGHTS.md#h019), [H022](docs/HIGHLIGHTS.md#h022), [H024](docs/HIGHLIGHTS.md#h024), [H039](docs/HIGHLIGHTS.md#h039), [H044](docs/HIGHLIGHTS.md#h044), [H048](docs/HIGHLIGHTS.md#h048), [H052](docs/HIGHLIGHTS.md#h052), [H053](docs/HIGHLIGHTS.md#h053), [H055](docs/HIGHLIGHTS.md#h055), [H056](docs/HIGHLIGHTS.md#h056), [H059](docs/HIGHLIGHTS.md#h059), [H060](docs/HIGHLIGHTS.md#h060), [H070](docs/HIGHLIGHTS.md#h070) |
| Partial identification and bounds | [H006](docs/HIGHLIGHTS.md#h006), [H012](docs/HIGHLIGHTS.md#h012), [H019](docs/HIGHLIGHTS.md#h019), [H022](docs/HIGHLIGHTS.md#h022), [H036](docs/HIGHLIGHTS.md#h036), [H052](docs/HIGHLIGHTS.md#h052), [H055](docs/HIGHLIGHTS.md#h055), [H063](docs/HIGHLIGHTS.md#h063), [H064](docs/HIGHLIGHTS.md#h064), [H070](docs/HIGHLIGHTS.md#h070) |
| Regression and variance estimation | [H008](docs/HIGHLIGHTS.md#h008), [H016](docs/HIGHLIGHTS.md#h016), [H017](docs/HIGHLIGHTS.md#h017), [H018](docs/HIGHLIGHTS.md#h018), [H021](docs/HIGHLIGHTS.md#h021), [H025](docs/HIGHLIGHTS.md#h025), [H034](docs/HIGHLIGHTS.md#h034), [H035](docs/HIGHLIGHTS.md#h035), [H037](docs/HIGHLIGHTS.md#h037), [H041](docs/HIGHLIGHTS.md#h041), [H042](docs/HIGHLIGHTS.md#h042), [H043](docs/HIGHLIGHTS.md#h043), [H044](docs/HIGHLIGHTS.md#h044), [H046](docs/HIGHLIGHTS.md#h046), [H053](docs/HIGHLIGHTS.md#h053), [H057](docs/HIGHLIGHTS.md#h057), [H058](docs/HIGHLIGHTS.md#h058), [H067](docs/HIGHLIGHTS.md#h067), [H068](docs/HIGHLIGHTS.md#h068) |
| Resampling | [H020](docs/HIGHLIGHTS.md#h020), [H029](docs/HIGHLIGHTS.md#h029), [H038](docs/HIGHLIGHTS.md#h038), [H039](docs/HIGHLIGHTS.md#h039), [H058](docs/HIGHLIGHTS.md#h058), [H069](docs/HIGHLIGHTS.md#h069) |
| Optimization and computation | [H008](docs/HIGHLIGHTS.md#h008), [H012](docs/HIGHLIGHTS.md#h012), [H062](docs/HIGHLIGHTS.md#h062) |
| Foundations | [H005](docs/HIGHLIGHTS.md#h005), [H008](docs/HIGHLIGHTS.md#h008), [H025](docs/HIGHLIGHTS.md#h025), [H031](docs/HIGHLIGHTS.md#h031), [H037](docs/HIGHLIGHTS.md#h037), [H040](docs/HIGHLIGHTS.md#h040) |

## Find a result

### By paper

[Browse the guide by work](docs/works/README.md): one page per work, with an overview, key results, corrections, and a table of every target and its Lean results.

<details>
<summary>All works, with counts</summary>

| Work | Title | Targets | Credited results |
| --- | --- | --- | --- |
| [P001](docs/works/P001.md) | Foundations of Agnostic Statistics | 128 | 301 |
| [P002](docs/works/P002.md) | Randomization-based confidence sets for the local average treatment effect | 30 | 124 |
| [P003](docs/works/P003.md) | Fast computation of exact confidence intervals for randomized experiments with binary outcomes | 35 | 112 |
| [P004](docs/works/P004.md) | Design-Based Inference for Spatial Experiments under Unknown Interference | 43 | 126 |
| [P005](docs/works/P005.md) | Exact Bias Correction for Linear Adjustment of Randomized Controlled Trials | 27 | 94 |
| [P006](docs/works/P006.md) | On Counterfactual Metrics for Social Welfare: Incentives, Ranking, and Information Asymmetry | 30 | 94 |
| [P007](docs/works/P007.md) | Listwise Deletion in High Dimensions | 17 | 61 |
| [P008](docs/works/P008.md) | Inference in Spatial Experiments with Interference using the SpatialEffect Package | 28 | 162 |
| [P009](docs/works/P009.md) | Average treatment effects in the presence of unknown interference | 51 | 121 |
| [P010](docs/works/P010.md) | A Note on Dropping Experimental Subjects who Fail a Manipulation Check | 23 | 41 |
| [P011](docs/works/P011.md) | Confidence Intervals for Linear Unbiased Estimators under Constrained Dependence | 41 | 134 |
| [P012](docs/works/P012.md) | Identification of homophily and preferential recruitment in respondent-driven sampling | 24 | 128 |
| [P013](docs/works/P013.md) | Estimating Average Causal Effects Under General Interference, with Application to a Social Network Experiment | 27 | 255 |
| [P014](docs/works/P014.md) | The Regression Discontinuity Design under Interference: A Local Randomization-Based Approach | 10 | 75 |
| [P015](docs/works/P015.md) | Does Regression Produce Representative Estimates of Causal Effects? | 24 | 140 |
| [P016](docs/works/P016.md) | Research Note: A More Powerful Test Statistic for Reasoning about Interference between Units | 21 | 91 |
| [P017](docs/works/P017.md) | Data-Adaptive Causal Effects and Superefficiency | 16 | 61 |
| [P018](docs/works/P018.md) | Cluster-Robust Variance Estimation for Dyadic Data | 28 | 126 |
| [P019](docs/works/P019.md) | Combining List Experiment and Direct Question Estimates of Sensitive Behavior Prevalence | 22 | 78 |
| [P020](docs/works/P020.md) | Unbiased Estimation of the Average Treatment Effect in Cluster-Randomized Experiments | 17 | 127 |
| [P021](docs/works/P021.md) | Nonparametric Identification for Respondent-Driven Sampling | 2 | 2 |
| [P022](docs/works/P022.md) | Sharp bounds on the variance in randomized experiments | 18 | 70 |
| [P023](docs/works/P023.md) | A Note on Close Elections and Regression Analysis of the Party Incumbency Advantage | 12 | 47 |
| [P024](docs/works/P024.md) | Field Experimental Designs for the Study of Media Effects | 8 | 87 |
| [P025](docs/works/P025.md) | Interval Estimation of Population Means under Unknown but Bounded Probabilities of Sample Selection | 21 | 133 |
| [P026](docs/works/P026.md) | A Class of Unbiased Estimators of the Average Treatment Effect in Randomized Experiments | 24 | 130 |
| [P027](docs/works/P027.md) | Conservative Variance Estimation for Sampling Designs with Zero Pairwise Inclusion Probabilities | 22 | 152 |
| [P028](docs/works/P028.md) | Sharp Bounds for Complier Average Potential Outcomes in Experiments with Noncompliance and Incomplete Reporting | 10 | 102 |
| [P029](docs/works/P029.md) | Beyond LATE: Estimation of the Average Treatment Effect with an Instrumental Variable | 26 | 134 |
| [P030](docs/works/P030.md) | A General Method for Detecting Interference Between Units in Randomized Experiments | 15 | 93 |
| [P031](docs/works/P031.md) | On Equivalencies Between Design-Based and Regression-Based Variance Estimators for Randomized Experiments | 11 | 12 |
| [P032](docs/works/P032.md) | Dyadic Clustering in International Relations | 12 | 129 |
| [P033](docs/works/P033.md) | On the reliability of published findings using the regression discontinuity design in political science | 18 | 15 |
| [P034](docs/works/P034.md) | The Negative Consequences of Informing Voters about Deepfakes: Evidence from Two Survey Experiments | 5 | 5 |
| [P035](docs/works/P035.md) | The Effect of Images of Michelle Obama's Face on Trick-or-Treaters' Dietary Choices: A Randomized Control Trial | 3 | 2 |
| [P036](docs/works/P036.md) | Information and Access to United Nations Diplomatic Missions | 2 | 56 |
| [P037](docs/works/P037.md) | Changing Climates of Conflict: A Social Network Experiment in 56 Schools | 43 | 192 |
| [P038](docs/works/P038.md) | Driving Fatalities on US Presidential Election Days: A Reanalysis | 1 | 1 |
| [P039](docs/works/P039.md) | Ideologically Extreme Candidates in U.S. Presidential Elections, 1948-2012 | 7 | 58 |
| [P040](docs/works/P040.md) | Chocolate Scents and Product Sales: A Randomized Controlled Trial in a Canadian Bookstore and Cafe | 5 | 98 |
| [P041](docs/works/P041.md) | Editorial Bias in Crowd-Sourced Political Information | 13 | 51 |
| [P042](docs/works/P042.md) | Field Experiments and the Study of Voter Turnout | 6 | 74 |
| [P043](docs/works/P043.md) | Does Knowledge of Constitutional Principles Increase Support for Civil Liberties? Results from a Randomized Field Experiment | 6 | 5 |
| [P044](docs/works/P044.md) | Estimating Causal Effects in Experiments with Network Spillovers | 13 | 118 |
| [P045](docs/works/P045.md) | Spillover Effects in Experimental Data | 32 | 98 |
| [P046](docs/works/P046.md) | Nonparametric identification is not enough, but randomized controlled trials are | 10 | 123 |
| [P047](docs/works/P047.md) | Rejoinder: Nonparametric Identification Is Not Enough, but Randomized Controlled Trials Are | 3 | 70 |
| [P053](docs/works/P053.md) | Understanding Ding's Apparent Paradox | 8 | 115 |
| [P054](docs/works/P054.md) | Policy Misperceptions and Support for Gun Control Legislation | 2 | 2 |
| [P061](docs/works/P061.md) | On the Foundations of the Design-Based Approach | 21 | 170 |

</details>

### By claim or Lean name

Every target has an identifier `PNNN-Tk` (work `PNNN`, target `k`), and every Lean result has a fully qualified name. [`catalog/results.jsonl`](catalog/results.jsonl) has one line per credited component result, with its file and line. For example, in Python:

```python
import json
rows = [json.loads(line) for line in open("catalog/results.jsonl")]
for r in rows:
    if r["target_id"] == "P011-T13":
        print(r["status"], r["lean_name"], f'{r["file"]}#L{r["line"]}')
```

or with `jq`:

```sh
jq -c 'select(.target_id == "P011-T13") | {status, lean_name, file, line}' catalog/results.jsonl
```

To find a declaration by name in the source: `grep -rn "theorem lindeberg_clt" AronowAudit`.

## What the labels mean

A **target** is one claim selected from a work: a theorem, a proposition, a printed example, or a statement touched by an error the audit found. A target can need several Lean results, one per component; each pairing of a target with a Lean declaration is a **component result**, and it is the unit counted above. A credited component result establishes that component, not necessarily the whole printed claim.

In the table below, rows classify targets by kind and columns classify their component results by status. A proved component of a `counterexample` or `corrected_statement` target proves part of the target's recorded statement (a corrected claim, or a step of a counterexample), not the printed claim.

| Target kind | Proved results | Counterexample results |
| --- | --- | --- |
| `headline_result` | 936 | 12 |
| `result_touched_by_finding` | 86 | 77 |
| `counterexample` | 949 | 371 |
| `corrected_statement` | 2343 | 21 |

- **proved**: the Lean declaration proves the component under its stated assumptions (for a corrected statement, the corrected version); an AI review judged the statement a faithful rendering of the component.
- **counterexample proved**: the Lean declaration belongs to a refutation of the claim as recorded in its target, under its stated assumptions: it proves the counterexample itself (for example an explicit instance) or a step of it. Where the target states a specific reading of the printed text, the refutation applies to that reading.
- **corrected statement**: the Lean result proves a corrected, narrower or alternative formulation of the claim. The work's page explains how it differs from the printed claim and whether the printed claim itself is refuted.
- **conditional**: the statement assumes a published theorem as an explicit hypothesis, named in the statement and in the catalog. 10 credited results are conditional; all others assume only what they state mathematically.
- **helper**: a supporting declaration with no claim of its own. Many highlights are helpers: proved in Lean, but they do not by themselves settle any paper claim.

A credited result does not certify a whole paper, does not certify the parts of a claim that were not formalized, and does not replace reading its statement: the Lean statement, not the paper's wording, is what is proved. [docs/GLOSSARY.md](docs/GLOSSARY.md) defines the terms used in this repository.

## Using the Lean code

The project is pinned to Lean 4.34.1 and Mathlib 4.34.1 (commit `d13f23b723b8a846827a245b89c10fc7d3f11612`), by `lean-toolchain` and `lake-manifest.json`. Install Lean through [elan](https://github.com/leanprover/elan), then, from the repository root:

```sh
lake exe cache get                                       # prebuilt Mathlib
lake build AronowAudit.Shared.MapTailB.PermutationArray  # one module and its imports
```

A module's name is its path with `/` replaced by `.` and `.lean` removed, so `AronowAudit/P037/P037_VaryingLindeberg.lean` is imported as `import AronowAudit.P037.P037_VaryingLindeberg`. Module paths and declaration namespaces can differ: that module contains `AronowAudit.P037.LindebergCompletion.lindeberg_clt`, so use the fully qualified names given in the guide and the catalog. `lake build` alone builds all 1400 library modules (through the root module `AronowAudit`; a long build).

Some large modules (the book, `P001`, in particular) collect many results in one file; the catalog's line numbers locate each declaration.

### Reading a Lean statement

In `theorem name (x : X) (h : P x) : Q x := by ...`, `x` is an input, `h` is a hypothesis and `Q x` is the conclusion; the proof follows `:=`. Arguments in braces, `{x : X}`, are inferred by Lean, and arguments in square brackets, `[C X]`, are structures or assumptions supplied by Lean's typeclass system (for example a measurable space, or a probability measure). Hypotheses can also be packed into definitions that the statement uses, so read those definitions too. Each entry of [docs/HIGHLIGHTS.md](docs/HIGHLIGHTS.md) states its declaration's hypotheses and conclusion in mathematical notation, which is a good place to start.

### From another Lake project

A Lake project on the same Lean and Mathlib versions can depend on this repository. Add to its `lakefile.toml`, with the full commit hash of the version you want:

```toml
[[require]]
name = "AronowAudit"
git = "https://github.com/pmaronow/llm-audit-lean"
rev = "<full commit hash>"
```

then run `lake update AronowAudit` and import the modules you need. This recipe follows Lake's documentation; it has not been tested against this repository.

## Checking the repository

`python3 scripts/check_repository.py` (Python 3.10 or later, no other dependencies) checks that every catalog entry points at its declaration in the source, that the catalog matches its schemas, and that every repository-relative link and line anchor in the documentation resolves (external URLs are not checked); it runs in continuous integration. After an intentional change to the sources or documentation, `python3 scripts/check_repository.py --refresh-index` rebuilds the inventory in `catalog/index.json`. When publishing the companion website, `python3 scripts/check_repository.py --website-root ../llm-audit` also compares every target ID and complete description against the website exports. Regenerate the website from this catalog after any description change, then use the website’s `scripts/prepare_publication.py` to validate both repositories before staging the publication artifact. The finite-design regression tests in `scripts/test_p045_design_assumptions.py` enumerate dependent assignments to show why P045’s independence assumptions are necessary. After building the project, `python3 scripts/print_axioms.py` writes a Lean file that prints the axioms of every credited declaration (or of one work's, with `--work PNNN`) and checks that each uses only `propext`, `Classical.choice` and `Quot.sound`.

## Machine-readable files

| File | Contents |
| --- | --- |
| [`catalog/index.json`](catalog/index.json) | Repository, toolchain, counts, vocabularies, file sizes and source-location coverage |
| [`catalog/results.jsonl`](catalog/results.jsonl) | One record per credited target–declaration pair |
| [`catalog/works.json`](catalog/works.json) | Public metadata and counts for the works with Lean results |
| [`catalog/highlights.json`](catalog/highlights.json) | Curated highlights with verified source locations and axioms |

Per-work detail is in `catalog/works/PNNN.json`, listed in [`catalog/index.json`](catalog/index.json) and linked from each [work page](docs/works/README.md); its schema is [`catalog/schema/work.schema.json`](catalog/schema/work.schema.json). The per-work files list every target of the work (1021 in all); the 21 targets without a credited result were excluded without proof credit and are marked `"credited": false`.

Identifiers are stable: works `PNNN`, targets `PNNN-Tk`, highlights `Hnnn`, and fully qualified Lean names. A component result is identified by the triple (work, target, Lean name).

## How the results were produced and checked

**Who wrote it.** The Lean code, the statement reviews and this documentation were produced by AI agents (Anthropic Claude models and OpenAI Codex models) working under P. M. Aronow's direction; adapted third-party code is attributed in [NOTICE](NOTICE). P. M. Aronow directed the work, set its scope and decided contested cases; the repository itself has not undergone human review.

**Proofs.** Every credited result compiles in this project and depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The source contains no `sorry`. `scripts/print_axioms.py` regenerates the axiom check.

**Statements.** A proof is only as good as its statement. In the audit, each credited statement was reviewed for fidelity by an AI reviewer that translated the Lean statement back into mathematics without seeing the paper, and the translation was compared with the claim; the review records are not part of this repository. These are AI reviews, not human ones; before relying on a result, compare its Lean statement and the definitions it uses with the claim.

**What is here.** This repository contains the Lean declarations that the credited results and the highlighted lemmas need, with their documentation.

## Repository layout

| Path | Contents |
| --- | --- |
| `AronowAudit/` | The Lean library: `PNNN/` per work, `Shared/` shared results, `Literature/` results from the literature, `External/` adapted third-party code (see [NOTICE](NOTICE)) |
| `docs/` | The guide: [HIGHLIGHTS.md](docs/HIGHLIGHTS.md), [works/](docs/works/README.md), [GLOSSARY.md](docs/GLOSSARY.md) |
| `catalog/` | Machine-readable index of every credited result, with JSON schemas |
| `scripts/` | `check_repository.py` and `print_axioms.py` |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | The Lake project and its pinned versions |

## License and citation

Original code and documentation are released under the [Apache License 2.0](LICENSE). `AronowAudit/External/` contains code adapted from the Causalean project (Apache License 2.0) and the StatLean project; some modules elsewhere adapt code from these and other projects listed in [NOTICE](NOTICE), as their source comments state. StatLean's source files state that they are released under the Apache 2.0 license as described in StatLean's LICENSE file, which is reproduced verbatim in `AronowAudit/External/StatLean/LICENSE` and `AronowAudit/P037/LICENSE-StatLean.txt`. Two files in `AronowAudit/P018/Wave1/Gap/` include code adapted from earlier work by P. M. Aronow and Patrick Lopatto under the MIT License, whose notice they retain. See [NOTICE](NOTICE).

P. M. Aronow (2026). *llm-audit-lean: Lean formalizations from a self-audit.* https://github.com/pmaronow/llm-audit-lean.

Citation metadata is in [CITATION.cff](CITATION.cff). To cite one result, add its highlight ID if it has one, its fully qualified Lean name and its source path, and pin the source to a commit (GitHub's "Copy permalink" at the declaration gives such a link). Include the target ID when the result has one; helpers may have none. When attributing a result of a paper, cite the paper as well.
