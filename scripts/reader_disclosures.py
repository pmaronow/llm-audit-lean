"""Plain-language scope disclosures bound to unchanged source explanations.

The original restrictions, omissions and decisions remain in the source metadata.
This module changes only their reader-facing wording.
"""

import hashlib


DISCLOSURES = {
    "P001-T15": {
        "source_sha256": "1d510c79941889bbd5ea322cc178f61ab0761ee724e605a74481c27e62f68036",
        "text": "Only the displayed mathematical matching example is stated: true-score bootstrap failure and consistency of the estimated intercept. Adds finite second-moment premises for the statistic and bootstrap variance. Does not refute the literal hedged footnote or the reported numbers. Omits the estimated-score statistic failure, score-match equalities, explicit design admissibility predicates, root-n tightness, gap decomposition and standard-error conclusion."
    },
    "P001-T105": {
        "source_sha256": "aa2cbeb8f7536eced1054c4a44d56f5b68f8c7335ef0c2f1de59d5d3b3f11f3c",
        "text": "The available supporting result negates a larger structural-rule statement with arbitrary real treatment and no predicate for the printed informational-completeness premise. Its stated theorem does not establish an admissible refutation of the printed binary-treatment implication. Facts proved only inside its proof, or in separately unassigned results, do not strengthen that stated theorem."
    },
    "P001-T120": {
        "source_sha256": "cc6eda07aa807a5d247f83b499494d5571941c9f40e2ade3c0e9b0f043a4e8ac",
        "text": "The available counterexample drops the true-model premise carried by canonical Definitions 5.2.1–5.2.2. Its misspecified Bernoulli witness fails that premise; neither a positive result nor a refutation under the canonical premises is established."
    },
    "P004-T36": {
        "source_sha256": "9f5089edf9c45d5c8353a2e70c9a24eaa51c21e08b6966c7eea999411ff57774",
        "text": "The available supporting result uses fitted IPW in its numerator, whereas the corrected as-printed claim retains the distinct Hajek numerator. It establishes neither that coverage assertion nor its refutation."
    },
    "P005-T8": {
        "source_sha256": "1c98024af8c01961cb40d4fc45b50be9ed95915d3adf1cad7072c00f7c8b32d9",
        "text": "The available expansion theorem assumes Tropp2011RowSampling instead of proving it. The target claim contains no such hypothesis, so this conditional theorem does not establish its unconditional estimator expansion. The separately targeted logarithm equivalences are retained in T9."
    },
    "P006-T28": {
        "source_sha256": "0e44b60cf3152150fcc0d20dd79e6de6017a21f4e23ffaffd094277c8f80cdea",
        "text": "The available supporting result refutes a universal implication for hypothetical numerical summaries, without connecting those summaries or interval premises to the actual fitted effects of either reported analysis. It establishes neither the two particular beneficiary means nor their refutation."
    },
    "P007-T13": {
        "source_sha256": "91f2cc11e8e751dd39340a4c28a9a647d761b4a411e46f8146cb1500d35ad2cf",
        "text": "No formal declaration of the named empirical array establishes or refutes the positive printed assertions for this target."
    },
    "P008-T24": {
        "source_sha256": "10b1b75551620e51af3f20611d42c0beb5ec072ca296087e34f9f1c288b37d6d",
        "text": "The available counterexample refutes a universal statement about arbitrary numerical arrays, without linking it to the reported cumulative estimate, its permutation percentiles, or a forest-loss event. The three printed values lie in [-1,1], so its range obstruction does not refute their asserted empirical interpretation."
    },
    "P016-T5": {
        "source_sha256": "26ac0d9ddb4d0b98a55102d57d0f8c3eb4612d612e77a64d55fb46c79f11aae1",
        "text": "The target is the printed information and reference-distribution comparison. No correction replacing it with a fixed-margin existential claim has been accepted. The available T2 margin-invariance theorem negates that different existential claim, but does not refute the printed comparison: equality of full group margins is stronger than equality of the scalar KS, as the T2 scalar-KS witness shows. T1 pairing/design witnesses and T2 design identities establish their own corrected claims without proving equivalence to the printed prose. The proposed supporting refutation addresses the different fixed-margin claim and is not used as a theorem for T5; its content is already implied by T2."
    },
    "P041-T13": {
        "source_sha256": "68f5e7fc33a5fc43a0b2b6489858bb1482204a1b80d857370e001c2a46b877e3",
        "text": "The target supplies a precise random-order/adaptive-schedule implication comparing the expected implemented contrast, expected planned contrast, and direct effect. Its counterexample and no-interference sufficient condition are covered by P041-T5 and P041-T6. No separate theorem is assigned to P041-T13; the related mathematical content is available under those two targets."
    },
    "P044-T11": {
        "source_sha256": "3ee14cc0b39ef598028cfb6433259a0f3e3fe74de31bd435fc64275bc36321b5",
        "text": "The available supporting result negates a stronger exact universal conjunction across independent and included observation regimes. It does not refute the printed approximation assertion or its seed-reused workflow."
    },
    "P044-T12": {
        "source_sha256": "7ac7a0db9b69bfc05995975bf9b93aa54220793ee657c95cd8a2d5ac42d8a955",
        "text": "The available supporting result refutes an extension that drops zero-support contributions, outside S7's positive-marginal-input estimator domain. It also establishes none of the quoted Hajek/WLS consistency or efficiency claims."
    }
}


def reader_disclosure(target_id, text):
    """Render an approved explanation only while its original source is unchanged."""
    replacement = DISCLOSURES.get(target_id)
    if replacement is None:
        return text
    if text is None or hashlib.sha256(text.encode("utf-8")).hexdigest() != replacement["source_sha256"]:
        raise ValueError(f"Reader disclosure source changed: {target_id}")
    return replacement["text"]
