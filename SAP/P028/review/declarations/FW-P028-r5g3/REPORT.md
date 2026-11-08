# Omission review

**P028-T3: omission_ok; severity none.**

`claims.json` marks T3 `no_lean: true`, with an empty `rows` list and no coverage judgments. Thus `record.json` accurately reports that T3 has no credited Lean rows or target formalization. Under the supplied rule, the absence of any proved row is sufficient to justify omission.

The canonical statement, read together with its definitions and the standing assumptions, concerns the printed application passage: additional joint-distribution information, its reported empirical inputs and complier estimates, and estimation by sample analogues. The omission reason does not misdescribe that passage. This decision does not depend on the audit-history note excluding the printed numbers.

The Challenge has no T3 theorem. T1 separately states the missing-outcome counterexample, and T9 separately states identification from ordinary cell summaries. Neither supplies a credited T3 row; merely restating either target would not qualify as a restricted T3 statement. No supported restricted statement is proposed, and no new proof or Lean compilation is needed.

The fingerprint in `findings.json` is copied from T3's entry in `closure.json`.
