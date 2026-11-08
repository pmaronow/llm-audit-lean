"""Strict count types. Equality with an int never establishes a counter's type."""
from boundaries import need

DECISIONS = {"whole", "restricted", "refuted", "omitted"}


def integer(value, label, expected=None):
    need(type(value) is int and value >= 0, "strict nonnegative integer required: " + label)
    if expected is not None:
        need(value == expected, "counter differs: " + label)
    return value


def decisions(value, label, expected=None):
    need(isinstance(value, dict) and set(value) <= DECISIONS, "invalid decision counter map: " + label)
    for key, count in value.items():
        integer(count, label + "." + key)
    if expected is not None:
        need(value == expected, "decision counters differ: " + label)
    return value


def promised(value, label):
    """Additional named counters anywhere in the documents this interface reads.

    Numeric expressions inside canonical Lean encodings are not counters. Units
    and targets may also be inventories; their required scalar occurrences are
    checked explicitly at the corresponding protocol paths.
    """
    scalar = {"unit_count", "target_count", "theorem_count", "items_reviewed", "theorems",
              "collected_file_count", "credited_count", "catalog_rows", "universe_count", "bytes", "round"}
    if isinstance(value, dict):
        for key, child in value.items():
            here = label + "." + key
            if key.endswith("_sha256"):
                continue  # Hash-map member filenames are not protocol fields.
            if key in scalar or key.endswith("_count"):
                integer(child, here)
            elif key == "targets" and isinstance(child,dict) and set(child)=={"listed","certified","omitted"}:
                # Certificate target counters, unlike INDEX.certified stamps.
                for name,count in child.items():
                    integer(count,here+"."+name)
            elif key in {"units","targets","omitted"} and not isinstance(child,(dict,list)):
                integer(child, here)
            elif key in {"decisions", "counts"}:
                decisions(child, here)
            else:
                promised(child, here)
    elif isinstance(value, list):
        for index, child in enumerate(value):
            promised(child, label + "[" + str(index) + "]")
