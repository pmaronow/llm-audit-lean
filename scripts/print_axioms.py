#!/usr/bin/env python3
"""Recheck credited declarations in an already built Lake project, one work at a time.

This requires substantial memory for some works. Each work runs in a separate
Lean process, so imported environments are released before the next work.
No packages are installed or fetched by this script. Sources and JSON output
are written in the chosen output directory (default: .lake/axiom-output).
"""
from pathlib import Path
import argparse
import json
import re
import subprocess
import sys

STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def parse_axioms(output, expected):
    found = {}
    pattern = re.compile(r"[‘'`]([^\n]+?)[’'`]\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", re.S)
    for m in pattern.finditer(output):
        name = m[1]
        if name not in expected:
            continue
        axioms = sorted(x.strip() for x in (m[2] or '').split(',') if x.strip())
        if name in found:
            raise ValueError(f'Duplicate axiom output: {name}')
        if set(axioms) - STANDARD:
            raise ValueError(f'Non-standard axioms: {name}: {axioms}')
        found[name] = axioms
    missing = set(expected) - set(found)
    if missing:
        raise ValueError(f'Missing axiom output: {sorted(missing)}')
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work', help='Check only one work, for example P037')
    parser.add_argument('--output', type=Path, default=Path('.lake/axiom-output'))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    rows = [json.loads(line) for line in (root / 'catalog/results.jsonl').read_text().splitlines()]
    works = sorted({r['work_id'] for r in rows})
    if args.work and args.work not in works:
        parser.error('Unknown work identifier')
    if not args.output.is_absolute():
        args.output = root / args.output
    args.output.mkdir(parents=True, exist_ok=True)
    all_axioms = {}
    for work in ([args.work] if args.work else works):
        selected = [r for r in rows if r['work_id'] == work]
        names = sorted({r['lean_name'] for r in selected})
        imports = sorted({r['module'] for r in selected})
        source = '\n'.join(['import ' + m for m in imports] + [''] + ['#print axioms ' + n for n in names]) + '\n'
        path = args.output.resolve() / (work + '.lean')
        path.write_text(source)
        print(f'{work}: checking {len(names)} declarations (one Lean process)', flush=True)
        result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=root,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (args.output / (work + '.txt')).write_text(result.stdout)
        if result.returncode:
            raise ValueError(f'Lean failed for {work}; see {work}.txt in the output directory')
        checked = parse_axioms(result.stdout, names)
        all_axioms.update(checked)
        (args.output / (work + '.json')).write_text(json.dumps(checked, indent=2, sort_keys=True) + '\n')
    (args.output / 'axioms.json').write_text(json.dumps(all_axioms, indent=2, sort_keys=True) + '\n')
    print(f'Checked {len(all_axioms)} distinct credited declarations; only standard axioms.')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, OSError) as exc:
        print(f'ERROR: {exc}', file=sys.stderr)
        raise SystemExit(1)
