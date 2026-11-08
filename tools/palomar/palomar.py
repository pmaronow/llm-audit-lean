#!/usr/bin/env python3
"""Reviewed standalone front door. Verify this entry's hash independently first."""
import sys
if not (sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode):
    raise SystemExit("Palomar entry requires python3 -I -S -B before any nonbuiltin import")
sys.dont_write_bytecode = True

# The interpreter/stdlib are explicit external trust inputs. Isolation removes
# script/CWD/PYTHONPATH lookup and -S disables site hooks before these imports.
import hashlib
import json
from pathlib import Path
import stat
import types

PINNED_FILES = {'scripts/PROTOCOL.json': '8366012878374dd36261a7f54265e1b74b3aa2aa5a1823a7d2d61127375b158b', 'scripts/WorkAudit.lean.tmpl': 'c209215fb02df1abeb2ba24a8a9ac19dd453e7e233da3fa84d31077d30f483f1', 'scripts/admission_contract.py': '1b8ed130bd24145fa264ee6fc116ba14a285e70ca2fc913ad7a1a04fc0430157', 'scripts/boundaries.py': 'f0f26f661b646c97d2570c1648a756c3987e62f6ce3146fddf254c01544afa09', 'scripts/closure_data.py': '6402708f19854ec42adb0561625e33a47140b6291d8c75357e6855931127115d', 'scripts/counts.py': 'dd2774d7f1f382e2d68153a2fea385443062cfccb0ed8c9e4488e1cc4b6dc37e', 'scripts/fixture_support.py': '70ee162ba4916a7f104e06cf7cc0f0b8268ad7a1bbdcdb179ea009ccaf900571', 'scripts/generate_work_packages.py': 'f2df3bc255fb90b525f93116f7f0b2852b12d06a0d369d075fd9be92f0815f9c', 'scripts/inventory_current.py': '2ac26f6ff66fb7109f7571e2cebf2509e8912eb534bf5222a2adba3aad29fffe', 'scripts/live_control_fixtures.py': 'ff5e21664d693b2d7397951a1771d60d54917b2a0c3ef79a37c277d2c49e929f', 'scripts/refresh_candidate.py': '99dcd0a2512b702f8561cc92f56365dc8fd2ab2c1f6fb222298d210073c9b1f6', 'scripts/replay_work.py': '283b3b814ef2566bedbd726c7923057bebd646ea05c7f51bd3ccd4e81947be83', 'scripts/run_checks.py': 'dac19b27678ed191d4663a260f55ba8b09f87244acc29163375d25ce51cfc99f', 'scripts/run_definition_probe.py': 'adfc743cd4d222dc942a34d8f2113003d48920d661318b74fe0af13d0b9e133b', 'scripts/run_runtime_controls.py': 'a06f5be9b7c864593efcc8332f5bfee904248827466e9f6570c1941a8ea98ea4', 'scripts/validate_work_packages.py': '5cfea70915129cfa007af7f7357a10f8cdb1f543b309f569e1fb8ebcf80741e8', 'scripts/work_package.py': 'ed33218d79b805af39faf058ec04f4528ee2804f230e20b215a590061162c627'}
ORDER = ["boundaries", "counts", "work_package", "closure_data", "admission_contract",
         "generate_work_packages", "validate_work_packages", "replay_work", "fixture_support",
         "live_control_fixtures", "run_definition_probe", "run_runtime_controls",
         "refresh_candidate", "inventory_current", "run_checks"]
COMMANDS = {"generate":"generate_work_packages", "validate":"validate_work_packages", "replay":"replay_work",
            "refresh":"refresh_candidate", "inventory":"inventory_current", "checks":"run_checks",
            "definition-probe":"run_definition_probe", "runtime-controls":"run_runtime_controls"}


def bootstrap(expected_entry_sha256):
    entry = Path(__file__).absolute()
    if entry != entry.resolve() or not stat.S_ISREG(entry.lstat().st_mode):
        raise RuntimeError("noncanonical standalone entry path")
    root = entry.parent
    entry_bytes=entry.read_bytes()
    if not (isinstance(expected_entry_sha256,str) and len(expected_entry_sha256)==64 and
            all(c in "0123456789abcdef" for c in expected_entry_sha256) and
            hashlib.sha256(entry_bytes).hexdigest()==expected_entry_sha256):
        raise RuntimeError("independently expected standalone entry identity missing/differs")
    helper = root/"scripts"
    if helper.is_symlink() or not helper.is_dir():
        raise RuntimeError("closed scripts installation missing")
    members = {"scripts/"+p.name for p in helper.iterdir()}
    if members != set(PINNED_FILES):
        raise RuntimeError("closed scripts installation membership differs")
    blobs = {}
    for rel, expected in PINNED_FILES.items():
        path = root/rel
        if path != path.resolve() or not stat.S_ISREG(path.lstat().st_mode):
            raise RuntimeError("nonregular/aliased installation member: "+rel)
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != expected:
            raise RuntimeError("byte-pinned installation member differs: "+rel)
        blobs[rel] = data
    context = types.ModuleType("_palomar_installation")
    context.root, context.entry, context.entry_bytes = root, entry, entry_bytes
    context.entry_sha256=expected_entry_sha256
    context.blobs = blobs
    context.files_sha256 = dict(PINNED_FILES)
    def recheck():
        if {"scripts/"+p.name for p in helper.iterdir()} != set(blobs):
            raise RuntimeError("installation membership drift")
        for rel,data in blobs.items():
            path=root/rel
            if path.is_symlink() or not path.is_file() or path.read_bytes()!=data:
                raise RuntimeError("installation byte drift: "+rel)
        if entry.read_bytes()!=context.entry_bytes:
            raise RuntimeError("standalone entry drift")
    context.recheck = recheck
    sys.modules[context.__name__] = context
    # All helper bytes are authenticated before any helper executes. Compile
    # these exact buffers; never change sys.path or consult adjacent pyc files.
    for name in ORDER:
        module = types.ModuleType(name)
        module.__file__ = str(root/"scripts"/(name+".py"))
        module.__package__ = None
        sys.modules[name] = module
        exec(compile(blobs["scripts/"+name+".py"],module.__file__,"exec"),module.__dict__)
    recheck()
    return context


def main():
    if len(sys.argv)<3 or sys.argv[1]!="--expected-entry-sha256":
        raise RuntimeError("--expected-entry-sha256 from independent code review records is required")
    context=bootstrap(sys.argv[2])
    sys.argv=[sys.argv[0],*sys.argv[3:]]
    if len(sys.argv)<2 or sys.argv[1] in {"-h","--help"}:
        print("Usage: python3 -I -S -B palomar.py --expected-entry-sha256 REVIEWED_SHA COMMAND ...; commands: "+", ".join(sorted(COMMANDS)))
        return 0
    command=sys.argv[1]
    if command=="installation-check":
        print(json.dumps({"status":"closed_installation_bytes_match", "independent_approval":False,
                          "helper_files":len(context.blobs),"files_sha256":context.files_sha256},sort_keys=True))
        return 0
    if command not in COMMANDS:
        raise RuntimeError("unknown Palomar command")
    sys.argv=[str(context.entry)+" "+command,*sys.argv[2:]]
    try:
        result=sys.modules[COMMANDS[command]].main()
        return result if type(result) is int else 0
    finally:
        context.recheck()


if __name__=="__main__":
    try:
        raise SystemExit(main())
    except (ValueError,OSError,KeyError,TypeError,RuntimeError) as exc:
        print("INVALID: "+str(exc),file=sys.stderr)
        raise SystemExit(1)
