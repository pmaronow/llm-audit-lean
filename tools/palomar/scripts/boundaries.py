"""Read/write boundaries shared by every v3 writer. No filesystem mutation here."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import hashlib
import os
import stat
import shutil


class Invalid(ValueError):
    pass


def need(ok, message):
    if not ok:
        raise Invalid(message)


def resolved(path):
    try:
        # Match pathlib/argparse input semantics exactly; a quoted '~' is a
        # literal path component, not an implicit HOME lookup.
        return Path(path).resolve(strict=False)
    except (RuntimeError, OSError) as exc:
        raise Invalid(f"cannot resolve boundary path: {path}: {exc}") from exc


def overlap(a, b):
    if a == b or a in b.parents or b in a.parents:
        return True
    # Path.resolve does not normalize case/Unicode aliases on every filesystem.
    # Compare an existing input/output node with the other path's ancestors.
    # Do NOT compare all ancestor pairs: ordinary siblings share an ancestor.
    for node, candidates in ((a,(b,*b.parents)),(b,(a,*a.parents))):
        if node.exists():
            for other in candidates:
                try:
                    if other.exists() and node.samefile(other):return True
                except OSError:
                    continue
    return False


def guard_paths(outputs, inputs, *, fresh=True):
    """Resolve ALL destinations before writes; reject either overlap direction.

    Inputs may be files or directory trees. A future output ancestor of an input
    is forbidden, as is a child of an input tree. Existing symlink aliases are
    resolved before comparison. Existing files/hardlinks are never overwritten.
    Outputs may be nested within one newly owned output tree.
    """
    outs = {name: resolved(p) for name, p in outputs.items() if p is not None}
    reads = {name: resolved(p) for name, p in inputs.items() if p is not None}
    for oname, dest in outs.items():
        for iname, source in reads.items():
            need(not overlap(dest, source), f"output boundary overlap: {oname}={dest} with read-only {iname}={source}")
    if fresh:
        for name, raw in outputs.items():
            if raw is not None:
                p = Path(raw)
                need(not p.exists() and not p.is_symlink(), f"fresh output required: {name}={p}")
    return outs


ARG_INPUTS = ("source", "entries", "base_source", "catalog", "site", "attestation", "routes",
              "collection_receipt", "collected_file_inventory", "admission_root", "admission_review",
              "lean", "comparator_lake", "primitive_check_file", "exporter", "lean_path_file",
              "failed_collection_receipt", "baseline_source", "collection_failure", "parent_update")


def inputs_for(args, *, code_root=None):
    reads = {name: getattr(args, name, None) for name in ARG_INPUTS}
    context=sys.modules.get("_palomar_installation")
    if context is not None:
        reads["standalone_front_door"]=context.entry
    for i, root in enumerate(getattr(args, "read_only_root", []) or []):
        reads[f"explicit_read_only_{i}"] = root
    if code_root is not None:
        root = Path(code_root)
        if root.is_file():
            reads["entry_code_directory"]=root.parent
            root=root.parent.parent if root.parent.name == "scripts" else root.parent
        for part in ("scripts", "tests", "lean"):
            if (root/part).exists():
                reads["code_" + part] = root / part
    reads["python_executable"]=Path(sys.executable)
    reads["python_runtime"]=Path(sys.base_prefix)
    reads["python_environment"]=Path(sys.prefix)
    return reads


def dependency_inputs(args, owned, compiler_cwds):
    reads={}
    for name in ("lean","comparator_lake"):
        value=getattr(args,name,None)
        if value is not None:
            reads[name+"_sysroot"]=resolved(value).parent.parent
    lp=getattr(args,"lean_path_file",None)
    if lp is not None and Path(lp).is_file():
        try:
            text=Path(lp).read_text().strip()
        except UnicodeError as exc:
            raise Invalid("LEAN_PATH inventory is not UTF-8") from exc
        need(text and "\n" not in text and "\r" not in text,"LEAN_PATH must be a nonempty single line")
        # Relative search paths resolve from the future compiler cwd. Paths
        # inside newly owned output are generated artifacts, not preexisting
        # read-only dependencies. Every external library tree is protected.
        for i,part in enumerate(text.split(os.pathsep)):
            for j,cwd in enumerate(compiler_cwds):
                p=resolved(Path(part) if Path(part).is_absolute() else Path(cwd)/(part or "."))
                if p != owned and owned not in p.parents:
                    reads[f"dependency_{i}_{j}"]=p
    lake=getattr(args,"comparator_lake",None)
    if lake is not None:
        search=str(resolved(lake).parent)+os.pathsep+os.environ.get("PATH","")
        for name in ("con-ron","nanoda_bin"):
            p=shutil.which(name,path=search)
            if p:reads["kernel_"+name]=Path(p)
    return reads


def plan_outputs(outputs,args,*,code_root=None,compiler_cwds=None):
    reads=inputs_for(args,code_root=code_root)
    planned=guard_paths(outputs,reads)
    owned=planned.get("mirror",planned.get("out"))
    cwds=compiler_cwds or [owned/"work"]
    reads.update(dependency_inputs(args,owned,cwds))
    return guard_paths(outputs,reads)


def sha_regular(path):
    path = Path(path)
    need(path.is_file() and not path.is_symlink(), f"not a regular immutable file: {path}")
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def tree_rows(root):
    """Entire immutable tree, including files outside any unit/index prefix.

    Match A3 compact-row convention. Reject all symlinks, including dangling
    links and directory links, and all sockets/devices/FIFOs before reading.
    """
    root = Path(root)
    need(root.is_dir() and not root.is_symlink(), f"immutable root missing or symlink: {root}")
    rows = []
    for directory, dirs, files in os.walk(root, followlinks=False):
        for name in sorted(dirs + files):
            path = Path(directory) / name
            mode = path.lstat().st_mode
            need(not stat.S_ISLNK(mode), f"symlink in immutable tree: {path}")
            if stat.S_ISDIR(mode):
                continue
            need(stat.S_ISREG(mode), f"unsupported immutable file: {path}")
            rows.append({"path": path.relative_to(root).as_posix(),
                         "mode": "100755" if mode & 0o111 else "100644",
                         "sha256": sha_regular(path), "bytes": path.stat().st_size})
    return sorted(rows, key=lambda row: row["path"])


def file_inventory(root):
    return {row["path"]: row["sha256"] for row in tree_rows(root)}


def exact_collection_tree(source, inventory):
    need(isinstance(inventory, dict) and inventory, "complete collection inventory missing")
    actual = file_inventory(source)
    need(actual == inventory, "entire collection root differs from successful file inventory")
    expected_dirs={str(parent) for name in inventory for parent in Path(name).parents if str(parent)!="."}
    actual_dirs={p.relative_to(source).as_posix() for p in Path(source).rglob("*") if p.is_dir()}
    need(actual_dirs==expected_dirs,"entire collection directory membership differs from successful inventory")
    return actual


def collection_layout(source, unit_ids):
    """Reject unknown/empty roots too, before hashing unrelated project files."""
    root=Path(source)
    need(root.is_dir() and not root.is_symlink() and
         {p.name for p in root.iterdir()} == {"SAP"} and
         (root/"SAP").is_dir() and not (root/"SAP").is_symlink(),
         "collection has extra root or unit; overlay must be separate")
    need({p.name for p in (root/"SAP").iterdir()} == set(unit_ids)|{"INDEX.json"},
         "collection has extra root or unit; overlay must be separate")
