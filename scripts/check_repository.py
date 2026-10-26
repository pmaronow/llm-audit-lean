#!/usr/bin/env python3
"""Conservative source locations, small JSON Schema checks and repository links.

Only the Python standard library is used.  Lean source scanning locates explicit
declarations; it is deliberately not a Lean parser and never chooses between
multiple declarations bearing the same fully qualified textual name.
"""
import html
import json
import math
from fractions import Fraction
import posixpath
import re
import unicodedata
from urllib.parse import unquote, urlsplit


OPERATOR_DELIMITERS = {
    'left', 'right', 'bigl', 'bigr', 'Bigl', 'Bigr', 'biggl', 'biggr',
    'Biggl', 'Biggr', 'big', 'Big', 'bigg', 'Bigg', 'lbrace', 'langle',
    'lvert', 'lVert', 'mid', 'middle',
}


def rewrite_math_operators(content):
    """Replace unsupported operator names only within a supplied math span."""
    pieces, cursor = [], 0
    pattern = re.compile(r'\\operatorname\*?\s*\{')
    while match := pattern.search(content, cursor):
        stop, depth = match.end(), 1
        while stop < len(content) and depth:
            if content[stop] == '\\':
                stop += 2
                continue
            if content[stop] == '{':
                depth += 1
            elif content[stop] == '}':
                depth -= 1
            stop += 1
        if depth:
            break
        body = rewrite_math_operators(content[match.end():stop-1])
        tail = content[stop:].lstrip()
        macro = re.match(r'\\([A-Za-z]+)', tail)
        spaced = bool(tail and (tail[0].isalpha() or tail[0].isdigit() or
                               (macro and macro[1] not in OPERATOR_DELIMITERS)))
        pieces += [content[cursor:match.start()], r'\mathrm{' + body + '}' + (r'\,' if spaced else '')]
        cursor = stop
    pieces.append(content[cursor:])
    return ''.join(pieces)


def github_math_content(content):
    content = rewrite_math_operators(content).replace('<', r'\lt ').replace('>', r'\gt ')
    if r'\operatorname' in content:
        raise ValueError('Unsupported GitHub math macro: operatorname')
    return content


def markdown_math_spans(text):
    """Yield rendered math contents, excluding ordinary Markdown code examples."""
    cursor = 0
    while cursor < len(text):
        if cursor == 0 or text[cursor-1] == '\n':
            opener = re.match(r' {0,3}(`{3,}|~{3,})([^\n]*)(?:\n|$)', text[cursor:])
            if opener:
                mark = opener[1]
                close = re.compile(r'^ {0,3}' + re.escape(mark[0]) + '{' + str(len(mark)) + r',}[ \t]*(?:\n|$)', re.M)
                match = close.search(text, cursor + opener.end())
                if opener[2].strip() == 'math':
                    yield text[cursor+opener.end():match.start() if match else len(text)]
                cursor = match.end() if match else len(text)
                continue
            if text.startswith(('    ', '\t'), cursor):
                stop = text.find('\n', cursor)
                cursor = stop+1 if stop >= 0 else len(text)
                continue
        if text[cursor] == '\\':
            cursor += 2
            continue
        if text.startswith('$`', cursor):
            stop = text.find('`$', cursor+2)
            if stop >= 0:
                yield text[cursor+2:stop]
                cursor = stop+2
                continue
        if text[cursor] == '`':
            run = re.match(r'`+', text[cursor:])[0]
            match = re.compile(r'(?<!`)' + re.escape(run) + r'(?!`)').search(text, cursor+len(run))
            if match:
                cursor = match.end()
                continue
        cursor += 1


def render_math(text, table=False, curated=True, field=None, warnings=None):
    """Render dollar math for GitHub while preserving Markdown code verbatim.

    ``table=None`` detects table rows from the opening delimiter's line.  An
    unpaired dollar in a record field preserves that whole field, rather than
    interpreting its remaining text as mathematics.  Warning labels are stable
    and deduplicated so callers can include them in their generation summary.
    """
    text = str(text)
    # Normalize existing outer math fences while preserving nested examples
    # inside ordinary code fences verbatim.
    lines, math_lines = [], []
    fence = None
    math_fence = False
    for line in text.splitlines(keepends=True):
        match = re.match(r"^ {0,3}(`{3,}|~{3,})([^\n]*)", line)
        if fence is None:
            if match:
                fence = match[1]
                math_fence = match[2].strip() == 'math'
            lines.append(line)
        elif match and match[1][0] == fence[0] and len(match[1]) >= len(fence) and not match[2].strip():
            if math_fence:
                lines.append(github_math_content(''.join(math_lines)))
                math_lines = []
            lines.append(line)
            fence = None
            math_fence = False
        elif math_fence:
            math_lines.append(line)
        else:
            lines.append(line)
    if math_lines:
        lines.append(github_math_content(''.join(math_lines)))
    text = ''.join(lines)
    if "$" not in text:
        return text

    def escaped(position):
        start = position - 1
        while start >= 0 and text[start] == "\\":
            start -= 1
        return (position - start - 1) % 2 == 1

    protected = [False] * len(text)
    existing_math = []
    cursor = 0
    while cursor < len(text):
        # Fences are recognized only at the beginning of a Markdown line.
        if cursor == 0 or text[cursor - 1] == "\n":
            if text.startswith("    ", cursor) or text.startswith("\t", cursor):
                stop = text.find("\n", cursor)
                stop = len(text) if stop < 0 else stop + 1
                protected[cursor:stop] = [True] * (stop - cursor)
                cursor = stop
                continue
            opener = re.match(r" {0,3}(`{3,}|~{3,})[^\n]*(?:\n|$)", text[cursor:])
            if opener:
                mark = opener.group(1)
                close = re.compile(r"^ {0,3}" + re.escape(mark[0]) + "{" + str(len(mark)) + r",}[ \t]*(?:\n|$)", re.M)
                end_match = close.search(text, cursor + opener.end())
                stop = end_match.end() if end_match else len(text)
                protected[cursor:stop] = [True] * (stop - cursor)
                cursor = stop
                continue
        # Already-rendered inline math is still math: normalize its contents,
        # but defer the edit until all dollars in the field have been checked.
        # Recognize it before its backticks are treated as ordinary code.
        if text.startswith("$`", cursor) and not escaped(cursor):
            stop = text.find("`$", cursor + 2)
            while stop >= 0 and escaped(stop):
                stop = text.find("`$", stop + 2)
            if stop >= 0:
                existing_math.append((cursor, stop + 2, text[cursor + 2:stop]))
                stop += 2
                protected[cursor:stop] = [True] * (stop - cursor)
                cursor = stop
                continue
        if text[cursor] == "`" and not escaped(cursor):
            run = re.match(r"`+", text[cursor:]).group()
            closer = re.compile(r"(?<!`)" + re.escape(run) + r"(?!`)")
            match = next((candidate for candidate in closer.finditer(text, cursor + len(run))
                          if not escaped(candidate.start())), None)
            if match:
                stop = match.end()
                protected[cursor:stop] = [True] * (stop - cursor)
                cursor = stop
                continue
            cursor += len(run)
            continue
        cursor += 1

    displays = []
    singles = []
    cursor = 0
    while cursor < len(text):
        if text[cursor] != "$" or protected[cursor] or escaped(cursor):
            cursor += 1
            continue
        if text.startswith("$$", cursor) and not protected[cursor + 1]:
            displays.append(cursor)
            cursor += 2
        else:
            singles.append(cursor)
            cursor += 1
    pairs = []
    if len(displays) % 2 == 0:
        pairs = [(displays[i], displays[i + 1], 2) for i in range(0, len(displays), 2)]
        singles = [position for position in singles if not any(start < position < stop for start, stop, _ in pairs)]
    # A display pair is atomic: a surrounding single-dollar pair would overlap
    # it, so those singles are not a valid inline pair.
    overlaps = (len(singles) % 2 == 0 and any(
        start < display_start < stop
        for start, stop in zip(singles[::2], singles[1::2])
        for display_start, _, _ in pairs))
    if len(displays) % 2 or len(singles) % 2 or overlaps:
        label = field or text
        if curated:
            raise ValueError(f"Unpaired dollar in curated math field: {label}")
        if warnings is not None and label not in warnings:
            warnings.append(label)
        return text
    pairs.extend((singles[i], singles[i + 1], 1) for i in range(0, len(singles), 2))
    replacements = [(start, stop, "$`" + github_math_content(content.strip()) + "`$")
                    for start, stop, content in existing_math]
    for start, stop, width in pairs:
        content = github_math_content(text[start + width:stop].strip())
        in_table = table
        if table is None:
            line_start = text.rfind("\n", 0, start) + 1
            line_stop = text.find("\n", start)
            line = text[line_start:line_stop if line_stop >= 0 else len(text)]
            in_table = line.lstrip().startswith("|")
        if width == 2 and not in_table:
            replacement = "\n\n```math\n" + content.strip() + "\n```\n\n"
        else:
            replacement = "$`" + content + "`$"
        replacements.append((start, stop + width, replacement))
    pieces = []
    cursor = 0
    for start, stop, replacement in sorted(replacements):
        pieces.append(text[cursor:start])
        pieces.append(replacement)
        cursor = stop
    pieces.append(text[cursor:])
    return "".join(pieces)


def render_markdown_math(text, curated=False, field=None, warnings=None):
    """Render a Markdown document, keeping display math inline in table rows."""
    return render_math(text, table=None, curated=curated, field=field, warnings=warnings)


def _mask_lean(text):
    """Remove comments and strings without changing offsets or line numbers."""
    chars = list(text)
    i = 0
    n = len(text)

    def blank(start, stop):
        for k in range(start, stop):
            if chars[k] != "\n":
                chars[k] = " "

    while i < n:
        if text.startswith("--", i):
            stop = text.find("\n", i)
            stop = n if stop < 0 else stop
            blank(i, stop)
            i = stop
        elif text.startswith("/-", i):
            start, depth = i, 1
            i += 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            blank(start, i)
        elif text[i] == "«":
            # Quoted identifiers are names, not strings.  They can contain
            # whitespace and punctuation, including comment delimiters.
            stop = text.find("»", i + 1)
            i = n if stop < 0 else stop + 1
        elif text[i] == '"':
            start = i
            # Lean raw strings use r#"..."# (with any number of #s).
            raw_start = i - 1
            while raw_start >= 0 and text[raw_start] == "#":
                raw_start -= 1
            raw_hashes = text[raw_start + 1:i]
            if raw_start >= 0 and text[raw_start] == "r" and raw_hashes:
                end = text.find('"' + raw_hashes, i + 1)
                i = n if end < 0 else end + 1 + len(raw_hashes)
            else:
                i += 1
                while i < n:
                    if text[i] == "\\":
                        i += 2
                    elif text[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
            blank(start, min(i, n))
        elif text[i] == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'»")):
            # A character literal is one character or one escaped character.
            match = re.match(r"'(?:[^'\\\n]|\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.))'", text[i:])
            if match:
                blank(i, i + len(match.group()))
                i += len(match.group())
            else:
                i += 1
        else:
            i += 1
    return "".join(chars)


_COMPONENT = r"(?:«[^»\n]+»|[^\W\d][\w'₀-₉]*)"
_NAME = _COMPONENT + r"(?:\." + _COMPONENT + r")*"
_DECLARATION = re.compile(
    r"^(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|public)\s+)*"
    r"(?:theorem|lemma|def|abbrev|axiom|opaque|structure|class|inductive|coinductive|instance)\s+(" + _NAME + r")(?=\s|[:({\[]|\.\{|$)"
)


def _name_parts(name):
    return re.findall(_COMPONENT, name)


def scan_declarations(text):
    """Return fully qualified textual declaration names and declaration lines.

    Namespace commands and sections have separate stack entries: closing a
    section must not close its surrounding namespace.  Declaration lines are
    the lines of ``theorem``/``def`` etc., not preceding comments or attributes.
    Private declarations are omitted: Lean's generated ``_private`` kernel
    names cannot be reconstructed here.  Unknown namespace-closing syntax stops
    location inference rather than guessing.
    """
    clean = _mask_lean(text)
    scopes = []  # (kind, written name, namespace before entry)
    namespace = []
    declarations = {}
    attribute_depth = 0
    reliable = True
    pending_modifiers = []
    for line_number, original in enumerate(clean.splitlines(), 1):
        line = original.strip()
        # Attributes can precede declarations on the same or earlier lines.
        while line:
            if attribute_depth:
                cursor = 0
                while cursor < len(line) and attribute_depth:
                    if line[cursor] == "[":
                        attribute_depth += 1
                    elif line[cursor] == "]":
                        attribute_depth -= 1
                    cursor += 1
                line = line[cursor:].lstrip()
                if attribute_depth:
                    break
            elif line.startswith("@["):
                attribute_depth = 1
                line = line[2:]
            else:
                break
        if not line or attribute_depth:
            continue
        # ``open ... in`` changes name lookup for one command, not the name
        # under which that command declares its result.  It can share a line
        # with the declaration or occupy the preceding line.
        local_open = re.match(r"open\s+.+?\s+in\s+(.+)$", line)
        if local_open:
            line = local_open.group(1)
        if re.fullmatch(r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|public)\s*)+", line):
            pending_modifiers.append(line)
            continue
        if pending_modifiers:
            line = " ".join(pending_modifiers + [line])
            pending_modifiers.clear()
        match = re.fullmatch(r"namespace\s+(" + _NAME + r")", line)
        if match:
            name = match.group(1)
            scopes.append(("namespace", name, namespace[:]))
            parts = _name_parts(name)
            namespace = parts[1:] if parts[0] == "_root_" else namespace + parts
            continue
        match = re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+(" + _NAME + r"))?", line)
        if match:
            scopes.append(("section", match.group(1), namespace[:]))
            continue
        match = re.fullmatch(r"end(?:\s+(" + _NAME + r"))?", line)
        if match:
            if not scopes:
                reliable = False
                continue
            kind, name, before = scopes.pop()
            closing = match.group(1)
            if closing is not None and closing != name:
                # Lean accepts the final component when a dotted namespace was
                # opened; names otherwise must identify the scope being closed.
                if name is None or closing != _name_parts(name)[-1]:
                    reliable = False
            namespace = before
            continue
        match = _DECLARATION.match(line)
        if match and reliable:
            if re.match(r"(?:(?:protected|noncomputable|unsafe|partial|nonrec|public)\s+)*private\s", line):
                continue
            parts = _name_parts(match.group(1))
            parts = parts[1:] if parts[0] == "_root_" else namespace + parts
            name = ".".join(parts)
            declarations.setdefault(name, []).append(line_number)
    return declarations


def resolve_declaration(text, name):
    """Return a unique explicit declaration line, or None."""
    lines = scan_declarations(text).get(name, [])
    return lines[0] if len(lines) == 1 else None


def json_number(value):
    """Interpret a finite JSON number by its decimal value, excluding bool."""
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError('Expected a JSON number')
    if isinstance(value, float) and not math.isfinite(value):
        raise ValueError('JSON numbers must be finite')
    return Fraction(str(value))


def json_value_key(value):
    """Hashable JSON equality: numbers by value, booleans a separate type."""
    if value is None:
        return ('null',)
    if isinstance(value, bool):
        return ('boolean', value)
    if isinstance(value, (int, float)):
        return ('number', json_number(value))
    if isinstance(value, str):
        return ('string', value)
    if isinstance(value, list):
        return ('array', tuple(json_value_key(item) for item in value))
    if isinstance(value, dict):
        if not all(isinstance(key, str) for key in value):
            raise ValueError('JSON object keys must be strings')
        return ('object', tuple((key, json_value_key(item)) for key,item in sorted(value.items())))
    raise ValueError('Expected a JSON value')


class SchemaSupportError(ValueError):
    """The schema uses unsupported features, independently of an instance."""


SCHEMA_KEYWORDS = {
    "$schema", "$id", "$ref", "$defs", "$comment", "title", "description", "examples", "default",
    "type", "enum", "const", "allOf", "anyOf", "oneOf", "not", "required", "properties",
    "patternProperties", "additionalProperties", "minProperties", "maxProperties", "items", "prefixItems",
    "minItems", "maxItems", "uniqueItems", "pattern", "minLength", "maxLength", "minimum", "maximum",
    "exclusiveMinimum", "exclusiveMaximum", "multipleOf", "deprecated", "readOnly", "writeOnly",
}


def preflight_schema(schema):
    """Inspect every schema node before any instance/combinator evaluation."""
    visited = set()
    root = schema
    def inspect(node, path):
        if isinstance(node, bool):
            return
        if not isinstance(node, dict):
            raise SchemaSupportError(f'{path}: schema must be an object or boolean')
        if id(node) in visited:
            return
        visited.add(id(node))
        unknown = set(node) - SCHEMA_KEYWORDS
        if unknown:
            raise SchemaSupportError(f"{path}: unsupported schema keyword(s): {', '.join(sorted(unknown))}")
        if 'multipleOf' in node:
            try:
                divisor = json_number(node['multipleOf'])
                if divisor <= 0:
                    raise ValueError('Nonpositive divisor')
            except ValueError:
                raise SchemaSupportError(f'{path}.multipleOf: expected a finite positive JSON number') from None
        for key in ('$defs', 'properties', 'patternProperties'):
            if key in node:
                if not isinstance(node[key], dict):
                    raise SchemaSupportError(f'{path}.{key}: expected schema map')
                for name, child in node[key].items():
                    inspect(child, f'{path}.{key}.{name}')
        for key in ('additionalProperties', 'items', 'not'):
            if key in node:
                inspect(node[key], f'{path}.{key}')
        for key in ('prefixItems', 'allOf', 'anyOf', 'oneOf'):
            if key in node:
                if not isinstance(node[key], list):
                    raise SchemaSupportError(f'{path}.{key}: expected schema array')
                for position, child in enumerate(node[key]):
                    inspect(child, f'{path}.{key}[{position}]')
        if '$ref' in node:
            ref = node['$ref']
            if not isinstance(ref, str) or not ref.startswith('#/'):
                raise SchemaSupportError(f'{path}: only local JSON Schema references are supported: {ref!r}')
            target = root
            try:
                for part in ref[2:].split('/'):
                    target = target[part.replace('~1', '/').replace('~0', '~')]
            except (KeyError, TypeError):
                raise SchemaSupportError(f'{path}: unresolved schema reference {ref}') from None
            inspect(target, f'{path}.$ref')
    inspect(schema, '$schema')


def validate_schema(value, schema, path="$", _root=None):
    """Validate the draft 2020-12 subset used by the generated catalog schemas.

    Supported: local $ref/$defs, type, enum, const, allOf/anyOf/oneOf/not,
    object properties/patternProperties/required/additionalProperties and size,
    array items/prefixItems/uniqueItems and size, string pattern and size, and
    numeric bounds.  Unsupported assertion keywords fail rather than silently
    presenting an incomplete check as validation.
    """
    if _root is None:
        preflight_schema(schema)
        json_value_key(value)
    if isinstance(schema, bool):
        if not schema:
            raise ValueError(f"{path}: disallowed by schema")
        return
    if not isinstance(schema, dict):
        raise ValueError(f"{path}: schema must be an object or boolean")
    root = schema if _root is None else _root

    unknown = set(schema) - SCHEMA_KEYWORDS
    if unknown:
        raise SchemaSupportError(f"{path}: unsupported schema keyword(s): {', '.join(sorted(unknown))}")
    if "$ref" in schema:
        ref = schema["$ref"]
        if not isinstance(ref, str) or not ref.startswith("#/"):
            raise ValueError(f"{path}: only local JSON Schema references are supported: {ref!r}")
        target = root
        try:
            for part in ref[2:].split("/"):
                target = target[part.replace("~1", "/").replace("~0", "~")]
        except (KeyError, TypeError):
            raise ValueError(f"{path}: unresolved schema reference {ref}") from None
        validate_schema(value, target, path, root)
    numeric = isinstance(value, (int, float)) and not isinstance(value, bool)
    number = json_number(value) if numeric else None
    types = {
        "null": value is None,
        "boolean": isinstance(value, bool),
        "integer": numeric and number.denominator == 1,
        "number": numeric,
        "string": isinstance(value, str),
        "array": isinstance(value, list),
        "object": isinstance(value, dict),
    }
    if "type" in schema:
        requested = schema["type"] if isinstance(schema["type"], list) else [schema["type"]]
        if any(item not in types for item in requested):
            raise ValueError(f"{path}: unknown schema type")
        if not any(types[item] for item in requested):
            raise ValueError(f"{path}: expected {' or '.join(requested)}, got {type(value).__name__}")
    # Structural JSON equality compares numeric values and distinguishes booleans.
    canonical = json_value_key
    if "enum" in schema and canonical(value) not in [canonical(item) for item in schema["enum"]]:
        raise ValueError(f"{path}: value is outside enum")
    if "const" in schema and canonical(value) != canonical(schema["const"]):
        raise ValueError(f"{path}: value differs from const")
    for keyword in ("allOf", "anyOf", "oneOf"):
        if keyword in schema:
            passed = 0
            for candidate in schema[keyword]:
                try:
                    validate_schema(value, candidate, path, root)
                except SchemaSupportError:
                    raise
                except ValueError:
                    pass
                else:
                    passed += 1
            expected = {"allOf": len(schema[keyword]), "anyOf": 1, "oneOf": 1}[keyword]
            if (keyword == "anyOf" and passed < expected) or (keyword != "anyOf" and passed != expected):
                raise ValueError(f"{path}: does not satisfy {keyword}")
    if "not" in schema:
        try:
            validate_schema(value, schema["not"], path, root)
        except SchemaSupportError:
            raise
        except ValueError:
            pass
        else:
            raise ValueError(f"{path}: matches prohibited schema")
    if isinstance(value, dict):
        for required in schema.get("required", []):
            if required not in value:
                raise ValueError(f"{path}: missing required property {required}")
        for key, item in value.items():
            matched = False
            if key in schema.get("properties", {}):
                validate_schema(item, schema["properties"][key], f"{path}.{key}", root)
                matched = True
            for pattern, candidate in schema.get("patternProperties", {}).items():
                if re.search(pattern, key):
                    validate_schema(item, candidate, f"{path}.{key}", root)
                    matched = True
            if not matched and "additionalProperties" in schema:
                validate_schema(item, schema["additionalProperties"], f"{path}.{key}", root)
        for keyword, test in (("minProperties", lambda bound: len(value) < bound), ("maxProperties", lambda bound: len(value) > bound)):
            if keyword in schema and test(schema[keyword]):
                raise ValueError(f"{path}: violates {keyword}")
    if isinstance(value, list):
        prefix = schema.get("prefixItems", [])
        for index, item in enumerate(value):
            candidate = prefix[index] if index < len(prefix) else schema.get("items", True)
            validate_schema(item, candidate, f"{path}[{index}]", root)
        for keyword, test in (("minItems", lambda bound: len(value) < bound), ("maxItems", lambda bound: len(value) > bound)):
            if keyword in schema and test(schema[keyword]):
                raise ValueError(f"{path}: violates {keyword}")
        if schema.get("uniqueItems") and len({canonical(item) for item in value}) != len(value):
            raise ValueError(f"{path}: array values must be unique")
    if isinstance(value, str):
        if "pattern" in schema and not re.search(schema["pattern"], value):
            raise ValueError(f"{path}: string does not match pattern")
        for keyword, test in (("minLength", lambda bound: len(value) < bound), ("maxLength", lambda bound: len(value) > bound)):
            if keyword in schema and test(schema[keyword]):
                raise ValueError(f"{path}: violates {keyword}")
    if types["number"]:
        for keyword, test in (("minimum", lambda bound: number < json_number(bound)), ("maximum", lambda bound: number > json_number(bound)),
                              ("exclusiveMinimum", lambda bound: number <= json_number(bound)), ("exclusiveMaximum", lambda bound: number >= json_number(bound))):
            if keyword in schema and test(schema[keyword]):
                raise ValueError(f"{path}: violates {keyword}")
        if "multipleOf" in schema and number % json_number(schema["multipleOf"]) != 0:
            raise ValueError(f"{path}: violates multipleOf")


def _mask_markdown_math(text):
    """Hide GitHub math content, which is not parsed as Markdown links."""
    def blank(match):
        return "".join("\n" if char == "\n" else " " for char in match.group())
    text = re.sub(r"(?<!\\)\$\$[\s\S]*?(?<!\\)\$\$", blank, text)
    return re.sub(r"(?<!\\)\$(?!\$)(?:\\.|[^$\\\n])+(?<!\\)\$(?!\$)", blank, text)


def _without_markdown_code(text, preserve_inline=False):
    lines = []
    fence = None
    for line in text.splitlines(keepends=True):
        match = re.match(r"^\s{0,3}(`{3,}|~{3,})", line)
        if fence:
            if match and match.group(1)[0] == fence[0] and len(match.group(1)) >= len(fence) and not line[match.end():].strip():
                fence = None
            lines.append("\n" if line.endswith("\n") else "")
        elif match:
            fence = match.group(1)
            lines.append("\n" if line.endswith("\n") else "")
        else:
            # Same delimiter length must close a code span.  Replacing the span
            # content still permits links whose label is an inline code span.
            def code_span(match):
                # Keep the code text of a link label for source-name checks.
                if preserve_inline and match.start() > 0 and line[match.start()-1] == '[' and line[match.end():].startswith(']('):
                    return match.group()
                return ' ' * len(match.group())
            line = re.sub(r"(`+)(?!`)(.*?)(?<!`)\1(?!`)", code_span, line)
            lines.append(line)
    return _mask_markdown_math("".join(lines))


def markdown_anchors(text):
    """Return explicit HTML anchors and GitHub-style Markdown heading slugs."""
    anchors = set(re.findall(r"<(?:a|h[1-6])\b[^>]*\b(?:id|name)=[\"']([^\"']+)[\"']", _without_markdown_code(text), re.I))
    counts = {}
    # Code spans contribute their text to a heading slug, but fenced code does
    # not define headings.  Use a separate fence pass for this reason.
    fenced = False
    fence_char = ""
    fence_len = 0
    previous = ""
    for line in _mask_markdown_math(text).splitlines():
        fence = re.match(r"^\s{0,3}(`{3,}|~{3,})", line)
        if fence:
            mark = fence.group(1)
            if not fenced:
                fenced, fence_char, fence_len = True, mark[0], len(mark)
            elif mark[0] == fence_char and len(mark) >= fence_len and not line[fence.end():].strip():
                fenced = False
            previous = ""
            continue
        if fenced:
            continue
        match = re.match(r"^\s{0,3}#{1,6}\s+(.+?)(?:\s+#+\s*)?$", line)
        heading = match.group(1) if match else None
        if heading is None and re.fullmatch(r"\s{0,3}(?:=+|-+)\s*", line) and previous.strip():
            heading = previous.strip()
        if heading is not None:
            heading = re.sub(r"!?(?:\[([^\]]*)\])\([^)]*\)", r"\1", heading)
            heading = html.unescape(re.sub(r"<[^>]+>", "", heading)).lower()
            heading = "".join(char for char in heading if char in "-_ " or unicodedata.category(char)[0] in "LN")
            slug = re.sub(r"\s", "-", heading)
            duplicate = counts.get(slug, 0)
            counts[slug] = duplicate + 1
            anchors.add(slug + (f"-{duplicate}" if duplicate else ""))
        previous = line
    return anchors


def _markdown_links(text):
    clean = _without_markdown_code(text)
    # Reference definitions can precede or follow their uses.
    definitions = {}
    for match in re.finditer(r"^\s{0,3}\[([^\]]+)\]:\s*(?:<([^>]+)>|(\S+))", clean, re.M):
        definitions[" ".join(match.group(1).lower().split())] = match.group(2) or match.group(3)
        yield match.group(2) or match.group(3)
    for match in re.finditer(r"!?\[([^\]\n]*(?:\][^\[\]\n]*)?)\]\(", clean):
        start = match.end()
        cursor, depth = start, 1
        while cursor < len(clean) and depth:
            if clean[cursor] == "\\":
                cursor += 2
                continue
            if clean[cursor] == "(":
                depth += 1
            elif clean[cursor] == ")":
                depth -= 1
            cursor += 1
        if depth:
            raise ValueError("Unclosed Markdown link destination")
        body = clean[start:cursor - 1].strip()
        if body.startswith("<"):
            end = body.find(">")
            if end < 0:
                raise ValueError("Unclosed angle-bracket Markdown link destination")
            yield body[1:end]
        elif body:
            yield re.split(r"\s+[\"'(]", body, maxsplit=1)[0]
    for match in re.finditer(r"!?\[([^\]\n]+)\](?:\[([^\]\n]*)\])?", clean):
        if match.end() < len(clean) and clean[match.end()] in "(:":
            continue
        label = match.group(2) if match.group(2) else match.group(1)
        key = " ".join(label.lower().split())
        if key in definitions:
            yield definitions[key]
        elif match.group(2) is not None:
            raise ValueError(f"Undefined Markdown link reference: {label}")
    for match in re.finditer(r"\b(?:href|src)=[\"']([^\"']+)[\"']", clean, re.I):
        yield match.group(1)


# Shared checks also used by the repository assembler.
from pathlib import Path, PurePosixPath
from collections import Counter
import argparse
import sys

sys.dont_write_bytecode = True
REPOSITORY = 'https://github.com/' + 'pm' + 'aronow/llm-audit-lean'
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
STATUSES = ['proved', 'counterexample_proved']
STATUS_DESCRIPTIONS = {
    'proved': 'proves the component under its stated assumptions (for a corrected statement, the corrected version)',
    'counterexample_proved': 'belongs to a refutation of the claim as recorded in its target, under its stated assumptions: proves the counterexample itself or a step of it; where the target states a specific reading of the printed text, the refutation applies to that reading',
}
KINDS = ['headline_result', 'result_touched_by_finding', 'counterexample', 'corrected_statement']
AREAS = {
    'probability': 'Probability', 'asymptotic-statistics': 'Asymptotic statistics',
    'randomization-inference': 'Randomization inference',
    'experimental-design-and-estimation': 'Experimental design and estimation',
    'survey-sampling': 'Survey sampling', 'interference-and-networks': 'Interference and networks',
    'causal-identification': 'Causal identification',
    'partial-identification-and-bounds': 'Partial identification and bounds',
    'regression-and-variance-estimation': 'Regression and variance estimation',
    'resampling': 'Resampling', 'optimization-and-computation': 'Optimization and computation',
    'foundations': 'Foundations',
}
SECTIONS = {'top_25': 'The most helpful results', 'reusable_libraries': 'Reusable libraries',
            'counterexamples': 'Counterexamples and corrections', 'mathlib_candidates': 'Candidates for Mathlib',
            'further_useful': 'Further useful results'}


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2, allow_nan=False) + '\n').encode()


PUBLIC_SECTION_TITLE = 'Replication on Wikipedia Pages of Dead and Retired Senators'
MODIFICATION_NOTICE = 'Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.'


def leading_header(text):
    """Return the leading comment's span, or None if code comes first."""
    start = len(text) - len(text.lstrip())
    if text.startswith('/-', start):
        cursor, depth = start + 2, 1
        while cursor < len(text) and depth:
            if text.startswith('/-', cursor):
                depth += 1
                cursor += 2
            elif text.startswith('-/', cursor):
                depth -= 1
                cursor += 2
            else:
                cursor += 1
        if depth:
            raise ValueError('Unbalanced leading Lean comment')
        return start, cursor
    if text.startswith('--', start):
        cursor = start
        while cursor < len(text):
            stop = text.find('\n', cursor)
            stop = len(text) if stop < 0 else stop + 1
            if text[cursor:stop].strip() and not text[cursor:stop].lstrip().startswith('--'):
                break
            cursor = stop
        return start, cursor
    return None


def statlean_adaptation_header(text):
    span = leading_header(text)
    return bool(span and ('Upstream project: StatLean.' in text[span[0]:span[1]] or re.search(r'adapted\s+from\s+(?:the\s+)?(?:pinned\s+)?(?:Apache-2\.0\s+)?StatLean\b', text[span[0]:span[1]], re.I)))


# Third-party requirements: {"apache_files": ["AronowAudit/External/Causalean/Experimentation/DesignBased/Designs/CompleteRandomization.lean", "AronowAudit/External/Causalean/Experimentation/DesignBased/Estimators/DifferenceInMeans.lean", "AronowAudit/External/Causalean/Experimentation/DesignBased/Estimators/NeymanVariance.lean", "AronowAudit/External/Causalean/Experimentation/DesignBased/FinitePopulationVariance.lean", "AronowAudit/External/Causalean/Experimentation/DesignBased/InProb.lean", "AronowAudit/External/Causalean/Experimentation/DesignBased/Risk.lean", "AronowAudit/External/Causalean/Experimentation/FinitePopulationMoments.lean", "AronowAudit/External/Causalean/Mathlib/Analysis/SignedTailRepresentation.lean", "AronowAudit/External/Causalean/Mathlib/Analysis/SpecialFunctions/Jacobi/Basic.lean", "AronowAudit/External/Causalean/Mathlib/Analysis/SpecialFunctions/Jacobi/Beta.lean", "AronowAudit/External/Causalean/Mathlib/Analysis/SpecialFunctions/Jacobi/Calculus.lean", "AronowAudit/External/Causalean/Mathlib/Analysis/SpecialFunctions/Jacobi/EndpointEnergy.lean", "AronowAudit/External/Causalean/Mathlib/Analysis/SpecialFunctions/Jacobi/Legendre.lean", "AronowAudit/External/Causalean/Mathlib/Probability/Distributions/Gaussian/Standard.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/Bounds.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/Bounds_Part1.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/Bounds_Part2.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/CLT.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/DepGraphCLT.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/DependencyCLT.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/Solution.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/StandardizedDepGraphCLT.lean", "AronowAudit/External/Causalean/Stat/CLT/ChiSquared.lean", "AronowAudit/External/Causalean/Stat/CLT/ChiSquaredProjection.lean", "AronowAudit/External/Causalean/Stat/CLT/GaussianCharFunBridge.lean", "AronowAudit/External/Causalean/Stat/Coupling/Basic.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/Coupling.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/FrechetHoeffding.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/FrechetHoeffdingAttainment.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/Hoeffding.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/HoeffdingFubini.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/HoeffdingFubiniIntegrability.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/Optimality.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/PIT.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/Survival.lean", "AronowAudit/External/Causalean/Stat/FiniteDesign/Chebyshev.lean", "AronowAudit/External/Causalean/Stat/FiniteDesign/DesignCore.lean", "AronowAudit/External/Causalean/Stat/FiniteDesign/FiniteDesignMeasure.lean", "AronowAudit/External/Causalean/Stat/Limit/Modes.lean", "AronowAudit/External/Causalean/Stat/Limit/StochasticOrder.lean", "AronowAudit/External/Causalean/Stat/OrderStatistic/Basic.lean", "AronowAudit/External/Causalean/Stat/OrderStatistic/Dirichlet.lean", "AronowAudit/External/Causalean/Stat/OrderStatistic/Moments.lean", "AronowAudit/External/Causalean/Stat/OrderStatistic/SimplexIntegrals.lean", "AronowAudit/External/Causalean/Stat/Quantile/Quantile.lean", "AronowAudit/External/Causalean/Stat/Quantile/Transport.lean", "AronowAudit/External/Causalean/Tactic/Attr.lean", "AronowAudit/External/Causalean/Tactic/IntegralLinearity.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/Core/CandidateIF.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/Core/Hilbert.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/Core/NondominatedQMDPath.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/Core/NondominatedQMDProductComparison.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/Core/QMDPath.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/DQM/Defs.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/DQM/Properties.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/BracketingDonsker.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/BrownianBridge.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/Carrier.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/Characterization.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/FiniteCarrier.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/GPNet.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/GPProcess.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/NecessityTightness.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/PBridgeTight.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/SufficiencyDiscretization.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/Bracketing.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/ChainingAssembly.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/Donsker.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/DonskerBracketing.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/EmpiricalDistribution.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/EmpiricalMeasure.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/EmpiricalProcess.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/EquicontinuityChaining.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/FunctionClass.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/GlivenkoCantelli.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/HalfLineBracketing.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/HalfLineIndicators.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/HalfLineQuantile.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/LocalizedClass.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/Maximal.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/MaximalBernstein.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/MaximalOrlicz.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/NestedPartition.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/PointwiseDense.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/SupMeasurability.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Contiguity.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/EmpiricalAverage.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/GaussianMGF.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/HellingerProduct.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/IIdJointLaw.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/IidWLLN.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/InProbability.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/IntegrableTail.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/L2.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/L2Asymptotics.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/L2Tail.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/LogTaylor.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/LpSeminorm.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Markov.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/MeanVarConvergence.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/MeasurableSelectionRandomFunctions.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/MultivariateCLT.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/OuterIntegration/OuterExpectation.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/PairwiseQMDAnalytic.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/PiWithDensity.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Probability/GaussianChaining.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Probability/GaussianMaximal.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Probability/IsonormalProcess.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Probability/SubgaussianGaussian.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Prohorov.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/QMDAnalytic.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/RnDerivSqrt.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Slutsky.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/SqrtLogProduct.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/WeakConvergence/Outer.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/WeakConvergence/OuterFiniteProduct.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/WeakConvergence/OuterMapping.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/WeakConvergence/OuterSlutsky.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/WeakConvergence/OuterTightness.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/WeakConvergence/TightCoordinateUniqueness.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/LocalAsymptoticNormality/LANExpansion.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/LowerBounds/T6_FinDimLAN/Abstract1DLAN.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/LowerBounds/T6_FinDimLAN/NondominatedQMDLAN.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/LowerBounds/T6_FinDimLAN/NondominatedQMDLeCamThird.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ParametricFamily/Defs.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ParametricFamily/FisherInformation.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ParametricFamily/Score.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ParametricFamily/SqrtDensityRatio.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/Probability/ScoreCLT.lean", "AronowAudit/External/StatLean/Bayesian/ForMathlib/MultinomialDist.lean", "AronowAudit/External/StatLean/ComputationalStatistics/Core/Defs.lean", "AronowAudit/External/StatLean/ComputationalStatistics/Core/EmpiricalMeasure.lean", "AronowAudit/External/StatLean/ComputationalStatistics/ForMathlib/PiMoments.lean", "AronowAudit/External/StatLean/ComputationalStatistics/Resampling/BootstrapMoments.lean", "AronowAudit/External/StatLean/ComputationalStatistics/Resampling/CategoricalCounts.lean", "AronowAudit/External/StatLean/ComputationalStatistics/Resampling/MultinomialMoments.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/ForMathlib/GaussianAbsMoment.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/ForMathlib/IndepTransport.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Maximal/FiniteMaximal.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/McDiarmid/CondHoeffding.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/McDiarmid/DoobDecomposition.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/McDiarmid/McDiarmid.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/SubGaussian/Defs.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/SubGaussian/TailBounds.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/Empirical.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/GaussianMax.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/GaussianVector.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/NormAddMeanZero.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/Rademacher.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/SignFlip.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/Symmetrization.lean", "AronowAudit/External/StatLean/HypothesisTesting/ForMathlib/BerryEsseen.lean", "AronowAudit/External/StatLean/HypothesisTesting/ForMathlib/CombinatorialCLT.lean", "AronowAudit/External/StatLean/HypothesisTesting/ForMathlib/DKWUniform.lean", "AronowAudit/External/StatLean/HypothesisTesting/ForMathlib/EsseenSmoothing.lean", "AronowAudit/External/StatLean/HypothesisTesting/ForMathlib/PermutationMarginals.lean", "AronowAudit/External/StatLean/HypothesisTesting/ForMathlib/SteinMethod.lean", "AronowAudit/External/StatLean/MultipleTesting/ForMathlib/ChiSquared.lean", "AronowAudit/External/StatLean/MultipleTesting/ForMathlib/ChiSquaredInverseMoment.lean", "AronowAudit/External/StatLean/MultipleTesting/ForMathlib/GammaMoments.lean", "AronowAudit/External/StatLean/MultipleTesting/ForMathlib/GaussianSquareMGF.lean", "AronowAudit/P001/P001_Foundations.lean", "AronowAudit/P001/Wave1/Gap/GLP0011B3.lean", "AronowAudit/P001/Wave1/Lib/TailA/EmpiricalCDFBound.lean", "AronowAudit/P004/P004_MCCompletion.lean", "AronowAudit/P009/Wave1/Gap/GLP0091B10.lean", "AronowAudit/P011/P011_CoverageCompletion.lean", "AronowAudit/P011/P011_OracleCompletion.lean", "AronowAudit/P011/P011_ProbabilityCompletion.lean", "AronowAudit/P013/Wave1/Gap/GP013P012B1.lean", "AronowAudit/P015/P015_FiniteConditioning.lean", "AronowAudit/P022/Wave1/Gap/GLP022B3.lean", "AronowAudit/P023/Wave1/Gap/GLP023B3.lean", "AronowAudit/P023/Wave1/Gap/GLP023B4c.lean", "AronowAudit/P033/Wave1/Gap/GLP010P033P033B2.lean", "AronowAudit/P033/Wave1/Gap/GLP010P033P033B3.lean", "AronowAudit/P037/P037_VaryingLindeberg.lean", "AronowAudit/P053/P053_NormalQuantiles.lean", "AronowAudit/P061/P061_Foundations.lean"], "listed_files": ["AronowAudit/External/Causalean/Experimentation/DesignBased/Designs/CompleteRandomization.lean", "AronowAudit/External/Causalean/Experimentation/DesignBased/Estimators/DifferenceInMeans.lean", "AronowAudit/External/Causalean/Experimentation/DesignBased/Estimators/NeymanVariance.lean", "AronowAudit/External/Causalean/Experimentation/DesignBased/FinitePopulationVariance.lean", "AronowAudit/External/Causalean/Experimentation/DesignBased/InProb.lean", "AronowAudit/External/Causalean/Experimentation/DesignBased/Risk.lean", "AronowAudit/External/Causalean/Experimentation/FinitePopulationMoments.lean", "AronowAudit/External/Causalean/Mathlib/Analysis/SignedTailRepresentation.lean", "AronowAudit/External/Causalean/Mathlib/Analysis/SpecialFunctions/Jacobi/Basic.lean", "AronowAudit/External/Causalean/Mathlib/Analysis/SpecialFunctions/Jacobi/Beta.lean", "AronowAudit/External/Causalean/Mathlib/Analysis/SpecialFunctions/Jacobi/Calculus.lean", "AronowAudit/External/Causalean/Mathlib/Analysis/SpecialFunctions/Jacobi/EndpointEnergy.lean", "AronowAudit/External/Causalean/Mathlib/Analysis/SpecialFunctions/Jacobi/Legendre.lean", "AronowAudit/External/Causalean/Mathlib/Probability/Distributions/Gaussian/Standard.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/Bounds.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/Bounds_Part1.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/Bounds_Part2.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/CLT.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/DepGraphCLT.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/DependencyCLT.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/Solution.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/StandardizedDepGraphCLT.lean", "AronowAudit/External/Causalean/Stat/CLT/ChiSquared.lean", "AronowAudit/External/Causalean/Stat/CLT/ChiSquaredProjection.lean", "AronowAudit/External/Causalean/Stat/CLT/GaussianCharFunBridge.lean", "AronowAudit/External/Causalean/Stat/Coupling/Basic.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/Coupling.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/FrechetHoeffding.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/FrechetHoeffdingAttainment.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/Hoeffding.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/HoeffdingFubini.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/HoeffdingFubiniIntegrability.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/Optimality.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/PIT.lean", "AronowAudit/External/Causalean/Stat/Coupling/Monotone/ProductLoss/Survival.lean", "AronowAudit/External/Causalean/Stat/FiniteDesign/Chebyshev.lean", "AronowAudit/External/Causalean/Stat/FiniteDesign/DesignCore.lean", "AronowAudit/External/Causalean/Stat/FiniteDesign/FiniteDesignMeasure.lean", "AronowAudit/External/Causalean/Stat/Limit/Modes.lean", "AronowAudit/External/Causalean/Stat/Limit/StochasticOrder.lean", "AronowAudit/External/Causalean/Stat/OrderStatistic/Basic.lean", "AronowAudit/External/Causalean/Stat/OrderStatistic/Dirichlet.lean", "AronowAudit/External/Causalean/Stat/OrderStatistic/Moments.lean", "AronowAudit/External/Causalean/Stat/OrderStatistic/SimplexIntegrals.lean", "AronowAudit/External/Causalean/Stat/Quantile/Quantile.lean", "AronowAudit/External/Causalean/Stat/Quantile/Transport.lean", "AronowAudit/External/Causalean/Tactic/Attr.lean", "AronowAudit/External/Causalean/Tactic/IntegralLinearity.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/Core/CandidateIF.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/Core/Hilbert.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/Core/NondominatedQMDPath.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/Core/NondominatedQMDProductComparison.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/Core/QMDPath.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/DQM/Defs.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/DQM/Properties.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/BracketingDonsker.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/BrownianBridge.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/Carrier.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/Characterization.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/FiniteCarrier.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/GPNet.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/GPProcess.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/NecessityTightness.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/PBridgeTight.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/AbstractDonsker/SufficiencyDiscretization.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/Bracketing.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/ChainingAssembly.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/Donsker.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/DonskerBracketing.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/EmpiricalDistribution.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/EmpiricalMeasure.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/EmpiricalProcess.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/EquicontinuityChaining.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/FunctionClass.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/GlivenkoCantelli.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/HalfLineBracketing.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/HalfLineIndicators.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/HalfLineQuantile.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/LocalizedClass.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/Maximal.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/MaximalBernstein.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/MaximalOrlicz.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/NestedPartition.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/PointwiseDense.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/EmpiricalProcess/SupMeasurability.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Contiguity.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/EmpiricalAverage.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/GaussianMGF.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/HellingerProduct.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/IIdJointLaw.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/IidWLLN.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/InProbability.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/IntegrableTail.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/L2.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/L2Asymptotics.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/L2Tail.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/LogTaylor.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/LpSeminorm.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Markov.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/MeanVarConvergence.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/MeasurableSelectionRandomFunctions.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/MultivariateCLT.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/OuterIntegration/OuterExpectation.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/PairwiseQMDAnalytic.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/PiWithDensity.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Probability/GaussianChaining.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Probability/GaussianMaximal.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Probability/IsonormalProcess.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Probability/SubgaussianGaussian.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Prohorov.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/QMDAnalytic.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/RnDerivSqrt.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/Slutsky.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/SqrtLogProduct.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/WeakConvergence/Outer.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/WeakConvergence/OuterFiniteProduct.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/WeakConvergence/OuterMapping.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/WeakConvergence/OuterSlutsky.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/WeakConvergence/OuterTightness.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ForMathlib/WeakConvergence/TightCoordinateUniqueness.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/LocalAsymptoticNormality/LANExpansion.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/LowerBounds/T6_FinDimLAN/Abstract1DLAN.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/LowerBounds/T6_FinDimLAN/NondominatedQMDLAN.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/LowerBounds/T6_FinDimLAN/NondominatedQMDLeCamThird.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ParametricFamily/Defs.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ParametricFamily/FisherInformation.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ParametricFamily/Score.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/ParametricFamily/SqrtDensityRatio.lean", "AronowAudit/External/StatLean/AsymptoticStatistics/Probability/ScoreCLT.lean", "AronowAudit/External/StatLean/Bayesian/ForMathlib/MultinomialDist.lean", "AronowAudit/External/StatLean/ComputationalStatistics/Core/Defs.lean", "AronowAudit/External/StatLean/ComputationalStatistics/Core/EmpiricalMeasure.lean", "AronowAudit/External/StatLean/ComputationalStatistics/ForMathlib/PiMoments.lean", "AronowAudit/External/StatLean/ComputationalStatistics/Resampling/BootstrapMoments.lean", "AronowAudit/External/StatLean/ComputationalStatistics/Resampling/CategoricalCounts.lean", "AronowAudit/External/StatLean/ComputationalStatistics/Resampling/MultinomialMoments.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/ForMathlib/GaussianAbsMoment.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/ForMathlib/IndepTransport.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Maximal/FiniteMaximal.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/McDiarmid/CondHoeffding.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/McDiarmid/DoobDecomposition.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/McDiarmid/McDiarmid.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/SubGaussian/Defs.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/SubGaussian/TailBounds.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/Empirical.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/GaussianMax.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/GaussianVector.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/NormAddMeanZero.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/Rademacher.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/SignFlip.lean", "AronowAudit/External/StatLean/ConcentrationInequalities/Symmetrization/Symmetrization.lean", "AronowAudit/External/StatLean/HypothesisTesting/ForMathlib/BerryEsseen.lean", "AronowAudit/External/StatLean/HypothesisTesting/ForMathlib/CombinatorialCLT.lean", "AronowAudit/External/StatLean/HypothesisTesting/ForMathlib/DKWUniform.lean", "AronowAudit/External/StatLean/HypothesisTesting/ForMathlib/EsseenSmoothing.lean", "AronowAudit/External/StatLean/HypothesisTesting/ForMathlib/PermutationMarginals.lean", "AronowAudit/External/StatLean/HypothesisTesting/ForMathlib/SteinMethod.lean", "AronowAudit/External/StatLean/MultipleTesting/ForMathlib/ChiSquared.lean", "AronowAudit/External/StatLean/MultipleTesting/ForMathlib/ChiSquaredInverseMoment.lean", "AronowAudit/External/StatLean/MultipleTesting/ForMathlib/GammaMoments.lean", "AronowAudit/External/StatLean/MultipleTesting/ForMathlib/GaussianSquareMGF.lean", "AronowAudit/P001/P001_Foundations.lean", "AronowAudit/P001/Wave1/Gap/GLP0011B3.lean", "AronowAudit/P001/Wave1/Lib/TailA/EmpiricalCDFBound.lean", "AronowAudit/P004/P004_MCCompletion.lean", "AronowAudit/P009/Wave1/Gap/GLP0091B10.lean", "AronowAudit/P011/P011_CoverageCompletion.lean", "AronowAudit/P011/P011_OracleCompletion.lean", "AronowAudit/P011/P011_ProbabilityCompletion.lean", "AronowAudit/P013/Wave1/Gap/GP013P012B1.lean", "AronowAudit/P015/P015_FiniteConditioning.lean", "AronowAudit/P018/Wave1/Gap/GLP0182B3.lean", "AronowAudit/P018/Wave1/Gap/GP0182B2b.lean", "AronowAudit/P022/Wave1/Gap/GLP022B3.lean", "AronowAudit/P023/Wave1/Gap/GLP023B3.lean", "AronowAudit/P023/Wave1/Gap/GLP023B4c.lean", "AronowAudit/P033/Wave1/Gap/GLP010P033P033B2.lean", "AronowAudit/P033/Wave1/Gap/GLP010P033P033B3.lean", "AronowAudit/P037/P037_VaryingLindeberg.lean", "AronowAudit/P053/P053_NormalQuantiles.lean", "AronowAudit/P061/P061_Foundations.lean"], "original_in_vendor_directories": ["AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/AlmostEverywhereDepGraphCLT.lean", "AronowAudit/External/Causalean/Mathlib/Probability/SteinMethod/AlmostEverywhereDepGraphVariance.lean", "AronowAudit/External/StatLean/MultipleTesting/ForMathlib/GaussianRatioMoments.lean"]}


def lean_comment_text(text):
    """Collect source comments, including embedded headers, excluding strings."""
    comments = []
    cursor = 0
    while cursor < len(text):
        if text.startswith('--', cursor):
            stop = text.find('\n', cursor)
            stop = len(text) if stop < 0 else stop
            comments.append(text[cursor:stop])
            cursor = stop
        elif text.startswith('/-', cursor):
            start, depth = cursor, 1
            cursor += 2
            while cursor < len(text) and depth:
                if text.startswith('/-', cursor):
                    depth += 1
                    cursor += 2
                elif text.startswith('-/', cursor):
                    depth -= 1
                    cursor += 2
                else:
                    cursor += 1
            if depth:
                raise ValueError('Unbalanced Lean comment')
            comments.append(text[start:cursor])
        elif text[cursor] == '"':
            cursor += 1
            while cursor < len(text):
                if text[cursor] == '\\':
                    cursor += 2
                elif text[cursor] == '"':
                    cursor += 1
                    break
                else:
                    cursor += 1
        elif text[cursor] == "'" and (cursor == 0 or not re.match(r"[\w']", text[cursor-1])):
            char = re.match(r"'(?:[^'\\\n]|\\[^\n])'", text[cursor:])
            cursor += len(char[0]) if char else 1
        else:
            cursor += 1
    return '\n'.join(comments)


def has_modification_notice(text):
    comments = lean_comment_text(text)
    comments = re.sub(r'\b(?:not|never)\s+(?:been\s+)?(?:adapted|modified)\b|\bno\s+modifications\b', '', comments, flags=re.I)
    return bool(re.search(r'\b(?:adapted|adapts|modified|modifications)\b', comments, re.I))


def local_vendor_header(path):
    safe_relative(path)
    parts = path.split('/')
    if len(parts) < 4 or parts[:2] != ['AronowAudit', 'External'] or parts[2] not in {'Causalean', 'StatLean'} or not path.endswith('.lean'):
        raise ValueError(f'Invalid original local vendor path: {path}')
    project = parts[2]
    return f'Local file of llm-audit-lean, not taken from {project}; it builds on the vendored {project} code in this directory tree.'


def attribution_requirements(files):
    source = files.get('scripts/check_repository.py', b'').decode()
    match = re.search(r'^# Third-party requirements: (.+)$', source, re.M)
    value = json.loads(match[1]) if match else None
    return value or {'apache_files': [], 'listed_files': []}


def has_third_party_copyright(text):
    for match in re.finditer(r'copyright[^\n]*', lean_comment_text(text), re.I):
        holder = re.split(r'\.\s+(?:Released|All rights|Licensed)', match[0], maxsplit=1, flags=re.I)[0]
        holder = holder.replace('P. M. Aronow', '')
        holder = re.sub(r'(?i)copyright|\(c\)|\b(?:and|the)\b|\d|[^\w]', '', holder)
        if holder:
            return True
    return False


def check_modification_notices(files, requirements=None):
    requirements = attribution_requirements(files) if requirements is None else requirements
    listed = set(requirements['listed_files'])
    apache = set(requirements['apache_files'])
    local = set(requirements.get('original_in_vendor_directories', []))
    if local & (apache | listed):
        raise ValueError('Original local vendor files cannot be listed as third-party adaptations')
    notice_files = set(re.findall(r'^  (AronowAudit/[^\n]+\.lean)$', files.get('NOTICE', b'').decode(), re.M))
    for path in sorted(listed):
        safe_relative(path)
        if path not in files or not path.endswith('.lean'):
            raise ValueError(f'Missing third-party adapted file: {path}')
        if path not in notice_files:
            raise ValueError(f'NOTICE omits adapted file: {path}')
    for path in sorted(local):
        expected = local_vendor_header(path)
        if path not in files:
            raise ValueError(f'Missing original local vendor file: {path}')
        text = files[path].decode()
        span = leading_header(text)
        if not span or expected not in text[span[0]:span[1]]:
            raise ValueError(f'Missing original local vendor header: {path}')
        comments = lean_comment_text(text)
        if MODIFICATION_NOTICE in comments or 'Upstream project:' in comments:
            raise ValueError(f'Original local vendor file has an upstream modification header: {path}')
        if path not in notice_files or expected not in files.get('NOTICE', b'').decode():
            raise ValueError(f'NOTICE omits original local vendor file description: {path}')
    count = 0
    for path, data in files.items():
        if not path.endswith('.lean'):
            continue
        text = data.decode()
        required = path not in local and (path in apache or path.startswith('AronowAudit/External/') or (path.startswith('AronowAudit/P037/') and statlean_adaptation_header(text)))
        if required:
            if not has_modification_notice(text):
                raise ValueError(f'Missing leading modification notice or adapted statement: {path}')
            count += 1
        if has_third_party_copyright(text) and path not in notice_files:
            raise ValueError(f'NOTICE omits third-party copyright file: {path}')
    return count


def safe_relative(path):
    p = PurePosixPath(path)
    if not isinstance(path, str) or not path or p.is_absolute() or '..' in p.parts or '\\' in path or str(p) != path:
        raise ValueError(f'Invalid repository path: {path!r}')
    return path


def read_files(root):
    files = {}
    for p in sorted(root.rglob('*')):
        if '.git' in p.relative_to(root).parts or '.lake' in p.relative_to(root).parts or '__pycache__' in p.relative_to(root).parts:
            continue
        if p.is_symlink():
            raise ValueError(f'Symbolic link is not allowed: {p.relative_to(root)}')
        if p.is_file():
            files[p.relative_to(root).as_posix()] = p.read_bytes()
    return files


def source_index(files):
    by_file, by_name = {}, {}
    for path, data in sorted(files.items()):
        if not path.endswith('.lean'):
            continue
        declarations = scan_declarations(data.decode())
        by_file[path] = declarations
        for name, lines in declarations.items():
            for line in lines:
                by_name.setdefault(name, []).append((path, line))
    return by_file, by_name


def check_location(row, by_file):
    path = safe_relative(row['file'])
    line = row['line']
    if type(line) is not int or line < 1 or by_file.get(path, {}).get(row['lean_name']) != [line]:
        raise ValueError(f'Declaration location mismatch: {row["lean_name"]} at {path}#L{line}')
    if row.get('module', path[:-5].replace('/', '.')) != path[:-5].replace('/', '.'):
        raise ValueError(f'Module/path mismatch: {row["lean_name"]}')



def base_lean_name(name):
    return re.sub(r'\.\{[^}]*\}$', '', name)


def published_premises(name, files, by_file, by_name, source_cache=None):
    """Conservatively follow explicit Prop statement aliases, never proof bodies."""
    visited = set()
    found = set()
    source_cache = {} if source_cache is None else source_cache
    literal = re.compile(r'AronowAudit\.Literature\.\w+(?:\.\w+)*(?:\.\{[^}\n]+\})?')
    reference = re.compile(r'AronowAudit\.\w+(?:\.\w+)*')

    def visit(current):
        if current in visited:
            return
        visited.add(current)
        locations = by_name.get(current, [])
        if len(locations) != 1:
            raise ValueError(f'Cannot resolve conditional statement declaration: {current}')
        path, line = locations[0]
        if path not in source_cache:
            source_cache[path] = files[path].decode().splitlines()
        lines = source_cache[path]
        following = [n for ns in by_file[path].values() for n in ns if n > line]
        end = min(following) - 1 if following else len(lines)
        source = _mask_lean('\n'.join(lines[line-1:end]))
        header, separator, body = source.partition(':=')
        if not separator and re.search(r'\binstance\b', header):
            header, separator, body = source.partition('where')
        if not separator:
            raise ValueError(f'Cannot locate conditional declaration statement: {current}')
        kind = re.search(r'\b(theorem|lemma|def|abbrev|instance)\b', header)
        if kind is None:
            raise ValueError(f'Unsupported declaration statement form: {current}')
        expression = header
        if kind[1] in {'def', 'abbrev'}:
            if re.search(r':\s*Prop\s*$', header):
                expression = header + '\n' + body
        for match in literal.finditer(expression):
            tail = expression[match.end():]
            binder = re.search(r'[({\[][^(){}\[\]:]+:\s*$', expression[:match.start()])
            if not re.match(r'\s*→', tail) and not (binder and re.match(r'\s*[)}\]]', tail)):
                continue
            written = match[0]
            base = base_lean_name(written)
            if len(by_name.get(base, [])) != 1:
                raise ValueError(f'Published-theorem premise does not resolve: {written}')
            suffix = written[len(base):]
            # Symbolic universes belong to the surrounding definition. Retain
            # concrete instantiations such as .{0}, as used in the declaration.
            if suffix and not re.fullmatch(r'\.\{\s*\d+(?:\s*,\s*\d+)*\s*\}', suffix):
                written = base
            found.add(written)
        for match in reference.finditer(expression):
            candidate = match[0]
            if candidate == current or candidate.startswith('AronowAudit.Literature.'):
                continue
            if candidate.endswith('_statement'):
                visit(candidate)
    visit(base_lean_name(name))
    return sorted(found)


def cached_premise_extractor(files, by_file, by_name):
    """Cache analysis by declaration name, and decoded source lines by file."""
    cache, source_cache = {}, {}
    def extract(name):
        key = base_lean_name(name)
        if key not in cache:
            cache[key] = published_premises(key, files, by_file, by_name, source_cache)
        return cache[key]
    return extract


def check_axioms(name, axioms):
    if not isinstance(axioms, list) or not all(isinstance(a, str) for a in axioms) or len(axioms) != len(set(axioms)):
        raise ValueError(f'Invalid axiom list: {name}')
    extra = set(axioms) - STANDARD_AXIOMS
    if extra:
        raise ValueError(f'Non-standard axioms for {name}: {sorted(extra)}')


def lean_gaps(path, data):
    clean = _mask_lean(data.decode())
    clean = re.sub(r'«[^»]*»', lambda m: ''.join('\n' if ch == '\n' else ' ' for ch in m[0]), clean)
    hits = []
    for match in re.finditer(r'(?<![\w\'«])(?:sorry|admit)(?![\w\'»])', clean):
        hits.append({'file': path, 'line': clean.count('\n', 0, match.start()) + 1,
                     'kind': 'lean-proof-gap', 'text': match.group()})
    return hits


def content_hits(files):
    """Return every prohibited occurrence with its file and one-based line."""
    patterns = {
        'local-path': re.compile('|'.join(re.escape(s) for s in [
            '/' + 'Users/', '/' + 'home/', '~' + '/', '/' + 'private/',
            'ru' + 'ns/', 'reg' + 'istry/', 'lean' + '-work'])),
        'email': re.compile(r'[A-Za-z0-9.!#$%&\x27*+/=?^_`{|}~-]+@[A-Za-z0-9](?:[A-Za-z0-9.-]*[A-Za-z0-9])?\.[A-Za-z]{2,}'),
        'account-name': re.compile('pm' + 'aronow', re.I),
    }
    process = re.compile(r'\b(?:Sol|Codex|Claude|validator|referee|mapper|orchestrator|subagent|frozen|superseded|withdrawn|retired)\b|dx-|batch\d|stage\d', re.I)
    hits = []
    for path, data in sorted(files.items()):
        text = data.decode('utf-8')
        for number, original in enumerate(text.splitlines(), 1):
            line = original.replace(REPOSITORY, '')
            for kind, pattern in patterns.items():
                for match in pattern.finditer(line):
                    hits.append({'file': path, 'line': number, 'kind': kind, 'text': match.group()})
            if path == 'README.md' or path.startswith(('docs/', 'catalog/')):
                process_line = line.replace(PUBLIC_SECTION_TITLE, "")
                for match in process.finditer(process_line):
                    if path == 'README.md' and original.startswith('**Who wrote it.**') and match.group().lower() in {'sol', 'codex', 'claude'}:
                        continue
                    hits.append({'file': path, 'line': number, 'kind': 'process-word', 'text': match.group()})
        if path.endswith('.lean'):
            hits.extend(lean_gaps(path, data))
    return hits


def check_math(files):
    for path, data in files.items():
        if path.endswith('.md'):
            text = data.decode()
            if any(r'\operatorname' in span for span in markdown_math_spans(text)):
                raise ValueError(f'Unsupported GitHub math macro operatorname: {path}')
            if render_markdown_math(text, curated=True, field=path) != text:
                raise ValueError(f'Mathematics is not in GitHub format: {path}')


def check_links(files):
    count = 0
    anchors = {}
    line_counts = {}
    declaration_cache = {}

    def declarations(path):
        if path not in declaration_cache:
            declaration_cache[path] = scan_declarations(files[path].decode())
        return declaration_cache[path]

    for source, data in sorted(files.items()):
        if not source.endswith('.md'):
            continue
        # Generated source links name their declaration in an inline-code label.
        for label, destination in re.findall(r'\[`([^`]+)`\]\(([^)]+)\)', _without_markdown_code(data.decode(), preserve_inline=True)):
            url = urlsplit(destination)
            if url.scheme or url.netloc or not url.path.endswith('.lean'):
                continue
            match = re.fullmatch(r'L([1-9][0-9]*)', url.fragment)
            if not match:
                continue
            target = posixpath.normpath(posixpath.join(posixpath.dirname(source), unquote(url.path)))
            if target not in files or declarations(target).get(label) != [int(match[1])]:
                raise ValueError(f'{source}: named source link does not hold its declaration: {label}: {destination}')
        for raw in _markdown_links(data.decode()):
            raw = html.unescape(re.sub(r'\\([()\[\] <>])', r'\1', raw))
            url = urlsplit(raw)
            if url.scheme or url.netloc:
                continue
            path = unquote(url.path)
            if path.startswith('/'):
                raise ValueError(f'{source}: absolute Markdown link: {raw}')
            target = posixpath.normpath(posixpath.join(posixpath.dirname(source), path)) if path else source
            if target == '..' or target.startswith('../'):
                raise ValueError(f'{source}: Markdown link escapes repository: {raw}')
            if path.endswith('/') or target == '.':
                prefix = '' if target == '.' else target + '/'
                if url.fragment or not any(p.startswith(prefix) for p in files):
                    raise ValueError(f'{source}: invalid directory link: {raw}')
            else:
                if target not in files:
                    raise ValueError(f'{source}: missing Markdown link target: {raw}')
                fragment = unquote(url.fragment)
                if fragment:
                    m = re.fullmatch(r'L([1-9][0-9]*)(?:-L([1-9][0-9]*))?', fragment)
                    if m:
                        if target not in line_counts:
                            line_counts[target] = len(files[target].splitlines())
                        first, last = int(m[1]), int(m[2] or m[1])
                        if first > last or last > line_counts[target]:
                            raise ValueError(f'{source}: invalid source line anchor: {raw}')
                        if target.endswith('.lean') and first not in {n for locations in declarations(target).values() for n in locations}:
                            raise ValueError(f'{source}: source anchor does not hold a declaration: {raw}')
                    elif target.endswith('.md'):
                        if target not in anchors:
                            anchors[target] = markdown_anchors(files[target].decode())
                        if fragment not in anchors[target]:
                            raise ValueError(f'{source}: missing heading anchor: {raw}')
                    else:
                        raise ValueError(f'{source}: unsupported anchor: {raw}')
            count += 1
    return count


def record_count(path, data):
    if path.endswith('.jsonl'):
        return len(data.splitlines())
    if path.endswith('.json'):
        value = json.loads(data)
        return len(value) if isinstance(value, list) else 1
    return None


def coverage(results, highlights):
    located = [{'file': r['file'], 'line': r['line']} for r in results]
    for h in highlights:
        located += [h['declaration']] + h['related_declarations']
    return {'credited_associations': len(results), 'credited_associations_located': sum(r['line'] is not None for r in results),
            'highlight_declarations': len(highlights),
            'highlight_declarations_located': sum(h['declaration']['line'] is not None for h in highlights),
            'related_highlight_declarations': sum(len(h['related_declarations']) for h in highlights),
            'related_highlight_declarations_located': sum(r['line'] is not None for h in highlights for r in h['related_declarations']),
            'distinct_source_locations': len({(r['file'], r['line']) for r in located})}


def counts_for(results, works, highlights, files):
    return {'works': len(works), 'targets': sum(len(w['targets']) for w in works),
            'targets_credited': len({(r['work_id'], r['target_id']) for r in results}),
            'targets_without_credit': sum(not t['results'] for w in works for t in w['targets']),
            'results': len(results), 'distinct_credited_declarations': len({r['lean_name'] for r in results}),
            'proved': sum(r['status'] == 'proved' for r in results),
            'counterexample_proved': sum(r['status'] == 'counterexample_proved' for r in results),
            'conditional': sum(bool(r['conditional_on']) for r in results), 'highlights': len(highlights),
            'modules': sum(p.startswith('AronowAudit/') and p.endswith('.lean') for p in files),
            'lean_lines': sum(len(data.splitlines()) for p, data in files.items() if p.endswith('.lean'))}


def check_curated(overview, results):
    pairs = {(r['lean_name'], r['target_id']) for r in results if r['work_id'] == overview['work_id']}
    for section in ['key_results', 'corrections']:
        for item in overview[section]:
            if not item['target_ids'] or any((item['lean_name'], t) not in pairs for t in item['target_ids']):
                raise ValueError(f'Uncredited curated declaration: {overview["work_id"]}: {item["lean_name"]}')


def schema_for_path(path):
    if path in ['catalog/index.json','catalog/results.jsonl','catalog/works.json','catalog/highlights.json']:
        return 'catalog/schema/' + path.split('/')[-1].split('.')[0] + '.schema.json'
    if re.fullmatch(r'catalog/works/P\d{3}\.json', path):
        return 'catalog/schema/work.schema.json'
    return None


def rebuild_index(files):
    """Build derived metadata and the inventory, including its own byte size."""
    results = [json.loads(line) for line in files['catalog/results.jsonl'].splitlines()]
    summaries = json.loads(files['catalog/works.json'])
    works = [json.loads(files[s['catalog']]) for s in summaries]
    highlights = json.loads(files['catalog/highlights.json'])
    index = {'repository':REPOSITORY, 'toolchain':files['lean-toolchain'].decode().strip(),
             'counts':counts_for(results,works,highlights,files),
             'vocabularies':{'statuses':STATUSES,'status_descriptions':STATUS_DESCRIPTIONS,'target_kinds':KINDS,'areas':AREAS,'highlight_sections':SECTIONS,
                             'standard_axioms':sorted(STANDARD_AXIOMS),'excluded_association_statuses':['not_applicable']},
             'line_coverage':coverage(results,highlights),'files':[]}
    snapshot = dict(files)
    path = 'catalog/index.json'
    snapshot.setdefault(path,b'')
    for _ in range(20):
        index['files'] = [{'path':p,'bytes':len(data),'records':1 if p==path else record_count(p,data),
                           'schema':schema_for_path(p)} for p,data in sorted(snapshot.items())]
        output = encoded(index)
        if output == snapshot[path]:
            return output
        snapshot[path] = output
    raise ValueError('Index self-size did not converge')


def refresh_index(root):
    """Explicitly refresh only the derived index; validation is still required."""
    files = read_files(root)
    output = rebuild_index(files)
    (root/'catalog/index.json').write_bytes(output)
    return output


def check_catalog(files):
    def load(path):
        return json.loads(files[path])
    index = load('catalog/index.json')
    results = [json.loads(line) for line in files['catalog/results.jsonl'].splitlines()]
    summaries = load('catalog/works.json')
    highlights = load('catalog/highlights.json')
    works = [load(s['catalog']) for s in summaries]
    for name, value in [('index', index), ('results', results), ('works', summaries), ('highlights', highlights)]:
        schema = load(f'catalog/schema/{name}.schema.json')
        preflight_schema(schema)
        if name == 'results':
            for row in value:
                validate_schema(row, schema, _root=schema)
        else:
            validate_schema(value, schema, _root=schema)
    work_schema = load('catalog/schema/work.schema.json')
    preflight_schema(work_schema)
    for work in works:
        validate_schema(work, work_schema, _root=work_schema)
    expected_files = set(files)
    listed = {row['path'] for row in index['files']}
    if len(listed) != len(index['files']) or expected_files != listed:
        raise ValueError(f'Index file inventory differs: {sorted(expected_files ^ listed)}')
    for row in index['files']:
        safe_relative(row['path'])
        path = row['path']
        expected_schema = schema_for_path(path)
        if row['schema'] != expected_schema or (expected_schema and expected_schema not in files):
            raise ValueError(f'Index schema reference mismatch: {path}')
        if row['bytes'] != len(files[row['path']]) or row['records'] != record_count(row['path'], files[row['path']]):
            raise ValueError(f'Index size or record count mismatch: {row["path"]}')
    actual_counts = counts_for(results, works, highlights, files)
    if index['counts'] != actual_counts:
        raise ValueError('Catalog counts disagree')
    if index['line_coverage'] != coverage(results, highlights):
        raise ValueError('Catalog line coverage disagrees')
    expected_vocab = {'statuses': STATUSES, 'status_descriptions': STATUS_DESCRIPTIONS, 'target_kinds': KINDS, 'areas': AREAS, 'highlight_sections': SECTIONS,
                      'standard_axioms': sorted(STANDARD_AXIOMS), 'excluded_association_statuses': ['not_applicable']}
    if index['vocabularies'] != expected_vocab or index['repository'] != REPOSITORY:
        raise ValueError('Catalog vocabularies or repository differ')
    if index['toolchain'] != files['lean-toolchain'].decode().strip():
        raise ValueError('Catalog toolchain differs')
    by_file, by_name = source_index(files)
    extract_premises = cached_premise_extractor(files, by_file, by_name)
    triples = set()
    for row in results:
        triple = (row['work_id'], row['target_id'], row['lean_name'])
        if triple in triples:
            raise ValueError(f'Duplicate credited association: {triple}')
        triples.add(triple)
        check_location(row, by_file)
        check_axioms(row['lean_name'], row['axioms'])
        expected_premises = extract_premises(row['lean_name'])
        if [c['hypothesis'] for c in row['conditional_on']] != expected_premises:
            raise ValueError(f'Conditional premise identifiers disagree with source: {row["lean_name"]}')
    seen_works = set()
    nested = []
    for summary, work in zip(summaries, works):
        wid = work['work_id']
        if wid in seen_works or summary['work_id'] != wid or summary['catalog'] != f'catalog/works/{wid}.json' or summary['docs'] != f'docs/works/{wid}.md':
            raise ValueError('Work identifiers or paths disagree')
        seen_works.add(wid)
        wr = [r for r in results if r['work_id'] == wid]
        if work['overview']['work_id'] != wid:
            raise ValueError(f'Curated work identifier disagrees: {wid}')
        if summary['work'] != work['work'] or summary['areas'] != work['overview']['areas'] or summary['counts'] != work['counts']:
            raise ValueError(f'Work summary disagrees: {wid}')
        expected = {'targets': len(work['targets']), 'results': len(wr), 'proved': sum(r['status'] == 'proved' for r in wr),
                    'counterexample_proved': sum(r['status'] == 'counterexample_proved' for r in wr)}
        if expected != work['counts']:
            raise ValueError(f'Work counts disagree: {wid}')
        check_curated(work['overview'], wr)
        tids = set()
        for target in work['targets']:
            if target['id'] in tids or not target['id'].startswith(wid + '-T'):
                raise ValueError(f'Invalid or duplicate target: {target["id"]}')
            tids.add(target['id'])
            if target['credited'] != bool(target['results']):
                raise ValueError(f'Target credited flag disagrees: {target["id"]}')
            if any(x['status'] in STATUSES for x in target['excluded_associations']):
                raise ValueError('Excluded association has credited status')
            for row in target['results']:
                if row['work_id'] != wid or row['target_id'] != target['id'] or row['target_kind'] != target['kind']:
                    raise ValueError('Target result identity mismatch')
                nested.append(row)
    key = lambda row: (row['work_id'], row['target_id'], row['lean_name'])
    if sorted(nested, key=key) != sorted(results, key=key):
        raise ValueError('Per-work results disagree with results catalog')
    if set(r['work_id'] for r in results) != seen_works:
        raise ValueError('Result work set disagrees')
    hids = set()
    for h in highlights:
        if h['id'] in hids:
            raise ValueError('Duplicate highlight identifier')
        hids.add(h['id'])
        if h['section'] != h['sections'][0] or len(set(h['sections'])) != len(h['sections']):
            raise ValueError('Highlight sections disagree')
        for row in [h['declaration']] + h['related_declarations']:
            check_location(row, by_file)
            check_axioms(row['lean_name'], row['axioms'])
        if [c['hypothesis'] for c in h['conditional_on']] != extract_premises(h['declaration']['lean_name']):
            raise ValueError('Highlight premise identifiers disagree with source')
        for condition in h['conditional_on']:
            if len(by_name.get(base_lean_name(condition['hypothesis']), [])) != 1:
                raise ValueError('Highlight published-theorem premise does not resolve')
        principal_rows = [r for r in results if r['lean_name'] == h['declaration']['lean_name']]
        if principal_rows and any([c['hypothesis'] for c in r['conditional_on']] != [c['hypothesis'] for c in h['conditional_on']] for r in principal_rows):
            raise ValueError('Highlight and credited result premise identifiers disagree')
        association = h['association']
        if association['status'] != 'helper':
            matches = [r for r in results if r['lean_name'] == h['declaration']['lean_name']]
            if not matches or association['status'] not in {r['status'] for r in matches}:
                raise ValueError('Highlight credit disagrees')
            if any(w not in {r['work_id'] for r in matches} for w in association['work_ids']) or any(t not in {r['target_id'] for r in matches} for t in association['target_ids']):
                raise ValueError('Highlight association identifiers disagree')
    for row in results:
        expected = sorted(h['id'] for h in highlights if row['lean_name'] in [d['lean_name'] for d in [h['declaration']] + h['related_declarations']])
        if row['highlight_ids'] != expected:
            raise ValueError('Result highlight identifiers disagree')
    return actual_counts


def check_apache_license(data):
    """Accept the canonical Apache 2.0 text with unfilled appendix fields."""
    import hashlib
    normalized = ' '.join(data.decode().split())
    if hashlib.sha256(normalized.encode()).hexdigest() != '0ffddef9e48f8a09aed5caf2d44f7ba1c1be2d9b8e0a6f693b1635b2d5566645':
        raise ValueError('Root LICENSE must be canonical Apache 2.0 with appendix placeholders')


def check_website_catalog(files, website_root):
    """Check every published target's identity and complete text against the catalog."""
    expected, actual = {}, {}

    def add_targets(records, work_id, targets, source):
        if not isinstance(targets, list):
            raise ValueError(f'{source}: targets must be an array')
        for target in targets:
            if not isinstance(target, dict):
                raise ValueError(f'{source}: target must be an object')
            target_id = target.get('id')
            if not isinstance(target_id, str) or not re.fullmatch(re.escape(work_id) + r'-T\d+', target_id):
                raise ValueError(f'{source}: invalid target identifier {target_id!r}')
            if target_id in records:
                raise ValueError(f'{source}: duplicate target {target_id}')
            text = target.get('text')
            if not isinstance(text, dict):
                raise ValueError(f'{source}: target {target_id} has no text object')
            records[target_id] = text

    for path, data in sorted(files.items()):
        if re.fullmatch(r'catalog/works/P\d{3}\.json', path):
            work = json.loads(data)
            add_targets(expected, work['work_id'], work['targets'], path)
    work_dir = website_root / 'data' / 'works'
    if not work_dir.is_dir():
        raise ValueError(f'Website work directory does not exist: {work_dir}')
    for path in sorted(work_dir.glob('*.json')):
        work = json.loads(path.read_text(encoding='utf-8'))
        work_id = work['work']['id']
        if work_id != path.stem or not re.fullmatch(r'P\d{3}', work_id):
            raise ValueError(f'{path}: work identifier does not match filename')
        lean = work.get('lean')
        if not isinstance(lean, dict):
            raise ValueError(f'{path}: missing Lean target data')
        add_targets(actual, work_id, lean.get('targets'), str(path))
    missing = sorted(expected.keys() - actual.keys())
    extra = sorted(actual.keys() - expected.keys())
    changed = sorted(t for t in expected.keys() & actual.keys() if expected[t] != actual[t])
    if missing or extra or changed:
        details = []
        for label, targets in [('missing', missing), ('unexpected', extra), ('text differs', changed)]:
            if targets:
                details.append(f'{label}: {", ".join(targets)}')
        raise ValueError('Website/catalog mismatch; ' + '; '.join(details))
    return len(expected)


def check_repository(root, scan=True, website_root=None):
    files = read_files(root)
    check_apache_license(files['LICENSE'])
    counts = check_catalog(files)
    check_modification_notices(files)
    links = check_links(files)
    check_math(files)
    gaps = [h for p, data in files.items() if p.endswith('.lean') for h in lean_gaps(p, data)]
    hits = content_hits(files) if scan else gaps
    if hits:
        for h in hits:
            print(f'{h["file"]}:{h["line"]}: {h["kind"]}: {h["text"]}', file=sys.stderr)
        raise ValueError(f'Content scan failed: {len(hits)} hits')
    if website_root is not None:
        check_website_catalog(files, website_root)
    return counts, links


def main():
    parser = argparse.ArgumentParser(description='Check the repository catalogs, source locations and documentation.')
    parser.add_argument('root', nargs='?', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--refresh-index',action='store_true',help='Rebuild the derived index from current files, then validate')
    parser.add_argument('--website-root', type=Path,
                        help='Also require all website target IDs and descriptions to match the catalog')
    args = parser.parse_args()
    try:
        if args.refresh_index:
            refresh_index(args.root)
        counts, links = check_repository(args.root, website_root=args.website_root)
    except (ValueError, KeyError, OSError, UnicodeError, json.JSONDecodeError) as exc:
        print(f'ERROR: {exc}', file=sys.stderr)
        return 1
    print(f'Checked {counts["results"]} credited associations, {counts["highlights"]} highlights and {links} repository-relative Markdown links.')
    if args.website_root is not None:
        print(f'Checked {counts["targets"]} website target descriptions against the catalog.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
