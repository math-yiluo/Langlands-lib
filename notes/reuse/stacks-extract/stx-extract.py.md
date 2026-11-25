# `stx-extract.py`

This page holds the script `stx-extract.py` as it is, in the code block below. To use it, save the content of the block under that name.

```python
#!/usr/bin/env python3
"""Make the extract of the Stacks copy.

    python3 tools/stx-extract.py [--source /srv/ll-stx/full] [--work .tmp/stx-work]

Run from the workspace root. Inputs (all in the repository):

* `tools/roots.tsv`             the root declarations;
* `tools/extra-decls.tsv`       declarations kept although the cone does not reach them, with
                                reasons;
* `STX-RENAMES.tsv`             the renames (old full name, new full name, module, clash);
* `tools/forbidden-imports.tsv` Mathlib modules that no module of the extract may have in its
                                import closure, with reasons;
* `tools/extra-imports.tsv`     imports a file needs beyond what its kept terms and text name,
                                found by compiling, with reasons (empty at present);
* the compiled copy in `--source` (its Lean files and `.lake/build/lib/lean`).

Steps:

1. `tools/StxCone.lean` (run with `lean --run` on the compiled copy) computes the cone of the
   roots and extras by commands, and for every module the modules outside the copy that its
   kept constants use, and writes them to the work directory.
2. For every module with a kept command, the source file is cut: every command that is not a
   declaration (except `example`s, and `attribute` and `export` commands that name a left-out
   declaration), and the kept declarations, each character for character as in the source apart
   from the renames.
3. The headers are made in import order (`Extract.make_headers`): the source's imports of kept
   copy modules and of modules outside the copy stay; an import of a left-out copy module is
   replaced by what that module makes visible (the level rules of the module system);
   `import Mathlib` and the forbidden modules are never written; and every module outside the
   copy that the kept text needs (its constants occur in the kept terms or are named in the kept
   text) and that the file's imports do not make visible is imported. The tool stops if a needed
   module is forbidden (naming the declaration) or if any import closure contains one.
4. The files are written to `StacksCore/` and `StacksFrontier/` (files there that this run does
   not produce are removed), the manifest to `STX-MANIFEST.tsv`, the counts to
   `tools/extract-stats.txt`, the changes of imports to `tools/extract-imports.tsv`.

The output depends only on the inputs: running the tool twice gives the same files.
"""

import argparse
import collections
import json
import glob
import os
import re
import subprocess
import sys

COPY_ROOTS = ('StacksCore', 'StacksFrontier')
WS = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))


def is_copy(mod):
    return mod.split('.')[0] in COPY_ROOTS


def mod_relpath(mod):
    return os.path.join(*mod.split('.')) + '.lean'


# --------------------------------------------------------------------------------------------
# Inputs

def read_tsv(path, ncols_min=1):
    rows = []
    if not os.path.exists(path):
        return rows
    with open(path, encoding='utf-8') as f:
        for line in f:
            line = line.rstrip('\n')
            if not line or line.startswith('#'):
                continue
            parts = line.split('\t')
            if len(parts) < ncols_min:
                sys.exit(f'bad line in {path}: {line!r}')
            rows.append(parts)
    return rows


def run_cone(args):
    lp = [os.path.join(args.source, '.lake', 'build', 'lib', 'lean')]
    lp += sorted(glob.glob(os.path.join(WS, '.lake', 'packages', '*', '.lake', 'build', 'lib', 'lean')))
    env = dict(os.environ, LEAN_PATH=':'.join(lp))
    os.makedirs(args.work, exist_ok=True)
    cmd = ['lean', '--run', os.path.join(WS, 'tools', 'StxCone.lean'),
           os.path.join(WS, 'tools', 'roots.tsv'), os.path.join(WS, 'tools', 'extra-decls.tsv'),
           args.work]
    r = subprocess.run(cmd, env=env, capture_output=True, text=True)
    sys.stderr.write(r.stdout)
    if r.returncode != 0:
        sys.stderr.write(r.stderr)
        sys.exit('the cone tool failed')


# --------------------------------------------------------------------------------------------
# Lexing: the spans of comments and string literals of a Lean file

SPECIAL = re.compile(r'--|/-|"|\'|«|\br#*"')
IDCHAR = re.compile(r'[\w\'!?₀-₉ₐ-ₜᵢ-ᵪⱼ]')
CHARLIT = re.compile(r"'(?:\\(?:[\\'\"ntr0]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4})|[^\\'\n])'")


def lex(text):
    """Return a sorted list of (start, end, kind) for comments ('line', 'block', 'doc', 'moddoc')
    and strings ('string'); guillemet identifiers are skipped."""
    spans = []
    i = 0
    n = len(text)
    while True:
        m = SPECIAL.search(text, i)
        if not m:
            break
        s = m.start()
        tok = m.group()
        if tok == '--':
            e = text.find('\n', s)
            e = n if e < 0 else e
            spans.append((s, e, 'line'))
            i = e
        elif tok == '/-':
            kind = 'block'
            if text.startswith('/--', s) and not text.startswith('/--/', s):
                kind = 'doc'
            elif text.startswith('/-!', s):
                kind = 'moddoc'
            depth = 1
            j = s + 2
            while depth > 0:
                a = text.find('/-', j)
                b = text.find('-/', j)
                if b < 0:
                    raise ValueError(f'unterminated comment at {s}')
                if 0 <= a < b:
                    depth += 1
                    j = a + 2
                else:
                    depth -= 1
                    j = b + 2
            spans.append((s, j, kind))
            i = j
        elif tok == '"' or tok.startswith('r'):
            if tok.startswith('r'):
                hashes = tok.count('#')
                close = '"' + '#' * hashes
                e = text.find(close, m.end())
                if e < 0:
                    raise ValueError(f'unterminated raw string at {s}')
                e += len(close)
            else:
                j = s + 1
                while True:
                    c = text[j]
                    if c == '\\':
                        j += 2
                        continue
                    if c == '"':
                        break
                    j += 1
                e = j + 1
            spans.append((s, e, 'string'))
            i = e
        elif tok == "'":
            prev = text[s - 1] if s > 0 else ' '
            cm = CHARLIT.match(text, s)
            if cm and not IDCHAR.match(prev):
                spans.append((s, cm.end(), 'string'))
                i = cm.end()
            else:
                i = s + 1
        elif tok == '«':
            e = text.find('»', s)
            i = e + 1 if e >= 0 else s + 1
        else:
            i = s + 1
    return spans


class Text:
    """A source text with its comment and string spans."""

    def __init__(self, text):
        self.text = text
        self.spans = lex(text)
        self.line_starts = [0]
        for m in re.finditer('\n', text):
            self.line_starts.append(m.end())
        # quick lookup of the span containing a position
        self.span_starts = [s for s, _, _ in self.spans]

    def index(self, line, col):
        return self.line_starts[line - 1] + col

    def span_at(self, pos):
        import bisect
        k = bisect.bisect_right(self.span_starts, pos) - 1
        if k >= 0:
            s, e, kind = self.spans[k]
            if s <= pos < e:
                return self.spans[k]
        return None

    def spans_in(self, a, b):
        import bisect
        k = bisect.bisect_left(self.span_starts, a)
        out = []
        while k < len(self.spans) and self.spans[k][0] < b:
            out.append(self.spans[k])
            k += 1
        return out

    def code_tokens(self, a, b):
        """Positions in [a, b) of the code (not comment, not string) as (start, end) runs."""
        runs = []
        pos = a
        for s, e, kind in self.spans_in(a, b):
            if kind == 'string':
                continue
            if s > pos:
                runs.append((pos, s))
            pos = max(pos, e)
        if pos < b:
            runs.append((pos, b))
        return runs

    def code_text(self, a, b):
        """The text of [a, b) with comments replaced by spaces (strings kept)."""
        out = []
        pos = a
        for s, e, kind in self.spans_in(a, b):
            if kind == 'string':
                continue
            s2 = max(s, a)
            if s2 > pos:
                out.append(self.text[pos:s2])
            e2 = min(e, b)
            out.append(' ' * (e2 - s2))
            pos = max(pos, e2)
        if pos < b:
            out.append(self.text[pos:b])
        return ''.join(out)


# --------------------------------------------------------------------------------------------
# Imports

ALL_LEVEL = (True, True)


def level_join(a, b):
    return (a[0] or b[0], a[1] or b[1])


def level_ge(a, b):
    return (a[0] or not b[0]) and (a[1] or not b[1])


def propagate(level, exported, import_all):
    """The level at which a module imported by a module at `level` with the given flags is
    imported, by the rules of the module system (`Lean.importModulesCore`); None if not."""
    lvl_exp, lvl_all = level
    new_exp = lvl_exp and exported
    new_all = lvl_all and import_all
    visible = exported or lvl_all   # B ≥ private
    if not visible and not new_all:
        return None
    return (new_exp, new_all)


def import_line(mod, level, meta):
    exp, al = level
    words = []
    if exp:
        words.append('public')
    if meta:
        words.append('meta')
    words.append('import')
    if al:
        words.append('all')
    words.append(mod)
    return ' '.join(words)


IMPORT_RE = re.compile(r'^(public\s+)?(meta\s+)?import\s+(all\s+)?([^\s]+)(.*)$')


class Graph:
    def __init__(self, path):
        self.imports = collections.defaultdict(list)   # mod -> [(imp, exported, all, meta)]
        self.mods = set()
        with open(path, encoding='utf-8') as f:
            for line in f:
                m, copy, imp, exp, al, meta = line.rstrip('\n').split('\t')
                self.mods.add(m)
                if imp:
                    self.imports[m].append((imp, exp == 'true', al == 'true', meta == 'true'))
        self._pub = {}
        self.order = sorted(self.mods)
        self.idx = {m: i for i, m in enumerate(self.order)}

    def pub_closure(self, m):
        """Bitset of modules reached from `m` by public imports only (including `m`)."""
        if m in self._pub:
            return self._pub[m]
        stack = [(m, False)]
        while stack:
            x, done = stack.pop()
            if x in self._pub:
                continue
            if done:
                bits = 1 << self.idx[x]
                for imp, exp, _, _ in self.imports.get(x, ()):
                    if exp:
                        bits |= self._pub[imp]
                self._pub[x] = bits
            else:
                stack.append((x, True))
                for imp, exp, _, _ in self.imports.get(x, ()):
                    if exp and imp not in self._pub:
                        stack.append((imp, False))
        return self._pub[m]


def expand_import(graph, kept_mods, mod, level, meta):
    """The modules (kept copy modules or modules outside the copy) that an import of the left-out
    copy module `mod` at `level` makes visible, with their levels."""
    out = {}
    stack = [(mod, level)]
    seen = set()
    while stack:
        m, lvl = stack.pop()
        if (m, lvl) in seen:
            continue
        seen.add((m, lvl))
        for imp, exp, al, imeta in graph.imports.get(m, ()):
            if imp == 'Init':
                continue
            nl = propagate(lvl, exp, al)
            if nl is None:
                continue
            if is_copy(imp) and imp not in kept_mods:
                stack.append((imp, nl))
            else:
                prev = out.get(imp)
                out[imp] = (level_join(prev[0], nl) if prev else nl, meta)
    return out


def reduce_imports(graph, direct, added):
    """Drop from `added` (dict mod -> (level, meta)) the modules that the other imports already
    make visible at the same level through public imports."""
    providers = []   # (bits, exported)
    for m, (lvl, meta) in list(direct.items()) + list(added.items()):
        if m in graph.idx:
            providers.append((m, graph.pub_closure(m), lvl[0]))
    result = {}
    for m, (lvl, meta) in added.items():
        if m in direct and level_ge(direct[m][0], lvl):
            continue
        if lvl[1] or meta or m not in graph.idx:
            result[m] = (lvl, meta)
            continue
        bit = 1 << graph.idx[m]
        covered = False
        for pm, bits, pexp in providers:
            if pm == m:
                continue
            if bits & bit and (pexp or not lvl[0]):
                covered = True
                break
        if not covered:
            result[m] = (lvl, meta)
    return result


# --------------------------------------------------------------------------------------------
# Commands of a file

SCOPE_WORDS = {'namespace', 'section', 'end', 'noncomputable', 'public', 'universe', 'variable',
               'set_option', 'include', 'omit', 'open', 'suppress_compilation'}
SYNTAX_WORDS = {'notation', 'notation3', 'infix', 'infixl', 'infixr', 'prefix', 'postfix',
                'macro', 'macro_rules', 'syntax', 'elab', 'elab_rules', 'declare_syntax_cat'}
CONTINUATION = {'|', 'where', 'termination_by', 'decreasing_by', 'deriving', ')', ']', '}', '·'}
WORD_RE = re.compile(r'[^\s\[\]()]+')
IDENT_RE = re.compile(r'(?:«[^»]*»|[^\s\[\](){},:@\'"⟨⟩]+)')


def first_words(code):
    return WORD_RE.findall(code)[:6]


def head_after_modifiers(code):
    """The first keyword of a command after attributes, doc comments and modifiers."""
    s = code.lstrip()
    while True:
        if s.startswith('@['):
            depth = 0
            for k, c in enumerate(s):
                if c == '[':
                    depth += 1
                elif c == ']':
                    depth -= 1
                    if depth == 0:
                        s = s[k + 1:].lstrip()
                        break
            else:
                return ''
            continue
        w = WORD_RE.match(s)
        if not w:
            return ''
        word = w.group()
        if word in ('private', 'protected', 'public', 'noncomputable', 'partial', 'unsafe',
                    'nonrec', 'local', 'scoped', 'meta'):
            s = s[w.end():].lstrip()
            continue
        return word


class Item:
    __slots__ = ('kind', 'start', 'end', 'kept', 'consts', 'info', 'prefix_of_next', 'line',
                 'rewrite')

    def __init__(self, kind, start, end, kept=True, consts=(), info=''):
        self.kind = kind          # 'trivia', 'cmd', 'decl'
        self.start = start
        self.end = end
        self.kept = kept
        self.consts = consts
        self.info = info
        self.prefix_of_next = False
        self.line = 0
        self.rewrite = None


def split_body(t, a, b, ranges, warnings, module):
    """Split the body [a, b) of a file into trivia, commands and declarations.

    `ranges` are the commands of the cone tool: (start, end, kept, names). A range that starts
    a line (or follows a prefix `… in` on its line) is a declaration; a range inside another
    command (the lemma that `attribute [mk_iff] C` generates, say) is attached to that command.
    Other commands start with code at column 0 outside declarations, comments and strings; a doc
    comment directly before such a start belongs to the command."""
    text = t.text
    top, nested = [], []
    for r in ranges:
        s, e, kept, names = r
        ls = text.rfind('\n', 0, s) + 1
        before = t.code_text(ls, s)
        if before.strip() == '' or re.search(r'(^|\s)in\s*$', before):
            top.append(r)
        else:
            nested.append(r)
    top.sort()
    top_starts = {r[0]: r for r in top}
    import bisect
    top_s = [r[0] for r in top]

    def inside_top(p):
        k = bisect.bisect_right(top_s, p) - 1
        return k >= 0 and top[k][0] < p < top[k][1]

    starts = set(top_starts)
    for m in re.finditer(r'(?m)^[^\s]', text[a:b]):
        p = a + m.start()
        if p in starts:
            continue
        if t.span_at(p) is not None:
            continue
        if inside_top(p):
            continue
        starts.add(p)
    # doc comments directly before a (non-range) command start belong to it
    adj = set()
    for p in starts:
        q = p
        if p not in top_starts:
            while True:
                j = q
                while j > a and text[j - 1] in ' \t\n':
                    j -= 1
                sp = t.span_at(j - 1) if j > a else None
                if sp and sp[2] == 'doc' and sp[1] == j and sp[0] >= a:
                    q = sp[0]
                    continue
                break
        adj.add(q)
    starts = sorted(adj)
    items = []
    pos = a
    for k, p in enumerate(starts):
        if p < pos:
            warnings.append(f'{module}: overlapping command at {p}')
            continue
        if p > pos:
            items.append(Item('trivia', pos, p))
        nxt = starts[k + 1] if k + 1 < len(starts) else b
        if p in top_starts:
            s, e, kept, names = top_starts[p]
            items.append(Item('decl', s, e, kept, names))
            # code after the range before the next command?
            for ra, rb in t.code_tokens(e, nxt):
                if text[ra:rb].strip():
                    line = text.count('\n', 0, ra) + 1
                    warnings.append(f'{module}:{line}: code after a declaration range: '
                                    f'{text[ra:rb].strip()[:40]!r}')
                    break
            pos = e
            continue
        end = p
        for ra, rb in t.code_tokens(p, nxt):
            seg = text[ra:rb].rstrip()
            if seg:
                end = ra + len(seg)
        for s2, e2, kind in t.spans_in(p, nxt):
            if kind in ('string', 'doc') and e2 > end:
                end = e2
        it = Item('cmd', p, end)
        it.consts = []
        items.append(it)
        pos = end
    if pos < b:
        items.append(Item('trivia', pos, b))
    # nested ranges
    cmd_items = [it for it in items if it.kind == 'cmd']
    cs = [it.start for it in cmd_items]
    for s, e, kept, names in nested:
        k = bisect.bisect_right(cs, s) - 1
        if k >= 0 and cmd_items[k].start <= s and e <= cmd_items[k].end:
            it = cmd_items[k]
            it.consts = list(it.consts) + names
            it.info = (it.info + ' ' if it.info else '') + ('generates-kept' if kept else 'generates')
        else:
            line = text.count('\n', 0, s) + 1
            warnings.append(f'{module}:{line}: nested range not inside a command: {names[:2]}')
    return items


def resolve_candidates(name, ns, opens):
    if name.startswith('_root_.'):
        return [name[len('_root_.'):]]
    out = []
    for k in range(len(ns), -1, -1):
        out.append('.'.join(ns[:k] + [name]))
    for o in opens:
        out.append(o + '.' + name)
    return out


class Extract:
    def __init__(self, args):
        self.args = args
        self.work = args.work
        self.graph = Graph(os.path.join(self.work, 'imports.tsv'))
        self.commands = collections.defaultdict(list)
        self.kept_names = set()
        self.dropped_names = set()
        with open(os.path.join(self.work, 'commands.tsv'), encoding='utf-8') as f:
            for line in f:
                m, sl, sc, el, ec, kept, consts = line.rstrip('\n').split('\t')
                names = [c.lstrip('*') for c in consts.split(' ') if c]
                kept = kept == '1'
                self.commands[m].append(((int(sl), int(sc)), (int(el), int(ec)), kept, names))
                (self.kept_names if kept else self.dropped_names).update(names)
        self.kept_mods = sorted(m for m, cmds in self.commands.items() if any(c[2] for c in cmds))
        self.kept_set = set(self.kept_mods)
        # Renames: each row renames a declaration and everything in its namespace (its name as a
        # prefix), so that dot notation on a renamed type keeps working.
        self.renames = []
        for row in read_tsv(os.path.join(WS, 'STX-RENAMES.tsv'), 2):
            if row[0] == 'old full name':
                continue
            o, n = split_name(row[0]), split_name(row[1])
            if len(o) != len(n):
                sys.exit(f'rename {row[0]} -> {row[1]}: the number of name components must stay')
            self.renames.append((o, n))
        self.renames.sort(key=lambda r: -len(r[0]))
        self.selections = collections.defaultdict(list)
        sel_path = os.path.join(self.work, 'selections.tsv')
        if os.path.exists(sel_path):
            with open(sel_path, encoding='utf-8') as f:
                for line in f:
                    name, mod, sl, sc, el, ec = line.rstrip('\n').split('\t')
                    self.selections[mod].append((name, (int(sl), int(sc)), (int(el), int(ec))))
        # modules outside the copy used by the terms of the kept constants of each module
        self.term_needs = collections.defaultdict(dict)
        tm_path = os.path.join(self.work, 'termmods.tsv')
        if os.path.exists(tm_path):
            with open(tm_path, encoding='utf-8') as f:
                for line in f:
                    sm, om, used, by, _ = line.rstrip('\n').split('\t')
                    self.term_needs[sm][om] = (used, by)
        # Mathlib modules that no module of the extract may have in its import closure
        self.forbidden = [r[0] for r in read_tsv(os.path.join(WS, 'tools', 'forbidden-imports.tsv'), 1)]
        # imports found by compiling to be needed beyond what terms and text name
        self.extra_imports = collections.defaultdict(dict)
        for row in read_tsv(os.path.join(WS, 'tools', 'extra-imports.tsv'), 2):
            self.extra_imports[row[0]][row[1]] = row[2] if len(row) > 2 else ''
        self.import_log = []
        self.applied = collections.Counter()     # (old, new) -> number of edits
        self.renamed_decls = {}                   # old full name -> new full name
        self.namespaces = {}
        with open(os.path.join(self.work, 'namespaces.tsv'), encoding='utf-8') as f:
            for line in f:
                n, flag = line.rstrip('\n').split('\t')
                self.namespaces[n] = flag
        self.kept_prefixes = set()
        for name in self.kept_names:
            user = re.sub(r'^_private\.(?:[^.]+\.)*?0\.', '', name)
            comps = user.split('.')
            if any(c.startswith('_') for c in comps):
                continue
            for k in range(1, len(comps)):
                self.kept_prefixes.add('.'.join(comps[:k]))
        self.texts = {}
        self.ns_commands = set()
        for mod in self.kept_mods:
            t = self.text_of(mod)
            code = t.code_text(0, len(t.text))
            for m in re.finditer(r'(?m)^namespace[ \t]+(\S+)', code):
                comps = m.group(1).split('.')
                for k in range(1, len(comps) + 1):
                    self.ns_commands.add('.'.join(comps[:k]))
        self.warnings = []
        self.manifest = []
        self.cmd_log = []
        self.rename_misses = []
        self.stats = collections.Counter()

    def ns_exists(self, n):
        """Whether `n` is a namespace in the extract's environment."""
        flag = self.namespaces.get(n)
        if flag is None:
            return n in self.ns_commands
        if flag == '0':
            return True
        return n in self.kept_prefixes or n in self.ns_commands

    def check_open(self, code, ends_in, ns, opens, module):
        """The namespaces an `open` command opens, and those of them that exist in the whole
        copy but not in the extract."""
        body = code.strip()[len('open'):]
        if ends_in:
            body = body.rstrip()[:-2]
        single = re.search(r'[()]|\bhiding\b|\brenaming\b', body) is not None
        toks = [x for x in IDENT_RE.findall(body) if x not in ('scoped', 'hiding', 'renaming', '→', '->')]
        if single:
            toks = toks[:1]
        names, invalid = [], []
        local_opens = list(opens)
        for x in toks:
            cands = []
            if x.startswith('_root_.'):
                cands = [x[len('_root_.'):]]
            else:
                for k in range(len(ns), -1, -1):
                    cands.append('.'.join(ns[:k] + [x]))
                for o in local_opens:
                    cands.append(o + '.' + x)
            in_full = [c for c in cands if c in self.namespaces or c in self.ns_commands]
            in_extract = [c for c in in_full if self.ns_exists(c)]
            names.append(x)
            if in_full and not in_extract:
                invalid.append(x)
            else:
                local_opens.append(in_extract[0] if in_extract else x)
        return names, invalid

    def rewrite_open(self, t, it, invalid):
        """The `open` command without the namespaces in `invalid`; None if nothing is left."""
        text = t.text[it.start:it.end]
        code = t.code_text(it.start, it.end)
        single = re.search(r'[()]|\bhiding\b|\brenaming\b', code) is not None
        if single:
            return None
        spans = []
        for m in IDENT_RE.finditer(code):
            if m.group() in invalid and m.start() > 0:
                spans.append((m.start(), m.end()))
        remaining = [m.group() for m in IDENT_RE.finditer(code)
                     if m.group() not in invalid and m.group() not in ('open', 'scoped', 'in')]
        if not remaining:
            return None
        out = text
        for a, b in reversed(spans):
            a2 = a
            while a2 > 0 and out[a2 - 1] in ' \t':
                a2 -= 1
            out = out[:a2] + out[b:]
        return out

    def names_dropped(self, ids, ns, opens, module):
        """The identifiers that resolve to left-out declarations of the copy (and, in
        `self.last_kept_hits`, those that resolve to kept ones)."""
        hits = []
        self.last_kept_hits = []
        for ident in ids:
            cands = resolve_candidates(ident, ns, opens)
            priv = ['_private.' + module + '.0.' + c for c in cands]
            found = None
            for c in priv + cands:
                if c in self.kept_names:
                    found = 'kept'
                    break
                if c in self.dropped_names and found is None:
                    found = 'dropped'
            if found == 'dropped':
                hits.append(ident)
            elif found == 'kept':
                self.last_kept_hits.append(ident)
        return hits

    def rename_of(self, name):
        """The new name of a constant of the extract under the renames, or None."""
        m = re.match(r'^(_private\.(?:[^.]+\.)*?0\.)(.*)$', name)
        pre, user = (m.group(1), m.group(2)) if m else ('', name)
        comps = split_name(user)
        for o, n in self.renames:
            if comps[:len(o)] == o:
                return pre + join_name(n + comps[len(o):])
        return None

    def rewrite_ident(self, written, old, new):
        """The identifier `written` (as the source writes a reference to `old`: in full, relative to
        a namespace, or as the field of a dot notation) with `old` replaced by `new`; None if the
        text is not such a reference."""
        pre = ''
        w = written
        if w.startswith('@'):
            pre, w = '@', w[1:]
        if w.startswith('_root_.'):
            pre, w = pre + '_root_.', w[len('_root_.'):]
        wc = split_name(w)
        oc = split_name(re.sub(r'^_private\.(?:[^.]+\.)*?0\.', '', old))
        nc = split_name(re.sub(r'^_private\.(?:[^.]+\.)*?0\.', '', new))
        if not wc or len(wc) > len(oc) or oc[-len(wc):] != wc:
            return None
        return pre + join_name(nc[-len(wc):])

    def rename_edits(self, module, t):
        """The edits (start, end, replacement) that the renames make in the source text of
        `module`: every reference to a renamed constant that Lean recorded in the module's
        `.ilean`, and the declared name of every renamed declaration of the module."""
        edits = {}
        text = t.text
        lines = text.split('\n')

        def cp(line0, u16):
            """Index in `text` of UTF-16 column `u16` of 0-based line `line0`."""
            ln = lines[line0]
            k = 0
            units = 0
            while k < len(ln) and units < u16:
                units += 2 if ord(ln[k]) > 0xFFFF else 1
                k += 1
            return t.line_starts[line0] + k

        def add(s, e, old, new, what):
            written = text[s:e]
            rep = self.rewrite_ident(written, old, new)
            if rep is None:
                if not re.fullmatch(r'\d+', written):
                    self.pending_misses.append((s, (module, text.count('\n', 0, s) + 1, old, written, what)))
                return
            if rep != written:
                prev = edits.get(s)
                if prev and prev != (e, rep):
                    self.warnings.append(f'{module}: two renames at {s}: {prev} {rep}')
                edits[s] = (e, rep)
                self.applied[(old, new)] += 1

        il = os.path.join(self.args.source, '.lake', 'build', 'lib', 'lean',
                          *module.split('.')) + '.ilean'
        with open(il, encoding='utf-8') as f:
            data = json.load(f)
        self.refs = []
        for key, info in data.get('references', {}).items():
            ref = json.loads(key)
            if 'c' not in ref:
                continue
            name = ref['c']['n']
            for u in info.get('usages', []):
                self.refs.append((cp(u[0], u[1]), name, ref['c']['m']))
            new = self.rename_of(name)
            if new is None:
                continue
            locs = [(u, 'usage') for u in info.get('usages', [])]
            if info.get('definition'):
                locs.append((info['definition'], 'definition'))
            for u, what in locs:
                l1, c1, l2, c2 = u[:4]
                add(cp(l1, c1), cp(l2, c2), name, new, what)
        for name, (sl, sc), (el, ec) in self.selections.get(module, []):
            new = self.rename_of(name)
            if new is None:
                continue
            self.renamed_decls[name] = new
            s0, e0 = t.index(sl, sc), t.index(el, ec)
            if s0 not in edits:
                add(s0, e0, name, new, 'declared name')
        return edits

    def ns_rename(self, ns, comps):
        """New components for a `namespace`/`end` argument `comps` opened inside `ns`, or None."""
        full = ns + comps
        for o, n in self.renames:
            if len(o) > len(ns) and full[:len(o)] == o:
                new = n[len(ns):] + comps[len(o) - len(ns):]
                return new if new != comps else None
        return None

    def text_of(self, module):
        if module not in self.texts:
            src = os.path.join(self.args.source, mod_relpath(module))
            with open(src, encoding='utf-8') as f:
                self.texts[module] = Text(f.read())
        return self.texts[module]

    def cut(self, module):
        src = os.path.join(self.args.source, mod_relpath(module))
        t = self.text_of(module)
        raw = t.text
        text = t.text
        # Header: `module` and the import lines at the top.
        header_end = 0
        header_lines = []
        pos = 0
        for line in text.splitlines(keepends=True):
            stripped = line.strip()
            if stripped == 'module' or IMPORT_RE.match(stripped) or stripped == '':
                header_lines.append(line)
                pos += len(line)
                if stripped:
                    header_end = pos
                continue
            break
        imports_here = [ln for ln in header_lines if IMPORT_RE.match(ln.strip())]
        graph_imps = [i for i in self.graph.imports.get(module, []) if i[0] != 'Init']
        if len(imports_here) != len(graph_imps):
            self.warnings.append(f'{module}: header has {len(imports_here)} import lines, Lean has {len(graph_imps)}')
        # Ranges of commands
        cmds = []
        for (sl, sc), (el, ec), kept, names in self.commands.get(module, []):
            s = t.index(sl, sc)
            e = t.index(el, ec)
            cmds.append((s, e, kept, names))
        cmds.sort()
        # Items of the body
        items = split_body(t, header_end, len(text), cmds, self.warnings, module)
        self.pending_misses = []
        self.edits = self.rename_edits(module, t)
        # Classify
        ns_stack = []     # list of (kind, components, opens)
        opens_top = []
        out_pieces = []

        def cur_ns():
            comps = []
            for kind, c, _ in ns_stack:
                comps += c
            return comps

        def cur_opens():
            res = list(opens_top)
            for _, _, o in ns_stack:
                res += o
            return res

        pending_open_in = []
        for idx, it in enumerate(items):
            it.line = text.count('\n', 0, it.start) + 1
            if it.kind == 'trivia':
                continue
            code = t.code_text(it.start, it.end)
            words = first_words(code)
            head = head_after_modifiers(code)
            if it.kind == 'decl':
                if head in SYNTAX_WORDS:
                    it.kept = True
                    it.info = 'syntax'
                elif head == 'mutual':
                    self.warnings.append(f'{module}:{it.line}: mutual block inside a range')
                continue
            # non-declaration command
            w0 = words[0] if words else ''
            if w0.startswith('@'):
                w0 = head
            ends_in = re.search(r'(^|\s)in$', code.rstrip()) is not None
            if ends_in:
                it.prefix_of_next = True
            if w0 == 'example' or head == 'example':
                it.kept = False
                it.info = 'example'
            elif w0.startswith('#'):
                it.kept = False
                it.info = 'info command'
            elif w0 in ('namespace',):
                comps = split_name(words[1]) if len(words) > 1 else []
                newc = self.ns_rename(cur_ns(), comps)
                if newc is not None:
                    self.ns_edit(t, it, words[1], join_name(newc))
                ns_stack.append(('ns', comps, []))
            elif head == 'section':
                ns_stack.append(('sec', [], []))
            elif w0 == 'end':
                if ns_stack:
                    kind, comps, _ = ns_stack.pop()
                    if kind == 'ns' and len(words) > 1:
                        newc = self.ns_rename(cur_ns(), comps)
                        if newc is not None:
                            self.ns_edit(t, it, words[1], join_name(newc))
                else:
                    self.warnings.append(f'{module}:{it.line}: unmatched end')
            elif w0 == 'open':
                names, invalid = self.check_open(code, ends_in, cur_ns(), cur_opens(), module)
                if invalid:
                    it.info = 'open of namespaces not in the extract: ' + ' '.join(invalid)
                    new_text = self.rewrite_open(t, it, invalid)
                    if new_text is None:
                        it.kept = False
                    else:
                        it.rewrite = new_text
                    names = [x for x in names if x not in invalid]
                if ends_in:
                    pending_open_in = names
                else:
                    if ns_stack:
                        ns_stack[-1][2].extend(names)
                    else:
                        opens_top.extend(names)
            elif w0 == 'attribute' or w0 == 'export':
                body = code.strip()
                if w0 == 'attribute':
                    k = body.find('[')
                    depth = 0
                    j = k
                    for j in range(k, len(body)):
                        if body[j] == '[':
                            depth += 1
                        elif body[j] == ']':
                            depth -= 1
                            if depth == 0:
                                break
                    rest = body[j + 1:]
                    if ends_in:
                        rest = rest.rstrip()[:-2]
                    ids = IDENT_RE.findall(rest)
                else:
                    m = re.match(r'export\s+(\S+)\s*\(([^)]*)\)', body)
                    ids = [m.group(1) + '.' + x for x in m.group(2).split()] if m else []
                hits = self.names_dropped(ids, cur_ns(), cur_opens() + pending_open_in, module)
                if hits:
                    it.kept = False
                    it.info = 'names left-out ' + ' '.join(hits)
                    if self.last_kept_hits:
                        it.info += '; also names kept ' + ' '.join(self.last_kept_hits)
                        self.warnings.append(f'{module}:{it.line}: left-out attribute also names kept '
                                             + ' '.join(self.last_kept_hits))
            elif w0 in SCOPE_WORDS or w0 in SYNTAX_WORDS or head in SYNTAX_WORDS:
                pass
            elif w0 == 'mutual':
                self.warnings.append(f'{module}:{it.line}: mutual block')
            elif w0 in CONTINUATION:
                self.warnings.append(f'{module}:{it.line}: continuation outside a range: {w0}')
            else:
                self.warnings.append(f'{module}:{it.line}: unknown command kept: {" ".join(words[:3])}')
            if not ends_in:
                pending_open_in = []
            if 'generates-kept' in it.info and not it.kept:
                self.warnings.append(f'{module}:{it.line}: left-out command generates kept constants {it.consts[:3]}')
        # prefixes (`open … in`, `set_option … in`, ...) follow the item they prefix
        for idx in range(len(items) - 1, -1, -1):
            it = items[idx]
            if it.kind == 'cmd' and it.prefix_of_next:
                j = idx + 1
                while j < len(items) and items[j].kind == 'trivia':
                    j += 1
                if j < len(items):
                    it.kept = it.kept and items[j].kept
        # comments directly attached to a left-out item are left out with it
        for idx, it in enumerate(items):
            if it.kind == 'trivia':
                continue
        # references to renamed constants in kept text that could not be rewritten
        for pos0, row in self.pending_misses:
            if any(it.kept and it.kind != 'trivia' and it.start <= pos0 < it.end for it in items):
                self.rename_misses.append(row)
        # Assemble
        pieces = []   # (text, protected)
        for idx, it in enumerate(items):
            seg = text[it.start:it.end]
            if it.kind == 'trivia':
                nxt = items[idx + 1] if idx + 1 < len(items) else None
                if nxt is not None and not nxt.kept:
                    seg = strip_attached_comments(t, it.start, it.end)
                prev = items[idx - 1] if idx > 0 else None
                pieces.append((seg, False))
                continue
            if it.kept:
                if it.rewrite is not None:
                    pieces.append((it.rewrite, True))
                else:
                    pieces.append((self.rename_text(t, it.start, it.end, module), True))
        body = assemble(pieces)
        # the header is made later, in import order (make_headers)
        out = None
        # manifest
        src_rel = os.path.relpath(src, self.args.source)
        def manifest_row(status, name):
            new = self.rename_of(name) if status == 'kept' else None
            shown = new or name
            m = re.match(r'^_private\.(?:[^.]+\.)*?0\.(.*)$', shown)
            private = 'private' if m else ''
            if m:
                shown = m.group(1)
            src_name = re.sub(r'^_private\.(?:[^.]+\.)*?0\.', '', name) if new else ''
            self.manifest.append((mod_relpath(module), src_rel, status, shown, private, src_name))

        for it in items:
            if it.kind == 'decl':
                for name in main_names(it.consts):
                    manifest_row('kept' if it.kept else 'dropped', name)
                self.stats['decl commands kept' if it.kept else 'decl commands dropped'] += 1
            elif it.kind == 'cmd':
                if not it.kept or it.rewrite is not None:
                    first = text[it.start:it.end].split('\n')[0][:100]
                    self.cmd_log.append((mod_relpath(module), str(it.line),
                                         'dropped' if not it.kept else 'rewritten',
                                         it.info or 'prefix of a left-out declaration', first))
                for name in main_names(it.consts):
                    manifest_row('kept' if it.kept else 'dropped', name)
                if not it.kept:
                    self.stats['other commands dropped'] += 1
        self.stats['source lines'] += raw.count('\n')
        # constants outside the copy named in the kept text (from the `.ilean`)
        text_needs = {}
        kept_items = [it for it in items if it.kept and it.kind != 'trivia']
        starts = [it.start for it in kept_items]
        import bisect
        for pos0, name, refmod in self.refs:
            k = bisect.bisect_right(starts, pos0) - 1
            if k >= 0 and kept_items[k].start <= pos0 < kept_items[k].end:
                if not is_copy(refmod) and refmod not in text_needs:
                    text_needs[refmod] = name
        return {'body': body, 'header_lines': header_lines, 'text_needs': text_needs}

    def make_headers(self, parts):
        """The headers of the files of the extract, in import order.

        A file keeps its source imports of modules outside the copy and of kept copy modules; an
        import of a left-out copy module is replaced by the modules it makes visible (module
        system levels). `import Mathlib` and the modules of `tools/forbidden-imports.tsv` are
        never written, neither directly nor in a replacement. Then every module outside the copy
        that the kept text needs (its constants occur in the terms of the kept constants, or are
        named in the kept text, or `tools/extra-imports.tsv` lists it) and that the file's imports
        do not make visible is imported (`public import`), at the place of a cut `import Mathlib`
        or after the last import. Fails if a needed module is a forbidden one, or if the import
        closure of a file contains one."""
        forbidden = set(self.forbidden)
        cut_names = forbidden | {'Mathlib'}
        g = Graph.__new__(Graph)
        g.imports = collections.defaultdict(list)
        g.mods = set()
        for m, lst in self.graph.imports.items():
            if not is_copy(m):
                g.imports[m] = list(lst)
        for m in self.graph.mods:
            if not is_copy(m):
                g.mods.add(m)
        g.mods |= set(self.kept_mods)
        g._pub = {}
        g.order = sorted(g.mods)
        g.idx = {m: i for i, m in enumerate(g.order)}
        full_memo = {}

        def full_closure(m):
            if m in full_memo:
                return full_memo[m]
            stack = [(m, False)]
            while stack:
                x, done = stack.pop()
                if x in full_memo:
                    continue
                if done:
                    bits = 1 << g.idx[x]
                    for imp, _, _, _ in g.imports.get(x, ()):
                        bits |= full_memo[imp]
                    full_memo[x] = bits
                else:
                    stack.append((x, True))
                    for imp, _, _, _ in g.imports.get(x, ()):
                        if imp not in full_memo:
                            stack.append((imp, False))
            return full_memo[m]

        # 1. the kept lines and the replacements of every file
        plan = {}
        for mod in self.kept_mods:
            lines = []   # (kind, payload): ('text', s) | ('line', (s, mod, lvl, meta)) | ('cut', s)
                         # | ('expand', dropped module)
            direct = {}
            added = {}
            cut_here = []
            for ln in parts[mod]['header_lines']:
                m = IMPORT_RE.match(ln.strip())
                if not m:
                    lines.append(('text', ln))
                    continue
                pub, meta, al, imp, _ = m.groups()
                lvl = (bool(pub), bool(al))
                if imp in cut_names:
                    lines.append(('cut', ln))
                    cut_here.append((imp, lvl))
                    continue
                if not is_copy(imp) or imp in self.kept_set:
                    lines.append(('line', (ln, imp, lvl, bool(meta))))
                    direct[imp] = (level_join(direct[imp][0], lvl) if imp in direct else lvl, bool(meta))
                    continue
                exp = expand_import(self.graph, self.kept_set, imp, lvl, bool(meta))
                for k, v in exp.items():
                    if k in cut_names:
                        cut_here.append((k, v[0]))
                        continue
                    lvlk = v[0]
                    if k in added:
                        added[k] = (level_join(added[k][0], lvlk), added[k][1] or bool(meta))
                    else:
                        added[k] = (lvlk, bool(meta))
                lines.append(('expand', imp))
            plan[mod] = (lines, direct, added, cut_here)
        # 2. import order among the kept modules
        deps = {}
        for mod, (lines, direct, added, _) in plan.items():
            deps[mod] = {k for k in list(direct) + list(added) if k in self.kept_set}
        order, done, temp = [], set(), set()

        def visit(m):
            if m in done:
                return
            if m in temp:
                sys.exit(f'import cycle at {m}')
            temp.add(m)
            for d in sorted(deps[m]):
                visit(d)
            temp.discard(m)
            done.add(m)
            order.append(m)

        for m in sorted(plan):
            visit(m)
        # 3. headers, bottom up
        init_bits = g.pub_closure('Init') if 'Init' in g.idx else 0
        for mod in order:
            lines, direct, added, cut_here = plan[mod]
            # the replacements, reduced against the direct imports (as before)
            g_src = self.graph
            reduced = reduce_imports(g, direct, added)
            entries = [(k, lvl, meta) for k, (lvl, meta) in direct.items()]
            entries += [(k, lvl, meta) for k, (lvl, meta) in reduced.items()]
            visible = init_bits
            for k, lvl, meta in entries:
                if k not in g.idx:
                    continue
                visible |= g.pub_closure(k)
                if lvl[1]:
                    # `import all k`: its private imports are visible as well
                    for imp, exp, al, _ in g.imports.get(k, ()):
                        if imp in g.idx:
                            visible |= g.pub_closure(imp)
            # what the kept text needs
            needs = {}
            for om, (used, by) in self.term_needs.get(mod, {}).items():
                needs.setdefault(om, f'term: {used} (in {by})')
            for om, name in parts[mod]['text_needs'].items():
                needs.setdefault(om, f'text: {name}')
            for om, why in self.extra_imports.get(mod, {}).items():
                needs.setdefault(om, f'tools/extra-imports.tsv: {why}')
            bad = {om: why for om, why in needs.items() if om in forbidden}
            if bad:
                for om, why in sorted(bad.items()):
                    print(f'ERROR: {mod} needs the forbidden module {om}: {why}', file=sys.stderr)
                sys.exit('a kept declaration needs a forbidden module; stopping')
            missing = []
            for om in sorted(needs):
                if om.split('.')[0] in ('Init', 'Lean') or om == 'Mathlib':
                    continue
                if om not in g.idx:
                    self.warnings.append(f'{mod}: needed module {om} is not in the import graph')
                    continue
                if not visible >> g.idx[om] & 1:
                    missing.append(om)
            additions = []
            for om in missing:
                bit = 1 << g.idx[om]
                if not any(o != om and g.pub_closure(o) & bit for o in missing):
                    additions.append(om)
            for imp, lvl in cut_here:
                self.import_log.append((mod_relpath(mod), 'not written', imp,
                                        'import Mathlib' if imp == 'Mathlib' else 'forbidden module'))
            for om in additions:
                self.import_log.append((mod_relpath(mod), 'added', om, needs[om]))
            # the header text
            out_lines = []
            emitted_exp = False
            placed = False
            add_lines = [f'public import {om}\n' for om in additions]
            last_import = max([k for k, (kind, _) in enumerate(lines) if kind != 'text'], default=-1)
            for k, (kind, payload) in enumerate(lines):
                if kind == 'text':
                    out_lines.append(payload)
                elif kind == 'line':
                    out_lines.append(payload[0])
                elif kind == 'expand':
                    if not emitted_exp:
                        for imp in sorted(reduced):
                            lvl, meta = reduced[imp]
                            out_lines.append(import_line(imp, lvl, meta) + '\n')
                        emitted_exp = True
                elif kind == 'cut':
                    if not placed:
                        out_lines.extend(add_lines)
                        placed = True
                if k == last_import and not placed:
                    out_lines.extend(add_lines)
                    placed = True
            if not placed:
                out_lines.extend(add_lines)
            parts[mod]['header'] = ''.join(out_lines)
            # the new edges of this module, for the modules above it
            edges = [(k, lvl[0], lvl[1], meta) for k, lvl, meta in entries]
            edges += [(om, True, False, False) for om in additions]
            g.imports[mod] = edges
        # 4. no import closure contains a forbidden module
        fb = 0
        for f in forbidden:
            if f in g.idx:
                fb |= 1 << g.idx[f]
        offenders = [m for m in order if full_closure(m) & fb]
        if offenders:
            for m in offenders[:20]:
                hit = [f for f in forbidden if f in g.idx and full_closure(m) >> g.idx[f] & 1]
                print(f'ERROR: the import closure of {m} contains {", ".join(hit)}', file=sys.stderr)
            sys.exit(f'{len(offenders)} modules of the extract have a forbidden module in their import closure')
        self.closure_sizes = {m: bin(full_closure(m)).count('1') for m in order}

    def ns_edit(self, t, it, written, new):
        k = t.text.find(written, it.start, it.end)
        if k >= 0:
            self.edits[k] = (k + len(written), new)
            self.applied[('namespace ' + written, new)] += 1

    def rename_text(self, t, a, b, module):
        """The source text [a, b) with the renames applied."""
        out = []
        pos = a
        for s0 in sorted(k for k in self.edits if a <= k < b):
            e0, rep = self.edits[s0]
            if s0 < pos or e0 > b:
                continue
            out.append(t.text[pos:s0])
            out.append(rep)
            pos = e0
        out.append(t.text[pos:b])
        return ''.join(out)


def split_name(name):
    """Components of a dotted Lean name (guillemets respected)."""
    out = []
    cur = ''
    k = 0
    while k < len(name):
        c = name[k]
        if c == '«':
            e = name.find('»', k)
            e = len(name) - 1 if e < 0 else e
            cur += name[k:e + 1]
            k = e + 1
            continue
        if c == '.':
            out.append(cur)
            cur = ''
        else:
            cur += c
        k += 1
    out.append(cur)
    return [x for x in out if x != ''] if name else []


def join_name(comps):
    return '.'.join(comps)


def main_names(consts):
    """The names a command declares, without the auxiliary constants Lean generates."""
    out = []
    for c in consts:
        if re.search(r'\.(_|match_|proof_|eq_\d|congr_simp|casesOn$|rec$|recOn$|mk\._flat_ctor|below$|brecOn$|binductionOn$|noConfusion|ibelow$|injEq$|inj$|sizeOf_spec$|ext_iff$)', c):
            continue
        if '._aux_' in c or c.startswith('_aux'):
            continue
        out.append(c)
    return out


def strip_attached_comments(t, a, b):
    """The trivia [a, b) without the comments that directly precede its end (no blank line
    between them and the end), except module docs."""
    text = t.text
    seg_end = b
    cut = b
    while True:
        j = cut
        while j > a and text[j - 1] in ' \t':
            j -= 1
        # allow exactly one newline between a comment and what follows
        if j > a and text[j - 1] == '\n':
            j2 = j - 1
            while j2 > a and text[j2 - 1] in ' \t':
                j2 -= 1
        else:
            j2 = j
        sp = t.span_at(j2 - 1) if j2 > a else None
        if sp and sp[1] == j2 and sp[0] >= a and sp[2] in ('line', 'block'):
            # the comment must start a line
            k = sp[0]
            line_start = text.rfind('\n', 0, k) + 1
            if text[line_start:k].strip() == '':
                cut = line_start
                continue
        break
    return text[a:cut] + ('\n' if cut < seg_end and text[cut:seg_end].endswith('\n') else '')


def assemble(pieces):
    out = []
    for seg, protected in pieces:
        out.append((seg, protected))
    # merge and collapse blank lines in unprotected text
    res = []
    buf = ''
    for seg, protected in out:
        if protected:
            res.append(collapse(buf))
            buf = ''
            res.append(seg)
        else:
            buf += seg
    res.append(collapse(buf))
    return ''.join(res)


def collapse(s):
    return re.sub(r'\n[ \t]*\n(?:[ \t]*\n)+', '\n\n', s)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--source', default='/srv/ll-stx/full')
    ap.add_argument('--work', default=os.path.join(WS, '.tmp', 'stx-work'))
    ap.add_argument('--skip-cone', action='store_true', help='reuse the cone in the work directory')
    args = ap.parse_args()
    if not args.skip_cone:
        run_cone(args)
    ex = Extract(args)
    parts = {}
    for mod in ex.kept_mods:
        parts[mod] = ex.cut(mod)
    ex.make_headers(parts)
    outputs = {}
    for mod in ex.kept_mods:
        out = parts[mod]['header'].rstrip('\n') + '\n' + parts[mod]['body']
        out = out.rstrip('\n') + '\n'
        outputs[mod_relpath(mod)] = out
        ex.stats['extract lines'] += out.count('\n')
    # write
    for root in COPY_ROOTS:
        for path in glob.glob(os.path.join(WS, root, '**', '*.lean'), recursive=True):
            rel = os.path.relpath(path, WS)
            if rel not in outputs:
                os.remove(path)
    for rel, content in outputs.items():
        path = os.path.join(WS, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        old = None
        if os.path.exists(path):
            with open(path, encoding='utf-8') as f:
                old = f.read()
        if old != content:
            with open(path, 'w', encoding='utf-8') as f:
                f.write(content)
    for root in COPY_ROOTS:
        for d, subdirs, files in sorted(os.walk(os.path.join(WS, root), topdown=False)):
            if d != os.path.join(WS, root) and not os.listdir(d):
                os.rmdir(d)
    with open(os.path.join(WS, 'STX-MANIFEST.tsv'), 'w', encoding='utf-8') as f:
        f.write('file\tsource\tstatus\tdeclaration (name in the extract)\tprivate\t'
                'name in the source, if renamed\n')
        for row in sorted(ex.manifest):
            f.write('\t'.join(row) + '\n')
    with open(os.path.join(WS, 'tools', 'extract-commands.tsv'), 'w', encoding='utf-8') as f:
        f.write('file\tline\tchange\treason\tcommand (first line)\n')
        for row in ex.cmd_log:
            f.write('\t'.join(row) + '\n')
    with open(os.path.join(WS, 'tools', 'extract-imports.tsv'), 'w', encoding='utf-8') as f:
        f.write('file\tchange\tmodule\treason\n')
        for row in ex.import_log:
            f.write('\t'.join(row) + '\n')
    with open(os.path.join(WS, 'tools', 'renames-applied.tsv'), 'w', encoding='utf-8') as f:
        f.write('# The constants of the extract that the rows of STX-RENAMES.tsv rename (generated ones included)\n')
        f.write('old full name\tnew full name\n')
        for old in sorted(ex.kept_names):
            new = ex.rename_of(old)
            if new is not None:
                f.write(f'{old}\t{new}\n')
        f.write('# edits per rename (references, declared names, namespace commands)\n')
        for (old, new), k in sorted(ex.applied.items()):
            f.write(f'# {old}\t{new}\t{k}\n')
        for row in ex.rename_misses:
            f.write('# not rewritten (text is not a reference to the name): ' +
                    '\t'.join(str(x) for x in row) + '\n')
    with open(os.path.join(WS, 'tools', 'extract-warnings.txt'), 'w', encoding='utf-8') as f:
        for w in ex.warnings:
            f.write(w + '\n')
    ex.stats['modules'] = len(outputs)
    with open(os.path.join(WS, 'tools', 'extract-stats.txt'), 'w', encoding='utf-8') as f:
        for k in sorted(ex.stats):
            f.write(f'{k}\t{ex.stats[k]}\n')
    print(f'{len(outputs)} files; {len(ex.warnings)} warnings (tools/extract-warnings.txt)')
    for k in sorted(ex.stats):
        print(f'{k}\t{ex.stats[k]}')


if __name__ == '__main__':
    main()
```
