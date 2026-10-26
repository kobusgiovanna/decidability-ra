#!/usr/bin/env bash
#
# Check that every .lean file under RAUndecidability/ is reachable, via
# imports, from RAUndecidability.lean (the file `lake build`/CI/Verify.lean
# actually see) — and that Verify.lean imports the RAUndecidability root.
#
# Why this exists instead of `lake exe mk_all --check`: mk_all expects every
# `lean_lib` in lakefile.toml to have a same-named directory (RAUndecidability/
# does; Verify does not — it is deliberately one flat file), and it crashes
# rather than reporting cleanly when that directory is missing. Separately,
# mk_all's own fix (regenerating the aggregator file) sorts the import list
# alphabetically, discarding this project's deliberate dependency-order
# imports — so even scoping it to RAUndecidability alone
# would still flag a false positive. This script checks the actual property
# ("nothing is silently unbuilt") without either problem, and needs no
# particular import order.
#
# Usage: scripts/check-imports.sh
# Exit status is 1 if any file is unreachable, so it can be used in CI.

set -euo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

python3 - <<'PY'
import re, sys, glob, os

def module_name(path):
    # RAUndecidability/Reduction/Threads.lean -> RAUndecidability.Reduction.Threads
    return path[:-len('.lean')].replace(os.sep, '.')

def imports_of(path):
    text = open(path, encoding='utf-8', errors='replace').read()
    return set(re.findall(r'(?m)^import\s+([A-Za-z0-9_.]+)\s*$', text))

# --- every file that must be reachable -------------------------------------
expected = {module_name(p) for p in sorted(glob.glob('RAUndecidability/**/*.lean', recursive=True))}

# --- the import graph over every .lean file in the project (root files and
# everything under RAUndecidability/); only RAUndecidability.* edges matter --
all_files = ['RAUndecidability.lean', 'Verify.lean'] + \
    sorted(glob.glob('RAUndecidability/**/*.lean', recursive=True))

graph = {}
for path in all_files:
    src = module_name(path) if path != 'RAUndecidability.lean' else 'RAUndecidability'
    if path == 'Verify.lean':
        src = 'Verify'
    graph[src] = {m for m in imports_of(path) if m == 'RAUndecidability' or m.startswith('RAUndecidability.')}

# --- BFS from the RAUndecidability aggregator ------------------------------
seen = set()
frontier = ['RAUndecidability']
while frontier:
    m = frontier.pop()
    if m in seen:
        continue
    seen.add(m)
    frontier.extend(graph.get(m, ()) - seen)

reachable = seen & expected
unreachable = sorted(expected - reachable)

problems = 0

if unreachable:
    problems += len(unreachable)
    print("Not imported (directly or transitively) from RAUndecidability.lean:")
    for m in unreachable:
        print("  %s" % m)
    print()

if 'RAUndecidability' not in graph.get('Verify', set()):
    problems += 1
    print("Verify.lean does not `import RAUndecidability` — it would not see")
    print("anything built under RAUndecidability/ at all.")
    print()

print("files under RAUndecidability/: %d   reachable from the root: %d"
      % (len(expected), len(reachable)))

if problems:
    print("\n%d problem(s) found." % problems)
    sys.exit(1)
print("Every file is reachable; Verify.lean imports the root. OK.")
PY
