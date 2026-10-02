"""Serial macOS reproduction of exact pinned Verso and trusted core audit/sanitizer.

Use isolated prepared render/core-audit workspaces. This does not claim Linux
sandbox confinement; the separate pinned hosted workflow provides that evidence.
"""
import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WORK = ROOT.parent / 'render-local'
POLICY = Path(os.environ['PALOMAR_SUBMISSION_DIR']).resolve()
PIN = '65f0154ed776cd26c224254aa57b379137f28b0d'
VERSO = '9f8096e40b31715b1d8d5997f15a0bd832f7e37d'
workspace = WORK / 'workspace'
core = WORK / 'core-audit'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(args, cwd, log, env=None):
    with (ROOT / 'evidence' / log).open('w') as handle:
        subprocess.run(args, cwd=cwd, stdout=handle, stderr=subprocess.STDOUT,
                       check=True, env=env, timeout=600)

assert subprocess.check_output(['git', '-C', str(POLICY), 'rev-parse', 'HEAD'], text=True).strip() == PIN
assert subprocess.check_output(['git', '-C', str(workspace / '.lake/packages/verso'), 'rev-parse', 'HEAD'], text=True).strip() == VERSO
assert sha(core / 'PalomarAudit.lean') == sha(POLICY / 'scripts/core_notation_audit.lean')
for name in ['Challenge.lean', 'Solution.lean', 'comparator.json']:
    shutil.copy2(ROOT / name, workspace / name)
run(['lake', 'build', 'palomar-audit'], core, 'local-core-audit-build.log')
run(['lake', 'build', 'Challenge:literate'], workspace, 'local-literate.log')
sys.path.insert(0, str(POLICY))
from scripts.render_challenge import core_notation_audit_lean_path, validated_audit_declarations

lean = Path(subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=workspace, text=True).strip())
prefix = Path(subprocess.check_output([str(lean), '--print-prefix'], text=True).strip())
path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=workspace, text=True).strip()
env = os.environ.copy()
env['LEAN_PATH'] = core_notation_audit_lean_path(path, workspace=workspace,
                                              challenge_module='Challenge', lean_prefix=prefix)
config = json.loads((ROOT / 'comparator.json').read_text())
names = config['theorem_names'] + config['definition_names']
pairs = [('theorem', name) for name in config['theorem_names']] + [('def', name) for name in config['definition_names']]
command = [str(core / '.lake/build/bin/palomar-audit'), 'Challenge'] + [item for pair in pairs for item in pair]
audit = subprocess.check_output(command, cwd=workspace, env=env, text=True, timeout=180)
rows = validated_audit_declarations(json.loads(audit), names)
(WORK / 'audit-declarations.json').write_text(json.dumps(rows, indent=2) + '\n')
shutil.copy2(WORK / 'audit-declarations.json', ROOT / 'evidence/render-core-audit.json')
raw, clean = WORK / 'raw-html', WORK / 'sanitized-html'
for directory in [raw, clean]:
    if directory.exists():
        shutil.rmtree(directory)
    directory.mkdir()
run(['lake', 'exe', 'verso-html', str(workspace / '.lake/build/literate'), str(raw)],
    workspace, 'local-verso-html.log')
run([sys.executable, str(POLICY / 'scripts/render_challenge.py'), 'sanitize',
     '--input-dir', str(raw), '--output-dir', str(clean),
     '--challenge', str(ROOT / 'Challenge.lean'), '--solution', str(ROOT / 'Solution.lean'),
     '--comparator', str(ROOT / 'comparator.json'), '--challenge-module', 'Challenge',
     '--lean', str(lean), '--diagnostic-out', str(WORK / 'sanitizer-diagnostic.json'),
     '--audit-declarations', str(WORK / 'audit-declarations.json')],
    POLICY, 'local-sanitizer.log')
pages = {str(page.relative_to(clean)): page.stat().st_size for page in clean.rglob('*.html')}
assert pages and max(pages.values()) < 8 * 1024 * 1024, pages
report = {'status': 'pass', 'scope': 'Local macOS reproduction; no Linux sandbox or hosted workflow claim',
          'policy_commit': PIN, 'verso_commit': VERSO,
          'challenge_sha256': sha(ROOT / 'Challenge.lean'),
          'core_audit_source_sha256': sha(core / 'PalomarAudit.lean'),
          'core_audit_executable_sha256': sha(core / '.lake/build/bin/palomar-audit'),
          'trusted_audit_declarations': len(rows), 'html_files': pages,
          'per_html_limit_bytes': 8 * 1024 * 1024}
(ROOT / 'evidence/local-render.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
