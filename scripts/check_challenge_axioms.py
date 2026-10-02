"""Audit genuine reference definitions separately from named theorem placeholders."""
import json
import re
import subprocess
import tempfile
from pathlib import Path
from authored_declarations import ROOT

config = json.loads((ROOT / 'comparator.json').read_text())
selected = config['theorem_names'] + config['definition_names']
assert config['theorem_names'] and config['definition_names']
source = 'module\npublic import Challenge\n' + ''.join('#print axioms ' + name + '\n' for name in selected)
with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='gershkov-reference-', delete=False) as handle:
    handle.write(source)
    path = Path(handle.name)
try:
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, text=True, capture_output=True, check=True)
finally:
    path.unlink()
rows = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout))
rows.update({name: '' for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout)})
assert set(rows) == set(selected)
permitted = set(config['permitted_axioms'])
for name, used in rows.items():
    allowed = permitted | {'sorryAx'} if name in config['theorem_names'] else permitted
    assert set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*', used)) <= allowed, (name, used)
(ROOT / 'evidence/challenge-reference-axioms.log').write_text(result.stdout)
print('Selected reference definitions have only standard axioms; theorem reference holes audited separately')
