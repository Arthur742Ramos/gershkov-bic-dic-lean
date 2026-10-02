"""Require finished contracts, no proof holes, full axiom coverage and exact hashes."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from authored_declarations import ROOT, authored_names, declaration_inventory, lean_files, strip_comments

config = json.loads((ROOT / 'comparator.json').read_text())
assert set(config) == {'challenge_module', 'solution_module', 'theorem_names', 'definition_names', 'permitted_axioms'}
permitted = {'propext', 'Quot.sound', 'Classical.choice'}
assert set(config['permitted_axioms']) == permitted
assert config['challenge_module'] == 'Challenge' and config['solution_module'] == 'Solution'
selected = config['theorem_names'] + config['definition_names']
assert config['theorem_names'] and config['definition_names'], 'Unfinished comparison name lists'
assert len(selected) == len(set(selected)) and all(name.startswith('GGKMS.') for name in selected)
assert all((ROOT / file).is_file() for file in ['Challenge.lean', 'Solution.lean', 'Audit.lean', 'ContractAudit.lean'])
original = {file: (ROOT / file).read_bytes() for file in ['Challenge.lean', 'Solution.lean', 'comparator.json']}
subprocess.run([sys.executable, str(ROOT / 'scripts/make_challenge.py')], check=True, capture_output=True)
assert all((ROOT / file).read_bytes() == content for file, content in original.items()), 'Generated exact contract drift'
challenge = strip_comments((ROOT / 'Challenge.lean').read_text())
holes = len(re.findall(r'\bsorry\b', challenge))
assert holes in {0, len(config['theorem_names'])}, 'Challenge holes must be exactly the named reference theorem proofs'
reference_declarations = declaration_inventory([ROOT / 'Challenge.lean'])
hole_names = []
for number, line in enumerate(challenge.splitlines(), 1):
    if re.search(r'\bsorry\b', line):
        preceding = [row for row in reference_declarations if row['line'] < number]
        assert preceding, ('Unowned reference hole', number)
        owner = preceding[-1]
        assert owner['kind'] == 'theorem' and owner['name'] in config['theorem_names'], owner
        assert re.fullmatch(r'\s*sorry\s*', line), ('Only an isolated named reference proof placeholder is allowed', number)
        hole_names.append(owner['name'])
if holes:
    assert len(hole_names) == len(set(hole_names)) and set(hole_names) == set(config['theorem_names'])
for file in lean_files():
    source = strip_comments(file.read_text())
    assert source.startswith('module\n'), file
    if file.name == 'Challenge.lean':
        source = re.sub(r'(?m)^\s*sorry\s*$', '', source)
    assert not re.search(r'\b(sorry|sorryAx|admit|axiom|unsafe|native_decide|ofReduceBool|implemented_by)\b', source), file
assert len((ROOT / 'Challenge.lean').read_bytes()) < 64*1024, 'Keep the exact contract compact and render it'
inventory = json.loads((ROOT / 'evidence/authored-declarations.json').read_text())
names = authored_names()
assert names == [row['name'] for row in inventory['declarations']]
for file, expected in inventory['sources_sha256'].items():
    assert hashlib.sha256((ROOT / file).read_bytes()).hexdigest() == expected, ('Inventory source drift', file)
log = (ROOT / 'evidence/final-axioms.log').read_text()
rows = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log))
rows.update({name: '' for name in re.findall(r"'([^']+)' does not depend on any axioms", log)})
assert set(rows) == set(names), ('Axiom inventory mismatch', set(names)-set(rows), set(rows)-set(names))
for name, used in rows.items():
    assert set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*', used)) <= permitted, (name, used)
environment_log = (ROOT / 'evidence/environment-axioms.log').read_text()
environment_rows = re.findall(r'ENV-AUDIT ([\w.]+) ([^:]+):', environment_log)
environment_names = {name for module, name in environment_rows}
assert set(names) <= environment_names, ('Environment omitted explicit declarations', set(names)-environment_names)
environment_count = re.search(r'ENV-AUDIT PASS: (\d+) authored constants', environment_log)
assert environment_count and int(environment_count[1]) == len(environment_rows)
hash_files = lean_files() + [ROOT / file for file in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'comparator.json', 'formalization.yaml', 'README.md', 'CITATION.cff']]
hash_files += sorted(ROOT.glob('scripts/*.py')) + sorted(ROOT.glob('scripts/*.sh')) + sorted(ROOT.glob('scripts/*.lean')) + sorted(ROOT.glob('.github/workflows/*.yml')) + [ROOT / 'LICENSE']
record = {'source_files_sha256': {str(file.relative_to(ROOT)): hashlib.sha256(file.read_bytes()).hexdigest() for file in sorted(hash_files)},
    'authored_declaration_count': len(names), 'environment_constant_count': int(environment_count[1]), 'selected_theorems': config['theorem_names'],
    'selected_definitions': config['definition_names'],
    'lean': (ROOT / 'lean-toolchain').read_text().strip(),
    'mathlib': '065356127b1dc0016f66b7283ce0ce2c4055aa55'}
manifest = ROOT / 'evidence/verification-manifest.json'
if '--record' in sys.argv:
    manifest.write_text(json.dumps(record, indent=2) + '\n')
else:
    assert json.loads(manifest.read_text()) == record, 'Verification source hash drift'
print(f'Package and all {len(names)} explicit authored declaration axiom checks passed')
