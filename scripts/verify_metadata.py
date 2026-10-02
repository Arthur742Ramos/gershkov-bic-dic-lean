"""Validate metadata with exact official policy and checked taxonomy entries."""
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PIN = '65f0154ed776cd26c224254aa57b379137f28b0d'
assert os.environ.get('PALOMAR_SUBMISSION_DIR'), 'Set PALOMAR_SUBMISSION_DIR'
policy = Path(os.environ['PALOMAR_SUBMISSION_DIR']).resolve()
assert subprocess.check_output(['git', '-C', str(policy), 'rev-parse', 'HEAD'], text=True).strip() == PIN
sys.path.insert(0, str(policy))
from scripts.submission_contract import load_formalization_metadata
import yaml

metadata = load_formalization_metadata(ROOT / 'formalization.yaml')
authors = ['Arthur Freitas Ramos', 'David Barros Hulak', 'Ruy Jose Guerra Barretto de Queiroz']
assert metadata['project']['authors'] == authors
assert metadata['project']['responsible_maintainers'] == authors
assert metadata['project']['license'] == 'BSD-3-Clause'
codes = ['91A27', '91A10', '91B44', '03B35']
taxonomy = json.loads((policy / 'taxonomies/msc2020-codes.json').read_text())
assert metadata['classification']['msc2020'] == codes and all(code in taxonomy for code in codes)
config = json.loads((ROOT / 'comparator.json').read_text())
assert [item['lean'] for item in metadata['alignment']['statements']] == config['theorem_names']
citation = yaml.safe_load((ROOT / 'CITATION.cff').read_text())
assert [item['given-names'] + ' ' + item['family-names'] for item in citation['authors']] == authors
assert all(author in (ROOT / 'README.md').read_text() for author in authors)
print('Official metadata structure, author, taxonomy and stated alignment checks passed; this does not verify the theorem')
