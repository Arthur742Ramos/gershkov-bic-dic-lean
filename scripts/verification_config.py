"""Use the pinned official validator; external kernels remain execution-only."""
import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PIN = '65f0154ed776cd26c224254aa57b379137f28b0d'
parser = argparse.ArgumentParser()
parser.add_argument('destination', type=Path)
args = parser.parse_args()
assert os.environ.get('PALOMAR_SUBMISSION_DIR'), 'Set PALOMAR_SUBMISSION_DIR to the pinned official checkout'
policy = Path(os.environ['PALOMAR_SUBMISSION_DIR']).resolve()
assert subprocess.check_output(['git', '-C', str(policy), 'rev-parse', 'HEAD'], text=True).strip() == PIN
sys.path.insert(0, str(policy))
from scripts.verify_submission import load_comparator_config

config = load_comparator_config(ROOT / 'comparator.json')
assert config['theorem_names'] and config['definition_names'], 'Comparison contracts are unfinished'
prefix = Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'], cwd=ROOT, text=True).strip())
kernels = {name: [str(prefix / 'bin' / binary)] for name, binary in
    (('nanoda', 'nanoda_bin'), ('con-ron', 'con-ron'))}
for command in kernels.values():
    assert Path(command[0]).is_file() and os.access(command[0], os.X_OK), command
destination = args.destination.resolve()
assert not destination.is_relative_to(ROOT) and not args.destination.is_symlink()
config['external_kernels'] = kernels
destination.write_text(json.dumps(config, indent=2) + '\n')
print('Official Comparator configuration validated; bundled NanoDa and con-ron selected for execution')
