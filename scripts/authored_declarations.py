"""Inventory explicit Lean declarations; fail closed on unhandled generated forms.

This scanner is deliberately limited to named def/abbrev/theorem/lemma/instance
declarations. Classes, structures, inductives, anonymous instances, private names
and examples need an environment-based inventory before they can be accepted.
Transitive #print axioms auditing also covers each named declaration's helpers.
"""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def strip_comments(source):
    """Mask nested Lean comments and string literals while preserving lines."""
    result, index, depth, quoted = [], 0, 0, False
    while index < len(source):
        if depth:
            if source.startswith('/-', index):
                depth += 1
                result.extend('  ')
                index += 2
            elif source.startswith('-/', index):
                depth -= 1
                result.extend('  ')
                index += 2
            else:
                result.append('\n' if source[index] == '\n' else ' ')
                index += 1
        elif quoted:
            if source[index] == '\\':
                result.extend('  ')
                index += 2
            elif source[index] == '"':
                quoted = False
                result.append(' ')
                index += 1
            else:
                result.append('\n' if source[index] == '\n' else ' ')
                index += 1
        elif source.startswith('/-', index):
            depth = 1
            result.extend('  ')
            index += 2
        elif source.startswith('--', index):
            end = source.find('\n', index)
            if end < 0:
                end = len(source)
            result.extend(' ' * (end-index))
            index = end
        elif source[index] == '"':
            quoted = True
            result.append(' ')
            index += 1
        else:
            result.append(source[index])
            index += 1
    assert depth == 0 and not quoted, 'Unterminated Lean comment/string'
    return ''.join(result)


def lean_files():
    return sorted([*ROOT.glob('*.lean'), *ROOT.glob('Gershkov/**/*.lean')])


def declaration_inventory(files=None):
    inventory = []
    for file in lean_files() if files is None else files:
        if files is None and file.name in {'Challenge.lean', 'Audit.lean', 'ContractAudit.lean'}:
            continue
        stack = []
        for number, line in enumerate(strip_comments(file.read_text()).splitlines(), 1):
            clean = re.sub(r'^\s*(?:@\[[^\]]*\]\s*)*', '', line).strip()
            namespace = re.match(r'^namespace\s+([^\s]+)$', clean)
            if namespace:
                name = namespace[1]
                current = stack[-1][1] if stack else ''
                full = name.removeprefix('_root_.') if name.startswith('_root_.') else (
                    current + '.' + name if current else name)
                stack.append(('namespace', full))
                continue
            if re.match(r'^(?:noncomputable\s+)?section(?:\s|$)', clean):
                stack.append(('section', stack[-1][1] if stack else ''))
                continue
            if re.match(r'^end(?:\s|$)', clean):
                assert stack, (file, number, 'Unmatched end')
                stack.pop()
                continue
            assert not re.match(r'^(?:private\s+|protected\s+)*(?:structure|class|inductive|opaque|example|macro|syntax|elab)\b', clean), (file, number, 'Requires environment inventory', clean)
            assert not re.match(r'^private\b', clean), (file, number, 'Private name requires environment inventory')
            decl = re.match(r'^(?:(?:public|protected|noncomputable)\s+)*(def|abbrev|theorem|lemma|instance)\s+([\w\']+(?:\.[\w\']+)*)', clean)
            if decl:
                current = stack[-1][1] if stack else ''
                name = current + '.' + decl[2] if current else decl[2]
                assert name.startswith(('Gershkov.', 'GGKMS.')), (file, number, name)
                inventory.append({'name': name, 'kind': decl[1],
                    'source': str(file.relative_to(ROOT)), 'line': number})
            else:
                assert not re.match(r'^(?:(?:public|protected|noncomputable)\s+)*(def|abbrev|theorem|lemma|instance)\b', clean), (file, number, 'Unnamed or unsupported declaration', clean)
        assert not stack, (file, 'Unclosed namespace/section')
    names = [row['name'] for row in inventory]
    assert names and len(names) == len(set(names)), 'Empty or duplicated declaration inventory'
    return inventory


def authored_names():
    return [row['name'] for row in declaration_inventory()]


if __name__ == '__main__':
    assert (ROOT / 'Solution.lean').is_file(), 'Complete Solution export is still missing'
    config = json.loads((ROOT / 'comparator.json').read_text())
    selected = config['theorem_names'] + config['definition_names']
    assert config['theorem_names'] and config['definition_names'], 'Comparison contracts are unfinished'
    inventory = declaration_inventory()
    (ROOT / 'Audit.lean').write_text('module\npublic import Solution\n\n' +
        ''.join('#print axioms ' + row['name'] + '\n' for row in inventory))
    (ROOT / 'ContractAudit.lean').write_text('module\npublic import Challenge\n\nset_option pp.explicit true\n' +
        ''.join('#check @' + name + '\n#print ' + name + '\n' for name in selected))
    record = {'declarations': inventory, 'sources_sha256': {
        str(file.relative_to(ROOT)): hashlib.sha256(file.read_bytes()).hexdigest()
        for file in lean_files() if file.name not in {'Audit.lean', 'ContractAudit.lean'}}}
    (ROOT / 'evidence').mkdir(exist_ok=True)
    (ROOT / 'evidence/authored-declarations.json').write_text(json.dumps(record, indent=2) + '\n')
    print(f'Inventoried {len(inventory)} explicit authored declarations; review generated-form coverage separately')
