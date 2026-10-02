"""Generate compact exact contracts with genuine copied definition bodies.

Challenge deliberately replaces only the three named reference theorem proofs.
Solution copies the same definitions and proves the same headers by the complete
Gershkov library. No theorem assumption or conclusion is rewritten.
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DECL = re.compile(r"(?m)^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|public|protected)\s+)*(?:abbrev|def|theorem|lemma|instance)\s+([\w']+)\b")


def declaration(file, name):
    source = (ROOT / 'Gershkov' / (file + '.lean')).read_text()
    matches = list(DECL.finditer(source))
    match = next(item for item in matches if item[1] == name)
    end = min([item.start() for item in matches if item.start() > match.start()] +
              [source.rindex('\nend ')])
    text = source[match.start():end]
    # Exclude doc comments belonging to the following declaration.
    text = re.sub(r'\n\s*/\-.*', '', text, flags=re.S)
    return text.rstrip()


def header(file, name):
    text = declaration(file, name)
    assert ' := by' in text, (file, name, 'Unexpected theorem proof syntax')
    return text[:text.index(' := by')]


groups = [
    ('Smoothing', 'GGKMS', '''universe uP uK uI
variable {P : Type uP} {K : Type uK} {I : Type uI}
variable [Fintype P] [DecidableEq P] [Fintype K] [Fintype I]''',
     ['value', 'Feasible', 'energy']),
    ('Model', 'GGKMS', '''universe uI uT uK
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {T : I → Type uT} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable {K : Type uK} [Fintype K]''',
     ['Profile', 'Opponents', 'pack', 'joint', 'opponentMass', 'SupportPrior',
      'interim', 'exAnte', 'slope', 'Matches']),
    ('Mechanism', 'GGKMS', '''universe uI uK
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {K : Type uK} [Fintype K]
variable {n : I → ℕ}''',
     ['Types', 'modified', 'payoff', 'interimPayoff', 'BIC', 'DIC',
      'modifiedInterim', 'socialSurplus']),
    ('Transfers', 'GGKMS.Transfers', '', ['ScalarIC', 'AdjacentIC']),
    ('Support', 'GGKMS', '''universe uA
variable {A : Type uA} [Fintype A] [DecidableEq A]''',
     ['PositiveSupport', 'positiveSupportFintype', 'positiveSupportDecidableEq']),
]
theorems = [
    ('Equivalence', 'GGKMS', groups[2][2], 'finite_bayesian_dominant_equivalence',
     'Gershkov.finite_bayesian_dominant_equivalence p θ hp hθ a c _ha q₀ pay₀ hfeasible hBIC'),
    ('Lifting', 'GGKMS', groups[1][2] + '\nvariable [∀ i, Preorder (T i)]',
     'weighted_monotone_lifting', 'Gershkov.weighted_monotone_lifting p hp a q₀ hq₀ hmono'),
    ('Lifting', 'GGKMS', groups[1][2] + '\nvariable [∀ i, Preorder (T i)]',
     'minimizer_monotone', 'Gershkov.minimizer_monotone p hp a q q₀ hq hmono hmin'),
]
imports = '''module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Order.Fin.Basic
'''
intro = '''
/-! Exact finite GGKMS Theorem 2 and its weighted allocation contracts. All model and support
definitions and named instances have genuine implementation bodies copied from
the library. Only the three named reference theorem proof bodies are intentional
placeholders. Complete proofs are exported by Solution under GGKMS and developed
under the distinct Gershkov namespace. Types are strictly ordered finite supports;
arbitrary independent positive support masses are permitted. Null-label deletion
preserves expectations and does not claim incentive compatibility at null reports. -/
@[expose] public section
open scoped BigOperators
'''
challenge = imports + intro
solution = 'module\npublic import Gershkov\n' + intro.replace(
    'Only the three named reference theorem proof bodies are intentional\nplaceholders.', 'Every theorem below is proved by the complete implementation.')
definition_names = []
for file, namespace, context, names in groups:
    block = '\nnamespace ' + namespace + '\n' + context + '\n\n'
    for name in names:
        block += declaration(file, name) + '\n\n'
        definition_names.append(namespace + '.' + name)
    block += 'end ' + namespace + '\n'
    challenge += block
    solution += block
theorem_names = []
for file, namespace, context, name, proof in theorems:
    block = '\nnamespace ' + namespace + '\n' + context + '\n\n' + header(file, name)
    challenge += block + ' := by\n  sorry\n\nend ' + namespace + '\n'
    solution += block + ' := by\n  exact ' + proof + '\n\nend ' + namespace + '\n'
    theorem_names.append(namespace + '.' + name)
(ROOT / 'Challenge.lean').write_text(challenge)
(ROOT / 'Solution.lean').write_text(solution)
config = {'challenge_module': 'Challenge', 'solution_module': 'Solution',
    'theorem_names': theorem_names, 'definition_names': definition_names,
    'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice']}
(ROOT / 'comparator.json').write_text(json.dumps(config, indent=2) + '\n')
print(f'Generated {len(theorem_names)} exact theorem contracts and {len(definition_names)} genuine definition/instance bodies')
