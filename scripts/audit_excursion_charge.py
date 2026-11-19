#!/usr/bin/env python3
"""Independently audit optimal excursion charges and their Lean proof footprints."""
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MODULE = 'Collatz.Strategy.ExcursionCharge'
NAMESPACE = 'Collatz.ExcursionCharge'
SOURCES = [
    ('Collatz.ExcursionCharge', ROOT / 'Collatz/Strategy/ExcursionChargeCore.lean'),
    ('Collatz.ExcursionCharge', ROOT / 'Collatz/Strategy/ExcursionCharge.lean'),
    ('Collatz.ExcursionMap', ROOT / 'Collatz/Strategy/ExcursionData.lean'),
    ('Collatz.ExcursionBudget', ROOT / 'Collatz/Strategy/ExcursionBudget.lean'),
]


def charge(scale, run):
    return scale - scale * 2**run // 3**run


def ninths(run):
    return (0, 3, 5)[run] if run < 3 else 9


def excursion(n):
    run = halvings = 0
    x = n
    while x % 2:
        x = (3*x + 1) // 2
        run += 1
    while x % 2 == 0:
        x //= 2
        halvings += 1
    return run, halvings, x


def arithmetic_checks():
    minimality = refinement = ternary = saturation = 0
    for scale in range(61):
        for run in range(81):
            a, b = 3**run, 2**run
            # Compute a ceiling directly, independently of the Lean formula.
            expected = (scale*(a-b) + a - 1) // a
            actual = charge(scale, run)
            assert actual == expected
            candidates = {0, max(actual-1, 0), actual, actual+1, scale, scale+1}
            for candidate in candidates:
                assert (actual <= candidate) == (scale*(a-b) <= candidate*a)
                minimality += 1
            for multiplier in range(13):
                assert charge(multiplier*scale, run) <= multiplier*actual
                refinement += 1
            assert (actual == scale) == (scale*b < a)
            saturation += 1
    for exponent in range(31):
        for run in range(exponent+1):
            scale = 3**exponent
            exact = scale - 2**run * 3**(exponent-run)
            assert charge(scale, run) == exact
            assert exact*3**run == scale*(3**run - 2**run)
            ternary += 1
    for scale in range(101):
        assert charge(scale, 2*scale) == scale
        saturation += 1
    assert [charge(9, run) for run in range(7)] == [0, 3, 5, 7, 8, 8, 9]
    for run in range(201):
        assert charge(9, run) <= ninths(run)
    assert charge(3, 1)*4 < charge(4, 1)*3
    return minimality, refinement, ternary, saturation


def trace_checks():
    checked = improved = 0
    for n in range(3, 20002, 2):
        x, odd, time, exact_weight, old_weight = n, 0, 0, 0, 0
        prefixes = [(odd, time)]
        for _ in range(12):
            run, halvings, x = excursion(x)
            odd += run
            time += run + halvings
            exact_weight += charge(9, run)
            old_weight += ninths(run)
            assert exact_weight <= old_weight
            for p, d in [(2, 1), (6, 5), (8, 7), (10, 9), (11, 10)]:
                proper = all(d*2**t <= p*3**a for a, t in prefixes)
                crossing = p*3**odd < d*2**time
                old = d*9*n + p*old_weight <= p*9*n
                new = d*9*n + p*exact_weight <= p*9*n
                if proper and crossing and new:
                    assert x < n
                    checked += 1
                    improved += not old
            prefixes.append((odd, time))
            if x == 1:
                break
    # Same-trace, same-threshold strict improvement used in Lean.
    assert excursion(7) == (3, 1, 13)
    assert excursion(13) == (1, 2, 5)
    assert 5*9*7 + 6*10 <= 6*9*7 < 5*9*7 + 6*12
    assert improved > 0
    return checked, improved


def lean_check(text):
    with tempfile.TemporaryDirectory(prefix='collatz-charge-') as directory:
        path = Path(directory) / 'Audit.lean'
        path.write_text(f'import {MODULE}\n' + text)
        return subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                              capture_output=True, text=True, timeout=120)


def proof_checks():
    names = []
    for namespace, source in SOURCES:
        found = re.findall(r'^(?:@\[[^\]]+\]\s+)?theorem ([\w.]+)',
                           source.read_text(), re.MULTILINE)
        assert found, source
        names.extend(f'{namespace}.{name}' for name in found)
    audit = lean_check(''.join(f'#print axioms {name}\n' for name in names))
    assert audit.returncode == 0, audit.stdout + audit.stderr
    footprints = re.findall(
        r"'([^']+)' "
        r'(?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])',
        audit.stdout)
    assert [name for name, _ in footprints] == names, audit.stdout
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, axioms in footprints:
        found = {axiom.strip() for axiom in axioms.split(',') if axiom.strip()}
        assert found <= allowed, (name, found)
    false_claims = [
        f'example : {NAMESPACE}.charge 9 3 = 6 := by decide\n',
        f'example : {NAMESPACE}.charge 9 6 < 9 := by decide\n',
        f'example : 3 * {NAMESPACE}.charge 4 1 ≤ 4 * {NAMESPACE}.charge 3 1 := by decide\n',
        'example : 9 * ((3 : Nat)^3 - 2^3) ≤ 6 * 3^3 := by decide\n',
        'example : (5 : Nat)*9*7 + 6*12 ≤ 6*9*7 := by decide\n',
    ]
    for claim in false_claims:
        result = lean_check(claim)
        assert result.returncode != 0, claim
        assert 'Tactic `decide` proved that the proposition' in result.stdout, result.stdout + result.stderr
        assert 'is false' in result.stdout, result.stdout + result.stderr
    return len(names), len(false_claims)


def main():
    subprocess.run(['lake', 'build', MODULE], cwd=ROOT, check=True)
    minimality, refinement, ternary, saturation = arithmetic_checks()
    certificates, improved = trace_checks()
    proofs, false = proof_checks()
    print(f'{minimality} minimality checks; {refinement} refinement checks; '
          f'{ternary} exact ternary charges; {saturation} saturation checks')
    print(f'{certificates} valid finite trace certificates; {improved} pass the '
          'optimal budget but fail the old budget at the same threshold')
    print(f'{proofs} Lean theorem footprints checked; {false} false controls rejected')
    print('Conditional criteria only; no universal crossing or convergence proof, '
          'and no claim of mathematical priority.')


if __name__ == '__main__':
    main()
