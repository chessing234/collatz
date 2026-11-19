#!/usr/bin/env python3
"""Independent exact audit of Syracuse shadows and infinite-class certificates."""
from pathlib import Path
import random
import re
import runpy
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MODULE = 'Collatz.Strategy.SyracuseWordSieve'
SOURCES = [
    ('Collatz.ValuationTransition', ROOT / 'Collatz/Strategy/SyracuseData.lean'),
    ('Collatz.SyracuseShadows', ROOT / 'Collatz/Strategy/SyracuseShadows.lean'),
    ('Collatz.SyracuseWordSieve', ROOT / 'Collatz/Strategy/SyracuseWordSieve.lean'),
]


def step(n):
    assert n > 0 and n % 2
    value = 3*n + 1
    exponent = (value & -value).bit_length() - 1
    return exponent, value >> exponent


def word_eval(n, word):
    for exponent in word:
        n = (3*n + 1) // 2**exponent
    return n


def path_check(n, word):
    for exponent in word:
        value = 3*n + 1
        m = value // 2**exponent
        if not (n % 2 == 1 and m % 2 == 1 and value == 2**exponent*m):
            return False
        n = m
    return True


def class_check(n, word):
    return (path_check(n, word) and n < 2**(sum(word)+1)
            and 3**len(word) < 2**sum(word) and word_eval(n, word) < n)


def tail_residue(word):
    modulus = 3**len(word)
    total = 0
    suffix_inverse = 1
    three_power = 1
    inv_two = pow(2, -1, modulus)
    for exponent in reversed(word):
        suffix_inverse = suffix_inverse * pow(inv_two, exponent, modulus) % modulus
        total = (total + three_power*suffix_inverse) % modulus
        three_power = 3*three_power % modulus
    return total


def orbit_checks():
    rng = random.Random(20261119)
    seeds = [2*rng.randrange(1, 2**19)+1 for _ in range(3000)]
    seeds += [1, 3, 5, 7, 27, 31, 47, 63]
    seeds += [2**bits-1 for bits in range(2, 65)]
    identities = forgetting = units = 0
    for seed in seeds:
        n, word, total, c = seed, [], 0, 0
        horizon = max(48, seed.bit_length()+2)
        for k in range(1, horizon+1):
            exponent, n = step(n)
            c = 3*c + 2**total
            total += exponent
            word.append(exponent)
            assert 2**total*n == 3**k*seed+c
            assert 2**k*(n+1) <= 3**k*(seed+1)
            residue = tail_residue(word)
            assert n % 3**k == residue
            assert (2**total*n) % 3**k == c % 3**k
            assert (3**k*seed+c) % 2**(total+1) == 2**total
            if n == seed:
                assert seed*(2**total-3**k) == c
            identities += 1
            assert n % 3 != 0
            units += 1
            if seed+1 <= 2**k:
                assert n < 3**k and n == residue
                forgetting += 1
    return identities, forgetting, units


def class_checks():
    certified = lifts = 0
    for seed in range(3, 2002, 2):
        n, word = seed, []
        for _ in range(128):
            exponent, n = step(n)
            word.append(exponent)
            if n < seed:
                break
        else:
            continue
        if not class_check(seed, word):
            continue
        certified += 1
        modulus = 2**(sum(word)+1)
        for q in range(41):
            source = seed+modulus*q
            endpoint = word_eval(source, word)
            assert path_check(source, word)
            assert endpoint == n+2*3**len(word)*q
            assert endpoint < source
            lifts += 1
    assert class_check(3, [1, 4])
    assert class_check(5, [4])
    assert class_check(7, [1, 1, 2, 3])
    assert not class_check(3, [1, 3])
    assert not class_check(5, [2])
    assert not class_check(1, [2])
    assert not class_check(7, [1])
    return certified, lifts


def lean_check(text):
    with tempfile.TemporaryDirectory(prefix='collatz-shadows-') as directory:
        path = Path(directory) / 'Audit.lean'
        path.write_text(f'import {MODULE}\n' + text)
        return subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                              capture_output=True, text=True, timeout=180)


def proof_checks():
    names = []
    screen = runpy.run_path(str(ROOT / 'scripts/check_proof_escapes.py'))
    for namespace, source in SOURCES:
        text = source.read_text()
        assert not screen['violations'](text), source
        found = re.findall(r'^(?:@\[[^\]]+\]\s+)?theorem ([\w.]+)', text, re.MULTILINE)
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
    prefix = 'Collatz.SyracuseWordSieve.classCheck'
    false_claims = [
        f'example : {prefix} 3 [1, 3] = true := by decide\n',
        f'example : {prefix} 5 [2] = true := by decide\n',
        f'example : {prefix} 1 [2] = true := by decide\n',
        f'example : {prefix} 7 [1] = true := by decide\n',
        'example : (5 : Nat) < 3^1 := by decide\n',
        'example : Collatz.SyracuseShadows.tailSum 2 [1, 4] % 9 = 2 := by decide\n',
    ]
    for claim in false_claims:
        result = lean_check(claim)
        assert result.returncode != 0, claim
        assert 'Tactic `decide` proved that the proposition' in result.stdout, result.stdout + result.stderr
        assert 'is false' in result.stdout, result.stdout + result.stderr
    return len(names), len(false_claims)


def main():
    subprocess.run(['lake', 'build', MODULE], cwd=ROOT, check=True)
    identities, forgetting, units = orbit_checks()
    print(f'{identities} exact cocycles/growth/residue checks; '
          f'{forgetting} seed-forgetting checks; {units} ternary-unit checks', flush=True)
    certified, lifts = class_checks()
    print(f'{certified} finite class certificates; {lifts} exact infinite-class samples', flush=True)
    proofs, false = proof_checks()
    print(f'{proofs} Lean theorem footprints checked; {false} false controls rejected')
    print('No independence, entropy cutoff, inverse theorem, or universal convergence claim.')


if __name__ == '__main__':
    main()
