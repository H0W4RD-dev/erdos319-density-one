"""Exact checks of the CRT lemma in erdos319-solution.tex.

No external packages. Small global checks exhaust all subsets. The larger
case checks all local subset choices at every prime and the exact CRT.
These checks do not certify the imported analytic theorem or novelty.
"""
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path


def prime(n):
    return n >= 2 and all(n % j for j in range(2, math.isqrt(n) + 1))


def subset_sums(values):
    result = [0]
    for value in values:
        result += [old + value for old in result]
    return result


def construct(k, primes, global_check=True):
    assert len(primes) >= 2 and len(set(primes)) == len(primes)
    ell = math.lcm(*range(1, k + 1))
    coefficients = [ell // j for j in range(1, k + 1)]
    b = sum(coefficients)
    assert all(prime(p) and p > b for p in primes)
    modulus = math.prod(primes)
    t = 0
    partial = 1
    for p in primes:
        residue = -ell * pow(b * (modulus // p), -1, p) % p
        assert residue != 0
        correction = (residue - t) * pow(partial, -1, p) % p
        t += partial * correction
        partial *= p
    assert partial == modulus and 0 < t < modulus
    assert math.gcd(t, modulus) == 1
    numer = t * b * sum(modulus // p for p in primes) + ell
    assert numer % modulus == 0
    total = Fraction(numer // modulus, t * ell)
    assert math.gcd(total.denominator, modulus) == 1
    assert total == sum((Fraction(1, p * j) for p in primes for j in range(1, k + 1)), Fraction()) + Fraction(1, modulus * t)
    local_sums = subset_sums(coefficients)
    for p in primes:
        multiplier = t * (modulus // p)
        absent = [v for v in local_sums if multiplier * v % p == 0]
        present = [v for v in local_sums if (multiplier * v + ell) % p == 0]
        assert absent == [0] and present == [b]
    denominators = [p * j for p in primes for j in range(1, k + 1)] + [modulus * t]
    assert len(set(denominators)) == len(denominators)
    assert all(math.gcd(n, modulus) > 1 for n in denominators)
    row = {
        'K': k, 'prime_count': len(primes), 'primes': primes,
        'anchor_terms': len(denominators),
        'H_K': str(Fraction(b, ell)),
        'prime_reciprocal_sum': float(sum((Fraction(1, p) for p in primes), Fraction())),
        'rho': float(Fraction(math.prod(p - 1 for p in primes), modulus)),
        'anchor_reciprocal_sum': float(total),
        'anchor_sum_greater_than_one': total > 1,
        'modulus_decimal_digits': len(str(modulus)),
        'target_denominator_decimal_digits': len(str(total.denominator)),
        'all_local_subset_choices_checked': len(primes) * 2 ** k,
        'local_admissible_choices_without_connector': 'empty only',
        'local_admissible_choices_with_connector': 'full only',
        'global_enumeration': global_check,
    }
    if global_check:
        common = modulus * t * ell
        weights = [common // n for n in denominators]
        assert all(common % n == 0 for n in denominators)
        sums = subset_sums(weights)
        good = [j for j, value in enumerate(sums) if value % modulus == 0]
        assert good == [0, len(sums) - 1]
        row.update({
            'D': str(modulus), 't': str(t), 'target': str(total),
            'global_subsets_checked': len(sums),
            'D_integral_subsets_including_empty_and_full': len(good),
            'transcript_sha256': hashlib.sha256(','.join(map(str, sums)).encode()).hexdigest(),
        })
    else:
        row['exact_parameter_commitment_sha256'] = hashlib.sha256(f'{modulus},{t},{total.numerator},{total.denominator}'.encode()).hexdigest()
    return row


def main():
    rows = [
        construct(2, [5, 7, 11]),
        construct(3, [13, 17, 19, 23]),
        construct(4, [29, 31, 37, 41]),
        construct(5, [139, 149, 151]),
    ]
    # A larger finite example verifies r>1, while still checking all
    # 64 subset choices in each prime group. It is not a near-density-one
    # numerical example; that assertion is the analytic existence proof.
    primes = []
    reciprocal_sum = Fraction()
    p = 149
    while reciprocal_sum < Fraction(43, 100):
        if prime(p):
            primes.append(p)
            reciprocal_sum += Fraction(1, p)
        p += 1
    large = construct(6, primes, global_check=False)
    assert large['anchor_sum_greater_than_one']
    rows.append(large)
    positive = [5, 10, 7, 14, 11, 22, 28105]
    negative = [2, 8, 39, 22776]
    assert all(math.gcd(n, 385) == 1 for n in negative)
    assert not set(positive) & set(negative)
    common = math.lcm(*(positive + negative))
    signed = [common // n for n in positive] + [-common // n for n in negative]
    assert sum(signed) == 0
    signed_sums = subset_sums(signed)
    assert signed_sums.count(0) == 2
    assert sum((Fraction(1, n) for n in positive), Fraction()) == Fraction(95, 146)
    result = {
        'claim': 'Exact finite verification of the CRT construction lemma.',
        'cases': rows,
        'worked_signed_identity': {
            'positive': positive, 'negative': negative,
            'common_reciprocal_sum': '95/146',
            'signed_zero_subset_count_including_empty_and_full': signed_sums.count(0),
            'global_signed_subsets_checked': len(signed_sums),
        },
        'analytic_asymptotic_certified_by_computation': False,
        'independent_review': False,
        'novelty_assessed': False,
    }
    output = Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'cases': len(rows), 'all_checks_passed': True,
                      'global_subsets_checked': sum(r.get('global_subsets_checked', 0) for r in rows),
                      'worked_signed_identity_subsets_checked': len(signed_sums),
                      'large_case_prime_count': large['prime_count'],
                      'large_case_anchor_sum': large['anchor_reciprocal_sum']}, indent=2))


if __name__ == '__main__':
    main()
