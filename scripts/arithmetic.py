"""Independent finite oracle using Kronecker symbols and exponential generating series."""
from fractions import Fraction
from math import factorial
from pathlib import Path
import json


def jacobi(a, n):
    if n <= 0 or n % 2 == 0:
        raise ValueError("positive odd denominator required")
    a %= n
    sign = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                sign = -sign
        if a % 4 == n % 4 == 3:
            sign = -sign
        a, n = n % a, a
    return sign if n == 1 else 0


def kronecker_at(D, a):
    if a == 0:
        return int(abs(D) == 1)
    result = -1 if a < 0 and D < 0 else 1
    a = abs(a)
    while a % 2 == 0:
        a //= 2
        result *= 0 if D % 2 == 0 else (-1 if D % 8 in (3, 5) else 1)
    return result * jacobi(D, a)


def calculate(inputs):
    f, D, p, modulus = (inputs[k] for k in
        ("conductor", "quadratic_discriminant", "local_prime", "modulus"))
    samples = inputs["negative_interpolation_indices"]
    signs = [kronecker_at(D, a) for a in range(1, f + 1)]
    moments = [sum(e * a**k for a, e in enumerate(signs, 1))
               for k in range(max(samples) + 2)]
    # Divide sum chi(a)e^(at) by (e^(ft)-1)/t as ordinary power series.
    coeff = []
    for k, moment in enumerate(moments):
        value = Fraction(moment, factorial(k))
        for j in range(1, k + 1):
            value -= Fraction(f**(j+1), factorial(j+1)) * coeff[k-j]
        coeff.append(value / f)

    def special(n):
        return -coeff[n+1] * factorial(n)

    F0 = (1 - kronecker_at(D, p)) * special(0)
    entries = {"conductor": f, "character_at_p": kronecker_at(D, p)}
    for k in inputs["power_sum_indices"]:
        entries[f"sum_{k}"] = moments[k]
    entries["L_0"] = special(0)
    slopes = []
    for n in samples:
        ln = special(n)
        fn = (1 - kronecker_at(D, p) * p**n) * ln
        slope = (fn - F0) / (-n * F0)
        residue = slope.numerator * pow(slope.denominator, -1, modulus) % modulus
        slopes.append(residue)
        entries.update({f"L_minus_{n}_num": ln.numerator, f"L_minus_{n}_den": ln.denominator,
                        f"secant_{n}_num": slope.numerator, f"secant_{n}_den": slope.denominator,
                        f"secant_{n}_mod49_ok": str(residue == 42).lower()})
    if len(set(slopes)) != 1:
        raise ValueError("inconsistent secants")
    entries["F_0"] = F0
    F6 = (1 - kronecker_at(D,p)*p**6) * special(6)
    entries["F_minus_6_mod49"] = F6.numerator * pow(F6.denominator,-1,modulus) % modulus
    entries["slope_F"] = slopes[0] * F0.numerator * pow(F0.denominator, -1, modulus) % modulus
    entries["slope_normalized"] = slopes[0]
    coeffs = inputs["cubic_coefficients_low_to_high"]
    for prime in inputs["cubic_primes"]:
        entries[f"cubic_{prime}_roots"] = [a for a in range(prime)
                if sum(b*a**i for i,b in enumerate(coeffs)) % prime == 0]
    for key, prime, fn in [
        ("quadratic_11_roots",11,lambda x:x*x-5),("quadratic_7_roots",7,lambda x:x*x+3),
        ("quadratic_29_roots",29,lambda x:x*x+1),("quadratic_229_at_29",29,lambda x:x*x-229),
        ("mu3_at_29",29,lambda x:x*x+x+1)]:
        entries[key] = [x for x in range(prime) if fn(x) % prime == 0]
    # Count actual fixed points in all 6 permutations and use the swap average.
    import itertools
    perms = list(itertools.permutations(range(3)))
    identity, swap = (0,1,2),(1,0,2)
    def chars(g):
        fixed = sum(i==v for i,v in enumerate(g))
        inversions = sum(g[i]>g[j] for i in range(3) for j in range(i+1,3))
        return [1, (-1)**inversions, fixed-1, fixed, len(perms) if g==identity else 0]
    entries["fixed_dimensions"] = [(a+b)//2 for a,b in zip(chars(identity),chars(swap))]
    return {name: str(value) for name,value in entries.items()}


if __name__ == "__main__":
    cfg = json.loads((Path(__file__).resolve().parents[1]/"inputs/arithmetic.json").read_text())
    print(json.dumps(calculate(cfg), indent=2, sort_keys=True))

