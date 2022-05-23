import binascii
import math
import hashlib
import time

def r_value(x, y, μ, int_size_bits=1024):
    """Generates the Fiat-Shamir verifier challenges Hash(xi,yi,μi)"""
    int_size = int_size_bits // 8
    s = (x.to_bytes(int_size, "big", signed=False) +
         y.to_bytes(int_size, "big", signed=False) +
         μ.to_bytes(int_size, "big", signed=False))
    b = hashlib.sha256(s).digest()
    return int.from_bytes(b[:16], "big")

def make_checkpoints(τ,s):
    # We're going to store 2^s values:
    # μ1 -> 2^T/2
    # μ2 -> 2^T/4, 2^3T/4
    # μ3 -> 2^T/8, 2^3T/8, 2^5T/8, 2^7T/8
    # μ4 -> 2^T/16, 2^3T/16, 2^5T/16, 2^7T/16, 2^T9/16, 2^11T/16, 2^13T/16, 2^15T/16 etc
    # We store T, T/2, T/4, 3T/4, T/8, 3T/8, 5T/8, 7T/8, .. in ascending order
    checkpoints = []
    denom = 2
    t = τ
    for i in range(1, s):
        t >>= 1
        for j in range(1, denom, 2):
            exp = t*j
            checkpoints.append(exp)
            # checkpoints.append(pow(2, exp))  # This is too slow
        denom <<= 1
    checkpoints.append(τ)
    return checkpoints

def repeated_squarings(N, x, checkpoints):
    """ Repeatedly square x. Caching values at checkpoints.  """
    powers_calculated = {}
    powers = sorted(checkpoints)  # We need checkpoints to remain unsorted
    # Repeatedly square x
    previous_power = 0
    for current_power in powers:
        # Use the speed of pow(x, exp, mod)  between checkpoints
        x = pow(x, pow(2, current_power - previous_power), N)
        powers_calculated[current_power] = x
        previous_power = current_power

    return powers_calculated

def generate_proof(xi, t, δ, yi, N, i, π=[]):
    """  Generate the proof, list of μi values """
    # Halving protocol from Pietrzak p16.
    # μi = xi^(2^(T/2^i))
    # ri = Hash((xi,T/2^(i−1),yi),μi)
    # xi+1 = xi^ri . μi
    # yi+1 = μi^ri . yi

    t = t//2  # or t = int(τ / pow(2, i))
    μi = pow(xi, pow(2, t), N)
    ri = r_value(xi, yi, μi) % N
    xi = (pow(xi, ri, N) * μi) % N
    yi = (pow(μi, ri, N) * yi) % N
    π.append(μi)
    print("Values: T:{}, x{}:{}, y{}:{}, u{}:{}, r{}: {}".format(t, i, xi, i, yi, i, μi, i, ri))

    if t == pow(2, δ):
        xi_delta = pow(xi, pow(2, pow(2, δ)), N)
        if xi_delta == yi:
            print("Match Last (x{})^2^2^{} {} = y{}: {}".format(i, δ, xi_delta, i, yi))
            return π
        else:
            print("Proof incomplete.")
            return

    return generate_proof(xi, t, δ, yi, N, i+1, π)

def generate_optimized_proof(xi, t, δ, yi, s, checkpoints, powers, N, i=1, π=[], r=[], factors=[1]):
    """  Generate the proof, list of μi values """
    # In this recursion, we accumulate proofs in π, and r[i]
    t >>= 1  # or t = int(τ / pow(2, i)) , or t = t//2
    # μ1 -> 1                                              T/2
    # μ2 -> r1, 1                                          T/4, 3T/4
    # μ3 -> r2 r1, r1, r2, 1                               T/8, 3T/8, 5T/8, 7T/8
    # μ4 -> r3 r2 r1, r2 r1, r3 r1, r1, r3 r2, r2, r3, 1   T/16, 3T/16, 5T/16, 7T/16, 9T/16, 11T/16, 13T/16, 15T/16
    # Each new level multiplies the previous series and interleaves it. Instead of
    # re-computing the values we're going to pass them down to the next level:
    # Given the last ri, we can take the factors, multiply and interleave them
    if len(r) != 0:
        last_ri = r[-1]
        xfactors = list(map(lambda f: f * last_ri, factors))
        # terms = [];  for pair in zip(xs, rs): ;  for val in pair: terms.append(val)
        new_factors = [val for pair in zip(xfactors, factors) for val in pair]
    else:
        new_factors = factors

    # Now do the combining of powers[checkpoint[i]] ^ new_factors[i]
    f = len(new_factors)
    μi = 1
    for i in range(f):
        μi *= pow(powers[checkpoints[i]], new_factors[i], N)
        μi %= N

    # We don't need the first f values in checkpoints anymore, pop them
    for i in range(f):
        checkpoints.pop(0)

    ri = r_value(xi, yi, μi) % N
    xi = (pow(xi, ri, N) * μi) % N
    yi = (pow(μi, ri, N) * yi) % N

    π.append(μi)
    r.append(ri)
    print("Values: T:{}, x{}:{}, y{}:{}, u{}:{}, r{}: {}".format(t, i, xi, i, yi, i, μi, i, ri))

    if t == pow(2, δ):
        xi_delta = pow(xi, pow(2, pow(2, δ)), N)
        if xi_delta == yi:
            print("Match Last (x{})^2^2^{} {} = y{}: {}".format(i, δ, xi_delta, i, yi))
            return π
        else:
            print("Proof incomplete.")
            return

    # Once we run out of checkpoints, we need to jump to the unoptimized proof algo
    if len(checkpoints) == 0:
        return generate_proof(xi, t, δ, yi, N, i + 1, π)

    return generate_optimized_proof(xi, t, δ, yi, s, checkpoints, powers, N, i+1, π, r, new_factors)

def optimized_proof(N, x, τ, δ, s):
    # Prep the cache for intermediate values Pietrzak p18 or Boneh p5.
    start_t = time.time() * 1000
    checkpoints = make_checkpoints(τ, s)
    print("Finished checkpoints in ", round(((time.time() * 1000) - start_t), 2), "ms")

    start_t = time.time() * 1000
    # Compute x^(2^τ) mod N , caching checkpoint values along the way
    powers = repeated_squarings(N, x, checkpoints)
    print("Finished squarings in ", round(((time.time() * 1000) - start_t), 2), "ms")
    checkpoints.pop()  # We won't need τ in the checkpoints anymore

    start_t = time.time() * 1000
    y = powers[τ]
    π = generate_optimized_proof(x, τ, δ, y, s, checkpoints, powers, N)
    print("Finished proof in ", round(((time.time() * 1000) - start_t), 2), "ms")
    return y, π

def verify_proof(xi, yi, π, τ, δ):
    """ Verify proof """
    # Verify algo from Pietrzak p16.
    # ri := hash((xi,T/^2i−1,yi), μi)
    # xi+1 := xi^ri . μi
    # yi+1 := μi^ri . yi

    μi = π.pop(0)
    ri = r_value(xi, yi, μi) % N
    xi = (pow(xi, ri, N) * μi) % N
    yi = (pow(μi, ri, N) * yi) % N
    # yt+1 ?= (xt+1)^2
    if yi == pow(xi,pow(2, pow(2, δ)),N):
        return True

    return verify_proof(xi, yi, π, τ, δ)


if __name__ == '__main__':
    print('This illustrates the Pietrzak Optimized VDF')
    # primes.rwh_primes1(123456789123456789)
    # Pick two of them.
    p = 123456211
    q = 123384263
    # p,q Need to be safe primes. p = 2p′+1 and q = 2q′ +1
    # i.e. p′ = (p −1)/2 and q′ = (q −1)/2  also prime


    # t is the number of bits in τ=2^t
    t = 28  # 28 -> ~ 25 sec
    # Tau
    τ = pow(2, t)
    # Prime Composite N
    N = p * q

    # Some Random value X
    x = pow(509, 23) % N

    print("Values: p:{},q:{} -> N:{}".format(p, q, N))
    print("Values: t:{} -> τ:{}, x:{}".format(t, τ, x))

    # Malicious Solver's VDF takes a while
    # start_t = time.time() * 1000
    # y = pow(x, pow(2, τ), N) % N
    # print("Values: y:{}".format(y))
    # print("Finished y in ", round(((time.time() * 1000) - start_t), 2), "ms")

    # Honest Prover's VDF takes even longer
    start_t = time.time() * 1000
    # Using a δ value makes the verification require a costly xi ^ pow(2,pow(2,δ)) but shortens the proof
    δ = 8
    # According to Boneh, ideal s=log_2(T)/2 see p5, they use (g,h,d,v) instead of (x,y,s,μ). Accounting for δ too.
    s = round((math.log(τ) - δ)/(2*math.log(2)))  # Maybe this doesn't work so well for deep proofs
    print("Delta: δ:{}".format(δ))
    print("Checkpoints: s:{}".format(s))
    y, π = optimized_proof(N, x, τ, δ, s)
    print("Finished total calc+proof in ", round(((time.time() * 1000) - start_t), 2), "ms")
    # Output the proof
    print("Result:", y)
    # Should π=[μi] have Log2(T) elements minus the delta optimization.
    print("Proof:", π)

    # Proof Verification
    start_t = time.time() * 1000
    ok = verify_proof(x, y, π, τ, δ)
    if ok:
        print("Proof is valid. Finished verifying in ", round(((time.time() * 1000) - start_t), 2), "ms")


