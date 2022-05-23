import binascii
import math
import hashlib
import time

def generate_r_value(x, y, μ, int_size_bits=1024):
    """Generates the Fiat-Shamir verifier challenges Hash(xi,yi,μi)"""
    int_size = int_size_bits // 8
    s = (x.to_bytes(int_size, "big", signed=False) +
         y.to_bytes(int_size, "big", signed=False) +
         μ.to_bytes(int_size, "big", signed=False))
    b = hashlib.sha256(s).digest()
    return int.from_bytes(b[:16], "big")

if __name__ == '__main__':
    print('This illustrates the Pietrzak VDF no proving')
    # primes.rwh_primes1(123456789123456789)
    # Pick two of them.
    # p = 1993,q = 2027
    p = 123456211
    q = 123384263

    φ = (p - 1) * (q - 1)
    # t is the number of bits in τ
    t = 25
    # Tau, must be a power of 2 for the halving protocol to work
    τ = pow(2, t)
    # Prime Composite N
    N = p * q

    # Some Random value X
    x = pow(509, 23) % N

    print("Values: p:{},q:{} -> N:{}".format(p, q, N))
    print("Values: t:{} -> τ:{}, x:{}".format(t, τ, x))

    # Start timer for VDF solving using Totient Function
    start_t = time.time() * 1000
    s = pow(x, pow(2, τ, φ), N)
    print("Solution s:{}".format(s))
    print("Finished s in ", round(((time.time() * 1000) - start_t), 2), "ms")

    # Malicious Solver's VDF takes longer
    start_t = time.time() * 1000
    y = pow(x, pow(2, τ), N) % N
    print("Solution y:{}".format(y))
    print("Finished y in ", round(((time.time() * 1000) - start_t), 2), "ms")
    print()

    # Generate the proof, re-calculate all VDF iterations
    xi = x
    yi = y
    δ = 8    # Using a Delta value makes the verification require a costly xi ^ pow(2,pow(2,δ)) but shortens the proof
    print("Delta: δ:{}".format(δ))
    start_t = time.time() * 1000
    for i in range(1, t+1-δ):
        T = int(τ/pow(2, i))
        ui = pow(xi, pow(2, T), N)
        ri = generate_r_value(xi, yi, ui) % N
        xi = (pow(xi, ri, N)*ui) % N
        yi = (pow(ui, ri, N)*yi) % N
        print("Values: T:{}, x{}:{}, y{}:{}, u{}:{}, r{}: {}".format(T, i, xi, i, yi, i, ui, i, ri))
        if pow(xi, 2, N) == yi:
            print("Match Last (x{})^2: {} = y{}: {}".format(i, pow(xi, 2, N), i, yi))
        if i == t-δ:
            xid = pow(xi,pow(2,pow(2,δ)),N)
            if xid == yi:
                print("Match Last (x{})^2^2^{} {} = y{}: {}".format(i, δ, xid, i, yi))
                print("Finished x^2^2^d in ", round(((time.time() * 1000) - start_t), 2), "ms")
