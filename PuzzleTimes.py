import time
''' This just shows the progression of puzzle times (x^(2^t)) based on the size of t'''

if __name__ == '__main__':
    p=123456211
    q=123384263

    φ = (p-1)*(q-1)
    N = p*q
    x = pow(509, 23) % N

    print("Values: p:{},q:{},N:{}".format(p, q, N))
    print("Values: x:{}".format(x))

    for i in range(1, 32):
        # Start timer
        start_t = time.time() * 1000
        y = pow(x,pow(2, pow(2, i)), N) % N
        print("Finished X^2(^2^", i, ") in ", round(((time.time() * 1000) - start_t), 2), "ms")

