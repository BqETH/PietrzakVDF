import math
import hashlib
import time
import pydot

def repeated_squaring(N, x, t):
    """ Leaf case t < k^d  """
    y = pow(x, pow(2, t), N)
    print("Squaring from {} to {} by {}".format(x, y, t))
    return y

class Node:
    def __init__(self, x, parent, level, step_size):
        self.x = x
        self.y = None
        self.children = []
        self.level = level
        self.step_size = step_size
        self.xp = None
        self.yp = None
        self.π = None
        self.parent = parent
        self.disabled = False
        self.sketch = False

    def add_child(self, node):
        self.children.append(node)

    def graph_label(self):
        return str(self.__hash__())

    def graph_name(self):
        s = f"level:{self.level}, step:{self.step_size} \nfrom:{self.x} \nto:{self.y}"
        # if self.π:
        #     s += f"\n π:({self.xp},{self.yp})"
        return s

def print_graph(graph, node):
    # Add nodes recursively
    # Node(x, y, xp, yp, π, parent, level, step_size)
    if node.disabled:
        graph.add_node(pydot.Node(node.graph_label(), label=node.graph_name(), shape="box", fontcolor="red"))
    else:
        if node.π:
            graph.add_node(pydot.Node(node.graph_label(), label=node.graph_name(),
                                      shape="box", fontcolor="blue", color="blue"))
        else:
            graph.add_node(pydot.Node(node.graph_label(), label=node.graph_name(), shape="box"))

    for c in node.children:
        print_graph(graph, c)
        if c.π:
            graph.add_edge(pydot.Edge(node.graph_label(), c.graph_label(), color="blue", style="dotted"))
        else:
            graph.add_edge(pydot.Edge(node.graph_label(), c.graph_label(), color="blue"))
    return

def print_tree(N,k,d,t,node):
    root = node
    while root.parent:
        root = root.parent
    graph = pydot.Dot("ephraim", graph_type="graph", bgcolor="white", rankdir="LR")
    print_graph(graph, root)
    graph.write_png(f"Ephraim-N:{N},k:{k},d:{d},t:{t}-{time.time()}.png")

def r_value(N, x, y, t, int_size_bits=1024):
    """Generates the Fiat-Shamir verifier challenges Hash(pp, (x, t), y) """
    int_size = int_size_bits // 8
    s = (N.to_bytes(int_size, "big", signed=False) +
         x.to_bytes(int_size, "big", signed=False) +
         y.to_bytes(int_size, "big", signed=False) +
         t.to_bytes(int_size, "big", signed=False)
         )
    b = hashlib.sha256(s).digest()
    return int.from_bytes(b[:16], "big")

# Sketch is called by both FSProve and FSVerify
def Sketch(N, xs, ys, t, k):
    alpha = [r_value(N, xs[i], ys[i], t) for i in range(k)]
    xprime = 1
    yprime = 1
    # Create x'= Π i=(1->k) (xi-1)^ri , from x0 to x(k-1) or simply (xi)^ri
    # Create y'= Π i=(1->k) (xi)^ri which can be expressed with y terms as (yi)^ri
    for i in range(k):
        xprime *= pow(xs[i], alpha[i], N) % N
        yprime *= pow(ys[i], alpha[i], N) % N
    # print(f"Sketch xs:{xs}, ys:{ys}, k:{k} -> xp:{xp}, yp:{yp}")
    # Return (x', y')
    return xprime, yprime

# From Pietrzak CVDF
# def FSHProver(curve, node):
#     starting_points = [child.initial_point for child in node.children]
#     final_points = [child.final_point for child in node.children]
#     (xprime, yprime) = combine(curve, starting_points, final_points)
#     return xprime, yprime

# def verify(curve, node):
#     if node.xprime == node.yprime == 1:
#         return pietr.verify(T // (k ** (n - node.level - 1)), curve, node.initial_point, node.final_point)
#     status = True
#     for child in node.children:
#         status = status and verify(curve, child)
#         if not status:
#             break
#     if not status:
#         return status
#     else:
#         return FSHVerifier(T // (k ** (n - node.level)), curve, node.xprime, node.yprime)

# def FSHVerifier(depth, curve, xprime, yprime):
#     return pietr.verify(depth, curve, xprime, yprime)


# From Pietrzak unoptimized version
# def verify_proof(xi, yi, π, τ, δ):
#     """ Verify proof """
#     # Verify algo from Pietrzak p16.
#     # ri := hash((xi,T/^2i−1,yi), μi)
#     # xi+1 := xi^ri . μi
#     # yi+1 := μi^ri . yi
#
#     μi = π.pop(0)
#     ri = r_value(xi, yi, μi) % N
#     xi = (pow(xi, ri, N) * μi) % N
#     yi = (pow(μi, ri, N) * yi) % N
#     # yt+1 ?= (xt+1)^2
#     if yi == pow(xi,pow(2, pow(2, δ)),N):
#         return True
#     return verify_proof(xi, yi, π, τ, δ)

# def generate_proof(xi, t, δ, yi, N, i, π=[]):
#     """  Generate the proof, list of μi values """
#     # Halving protocol from Pietrzak p16.
#     # μi = xi^(2^(T/2^i))
#     # ri = Hash((xi,T/2^(i−1),yi),μi)
#     # xi+1 = xi^ri . μi
#     # yi+1 = μi^ri . yi
#
#     t = t//2  # or t = int(τ / pow(2, i))
#     μi = pow(xi, pow(2, t), N)
#     ri = r_value(xi, yi, μi) % N
#     xi = (pow(xi, ri, N) * μi) % N
#     yi = (pow(μi, ri, N) * yi) % N
#     π.append(μi)
#     print("Values: T:{}, x{}:{}, y{}:{}, u{}:{}, r{}: {}".format(t, i, xi, i, yi, i, μi, i, ri))
#
#     if t == pow(2, δ):
#         xi_delta = pow(xi, pow(2, pow(2, δ)), N)
#         if xi_delta == yi:
#             print("Match Last (x{})^2^2^{} {} = y{}: {}".format(i, δ, xi_delta, i, yi))
#             return π
#         else:
#             print("Proof incomplete.")
#             return
#     return generate_proof(xi, t, δ, yi, N, i+1, π)

def CVDF_Prove(N, k, d, x, t, node):
    """ This function makes a proof for segment x at level t """
    # Check validity of x
    if isInvalid(x, N):
        return None
    # # Instead of redoing k**d each time, since this is the only use of d, change the param to k**d
    # if t <= pow(k, d):
    #     assert(False)   ## I don't think we should ever hit this .
    #     return None
    xs = [child.x for child in node.children]
    ys = [child.y for child in node.children]
    (xp, yp) = Sketch(N, xs, ys, t, k)
    return xp, yp

def CVDF_IncrementalEval(N, k, d, squarings, node) -> Node:   # Always returns a leaf

    # Eval first condition
    if isInvalid(x, N):
        return None
    assert(squarings % (k**d) == 0)   ## steps should always be a multiple of k, or 1 if d is 0

    # This is non-recursive, because we always operate at the leaf level, the smallest amount of
    # work is k**d , after which we always have to create one of more sketches
    work = k**d
    while squarings > 0:

        # Is this not the first leaf do node management
        if node.y:
            last_known_y = node.y
            # Travel up to the first parent with less than k children (ignore sketch nodes)
            n = node
            while n.parent and len(n.parent.children) >= k:
                n.parent.y = last_known_y  # propagate result y back up
                n = n.parent         # travel up

            if n.parent:    # just need a new sibling
                node = Node(x=n.y, parent=n.parent, level=n.level, step_size=n.step_size)
                n.parent.add_child(node)
            else:           # Create a new parent
                node = Node(x=n.x, parent=None, level=n.level + 1, step_size=n.step_size * k)
                n.parent = node
                node.add_child(n)

            # Now travel back down to the leaf level creating children
            while node.level > 1:
                c = Node(x=last_known_y, parent=node, level=node.level - 1, step_size=node.step_size // k)
                node.add_child(c)
                node = c            # travel back down

        # Conveniently, 'node' is still the last leaf to compute ;-)

        # Compute the new value
        if squarings <= k**d:   # This node has no result yet, calculate it
            y = repeated_squaring(N, node.x, work)
            (node.y, node.xp, node.yp) = (y, 1, 1)
            # Leaf case, always has no proof
            node.π = None
            last_known_y = y    # For consistency

        # Now travel back up again, and if this is the last segment for any parent, add the sketch
        # Travel up to the first parent with less than k children (ignore sketch nodes)
        n = node
        while n.parent and len(n.parent.children) == k:
            pa = n.parent           # working with the parent
            pa.y = n.y     # propagate result y back up
            print(f"Generating Sketch node at level {pa.step_size}  x:{pa.x} -> y:{pa.y}")
            # Once all segments have been evaluated, produce the proof for this level
            (xp, yp) = CVDF_Prove(N, k, d, pa.x, pa.step_size, pa)
            π = (pa.y, (xp, yp))
            sketch = Node(x=pa.x, parent=pa, level=n.level, step_size=n.step_size)
            sketch.y = pa.y
            sketch.xp = xp
            sketch.yp = yp
            sketch.sketch = True
            sketch.π = π
            pa.children.append(sketch)
            print(f"Level: x:{pa.x} -> y:{pa.y} t:{pa.step_size} Proof:{pa.π}")
            # This is the proof merging stuff, so prune children we don't need
            for c in pa.children:
                for d in c.children:
                    d.disabled = True
            n = n.parent            # travel up

        # Decrement the count
        squarings -= work
        # while-loop

    # Always returns the complete last leaf (node.y is only None for the first leaf)
    return node

def isInvalid(x,N):
    return math.gcd(x - 1, N) != 1 or math.gcd(x + 1, N) != 1

# def collect_proof(proof, node):
#     # collect proof nodes, should only be one per level
#     if node.sketch and not node.disabled:
#         proof.append(node.π)
#     for c in node.children:
#         collect_proof(proof, c)
#
# def extract_proof(leaf):
#     root = leaf
#     while root.parent:
#         root = root.parent
#     proof = []
#     collect_proof(proof, root)
#     return proof

def main():
    # p,q Need to be safe primes. p = 2p′+1 and q = 2q′ +1
    # i.e. p′ = (p −1)/2 and q′ = (q −1)/2  also prime
    # This will imply there might be up to 4 square roots.
    p = 123456211
    q = 123384263
    # Prime Composite N
    N = p * q
    # Some Random value X
    x0 = pow(509, 23) % N

    # Number of segments k (should be 112 for k(λ) linear in λ ) k=2 for Pietrzak
    λ = 112
    # k should be a power of 2
    k = 42  # Testing with 2
    t = pow(k, 17)  # multiple of k for now
    h = int(math.log(t)/math.log(k))+1
    # Ephraim Tree is of depth d : Log_k(T)+1
    # Ephraim: We can truncate the tree. p10 d=d(λ)=λ/32 ->
    d = λ // 32

    # # This is the basic Pietrzak tree with sketch ===========
    # d = 0
    # k = 2  # 2
    # t = pow(2, 4)  # 32
    # h = int(math.log(t) / math.log(k)) + 1

    # Testing overrides ====================================
    d = 0
    k = 2  # 2
    t = pow(2, 4)  # 32
    h = int(math.log(t) / math.log(k)) + 1

    # This is the security check that x is a square root mod N
    assert (math.gcd(x0 - 1, N) == 1)
    assert (math.gcd(x0 + 1, N) == 1)
    print("Values: p:{},q:{} -> N:{}".format(p, q, N))
    print("Values: t:{}, x:{}".format(t, x0))

    # Malicious Solver's VDF takes a short time
    start_t = time.time() * 1000
    y = pow(x0, pow(2, t), N) % N
    print("Solution: y:{}".format(y))
    print("Finished in ", round(((time.time() * 1000) - start_t), 2), "ms")

    # Honest Prover's CVDF
    start_t = time.time() * 1000
    # Public parameters (N,B,k,d,hash)
    print("Public parameters N:{}, k:{}, d:{} ".format(N, k, d))

    # Incremental Version, build the tree bottom-up, first tree is a leaf, add parents as needed
    leaf = Node(x=x0, parent=None, level=1, step_size=1)
    step = k**d
    for _ in range(0, t, step):
        leaf = CVDF_IncrementalEval(N, k, d, step, leaf)
        print_tree(N, k, d, t, leaf)
        # proof = extract_proof(leaf)
        # print(f"Proof {proof}")

    # Evaluate, then generate the final proof , which should have (k-1)^2 Log_k(T)^2 elements
    # print(f"Proof should have {pow(k-1,2)*pow(h-1,2)} elements.")
    print("Finished total calc+proof in ", round(((time.time() * 1000) - start_t), 2), "ms")

    # print("Verifying final proof --- Step")
    # if CVDF_FSVerify(N, k, cutoff, x0, mp, y, π):
    #     print("Valid intermediate Proof")
    # else:
    #     print("Invalid intermediate proof")
    #
    # (y, π) = CVDF_Resume(N, k, cutoff, mp, t, y, π)
    # if CVDF_FSVerify(N, k, cutoff, mp, t, y, π):
    #     print("Valid last Proof")
    # else:
    #     print("Invalid last proof")

if __name__ == '__main__':
    print('This illustrates the Ephraim Continuous Verifiable Delay Function')
    main()

