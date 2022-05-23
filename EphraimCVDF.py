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
    def __init__(self, x, y, xp, yp, π, parent, level, step_size):
        self.x = x
        self.y = y
        self.children = []
        self.level = level
        self.step_size = step_size
        self.xp = xp
        self.yp = yp
        self.π = π
        self.parent = parent

    def add_child(self, node):
        self.children.append(node)

    def graph_label(self):
        int_size = 128
        s = (self.level.to_bytes(int_size, "big", signed=False) +
             self.x.to_bytes(int_size, "big", signed=False) +
             self.y.to_bytes(int_size, "big", signed=False) +
             self.step_size.to_bytes(int_size, "big", signed=False)
             )
        b = hashlib.sha256(s).digest()
        name = hex(int.from_bytes(b[:16], "big"))
        return name

    def graph_name(self):
        return f"level:{self.level}, step:{self.step_size} \nfrom:{self.x} \nto:{self.y}"

def print_graph(graph, node):
    # Add nodes recursively
    # Node(x, y, xp, yp, π, parent, level, step_size)
    if node.π:
        graph.add_node(pydot.Node(node.graph_label(), label=node.graph_name(), shape="box", color="lightblue"))
    else:
        graph.add_node(pydot.Node(node.graph_label(), label=node.graph_name(), shape="box"))
    for c in node.children:
        print_graph(graph, c)
        if c.π:
            graph.add_edge(pydot.Edge(node.graph_label(), c.graph_label(), color="blue", style="dotted"))
        else:
            graph.add_edge(pydot.Edge(node.graph_label(), c.graph_label(), color="blue"))
    return

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

def CVDF_Prove(N, k, d, x, t, node):
    """ This function makes a proof for segment x at level t """
    # CHeck validity of x
    if math.gcd(x - 1, N) != 1 or math.gcd(x + 1, N) != 1:
        return None
    # # Instead of redoing k**d each time, since this is the only use of d, change the param to k**d
    # if t <= pow(k, d):
    #     assert(False)   ## I don't think we should ever hit this .
    #     return None
    xs = [child.x for child in node.children]
    ys = [child.y for child in node.children]
    (xp, yp) = Sketch(N, xs, ys, t, k)
    return xp, yp

def CVDF_Eval(N, k, d, x, t, node) -> Node:
    # Eval first condition
    if math.gcd(x + 1, N) != 1 or math.gcd(x + 1, N) != 1:
        return None

    # If t <= k**d (node.level < d), complete the node, this should be the single squaring level if d=1
    # We will force the verifier to redo the squaring below depth d
    # TODO Instead of redoing k**d each time, since this is the only use of d, change the param to k**d
    if t <= k**d:
        y = repeated_squaring(N, x, t)
        (node.y, node.xp, node.yp) = (y, 1, 1)
        # Leaf case, always has no proof
        node.π = None
        return node
    else:
        # xi = x^(2^(i*t/k) t increment is t/k
        ti = t//k
        # Add the first child
        child = Node(x=x, y=None, xp=None, yp=None, π=None, parent=node, level=node.level-1, step_size=ti)
        node.children.append(child)
        c = CVDF_Eval(N, k, d, x, ti, child)
        # assert(c == child)    # child assignment should not change

        # Add the other k-1 children
        for i in range(1, k):
            child = Node(x=child.y, y=None, xp=None, yp=None, π=None, parent=node, level=node.level-1, step_size=ti)
            node.children.append(child)
            child = CVDF_Eval(N, k, d, child.x, ti, child)

        # Once all the node's children have been computed finish it
        # node.x = node.children[0].x  # Should do nothing ?
        # node.y = node.children[-1].y
        node.y = child.y

        print(f"Generating Proof node at level {t}  x:{node.x} -> y:{node.y}")
        # Once all segments have been evaluated, produce the proof for this level
        (xp, yp) = CVDF_Prove(N, k, d, x, t, node)
        π = (node.y, (xp, yp))
        sketch = Node(x=x, y=node.y, xp=xp, yp=yp, π=π, parent=node, level=node.level - 1, step_size=ti)
        node.children.append(sketch)
        print(f"Level: x:{x}, t:{t},  Proof:{π}")
        return node

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

    # Malicious Solver's VDF takes a while
    start_t = time.time() * 1000
    y = pow(x0, pow(2, t), N) % N
    print("Solution: y:{}".format(y))
    print("Finished in ", round(((time.time() * 1000) - start_t), 2), "ms")

    # Honest Prover's CVDF
    start_t = time.time() * 1000
    # Public parameters (N,B,k,d,hash)
    print("Public parameters N:{}, k:{}, d:{} ".format(N, k, d))
    # Build the branch down from root to leaf on the first squaring
    root_node = Node(x=x0, y=None, xp=None, yp=None, π=None, parent=None, level=h, step_size=t)
    r = CVDF_Eval(N, k, d, x0, t, root_node)
    assert(r == root_node)

    # Print the tree
    # graph = pydot.Dot("ephraim", graph_type="graph", bgcolor="white")
    graph = pydot.Dot("ephraim", graph_type="graph", bgcolor="white", rankdir="LR")
    print_graph(graph, root_node)
    graph.write_png(f"Ephraim-N:{N},k:{k},d:{d},t:{t}.png")


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

