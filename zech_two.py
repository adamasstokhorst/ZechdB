import sympy
import random
from fractions import gcd
from itertools import product, chain, combinations


def powerset(iterable, reverse=True):
    """powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"""
    s = list(iterable)
    if not reverse:
        return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))
    else:
        return chain.from_iterable(combinations(s, r) for r in reversed(range(len(s)+1)))


def LFSR_from_poly(char_poly, state):
    """Return the next state given the characteristic polynomial of a LFSR and a state."""
    lfsr = list(reversed(char_poly.all_coeffs()))[:-1]
    next_state = state + [sum(map(lambda x, y: x & int(y), state, lfsr)) % 2]
    return next_state[1:]


def seq_decimation(p, t, offset=0, c_state=None):
    """Decimation of a given sequence, making sure not to have a list too big.
    :type p: sympy.Poly
    :type t: int
    :type offset: int
    :type c_state: list[int]
    :rtype: list[int]
    """
    deg = sympy.degree(p)
    if c_state is None:
        c_state = [1] * deg
    ret = [0] * (2*deg)
    for _ in range(offset):
        c_state = LFSR_from_poly(p, c_state)
    indexes = map(lambda x: (x*t) % (2**deg - 1), range(2*deg))
    ctr = 0
    i = 0
    while ctr < 2*deg:
        if i in indexes:
            pos = indexes.index(i)
            ret[pos] = c_state[0]
            indexes[pos] = -1
            ctr += 1
        c_state = LFSR_from_poly(p, c_state)
        i += 1
        if i >= 2**deg - 1:
            i -= 2**deg - 1
    return ret


def poly_decimation(p, t):
    """Decimates polynomial and returns decimated polynomial.
    :type p: sympy.Poly
    :type t: int
    :rtype: sympy.Poly
    """
    from sympy.abc import x
    from operator import mul
    n = sympy.degree(p)
    s = seq_decimation(p, t)
    while len(s) < 2*n:
        s += s

    cd = sympy.Poly(1, x, modulus=2)
    l, m, bd = 0, -1, 1
    for i in range(2*n):
        sub_cd = list(reversed(cd.all_coeffs()))[1:l+1]
        sub_s = list(reversed(s[i-l:i]))
        sub_cd += [0] * (len(sub_s) - len(sub_cd))
        disc = s[i] + sum(map(mul, sub_cd, sub_s))
        if disc % 2 == 1:
            td = cd
            cd += bd * sympy.Poly(x**(i - m), x, modulus=2)
            if l <= i/2:
                l = i + 1 - l
                m = i
                bd = td
    if sympy.degree(cd) == n:
        cd = sympy.Poly(reversed(cd.all_coeffs()), x, modulus=2)
        return cd
    else:
        return None


def zechlog_from_list(p, bl):
    import requests
    from lxml import etree
    poly_string = str(p.as_expr()).replace('**', '^')
    res = []
    for i in range(0, len(bl)/200 + 1 - (len(bl) % 200 == 0)):
        l = bl[i*200:(i+1)*200]
        uri = "http://magma.maths.usyd.edu.au/xml/calculator.xml"
        m_input = ("P<x>:=PolynomialRing(GF(2));\n"
                   "f := {};\n".format(poly_string) +
                   "K<w> := ExtensionField<GF(2), x|f>;\n"
                   "Init := {};\n".format(l) +
                   "for m := 1 to #Init do\n"
                   "    z := ZechLog(K, Init[m]);\n"
                   "    printf \"%o,%o\\n\", Init[m], z;\n"
                   "end for;")
        result = None
        while not result:
            r = requests.post(uri, data={'input': m_input})
            result = etree.fromstring(r.text).xpath('results')
        result = result[0]
        s = '\n'.join([child.text for child in result if child.tag == 'line' and child.text])
        res += map(lambda x: tuple(map(int, x.split(','))), s.split('\n'))
    return res


def get_special_state(p, t):
    from operator import add
    deg = sympy.degree(p)
    if (2**deg - 1) % t != 0:
        return
    base = [1] + [0] * (deg - 1)
    base_state = seq_decimation(p, t, c_state=base)[:deg]
    ones = []
    init = base[:]
    for i in range(1, deg):
        init[i] = 1
        init[i-1] = 0
        if i % t != 0:
            state = seq_decimation(p, t, c_state=init)[:deg]
            ones.append((init[:], state))

    i = 0
    for i in range(2**len(ones)):
        cstate = base_state[:]
        for j in range(len(ones)):
            if i & 2**j != 0:
                cstate = map(add, cstate, ones[j][1])
        cstate = map(lambda x: x % 2, cstate)
        if cstate == base:
            break

    for j in range(len(ones)):
        if i & 2**j != 0:
            base = map(add, base, ones[j][0])
        base = map(lambda x: x % 2, base)

    return base


def get_primitive(n):
    from sympy.abc import x
    import requests
    from lxml import etree
    uri = "http://magma.maths.usyd.edu.au/xml/calculator.xml"
    m_input = ("P<x>:=PolynomialRing(GF(2));\n"
               "p:=PrimitivePolynomial(GF(2), {});\n".format(n) +
               "print p;")
    r = requests.post(uri, data={'input': m_input})
    result = etree.fromstring(r.text).xpath('results')[0]
    s = '\n'.join([child.text for child in result if child.tag == 'line' and child.text])
    return sympy.Poly(eval(s.strip().replace('^', '**')), x, modulus=2)


def get_reps(n, coprime=True):
    # note that each representative represents n-1 other entries
    # so in total there are phi(2**n - 1)
    l = sympy.totient(2**n - 1)/n
    reps = [1]
    p = 2
    while p < 2**n - 1:
        if coprime:
            m = p = sympy.nextprime(p)
        else:
            p += 2
            if p % 2 == 0:
                p -= 1
        if coprime and gcd(p, 2**n - 1) != 1:
            continue
        i = 1
        for i in range(1, n):
            if (p * 2**i) % (2**n - 1) in reps:
                break
            if coprime:
                m = m if (m < (p * 2**i) % (2**n - 1)) else ((p * 2**i) % (2**n - 1))
        if (p * 2**i) % (2**n - 1) in reps:
            continue
        if not coprime:
            m = p
        reps.append(m)
        if len(reps) == l and coprime:
            break
    return sorted(reps)


def populate_zech_log(zech_dict, n):
    k = zech_dict.keys()
    for z in k:
        for i in range(1, n):
            zech_dict[2**i*z % (2**n-1)] = 2**i*zech_dict[z] % (2**n-1)


def get_spanning_trees(mat):
    """Initialize the spanning tree generator and return it."""
    d1_index = [i for i in range(mat.rows) if mat[i, i] == 1]
    if d1_index:
        init_edges = []
        init_verts = []
        for index in d1_index:
            if index not in init_verts:
                n_index = list(mat[:, index]).index(-1)
                init_edges.append((index, n_index))
                init_verts += [n_index]
        else:
            init_verts.sort()
        init_verts = d1_index + init_verts[:1]
        return span_tree_gen(mat, init_verts, init_edges, len(d1_index))
    else:
        init_verts = [0]
        return span_tree_gen(mat, init_verts)


def span_tree_gen(mat, verts_in, edgelist=None, cur_vert=0):
    """Generate and yield all spanning trees of a given graph."""
    if len(edgelist) == mat.rows-1:
        yield sorted(edgelist)
    else:
        if edgelist is None:
            edgelist = []
        if cur_vert < len(verts_in):
            neighbor = mat[verts_in[cur_vert], :]
            nlist = [i for i, j in enumerate(neighbor) if j == -1 if i not in verts_in]
            for vertices in powerset(nlist):
                verts = list(vertices)
                new_edges = [(verts_in[cur_vert], i) for i in verts]
                for next_tree in span_tree_gen(mat, verts_in + verts, edgelist + new_edges, cur_vert + 1):
                    yield next_tree


def get_t_from_magma(q, zr, z):
    # requires new base polynomial, zech representatives, list of zech logs
    import requests
    from lxml import etree
    deg = sympy.degree(q)
    poly_string = str(q.as_expr()).replace('**', '^')
    uri = "http://magma.maths.usyd.edu.au/xml/calculator.xml"
    m_input = ("P<x>:=PolynomialRing(GF(2));\n"
               "f := {};\n".format(poly_string) +
               "K<w> := ExtensionField<GF(2), x|f>;\n"
               "z := ZechLog(K, {});\n".format(zr[0]) +
               "printf \"%o\\n\", z;\n")
    r = requests.post(uri, data={'input': m_input})
    try:
        result = etree.fromstring(r.text).xpath('results')[0]
    except IndexError:
        raise ValueError(r.text)
    s = '\n'.join([child.text for child in result if child.tag == 'line' and child.text])
    target = int(s.strip())
    for t in zr:
        if target * t % (2**deg - 1) == z[zr[0] * t % (2**deg - 1)]:
            return t
    return None


def get_db_seq(p=None, t=None, n=None, t_limit=500, quiet=True, num_seq=None, i_state=None):
    """ wrapper around get_db_seq_bits to emit full de Bruijn sequences. """
    dbs = []
    for b in get_db_seq_bits(p=p, t=t, n=n, t_limit=t_limit, quiet=quiet, i_state=i_state):
        if b is not None:
            dbs.append(b)
        else:
            yield dbs
            if num_seq:
                num_seq -= 1
            if num_seq == 0:
                    break
            dbs = []


def get_db_seq_bits(p=None, t=None, n=None, t_limit=500, quiet=True, i_state=None):
    """ warning: do NOT pass this to list() """
    # prep work
    if not (p or t or n):
        raise ValueError('provide at least n value or polynomial and t value.')

    if n:
        mode = 'DEGREE'
    else:
        if p and t:
            mode = 'POLY'
            n = int(sympy.degree(p, sympy.Symbol('x')))
        else:
            raise ValueError('provide both polynomial and t value.')

    if i_state:
        if len(i_state) == n:
            i_state = map(lambda x: 1 if x != '0' else 0, i_state)
        else:
            i_state = None

    zech_reps = None  # for later use
    sympy.init_printing()

    # get zech data
    try:
        f = open('zech_data_{}.txt'.format(n), 'r')
        coef = map(int, f.readline().split(','))
        primitive = sympy.Poly(coef, sympy.Symbol('x'))
        pairs = []
        for line in f:
            pairs.append(tuple(map(int, line.split(','))))
        f.close()
    except IOError:
        f = open('zech_data_{}.txt'.format(n), 'w')
        primitive = get_primitive(n)
        f.write(','.join(map(str, primitive.all_coeffs())) + '\n')

        zech_reps = get_reps(n, False)
        if 2**n-1 in zech_reps:
            zech_reps.pop()
        pairs = zechlog_from_list(primitive, zech_reps)
        f.write('\n'.join(map(lambda x: ','.join(map(str, list(x))), pairs)))
        f.close()

    zech_0 = {}
    for z1, z2 in pairs:
        zech_0[z1] = z2
        zech_0[z2] = z1
    populate_zech_log(zech_0, n)

    if not quiet:
        print 'original poly: {}'.format(primitive.as_expr())

    if mode == 'DEGREE':
        # choose random primitive
        beta = 1
        while True:
            beta = random.randint(1, 2**n-1)
            if gcd(beta, 2**n-1) == 1:
                break
        while beta % 2 == 0:
            beta /= 2
        if not quiet:
            print 'decimate by {}'.format(beta)
        p = poly_decimation(primitive, beta)
        if not quiet:
            print 'primitive poly: {}'.format(p.as_expr())
    elif mode == 'POLY':
        # sequence method
        if not zech_reps:
            zech_reps = get_reps(n, True)[1:]  # throw away 1
        else:
            zech_reps = [z for z in zech_reps if gcd(z, 2**n - 1) == 1 and z != 1]
        beta = get_t_from_magma(p, zech_reps, zech_0)

    zech = {}
    for k in zech_0:
        zech[k] = zech_0[(k*beta) % (2**n - 1)] * pow(beta, 2**n - 2, 2**n - 1) % (2**n - 1)

    if mode == 'DEGREE':
        # choose random t
        t_candidate = [v for v in sympy.divisors(2**n-1) if 1 < v <= t_limit]
        q = None
        random.shuffle(t_candidate)
        while not q:
            if not t_candidate:
                raise ValueError('no viable t-value available. raise t_limit or use different n.')
            t = t_candidate.pop()
            q = poly_decimation(p, t)
        if not quiet:
            print 'chosen t: {}'.format(t)
    elif mode == 'POLY':
        q = poly_decimation(p, t)
        if not q:
            raise ValueError('t-value not compatible with degree.')

    adj_matrix = sympy.zeros(t+1)
    adj_matrix[0, 0] = adj_matrix[t, t] = 1
    adj_matrix[0, t] = adj_matrix[t, 0] = -1
    adj_dict = {0: {t: [(0, 0)]},
                t: {0: [(0, 0)]}}

    for k in zech:
        l = zech[k]
        adj_matrix[k % t, l % t] -= 1
        if k % t not in adj_dict:
            adj_dict[k % t] = {}
        if l % t not in adj_dict[k % t]:
            adj_dict[k % t][l % t] = []
        adj_dict[k % t][l % t].append((k/t, l/t))
    for i in range(t+1):
        adj_matrix[i, i] -= sum(adj_matrix[i, :])

    if not quiet:
        print "generating states..."
    states = []
    init_state = get_special_state(p, t)
    for i in range(t):
        s = seq_decimation(p, t, offset=i, c_state=init_state)
        s = s[:n]
        while len(s) < n:
            s += s
        states.append(s)
    if not quiet:
        print
    states.append([0] * n)

    if not quiet:
        sympy.pprint(adj_matrix)
        print

    if not quiet:
        print "calculated states:"
        for i, v in enumerate(states):
            print "{}:  {}".format(i, str(v))
        print

    if not quiet:
        print "generating de bruijn sequences..."
    new_graph = adj_matrix.applyfunc(lambda x: -1 if x < 0 else x)
    for i in range(new_graph.rows):
        new_graph[i, i] -= sum(new_graph[i, :])

    if not quiet:
        sympy.pprint(new_graph)

    for tree in get_spanning_trees(new_graph):
        edge_weights = [len(adj_dict[i][j]) for (i, j) in tree]
        weight_list = [range(w) for w in edge_weights]
        for weight in product(*weight_list):
            states_set = []
            for w, (i, j) in enumerate(tree):
                cur_state = states[i]
                for _ in range(adj_dict[i][j][weight[w]][0]):
                    cur_state = LFSR_from_poly(q, cur_state)
                states_set.append(cur_state[1:])

            state = i_state if i_state else map(int, bin(random.randint(0, 2**n-1))[2:].zfill(n))
            for _ in state:
                yield _

            for _ in range(2**n - n):
                if state[1:] in states_set:
                    state = LFSR_from_poly(q, state)
                    state[-1] = 1 - state[-1]
                else:
                    state = LFSR_from_poly(q, state)
                yield state[-1]
            yield None
