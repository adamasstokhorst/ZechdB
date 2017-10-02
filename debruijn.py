import argparse
import random
from itertools import chain, combinations, product
from math import log, sqrt
from time import clock
from mathhelper import Poly, degree, LT, quo, rem, to_list
from mathhelper import Matrix, zeros
from mathhelper import gcd, lcm, totient


def powerset(iterable, reverse=True):
    """powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"""
    s = list(iterable)
    if not reverse:
        return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))
    else:
        return chain.from_iterable(combinations(s, r) for r in reversed(range(len(s)+1)))


def random_permutation(iterable, r=None):
    """Random selection from itertools.permutations(iterable, r)"""
    r = len(iterable) if r is None else r
    return random.sample(iterable, r)


def th_sep(a, sep=" "):
    """Return the number as a string with a specified thousand separator."""
    return "{:,}".format(a).replace(",", sep)


# HELPER FUNCTIONS #

def init():
    """Retrieve parameters from command line arguments."""
    parser = argparse.ArgumentParser(description="Calculate the de Bruijn "
                                                 "sequences generated from "
                                                 "members of F_2[X].")
    parser.add_argument("-v", "--verbose", action="store_true",
                        help="increase output verbosity")
    parser.add_argument("-r", "--random", action="store_true",
                        help="pick trees randomly (might alter run time)")
    parser.add_argument("-n", "--no-sequence", action="store_true",
                        help="halts after calculating the number of spanning "
                        "trees")
    parser.add_argument("-o", "--output", type=argparse.FileType("w"),
                        nargs="?", help="saves output to a given file, "
                        "prints to stdout if omitted")
    parser.add_argument("-t", "--tree-num", type=int, nargs="?", help="number "
                        "of sequences to output, defaults to 1024 or the "
                        "total number of trees, whichever is smaller",
                        default=1024)
    parser.add_argument('-R', '--random-uniform', action="store_true",
                        help="generates a sequence, chosen uniformly at "
                        "random amongst all sequences. ignores -n, -r and -t "
                        "if specified")
    parser.add_argument("polys", type=str, nargs="+", help="list of input "
                        "polynomials as a binary string of coefficients, from "
                        "HIGHEST to LOWEST power")
    return parser.parse_args()


def divisors(n, proper=False):
    """Return a list of the divisors of a given number."""
    divs = reduce(list.__add__, [[i, n/i] for i in range(1, int(sqrt(n))+1) if
                  not n%i])
    if divs[-1]**2 == n:
        divs.pop()

    if proper:
        return sorted(divs)[:-1]
    else:
        return sorted(divs)


def get_poly_list(list_):
    """Return a list of polynomials and the sum of their degrees."""
    f = Poly(1, modulus=2)
    sum_degree = 0
    poly_list = []
    found_reduc = False
    found_const = False
    found_dup = False
    for bin_str in list_:
        polynum = int(bin_str, 2)
        p = poly_from_num(polynum)
        if not p.is_irreducible():
            found_reduc = True
        elif p == Poly(1, modulus=2):
            found_const = True
        elif p in poly_list:
            found_dup = True
        else:
            f *= p
            poly_list.append(p)
            sum_degree += int(degree(p))
    if found_reduc:
        print "WARNING: At least one input was reducible."
    if found_const:
        print "WARNING: At least one input was a constant polynomial."
    if found_dup:
        print "WARNING: Multiple entries found."
    return (f, sorted(poly_list, key=lambda x: int(degree(x))), sum_degree)


def hamming_weight(n):
    """Return the Hamming weight of a given integer."""
    return bin(n).count("1")


def poly_from_num(num):
    """Return a polynomial in F_2[X] from the binary representation of
    a given integer."""
    ctr = 0
    p = Poly(0, modulus=2)
    while num > 0:
        if num%2 == 1:
            p += Poly(to_list([ctr]), modulus=2)
        num /= 2
        ctr += 1
    return p


def binreverse(n):
    return int(bin(n)[:1:-1], 2)


def check_primitive(p):
    """Check if a polynomial is primitive in F_2[X]."""
    if not p.is_irreducible():
        return False
    deg_p = int(degree(p))
    for i in [j for j in divisors(2**deg_p-1, proper=True) if j > deg_p]:
        q = Poly(to_list([0,i]), modulus=2)
        if rem(q, p, modulus=2).is_zero():
            return False
    return True


def generate_primitive(deg):
    """Generate all primitive polynomials of a given degree."""
    primitive_poly = []
    for i in range(1, 2**(deg-1)):
        if hamming_weight(i)%2 == 1:
            poly_num = 1 + 2*i + 2**deg
            rev_poly_num = binreverse(poly_num)
            if rev_poly_num >= poly_num:
                p = poly_from_num(poly_num)
                if check_primitive(p):
                    primitive_poly.append(p)
                    if rev_poly_num != poly_num:
                        primitive_poly.append(poly_from_num(rev_poly_num))
    if deg == 1:
        primitive_poly.append(Poly([1,1], modulus=2))
    return sorted(primitive_poly, key=lambda x:x(2))


def generate_primitive_trinom(deg):
    """Generate all primitive polynomials of a given degree."""
    primitive_poly = []
    for i in range(1, (deg + 1)/2):
        if deg % 2 == 1:
            if i % 2 == 1:
                i = deg - i
            if (2 * deg)%i == 0:
                if deg % 8 == 1 or deg % 8 == 7:
                    continue
            else:
                if deg % 8 == 3 or deg % 8 == 5:
                    continue
        else:
            if i % 2 == 0:
                continue
            if deg != 2*i:
                if (deg * i / 2)%4 == 0 or (deg * i / 2)%4 == 1:
                    continue
        poly_num = 1 + 2**i + 2**deg
        rev_poly_num = 1 + 2**(deg - i) + 2**deg
        p = poly_from_num(poly_num)
        if check_primitive(p):
            primitive_poly.append(p)
            if rev_poly_num != poly_num:
                primitive_poly.append(poly_from_num(rev_poly_num))
    return sorted(primitive_poly, key=lambda x:x(2))


def get_associate_poly(poly_list):
    """Return the associated primitive polynomial of a list of
    polynomials."""
    associates = []
    max_degree = max([int(degree(p)) for p in poly_list])
    for i in range(1, max_degree+1):
        poly_sublist = [p for p in poly_list if int(degree(p)) == i]
        if poly_sublist:
            primitive_poly = generate_primitive(i)
            m_seq = []
            for p in primitive_poly:
                seq = [1] * (2**i-1)
                state = [1] * i
                for j in range(i, 2**i-1):
                    state = LFSR_from_poly(p, state)
                    seq[j] = state[-1]
                m_seq.append(seq)
        for p in poly_sublist:
            if check_primitive(p):
                associates.append({"poly":p, "t":1})
            else:
                for j in divisors(2**i-1, proper=True)[1:]:
                    found_associate = False
                    if totient(2**i-1)/totient((2**i-1)/j) <= len(primitive_poly):
                        decimated_seq = map(lambda x: decimate(x, j), m_seq)
                        while len(decimated_seq[0]) < 2*i:
                            for seq in decimated_seq:
                                seq += seq[:min(len(seq), 2*i - len(seq))]
                        for idx, seq in enumerate(decimated_seq):
                            state = seq[:i]
                            cur_seq = state * 2
                            for k in range(i, 2*i):
                                state = LFSR_from_poly(p, state)
                                cur_seq[k] = state[-1]
                            if cur_seq == seq[:2*i]:
                                associates.append({"poly":primitive_poly[idx], "t":j})
                                found_associate = True
                                break
                        if found_associate:
                            break
    return associates


def _get_associate_poly(poly_list):
    """Return the associated primitive polynomial of a list of
    polynomials."""
    associates = []
    max_degree = max([int(degree(p)) for p in poly_list])
    for i in range(1, max_degree+1):
        poly_sublist = [p for p in poly_list if int(degree(p)) == i]
        if poly_sublist:
            primitive_poly = generate_primitive(i)
        for p in poly_sublist:
            if check_primitive(p):
                associates.append({"poly":p, "t":1})
            else:
                for q in primitive_poly:
                    found_associate = False
                    for j in divisors(2**i-1, proper=True):
                        if rem(p(Poly(to_list([j]), modulus=2)), q).is_zero():
                            associates.append({"poly":q, "t":j})
                            found_associate = True
                            break
                    if found_associate:
                        break
    return associates


def LFSR_from_poly(char_poly, state):
    """Return the next state given the characteristic polynomial of a
    LFSR and a state."""
    deg_p = int(degree(char_poly))
    LFSR = zeros(deg_p, 1)
    for i in range(deg_p):
        LFSR[i] = int(char_poly.all_coeffs()[-i-1])
    next_state = state[:] + [(Matrix(1, deg_p, state) * LFSR)[0]%2]
    return next_state[1:]


def get_P_matrix(poly_list):
    """Return the P matrix as specified in the paper."""
    n = sum([int(degree(p)) for p in poly_list])
    P_matrix = zeros(n)
    runsum = 0
    for p in poly_list:
        deg_p = int(degree(p))
        for i in range(deg_p):
            P_matrix[runsum+i, i] = 1
            cur_state = [0] * deg_p
            cur_state[i] = 1
            for j in range(deg_p, n):
                cur_state = LFSR_from_poly(p, cur_state)
                P_matrix[runsum+i, j] = cur_state[-1]
        runsum += deg_p
    return P_matrix


# ALGORITHM 1 #

def _get_base_matrix(p, q, t):
    """Return the basis-conversion matrix between the roots of two
    polynomials."""
    n = int(degree(p))
    M = zeros(n)
    M[0, 0] = 1
    q_trimmed = q - Poly(LT(q), modulus=2)
    cur_poly = Poly(to_list([t]), modulus=2)
    div_poly = Poly(to_list([n]), modulus=2)
    for i in range(1, n):
        while degree(cur_poly) >= n:
            cur_poly = quo(cur_poly, div_poly) * q_trimmed + rem(cur_poly,
                       div_poly)
        for j in range(len(cur_poly.all_coeffs())):
            M[i, j] = cur_poly.all_coeffs()[-j-1]
        cur_poly = cur_poly * Poly(to_list([t]), modulus=2)
    return M.inv_mod(2)


def _get_state(M, p, t):
    """Return the states of a polynomial, given its basis conversion
    matrix."""
    deg_p = int(degree(p))
    state = [1] * (t * deg_p)
    new_p = p - Poly(LT(p), modulus=2)
    cur_poly = Poly(1, modulus=2)
    div_poly = Poly(LT(p), modulus=2)
    for i in range(1, t * deg_p):
        cur_poly *= Poly([0, 1], modulus=2)
        if degree(cur_poly) == deg_p:
            cur_poly = quo(cur_poly, div_poly) * new_p + rem(cur_poly,
                       div_poly)
        coeff = zeros(1, deg_p)
        for j in range(len(cur_poly.all_coeffs())):
            coeff[j] = int(cur_poly.all_coeffs()[-j-1])
        coeff = (coeff * M).applyfunc(lambda x: x%2)
        state[i] = coeff[0]
    v = []
    for i in range(t):
        v.append(state[i::t])
    v.append([0] * deg_p)
    return v


def get_state(q, t):
    deg = degree(q)
    seq = [1] * (2**deg - 1)
    state = [1] * deg
    for i in range(deg, 2**deg-1):
        state = LFSR_from_poly(q, state)
        seq[i] = state[-1]

    states = []
    for i in range(t):
        state = decimate(seq, t, i)
        while len(state) < deg:
            state += state
        states.append(state[:deg])

    states.append([0] * deg)

    return states


def get_cycle(p, states, t):
    """Return the distinct cycles of LFSR with a given characteristic
    polynomial."""
    n = degree(p)
    e = (2**n-1)/t
    cycles = []
    for state in states:
        if e <= n:
            cur_cycle = state[0:e]
        else:
            cur_cycle = [0] * e
            cur_cycle[0:n] = state
            temp_state = state
            for i in range(n, e):
                temp_state = LFSR_from_poly(p, temp_state)
                cur_cycle[i] = temp_state[-1]
        cycles.append(cur_cycle)
    return cycles


# ALGORITHM 2 #


def find_special_state(poly_list, P_matrix, states):
    """Calculate the special state for each state, given the P matrix.
    Return format: (c, d) where T^c a^i_d = special_state for each i.
    """
    n = P_matrix.rows
    special_s = zeros(1, n)
    special_s[0] = 1
    special_s *= P_matrix.inv_mod(2)
    special_state = []
    runsum = 0
    for p in poly_list:
        special_state.append(special_s[runsum:runsum+degree(p)])
        runsum += degree(p)
    special_param = []
    for i, p in enumerate(poly_list):
        t = len(states[i])-1
        e = (2**degree(p) - 1) / t
        found = False
        for j, state in enumerate(states[i]):
            cur_state = state[:]
            for k in range(e):
                if cur_state == special_state[i]:
                    special_param.append({"shift":k, "state":j})
                    found = True
                    break
                cur_state = LFSR_from_poly(p, cur_state)
            if found:
                break
    return special_param


# ALGORITHM 3 #

def find_pairs(p, poly_state, shift, state):
    """Find all pairs between states of a given polynomial such that
    T^l a_j + T^-m a_k = special_state."""
    special_state = list(poly_state[state])
    for i in range(shift):
        special_state = LFSR_from_poly(p, special_state)
    t = len(poly_state)-1
    e = (2**degree(p)-1)/t
    pairs_list = {}
    for j in range(t+1):
        state_j = poly_state[j]
        for k in range(j, t+1):
            ctr = 0
            for l in range(e):
                temp = [(state_j[i] + special_state[i])%2 for i in
                        range(degree(p))]
                for m in range(e):
                    if temp == poly_state[k]:
                        if (j, k) in pairs_list:
                            pairs_list[(j, k)].append((l, -m%e))
                            if j != k:
                                pairs_list[(k, j)].append((-m%e, l))
                        else:
                            pairs_list[(j, k)] = [(l, -m%e)]
                            if j != k:
                                pairs_list[(k, j)] = [(-m%e, l)]
                        ctr += 1
                        break
                    else:
                        temp = LFSR_from_poly(p, temp)
                state_j = LFSR_from_poly(p, state_j)
    return pairs_list


# ALGORITHM 4 #

def pair_generator(poly_list, lists):
    """Generate all combination of pairs as given from find_pairs."""
    if poly_list:
        pairs = lists[0]
        t = max([key[0] for key in pairs])
        e = (2**degree(poly_list[0])-1) / t
        for pair in pairs:
            state_1 = pair[0]
            state_2 = pair[1]
            for shift_pair in pairs[pair]:
                next_list = pair_generator(poly_list[1:], lists[1:])
                ord_1 = e if state_1 != t else 1
                ord_2 = e if state_2 != t else 1
                cur_param = {"order_1": ord_1,
                             "order_2": ord_2,
                             "shift_pair_1": shift_pair[0],
                             "shift_pair_2": shift_pair[1],
                             "state_1": state_1,
                             "state_2": state_2}
                for next_pair in next_list:
                    yield [cur_param] + next_pair
    else:
        yield []


def conjugate_pairs(poly_list, lists):
    """Find all conjugate pairs between all cycles."""
    pairs = pair_generator(poly_list, lists)
    s = len(poly_list)
    for pair in pairs:
        f_list1 = [vj["order_1"] for vj in pair]
        f_list2 = [vj["order_2"] for vj in pair]
        for l_index1 in product(*[range(x) for x in f_list1]):
            for l_index2 in product(*[range(x) for x in f_list2]):
                found = True
                for (i, j) in product(range(s), repeat=2):
                    if gcd(f_list1[i], f_list2[j]) != 1 and i != j:
                        diff_u = (pair[i]["shift_pair_1"] -
                                  pair[j]["shift_pair_1"])
                        diff_v = (pair[i]["shift_pair_2"] -
                                  pair[j]["shift_pair_2"])
                        found &= (diff_u - l_index1[i] + l_index1[j])%gcd(
                                  f_list1[i], f_list2[j]) == 0
                        found &= (diff_v - l_index2[i] + l_index2[j])%gcd(
                                  f_list1[i], f_list2[j]) == 0
                        if not found:
                            break
                if found:
                    yield {"state_1": [vj["state_1"] for vj in pair],
                           "state_2": [vj["state_2"] for vj in pair],
                           "shift_1": [vj["shift_pair_1"] for vj in pair],
                           "shift_2": [vj["shift_pair_2"] for vj in pair],
                           "f_1": f_list1,
                           "f_2": f_list2}
                    break
            if found:
                break


# SPANNING TREE ALGORITHM #

def get_spanning_trees(M):
    """Initialize the spanning tree generator and return it."""
    d1_index = [i for i in range(M.rows) if M[i, i] == 1]
    if d1_index:
        init_edges = []
        init_verts = []
        for index in d1_index:
            if index not in init_verts:
                n_index = list(M[:, index]).index(-1)
                init_edges.append((index, n_index))
                init_verts += [n_index]
        if RANDOM_MODE:
            init_verts = random_permutation(init_verts)
        else:
            init_verts.sort()
        init_verts = d1_index + init_verts[:1]
        return span_tree_gen(M, init_verts, init_edges, len(d1_index))
    else:
        init_verts = [random.randrange(M.rows)] if RANDOM_MODE else [0]
        return span_tree_gen(M, init_verts)


def span_tree_gen(M, verts_in, edgelist=None, cur_vert=0):
    """Generate and yield all spanning trees of a given graph."""
    if len(edgelist) == M.rows-1:
        yield sorted(edgelist)
    else:
        if edgelist is None:
            edgelist = []
        if cur_vert < len(verts_in):
            neighbor = M[verts_in[cur_vert], :]
            nlist = [i for i, j in enumerate(neighbor) if j == -1 if not i in
                     verts_in]
            if RANDOM_MODE:
                nlist = random_permutation(nlist)
            for vertices in powerset(nlist):
                verts = list(vertices)
                new_edges = [(verts_in[cur_vert], i) for i in verts]
                for next_tree in span_tree_gen(M, verts_in + verts, edgelist +
                                               new_edges, cur_vert + 1):
                    yield next_tree


def sublist_exists(list_, sublist):
    """Determine the existence of a sublist in a given list."""
    for i in range(len(list_)-len(sublist)+1):
        if sublist == list_[i:i+len(sublist)]:
            return True
    return False


def is_dbseq(sequence, order):
    """Determine whether a given sequence is de Bruijn or not."""
    nseq = sequence + sequence[0:order]
    for i in range(2**order):
        n_i = i
        seqcheck = [0] * order
        ctr = 1
        while n_i > 0:
            seqcheck[-ctr] = n_i%2
            n_i /= 2
            ctr += 1
        if not sublist_exists(nseq, seqcheck):
            return False
    return True


def get_seq(polys, n):
    """Return a list of n de Bruijn binary strings from a given list of polynomials as 1-0 strings."""
    F, POLY_LIST, N = get_poly_list(polys)
    s = len(POLY_LIST)

    P = get_P_matrix(POLY_LIST)

    states = []
    assoc_poly = get_associate_poly(POLY_LIST)
    for i, p in enumerate(POLY_LIST):
        #if p == assoc_poly[i]["poly"]:
        #    M = eye(degree(p))
        #else:
        #    M = get_base_matrix(p, assoc_poly[i]["poly"],
        #                        assoc_poly[i]["t"])
        state_i = get_state(assoc_poly[i]["poly"], assoc_poly[i]["t"])
        states.append(state_i)

    special_state = find_special_state(POLY_LIST, P, states)

    pairs_list = []
    for i in range(s):
        pairs = find_pairs(POLY_LIST[i], states[i], **special_state[i])
        pairs_list.append(pairs)

    conjugates = conjugate_pairs(POLY_LIST, pairs_list)
    adjdict = {}

    for pairs in conjugates:
        shift_1 = pairs["shift_1"]
        shift_2 = pairs["shift_2"]
        f_1 = pairs["f_1"]
        f_2 = pairs["f_2"]
        x_list1 = []
        x_list2 = []

        for i in range(s):
            x_list1.append(gcd(f_1[i], lcm(f_1[:i])))
            x_list2.append(gcd(f_2[i], lcm(f_2[:i])))
        eff_li_1 = [(shift_1[i] - shift_1[0])%x_list1[i] for i in range(s)]
        eff_li_2 = [(shift_2[i] - shift_2[0])%x_list2[i] for i in range(s)]
        param_1 = tuple(pairs["state_1"] + eff_li_1)
        param_2 = tuple(pairs["state_2"] + eff_li_2)

        if param_1 != param_2:
            if param_1 not in adjdict:
                adjdict[param_1] = {}
            if param_2 not in adjdict[param_1]:
                adjdict[param_1][param_2] = []
            adjdict[param_1][param_2].append(shift_1)

    perm = range(len(adjdict.keys()))
    ordered_keys = sorted(adjdict.keys(), reverse=True)
    for i, key in enumerate(adjdict):
        perm[i] = ordered_keys.index(key)

    adjmatrix = zeros(len(perm))
    for key in adjdict:
        for inkey in adjdict[key]:
            pos1 = perm[adjdict.keys().index(key)]
            pos2 = perm[adjdict.keys().index(inkey)]
            adjmatrix[pos1, pos2] = -len(adjdict[key][inkey])
    for i in range(adjmatrix.rows):
        adjmatrix[i, i] = -sum(adjmatrix[:, i])
    num_dbseq = int(adjmatrix.cofactor(0, 0))

    adjmatrix = adjmatrix.applyfunc(lambda x: -1 if x < 0 else 0)
    for i in range(adjmatrix.rows):
        adjmatrix[i, i] = -sum(adjmatrix[:, i])

    NUM_TREES = min(n, num_dbseq)
    dbseqs = []

    for tree in get_spanning_trees(adjmatrix):
        edge_weights = [len(adjdict[ordered_keys[i]][ordered_keys[j]])
                        for (i, j) in tree]
        weight_list = [range(w) for w in edge_weights]

        for weight in product(*weight_list):
            states_set = []
            for w, (i, j) in enumerate(tree):
                key1 = ordered_keys[i]
                key2 = ordered_keys[j]
                vstate = []
                cur_state = list(key1)[:s]
                for k in range(s):
                    cur_v = list(states[k][cur_state[k]])
                    for l in range(adjdict[key1][key2][weight[w]][k]):
                        cur_v = LFSR_from_poly(POLY_LIST[k], cur_v)
                    vstate += cur_v
                vstate = (Matrix(1, N, vstate)*P).applyfunc(
                    lambda x: x%2)[:]
                states_set.append(vstate[1:])

            dbseq = []
            initstate = [0] * (N)
            startnum = random.randrange(2**N)
            startnum = bin(startnum)
            for i in range(len(startnum)-2):
                initstate[-i-1] = int(startnum[-i-1])
            dbseq += initstate

            for i in range(2**N - N):
                if initstate[1:] in states_set:
                    initstate = LFSR_from_poly(F, initstate)
                    initstate[-1] = 1 - initstate[-1]
                else:
                    initstate = LFSR_from_poly(F, initstate)
                dbseq.append(initstate[-1])

            dbseqs.append("".join([str(i) for i in dbseq]))
            NUM_TREES -= 1

            if NUM_TREES == 0:
                break
        if NUM_TREES == 0:
            break
    return dbseqs


def decimate(s, t, offset=0):
    ctr = offset
    looped = False
    d_seq = []
    while not looped:
        d_seq.append(s[ctr])
        ctr += t
        ctr %= len(s)
        if ctr == offset:
            looped = True
    return d_seq

# MAIN PROGRAM #

RANDOM_MODE = False

if __name__ == "__main__":
    random.seed()

    params = init()
    VERBOSE = params.verbose
    RANDOM_MODE = params.random
    RAND_UNIFORM = params.random_uniform
    NO_TREES = params.no_sequence
    NUM_TREES = params.tree_num
    OUTFILE = params.output
    POLYS = params.polys
    GLOBAL_TIMER = clock()

    F, POLY_LIST, N = get_poly_list(POLYS)
    s = len(POLY_LIST)

    if VERBOSE:
        print "Received these polynomials:"
        for i, p in enumerate(POLY_LIST):
            print str(i+1) + ":", p
        print

    P = get_P_matrix(POLY_LIST)

    print "Finding associate polynomials..."
    timer = clock()
    states = []
    assoc_poly = get_associate_poly(POLY_LIST)
    for i, p in enumerate(POLY_LIST):
        #if p == assoc_poly[i]["poly"]:
        #    M = eye(degree(p))
        #else:
        #    M = get_base_matrix(p, assoc_poly[i]["poly"],
        #    assoc_poly[i]["t"])
        state_i = get_state(assoc_poly[i]["poly"], assoc_poly[i]["t"])
        states.append(state_i)
    print clock() - timer, "seconds elapsed.\n"

    if VERBOSE:
        print "List of states:"
        for i, state_i in enumerate(states):
            print str(i+1) + ":"
            for single_state in state_i:
                print "  " + str(single_state)
        print

    print "Finding the special state and pairs..."
    timer = clock()
    special_state = find_special_state(POLY_LIST, P, states)

    pairs_list = []
    for i in range(s):
        pairs = find_pairs(POLY_LIST[i], states[i], **special_state[i])
        pairs_list.append(pairs)
    print clock() - timer, "seconds elapsed.\n"

    conjugates = conjugate_pairs(POLY_LIST, pairs_list)
    adjdict = {}
    x_list1 = []
    x_list2 = []
    print "Finding conjugate pairs..."
    timer = clock()

    for pairs in conjugates:
        state_1 = pairs["state_1"]
        state_2 = pairs["state_2"]
        shift_1 = pairs["shift_1"]
        shift_2 = pairs["shift_2"]
        f_1 = pairs["f_1"]
        f_2 = pairs["f_2"]
        x_list1 = []
        x_list2 = []

        for i in range(s):
            x_list1.append(gcd(f_1[i], lcm(f_1[:i])))
            x_list2.append(gcd(f_2[i], lcm(f_2[:i])))
        eff_li_1 = [(shift_1[i] - shift_1[0])%x_list1[i] for i in range(s)]
        eff_li_2 = [(shift_2[i] - shift_2[0])%x_list2[i] for i in range(s)]
        param_1 = tuple(pairs["state_1"] + eff_li_1)
        param_2 = tuple(pairs["state_2"] + eff_li_2)

        if param_1 != param_2:
            if param_1 not in adjdict:
                adjdict[param_1] = {}
            if param_2 not in adjdict[param_1]:
                adjdict[param_1][param_2] = []
            adjdict[param_1][param_2].append(shift_1)

    print clock() - timer, "seconds elapsed.\n"

    perm = range(len(adjdict.keys()))
    ordered_keys = sorted(adjdict.keys(), reverse=True)
    for i, key in enumerate(adjdict):
        perm[i] = ordered_keys.index(key)

    if VERBOSE:
        print "Number of cycles: {}\n".format(len(perm))

    adjmatrix = zeros(len(perm))
    for key in adjdict:
        for inkey in adjdict[key]:
            pos1 = perm[adjdict.keys().index(key)]
            pos2 = perm[adjdict.keys().index(inkey)]
            adjmatrix[pos1, pos2] = -len(adjdict[key][inkey])
    for i in range(adjmatrix.rows):
        adjmatrix[i, i] = -sum(adjmatrix[:, i])
    num_dbseq = int(adjmatrix.cofactor(0, 0))

    if VERBOSE:
        print "Adjacency matrix:"
        print adjmatrix
        print

    if RAND_UNIFORM:
        import sys

        if VERBOSE:
            print "Number of de Bruijn sequences:\n   ", th_sep(num_dbseq)
            print "log2:", log(num_dbseq)/log(2)
            print

        print "Generating a de Bruijn sequence..."
        timer = clock()

        # random walk
        rd = random
        # if it needs to be cryptographically secure...
        # rd = random.SystemRandom()

        d1_index = [i for i in range(adjmatrix.rows) if adjmatrix[i, i] == 1]
        edges = []
        verts = []
        param = []
        if d1_index:
            for index in d1_index:
                if index not in verts:
                    n_index = list(adjmatrix[:, index]).index(-1)
                    edges.append((index, n_index))
                    verts += [n_index]
                    param += adjdict[ordered_keys[index]].items()[0][1]
            verts.sort()
            verts = d1_index + verts[:1]
        else:
            verts += rd.randrange(adjmatrix.rows)
        cur_vert = verts[-1]

        while len(verts) < adjmatrix.rows:
            neighbor = adjmatrix[cur_vert, :]
            nlist = [(i, -j) for i, j in enumerate(neighbor) if j < 0]

            neighbor = []
            for (i, j) in nlist:
                neighbor += [(i, k) for k in range(j)]

            next_vert = rd.choice(neighbor)
            if next_vert[0] not in verts:
                verts.append(next_vert[0])
                edges.append((cur_vert, next_vert[0]))
                param.append(adjdict[ordered_keys[cur_vert]][ordered_keys[
                             next_vert[0]]][next_vert[1]])

            cur_vert = next_vert[0]

        states_set = []
        for w, (i, j) in enumerate(edges):
            key1 = ordered_keys[i]
            key2 = ordered_keys[j]
            vstate = []
            cur_state = list(key1)[:s]
            cur_shift = list(key1)[s:]
            for k in range(s):
                cur_v = list(states[k][cur_state[k]])
                for l in range(param[w][k]):
                    cur_v = LFSR_from_poly(POLY_LIST[k], cur_v)
                vstate += cur_v
            vstate = (Matrix(1, N, vstate)*P).applyfunc(lambda x: x%2)[:]
            states_set.append(vstate[1:])

        dbseq = []
        initstate = [0] * N
        if RANDOM_MODE:
            startnum = random.randrange(2**N)
            startnum = bin(startnum)
            for i in range(len(startnum)-2):
                initstate[-i-1] = int(startnum[-i-1])
        dbseq += initstate

        for i in range(2**N - N):
            if initstate[1:] in states_set:
                initstate = LFSR_from_poly(F, initstate)
                initstate[-1] = 1 - initstate[-1]
            else:
                initstate = LFSR_from_poly(F, initstate)
            dbseq.append(initstate[-1])

        if OUTFILE:
            OUTFILE.write("".join([str(i) for i in dbseq]) + "\n")
            OUTFILE.flush()
        else:
            print " ".join([str(i) for i in dbseq])

        print clock() - timer, "seconds elapsed.\n"

        print clock() - GLOBAL_TIMER, "seconds elapsed in total."

        # too lazy to wrap the rest in an else block
        sys.exit()

    adjmatrix = adjmatrix.applyfunc(lambda x: -1 if x < 0 else 0)
    for i in range(adjmatrix.rows):
        adjmatrix[i, i] = -sum(adjmatrix[:, i])

    num_spanning_tree = int(adjmatrix.cofactor(0, 0))
    if VERBOSE or NO_TREES:
        print "Number of de Bruijn sequences:\n   ", th_sep(num_dbseq)
        print "log2:", log(num_dbseq)/log(2)
        print
        print "Number of spanning trees:\n   ", th_sep(num_spanning_tree)
        print

    if OUTFILE:
        OUTFILE.write(str(num_dbseq) + "\n")

    if not NO_TREES:
        print "Generating de Bruijn sequences..."
        NUM_TREES = min(NUM_TREES, num_dbseq)
        timer = clock()

        for tree in get_spanning_trees(adjmatrix):
            edge_weights = [len(adjdict[ordered_keys[i]][ordered_keys[j]])
                            for (i, j) in tree]
            if RANDOM_MODE:
                weight_list = [random_permutation(range(w)) for w in
                               edge_weights]
            else:
                weight_list = [range(w) for w in edge_weights]

            for weight in product(*weight_list):
                states_set = []
                for w, (i, j) in enumerate(tree):
                    key1 = ordered_keys[i]
                    key2 = ordered_keys[j]
                    vstate = []
                    cur_state = list(key1)[:s]
                    cur_shift = list(key1)[s:]
                    for k in range(s):
                        cur_v = list(states[k][cur_state[k]])
                        for l in range(adjdict[key1][key2][weight[w]][k]):
                            cur_v = LFSR_from_poly(POLY_LIST[k], cur_v)
                        vstate += cur_v
                    vstate = (Matrix(1, N, vstate)*P).applyfunc(
                              lambda x: x%2)[:]
                    states_set.append(vstate[1:])

                dbseq = []
                initstate = [0] * (N)
                if RANDOM_MODE:
                    startnum = random.randrange(2**N)
                    startnum = bin(startnum)
                    for i in range(len(startnum)-2):
                        initstate[-i-1] = int(startnum[-i-1])
                dbseq += initstate

                for i in range(2**N - N):
                    if initstate[1:] in states_set:
                        initstate = LFSR_from_poly(F, initstate)
                        initstate[-1] = 1 - initstate[-1]
                    else:
                        initstate = LFSR_from_poly(F, initstate)
                    dbseq.append(initstate[-1])

                if OUTFILE:
                    OUTFILE.write("".join([str(i) for i in dbseq]) + "\n")
                    OUTFILE.flush()
                else:
                    print " ".join([str(i) for i in dbseq])

                NUM_TREES -= 1
                if NUM_TREES == 0:
                    break
            if NUM_TREES == 0:
                break
        print clock() - timer, "seconds elapsed.\n"

    print clock() - GLOBAL_TIMER, "seconds elapsed in total."
