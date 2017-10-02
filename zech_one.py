import debruijn as db
import sympy
import random
from itertools import product
from time import clock
from math import log
from sympy.abc import x as sym_x
from operator import mul


def LFSR_from_poly(char_poly, state):
    """Return the next state given the characteristic polynomial of a LFSR and a state."""
    lfsr = list(reversed(char_poly.all_coeffs()))[:-1]
    next_state = state + [sum(map(lambda x, y: x & int(y), state, lfsr)) % 2]
    return next_state[1:]


def get_sums(l, s):
    i = 0
    j = len(l) - 1
    l_sort = sorted(l)
    results = []
    cur_sum = l_sort[i] + l_sort[j]
    while i < j:
        if cur_sum == s:
            results.append((l_sort[i], l_sort[j]))
            i += 1
            j -= 1
        elif cur_sum < s:
            i += 1
        else:
            j -= 1
        cur_sum = l_sort[i] + l_sort[j]
    return results


def get_powers(p):
    deg = sympy.degree(p)
    l = []
    for i in range(deg, -1, -1):
        if p.coeff_monomial(sym_x**i):
            l.append(i)
    return l


def high_decimation(p, t, offset=0, c_state=None):
    deg = sympy.degree(p)
    if c_state is None:
        c_state = [1] + [0] * (deg - 1)
    ret = []
    for _ in range(offset):
        c_state = LFSR_from_poly(p, c_state)
    for _ in range(min(2*deg, 2**deg/t)):
        ret += [c_state[0]]
        t_copy = t
        while t_copy > 0:
            c_state = LFSR_from_poly(p, c_state)
            t_copy -= 1
    return ret


def get_big_poly(p, t):
    n = sympy.degree(p)
    d = high_decimation(p, t)
    while len(d) < (2*n):
        d += d

    cd = sympy.Poly(1, sym_x, modulus=2)
    l, m, bd = 0, -1, 1
    for i in range(2*n):
        sub_cd = list(reversed(cd.all_coeffs()))[1:l+1]
        sub_s = list(reversed(d[i-l:i]))
        sub_cd += [0] * (len(sub_s) - len(sub_cd))
        disc = d[i] + sum(map(mul, sub_cd, sub_s))
        if disc % 2 == 1:
            td = cd
            cd += bd * sympy.Poly(sym_x**(i - m), sym_x, modulus=2)
            if l <= i/2:
                l = i + 1 - l
                m = i
                bd = td
    if sympy.degree(cd) == n:
        cd = sympy.Poly(reversed(cd.all_coeffs()), sym_x, modulus=2)
        return cd
    else:
        return None


def zech_test(p, timit=15, write_file=False):
    coeff = get_powers(p)
    deg = sympy.degree(p)
    if write_file:
        f = open('zech_{}-{}.txt'.format(coeff[0], coeff[1]), 'w')
    zech_log = {coeff[1]: coeff[0]}
    additional = [coeff[1]]
    sumstack = []
    lastsec = 0
    from time import clock
    start = clock()
    trying = True
    while trying:
        while clock() - start < timit:
            remsec = int(timit + start - clock() + 1)
            if remsec % 5 == 0 and remsec != lastsec:
                print "{} seconds remaining...".format(remsec)
                lastsec = remsec
            for i in additional:
                if zech_log[i] not in zech_log:
                    zs = (zech_log[i] - i) % (2**deg-1)
                    zsinv = -zs % (2**deg-1)
                    iinv = -i % (2**deg-1)
                    zlinv = -zech_log[i] % (2**deg-1)
                    for j in range(deg):
                        ni = 2**j * i % (2**deg-1)
                        nz = 2**j * zech_log[i] % (2**deg-1)
                        nii = 2**j * iinv % (2**deg-1)
                        nzi = 2**j * zlinv % (2**deg-1)
                        nzs = 2**j * zs % (2**deg-1)
                        nzsi = 2**j * zsinv % (2**deg-1)
                        zech_log[ni] = nz
                        zech_log[nz] = ni
                        zech_log[nii] = nzs
                        zech_log[nzs] = nii
                        zech_log[nzi] = nzsi
                        zech_log[nzsi] = nzi
                        sumstack += [ni, nz, nii, nzi, nzs, nzsi]
            additional = []
            while sumstack:
                i = sumstack.pop()
                c = get_sums(zech_log.keys(), i)
                for x, y in c:
                    sum1 = (zech_log[i] - zech_log[y])%(2**deg-1)
                    sum2 = (zech_log[i] - zech_log[x])%(2**deg-1)
                    if sum1 not in zech_log and sum1 not in additional:
                        zech_log[sum1] = (zech_log[x] + y - zech_log[y])%(2**deg-1)
                        additional.append(sum1)
                        # print "({}, {}) -> t({})".format(i, y, sum1)
                    if sum2 not in zech_log and sum2 not in additional:
                        zech_log[sum2] = (zech_log[y] + x - zech_log[x])%(2**deg-1)
                        additional.append(sum2)
                        # print "({}, {}) -> t({})".format(i, x, sum2)
                    if len(additional) > 1000 or clock() - start >= timit:
                        break
                if len(additional) > 1000 or clock() - start >= timit:
                    break
            if len(zech_log) == 2**deg - 2:
                print "took {} secs to find".format(clock()-start)
                break
            if not additional and clock() - start < timit:
                print "cannot find new zech logs..."
                break
            if clock() - start >= timit:
                print "ran out of time"
                for i in additional:
                    if zech_log[i] not in zech_log:
                        zs = (zech_log[i] - i)%(2**deg-1)
                        zsinv = -zs%(2**deg-1)
                        iinv = -i%(2**deg-1)
                        zlinv = -zech_log[i]%(2**deg-1)
                        zech_log[zech_log[i]] = i
                        zech_log[iinv] = zs
                        zech_log[zs] = iinv
                        zech_log[zlinv] = zsinv
                        zech_log[zsinv] = zlinv
        if clock() - start >= timit or len(zech_log) == 2**deg - 2:
            break
        else:
            print "attempt to find missed zech log..."
            trying = False
            for i in zech_log:
                remsec = int(timit + start - clock() + 1)
                if remsec%5 == 0 and remsec != lastsec:
                    print "{} seconds remaining...".format(remsec)
                    lastsec = remsec
                c = get_sums(zech_log.keys(), i)
                for x, y in c:
                    sum1 = (zech_log[i] - zech_log[y]) % (2**deg-1)
                    sum2 = (zech_log[i] - zech_log[x]) % (2**deg-1)
                    if sum1 not in zech_log and sum1 not in additional:
                        zech_log[sum1] = (zech_log[x] + y - zech_log[y]) % (2**deg-1)
                        additional.append(sum1)
                        print "({}, {}) -> t({})".format(i, y, sum1)
                    if sum2 not in zech_log and sum2 not in additional:
                        zech_log[sum2] = (zech_log[y] + x - zech_log[x]) % (2**deg-1)
                        additional.append(sum2)
                        print "({}, {}) -> t({})".format(i, x, sum2)
                if additional:
                    print "found new zech log(s)!"
                    trying = True
                    break
            if not additional:
                print "no more zech log!"
                print "{} found ({:.7f}%)".format(len(zech_log), len(zech_log)/float(2**deg-2))
    if write_file:
        print "writing to file..."
        from pprint import pprint
        pprint(zech_log, stream=f)
        f.close()
    print "done!"


def zechlog_from_magma_list(p, i):
    import requests
    from lxml import etree
    poly_string = p.as_expr().replace('**', '^')
    uri = "http://magma.maths.usyd.edu.au/xml/calculator.xml"
    m_input = ("P<x>:=PolynomialRing(GF(2));"
               "f := " + poly_string + ";\n"
               "K<w> := ExtensionField<GF(2), x|f>;\n"
               "for i in " + str(i) + " do;\n"
               "    printf \"%o,%o,\", i, ZechLog(K, i);\n"
               "end for;")
    r = requests.post(uri, data={'input': m_input})
    result = etree.fromstring(r.text).xpath('results')[0]
    s = '\n'.join([child.text for child in result if child.tag == 'line' and child.text])[:-1]
    return map(int, s.split(',')[1::2])


def zechlog_from_magma_loop(p, i, e, t):
    import requests
    from lxml import etree
    deg = sympy.degree(p)
    poly_string = p.as_expr().replace('**', '^')
    uri = "http://magma.maths.usyd.edu.au/xml/calculator.xml"
    m_input = ("P<x>:=PolynomialRing(GF(2));\n"
               "f := {};\n".format(poly_string) +
               "K<w> := ExtensionField<GF(2), x|f>;\n"
               "Init := {};\n".format(i) +
               "Goal := {};\n".format(e) +
               "for m := 1 to #Init do\n"
               "    i := Init[m];\n"
               "    if i eq 0 then\n"
               "        i +:= {};\n".format(t) +
               "    end if;\n"
               "    while i lt 2^{}-1 do\n".format(deg) +
               "        z := ZechLog(K, i);\n"
               "        if (z mod {}) eq Goal[m] then;\n".format(t) +
               "            printf \"%o,%o\\n\", i, z;\n"
               "            break;\n"
               "        end if;\n"
               "        i +:= {};\n".format(t) +
               "    end while;\n"
               "end for;\n")
    r = requests.post(uri, data={'input': m_input})
    result = etree.fromstring(r.text).xpath('results')[0]
    s = '\n'.join([child.text for child in result if child.tag == 'line' and child.text])
    return map(lambda x: tuple(map(int, x.split(','))), s.split('\n'))


def get_db_seq(p, t, num_seq=150, print_matrix=False):
    if print_matrix:
        import networkx as nx
        import matplotlib.pyplot as plt

    p.sort(reverse=True)
    if p[-1] != 0 or len(p) != 3:
        raise ValueError("invalid polynomial, must be a trinomial.")
    deg = p[0]
    mid_term = p[1]
    p = sympy.Poly(sum(map(lambda x: sym_x**x, p)), sym_x, modulus=2)

    if (2**deg - 1) % t != 0:
        raise ValueError("invalid t value")

    q = get_big_poly(p, t)

    # if zech-log doesn't exist, create it first
    try:
        f = open("zech_{}-{}.txt".format(deg, mid_term), "r")
    except IOError:
        print "no zech log file, creating one..."
        zech_test(p, write_file=True)
        print
    else:
        f.close()

    #  read from file
    zech_log = {}
    with open("zech_{}-{}.txt".format(deg, mid_term), "r") as f:
        print "reading from file..."
        for line in f:
            z = map(int, line.replace('L', '')[1:-2].split(': '))
            zech_log[z[0]] = z[1]
    print

    print "generating states..."
    states = []
    init_state = get_special_state(p, t)
    for i in range(t):
        s = high_decimation(p, t, offset=i, c_state=init_state)
        s = s[:deg]
        while len(s) < deg:
            s += s
        states.append(s)
    print
    states.append([0] * deg)

    print "calculated states:"
    for i, v in enumerate(states):
        print "{}:  {}".format(i, str(v))
    print

    #  generate adjacency graph from zech log assuming t is valid
    print "generating adjacency graph..."
    adj_graph = sympy.zeros(t + 1)
    adj_dict = {}
    if print_matrix:
        g = nx.Graph()
        g.add_nodes_from(range(t+1))
    for i in zech_log:
        adj_graph[int(i % t), int(zech_log[i] % t)] -= 1
        if i % t not in adj_dict:
            adj_dict[i % t] = {}
        if zech_log[i] % t not in adj_dict[i % t]:
            adj_dict[i % t][zech_log[i] % t] = []
        # 1st shift, 2nd shift
        if print_matrix:
            g.add_edge(i % t, zech_log[i] % t)
        adj_dict[i % t][zech_log[i] % t].append((i/t, zech_log[i]/t))
    print

    adj_dict[t] = {}
    adj_dict[t][0] = [(0, 0)]
    if 0 not in adj_dict:
        adj_dict[0] = {}
    adj_dict[0][t] = [(0, 0)]
    adj_graph[0, t] -= 1
    adj_graph[t, 0] -= 1
    if print_matrix:
        g.add_edge(0, t)
        g.add_edge(t, 0)
    for i in range(t + 1):
        adj_graph[i, i] = 0
        adj_graph[i, i] = -sum(adj_graph[i, :])

    if print_matrix:
        print adj_graph
        node_pos = nx.shell_layout(g)
        nx.draw(g, node_pos)
        nx.draw_networkx_labels(g, node_pos)
        plt.show()

    iserror = False
    if any([adj_graph[i, i] == 0 for i in range(t + 1)]):
        print "WARNING: graph is incomplete!"
        print "missing states:"
        print [i for i in range(t + 1) if adj_graph[i, i] == 0]
        iserror = True

    # this may be expensive
    if not iserror:
        cofactor = adj_graph.cofactor(0, 0)
        if cofactor == 0:
            print "graph is disconnected"
            iserror = True

    # this might not always work
    if iserror:
        ctr = 0
        clusters = []
        bunch = [0]
        queue = [0]
        while True:
            neighbor = []
            if queue[ctr] in adj_dict:
                neighbor = [i for i in adj_dict[queue[ctr]].keys() if i not in queue]
            if neighbor:
                queue += neighbor
                bunch += neighbor
                ctr += 1
            else:
                if ctr == len(queue) - 1:
                    clusters.append(bunch)
                    unreached = [i for i in range(t+1) if i not in queue]
                    if unreached:
                        queue.append(unreached[0])
                        bunch = [queue[-1]]
                    else:
                        break
                ctr += 1
        print "graph clusters:"
        print clusters
        reach_list = [clusters[0]]
        clusters.remove(reach_list[0])
        inits = []
        goals = []
        while clusters:
            s = [random.choice(reach_list), random.choice(clusters)]
            reach_list.append(s[1])
            clusters.remove(s[1])
            inits.append(random.choice(s[0]))
            goals.append(random.choice(s[1]))
            print "connect {} <-> {}".format(s[0], s[1])
        pairs = zechlog_from_magma_loop(p, inits, goals, t)
        for a, b in pairs:
            zech_log[a] = b
            zech_log[b] = a
            adj_graph[int(a % t), int(b % t)] -= 1
            adj_graph[int(b % t), int(a % t)] -= 1
            if a % t not in adj_dict:
                adj_dict[a % t] = {}
            if b % t not in adj_dict[a % t]:
                adj_dict[a % t][b % t] = []
            if b % t not in adj_dict:
                adj_dict[b % t] = {}
            if a % t not in adj_dict[b % t]:
                adj_dict[b % t][a % t] = []
            # 1st shift, 2nd shift
            g.add_edge(a % t, b % t)
            g.add_edge(b % t, a % t)
            adj_dict[a % t][b % t].append((a/t, b/t))
            adj_dict[b % t][a % t].append((b/t, a/t))
        for i in range(t + 1):
            adj_graph[i, i] = 0
            adj_graph[i, i] = -sum(adj_graph[i, :])
        cofactor = adj_graph.cofactor(0, 0)
        if print_matrix:
            print adj_graph
            nx.draw(g, node_pos)
            nx.draw_networkx_labels(g, node_pos)
            plt.show()

    print "graph is connected!"
    print "# de bruijn sequences:\n    {}".format(cofactor)
    print "log2:\n    {}".format(log(cofactor)/log(2))
    print

    print "generating de bruijn sequences..."
    new_graph = adj_graph.applyfunc(lambda x: -1 if x < 0 else x)
    for i in range(new_graph.rows):
        new_graph[i, i] = new_graph[i, i] - sum(new_graph[i, :])
    for tree in db.get_spanning_trees(new_graph):
        print tree
        edge_weights = [len(adj_dict[i][j]) for (i, j) in tree]
        weight_list = [range(w) for w in edge_weights]
        for weight in product(*weight_list):
            start = clock()
            states_set = []
            for w, (i, j) in enumerate(tree):
                cur_state = states[i]
                for _ in range(adj_dict[i][j][weight[w]][0]):
                    cur_state = LFSR_from_poly(q, cur_state)
                states_set.append(cur_state[1:])

            seq = []
            state = [0] * deg
            seq += state

            for _ in range(2**deg - deg):
                if state[1:] in states_set:
                    state = LFSR_from_poly(q, state)
                    state[-1] = 1 - state[-1]
                else:
                    state = LFSR_from_poly(q, state)
                seq.append(state[-1])
                # print "{}\r".format(_ + deg),

            print "".join(map(str, seq))
            print clock() - start
            num_seq -= 1

            if num_seq <= 0:
                break
        if num_seq <= 0:
            break

    print "done!"


def get_special_state(p, t=3):
    deg = sympy.degree(p)
    if (2**deg - 1) % t != 0:
        return
    base = [1] + [0] * (deg - 1)
    base_state = high_decimation(p, t, c_state=base)[:deg]
    ones = []
    init = base[:]
    for i in range(1, deg):
        init[i] = 1
        init[i-1] = 0
        if i % t != 0:
            state = high_decimation(p, t, c_state=init)[:deg]
            ones.append((init[:], state))

    for i in range(2**len(ones)):
        cstate = base_state[:]
        for j in range(len(ones)):
            if i & 2**j != 0:
                cstate = map(int.__add__, cstate, ones[j][1])
        cstate = map(lambda x: x % 2, cstate)
        if cstate == base:
            break

    for j in range(len(ones)):
        if i & 2**j != 0:
            base = map(int.__add__, base, ones[j][0])
        base = map(lambda x: x % 2, base)

    return base
