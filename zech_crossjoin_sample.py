import debruijn
import random
import sympy

order = 12

# Preparative work -- get a primitive polynomial and construct the m-sequence
p = debruijn.generate_primitives(order, just_one=True)[0]
print 'primitive seed: {}'.format(p.as_expr())
coeff = p.all_coeffs()[:0:-1]  # exclude first element and reverse
state = [1] + [0] * (order - 1)
m_seq = state[:]
while len(m_seq) < (2**order - 1):
    next_bit = sum([j for i, j in enumerate(state) if coeff[i]]) % 2
    m_seq.append(next_bit)
    state = state[1:] + [next_bit]
# print ''.join(['-' if i%5 != 0 else '|' if i%10 != 0 else str(i/10%10) for i in range(min(2**order - 1, 100))])
# print ''.join([v if i%100 != 99 else v + '\n' for i, v in enumerate(map(str, m_seq))])
m_seq += m_seq[:order-1]
m_seq_str = ''.join(map(str, m_seq))

# Write original feedback function
syms = sympy.symbols('x_:{}'.format(order), integer=True)
func = sum([sym for i, sym in enumerate(syms) if coeff[i]])

# Use searching to construct Zech's log table
zlog = [None] * (2**order - 1)
for i in range(1, 2**order - 1):
    if zlog[i] is not None:
        continue
    tau = m_seq_str.rfind(m_seq_str[i+1:i+order]) - 1
    zlog[i], zlog[tau] = tau, i

# Pick random states A, B such that A < B < t(A) < t(B)
while True:
    a, b = random.sample(range(1, 2**order-1), 2)
    a, b = (a, b) if a <= b else (b, a)
    if b < zlog[a] < zlog[b]:
        break

print 'chosen pairs: ({}, {}) <-> ({}, {})'.format(a, b, zlog[a], zlog[b])

# Construct transition matrix
transition = sympy.zeros(order)
for i in range(order-1):
    transition[i+1, i] = 1
for i in range(order):
    transition[i, -1] = coeff[i]

# Get the relevant states
i_state = sympy.Matrix(1, order, [1] + [0]*(order-1))
a_state = map(lambda x: x%2, i_state*transition**a)
b_state = map(lambda x: x%2, i_state*transition**b)

# print list(a_state), list(b_state)

# Compute resulting feedback function
func += reduce(lambda x, y: x*y, map(lambda x, y: x + (1 - y), syms[1:], a_state[1:]))
func += reduce(lambda x, y: x*y, map(lambda x, y: x + (1 - y), syms[1:], b_state[1:]))
func = sympy.Poly(func, modulus=2).as_expr()
print 'resulting feedback function: {}'.format(func)
seq = [1] + [0] * (order-1)
# for i in range(2**order-1 - order):
#     args = zip(syms, seq[-order:])
#     next_bit = int(func.subs(args)) % 2
#     seq += [next_bit]
# print ''.join(['-' if i%5 != 0 else '|' if i%10 != 0 else str(i/10%10) for i in range(min(2**order - 1, 100))])
# print ''.join([v if i%100 != 99 else v + '\n' for i, v in enumerate(map(str, seq))])
