# Math helper functions and classes for use with debruijn.py
# WARNING: may not be fool-proof, may not suit your usage
# Last updated: 2016-12-21

def sgn(a):
    """Signum function."""
    return 1 if a > 0 else -1 if a < 0 else 0

def get_prime(n):
    """Return primes up to n."""
    if n < 2:
        return []
    prime = [True] * (n+1)
    prime[0] = False
    prime[1] = False
    for i in range(2, int(n**0.5)+1):
        if prime[i]:
            for j in range(2, n/i+1):
                prime[i*j] = False
    return [i for i, j in enumerate(prime) if j]

def get_prime_factor(n):
    """Return list of prime factors of n."""
    p_list = get_prime(n)
    return [p for p in p_list if n%p==0]

def get_factorization(n):
    """Return list of prime factors of n as well as their multiplicities."""
    p_list = get_prime_factor(n)
    factors = []
    for p in p_list:
        i = 0
        while n%p == 0:
            n /= p
            i += 1
        factors.append((p, i))
    return factors

def totient(n):
    for p in get_prime_factor(n):
        n /= p
        n *= (p-1)
    return n

def factor_str(n):
    """Return factorization of n as a human-readable string."""
    s = []
    for p, i in get_factorization(n):
        if i == 1:
            s.append(str(p))
        else:
            s.append("{}**{}".format(p, i))
    return " . ".join(s)

def _gcd(a, b, extended=False):
    """Extended Euclidean algorithm."""
    s0 = 1; s1 = 0
    t0 = 0; t1 = 1
    swapped = False
    if type(a) is int or type(a) is long:
        sga = sgn(a); sgb = sgn(b)
        a = abs(a); b = abs(b)
    else:
        sga = 1; sgb = 1
    if b == 0:
        if extended:
            return (None, None, a)
        else:
            return a
    if a == 0:
        if extended:
            return (None, None, b)
        else:
            return b
    if type(a) is int or type(a) is long:
        if b > a:
            tmp = b
            b = a
            a = tmp
            swapped = True
        while b != 0:
            q = a/b
            tmp = b; b = a%b; a = tmp
            tmp = s1; s1 = s0 - q*s1; s0 = tmp
            tmp = t1; t1 = t0 - q*t1; t0 = tmp
        if extended:
            if swapped:
                return (t0*sgb, s0*sga, a)
            else:
                return (s0*sga, t0*sgb, a)
        else:
            return a
    else:
        if degree(b) > degree(a):
            tmp = b
            b = a
            a = tmp
            swapped = True
        while not b.is_zero():
            q = quo(a,b)
            tmp = b; b = rem(a,b); a = tmp
            tmp = s1; s1 = s0 - q*s1; s0 = tmp
            tmp = t1; t1 = t0 - q*t1; t0 = tmp
        if extended:
            if swapped:
                return (t0*sgb, s0*sga, a)
            else:
                return (s0*sga, t0*sgb, a)
        else:
            return a

def gcd(*s):
    """Greatest common divisor function."""
    if len(s) > 1:
        return reduce(_gcd, s)
    elif len(s) == 0:
        return 0
    elif type(s[0]) is int or type(s[0]) is long:
        return s[0]
    elif not s[0]:
        return 0
    else:
        return reduce(_gcd, s[0])

def lcm(*s):
    """Least common multiple function."""
    if len(s) > 1:
        return reduce(lambda x, y: x*y, s)/gcd(s)
    elif len(s) == 0:
        return 1
    elif type(s[0]) is int or type(s[0]) is long:
        return s[0]
    elif not s[0]:
        return 1
    elif len(s[0]) == 1:
        return s[0][0]
    else:
        return reduce(lambda x, y: x*y, s[0])/gcd(s[0])

class Poly:
    """Simulates standard polynomials."""

    def __init__(self, args, modulus=0):
        if type(args) is int or type(args) is long:
            self._coeffs = [args]
            self.modulus = abs(modulus)
        elif isinstance(args, Poly):
            self._coeffs = args._coeffs[:]
            self.modulus = args.modulus
        else:
            if not args:
                self._coeffs = [0]
            else:
                self._coeffs = list(args)
            self.modulus = abs(modulus)
        self._applymod()

    def __str__(self):
        s = []
        for i, c in enumerate(self._coeffs):
            deg = degree(self)
            sg = '+' if c >=0 else '-'
            cs = str(abs(c)) if abs(c) != 1 else ''
            if deg == 0:
                return str(c)
            elif c != 0:
                if i == 0:
                    if i < deg:
                        s.append([sg, str(abs(c))])
                    else:
                        s.append([str(c)])
                elif i == 1:
                    if i < deg:
                        s.append([sg, cs + 'x'])
                    else:
                        s.append([cs + 'x'] if sg == '+' else [sg + cs + 'x'])
                elif i == deg:
                    if sg == '+':
                        s.append([cs + 'x**' + str(i)])
                    else:
                        s.append(['-' + cs + 'x**' + str(i)])
                else:
                    s.append([sg, cs + 'x**' + str(i)])
        s.reverse()
        return ' '.join(reduce(lambda x, y: x+y, s))

    def __repr__(self):
        return self.__str__()

    def _applymod(self):
        if self.modulus != 0:
            self._coeffs = [x%self.modulus for x in self._coeffs]
        self._cleanup()

    def _cleanup(self):
        while self._coeffs[-1] == 0 and len(self._coeffs) > 1:
            self._coeffs.pop()

    def __add__(self, other):
        if type(other) is int or type(other) is long:
            res = Poly(self)
            res._coeffs[0] += other
        else:
            if degree(self) > degree(other):
                res = Poly(self)
            else:
                res = Poly(other)
            for i in range(min(degree(self), degree(other))+1):
                res._coeffs[i] = self._coeffs[i] + other._coeffs[i]
        res._applymod()
        return res

    def __radd__(self, other):
        return self + other

    def __neg__(self):
        res = Poly(self)
        res._coeffs = [-x for x in res._coeffs]
        res._applymod()
        return res

    def __sub__(self, other):
        return self + (-other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if type(other) is int:
            res = Poly(self)
            res._coeffs = [x * other for x in res._coeffs]
        else:
            coeff = []
            for i in range(degree(self) + degree(other) + 1):
                sum = 0
                for j in range(min(i, degree(self))+1):
                    if (i-j) <= degree(other):
                        sum += self._coeffs[j] * other._coeffs[i-j]
                coeff.append(sum)
            if self.modulus == other.modulus:
                res = Poly(coeff, modulus=self.modulus)
            else:
                res = Poly(coeff)
        res._applymod()
        return res

    def __rmul__(self, other):
        return self * other

    def __pow__(self, other):
        if type(other) is not int:
            raise TypeError('Unsupported type for exponent.')
        else:
            if other == 0:
                return Poly(1, modulus=self.modulus)
            elif other == 1:
                return self
            elif other%2 == 0:
                return self**(other/2) * self**(other/2)
            else:
                return self * self**(other/2) * self**(other/2)

    def __call__(self, arg):
        sum = self._coeffs[0]
        for i in range(degree(self)):
            sum += self._coeffs[i+1] * arg**(i+1)
        return sum

    def is_zero(self):
        return degree(self) == 0 and self._coeffs[0] == 0

    def is_irreducible(self):
        # only works for prime modulus
        d = degree(self)
        check = Poly(to_list([2**d]), modulus=self.modulus)
        check -= Poly([0, 1], modulus=self.modulus)
        if not rem(check, self).is_zero():
            return False
        for q in get_prime_factor(d):
            check = Poly(to_list([2**(d/q)]), modulus=self.modulus)
            check -= Poly([0, 1], modulus=self.modulus)
            if not (gcd(check, self) - 1).is_zero():
                return False
        return True

    def all_coeffs(self, reverse=False):
        return self._coeffs if reverse else list(reversed(self._coeffs))

def LT(self):
    res = Poly(self)
    res._coeffs = [0 if i != degree(self) else x for i, x in enumerate(
                   res._coeffs)]
    return res

def degree(p):
    if type(p) is int or type(p) is long:
        return 0
    else:
        return len(p._coeffs) - 1

def div(p, q, modulus=None):
    if modulus is None:
        mod = p.modulus if p.modulus == q.modulus else 0
    else:
        mod = modulus

    if mod != 2:
        raise NotImplementedError('Modulus other than 2 not implemented yet.')
    if degree(p) < degree(q):
        return (Poly(0, mod), p)
    else:
        r = p._coeffs[:]
        for i in range(degree(p), degree(q)-1, -1):
            if r[i]%mod == 1:
                for j in range(degree(q)):
                    r[i-j-1] += q._coeffs[-2-j]
        return (Poly(r[degree(q):], modulus=2), Poly(r[:degree(q)], modulus=2))

def quo(p, q, modulus=None):
    if modulus is None:
        mod = p.modulus if p.modulus == q.modulus else 0
    else:
        mod = modulus
    return div(p, q, modulus=mod)[0]

def rem(p, q, modulus=None):
    if modulus is None:
        mod = p.modulus if p.modulus == q.modulus else 0
    else:
        mod = modulus
    return div(p, q, modulus=mod)[1]

def to_list(s):
    m = max(s)
    coef = [0] * (m+1)
    for e in s:
        coef[e] += 1
    return coef

class Matrix:
    """Simulates standard 2-dimensional matrices."""

    def __init__(self, *args):
        # Matrix(2, 3, [1, 2, 3, 4, 5, 6])
        if len(args) == 3:
            if len(args[2]) == args[0]*args[1]:
                self.rows = args[0]
                self.cols = args[1]
                self._matrix = [args[2][self.cols*i:self.cols*(i+1)] for i in
                                range(self.rows)]

            else:
                raise ValueError('List length should be equal to rows*columns')
        else:
            raise TypeError('Expected 3 arguments (' + str(len(args)) +
                            ' given)')

    def __str__(self):
        MAX_WIDTH = 79
        lenmatrix = self.applyfunc(lambda x: len(str(x)))
        lenmatrix.transpose()
        maxlens = max([max(_) for _ in lenmatrix._matrix])
        strs = ['[ '] * self.rows
        for i in range(self.rows):
            for j in range(self.cols):
                if len(strs[i])%MAX_WIDTH > (len(strs[i])+maxlens)%MAX_WIDTH:
                    strs[i] += ' ' * (-len(strs[i])%MAX_WIDTH + 1)
                strs[i] += ' ' * (maxlens - lenmatrix[j,i])
                strs[i] += str(self._matrix[i][j]) + ' '
            strs[i] += ']'
        res = ''
        for i in range(-(-len(strs[0])/MAX_WIDTH)):
            for k, j in enumerate(strs):
                res += j[i*MAX_WIDTH:(i+1)*MAX_WIDTH]
                if k != len(strs) - 1 or i < -(-len(strs[0])/MAX_WIDTH+1):
                    res += '\n'
        return res

    def __getitem__(self, key):
        if type(key) is int or type(key) is slice:
            return reduce(lambda x, y: x+y, self._matrix)[key]
        elif len(key) == 2:
            if type(key[0]) is int:
                sliced = self._matrix[key[0]][key[1]]
                r = 1
            elif type(key[0]) is slice:
                sliced = [self._matrix[i][key[1]] for i in range(
                          *key[0].indices(self.rows))]
                if type(sliced[0]) is list:
                    sliced = reduce(lambda x, y: x+y, sliced)
                r = len(range(*key[0].indices(self.rows)))
            else:
                raise TypeError('Invalid index to matrix')

            if type(key[1]) is int:
                c = 1
            else:
                c = len(range(*key[1].indices(self.cols)))

            if r == 1 and c == 1:
                if type(key[0]) is int and type(key[1]) is int:
                    return sliced
                else:
                    return Matrix(r, c, sliced)
            else:
                return Matrix(r, c, sliced)
        else:
            raise TypeError('Invalid index to matrix')

    def __setitem__(self, key, value):
        if type(key) is int:
            self._matrix[key/self.cols][key%self.cols] = value
        elif len(key) == 2:
            self._matrix[key[0]][key[1]] = value
        else:
            raise TypeError('Invalid index to matrix')

    def __iter__(self):
        return iter(reduce(lambda x, y: x+y, self._matrix))

    def __add__(self, other):
        if type(other) is int:
            return self.applyfunc(lambda x: x+other)
        elif isinstance(other, Matrix):
            if self.cols != other.cols or self.rows != other.rows:
                raise ValueError('Matrix size mismatch')
            else:
                new_matrix = zeros(self.rows, self.cols)
                for i in range(self.rows):
                    for j in range(self.cols):
                        new_matrix[i, j] = self[i, j] + other[i, j]
                return new_matrix
        else:
            raise TypeError('Invalid other operand')

    def __radd__(self, other):
        return self+other

    def __mul__(self, other):
        if type(other) is int or type(other) is long:
            return self.applyfunc(lambda x: x*other)
        elif isinstance(other, Matrix):
            if self.cols != other.rows:
                raise ValueError('Matrix size mismatch')
            else:
                new_matrix = zeros(self.rows, other.cols)
                for i in range(self.rows):
                    for j in range(other.cols):
                        new_matrix[i, j] = sum([self[i, k] * other[k, j]
                                               for k in range(self.cols)])
                return new_matrix
        else:
            raise TypeError('Invalid other operand')

    def __rmul__(self, other):
        return self*other

    def __neg__(self):
        return -1*self

    def __pow__(self, power, modulo=None):
        if self.rows != self.cols:
            raise ValueError('Matrix is not a square matrix')
        if power == 0:
            return eye(self.rows)
        if power < 0:
            raise NotImplementedError('Raising to negative power not implemented')
        if power % 2 == 0:
            if modulo is None:
                return self * self
            else:
                return (self * self).applyfunc(lambda x: x % modulo)
        else:
            if modulo is None:
                return self * (self * self)**((power - 1)/2)
            else:
                return (self * (self * self)**((power - 1)/2)).applyfunc(lambda x: x % modulo)

    def transpose(self):
        t = [[self._matrix[i][j] for i in range(self.rows)] for j in
             range(self.cols)]
        swap = self.rows
        self.rows = self.cols
        self.cols = swap
        self._matrix = t

    def applyfunc(self, f):
        res = [f(x) for x in list(self)]
        return Matrix(self.rows, self.cols, res)

    def minor(self, i, j):
        if i > self.rows or j > self.cols or i < 0 or j < 0:
            raise IndexError('Index out of range')
        elif self.rows==1 or self.cols==1:
            return Matrix(0, 0, [])
        else:
            new_matrix = []
            for x in self._matrix:
                new_matrix.append(x[:])
                new_matrix[-1].pop(j)
            new_matrix.pop(i)
            return Matrix(self.rows-1, self.cols-1, reduce(lambda x, y: x+y,
                    new_matrix))

    def det(self):
        if self.rows != self.cols:
            raise ValueError('Matrix is not a square matrix')
        elif self.rows == 0:
            return 1
        else:
            A, N = self, self.rows
            transforms = [0]*(N - 1)

            for n in range(N, 1, -1):
                T, k = zeros(n + 1, n), n - 1

                R, C = -A[k, :k], A[:k, k]
                A, a = A[:k, :k], -A[k, k]

                items = [C]

                for i in range(0, n - 2):
                    items.append(A*items[i])

                for i, B in enumerate(items):
                    items[i] = (R*B)[0, 0]

                items = [1, a] + items

                for i in range(n):
                    for j in range(i, n+1):
                        T[j, i] = items[j - i]

                transforms[k - 1] = T

            polys = [Matrix(2,1,[1, -A[0, 0]])]

            for i, T in enumerate(transforms):
                polys.append(T*polys[i])

            poly = polys[-1]
            return (-1)**(len(list(poly)) - 1)*poly[-1]

    def cofactor(self, i, j):
        if self.rows != self.cols:
            raise ValueError('Matrix is not a square matrix')
        else:
            return (-1) ** ((i+j)%2) * self.minor(i, j).det()

    def cofactorMatrix(self):
        if self.rows != self.cols:
            raise ValueError('Matrix is not a square matrix')
        else:
            entries = []
            for i in range(self.rows):
                for j in range(self.cols):
                    entries.append(self.cofactor(i,j))
            return Matrix(self.rows, self.cols, entries)

    def inv_mod(self, m):
        det_M = self.det()
        x, y, z = _gcd(det_M, m, extended=True)
        if z != 1:
            raise ValueError('Matrix is not invertible modulo ' + str(m))
        else:
            cofac = self.cofactorMatrix()
            cofac.transpose()
            newM = (x * cofac).applyfunc(lambda t: t%m)
            return newM

def zeros(*args):
    """Return zero matrix of given size."""
    if len(args) == 1:
        return Matrix(args[0], args[0], [0] * (args[0]**2))
    elif len(args) == 2:
        return Matrix(args[0], args[1], [0] * (args[0]*args[1]))
    else:
        return TypeError('Expected 1 or 2 arguments (' + len(args) + ' given')

def eye(n):
    """Return identity matrix."""
    entries = []
    for i in range(n-1):
        entries += [1] + [0] * n
    entries += [1]
    return Matrix(n, n, entries)