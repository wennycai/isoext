#!/usr/bin/env python3

from sage.all import *
from sage.schemes.elliptic_curves.hom_composite import EllipticCurveHom_composite
from sage.rings.generic import ProductTree
def xDBL(a, b, X1):
    r"""
    Given an x-coordinate X1 = x(P) on the curve y^2 = x^3 + ax + b,
    returns the x-coordinate x([2]P).
    """
    # https://hyperelliptic.org/EFD/g1p/auto-code/shortw/xz/doubling/dbl-2002-it-2.op3
    # simplified using Z1=1
    T1 = X1**2
    T4 = T1-a
    T5 = T4**2
    T8 = b*X1
    T9 = 8*T8
    X3 = T5-T9
    T10 = T1+a
    T11 = X1*T10
    T13 = T11+b
    Z3 = 4*T13
    return X3/Z3

def xADD(a, b, X1, X2, X3):
    r"""
    Given x-coordinates X1 = x(P-Q), X2 = x(P), X3 = x(Q)
    on the curve y^2 = x^3 + a*x + b, returns the x-coordinate x(P+Q)
    """
    if X1:
        # https://hyperelliptic.org/EFD/g1p/auto-code/shortw/xz/diffadd/mdadd-2002-it-3.op3
        # simplified using Z2=Z3=1
        T1 = X2*X3
        T6 = T1-a
        T7 = T6**2
        T9 = 4*b
        T10 = X2+X3
        T11 = T9*T10
        X5 = T7-T11
        T13 = X2-X3
        T14 = T13**2
        Z5 = X1*T14
    else:
        # https://hyperelliptic.org/EFD/g1p/auto-code/shortw/xz/diffadd/mdadd-2002-it-2.op3
        # simplified using Z2=Z3=1
        t2 = X2*X3
        t5 = X2+X3
        t6 = t2+a
        t11 = 4*b
        t12 = t5*t6
        t13 = 2*t12
        R = t13+t11
        t16 = X2-X3
        S = t16**2
        t17 = S*X1
        X5 = R-t17
        Z5 = S
    return X5/Z5

def x_multiples(E, x):
    r"""
    Given an x-coordinate x(P), on the curve E,
    returns all the roots of the kernel polynomial of <P>.
    """
    _,_,_,a,b = E.a_invariants()
    assert E == EllipticCurve([a,b])
    if x is None:
        return []
    xs = [x]
    try:
        x = xDBL(a, b, x)
    except ZeroDivisionError:    # point of order two
#        assert x**3 + a*x + b == 0
        return xs
    while x not in xs[-2:]:
        xs.append(x)
        x = xADD(a, b, xs[-2], xs[-1], xs[0])
    return xs

################################################################

import ast
class _ntl_funs:
    r"""
    An object encapsulating the NTL context for a given finite
    field F, such that polynomials in F[X] can be converted to
    NTL using .ntlify() and minimal polynomials in F[X]/f can
    be computed using .minpoly_mod().
    """
    def __init__(self, F):
        self.ctx = ntl.ZZ_pEContext(ntl.ZZ_pX(F.modulus().list(), F.characteristic()))
        self.F = F
        self.R = F['X']

    def ntlify(self, poly):
        try:
            poly = poly.vector()
        except AttributeError:
            pass
        assert poly.base_ring() == self.F
        return ntl.ZZ_pEX([ntl.ZZ_pE(c.list(), self.ctx) for c in poly])

    def minpoly_mod(self, elt, mod):
        ntl_mod = self.ntlify(mod)
        ntl_elt = self.ntlify(elt) % ntl_mod
        ntl_res = ntl_elt.minpoly_mod(ntl_mod)
        return self.R(ast.literal_eval(str(ntl_res).replace(' ',',')))

@cached_function
def ntl_funs(F2):
    r"""
    Caching helper function to construct the _ntl_funs object
    for a given base field F2 of degree 2 over its prime field.
    """
    assert F2.degree() == 2
    return _ntl_funs(F2)

################################################################
class xPoint:
    r"""
    Class for x-only arithmetic on short Weierstrass curves.
    """
    def __init__(self, X, E):
        k = E.base_field()
        self.X = k(X) if X is not None else None
        self.curve = E

    def __repr__(self):
        return f"Point with X-coordinate {self.X} on {self.curve}"

    def __bool__(self):
        return self.X is not None

    def push(self, isogeny):
        r"""
        Given an isogeny phi (where phi is computed as a composition of isogenies
        computed with Kohel's algorithm), returns phi(self)
        """
        if type(isogeny) is not EllipticCurveHom_composite:
            isogeny = EllipticCurveHom_composite.from_factors([isogeny])

        newX = self.X

        for isopart in isogeny.factors():
            assert isinstance(isopart, EllipticCurveIsogeny)
            assert isopart._EllipticCurveIsogeny__algorithm == 'kohel'

            if (isom := isopart._EllipticCurveIsogeny__pre_isomorphism):
                newX = isom.x_rational_map()(newX)

            phi = isopart._EllipticCurveIsogeny__phi
            psi = isopart._EllipticCurveIsogeny__psi
            try:
                newX = phi(newX) / psi(newX)**2
            except ZeroDivisionError:
                verbose("Point seems to be in the kernel")
                newX = None
                return xPoint(None, isogeny.codomain())

            if (isom := isopart._EllipticCurveIsogeny__post_isomorphism):
                newX = isom.x_rational_map()(newX)

        new_curve = isogeny.codomain().base_extend(newX.parent())
        return xPoint(newX, new_curve)

    def dbl(self):
        r"""
        The x-only doubling map P -> [2]P
        """
        if not self:
            return self
        try:
            X = xDBL(self.curve.a4(), self.curve.a6(), self.X)
        except ZeroDivisionError:
            X = None
        return xPoint(X, self.curve)

    def add(self, other, diff):
        """
        The x-only map (P, Q, P-Q) -> P+Q
        """
        if not self:
            return other
        if not other:
            return self
        if not diff:
            assert self.X == other.X
            return self.dbl()
        assert self.curve == other.curve
        try:
            X = xADD(self.curve.a4(), self.curve.a6(), diff.X, self.X, other.X)
        except ZeroDivisionError:
            X = None
        return xPoint(X, self.curve)

    def mul(self, n):
        """
        Given an integer n, computes [n]self
        """
        n = ZZ(n).abs()
        if n == 0:
            return xPoint(None, self.curve)
        if n == 1:
            return self
        R0, R1, diff = self, self.dbl(), self
        for i in [int(b) for b in bin(n)[3:]]:
            R0pR1 = R0.add(R1, diff)
            diff = R0.add(R1, R0pR1)
            if i == 0:
                R0, R1 = R0.dbl(), R0pR1
            if i == 1:
                R0, R1 = R0pR1, R1.dbl()
        return R0

def kernel_polynomial_from_x(E, x, l):
    """
    Given the x-coordinate x(P), where P has order l,
    returns the kernel polynomial of <P>
    """
    F2 = E.base_field()
    Fbig = x.parent()
    ext = Fbig.over(F2)
    R,X = F2['X'].objgen()

    assert l.is_prime()
    if l <= 3:
        return R([-x, 1])

    try:
        X_in_F2 = F2(x)
    except ValueError:
        pass
    else:
        return prod(X - xx for xx in x_multiples(E, X_in_F2))

    if E.frobenius() not in ZZ:
        raise NotImplementedError

    def minpoly(elt):
        return ntl_funs(F2).minpoly_mod(ext(elt).vector(), ext.modulus())

    #t = cputime()
    fs = [minpoly(x)]
    #t1 = cputime(t)

    k = fs[0].degree()
    m = (l-1) // (2*k)

    #print("The extension degree is", k)
    #print("The order is", l)

    # if k >= 20:
    #     print("The runtime of computing the first minimal polynomial is",t1,"s")
    assert k > 1    # handled above

    from sage.schemes.elliptic_curves.isogeny_small_degree import _least_semi_primitive
    # t = cputime()
    a = _least_semi_primitive(l)
    xi = xPoint(x, E.change_ring(Fbig))
    for _ in range(1, m):
        xi = xi.mul(a)
        fs.append(minpoly(xi.X))
    # t1 = cputime(t)
    # if k >= 20:
    #     print("The runtime of Algorithm 3 is",t1,"s")

    # t = cputime()
    res = prod(fs)
    # t1 = cputime(t)
    # if k >= 20:
    #     print("The runtime of the product tree is",t1,"s")
    return res

# def find_smallest_integer(l, k):
#     """
#     Input l and k, k must divides l-1
#     output the smallest integers a and b such that a, b are in the same coset
#     with gcd(a,b)=1 and (l-1)/k|ord(a).
#     """
#     assert k > 1
#     F = GF(l)
#     #bound = l # Find a and b in Z_\ell
#     bound = k//2
#     A = []
#     # Find a primitive root of Z_\ell
#     from sage.schemes.elliptic_curves.isogeny_small_degree import _least_semi_primitive
#     a0 = F(_least_semi_primitive(l))
#     e = (l-1)//k
#     # Construct the set S = {1,\lambda,\lambda^2,...,\lambda^{k-1}}
#     lam = a0**e
#     S = []
#     for x in range(0,k):
#         s = lam**x
#         S.append(s)
#     # Find a and b
#     R = []
#     for j in range(2,bound):
#         a = F(j)
#         ord_a = a.multiplicative_order()
#         if ord_a % e ==0:
#             A = []
#             B = []
#             for x in S:
#                 b = x*a
#                 B.append(b)
#             # Filter B by <+->
#             B1 = []
#             for x in B:
#                 tmp = (l-1)//2
#                 if x > tmp:
#                     B1.append(Integer(l-x))
#                 else:
#                     B1.append(Integer(x))
#             B1.sort() # Sort the set of B1 with ascending order
#             B1 = set(B1) # Filter repeated elements
#             if 1 in B1:
#                 B1.remove(1)
#             while len(B1)!=0:
#                 candidate = B1.pop()
#                 if gcd(Integer(a),candidate) == 1:
#                     A.append(candidate)
#                     break
#         if len(A)!=0:
#             R.append((a,A[0]))
#     if len(R)!=0:
#         a,b = min(R)
#     else:
#         # If entering this branch, set a = b = 0 and choose shoup's algorithm
#         a = 0
#         b = 0
#     return (a,b)
@cached_method
def find_smallest_integer(l, k):
    """
    Input l and k, output the smallest integers a and b such that a, b are in the same coset
    with gcd(a,b)=1 and (l-1)/k|ord(a).
    """
    assert k>1
    F = GF(l)
    # Find a primitive root of Z_\ell
    from sage.schemes.elliptic_curves.isogeny_small_degree import _least_semi_primitive
    a0 = F(_least_semi_primitive(l))
    e = (l-1)//k
    # Construct the set S = {1,\lambda,\lambda^2,...,\lambda^{k-1}}
    lam = a0**e
    S = []
    for x in range(0,k):
        s = lam**x
        S.append(s)
    # Find a and b
    B = []
    R = []
    B.append(S)
    for ii in range(1,e):
        T = []
        tmp = a0**ii
        for s in S:
            T.append(tmp*s)
        B.append(T)
    # Filter B by <+->
    for ii in range(len(B)):
        T = []
        for x in B[ii]:
            tmp = (l-1)//2
            if x > tmp:
                T.append(Integer(l-x))
            else:
                T.append(Integer(x))
        T.sort() # Sort the set of B1 with ascending order
        T = set(T) # Filter repeated elements
        if 1 in T:
            T.remove(1)
        T.update()
        t1 = min(T)
        T.remove(t1)
        t2 = min(T)
        T.remove(t2)
        while gcd(t1,t2)!=1 and len(T)!=0:
            t2 = min(T)
            T.remove(t2)
            break
        R.append((t1,t2))
    B = dict()
    for x in R:
        tmp = max(x)
        B[tmp] = x
    a,b = B[min(B)]
    return a,b

def get_scalarmul(a,b,x,n):
    """
    Give the parameters a and b of the elliptic curve,
    the x-coordinates of an point P=(x,y) on the curve,
    return the x-coordinates of [n]P=m(x)/d(x).
    """
    if n == 2:
        if a == 0:
            T1 = x**2
            T2 = x*T1
            phi_2 = x*(T2-8*b)
            psi_22 = 4*(T2+b)
        else:
            T1 = x**2
            T4 = T1 - a
            T5 = T4**2
            T8 = b*x
            T9 = 8*T8
            phi_2 = T5 - T9
            T10 = T1 + a
            T11 = x*T10
            T13 = T11 + b
            psi_22 = 4*T13
        # phi_2 = x**4 - 2*x**2*a + a**2 - 8*x*b
        # psi_22 = 4*x**3 + 4*x*a + 4*b
        return phi_2,psi_22
    elif n == 3:
        if a == 0:
            T1 = b**2
            T2 = x**2
            T0 = b*T1
            T3 = T2*x
            T4 = T1*T3
            T5 = T3**2
            T6 = b*T5
            phi_3 = 48*(T4-2*T6+T0)+16*T0
            T7 = T5*T3
            phi_3 = T7 + phi_3
            psi_32 = 3*x*(T3+4*b)
            psi_32 = psi_32**2
        else:
            phi_3 = x**9 - 12*x**7*a + 30*x**5*a**2 - 96*x**6*b + 36*x**3*a**3 - 24*x**4*a*b + 9*x*a**4 + 48*x**2*a**2*b + 48*x**3*b**2 + 8*a**3*b + 96*x*a*b**2 + 64*b**3
            psi_32 = (3*x**4 + 6*x**2*a - a**2 + 12*x*b)**2
        return phi_3,psi_32
    elif n == 4:
        x3 = x**16 - 40*x**14*a + 348*x**12*a**2 - 544*x**13*b + 1000*x**10*a**3 + 128*x**11*a*b + 1478*x**8*a**4 + 1760*x**9*a**2*b + 2944*x**10*b**2 + 1000*x**6*a**5 + 3584*x**7*a**3*b + 9696*x**8*a*b**2 + 348*x**4*a**6 + 1952*x**5*a**4*b + 14208*x**6*a**2*b**2 + 8704*x**7*b**3 - 40*x**2*a**7 + 1408*x**3*a**5*b + 2368*x**4*a**3*b**2 + 26624*x**5*a*b**3 + a**8 - 96*x*a**6*b + 1536*x**2*a**4*b**2 + 7680*x**3*a**2*b**3 + 15872*x**4*b**4 - 32*a**5*b**2 + 11264*x**2*a*b**4 - 256*a**2*b**4 + 4096*x*b**5
        z3 = 2**4 * (x**3 + x*a + b) * (-x**6 - 5*x**4*a + 5*x**2*a**2 - 20*x**3*b + a**3 + 4*x*a*b + 8*b**2)**2
        return x3,z3
    else:
        assert False #TODO: Precompute x-only scalar multiplication for larger scalars.

def kernel_polynomial_from_x_fft(E, x, l):
    """
    Given the x-coordinate x(P), where P has order l,
    returns the kernel polynomial of <P> using FFT
    """
    F2 = E.base_field()
    p = F2.characteristic()
    Fbig = x.parent()
    ext = Fbig.over(F2)
    R,X = F2['X'].objgen()

    assert l.is_prime()
    if l <= 3:
        return R([-x, 1])

    try:
        X_in_F2 = F2(x)
    except ValueError:
        pass
    else:
        return prod(X - xx for xx in x_multiples(E, X_in_F2))

    if E.frobenius() not in ZZ:
        raise NotImplementedError

    def minpoly(elt):
        return ntl_funs(F2).minpoly_mod(ext(elt).vector(), ext.modulus())
    t = cputime()
    fs = [minpoly(x)]
    t1 = cputime(t)

    k = fs[0].degree()
    m = (l-1) // (2*k)

    assert k > 1    # handled above

    from sage.schemes.elliptic_curves.isogeny_small_degree import _least_semi_primitive

    print("The extension degree is", k)
    print("The order is", l)
    if k >= 20:
        print("The runtime of computing the first minimal polynomial is",t1,"s")
    t2 = cputime()
    if k > 7:
        (a, b) = find_smallest_integer(l,k)
        print("a = ",a,"b =",b)
        if a !=0 and m > 1 and a < 5 and ZZ(b).abs() < 5:
            # def FFT2(eval,var):
            #     n = len(eval)
            #     ms = [X-beta for beta in var]
            #     y = ProductTree(ms).remainders(R(eval))
            #     return y
            #Need fix = 1/n mod p, i.e., y = y*fix
            def IFFT2(eval,var):
                n = len(eval)
                ms = [X-beta for beta in var]
                y = ProductTree(ms).remainders(R(eval))
                tmp = ZZ(n).inverse_mod(p)
                y = [tmp*ii for ii in y]
                return y
            t = cputime()
            a = ZZ(a).abs()
            b = ZZ(b).abs()
            len_a = k*a**2 + 1
            len_b = k*b**2 + 1
            n_a = len_a.bit_length()
            n_b = len_b.bit_length()
            n_a = 2**n_a
            n_b = 2**n_b
            ia = n_a//2
            ib = n_b//2
            Ea = E.a4()
            Eb = E.a6()
            alpha = F2.primitive_element()
            # Compute [a]x = ma(x)/da(x) and [b]x=mb(x)/db(x)
            xa = []
            xb = []
            ma = []
            mb = []
            da = []
            db = []
            if n_a >= n_b:
                two_n = n_a//n_b
                e = (p**2-1)//n_a
                zeta_a = alpha**e
                zeta_b = zeta_a**two_n
                for ii in range(ia):
                    xa.append(zeta_a**ii)
                    tmp_ma,tmp_da = get_scalarmul(Ea,Eb,xa[ii],a)
                    if tmp_da == 0:
                        ma.append(tmp_ma)
                    else:
                        ma.append(tmp_ma/tmp_da)
                    da.append(tmp_da)
                for ii in range(ib):
                    xb.append(xa[ii]**two_n)
                    tmp_mb,tmp_db = get_scalarmul(Ea,Eb,xb[ii],b)
                    if tmp_db == 0:
                        mb.append(tmp_mb)
                    else:
                        mb.append(tmp_mb/tmp_db)
                    db.append(tmp_db)
            else:
                two_n = n_b//n_a
                e = (p**2-1)//n_b
                zeta_b = alpha**e
                zeta_a = zeta_b**two_n
                for ii in range(ib):
                    xb.append(zeta_b**ii)
                    tmp_mb,tmp_db = get_scalarmul(Ea,Eb,xb[ii],b)
                    if tmp_db == 0:
                        mb.append(tmp_mb)
                    else:
                        mb.append(tmp_mb)
                    db.append(tmp_db)
                for ii in range(ia):
                    xa.append(xb[ii]**two_n)
                    tmp_ma,tmp_da = get_scalarmul(Ea,Eb,xa[ii],a)
                    if tmp_da == 0:
                        ma.append(tmp_ma)
                    else:
                        ma.append(tmp_ma/tmp_da)
                    da.append(tmp_da)
            for ii in range(ia):
                tmp = -xa[ii]
                xa.append(tmp)
                tmp_ma,tmp_da = get_scalarmul(Ea,Eb,tmp,a)
                if tmp_da == 0:
                    ma.append(tmp_ma)
                else:
                    ma.append(tmp_ma/tmp_da)
                da.append(tmp_da)
            for ii in range(ib):
                tmp = -xb[ii]
                xb.append(tmp)
                tmp_mb,tmp_db = get_scalarmul(Ea,Eb,tmp,b)
                if tmp_db == 0:
                    mb.append(tmp_mb)
                else:
                    mb.append(tmp_mb/tmp_db)
                db.append(tmp_db)
            print("The runtime of computing [a]x and [b]x is ",cputime(t),"s")
            # Compute the coefficients of ga and gb and then compute gcd(ga,gb)
            t = cputime()
            # Compute the inverse of xa and xb
            if n_a >= n_b:
                for j in range(ia):
                    xa[j]=1/xa[j]
                    xa[j+ia]=-xa[j]
                for j in range(ib):
                    xb[j]=xa[j]**two_n
                    xb[j+ib]=-xb[j]
            else:
                for j in range(ib):
                    xb[j]=1/xb[j]
                    xb[j+ib]=-xb[j]
                for j in range(ia):
                    xa[j]=xb[j]**two_n
                    xa[j+ia]=-xa[j]
            for ii in range(1, m):
                y1 = []
                y2 = []
                #cofs = fs[ii-1].list()
                #y1 = FFT2(cofs,fa)
                #y2 = FFT2(cofs,fb)
                for j in range(n_a):
                    if da[j]!= 0:
                        y1.append(fs[ii-1](ma[j])*da[j]**k)
                    else:
                        y1.append(ma[j]**k)
                for j in range(n_b):
                    if db[j]!= 0:
                        y2.append(fs[ii-1](mb[j])*db[j]**k)
                    else:
                        y2.append(mb[j]**k)
                res1 = IFFT2(y1, xa)
                res2 = IFFT2(y2, xb)
                ga = []
                gb = []
                for ii in range(len_a):
                    ga.append(res1[ii])
                for ii in range(len_b):
                    gb.append(res2[ii])
                res = gcd(R(ga),R(gb))
                fs.append(res)
                print(res)
            print("done-------------------------------------------------------")
            print("The runtime of FFT is ",cputime(t),"s")
        else:
            xi = xPoint(x, E.change_ring(Fbig))
            a = _least_semi_primitive(l)
            for _ in range(1, m):
                xi = xi.mul(a)
                fs.append(minpoly(xi.X))
    else:
        xi = xPoint(x, E.change_ring(Fbig))
        a = _least_semi_primitive(l)
        #t = cputime()
        for _ in range(1, m):
            xi = xi.mul(a)
            fs.append(minpoly(xi.X))
    t1 = cputime(t2)
    if k >= 20:
        print("The runtime of New algorithm 3 is ",t1,"s")
    t = cputime()
    res = prod(fs)
    t1 = cputime(t)
    if k >= 20:
        print("The runtime of the product tree is ",t1,"s")
    return res

def kernel_polynomial_from_x_comp(E, x, l):
    r"""
    Given the x-coordinate x(P), where P has order l,
    returns the kernel polynomial of <P>.
    Compare the runtime of two different methods.
    """

    F2 = E.base_field()
    p = F2.characteristic()
    Fbig = x.parent()
    ext = Fbig.over(F2)
    R,X = F2['X'].objgen()

    assert l.is_prime()
    if l <= 3:
        return R([-x, 1])

    try:
        X_in_F2 = F2(x)
    except ValueError:
        pass
    else:
        return prod(X - xx for xx in x_multiples(E, X_in_F2))

    if E.frobenius() not in ZZ:
        raise NotImplementedError

    def minpoly(elt):
        return ntl_funs(F2).minpoly_mod(ext(elt).vector(), ext.modulus())

    t = cputime()
    fs = [minpoly(x)]
    t1 = cputime(t)

    k = fs[0].degree()
    m = (l-1) // (2*k)

    assert k > 1    # handled above

    from sage.schemes.elliptic_curves.isogeny_small_degree import _least_semi_primitive

    print("The extension degree is", k)
    print("The order is", l)
    if k >= 20:
        print("The runtime of computing the first minimal polynomial is",t1,"s")
    ### original algorithm:
    t = cputime()
    a = _least_semi_primitive(l)
    xi = xPoint(x, E.change_ring(Fbig))

    for _ in range(1, m):
        xi = xi.mul(a)
        fs.append(minpoly(xi.X))
    t1 = cputime(t)
    fs = [minpoly(x)]
    # New algorithm:
    # t2 = cputime()
    if k > 7:
        t = cputime()
        (a, b) = find_smallest_integer(l,k)
        t_ab = cputime(t)
        print("a = ",a,"b =",b)
        if a !=0 and m > 1 and a < 5 and ZZ(b).abs() < 5:
            def FFT2(eval,var):
                ms = [X-beta for beta in var]
                y = ProductTree(ms).remainders(R(eval))
                return y
            #Need fix = 1/n mod p, i.e., y = y*fix
            t = cputime()
            tt1 = cputime()
            def IFFT2(eval,var):
                n = len(eval)
                ms = [X-beta for beta in var]
                y = ProductTree(ms).remainders(R(eval))
                tmp = ZZ(n).inverse_mod(p)
                y = [tmp*ii for ii in y]
                return y
            a = ZZ(a).abs()
            b = ZZ(b).abs()
            len_a = k*a**2 + 1
            len_b = k*b**2 + 1
            n_a = len_a.bit_length()
            n_b = len_b.bit_length()
            n_a = 2**n_a
            n_b = 2**n_b
            ia = n_a//2
            ib = n_b//2
            Ea = E.a4()
            Eb = E.a6()
            print(cputime(tt1))
            # alpha = F2.primitive_element()
            alpha = F2([3,1])
            # Compute [a]x and [b]x
            xa = []
            xb = []
            ma = []
            mb = []
            da = []
            db = []
            tt = 0
            if n_a >= n_b:
                two_n = n_a//n_b
                e = (p**2-1)//n_a
                zeta_a = alpha**e
                zeta_b = zeta_a**two_n
                for ii in range(ia):
                    xa.append(zeta_a**ii)
                    tmp_ma,tmp_da = get_scalarmul(Ea,Eb,xa[ii],a)
                    if tmp_da == 0:
                        ma.append(F2(tmp_ma))
                    else:
                        ma.append(F2(tmp_ma/tmp_da))
                    da.append(tmp_da)
                for ii in range(ib):
                    xb.append(xa[ii]**two_n)
                    tmp_mb,tmp_db = get_scalarmul(Ea,Eb,xb[ii],b)
                    if tmp_db == 0:
                        mb.append(F2(tmp_mb))
                    else:
                        mb.append(F2(tmp_mb/tmp_db))
                    db.append(F2(tmp_db))
            else:
                two_n = n_b//n_a
                e = (p**2-1)//n_b
                zeta_b = alpha**e
                zeta_a = zeta_b**two_n
                for ii in range(ib):
                    xb.append(zeta_b**ii)
                    tmp_mb,tmp_db = get_scalarmul(Ea,Eb,xb[ii],b)
                    if tmp_db == 0:
                        mb.append(F2(tmp_mb))
                    else:
                        mb.append(F2(tmp_mb/tmp_db))
                    db.append(F2(tmp_db))
                for ii in range(ia):
                    xa.append(xb[ii]**two_n)
                    tmp_ma,tmp_da = get_scalarmul(Ea,Eb,xa[ii],a)
                    if tmp_da == 0:
                        ma.append(F2(tmp_ma))
                    else:
                        ma.append(F2(tmp_ma/tmp_da))
                    da.append(F2(tmp_da))
            for ii in range(ia):
                tmp = -xa[ii]
                xa.append(tmp)
                tmp_ma,tmp_da = get_scalarmul(Ea,Eb,tmp,a)
                if tmp_da == 0:
                    ma.append(F2(tmp_ma))
                else:
                    ma.append(F2(tmp_ma/tmp_da))
                da.append(F2(tmp_da))
            for ii in range(ib):
                tmp = -xb[ii]
                xb.append(tmp)
                tmp_mb,tmp_db = get_scalarmul(Ea,Eb,tmp,b)
                if tmp_db == 0:
                    mb.append(F2(tmp_mb))
                else:
                    mb.append(F2(tmp_mb/tmp_db))
                db.append(F2(tmp_db))
            t_sc = cputime(t)
            # Compute the coefficients of ga and gb and then compute gcd(ga,gb)
            t = cputime()
            # Compute the inverse of xa and xb
            if n_a >= n_b:
                for j in range(ia):
                    xa[j]=1/xa[j]
                    xa[j+ia]=-xa[j]
                for j in range(ib):
                    xb[j]=xa[j]**two_n
                    xb[j+ib]=-xb[j]
            else:
                for j in range(ib):
                    xb[j]=1/xb[j]
                    xb[j+ib]=-xb[j]
                for j in range(ia):
                    xa[j]=xb[j]**two_n
                    xa[j+ia]=-xa[j]
            t_inv = cputime(t)
            t_loop = 0
            t_fft = 0
            for ii in range(1, m):
                t = cputime()
                y1 = []
                y2 = []
                # For big k, using FFT to evaluate is much faster.
                cofs = fs[ii-1].list()
                y1 = FFT2(cofs,ma)
                y2 = FFT2(cofs,mb)
                for j in range(n_a):
                    if da[j]!= 0:
                        # y1.append(fs[ii-1](ma[j])*da[j]**k)
                        y1[j]=y1[j]*da[j]**k
                    else:
                        # y1.append(ma[j]**k)
                        y1[j]=ma[j]**k
                for j in range(n_b):
                    if db[j]!= 0:
                        # y2.append(fs[ii-1](mb[j])*db[j]**k)
                        y2[j]=y2[j]*db[j]**k
                    else:
                        # y2.append(mb[j]**k)
                        y2[j]=mb[j]**k
                t_loop += cputime(t)
                t = cputime()
                res1 = IFFT2(y1, xa)
                res2 = IFFT2(y2, xb)
                ga = []
                gb = []
                for ii in range(len_a):
                    ga.append(res1[ii])
                for ii in range(len_b):
                    gb.append(res2[ii])
                res = gcd(R(ga),R(gb))
                fs.append(res)
                t_fft += cputime(t)
                assert res.degree() == k
                # print(res)
                print("done-------------------------------------------------------")
            print("The runtime of computing a and b is ",t_ab,"s")
            print("The runtime of computing [a]x and [b]x is ",t_sc,"s")
            print("The runtime of evaluation is ",t_inv+t_loop,"s")
            print("The runtime of FFT is ",t_fft,"s")
            print("The runtime of the new method is ",t_ab+t_sc+t_inv+t_loop+t_fft,"s")
        else:
            xi = xPoint(x, E.change_ring(Fbig))
            a = _least_semi_primitive(l)
            for _ in range(1, m):
                xi = xi.mul(a)
                fs.append(minpoly(xi.X))
    else:
        xi = xPoint(x, E.change_ring(Fbig))
        a = _least_semi_primitive(l)
        #t = cputime()
        for _ in range(1, m):
            xi = xi.mul(a)
            fs.append(minpoly(xi.X))
    # t = cputime(t2)
    if k >= 2:
        print("The runtime of original algorithm 3 is ",t1,"s")
    t = cputime()
    res = prod(fs)
    t1 = cputime(t)
    if k >= 20:
        print("The runtime of the product tree is ",t1,"s")
    return res

################################################################

def xMUL(E, x, n):
    r"""
    Given an integer n, and x = x(P) of a point P on E, computes x([n]P)
    """
    Q = xPoint(x, E).mul(n)
    if not Q:
        raise ZeroDivisionError
    return Q.X

def xISOG(E, x, l):
    r"""
    Given a x = x(P) of a point P on E of order l,
    computes the separable isogeny with <P> as kernel
    """
    #t = cputime()
    h = kernel_polynomial_from_x(E, x, l)
    #print("The runtime of algorithm 4 is",cputime(t),"s")
    return E.isogeny(h, check=False)

def xISOG_comp(E, x, l):
    r"""
    This version is for comparison.
    Given a x = x(P) of a point P on E of order l,
    computes the separable isogeny with <P> as kernel.
    """
    h = kernel_polynomial_from_x_comp(E, x, l)
    return E.isogeny(h, check=False)