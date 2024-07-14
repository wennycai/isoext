#!/usr/bin/env python3

from sage.all import *
from sage.schemes.elliptic_curves.hom_composite import EllipticCurveHom_composite
proof.all(False)

def twistcurve(E,k):
    r"""
    Returns a quadratic twist \widetilde{E_0} of E_0 over F_{p^2k}.
    """
    F2 = E.base_field()
    p = F2.characteristic()
    Fbig,A = F2.extension(k,'A').objgen()

    Ek = E.change_ring(Fbig)
    while True:
        D = Fbig.random_element()
        if (not D.is_square()):
            break
    tmp_a = 1/D
    _,_,_,a,b = Ek.a_invariants()
    assert Ek == EllipticCurve([a,b])
    Et = EllipticCurve([a*tmp_a**2, b*tmp_a**3])
    assert Et.is_isomorphic(Ek.quadratic_twist())
    Et.twist_D = D

    u = D**(p//2)
    def eval_j(pt):
        if not pt:
            return pt
        x,y = pt.xy()
        return pt.curve()(x**p * u**2, y**p * u**3)
    E.endo_j = eval_j   #FIXME adding this attribute is quite a hack

    return Et

@cached_method
def twistcurve_new(E,Fbig):
    r"""
    Returns a quadratic twist \widetilde{E_0} of E_0 over F_{p^2k}.
    """
    Ek = E.change_ring(Fbig)
    while True:
        D = Fbig.random_element()
        if (not D.is_square()):
            break
    tmp_a = 1/D
    _,_,_,a,b = Ek.a_invariants()
    assert Ek == EllipticCurve([a,b])
    Et = EllipticCurve([a*tmp_a**2, b*tmp_a**3])
    assert Et.is_isomorphic(Ek.quadratic_twist())
    Et.twist_D = D
    return Et,tmp_a

def com_minipoly_k_P(E, QF, iota, l):
    F2 = E.base_field()
    #t = cputime()
    # Step 1. Find a,b such that a^2+b^2=\ell^e, a and b can not be 1 or -1
    a,b = QF.solve_integer(l)
    # Step 2. Construct map phi = [a]+\tau[b]
    #print("Start to construct phi")
    phi_a = E.scalar_multiplication(a)
    phi_b = E.scalar_multiplication(b)
    tau_b = iota*phi_b
    phi_a = phi_a.rational_maps()
    tau_b = tau_b.rational_maps()
    #print("Repeated computation:",cputime(t),"s")
    # Elliptic curve point addition in affine coordinates
    lam = (phi_a[1]-tau_b[1])/(phi_a[0]-tau_b[0])
    phi_x = lam**2-E.a2()-phi_a[0]-tau_b[0]
    #phi_y = lam*(phi_a[0]-phi_x)-phi_a[1]
    # phi =  (phi_x,phi_y)
    #print("Construction is finished")
    # Step 3. Take the denominator of phi as psi.
    #print("Start to extract psi")
    R = F2['x','y','z']
    x,y,z = R.gens()
    g = [y**2-z]
    tmp_0 = R(phi_x.numerator())
    tmp_1 = R(phi_x.denominator())
    tmp_0 = tmp_0.reduce(g)
    tmp_1 = tmp_1.reduce(g)
    tmp_0 = tmp_0.subs({z:x**3+x}) # If we don't use this substitution, y^2 can not be reduced to x^3+x automatically.(E0: y^2=x^3+x)
    tmp_1 = tmp_1.subs({z:x**3+x})
    # Our target is tmp_0/tmp_1, but if we compute this directly, the denominator and the numerator of the result will have common polynomials.
    # In Sagemath, Multivariate polynomial ring can not compute gcd normally.
    # Fortunately, the x-coordinate of our target is a polynomial solely rely on x. Even the y-coordinate of our target, we can extract y of the polynomial and then we will meet a similar situation.
    # Change ring can help us solve this issue.
    Rx=F2['x']
    tmp_0 = Rx(tmp_0)
    tmp_1 = Rx(tmp_1)
    tmp = tmp_0/tmp_1
    psi_x = tmp.denominator()
    #tmp = list(psi_x.factor())
    #fp = tmp[len(tmp)-1][0]
    assert psi_x.is_square()
    fp = psi_x.sqrt()
    #print("Extraction is finished")
    return fp, phi_a, tau_b

def com_minipoly_k_Q(E,phi_a,tau_b):
    F2 = E.base_field()
    # Step 1. Find a,b such that a^2+b^2=\ell^e, a and b can not be 1 or -1
    # Step 2. Construct map phi = [a]+\tau[b]
    #print("Start to construct phi")
    R = F2['x','y','z']
    x,y,z = R.gens()
    # Elliptic curve point addition in affine coordinates
    lam = (phi_a[1]+tau_b[1])/(phi_a[0]-tau_b[0])
    phi_x = lam**2-E.a2()-phi_a[0]-tau_b[0]
    # phi_y = lam*(phi_a[0]-phi_x)-phi_a[1]
    # phi =  (phi_x,phi_y)
    #print("Construction is finished")
    # Step 3. Take the denominator of phi as psi.
    #print("Start to extract psi")
    g = [y**2-z]
    tmp_0 = R(phi_x.numerator())
    tmp_1 = R(phi_x.denominator())
    tmp_0 = tmp_0.reduce(g)
    tmp_1 = tmp_1.reduce(g)
    tmp_0 = tmp_0.subs({z:x**3+x}) # If we don't use this substitution, y^2 can not be reduced to x^3+x automatically.(E0: y^2=x^3+x)
    tmp_1 = tmp_1.subs({z:x**3+x})
    # Our target is tmp_0/tmp_1, but if we compute this directly, the denominator and the numerator of the result will have common polynomials.
    # In Sagemath, Multivariate polynomial ring can not compute gcd normally.
    # Fortunately, the x-coordinate of our target is a polynomial solely rely on x. Even the y-coordinate of our target, we can extract y of the polynomial and then we will meet a similar situation.
    # Change ring can help us solve this issue.
    Rx=F2['x']
    tmp_0 = Rx(tmp_0)
    tmp_1 = Rx(tmp_1)
    tmp = tmp_0/tmp_1
    psi_x = tmp.denominator()
    # tmp = list(psi_x.factor())
    # fq = tmp[len(tmp)-1][0]
    assert psi_x.is_square()
    fq = psi_x.sqrt()
    #print("Extraction is finished")
    return fq

def construct_ext_P(E,fp,extdeg):
    F2 = E.base_field()
    Fp = F2.base_ring()
    # say this is the polynomial over Fq with which you want to take the extension
    f = F2['x'](fp)
    # compute the minimal polynomial g _over Fp_ of a root of f using Galois theory
    frob = F2.frobenius_endomorphism()
    hs = [f]
    for _ in range(1, F2.degree()):
        hs.append(hs[-1].map_coefficients(frob))
    g = prod(hs).change_ring(Fp)
    # now we construct the field extension Fbig/Fp defined by g
    #Fbig = GF(self.p**(2*extdeg), name = "beta", modulus =g)
    Fbig_p = Fp.extension(g,name = 'vp')
    v = Fbig_p.gen()
    for root,_ in F2.modulus().roots(ring=Fbig_p):
        if sum(c.polynomial()(root)*v**i for i,c in enumerate(f)) == 0:
            break
        #else: assert False
    emb = F2.hom([root])
    try:
        emb.register_as_coercion()  # make type coercions between Fq and Fr automatic
    except AssertionError:
        None
    return Fbig_p

def construct_ext_Q(E,fp,extdeg):
    F2 = E.base_field()
    Fp = F2.base_ring()
    # say this is the polynomial over Fq with which you want to take the extension
    f = F2['x'](fp)
    # compute the minimal polynomial g _over Fp_ of a root of f using Galois theory
    frob = F2.frobenius_endomorphism()
    hs = [f]
    for _ in range(1, F2.degree()):
        hs.append(hs[-1].map_coefficients(frob))
    g = prod(hs).change_ring(Fp)
    # now we construct the field extension Fbig/Fp defined by g
    #Fbig = GF(self.p**(2*extdeg), name = "beta", modulus =g)
    Fbig_q = Fp.extension(g,name = 'vq')
    v = Fbig_q.gen()
    for root,_ in F2.modulus().roots(ring=Fbig_q):
        if sum(c.polynomial()(root)*v**i for i,c in enumerate(f)) == 0:
            break
        #else: assert False
    emb = F2.hom([root])
    try:
        emb.register_as_coercion()  # make type coercions between Fq and Fr automatic
    except AssertionError:
        None
    return Fbig_q

def genTorsionBasisP_1mod4_one(E, QF, iota, l, k):
    """
    Given a curve E, prime l, exponent e=1, output generators P of E[l]
    """
    # If l = 1 mod 4, the l-torsion point is awalys on the twisted curve.
    F2 = E.base_field()
    # Compute minimal polynomial of degree k for xP, satisfies l|p^k+1.
    fp, phi_a, tau_b = com_minipoly_k_P(E,QF,iota,l)

    # Construct extension field Fp^2k with fp
    Fbig_p = construct_ext_P(E,fp,k)
    # if not Fbig.has_coerce_map_from(F2):
    #     Fbig.register_coercion(Hom(F2,Fbig).an_element())

    # Compute the twisted curve
#    t = cputime()
    Et, tmp_a = twistcurve_new(E, Fbig_p)
#    print("Repeated time is ", cputime(t),"s")
    xP = Fbig_p.gen()
    a4 = Et.a4()
    # We need to map the point
    xP = xP*tmp_a#tmp_a = 1/D
    tmp = xP**3 + a4*xP
    # a6 = tmpE.a6()
    # tmp = xP**3 + a4*xP + a6
    assert tmp.is_square() == True
    tmpy = Fbig_p(tmp).sqrt()
    P = Et([xP,tmpy])
    P.set_order(l)

    return P, phi_a, tau_b

def genTorsionBasisQ_1mod4_one(E, l, k, phi_a, tau_b):
    """
    Given a curve E, prime l, exponent e=1, output generators (P, Q) of E[l^e]
    """
    # If l = 1 mod 4, the l-torsion point is awalys on the twisted curve.
    F2 = E.base_field()
    # Compute minimal polynomial of degree k for xP, satisfies l|p^k+1.
    fq = com_minipoly_k_Q(E, phi_a, tau_b)

    # Construct extension field Fp^2k with fp
    Fbig_q = construct_ext_Q(E, fq, k)

    # Compute the twisted curve
    Et, tmp_a = twistcurve_new(E, Fbig_q)
    xQ = Fbig_q.gen()
    a4 = Et.a4()
    # We need to map the point
    xQ = xQ*tmp_a
    tmp = xQ**3 + a4*xQ
    # a6 = tmpE.a6()
    # tmp = xP**3 + a4*xP + a6
    assert tmp.is_square() == True
    tmpy = Fbig_q(tmp).sqrt()
    Q = Et([xQ,tmpy])
    Q.set_order(l)

    return Q

# Compute h_k
def compute_hk(k,E):
    #E(F_p^k)
    F2 = E.base_field()
    p = F2.characteristic()
    Nk = E.order()
    N = Nk
    if k == 2:
        N1 = p+1
        N = Nk//N1
        return N
    elif k == 3:
        N1 = (p+1)
        N = Nk//N1
        return N
    elif k == 4:
        N2 = (p+1)**2
        N = Nk//N2
        return N
    elif k == 8:
        N4 = (p**2-1)**2
        N = Nk//N4
        return N
    elif k == 12:
        tmp = p**2  #p^2
        N2 = (p+1)**2
        N4 = (tmp-1)**2
        N6 = (tmp*p+1)**2
        N = (Nk*N2)//(N6*N4)
        return N
    elif k == 16:
        N8 = (p**4-1)**2
        N = Nk//N8
        return N
    elif k == 20:
        tmp = p**2  #p^2
        tmp1 = tmp**2   #p^4
        N2 = (p+1)**2
        N4 = (tmp-1)**2
        N10 = (tmp1*p+1)**2
        N = (Nk*N2)//(N10*N4)
        return N
    elif k == 32:
        N16 = (p**8-1)**2
        N = Nk//N16
        return N
    elif k == 40:
        tmp = p**2 #p^2
        tmp1 = tmp**2 #p^4
        tmp2 = p*tmp1 #p^5
        tmp2 = tmp2**2 #p^10
        N4 = (tmp-1)**2
        N8 = (tmp1-1)**2
        N20 = (tmp2-1)**2
        N = (Nk*N4)//(N8*N20)
        return N
    elif k == 48:
        tmp = p**4
        tmp1 = tmp**2
        tmp2 = tmp*tmp1
        N8 = (tmp-1)**2
        N16 = (tmp1-1)**2
        N24 = (tmp2-1)**2
        N = (Nk*N8)//(N16*N24)
        return N
    elif k == 96:
        tmp = p**8
        tmp1 = tmp**2
        tmp2 = tmp*tmp1
        N16 = (tmp-1)**2
        N32 = (tmp1-1)**2
        N48 = (tmp2-1)**2
        N = (Nk*N16)//(N32*N48)
        return N
    elif k == 192:
        tmp = p**16
        tmp1 = tmp**2
        tmp2 = tmp*tmp1
        N32 = (tmp-1)**2
        N64 = (tmp1-1)**2
        N96 = (tmp2-1)**2
        N = (Nk*N32)//(N64*N96)
        return N
    return N

def frob_power(P,power):
    E = P.curve()
    K = E.base_field()
    frob = K.frobenius_endomorphism(power)
    R = E(frob(P[0]),frob(P[1]))
    return R

def compute_delta(P,k0):
    R = P
    if k0 == 2:
        #pi - [1]
        S = frob_power(P,1)
        R = S - P
        return R
    elif k0 == 3:
        #pi - [1]
        S = frob_power(P,1)
        R = S - P
        return R
    elif k0 == 4:
        #pi^2-1
        S = frob_power(P,2)
        R = S - P
        return R
    elif k0 == 8:
        #pi^4 - [1]
        S = frob_power(P,4)
        R = S - P
        return R
    elif k0 == 12:
        #(pi^2+1)(pi^6-1)
        S = frob_power(P,6)
        S = S - P
        R = frob_power(S,2)
        R = R + S
        return R
    elif k0 == 16:
        #pi^8 - [1]
        S = frob_power(P,8)
        R = S - P
        return R
    elif k0 == 20:
        #(pi^2+1)(pi^10-1)
        S = frob_power(P,10)
        S = S - P
        R = frob_power(S,2)
        R = R + S
        return R
    elif k0 == 32:
        #pi^16 - [1]
        S = frob_power(P,16)
        R = S - P
        return R
    elif k0 == 40:
        #(pi^20-1)(pi^4+1)
        S = frob_power(P,20)
        S = S - P
        R = frob_power(S,4)
        R = R + S
        return R
    elif k0 == 48:
        #(pi^8+1)(pi^24-1)
        S = frob_power(P,24)
        S = S - P
        R = frob_power(S,8)
        R = R + S
        return R
    elif k0 == 96:
        #(pi^16+1)(pi^48-1)
        S = frob_power(P,48)
        S = S - P
        R = frob_power(S,16)
        R = R + S
        return R
    elif k0 == 192:
        #(pi^32+1)(pi^96-1)
        S = frob_power(P,96)
        S = S - P
        R = frob_power(S,32)
        R = R + S
        return R
    return R

def torsiongen_new(E,QF,iota,l,k):
# A better algorithm to find a torsion basis if l=1mod4 and k=(l-1)/2 for p=3mod4
    P, phi_a, tau_b = genTorsionBasisP_1mod4_one(E, QF, iota, l,k)
    Q = genTorsionBasisQ_1mod4_one(E,l,k,phi_a,tau_b)
    return P,Q

def torsiongen_BGDS(E,l,k):
# Algorithm in [Fast and Frobenius: Rational Isogeny Evaluation over Finite Fields]
# Find a torsion basis of E[l]
    F2 = E.base_field()
    p = F2.characteristic()
    twist = not l.divides(p**k - (-1)**k)
    if twist:
        extdeg = 2*k
    else:
        extdeg = k
    Fbig,A = E.base_field().extension(extdeg,'A').objgen()
    Et = E.change_ring(Fbig)

    order = p**extdeg - (-1)**extdeg
    Et.set_order(order**2, num_checks=0)
    assert l.divides(order)

    N = compute_hk(extdeg,Et)
    cof = N.prime_to_m_part(l)

    def BGDS():
        P_l = Et(0)
        while P_l.is_zero():
            P = Et.random_point()
            R = compute_delta(P,extdeg)
            P_l = cof*R
            P_l.set_order(l)
        return P_l

    P = BGDS()
    Q = BGDS()

    #while P.weil_pairing(Q,l).is_one():
    #    Q = BGDS()

    return P,Q

def torsiongen_old(E,l,k):
# Algorithm in [Deuring for the People: Supersingular Elliptic Curves with Prescribed Endomorphism Ring in General Characteristic]
# Find a torsion basis of E[l]
    F2 = E.base_field()
    p = F2.characteristic()
    twist = not l.divides(p**k - (-1)**k)
    if twist:
        Et = twistcurve(E,k)
        Fbig = Et.base_field()
    else:
        Fbig,A = E.base_field().extension(k,'A').objgen()
        Et = E.change_ring(Fbig)
    order = p**k - (-1 if twist else +1) * (-1)**k
    Et.set_order(order**2, num_checks=0)
    assert l.divides(order)

    cof = order.prime_to_m_part(l)
    def rpt():
        while True:
            T = cof * Et.random_point()
            if T: break
        T.set_order(l)
        return T
    P = rpt()
    Q = rpt()
    while P.weil_pairing(Q,l).is_one():
        Q = rpt()
    return P,Q