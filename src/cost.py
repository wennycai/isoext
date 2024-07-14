#!/usr/bin/env python3
import collections
from sage.all import *
from sage.misc.verbose import verbose

def smoothPart(n, B, N=1):
    r"""
    Compute the maximal divisor of n which is B-smooth and coprime to N.
    """
    n = ZZ(n)
    n = n.prime_to_m_part(N)
    return prod(l**e for l,e in n.factor(limit=B) if l < B)

def cost_model(p, newconst=None):
    r"""
    Given a prime characteristic p, return a function in two arguments
    l^e and k which roughly describes the cost of the Deuring algorithm
    when using l^e-torsion in GF(p^(2k)).
    """
    logp = p.log(2).n()
    loglogp = logp.log(2).n()
    log3 = log(3,2).n()

    # experimentally guessed using Sage 9.7 on a 2016 laptop
    if logp < 32:
        cutoff = 79
        def karatsuba(k):
            return k**log3 * (1/30 + logp/1e3 + logp**2/5e5 + (logp>=30)/50 + (logp>=31)/30)
    elif logp <= 64:
        cutoff = 44
        def karatsuba(k):
            return k**log3 * (1/30 + logp/190)
    else:
        cutoff = 55
        def karatsuba(k):
            return k**log3 * (1/30 + loglogp/10)

    def quasilinear(k):
        fun0 = lambda k: k*log(k,2).n() * (1/10 + logp/200)
        off = karatsuba(cutoff) - fun0(cutoff)
        return off + fun0(k)

    def field_model(kk):
        if kk < cutoff:
            oneop = karatsuba(RR(kk))
        else:
            oneop = quasilinear(RR(kk))
        return RR(oneop)

    if newconst:
        c1, c2, c3, c4 = newconst
    else:
        c1, c2, c3, c4 = (0.31, 1.17, 0.46, 0.01)  # Empirically estimated
        #c1, c2, c3, c4 = (0.25, 1.82, 0.51, 0.22)  # Empirically estimated
        #c1, c2, c3, c4 = (2.65, 0.01, 1.25, 0.022) # Estimate in ApresSQI

    def model(le, k):
        le = ZZ(le)
        (l,e), = le.factor()
        logl = RR(l).log(2)
        #logle = e * logl
        #logk = RR(k).log(2)
        oneop = field_model(k)
        res = RR(oneop * (c1*k*logp + c2*logp) + c3*e*l*(k+c4*logl**2)) # Roughly torsion basis + eval. action + isogeny
        # if l % 4 == 1 and e == 1 and k == (l-1)//2:
        #     res = res/3
        return res
        #return RR(oneop * (c1*k*logp + c2*logp) + c3*e*l*((l//k)+c4*logl**2))  # Roughly torsion basis + eval. action + isogeny
        #return RR(oneop * (c1*e*logl + c2*l*logl) + c3*e*l*(k+c4*logl**2))  # Roughly torsion basis + eval. action + isogeny
    return model

def cost_model_2(p, newconst=None):
    r"""
    Given a prime characteristic p, return a function in two arguments
    l^e and k which roughly describes the cost of the Deuring algorithm
    when using l^e-torsion in GF(p^(2k)).
    """
    logp = p.log(2).n()
    loglogp = logp.log(2).n()
    log3 = log(3,2).n()

    # experimentally guessed using Sage 9.7 on a 2016 laptop
    if logp < 32:
        cutoff = 79
        def karatsuba(k):
            return k**log3 * (1/30 + logp/1e3 + logp**2/5e5 + (logp>=30)/50 + (logp>=31)/30)
    elif logp <= 64:
        cutoff = 44
        def karatsuba(k):
            return k**log3 * (1/30 + logp/190)
    else:
        cutoff = 55
        def karatsuba(k):
            return k**log3 * (1/30 + loglogp/10)

    def quasilinear(k):
        fun0 = lambda k: k*log(k,2).n() * (1/10 + logp/200)
        off = karatsuba(cutoff) - fun0(cutoff)
        return off + fun0(k)

    def field_model(kk):
        if kk < cutoff:
            oneop = karatsuba(RR(kk))
        else:
            oneop = quasilinear(RR(kk))
        return RR(oneop)

    if newconst:
        c1, c2, c3, c4 = newconst
    else:
        c1, c2, c3, c4 = (0.31, 1.17, 0.46, 0.01)  # Empirically estimated
        #c1, c2, c3, c4 = (0.25, 1.82, 0.51, 0.22)  # Empirically estimated
        #c1, c2, c3, c4 = (2.65, 0.01, 1.25, 0.022) # Estimate in ApresSQI

    def model(le, k):
        le = ZZ(le)
        (l,e), = le.factor()
        logl = RR(l).log(2)
        #logle = e * logl
        #logk = RR(k).log(2)
        oneop = field_model(k)
        res = RR(oneop * (c1*k*logp + c2*logp) + c3*e*l*(k+c4*logl**2)) # Roughly torsion basis + eval. action + isogeny
        if l % 4 == 1 and e == 1 and k == (l-1)//2:
            res = res/3
        return res
        #return RR(oneop * (c1*k*logp + c2*logp) + c3*e*l*((l//k)+c4*logl**2))  # Roughly torsion basis + eval. action + isogeny
        #return RR(oneop * (c1*e*logl + c2*l*logl) + c3*e*l*(k+c4*logl**2))  # Roughly torsion basis + eval. action + isogeny
    return model

def choose_torsion(p, q, N, lowbound, newconst=None):
    r"""
    Given p,q,N as in the Deuring correspondence, greedily find a set
    of pairs (l^e,k) for the specific characteristic which minimize
    the cost of the Deuring algorithm according to the cost_model().
    """
    facToExt = dict()
    # establish a baseline: take every l
    le = ZZ.one()
    # I don't really know how to get this bound and why we choose this bound
    num = 0
    while lcm(le for le in facToExt.keys()) < lowbound*2*q:
        le += 1
        # I think this branch is never happened
        if p.divides(le):
            continue
        # tmp = list(le.factor())
        # for i in range(len(tmp)):
        #     (l,e) = tmp[i]
        #     if l > 10:
        #         if l %4 !=1 and e!=1:
        #             continue
        # For an integer m = l1^e1*...*ln^en, m.radical() will return the product of factors l1*l2*...*ln
        # This branch makes sure that le is the power of l
        if not is_pseudoprime(le.radical()):
            continue
        k = Mod(p, le).multiplicative_order()# p mod le, ord(p) in Z le
        if k%2 == 0 and pow(p, k//2, le) - le == -1: # Use twist in this case  )
            k //= 2
        # for i in range(len(tmp)):
        #     (l,e) = tmp[i]
        #     if l > 10:
        #         if (l %4 ==1) and (e == 1) and (k!=(l-1)//2):
        #             continue
        facToExt[le] = k

    model = cost_model(p, newconst=newconst)

    # now, keep increasing k, looking for small-ish l defined over small k
    k = ZZ.zero()
    while True:

        # sort pairs (l^e,k) by cost estimate
        tups = sorted(facToExt.items(), key = lambda tup: model(*tup))

        # compute T to check what's the worst (l^e,k) pair we currently have to use
        it = 0
        T = ZZ.one()
        while it < len(tups) and T//T.gcd(2*q) < lowbound:
            tup = tups[it]
            cost = model(*tup)
            T = lcm(T, tup[0])
            it += 1

        facToExt = dict(tups[:it])
        T //= T.gcd(2 * q)   # point divisions
        assert T >= lowbound

        k += 1
        # figure out up to which prime l it's worth searching for this k
        maxlebits = 0
        while model(next_prime(1 << maxlebits), k) < cost:
            maxlebits += 1
        maxle = 0
        # print("k = ",k,"prime ",next_prime(1 << maxlebits), " is worth searching, and maxlebits = ",maxlebits)
        for i in reversed(range(maxlebits+1)):
            # if (model(next_prime(maxle | (1 << i)), k) < cost) or (next_prime(maxle | (1 << i))%4 == 1):
            if (model(next_prime(maxle | (1 << i)), k) < cost):
                maxle |= 1 << i
        verbose(f'{k = }:', tup, cost, maxle)
        if maxle < 1:   # no l^e at all -> done
            break

        # trial-divide the order in degree k to find new l^e
        on_curve = smoothPart(p**k - (-1)**k, maxle, N)
        on_twist = smoothPart(p**k + (-1)**k, maxle, N)
        for fac in (on_curve, on_twist):
            for l,e in fac.factor():
                for i in range(1,e+1):
                    if l**i in facToExt:
                        facToExt[l**i] = min(k, facToExt[l**i])
                    else:
                        facToExt[l**i] = k

    # apparently some other parts of the code need this to be sorted?   #TODO
    facToExt = dict(sorted(facToExt.items(), key = lambda tup: tup[0].prime_factors()))
    assert T >= lowbound
    return T, facToExt

def choose_torsion_2(p, q, N, lowbound, newconst=None):
    r"""
    Given p,q,N as in the Deuring correspondence, greedily find a set
    of pairs (l^e,k) for the specific characteristic which minimize
    the cost of the Deuring algorithm according to the cost_model().
    """
    facToExt = dict()
    # establish a baseline: take every l
    le = ZZ.one()
    # I don't really know how to get this bound and why we choose this bound
    num = 0
    while lcm(le for le in facToExt.keys()) < lowbound*2*q:
        le += 1
        # I think this branch is never happened
        if p.divides(le):
            continue
        tmp = list(le.factor())
        for i in range(len(tmp)):
            (l,e) = tmp[i]
            if l > 10:
                if l %4 !=1 and e!=1:
                    continue
        # For an integer m = l1^e1*...*ln^en, m.radical() will return the product of factors l1*l2*...*ln
        # This branch makes sure that le is the power of l
        if not is_pseudoprime(le.radical()):
            continue
        k = Mod(p, le).multiplicative_order()# p mod le, ord(p) in Z le
        if k%2 == 0 and pow(p, k//2, le) - le == -1: # Use twist in this case  )
            k //= 2
        for i in range(len(tmp)):
            (l,e) = tmp[i]
            if l > 10:
                if (l %4 ==1) and (e == 1) and (k!=(l-1)//2):
                    continue
        facToExt[le] = k

    model = cost_model_2(p, newconst=newconst)

    # now, keep increasing k, looking for small-ish l defined over small k
    k = ZZ.zero()
    while True:

        # sort pairs (l^e,k) by cost estimate
        tups = sorted(facToExt.items(), key = lambda tup: model(*tup))

        # compute T to check what's the worst (l^e,k) pair we currently have to use
        it = 0
        T = ZZ.one()
        while it < len(tups) and T//T.gcd(2*q) < lowbound:
            tup = tups[it]
            cost = model(*tup)
            T = lcm(T, tup[0])
            it += 1

        facToExt = dict(tups[:it])
        T //= T.gcd(2 * q)   # point divisions
        assert T >= lowbound

        k += 1
        # figure out up to which prime l it's worth searching for this k
        maxlebits = 0
        while model(next_prime(1 << maxlebits), k) < cost:
            maxlebits += 1
        maxle = 0
        # print("k = ",k,"prime ",next_prime(1 << maxlebits), " is worth searching, and maxlebits = ",maxlebits)
        for i in reversed(range(maxlebits+1)):
            if (model(next_prime(maxle | (1 << i)), k) < cost) or (next_prime(maxle | (1 << i))%4 == 1):
            # if (model(next_prime(maxle | (1 << i)), k) < cost):
                maxle |= 1 << i
        verbose(f'{k = }:', tup, cost, maxle)
        if maxle < 1:   # no l^e at all -> done
            break

        # trial-divide the order in degree k to find new l^e
        on_curve = smoothPart(p**k - (-1)**k, maxle, N)
        on_twist = smoothPart(p**k + (-1)**k, maxle, N)
        for fac in (on_curve, on_twist):
            for l,e in fac.factor():
                for i in range(1,e+1):
                    if l**i in facToExt:
                        facToExt[l**i] = min(k, facToExt[l**i])
                    else:
                        facToExt[l**i] = k

    # apparently some other parts of the code need this to be sorted?   #TODO
    facToExt = dict(sorted(facToExt.items(), key = lambda tup: tup[0].prime_factors()))
    assert T >= lowbound
    return T, facToExt
