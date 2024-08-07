#!/usr/bin/env python3

from sage.all import *
from sage.schemes.elliptic_curves.hom_composite import EllipticCurveHom_composite
from .klpt import DecompAlphaN
from .xonly import xPoint, xISOG, xISOG_comp
from sage.misc.verbose import verbose
import pickle
proof.all(False)

def Frob(P):
    r"""
    Given a point P on any elliptic curve over a finite field
    whose coefficients lie in the prime field,
    returns P evaluated in the frobenius endomorphism
    """
    E = P.curve()
    p = E.base_field().characteristic()
    return E(*(c**p for c in P))

def chain_iso(kernelPointsIn, E):
    r"""
    Given points {P_1, ..., P_n} on curve E, outputs the isogeny
    whose kernel is generated by {P_1, ..., P_n}
    """
    Ei = E
    kernelPoints = kernelPointsIn[::-1]
    philist = []
    t1 = 0
    t2 = 0
    while kernelPoints:
        Ri, (l,e) = kernelPoints.pop()
        Ki = Ri.mul(l**(e-1))
        t3 = cputime()
        phi = xISOG_comp(Ei, Ki.X, l)
        t1+=cputime(t3)
        Ei = phi.codomain()
        if e > 1:
            kernelPoints.append((Ri, (l, e-1)))
        #t4 = cputime()
        kernelPoints = [(P.push(phi), order) for (P, order) in kernelPoints]
        #t2+=cputime(t4)
        philist.append(phi)
    print("The runtime of computing kernel polynomials is",t1,"s")
    #print("The runtime of pushing points is",t2,"s")
    return EllipticCurveHom_composite.from_factors(philist)

class Deuring_Context:
    r"""
    Helper to setup parameters for computing the Deuring correspondence.
    """
    def __init__(self, O0, E0, iota, facToExt):
        self.O0 = O0
        self.E0 = E0
        F2 = E0.base_field()
        assert F2.degree() == 2
        self.p = F2.characteristic()
        self.iota = iota
        self.facToExt = facToExt

        def eval_i(pt):
            r"""
            Given a point P on E_0, returns P evaluated in iota,
            where iota corresponds to i in O_0 under the isomorphism E_0 -> O_0
            """
            if not pt:
                return pt
            x,y = pt.xy()
            R = pt.base_ring()['x,y'].fraction_field()
            f,g = map(R, iota.rational_maps())
            try:
                return pt.curve()(f(x,y), g(x,y))
            except ZeroDivisionError:   # Point is in the kernel
                return pt.curve()(0)
        self.endo_i = eval_i
        self.endo_j = Frob


    #@cached_method
    def twistE0(self, extdeg):
        r"""
        Returns a quadratic twist \widetilde{E_0} of E_0 over F_{p^2k}.
        The twist has its own isomorphism \widetilde{E_0} -> O_0
        """
        Fbig,A = self.E0.base_field().extension(extdeg,'A').objgen()
        E0big = self.E0.change_ring(Fbig)
        while True:
            D = Fbig.random_element()
            if not D.is_square():
                break
        _,_,_,a,b = E0big.a_invariants()
        assert E0big == EllipticCurve([a,b])
        E = EllipticCurve([a/D**2, b/D**3])
        #assert E.is_isomorphic(E0big.quadratic_twist())
        E.twist_D = D       #FIXME adding this attribute is quite a hack

        R,(x,y) = Fbig['x,y'].fraction_field().objgens()
        f,g = map(R, self.iota.rational_maps())
        f = f(x=D*x) / D
        g = (g//y)(x=D*x) * y
        def eval_i(pt):
            if not pt:
                return pt
            x,y = pt.xy()
            return pt.curve()(f(x,y), g(x,y))
        E.endo_i = eval_i   #FIXME adding this attribute is quite a hack

        u = D**(self.p//2)
        def eval_j(pt):
            if not pt:
                return pt
            x,y = pt.xy()
            return pt.curve()(x**self.p * u**2, y**self.p * u**3)
        E.endo_j = eval_j   #FIXME adding this attribute is quite a hack

        return E

    def evalIdealElt(self, a, Q):
        r"""
        Given an endomorphism a and a point Q of
        order coprime to the denominator of a,
        returns a(Q)
        """
        assert Q
        #d = lcm(c.denominator() for c in a)
        E = Q.curve()
        twist = hasattr(E, 'twist_D')
        if not twist:
            iQ = self.endo_i(Q)
            jQ = self.endo_j(Q)
            kQ = self.endo_i(jQ)
        else:
            iQ = E.endo_i(Q)
            jQ = E.endo_j(Q)
            kQ = E.endo_i(jQ)
        coeffs = [coeff % Q.order() for coeff in a]
        aQ = coeffs[0]*Q + coeffs[1]*iQ + coeffs[2]*jQ + coeffs[3]*kQ
        return aQ, (E.twist_D if twist else 1)

    def IdealToIsogenyGens(self, I, specificTorsion=0):
        r"""
        Given a left O0-ideal I, returns {P_1, .., P_n} such that ker phi_I = <P_1, .., P_n>
        """
        kerGens = []
        a = DecompAlphaN(I)
        d = lcm(c.denominator() for c in a)
        N = ZZ(I.norm()).gcd(specificTorsion) if specificTorsion else ZZ(I.norm())
        for (l,e) in N.factor():
            lval = d.valuation(l)  # point divisions
            P, Q = self.genTorsionBasis(self.E0, l, e+lval)
            R,twD = self.evalIdealElt(l**lval * a.conjugate(), P)
            if not l**(e-1) * R:
                R,twD = self.evalIdealElt(l**lval * a.conjugate(), Q)
            kerGens.append((xPoint(R.xy()[0]*twD, self.E0.change_ring(R.base_ring())), (l,e)))
        return P

    def IdealToIsogenyGens_new(self, I, specificTorsion=0):
        r"""
        New algorithm for computing kernel points.
        Given a left O0-ideal I, returns {P_1, .., P_n} such that ker phi_I = <P_1, .., P_n>.
        """
        kerGens = []
        a = DecompAlphaN(I)
        d = lcm(c.denominator() for c in a)
        N = ZZ(I.norm()).gcd(specificTorsion) if specificTorsion else ZZ(I.norm())
        for (l,e) in N.factor():
            lval = d.valuation(l)  # point divisions
            P, Pl = self.genTorsionBasisP(self.E0, l, e+lval)
            R,twD = self.evalIdealElt(l**lval * a.conjugate(), P)
            if not l**(e-1) * R:
                print("We need to Generate Q")
                Q = self.genTorsionBasisQ(self.E0, Pl, l, e+lval)
                R,twD = self.evalIdealElt(l**lval * a.conjugate(), Q)
            kerGens.append((xPoint(R.xy()[0]*twD, self.E0.change_ring(R.base_ring())), (l,e)))
        return kerGens

    def Computextension(self, I, P):
        r"""
        Given precomputed kernel generators and a left ideal I of prime norm,
        construct the extension field Fp^2k and return the x-coordinate of generators.
        """
        a = DecompAlphaN(I)
        d = lcm(c.denominator() for c in a)
        N = ZZ(I.norm())
        for (l,e) in N.factor():
            lval = d.valuation(l)  # point divisions
            t = l**(lval+e)
            extdeg = self.facToExt[t]
            Fbig,A = self.E0.base_field().extension(extdeg,'A').objgen()
            tmp = (P.X).list()
        return xPoint(Fbig(tmp), self.E0.change_ring(Fbig))

    def Initial_precom(self, I, specificTorsion=0):
        r"""
        Given a left O0-ideal I, compute the corresponding elliptic curve if we use the twist.
        (Only use this function if precomputation is used)
        """
        a = DecompAlphaN(I)
        d = lcm(c.denominator() for c in a)
        N = ZZ(I.norm()).gcd(specificTorsion) if specificTorsion else ZZ(I.norm())
        for (l,e) in N.factor():
            lval = d.valuation(l)  # point divisions
            res= self.Init_curve(self.E0, l, e+lval)
        return res

    def IdealToIsogeny(self, I, specificTorsion=0):
        r"""
        Given a left O0-ideal I, returns the corresponding isogeny phi_I
        """
        # t = cputime()
        kerGens = self.IdealToIsogenyGens_new(I,specificTorsion=specificTorsion)
        # points = "point_k24.pkl"
        # tmp = kerGens0[::-1]
        # with open(points,"wb") as file:
        #     while tmp:
        #         pickle.dump(tmp.pop(),file)
        # print("writing done")
        # print("The runtime of initial kernel points is",cputime(t),"s")
        # points = "point_k24.pkl"
        # kerGens = []
        # tmp = []
        # with open(points,"rb") as file:
        #     while True:
        #         try:
        #             tmp.append(pickle.load(file))
        #         except EOFError:
        #             break
        # for ii in range(len(tmp)):
        #     R,(l,e) = tmp[ii]
        #     kerGens.append((R,(l,e)))
        # res = self.Initial_precom(I, specificTorsion=specificTorsion) # Only use this function if precomputation is used
        return chain_iso(kerGens, self.E0)

    @cached_method
    def genTorsionBasis(self, E, l, e, xOnly=False):
        ### is there anything to be gained by using a more clever basis
        ### such that we do know the action of the endo ring on it?
        ### eg SIDH choice P, iota(P)
        r"""
        Given a curve E, prime l, exponent e, output generators (P, Q) of E[l^e]
        """
        t = l**e
        extdeg = self.facToExt[t]
        twist = not t.divides(self.p**extdeg - (-1)**extdeg)
        verbose(f"Generating torsion basis for E[{l}^{e}] over F_p^{2*extdeg}" + (" on quadratic twist" if twist else ""))

        if twist:
            assert E is self.E0
            E = self.twistE0(extdeg)
            Fbig = E.base_field()
        else:
            Fbig,A = E.base_field().extension(extdeg,'A').objgen()
            E = E.change_ring(Fbig)

        order = self.p**extdeg - (-1 if twist else +1) * (-1)**extdeg
        E.set_order(order**2, num_checks=0)
        assert t.divides(order)

        cof = order.prime_to_m_part(l)

        def rpt():
            while True:
                T = cof * E.random_point()
                Tl = l**(e-1)*T
                if Tl: break
            U = l*Tl
            while U:
                Tl = U
                U *= l
                T *= l
#            assert l**(e-1)*T and not l**e*T
#            assert Tl and not l*Tl
            T.set_order(l**e)
            Tl.set_order(l)
            return T, Tl

        P,Pl = rpt()
        Q,Ql = rpt()
        while Pl.weil_pairing(Ql,l).is_one():
            Q,Ql = rpt()

        if xOnly:
            D = E.twist_D if twist else 1
            P = xPoint(P.xy()[0]*D, self.E0.change_ring(Fbig))
            Q = xPoint(Q.xy()[0]*D, self.E0.change_ring(Fbig))
        return P, Q

    @cached_method
    def genTorsionBasisP(self, E, l, e, xOnly=False):
        r"""
        Given a curve E, prime l, exponent e, output a torsion basis P of E[l^e].
        """
        t = l**e
        extdeg = self.facToExt[t]
        twist = not t.divides(self.p**extdeg - (-1)**extdeg)
        verbose(f"Generating torsion basis P for E[{l}^{e}] over F_p^{2*extdeg}" + (" on quadratic twist" if twist else ""))

        if twist:
            assert E is self.E0
            E = self.twistE0(extdeg)
            Fbig = E.base_field()
        else:
            Fbig,A = E.base_field().extension(extdeg,'A').objgen()
            E = E.change_ring(Fbig)

        order = self.p**extdeg - (-1 if twist else +1) * (-1)**extdeg
        E.set_order(order**2, num_checks=0)
        assert t.divides(order)

        cof = order.prime_to_m_part(l)

        def rpt():
            while True:
                T = cof * E.random_point()
                Tl = l**(e-1)*T
                if Tl: break
            U = l*Tl
            while U:
                Tl = U
                U *= l
                T *= l
#            assert l**(e-1)*T and not l**e*T
#            assert Tl and not l*Tl
            T.set_order(l**e)
            Tl.set_order(l)
            return T, Tl

        P,Pl = rpt()

        if xOnly:
            D = E.twist_D if twist else 1
            P = xPoint(P.xy()[0]*D, self.E0.change_ring(Fbig))
        return P, Pl

    def Init_curve(self, E, l, e, xOnly=False):
        t = l**e
        extdeg = self.facToExt[t]
        twist = not t.divides(self.p**extdeg - (-1)**extdeg)
        if twist:
            assert E is self.E0
            E = self.twistE0(extdeg)
        else:
            Fbig,A = E.base_field().extension(extdeg,'A').objgen()
            E = E.change_ring(Fbig)
        return 1

    @cached_method
    def genTorsionBasisQ(self, E, Pl, l, e, xOnly=False):
        r"""
        Given a curve E, prime l, exponent e, output another torsion basis Q in E[l^e].
        """
        t = l**e
        extdeg = self.facToExt[t]
        twist = not t.divides(self.p**extdeg - (-1)**extdeg)
        verbose(f"Generating torsion basis Q for E[{l}^{e}] over F_p^{2*extdeg}" + (" on quadratic twist" if twist else ""))

        if twist:
            assert E is self.E0
            E = self.twistE0(extdeg)
            Fbig = E.base_field()
        else:
            Fbig,A = E.base_field().extension(extdeg,'A').objgen()
            E = E.change_ring(Fbig)

        order = self.p**extdeg - (-1 if twist else +1) * (-1)**extdeg
        E.set_order(order**2, num_checks=0)
        assert t.divides(order)

        cof = order.prime_to_m_part(l)

        def rpt():
            while True:
                T = cof * E.random_point()
                Tl = l**(e-1)*T
                if Tl: break
            U = l*Tl
            while U:
                Tl = U
                U *= l
                T *= l
#            assert l**(e-1)*T and not l**e*T
#            assert Tl and not l*Tl
            T.set_order(l**e)
            Tl.set_order(l)
            return T, Tl

        Q,Ql = rpt()
        while Pl.weil_pairing(Ql,l,algorithm='pari').is_one():
            Q,Ql = rpt()

        if xOnly:
            D = E.twist_D if twist else 1
            Q = xPoint(Q.xy()[0]*D, self.E0.change_ring(Fbig))
        return Q
