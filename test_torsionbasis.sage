# Test the new method for generating the torsion basis <P,Q>=E[\ell]

from sage.all import *
from src.broker import starting_curve
from sage.schemes.elliptic_curves.hom_composite import EllipticCurveHom_composite
from src.idealtoisogeny import Deuring_Context
from src.klpt import DecompAlphaN
from src.torsionbasis import torsiongen_old, torsiongen_new, torsiongen_BGDS
from src.torsionbasis import compute_hk
proof.all(False)

# Finding \ell
def find_ell(p, e, lb):
# Given prime p, the power e of \ell and the lowest bound lb such that l = 4*lb + 1.
# Return \ell such that \ell^e is split in Q(i) and extension degree k = \ell^(e-1)*(\ell-1)/2.
    for ii in range(lb,100):
        l = 4*ii+1 # l = 1 mod 4
        if is_pseudoprime(l):
            k = Mod(p, l**e).multiplicative_order()# p mod l^e, ord(p) in Z l^e
            if(k%2 == 0):
                k//=2
            if k == (l**(e-1)*(l-1))//2:
                print("l = ",l,"k = ",k)
                #break
    return l


def compute_k(l):
    # p = 3 mod 4
    n = 254 # The bit length of m
    m = ZZ(randint(2^(n-1),2^n-1))
    p = 4*m + 3
    while True:
        while not is_pseudoprime(p):
            m = ZZ(randint(2^(n-1),2^n-1))
            p = 4*m + 3
        k = Mod(p, l**e).multiplicative_order()# p mod l^e, ord(p) in Z l^e
        if(k%2 == 0):
            k//=2
        if k == (l**(e-1)*(l-1))//2:
            print("l = ",l,"k = ",k)
            print("p = ", p)
            break
    return p,k

#p, k = compute_k(l)
#p = 66349865482136799597423426703589536462545536174475714315679284447803044365887 #l=5
p = 102048467339623158506645658223447225762629635207267170428015600155663323117259 #l=13
#p = 37670568336551536389503919665937491111216122470333837677213877442445311999999
#p = 78278574168605041334522887375273568900953370692274455135290682043244181458199 #l=17
#p = 72877392169357447977123374094516472224439866527619463796629079622727645384511 #l=41
#p = 84653884921425332149751711381494615330443068360277274133539117326448784906767 #l=97
#p = 92371312324454870956864537369378048571858598084795271608626407734621069745511 #l=193

l = 13
e = 1
#k = (l-1)//2
k = 5
x = var("x")
F = GF(p)
F2 = GF(p**2, name = "u", modulus = x**2+1)
u = F2.gen()
q = 1
QF = BinaryQF([1,0,q])
E = EllipticCurve(F, [1,0])
E.set_order(p + 1)
E0 = E.change_ring(F2)
iota,_ = sorted(a for a in E0.automorphisms() if a**4 != a**2) # starting_curve for p=3 mod 4 is y^2=x^3+x


# Test algorithm
flag1 = True
t1 = 0
t2 = 0
t3 = 0
if flag1:
    #for ii in range(10):
    #    t = cputime()
    P1,Q1 = torsiongen_new(E0,QF,iota,l,k)
    #    t1+=cputime(t)
    #print("Computing torsion basis (new) takes ",t1/10,"s")
    #for ii in range(1):
    #    t = cputime()
    #    P2,Q2 = torsiongen_BGDS(E0,l,k)
    #    t2+=cputime(t)
    #print("Compute kernel takes (BGDS)  ",t2/1,"s")
    #for ii in range(10):
    #    t = cputime()
    #    P3,Q3 = torsiongen_old(E0,l,k)
    #    t3+=cputime(t)
    #print("Compute kernel takes (old)  ",t3/10,"s")

# Test for the new algorithm
flag2 = False
if flag2:
    QF = BinaryQF([1,0,q])
    # Step 1. Find a,b such that a^2+b^2=\ell^e, a and b can not be 1 or -1
    a,b = QF.solve_integer(l**e)
    print("a = ",a)
    print("b = ",b)

    # Step 2. Construct map phi = [a]+\tau[b]
    print("Start to construct phi")
    R.<x, y, z> = PolynomialRing(F2)
    phi_a = E0.scalar_multiplication(a)
    phi_b = E0.scalar_multiplication(b)
    tau_b = iota*phi_b
    phi_a = phi_a.rational_maps()
    tau_b = tau_b.rational_maps()
    # Elliptic curve point addition in affine coordinates
    lam = (phi_a[1]-tau_b[1])/(phi_a[0]-tau_b[0])
    phi_x = lam**2-E0.a2()-phi_a[0]-tau_b[0]
    phi_y = lam*(phi_a[0]-phi_x)-phi_a[1]
    phi =  (phi_x,phi_y)
    print("Construction is finished")

    # Step 3. Take the denominator of phi as psi.
    print("Start to extract psi")
    g = [y^2-z]
    tmp_0 = R(phi_x.numerator())
    tmp_1 = R(phi_x.denominator())
    tmp_0 = tmp_0.reduce(g)
    tmp_1 = tmp_1.reduce(g)
    tmp_0 = tmp_0.subs({z:x^3+x}) # If we don't use this substitution, y^2 can not be reduced to x^3+x automatically.(E0: y^2=x^3+x)
    tmp_1 = tmp_1.subs({z:x^3+x})
    # Our target is tmp_0/tmp_1, but if we compute this directly, the denominator and the numerator of the result will have common polynomials.
    # In Sagemath, Multivariate polynomial ring can not compute gcd normally.
    # Fortunately, the x-coordinate of our target is a polynomial solely rely on x. Even the y-coordinate of our target, we can extract y of the polynomial and then we will meet a similar situation.
    # Change ring can help us solve this issue.
    Rx.<x> = PolynomialRing(F2)
    tmp_0 = Rx(tmp_0)
    tmp_1 = Rx(tmp_1)
    tmp = tmp_0/tmp_1
    psi_x = tmp.denominator()
    tmp_0 = R(phi_y.numerator())
    tmp_1 = R(phi_y.denominator())
    tmp_0 = tmp_0.reduce(g)
    tmp_1 = tmp_1.reduce(g)
    tmp_0 = tmp_0.subs({z:x^3+x})
    tmp_1 = tmp_1.subs({z:x^3+x})
    tmp_0 = tmp_0.subs({y:1})
    tmp_1 = tmp_1.subs({y:1})
    tmp_0 = Rx(tmp_0)
    tmp_1 = Rx(tmp_1)
    tmp = tmp_0/tmp_1
    psi_y = tmp.denominator()
    psi = (psi_x,psi_y)
    res= psi_x.sqrt()
    #res = tmp[0][0]
    print("Extraction is finished")
    ################################################################
    #Construct extension field
    Fp = GF(p)
    # say this is the polynomial over Fp^2 with which you want to take the extension
    #d = 5
    #f = F2['x'].irreducible_element(d)
    R.<x> = F2[]
    f = R(res)
    # compute the minimal polynomial g _over Fp_ of a root of f using Galois theory
    frob = F2.frobenius_endomorphism()
    hs = [f]
    for _ in range(1, F2.degree()):
        hs.append(hs[-1].map_coefficients(frob))
    g = prod(hs).change_ring(Fp)

    # now we construct the field extension Fr/Fp defined by g
    Fr.<beta> = GF(p).extension(g)

    # and an embedding Fq->Fr such that Fr/Fq is defined by f
    # (there is almost certainly a better way of doing this!)

    for root,_ in F2.modulus().roots(ring=Fr):
        if sum(c.polynomial()(root)*beta^i for i,c in enumerate(f)) == 0:
            break
    else: assert False
    emb = F2.hom([root])
    try:
        emb.register_as_coercion()  # make type coercions between Fq and Fr automatic
    except AssertionError:
        None
    ext = Fr.over(F2)
    # the extension Fr/Fq is indeed generated by f
    assert ext.modulus() == f

    ################################################################

    # now we can interpret elements of Fr as elements of Fq[x] via the extension
    #elt = Fr.random_element()
    #print('written over Fp:', elt)
    #print('written over Fq:', ext(elt).polynomial())
