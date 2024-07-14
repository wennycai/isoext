# This is an implementation to find the "good" prime for new method to compute kernel polynomials

from sage.all import *
#Given the embedding degree k, return candidates l
def candidates(k):
	res = []
	lowest = 2*k+1
	highest = floor(sqrt(k**3))
	for ii in range(lowest,highest):
		tmp = next_prime(ii)
		if k.divides(tmp-1):
			if tmp not in res:
				res.append(tmp)
	return res

def candidates_2(k):
	res = []
	lowest = floor(sqrt(k**3))
	highest = k**3
	for ii in range(lowest,highest):
		tmp = next_prime(ii)
		if k.divides(tmp-1):
			if tmp not in res:
				res.append(tmp)
	return res

def list_lk(ells,n):
    """
    Input ells, size of p and p is 3 mod 4, output all primes in ells such that ord(p)=ell-1/2 in Zl
    """
    flag = True
    bound = 0
    while flag:
        p = next_prime(ZZ(randint(2**(n-1),2**n-1)))
        if p % 4 != 3:
            continue
        for ii in range(len(ells)):
            l = ells[ii]
            count = 0 # the number of ell such that ord(p)!=ell-1/2
            x = Mod(p, l).multiplicative_order() # p mod l, ord(p) in Z l
            if x%2 == 0:
                x//=2
            if x != (l-1)//2:
                count += 1
            if count > bound:
                continue
        if count <= bound:
            flag = False
    return p

def find_smallest_integer_1(l, k):
    """
    Input l and k, output the smallest integers a and b such that a, b are in the same coset
    with gcd(a,b)=1 and ord(a)|(l-1)/k.
    """
    F = GF(l)
    bound = min(l-1,k)
    A = []
    a0 = F.primitive_element()
    e = floor((l-1)/k)
    lam = a0**e
    S = []
    for x in range(0,k):
        s = lam**x
        S.append(s)
    for j in range(2,bound):
        a = F(j)
        orn_a = a.multiplicative_order()
        if orn_a % e ==0:
            B = []
            for x in range(0,k):
                b = S[x]*a
                B.append(b)
            flag = True
            while flag:
                b0 = min(B)
                b1 = max(B)
                if b0 == 1:
                    B.remove(b0)
                    b0 = min(B)
                if l-b1 == 1:
                    B.remove(b1)
                    b1 = max(B)
                if gcd(Integer(a),Integer(b0))==1:
                    flag = False
                    if b0 < a:
                        A.append((Integer(a),Integer(b0)))
                elif gcd(Integer(a),Integer(l-b1))==1:
                    flag = False
                    if Integer(l-b1)<Integer(a):
                        A.append((Integer(a),-Integer(l-b1)))
                else:
                    B.remove(b0)
    if len(A)!=0:
        (a,b)=min(A)
    else:
        a = 0
        b = 0
    return (a,b)

def find_smallest_integer(l, k):
    """
    Input l and k, output the smallest integers a and b such that a, b are in the same coset
    with gcd(a,b)=1 and (l-1)/k|ord(a).
    """
    assert k>1
    F = GF(l)
    A = []
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

def find_p(k,l,L,n):
    iter = 0
    bound = 2^n-2^(n-1)-1
    while True:
        iter += 1
        r = ZZ(randint(2**(n-1),2**n-1))
        p = r*2**L+1 # This case will make p = 1 mod 4, set p = r*2^L-1 can find p = 3 mod 4.
        if not p.is_pseudoprime():
            continue
        if p % 3 == 1:
            continue
        x = Mod(p, l).multiplicative_order() # p mod l, ord(p) in Z l
        if x%2 == 0:
            x //= 2
        if x == k:
            print("Find!")
            print("Prime p = ",p)
            break
        if iter >= bound:
            print("Not find!")
            print(iter)
            break
    return p

# We want to implement this k and l.
k = 24
l = 97
L = (k*3^2).bit_length()+1
n = 255-L # the bit length of r, such that p = 2^L*r+1
print("ell = ", l, ", k = ", k, ", find p.")
p = find_p(k,l,L,n)

def candidates_2(k):
	res = []
	lowest = floor(sqrt(k**3))
	highest = 5*floor(sqrt(k**3))
	for ii in range(lowest,highest):
		tmp = next_prime(ii)
		if k.divides(tmp-1):
			if tmp not in res:
				res.append(tmp)
	return res

# Find candidates k and l, such that max(|a|,|b|)=3.
init_k = 10
k = init_k
count = 0
while k <= 200:
    ls = candidates_2(k)
    for ii in range(len(ls)):
        a,b = find_smallest_integer(ls[ii],k)
        if (max(abs(a),abs(b))==3) and (((ls[ii]-1)//(2*k))>10):
            print("ell = ", ls[ii], ", k = ", k)
            count+=1
    k = k + 1