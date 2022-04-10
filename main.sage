def linearize(p):  
    L = 0
    indici_soluzione = {}
    dct = p.dict()
    n_monomi = len(dct)
    print(n_monomi)
    for i in range(n_monomi):      
        item = dct.popitem()
        esponenti = item[0]
        coeff = item[1]
        S = PolynomialRing(GF(q), ['y%d' % i for i in range(n_monomi)])
        L = L + S(coeff)*S(var('y%d' % i))
        if(sum(esponenti)==1):
            indici_soluzione[esponenti]=i
    return (L, indici_soluzione)

def oracle_LWE(u, alpha):
    m = len(u)
    G = vector(u).base_ring()
    q = G.characteristic()
    V = G^m
    a = V.random_element()
    sigma = alpha*q
    N = RealDistribution('gaussian', sigma)
    r = N.get_random_element()
    eta = GF(q)(int(r))
    b = a*u + eta
    return (a,b)

def LWE_polynomial (q,d):
    F.<t> = GF(q)[]
    poly=GF(q)(1)*t
    for i in range(d):
        poly = poly*(t^2 - (i+1)^2)      
    return poly 
