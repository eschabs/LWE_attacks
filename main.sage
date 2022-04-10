def exp_to_index(exp):
    s=str(exp)
    s=s.replace('(','')
    s=s.replace(')','')
    s=s.replace(' ','')
    s=s.replace(',', '_')
    return s

def create_polynomials(R,q,d,l,a,b):
    insieme_esponenti = set()
    l_new = []
    for p in l:
        p=p(sum([R(a[i])*R('z%d' % i) for i in range(d)])+b)
        l_new.append(p)
        dct = p.dict()
        n_monomi = len(dct)
        print(n_monomi)
        for i in range(n_monomi):      
            item = dct.popitem()
            insieme_esponenti.update([item[0]])
    #ORIGINALE
    return (l_new,PolynomialRing(GF(q),[('y%s' % exp_to_index(esponenti)) for esponenti in insieme_esponenti] + ['z%d' % i for i in range(d)]))

def linearize(S,l):  
    l_new=[]
    for p in l:
        L = 0
        indici_soluzione = {}
        dct = p.dict()
        n_monomi = len(dct)
        print(n_monomi)
        for i in range(n_monomi):      
            item = dct.popitem()
            esponenti = item[0]
            coeff = item[1]
            L = L + S(coeff)*S(var('y%s' % exp_to_index(esponenti)))
        l_new.append(L)
    return l_new

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

# TEST:
q=17
d=4
R = PolynomialRing(GF(q), ['z%d' % i for i in range(d)])
u = vector(GF(q),[1+2*i for i in range(d)])
alpha = 5
(a,b) = oracle_LWE(u, alpha)
poly = LWE_polynomial(q,d)
(lista_polinomi,S) = create_polynomials(R,q,d,[poly],a,b)
z=[var('z%d' % i) for i in range(d)]
print('- 0')
print(poly)
print(poly.dict())
print('- 1')
L = linearize(S,lista_polinomi)

print(L)
print('- 2')
print(len(L), d)
print('- 3')
print('DONE')

#   COSTRUIRE e_j
#   s= '(' 
#   for i in range(d-1):
#       s=s+('%d,' % int((i+1)==j))
#   s=s+('%d)' % int(d==j))
#
#   COSTRUIRE e_j
#   s= '' 
#   for i in range(d-1):
#       s=s+('%d_' % int((i+1)==j))
#   s=s+('%d' % int(d==j))
