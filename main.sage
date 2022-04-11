import time

def exp_to_index(exp):
    s=str(exp)
    s=s.replace('(','')
    s=s.replace(')','')
    s=s.replace(' ','')
    s=s.replace(',', '_')
    return s

def create_polynomials(R,q,d,l,u,alpha):
    n=len(u)
    insieme_esponenti = set()
    l_new = []
    for p in l:
        (a,b) = oracle_LWE(u, alpha)
        p=p(sum([R(a[i])*R('z%d' % i) for i in range(n)])+b)
        l_new.append(p)
        dct = p.dict()
        n_monomi = len(dct)
        for i in range(n_monomi):      
            item = dct.popitem()
            insieme_esponenti.update([item[0]])
    return (l_new,PolynomialRing(GF(q),[('y%s' % exp_to_index(esponenti)) for esponenti in insieme_esponenti] + ['z%d' % i for i in range(n)]), insieme_esponenti)

def linearize(S,l):  
    l_new=[]
    for p in l:
        L = 0
        indici_soluzione = {}
        dct = p.dict()
        n_monomi = len(dct)
        for i in range(n_monomi):      
            item = dct.popitem()
            esponenti = item[0]
            coeff = item[1]
            L = L + S(coeff)*S(var('y%s' % exp_to_index(esponenti)))
        l_new.append(L)
    return l_new

def oracle_LWE(u, alpha):
    n = len(u)
    G = vector(u).base_ring()
    q = G.characteristic()
    V = G^n
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

def solve_linear_system_old (l, insieme_esponenti):
    start_time = time.time()
    print('Inizio a misurare il tempo!', start_time)
    variables = ['y%s' % exp_to_index(esponente) for esponente in insieme_esponenti]
    soluzione = solve(l, var(*variables))
    print("--- %s secondi ---" % (time.time() - start_time))
    return soluzione

def solve_linear_system (R,l,n,insieme_esponenti):
    start_time = time.time()
    print('Inizio a misurare il tempo!', start_time)
    print(l[0])
    variables=['y%s' % exp_to_index(esponente) for esponente in insieme_esponenti if str(esponente) != '('+ '0, '*(n-1) + '0)']
    M_list=[]
    for p in l:
        M_list.append([p.coefficient(R(v)) for v in variables])
    print(M_list)
    M = Matrix(tuple(M_list))
    c = vector([-p(0) for p in l])
    soluzione = M \ c
    print("--- %s secondi ---" % (time.time() - start_time))
    return soluzione
    return [0]
def canonical_basis_exponent(j,n):
    s= '(' 
    for i in range(d-1):
        s=s+('%d,' % int((i+1)==j))
    s=s+('%d)' % int(d==j))
    return s

# TEST:
q=17
d=2
n=5
alpha=n^(1/6)/q
D=2*d+1
N=binomial(n+D,n)

R = PolynomialRing(GF(q), ['z%d' % i for i in range(n)])
u = vector(GF(q),[1+2*i for i in range(n)])

z=[var('z%d' % i) for i in range(n)]

poly = LWE_polynomial(q,d)
l_poly=[]
#k = ceil(N*q^2*log(q)/100)
k = 1000

print('Chiamo l\'oracolo %d volte' % k)
print('Polinomio associato all\'oracolo: ', poly)

for i in range(k):
    l_poly.append(poly)

(lista_polinomi,S,esponenti) = create_polynomials(R,q,d,l_poly,u,alpha)

L = linearize(S,lista_polinomi)
print('Linearizzato!')
#print('Polinomi linearizzati: ', L)
#print('Esponenti dei linearizzati: ', esponenti)
soluzione = solve_linear_system(S,L,n,esponenti)
print('Trovata soluzione!')
print('Lunghezza soluzione: ', len(soluzione))
print('Soluzione del linearizzato: ', soluzione)

stringa_soluzione= '['
for i in range(n):
    stringa_soluzione = stringa_soluzione + str(soluzione[list(insieme_esponenti).index(canonical_basis_exponent(i,n))])