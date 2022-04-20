# coding=utf-8
from math import ceil
from random import randint
import warnings
import time
from sage.crypto.lwe import LWE
from sage.stats.distributions.discrete_gaussian_integer import DiscreteGaussianDistributionIntegerSampler


def LWE_polynomial (G, d):
    """
    Restituisco il polinomio p(t) := t(t+1)(t-1)...(t+d)(t-d).
    :param G    -- Anello in cui vivono i coefficienti del polinomio
    :param d    -- Modulo massimo delle radici del polinomio
    """
    F.<t> = G[]
    poly = G(1)*t
    for i in range(d):
        poly = poly*(t^2 - (i+G(1))^2)      
    return poly 

def create_polynomials(L, n, oracle):
    """
    Prende una lista di polinomi e li valuta in a_i*z + b_i, dove (a_i,b_i) sono coppie ottenute chiamando l'oracolo.
    :param L                    -- Lista di polinomi da valutare in a_i*z + b_i
    :param n                    -- Lunghezza del segreto
    :param oracle               -- Oracolo con cui genero le coppie (a_i,b_i)
    :return (l_new,exp_set):
             l_new              -- Polinomi nell'anello polinomiale R valutati in a*z+b 
             exp_lista          -- Lista degli esponenti associati alle variabili z_i dei monomi dei polinomi di l
    """
    G = ((L[0]).parent()).base_ring()
    R = PolynomialRing(G, ['z%d' % i for i in range(n)])
    p = R(1)      # Per sicurezza, nel caso non appaia nei polinomi, inserisco l'esponente associato al monomio costante 1
    exp_set = set()
    const_exp = ((p.dict()).popitem()) 
    exp_set.update([const_exp[0]])

    L_new = []  # Lista in cui inserire i nuovi polinomi 
    for p in L:
        (a,b) = oracle()
        p = p(sum([-R(a[i])*R('z%d' % i) for i in range(n)])+b)
        L_new.append(p)
        dct = p.dict()
        n_monomials = len(dct)
        for i in range(n_monomials):      
            item = dct.popitem()
            exp_set.update([item[0]])
    exp_list = [str(exp) for exp in exp_set] 
    return (L_new,exp_list)

def exp_to_index(exp):
    """
    Converte la rappresentazione in tuple degli esponenti dei monomi in delle stringhe che posso usare come indici.
    i.e.  e := (1,2,3,4) 
          'y%s' % exp_to_index(e) --> y1_2_3_4
    """
    s = str(exp)
    s = s.replace('(', '')      # Elimino parentesi
    s = s.replace(')', '')
    s = s.replace(', ', '_')    # Sostituisco virgole con underscore
    return s

def linearize(L, exp_list):  
    """
    Linearizza una lista di polinomi.
    :param L        -- Lista di polinomi
    :param exp_list -- Lista degli esponenti associati ai monomi dei polinomi di L
    """
    G = ((L[0]).parent()).base_ring()
    S = PolynomialRing(G, [('y%s' % exp_to_index(exp_monomial)) for exp_monomial in exp_list])
    L_new = []
    for p in L:
        q = S(0)
        dct = p.dict()
        n_monomials = len(dct)
        for i in range(n_monomials):      
            item = dct.popitem()
            exp_monomial = item[0]
            coeff = item[1]
            q = q + S(coeff)*S('y%s' % exp_to_index(exp_monomial))
        L_new.append(q)
    return L_new

def create_system(L, exp_list, n):
    """
    A partire dai polinomi linearizzati L genera la matrice del sistema lineare associata con i relativi termini noti.
    :param L            -- Lista di polinomi con cui creare il sistema
    :param exp_list     -- Lista degil esponenti associati ai monomi dei polinomi di L
    :param n            -- Numero di indici delle variabili
    :return (M,v)       -- Matrice e vettore del nostro sistema lineare da risolvere M*x = v
    """
    variables = ['y%s' % exp_to_index(exp_monomial) for exp_monomial in exp_list if str(exp_monomial) != '('+ '0, '*(n-1) + '0)']
    R = (L[0]).parent()
    G = R.base_ring()
    L_new = []
    const = []
    for p in L:
        coeff = []
        for v in variables:
            coeff.append(G(p.coefficient(R(v))))
        L_new.append(coeff)
        const.append(G(-p.coefficient(R('y' + '0_'*(n-1) + '0'))))
    return (Matrix(tuple(L_new)),vector(const))

def pick_values(n, q, alpha, C):
    """
    Sceglie il valore di d e del numero m di chiamate da fare all'oracolo per ottenere, con elevata probabilità, un sistema che possieda 
    un'unica soluzione (esatta).
    :param q                -- Ordine del campo finito in cui vivono gli elementi del vettore segreto
    :param n                -- Mumero di coordinate del vettore segreto
    :param alpha            -- Parametro della distribuzione gaussiana discreta con cui genero gli errori
    :param C                -- Moltiplicatore del numero di sample
    :return (d,m)           -- Coppia con d parametro che corrisponde all'upperbound stimato degli errori generati dall'oracolo e m numero di sample da richiedere
    """
    sigma = (alpha * q) / (sqrt(2 * RR(pi)))
    d = 4 * sigma^2 * RR(log(n))
    D = 2*d + 1
    m = C * binomial(n+D,n) * alpha * q^2 * RR(log(q))
    return (ceil(d),ceil(m))

def canonical_basis_exponent(j, n):
    """
    Ritorna la stringa associata allo j-simo della base canonica in un vettore di n componenti.
    i.e.: (j=2, n=5) --> (0, 1, 0, 0, 0)
    """
    s = '(' 
    for i in range(1,n):
        s = s + ('%d, ' % (i == j))
    s = s + ('%d)' % (n == j))
    return s

def balance(e, q=None):
    """
    Rappresenta l'oggetto e a termini in GL(q) prendendo i rappresentanti 
    dei suoi termini in [-(q-1)/2, ... , +(q-1)/2] invece che in [1, ... , q-1]
    """
    try:
        p = parent(e).change_ring(ZZ)
        return p([balance(e_) for e_ in e])
    except (TypeError, AttributeError):
        if q is None:
            try:
                q = parent(e).order()
            except AttributeError:
                q = parent(e).base_ring().order()
        return ZZ(e)-q if ZZ(e)>q/2 else ZZ(e)


def arora_ge_attack(q, n, alpha, C=1):
    """
    Dato un oracolo del problema LWE, ne recupera il suo vettore segreto
    :param q                -- Ordine del campo finito in cui vivono gli elementi del vettore segreto
    :param n                -- Mumero di coordinate del vettore segreto
    :param alpha            -- Parametro della distribuzione gaussiana discreta con cui genero gli errori
    :param C (= 1)          -- Moltiplicatore numero di sample
    :return u               -- Segreto dell'oracolo
    """
    if (q*alpha > sqrt(n)):
        warnings.warn("Il tasso di rumore del tuo oracolo è superiore alla soglia n^0.5: "+\
                      "l'algoritmo che stai eseguendo non ha complessità sub-esponenziale.")
        
    (d,m) = pick_values(n, q, alpha, C)    

    oracle_LWE = LWE(n=n, q=q, D=DiscreteGaussianDistributionIntegerSampler(alpha))
    G = GF(q)
    u = oracle_LWE._LWE__s
    print('Il segreto è: %s' % str(balance(u)))

    # Genero il sistema di polinomi {p(a_i*z + b_i)}_{i=1,...,n} dove z=[z1,...,zn] e p(t):=t(t-1)(t+1)...(t-d)(t+d)
    poly = LWE_polynomial(G, d)
    print('Chiamo l\'oracolo %d volte' % m)
    (polynomial_list,exp_list) = create_polynomials([poly]*m, n, oracle_LWE)

    L = linearize(polynomial_list, exp_list)
    print('Terminato il processo di linearizzazione! Ho ottenuto un sistema polinomiale in %d variabili' % (len(exp_list) - 1))

    # Risolvo il sistema
    print('Inizio a risolvere il sistema...')
    (M,c) = create_system(L, exp_list, n)
    soluzione = M \ c

    # Stampo vettore segreto estratto dalla soluzione sistema
    exp_list = [exp_monomial for exp_monomial in exp_list if str(exp_monomial) != '(' + '0, '*(n-1) + '0)']
    secret_vector= list([])
    for i in range(1, n+1):
        secret_vector.append(soluzione[exp_list.index(canonical_basis_exponent(i,n))])
    return balance(vector(secret_vector))