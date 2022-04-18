# coding=utf-8
from math import ceil
from random import randint
import warnings
import time

# Restituisco il polinomio p(t) := t(t+1)(t-1)...(t+d)(t-d)
def LWE_polynomial (q, d):
    F.<t> = GF(q)[]
    poly = GF(q)(1)*t
    for i in range(d):
        poly = poly*(t^2 - (i+1)^2)      
    return poly 

# Oracolo associato al nostro problema
# :param u              -> La chiave privata da recuperare
# :param alpha          -> Il parametro della distribuzione gaussiana discreta
# :param bool (= False) -> Se bool=True uso una distribuzione uniforme su [-d;+d] 
# :param d (= 1)        -> Se bool=True uso una distribuzione uniforme su [-d;+d] 
def oracle_LWE(u, alpha, bool=False, d=1):
    n = len(u)
    G = vector(u).base_ring()
    q = G.characteristic()
    V = G^n
    a = V.random_element()
    sigma = alpha*q
    if (bool == True):
        eta = G(randint(-d,d))
    else:
        N = RealDistribution('gaussian', sigma)
        r = round(N.get_random_element())
        eta = G(r)   
    b = a*u + eta
    return (a,b)

# Prende una lista di polinomi e li valuta in a_i*z + b_i, dove (a_i,b_i) sono coppie ottenute chiamando l'oracolo con parametro alpha
# :param R                  -- Anello polinomiale in cui vivono i polinomi p(a_i*z + b_i)
# :param l                  -- Lista di polinomi da valutare in a_i*z + b_i
# :param u                  -- Vettore segreto usato per generare le coppie (a_i,b_i)
# :param alpha              -- Parametro della distribuzione gaussiana discreta
# :param bool               -- Se bool=True, scelgo i b_i mediante una distribuzione uniforme su [-d; +d] 
# :param d                  -- Se bool=True, l'intervallo su cui vengono scelti i b_i è [-d; +d]
# :return (l_new,exp_set):
#         l_new             -- Polinomi nell'anello polinomiale R valutati in a*z+b 
#         exp_set           -- Insieme contenente tutti gli esponenti associati alle variabili z_i dei monomi dei polinomi di l
def create_polynomials(R, l, u, alpha, bool=False, d=1):
    n=len(u)

    p=R(1)      # Per sicurezza, nel caso non appaia nei polinomi, inserisco l'esponente associato al monomio costante 1
    exp_set = set()
    const_exp = ((p.dict()).popitem()) 
    exp_set.update([const_exp[0]])

    l_new = []  # Lista in cui inserire i nuovi polinomi 
    for p in l:
        (a,b) = oracle_LWE(u, alpha, bool, d)
        p = p(sum([-R(a[i])*R('z%d' % i) for i in range(n)])+b)
        l_new.append(p)
        dct = p.dict()
        n_monomials = len(dct)
        for i in range(n_monomials):      
            item = dct.popitem()
            exp_set.update([item[0]])

    return (l_new,exp_set)

# Converte la rappresentazione in tuple degli esponenti dei monomi in delle stringhe che posso usare come indici
# i.e.  e := (1,2,3,4) 
#       'y%s' % exp_to_index(e) -> y1_2_3_4
def exp_to_index(exp):
    s = str(exp)
    s = s.replace('(', '')      #Elimino parentesi
    s = s.replace(')', '')
    s = s.replace(', ', '_')    #Sostituisco virgole con underscore
    return s

# Linearizza una lista l di polinomi portandoli nell'anello polinomiale S
def linearize(S, L):  
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

# A partire dai polinomi linearizzati L genera la matrice del sistema lineare associata con i relativi termini noti 
# :param L                  -- Lista di polinomi con cui creare il sistema
# :param exp_list           -- Lista esponenti associati ai monomi presenti nei polinomi di L
# :param n                  -- Numero di indici delle variabili
# :return (M,v)             -- Matrice e vettore del nostro sistema lineare da risolvere M*x = v
def create_system(L, exp_list, n):
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

# Ritorna la stringa associata allo j-simo della base canonica in un vettore di n componenti
# i.e.: (2,5) -> (0, 1, 0, 0, 0) 
def canonical_basis_exponent(j, n):
    s = '(' 
    for i in range(1,n):
        s = s + ('%d, ' % (i == j))
    s = s + ('%d)' % (n == j))
    return s

# Sceglie il valore di d e del numero m di chiamate da fare all'oracolo per ottenere, con alta probabilità, un sistema che possiede 
# soluzione che corrisponda al vettore segreto.
# In particolare, sappiamo che se prendiamo e^(o(l^2)) sample la distribuzione del nostro oracolo avrà una probabilità di essere 
# maggiore di l*alpha*q trascurabile.
# Inoltre il nostro numero di sample deve essere O(binomial(n+d,n)*alpha*q^2*log(q)).
# ---
# La nostra scelta di d e m avviene scorrendo d come parametro intero e assumendo che:
#  - m = C*binomial(n+d,n)*alpha*q^2*log(q)
#  - m ≈ e^l = e^(o(l^2)) => d ≈ log(binomial(n+d,n)*alpha*q^2*log(q))*alpha*q 
# Prendiamo perciò tra i valori di d possibili quello che minimizza il rapporto tra d e log(binomial(n+d,n)*alpha*q^2*log(q))*alpha*q 
def pick_values(n, q, alpha, C):
    best_d = 1
    best_e = math.inf
    coeff = alpha*q^2*float(log(q))
    sigma = alpha*q
    for d in range(1, (q-1)/2):
        N = binomial(n+d, n)
        e = float(log(C*N*coeff))*sigma - d
        # Se e < 0 vuol dire che mi trovo in una distribuzione per cui, con alta probabilità, 
        # tutti i valori di eta che ottengo sono minori o uguali a d                         
        if e < 0:   
            best_d = d
            m = ceil(C*N*coeff)
            return(best_d,m)
        else:
            if e/d < best_e/best_d:
                best_d = d
                best_e = e
    m = ceil(C*binomial(n+best_d, n)*coeff)
    return (best_d,m)

# Dato un oracolo del problema LWE, ne recupera il suo vettore segreto
# :param q              -- Ordine del campo finito in cui vivono gli elementi del vettore segreto
# :param n              -- Mumero di coordinate del vettore segreto
# :param alpha          -- Parametro della distribuzione gaussiana discreta con cui genero gli errori
# :param C (= 1)        -- Coefficiente da inserire per calcolare il numero di sample
# :param bool (= False) -- Se bool=True, scelgo i b_i delle coppie (a_i,b_i) generate dall'oracolo mediante 
#                          una distribuzione uniforme su un intervallo [-d; +d]
# :return u             -- Vettore segreto dell'oracolo
def arora_ge_attack(q, n, alpha, C=1, bool = False):
    
    if (q*alpha > sqrt(n)):
        warnings.warn("Il tasso di rumore del tuo oracolo è superiore alla soglia n^0.5: "+\
                      "l'algoritmo che stai eseguendo non ha complessità sub-esponenziale.")
        
    (d,k) = pick_values(n, q, alpha, C)    
    # PER CONTROLLARE LA QUALITA' DEI PARAMETRI SCELTI:
    # print('k*alpha*q = %f' % (float(log(k))*alpha*q))
    # print('d = %d' % d) 

    R = PolynomialRing(GF(q), ['z%d' % i for i in range(n)])
    u = (GF(q)^n).random_element()
    print('Il vettore segreto è: %s' % str(list(u)))

    print('Chiamo l\'oracolo %d volte' % k)
    print('Upper bound del modulo dell\'errore: d = %d' % d)

    # Genero il sistema de polinomi in z p(a_i*z + b_i) dove p(t):=t(t-1)(t+1)...(t-d)(t+d)
    poly = LWE_polynomial(q, d)
    (polynomial_list,exp_list) = create_polynomials(R, [poly]*k, u, alpha, bool, d)
    # Anello polinomiale in cui vivranno i polinomi linearizzati
    S = PolynomialRing(GF(q),[('y%s' % exp_to_index(exp_monomial)) for exp_monomial in exp_list])
    # Converto gli esponenti in stringhe per lavorarci più facilmente
    exp_list = [str(exp) for exp in exp_list] 

    # Linearizzo il sistema di polinomi
    L = linearize(S, polynomial_list)
    print('Terminato il processo di linearizzazione!')
    print('Ho ottenuto un sistema polinomiale in %d variabili' % len(S.gens()))

    # Risolvo il sistema
    print('Inizio a risolvere il sistema...')
    start_time = time.time()
    (M,c) = create_system(L, exp_list, n)
    soluzione = M \ c
    print("--- %.2f secondi impiegati ---" % (time.time() - start_time))

    # Stampo vettore segreto estratto dalla soluzione sistema
    exp_list = [exp_monomial for exp_monomial in exp_list if str(exp_monomial) != '(' + '0, '*(n-1) + '0)']
    secret_vector= list([])
    for i in range(1, n+1):
        secret_vector.append(soluzione[exp_list.index(canonical_basis_exponent(i,n))])
    print('Vettore segreto recuperato: %s' % str(secret_vector))
    return vector(secret_vector)
