import sys

#-- Pila
stack = []

#-- Base de datos de teoremas
th_db = {
    #--------- Reglas de construccion -----
    "wn": {
        "hyp": ["wff 𝜑"],
        "conc": "wff ¬𝜑",
        "proof": ["wph", "wn"]
    },
    "wi": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "wff ( 𝜑 → 𝜓 )",
        "proof": ["wph", "wps", "wi"]
    },
    "ax-th": {
        "hyp": ["wff 𝜑"],
        "conc": "⊢ 𝜑",
        "proof": ["wph", "ax-th"]
    },
    #--------- AXIOMAS --------------------
    "ax-mp": {
        "hyp": ["wff 𝜑", "wff 𝜓",
                "⊢ 𝜑", "⊢ ( 𝜑 → 𝜓 )"],
        "conc": "⊢ 𝜓"
    },
    
    "ax-1": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → 𝜑 ) )",
        "proof": ["wph", "wps", "wph", "wi", "wi", "ax-th"]
    },
    "ax-2": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒"],
        "conc": "⊢ ( ( 𝜑 → ( 𝜓 → 𝜒 ) ) → ( ( 𝜑 → 𝜓 ) → ( 𝜑 → 𝜒 ) ) )",
        "proof": ["wph", "wps", "wch", "wi", "wi", "wph", "wps", "wi", "wph",
                  "wch", "wi", "wi", "wi", "ax-th"]
    },
    "ax-3": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( ¬𝜑 → ¬𝜓 ) → ( 𝜓 → 𝜑 ) )",
        "proof": ["wph", "wn", "wps", "wn", "wi", "wps", "wph", "wi", "wi",
                  "ax-th"]
    },
    #----------- TEOREMAS --------------------
    "mp2": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ 𝜑", "⊢ 𝜓", "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )"],
        "conc": "⊢ 𝜒",
        "proof": ["wps", "wch", "hyp.2", "wph", "wps", "wch", "wi", "hyp.1", 
                  "hyp.3", "ax-mp", "ax-mp"]
    },
    "mp2b": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ 𝜑", "⊢ ( 𝜑 → 𝜓 )", "⊢ ( 𝜓 → 𝜒 )"],
        "conc": "⊢ 𝜒",
        "proof": ["wps", "wch", "wph", "wps", "hyp.1", "hyp.2", "ax-mp",
                  "hyp.3", "ax-mp"]
    },
    "a1i": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ 𝜑"],
        "conc": "⊢ ( 𝜓 → 𝜑 )",
        "proof": ["wph", "wps", "wph", "wi", "hyp.1", "wph", "wps", "ax-1",
                  "ax-mp"]
    },
    "a2i": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( ( 𝜑 → 𝜓 ) → ( 𝜑 → 𝜒 ) )",
        "proof": ["wph", "wps", "wch", "wi", "wi", "wph", "wps", "wi", "wph", "wch",
         "wi", "wi", "hyp.1", "wph", "wps", "wch", "ax-2", "ax-mp"]
    },
}


def count_wff(wffs: list):
    """Obtener el numero de wffs en una lista"""

    #-- Inicialmente hay 0 formas
    cont = 0

    #-- Recorrer todas las formulas
    for f in wffs:

        #-- ¡Es una wff!
        if f.startswith("wff "):

            #-- Incrementar contador
            cont+=1

    #-- Retornar el contador
    return cont

def assert_wff(w : str) -> str:
    """Comprobar que w es una fórmula bien formada (wff)"""
    """En caso de serlo, se retorna la fórmula"""

    #-- Comprobar si w es una wff
    if w.startswith("wff "):
        w = w[4:]
    else:
        print(f"Error: {w} no es una fórmula bien formada (wff)")
        print()
        sys.exit(1)

    #-- Retornar la fórmula
    return w

def assert_theorem(th : str) -> str:
    """Comprobar que th es un teorema"""
    """En caso de serlo, se retorna la fórmula"""

    #-- Comprobar si th es un teorema
    if th.startswith("⊢ "):
        th = th[2:]
    else:
        print(f"Error: {th} no es un teorema")
        print()
        sys.exit(1)

    #-- Retornar la fórmula
    return th

def wff(w : str) -> str:
    """Convertir una cadena en una fórmula bien formada (wff)"""
    return f"wff {w}"

def theorem(w : str) -> str:
    """Afirmar que w es un teorema"""

    #-- Obtener la fórmula a convertir en teorema
    𝜑 = assert_wff(w)

    #-- Crear la formula teorema
    th = f"⊢ {𝜑}"

    return th

def wp():
    """La proposición p es una fórmula bien formada (wff)"""
    stack.append("wff p")

def wq():
    """La proposición q es una fórmula bien formada (wff)"""
    stack.append("wff q")

def wph():
    """La variable 𝜑 es una fórmula bien formada (wff)"""
    stack.append("wff 𝜑")

def wps():
    """La variable 𝜓 es una fórmula bien formada (wff)"""
    stack.append("wff 𝜓")

def wch():
    """La variable 𝜒 es una fórmula bien formada (wff)"""
    stack.append("wff 𝜒")

def wn(show_proof = False):
    """Si w es una fórmula bien formada (wff), """
    """entonces ¬w es una fórmula bien formada (wff) """

    #-- Leer formula de la pila
    w = stack.pop()

    #-- Obtener la fórmula
    𝜑 = assert_wff(w)

    #-- Crear la cadena wff resultante
    w = f"wff ¬{𝜑}"

    #-- Meterla en la pila
    stack.append(w)

def wi(show_proof = False):
    """Si wa y wc son fórmulas bien formadas (wff), """
    """entonces (wa → wc) es una fórmula bien formada (wff)"""

    # -- Leer el consecuente de la pila
    wc = stack.pop()

    # -- Leer el antecedente de la pila
    wa = stack.pop()

    #-- Obtener la fórmula antecedente
    𝜑 = assert_wff(wa)
    
    #-- Obtener la fórmula consecuente
    𝜓 = assert_wff(wc)

    #-- Crear la cadena wff
    w = f"wff ( {𝜑} → {𝜓} )"
    
    #-- Meterla en la pila
    stack.append(w)

def ax_th(show_proof = False):
    """Axioma de generacion de teoremas
    Si 𝜑 es una wff, entonces esta formula es un teorema:
    ⊢ 𝜑
    """
    #-- Obtener la hipotesis
    wph = stack.pop()

    #-- Comprobar que es una wff
    assert_wff(wph)

    #-- Obtener la conclusion
    conclusion = theorem(wph)

    #-- Meterla en la pila
    stack.append(conclusion)

def ax_mp(show_proof = False):
    """Regla de inferencia ax-mp (Modus pones)
       si 𝜑 y 𝜓 son wff
       si ⊢ 𝜑 y ⊢ (𝜑 → 𝜓 ) son teoremas, entonces
       ⊢ 𝜓 es un teorema
    """

    #-- Obtener las hipótesis
    maj = stack.pop()
    min = stack.pop()
    wps = stack.pop()
    wph = stack.pop()
    
    #-- Comprobar que las hipotesis son wff
    assert_wff(wph)  #-- wph es una wff
    assert_wff(wps)  #-- wps es una wff

    #-- ⊢ 𝜑 es un teorema
    #-- En fmin metemos la fórmula (sin el ⊢)
    fmin = assert_theorem(min)

    #-- fmin es ahora una wff
    fmin = wff(fmin)

    #-- Comprobar que las fórmulas son iguales
    assert fmin == wph

    #-- ⊢ ( 𝜑 → 𝜓 ) es un teorema
    #-- Guardar en fmaj la formula (sin el ⊢)
    fmaj = assert_theorem(maj)

    #-- fmaj es ahora una wff
    fmaj = wff(fmaj)

    #-- Comprobar que fmaj es de la forma ( 𝜑 → 𝜓 )
    stack.append(wph)
    stack.append(wps)
    wi()
    assert fmaj == stack.pop()

    #-- Conclusion
    #-- Podemos asegurar, en este caso, que 𝜓 es un teorema
    conclusion = theorem(wps)

    #-- Meterla en la pila
    stack.append(conclusion)
    
def ax_1(show_proof=False):
    """Axioma de Simplificacion
       si 𝜑 y 𝜓 son wff, entonces esta formula es un teorema
       ⊢ (𝜑 → (𝜓 → 𝜑))
    """

    #-- Obtener las hipótesis
    proof_theorems(th_db["ax-1"]["proof"],2,2)
    

def ax_2(show_proof=False):
    """Axioma de Frege
    si 𝜑, 𝜓 y 𝜒 son wffs, entonces esta formula es un teorema
    ⊢ ((𝜑 → (𝜓 → 𝜒)) → ((𝜑 → 𝜓) → (𝜑 → 𝜒)))
    """

    #-- Obtener las hipótesis
    proof_theorems(th_db["ax-2"]["proof"],3,3)


def ax_2_old(show_proof=False):
    """Axioma de Frege
    si 𝜑, 𝜓 y 𝜒 son wffs, entonces esta formula es un teorema
    ⊢ ((𝜑 → (𝜓 → 𝜒)) → ((𝜑 → 𝜓) → (𝜑 → 𝜒)))
    """

    #-- Obtener las hipótesis
    wch = stack.pop()
    wps = stack.pop()
    wph = stack.pop()
    
    #-- Comprobar que las hipotesis son wff
    assert_wff(wph)  #-- wph es una wff
    assert_wff(wps)  #-- wps es una wff
    assert_wff(wch)  #-- wch es una wff

    #-- Demostracion: Construir el teorema
    step_1 = wph         # wff 𝜑
    stack.append(step_1)

    step_2 = wps         # wff 𝜓
    stack.append(step_2)

    step_3 = wch
    stack.append(step_3) # wff 𝜒

    wi()
    step_4 = stack[-1]   # wff (𝜓 → 𝜒)

    wi()
    step_5 = stack[-1]   # wff (𝜑 → (𝜓 → 𝜒))

    stack.append(step_1)
    stack.append(step_2)
    wi()
    step_6 = stack[-1]   #  wff (𝜑 → 𝜓)

    stack.append(step_1)  # wff (𝜑 → 𝜒)
    stack.append(step_3)
    wi() 
    step_7 = stack[-1]

    wi()
    step_8 = stack[-1]  # wff ((𝜑 → 𝜓) → (𝜑 → 𝜒))

    wi()
    step_9 = stack[-1]  # wff ((𝜑 → (𝜓 → 𝜒)) → ((𝜑 → 𝜓) → (𝜑 → 𝜒)))

    step_10 = theorem(step_9)
    stack.append(step_10)

    if (show_proof):
        print("\n🟢️ Paso 1: wff 𝜑")
        print(step_1)
        print ("\n🟢️ Paso 2: wff 𝜓")
        print(step_2)
        print ("\n🟢️ Paso 3: wff 𝜒")
        print(step_3)
        print ("\n🟢️ Paso 4: wi")
        print(step_4)
        print ("\n🟢️ Paso 5: wi")
        print(step_5)
        print ("\n🟢️ Paso 6: wi")
        print(step_6)
        print ("\n🟢️ Paso 7: wi")
        print(step_7)
        print ("\n🟢️ Paso 8: wi")
        print(step_8)
        print ("\n🟢️ Paso 9: wi")
        print(step_9)
        print ("\n🟢️ Paso 10: Es Axioma")
        print (step_10)

def mp2(show_proof=False):
    """Teorema mp2:
       hypostesis:
         wff 𝜑, wff 𝜓, wff 𝜒
         ⊢ 𝜑               (mp2_1)
         ⊢ 𝜓               (mp2_2)
         ⊢ (𝜑 → (𝜓 → 𝜒))  (mp2_3)
       conclusion:
         ⊢ 𝜒
    """
    #-- Obtener las hipótesis
    mp2_3 = stack.pop()
    mp2_2 = stack.pop()
    mp2_1 = stack.pop()
    wch = stack.pop()
    wps = stack.pop()
    wph = stack.pop()

    hyp_1 = mp2_1
    hyp_2 = mp2_2
    hyp_3 = mp2_3

    print("=============")
    stack.append(wps)
    stack.append(wch)
    stack.append(hyp_2)
    stack.append(wph)
    stack.append(wps)
    stack.append(wch)
    exec("wi")
    stack.append(hyp_1)
    stack.append(hyp_3)
    exec("ax-mp")
    exec("ax-mp")
    print_top()
    print(stack)

    """
    wps wch mp2.2 wph wps wch wi hyp.1 mp2.3 ax-mp ax-mp
    """
    
def mp2b(show_proof=False):
    """Teorema mp2b
       Hypotesis:
         wff 𝜑, wff 𝜓, wff 𝜒
         ⊢ 𝜑          (mp2b_1)
         ⊢ ( 𝜑 → 𝜓 )  (mp2b_2)
         ⊢ ( 𝜓 → 𝜒 )  (mp2b_3)
       Conclusion:
         ⊢ 𝜒
    """
    pass

def print_top():
    """Print the current formula (at the top of stack)"""

    #-- Leer la cima de la pila (sin consumir)
    w = stack[-1]

    #-- Imprimir la fórmula!
    print(w)

def exec(name: str, show_proof=False):
    """Ejecutar el teorema a partir de su nombre"""

    #-- Obtener el nombre de la función asociada
    #-- Los caracteres '-' y '.' se convierten a '_'
    #-- Ya que los nombres de las funciones no pueden tener '-' ni '.'
    func = globals()[name.replace("-", "_").replace(".", "_")]

    #-- Ejecutar el teorema!
    func(show_proof)

def proof(ths: list[str]):
    """Proof a lists of theorems"""

    for th in ths:
        exec(th)

def print_theorem(name: str):
    """Imprimir un teorema"""

    #-- Primero se imprimen las hipotesis
    for hyp in th_db[name]["hyp"]:
        print(hyp)

    #-- Calcular el tamaño de la hipotesis mas larga
    tam = max([len(hyp) for hyp in th_db[name]["hyp"]])

    #-- Calcular el tamaño maximo de cualquier formula
    #-- (hipotesis + conclusion)
    tam = max(tam, len(th_db[name]["conc"]))

    #-- Imprimir linea horizontal
    #-- Su tamano es igual al de la cadena mas larga
    print(f"{"─" * tam}") 

    #-- Imprimir la conclusion
    print(th_db[name]["conc"])


def proof_theorems(proof: list[str], nh_orig: int, wffs: int, 
                   show_proof=False):
    """Probar una lista de teoremas
       nh_orig: Numero de hipotesis del teorema original
       wffs: Numero de wffs
    """

    #-- Leer las hipotesis del teorema original, de la pila
    #-- Se meten en la lista hyp_orig
    hyp_orig = []
    for i in range(nh_orig):
        hyp_orig.insert(0, stack[-1-i])
        #hyp_orig.insert(0, stack.pop())

    #-- DEBUG: Vaciar la pila...
    for i in range(nh_orig):
        stack.pop()


    #-- Recorrer la lista de teoremas de una prueba
    for step,name in enumerate(proof, 1):

        if (show_proof):
            print(f"\n🟢️ Paso {step}: {name}")

        #-- TODO 🚧: REFACTOR!! Eliminar los IFs!!!

        #-- Caso especial: Meter hipotesis 1 en la pila
        if name == "wph":
            stack.append(hyp_orig[0])
            if (show_proof):
                print_top()
            continue

        #-- Caso especial: Meter hipotesis 2 en la pila
        if name == "wps":
            stack.append(hyp_orig[1])
            if (show_proof):
                print_top()
            continue

        #-- Caso especial: Meter hipotesis 3 en la pila
        if name == "wch":
            stack.append(hyp_orig[2])
            if (show_proof):
                print_top()
            continue

        #-- Caso especial: teorema hip. 1
        if name == "hyp.1":
            stack.append(hyp_orig[wffs])
            if (show_proof):
                print_top()
            continue

        #-- Caso especial: teorema hip. 2
        if name == "hyp.2":
            stack.append(hyp_orig[wffs+1])
            if (show_proof):
                print_top()
            continue

        #-- Caso especial: teorema hip. 3
        if name == "hyp.3":
            stack.append(hyp_orig[wffs+2])
            if (show_proof):
                print_top()
            continue



        hyp = []  #-- Lista para lectura de las hipotesis

        #-- Obtener Numero de hipotesis del paso actual
        nh = len(th_db[name]["hyp"])

        #print(f"Hyp: {nh}")

        #-- Obtener las hipotesis de la pila 
        #-- y depositarlas en la lista hyp
        #-- NO se eliminan de la pila
        for i in range(nh):
          hyp.insert(0, stack[-1-i])

        #-- Ejecutar el teorema
        exec(name)

        if (show_proof):
            #-- Mostrar las hipotesis
            for i, h in enumerate(hyp, 1):
                print(f"{h}")

        #-- Leer la conclusion y meterla en hyp para calcular
        #-- su longitud
        hyp.append(stack[-1])

        #-- Calcular el tamaño de la fórmula mas larga
        #-- (hipotesis + conclusion)
        tam = max([len(f) for f in hyp])

        #-- Imprimir linea horizontal
        if (show_proof):
            print("─" * tam)

        #-- Imprimir la conclusion
        if (show_proof):
            print_top()


def check_theorem(name: str, show_proof=False):
    """Comprobar el teorema dado por su nombre en metamath"""

    print(f"\n───────────────┤ TEOREMA {name} ├────────────────")

    #-- Mostrar el teorema
    print_theorem(name)
    
    #-- Meter las hipotesis en la pila
    for h in th_db[name]["hyp"]:
        stack.append(h)

    #-- Obtener el numero de wffs
    wffs = count_wff(th_db[name]["hyp"])

    #-- Obtener el numero total de hipotesis (wffs + ths)
    nhyp = len(th_db[name]["hyp"])

    #-- Comprobar si el teorema tiene prueba
    if "proof" in th_db[name]:
        proof_theorems(th_db[name]["proof"], nhyp, wffs, show_proof)
    else:
        #-- No hay prueba: Ejecutar el teorema
        exec(name, show_proof)

    #-- Extraer la conclusion de la pila
    conclusion = stack.pop()

    #-- Verificar si la conclusión es correcta
    if conclusion == th_db[name]["conc"]:
        print ("✅️ Prueba correcta")
    else:
        print("❌️ Prueba incorrecta")
        print(conclusion)
        print(th_db[name]["conc"])


print()
#check_theorem("wn", True)
#check_theorem("wi", True)
#check_theorem("ax-th", True)
#check_theorem("ax-mp", True)
#check_theorem("ax-1", True)
#check_theorem("ax-2", True)
#check_theorem("ax-3", True)
#check_theorem("mp2", True)
#check_theorem("mp2b", True)
#check_theorem("a1i", True)
check_theorem("a2i", True)


print("----------------")
sys.exit(0)

name = "a2i"

#-- Meter las hipotesis en la pila
for h in th_db[name]["hyp"]:
    stack.append(h)

#-- Obtener el numero de wffs
wffs = count_wff(th_db[name]["hyp"])

#-- Obtener el numero total de hipotesis (wffs + ths)
nhyp = len(th_db[name]["hyp"])

proof = ["wph", "wps", "wch", "wi", "wi", "wph", "wps", "wi", "wph", "wch",
         "wi", "wi", "hyp.1", "wph", "wps", "wch", "ax-2", "ax-mp"]

proof_theorems(proof, nhyp, wffs, True)
print(stack)


print()
 
"""
""" 
