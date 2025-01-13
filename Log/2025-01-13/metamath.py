import sys

def assert_wff(w : str) -> str:
    """Comprobar que s es una fórmula bien formada (wff)"""
    """En caso de serlo, se retorna la fórmula"""

    #-- Comprobar si s es una wff
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

def debug_wff(w : str):
    """Imprimir la cadena wff"""
    print(f"• {w}")
    return

def w𝜑() -> str:
    """La variable 𝜑 es una fórmula bien formada (wff)"""

    #-- Crear la cadena wff
    w = f"wff 𝜑"

    #-- Retornar la cadena wff
    return w

def w𝜓() -> str:
    """La variable 𝜓 es una fórmula bien formada (wff)"""

    #-- Crear la cadena wff
    w = f"wff 𝜓"

    #-- Retornar la cadena wff
    return w

def w𝜒() -> str:
    """La variable 𝜒 es una fórmula bien formada (wff)"""

    #-- Crear la cadena wff
    w = f"wff 𝜒"

    #-- Retornar la cadena wff
    return w

def wp() -> str:
    """La proposición p es una fórmula bien formada (wff)"""

    #-- Crear la cadena wff
    w = f"wff p"

    #-- Retornar la cadena wff
    return w

def wq() -> str:
    """La proposición q es una fórmula bien formada (wff)"""

    #-- Crear la cadena wff
    w = f"wff q"

    #-- Retornar la cadena wff
    return w

def wr() -> str:
    """La proposición r es una fórmula bien formada (wff)"""

    #-- Crear la cadena wff
    w = f"wff r"

    #-- Retornar la cadena wff
    return w

def wi(wa : str, wc : str) -> str:
    """Si wa y wc son fórmulas bien formadas (wff), """
    """entonces (wa → wc) es una fórmula bien formada (wff)"""

    #-- Obtener la fórmula antecedente
    𝜑 = assert_wff(wa)
    
    #-- Obtener la fórmula consecuente
    𝜓 = assert_wff(wc)

    #-- Crear la cadena wff
    w = f"wff ( {𝜑} → {𝜓} )"
    
    return w

def theorem(w : str) -> str:
    """Afirmar que w es un teorema"""

    #-- Obtener la fórmula a convertir en teorema
    𝜑 = assert_wff(w)

    #-- Crear la formula teorema
    th = f"⊢ {𝜑}"

    return th

#-- FUNCIONES PARA TESTS UNITARIOS

def test_w𝜑():
    """Prueba la función w𝜑()"""
    
    #-- Verificar que la función w𝜑() retorne la cadena correcta
    assert w𝜑() == "wff 𝜑"
    print("✅️ w𝜑. Test 1")

def test_w𝜓():
    """Prueba la función w𝜓()"""
    
    #-- Verificar que la función w𝜓() retorne la cadena correcta
    assert w𝜓() == "wff 𝜓"
    print("✅️ w𝜓. Test 1")

def test_w𝜒():
    """Prueba la función w𝜒()"""
    
    #-- Verificar que la función w𝜓() retorne la cadena correcta
    assert w𝜒() == "wff 𝜒"
    print("✅️ w𝜒. Test 1")

def test_wp():
    """Prueba la función wp()"""
    
    #-- Verificar que la función wp() retorne la cadena correcta
    assert wp() == "wff p"
    print("✅️ wp. Test 1")

def test_wq():
    """Prueba la función wq()"""
    
    #-- Verificar que la función wq() retorne la cadena correcta
    assert wq() == "wff q"
    print("✅️ wq. Test 1")

def test_wr():
    """Prueba la función wr()"""
    
    #-- Verificar que la función wr() retorne la cadena correcta
    assert wr() == "wff r"
    print("✅️ wr. Test 1")

def test_wi():
    """Prueba la función wi()"""
    
    #-- Verificar que la función wi() retorne la cadena correcta
    assert wi("wff p", "wff q") == "wff ( p → q )"
    print("✅️ wi. Test 1")

    assert wi("wff 𝜑", "wff 𝜓")
    print("✅️ wi. Test 2")

    assert wi(wφ(), wψ()) == "wff ( 𝜑 → 𝜓 )"
    print("✅️ wi. Test 2")

    wff1 = wi(wφ(), wψ())
    wff2 = wi(wφ(), wff1)
    assert wff1 == "wff ( 𝜑 → 𝜓 )"
    assert wff2 == "wff ( 𝜑 → ( 𝜑 → 𝜓 ) )"
    print("✅️ wi. Test 3")

def test_theorem():
    """Prueba la función theorem()"""
    
    #-- Verificar que la función theorem() retorne la cadena correcta
    assert theorem("wff 𝜑") == "⊢ 𝜑"
    print("✅️ theorem. Test 1")

    assert theorem("wff ( 𝜑 → 𝜓 )") == "⊢ ( 𝜑 → 𝜓 )"
    print("✅️ theorem. Test 2")

    assert theorem(wi(wφ(), wψ())) == "⊢ ( 𝜑 → 𝜓 )"
    print("✅️ theorem. Test 3")

    assert theorem( wi(wφ(), wi(wφ(), wψ()) ) ) == "⊢ ( 𝜑 → ( 𝜑 → 𝜓 ) )"
    print("✅️ theorem. Test 4")

def ax_mp(wph : str, wps : str, min : str, maj : str) -> str:
    """Regla de inferencia ax-mp (Modus pones)"""

    #---- Comprobar el teorema min

    #-- 𝜑 es una wff
    #-- Guardamos la fórmula (sin el wff)
    𝜑 = assert_wff(wph)

    #-- ⊢ 𝜑 es un teorema
    #-- En fmin metemos la fórmula (sin el ⊢)
    fmin = assert_theorem(min)

    #-- fmin es ahora una wff
    fmin = wff(fmin)

    #-- Comprobar que las fórmulas son iguales
    assert fmin == wph

    # ---- Comprobar el teorema maj
    #-- 𝜓 es una wff
    #-- Guardamos la fórmula (sin el wff)
    𝜓 = assert_wff(wps)

    #-- ⊢ ( 𝜑 → 𝜓 ) es un teorema
    #-- Guardar en fmaj la formula (sin el ⊢)
    fmaj = assert_theorem(maj)

    #-- fmaj es ahora una wff
    fmaj = wff(fmaj)

    #-- Comprobar que fmaj es de la forma ( 𝜑 → 𝜓 )
    assert fmaj == wi(wph, wps)

    #-- Podemos asegurar, en este caso, que 𝜓 es un teorema
    return theorem(wps)


#-- Tests
print("-------Test unitarios-------")
print("-- Variables proposicionales: ")
test_wp()
test_wq()
test_wr()

print("-- Variables de fórmulas: ")
test_wφ()
test_wψ()
test_wχ()

print("-- Implicación: ")
test_wi()

print("Teorema: ")
test_theorem()

print()

print("------- Main---------")
wff1 = wφ()
wff2 = wψ()
wff3 = wχ()
debug_wff(wff1)
debug_wff(wff2)
debug_wff(wff3)

#-- Crear wff ( 𝜑 → 𝜓 )
w3 = wi(wff1, wff2)
debug_wff( w3 )

#-- Crear wff ( 𝜑 → ( 𝜑 → 𝜓 ) )
w4 = wi(wff1, w3)
debug_wff(w4)

#-- Crear wff ( p → q )
w5 = wi(wp(), wq())
debug_wff(w5)

#-- Crear teorema ⊢ ( 𝜑 )
w6 = theorem(wff1)
debug_wff(w6)

#-- Crear teorema ⊢ ( 𝜑 → 𝜓 )
w7 = theorem(w3)
debug_wff(w7)


#-- Prueba de ax-mp
print("--- MODUS PONEN ----")
wph = wφ()
wps = wψ()
min = theorem(wph)
maj = theorem( wi(wph,wps) )
debug_wff(wph)
debug_wff(wps)
print(min)
print(maj)
print(f"{"─"*len(maj)}")

#-- Aplicamos el axioma de modus ponens
th1 = ax_mp(wph, wps, min, maj)

#-- Mostrar la conclusion
print(th1)

#---- Otra prueba de ax-mp
print("--- MODUS PONEN ----")
mp2_wph = w𝜓()
mp2_wps = w𝜒()
min = theorem(mp2_wph)
maj = theorem( wi ( mp2_wph, mp2_wps) ) 
print(min)
print(maj)
th2 = ax_mp(
    mp2_wph, 
    mp2_wps, 
    min,
    maj
)

#-- Imprimir la conclusion
print(th2)

print()


