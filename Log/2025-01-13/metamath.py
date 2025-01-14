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

#-- Construccion de fórmulas

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

#------- Axiomas
def ax_mp(wph : str, wps : str, min : str, maj : str, debug=False) -> str:
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

    #-- Conclusion
    #-- Podemos asegurar, en este caso, que 𝜓 es un teorema
    conclusion = theorem(wps)

    #-- Si estamos en modo DEBUG, se imprimen las premisas y las conclusiones
    if (debug):
        print("══════════")
        print("🟢️ ax-mp: ")
        #debug_wff(wph)
        #debug_wff(wps)  
        print(min)  
        print(maj)  
        print(f"{"─"*len(maj)}") #-- Dibujar linea
        print(conclusion)
        print()

    #-- Devolver el teorema conclusión
    return conclusion

def ax_1(wph: str, wps: str, debug=False) -> str:
    """Axioma de Simplificacion
       si 𝜑 y 𝜓 son wff, entonces esta formula es un teorema
       ⊢ (𝜑 → (𝜓 → 𝜑))
    """

    # -- wph es una wff
    assert_wff(wph)

    # -- wps es una wff
    assert_wff(wps)

    # -- Construir el teorema
    conclusion = theorem (wi (wph, wi (wps, wph)))

    #-- Modo debug
    if (debug):
        print("══════════")
        print("🟢️ ax-1: ")
        debug_wff(wph)
        debug_wff(wps)
        print(f"{"─"*len(conclusion)}") #-- Dibujar linea
        print(conclusion)
        print()

    return conclusion

#------- TEOREMAS
def mp2(
        #-- wff
        wph : str, wps: str, wch : str,

        #-- Teoremas hipótesis
        mp2_1: str,  #-- ⊢ 𝜑 
        mp2_2: str,  #-- ⊢ 𝜓
        mp2_3: str   #-- ⊢ (𝜑 → (𝜓 → 𝜒))
        ) -> str: 
    
    print()
    print("───────────────┤ TEOREMA mp2 ├────────────────")

    #-- Teorema
    #• wff 𝜑
    #• wff 𝜓
    #• wff 𝜒
    print("""\
⊢ 𝜑
⊢ 𝜓
⊢ (𝜑 → (𝜓 → 𝜒))
───────────────
⊢ 𝜒
""")

    """
     Demostracion en Metamath:     
     1 wps           $f wff ps
     2 wch           $f wff ch
     3 mp2.2         $e |- ps
     4 wph           $f wff ph
     5 wps           $f wff ps
     6 wch           $f wff ch
     7 5,6 wi        $a wff ( ps -> ch )
     8 mp2.1         $e |- ph
     9 mp2.3         $e |- ( ph -> ( ps -> ch ) )
    10 4,7,8,9 ax-mp  $a |- ( ps -> ch )
    11 1,2,3,10 ax-mp  $a |- ch
    """

    # -- Debug
    # print("HIPOTESIS:")
    # debug_wff(wph)
    # debug_wff(wps)
    # debug_wff(wch)
    # print(f"• mp2.1: {mp2_1}")
    # print(f"• mp2.2: {mp2_2}")
    # print(f"• mp2.3: {mp2_3}")
    # print()

    print("📜️ Paso 1:")
    step_1  = ax_mp(wph,            # • wff 𝜑
                    wi(wps, wch),   # • wff ( 𝜓 → 𝜒 )
                    mp2_1,          # ⊢ 𝜑
                    mp2_3,          # ⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )
                    debug=True)  
                        # Conclusion: ⊢ ( 𝜓 → 𝜒 )

    print("📜️ Paso 2:")
    step_2 = ax_mp(wps,             # • wff 𝜓
                   wch,             # • wff 𝜒
                   mp2_2,           # ⊢ 𝜓
                   step_1,          # ⊢ ( 𝜓 → 𝜒 )
                   debug=True)
                       # Conclusion: ⊢ 𝜒
    
    conclusion = step_2

    #-- Debug
    #print("══════════")
    #print("RESUMEN: ")
    #print(f"{mp2_1}")
    #print(f"{mp2_2}")
    #print(f"{mp2_3}")
    #print(f"{"─"*len(mp2_3)}") #-- Dibujar linea
    #print(conclusion)
    #print()

    return conclusion

def mp2b(#-- wff
        wph : str, wps: str, wch : str,

        #-- Teoremas hipótesis
        mp2b_1: str,  #-- ⊢ 𝜑 
        mp2b_2: str,  #-- ⊢ ( 𝜑 → 𝜓 )
        mp2b_3: str   #-- ⊢ ( 𝜓 → 𝜒 )
        ) -> str:
    
    # https://us.metamath.org/mpeuni/mp2b.html
    print("───────────────┤ TEOREMA mp2b ├────────────────")

    #-- Teorema
    #• wff 𝜑
    #• wff 𝜓
    #• wff 𝜒
    print("""\
⊢ 𝜑
⊢ ( 𝜑 → 𝜓 )
⊢ ( 𝜓 → 𝜒 )
───────────────
⊢ 𝜒 
""")
    
    """
    Demostracion en Metamath:
    1 wps            # • wff 𝜓
    2 wch            # • wff 𝜒
    3 wph            # • wff 𝜑
    4 wps            # • wff 𝜓
    5 mp2b.1         # ⊢ 𝜑
    6 mp2b.2         # ⊢ ( 𝜑 → 𝜓 )
    7 3,4,5,6 ax-mp  # ⊢ 𝜓
    8 mp2b.3         # ⊢ ( 𝜓 → 𝜒 )
    9 1,2,7,8 ax-mp  # ⊢ 𝜒
    """

    #-- Debug
    #print("HIPOTESIS:")
    #debug_wff(wph)
    #debug_wff(wps)
    #debug_wff(wch)
    #print(f"• mpb2.1: {mp2b_1}")
    #print(f"• mpb2.2: {mp2b_2}")
    #print(f"• mpb2.3: {mp2b_3}")
    #print()

    print("📜️ Paso 1:")
    step_1 = ax_mp(wφ(),          # • wff 𝜑
                   wψ(),          # • wff 𝜓
                   mp2b_1,        # ⊢ 𝜑
                   mp2b_2,        # ⊢ ( 𝜑 → 𝜓 )
                   debug = True) 
                      # Conclusion: ⊢ 𝜓

    print("📜️ Paso 2:")
    step_2 = ax_mp(wψ(),          # • wff 𝜓
                   wχ(),          # • wff 𝜒
                   step_1,        # ⊢ 𝜓
                   mp2b_3,        # ⊢ ( 𝜓 → 𝜒 )
                   debug = True)
                      # Conclusion: ⊢ 𝜒
    conclusion = step_2

    #-- Debug
    #print("══════════")
    #print("RESUMEN: ")
    #print(f"{mp2b_1}")
    #print(f"{mp2b_2}")
    #print(f"{mp2b_3}")
    #print(f"{"─"*len(mp2b_3)}") #-- Dibujar linea
    #print(conclusion)
    #print()

    return conclusion

def a1i(wph: str, wps: str,  #-- wff
        
        #-- Hipotesis
        a1i_1: str  # ⊢ 𝜑 
        ) -> str:

    # https://us.metamath.org/mpeuni/a1i.html
    print("───────────────┤ TEOREMA a1i ├────────────────")

    #-- Teorema
    #• wff 𝜑
    #• wff 𝜓
    print("""\
⊢ 𝜑
────────────
⊢ ( 𝜓 → 𝜑 )
""")

    """
    1 wph            $f wff ph
    2 wps            $f wff ps
    3 wph            $f wff ph
    4 2,3 wi         $a wff ( ps -> ph )
    5 a1i.1          $e |- ph
    6 wph            $f wff ph
    7 wps            $f wff ps
    8 6,7 ax-1       $a |- ( ph -> ( ps -> ph ) )
    9 1,4,5,8 ax-mp  $a |- ( ps -> ph )
    """

    print("📜️ Paso 1:")
    step_1 = ax_1(wph,          # • wff 𝜑
                  wps,          # • wff 𝜓
                  debug=True)
                    # Conclusion: ⊢ ( 𝜑 → ( 𝜓 → 𝜑 ) )

    print("📜️ Paso 2:")
    step_2 = ax_mp(wph,           # • wff 𝜑
                   wi(wps, wph),  # • wff ( 𝜓 → 𝜑 )
                   a1i_1,  # ⊢ 𝜑
                   step_1,        # ⊢ ( 𝜑 → ( 𝜓 → 𝜑 ) )
                   debug=True)
                    # Conclusion:   ⊢ ( 𝜓 → 𝜑 )

    conclusion = step_2

    #-- Debug
    #print("══════════")
    #print("RESUMEN: ")
    #print(f"{a1i_1}")
    #print(f"{"─"*len(conclusion)}") #-- Dibujar linea
    #print(conclusion)
    #print()

    return conclusion


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

def test_ax_mp():
    """Prueba del axioma ax_mp"""

    assert ax_mp("wff 𝜑", "wff 𝜓", "⊢ 𝜑", "⊢ ( 𝜑 → 𝜓 )") == "⊢ 𝜓"
    print("✅️ ax-mp. Test 1")

    assert ax_mp("wff 𝜓", "wff 𝜒", "⊢ 𝜓", "⊢ ( 𝜓 → 𝜒 )") == "⊢ 𝜒"
    print("✅️ ax-mp. Test 2")

    assert ax_mp("wff 𝜑", "wff ( 𝜓 → 𝜒 )", 
                 "⊢ 𝜑", "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )") == "⊢ ( 𝜓 → 𝜒 )"
    print("✅️ ax-mp. Test 3")
    
    assert ax_mp("wff ( 𝜑 → 𝜒 )", "wff ( 𝜓 → 𝜑 )",
                  "⊢ ( 𝜑 → 𝜒 )", 
                  "⊢ ( ( 𝜑 → 𝜒 ) → ( 𝜓 → 𝜑 ) )") == "⊢ ( 𝜓 → 𝜑 )"
    print("✅️ ax-mp. Test 4")

    wph = wφ()
    wps = wψ()
    min = theorem(wph)
    maj = theorem( wi(wph,wps) )
    assert ax_mp(wph, wps, min, maj) == "⊢ 𝜓"
    print("✅️ ax-mp. Test 5")

    wph = w𝜓()
    wps = w𝜒()
    min = theorem(wph)
    maj = theorem( wi ( wph, wps) ) 
    assert ax_mp(wph, wps, min, maj) == "⊢ 𝜒"
    print("✅️ ax-mp. Test 6")

    wph = wφ()
    wps = wi( w𝜓(), w𝜒())
    min = theorem(wph)
    maj = theorem( wi ( wph, wps) ) 
    assert ax_mp(wph, wps, min, maj) == "⊢ ( 𝜓 → 𝜒 )"
    print("✅️ ax-mp. Test 7")

    wph = wi (wφ(), w𝜒())
    wps = wi( w𝜓(), w𝜒())
    min = theorem(wph)
    maj = theorem( wi ( wph, wps) ) 
    assert ax_mp(wph, wps, min, maj) == "⊢ ( 𝜓 → 𝜒 )"
    print("✅️ ax-mp. Test 8")

def test_ax_1():
    """Prueba del axioma ax_1"""

    assert ax_1("wff 𝜑", "wff 𝜓") == "⊢ ( 𝜑 → ( 𝜓 → 𝜑 ) )"
    print("✅️ ax-1. Test 1")

    assert ax_1("wff 𝜓", "wff 𝜒") == "⊢ ( 𝜓 → ( 𝜒 → 𝜓 ) )"
    print("✅️ ax-1. Test 2")

    assert ax_1("wff 𝜑", "wff ( 𝜓 → 𝜒 )") == "⊢ ( 𝜑 → ( ( 𝜓 → 𝜒 ) → 𝜑 ) )"
    print("✅️ ax-1. Test 3")

    assert ax_1("wff ( 𝜑 → 𝜒 )", "wff ( 𝜓 → 𝜑 )") == \
                "⊢ ( ( 𝜑 → 𝜒 ) → ( ( 𝜓 → 𝜑 ) → ( 𝜑 → 𝜒 ) ) )"
    print("✅️ ax-1. Test 4")

    assert ax_1(wφ(), wψ()) == "⊢ ( 𝜑 → ( 𝜓 → 𝜑 ) )"
    print("✅️ ax-1. Test 5")

    assert ax_1(w𝜓(), w𝜒()) == "⊢ ( 𝜓 → ( 𝜒 → 𝜓 ) )"
    print("✅️ ax-1. Test 6")

    assert ax_1(wφ(), wi( w𝜓(), w𝜒())) == "⊢ ( 𝜑 → ( ( 𝜓 → 𝜒 ) → 𝜑 ) )"
    print("✅️ ax-1. Test 7")    
   
    wph = wi (wφ(), w𝜒())
    wps = wi( w𝜓(), w𝜒())
    assert ax_1(wph, wps) == "⊢ ( ( 𝜑 → 𝜒 ) → ( ( 𝜓 → 𝜒 ) → ( 𝜑 → 𝜒 ) ) )"
    print("✅️ ax-1. Test 8")

def unittest():
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

    print("--Teorema: ")
    test_theorem()

    print("-- ax-mp:")
    test_ax_mp()

    print("-- ax-1:")
    test_ax_1()

    print()

#--- DEMOS DE USO
def demo_wff():

    print("---- Generando wffs ----")
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

    print()

def demo_ax_mp():
    #-- Prueba de ax-mp
    print("--- MODUS PONENS ----")

    #---- PRUEBA 1
    #-- Premisas
    wph = wφ()
    wps = wψ()
    min = theorem(wph)
    maj = theorem( wi(wph,wps) )

    #-- Conclusión
    ax_mp(wph, wps, min, maj, debug=True)
    print()

    #----- PRUEBA 2
    wph = w𝜓()
    wps = w𝜒()
    min = theorem(wph)
    maj = theorem( wi ( wph, wps) ) 
    ax_mp(wph, wps, min, maj, debug=True)
    print()

    #------ PRUEBA 3
    wph = wφ()
    wps = wi( w𝜓(), w𝜒())
    min = theorem(wph)
    maj = theorem( wi ( wph, wps) ) 
    ax_mp(wph, wps, min, maj, debug=True)
    print()

    #----- PRUEBA 4
    wph = wi (wφ(), w𝜒())
    wps = wi( w𝜓(), wφ())
    min = theorem(wph)
    maj = theorem( wi ( wph, wps) ) 
    ax_mp(wph, wps, min, maj, debug=True)
    print()

#--- Comprobar teoremas
def check_mp2():
    
    wph = wφ()
    wps = w𝜓()
    wch = w𝜒()
    mp2_1 = theorem(wph)                    # ⊢ 𝜑 
    mp2_2 = theorem(wps)                    # ⊢ 𝜓
    mp2_3 = theorem(wi(wph, wi(wps, wch)))  # ⊢ (𝜑 → (𝜓 → 𝜒))
                                            #─────────────────
    mp2(wph, wps, wch, mp2_1, mp2_2, mp2_3) # ⊢ 𝜒

def check_mp2b():

    wph = wφ()
    wps = w𝜓()
    wch = w𝜒()
    h1 = theorem(wph)                    # ⊢ 𝜑 
    h2 = theorem(wi(wph, wps))           # ⊢ ( 𝜑 → 𝜓 )
    h3 = theorem(wi(wps, wch))           # ⊢ ( 𝜓 → 𝜒 )
                                         #─────────────────
    mp2b(wph, wps, wch, h1, h2, h3)      # ⊢ 𝜒

def check_a1i():
    wph = wφ()        
    wps = w𝜓()       
    h1 = theorem(wph)   # ⊢ 𝜑
                        #──────
    a1i(wph, wps, h1)   # ⊢ (𝜓 → 𝜑)

#--------------------- MAIN ------------------
#-- Tests
#unittest()

#print("------- Main---------")
#demo_wff()
#demo_ax_mp()

#------------- TEOREMAS
print()
#check_mp2()
#check_mp2b()
check_a1i()

print()

