import sys
from collections.abc import Callable

#-- Base de datos con los Teoremas
th = {
    "ax-1": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → 𝜑 ) )"
    },
    "ax-2": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒"],
        "conc": "⊢ ( ( 𝜑 → ( 𝜓 → 𝜒 ) ) → ( ( 𝜑 → 𝜓 ) → ( 𝜑 → 𝜒 ) ) )"
    },
    "ax-3": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( ¬𝜑 → ¬𝜓 ) → ( 𝜓 → 𝜑 ) )"
    },
    "mp2": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "⊢ 𝜑", "⊢ 𝜓", "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )"],
        "conc": "⊢ 𝜒"
    },
    "mp2b": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ 𝜑", "⊢ ( 𝜑 → 𝜓 )", "⊢ ( 𝜓 → 𝜒 )"],
        "conc": "⊢ 𝜒"
    },
    "a1i": {
        "hyp": ["wff 𝜑", "wff 𝜓", "⊢ 𝜑"],
        "conc": "⊢ ( 𝜓 → 𝜑 )"
    },
    "a2i": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( ( 𝜑 → 𝜓 ) → ( 𝜑 → 𝜒 ) )"
    },
    "mpd": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → 𝜓 )",
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )"
    },
    "id": {
        "hyp": ["wff 𝜑"],
        "conc":"⊢ ( 𝜑 → 𝜑 )"
    },
    "con4": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc":"⊢ ( ( ¬𝜑 → ¬𝜓 ) → ( 𝜓 → 𝜑 ) )"
    },
    "syl": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( 𝜑 → 𝜓 )", "⊢ ( 𝜓 → 𝜒 )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )"
    },
    "con4d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( ¬𝜓 → ¬𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜒 → 𝜓 ) )"                
    },
    "a1d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( 𝜑 → 𝜓 )"],
        "conc": "⊢ ( 𝜑 → ( 𝜒 → 𝜓 ) )"
    }
}


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

def wn(w: str) -> str:
    """Si w es una fórmula bien formada (wff), """
    """entonces ¬ w es una fórmula bien formada (wff) """

    #-- Obtener la fórmula
    𝜑 = assert_wff(w)

    #-- Crear la cadena wff resultante
    w = f"wff ¬{𝜑}"

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

def ax_1(hyp: list, show_proof = False) -> str:
    """Axioma de Simplificacion
       si 𝜑 y 𝜓 son wff, entonces esta formula es un teorema
       ⊢ (𝜑 → (𝜓 → 𝜑))
    """

    # https://us.metamath.org/mpeuni/ax-1.html
    
    #-- Obtener las hipótesis
    wph, wps = hyp

    #-- Comprobar que las hipotesis son wff
    assert_wff(wph)  #-- wph es una wff
    assert_wff(wps)  #-- wps es una wff

    #-- Demostracion: Construir el teorema
    step_1 = wph
    step_2 = wps
    step_3 = wi (wps, wph)
    step_4 = wi(wph, step_3)
    step_5 = theorem(step_4)
    
    if (show_proof):
        print("\n🟢️ Paso 1: wff 𝜑")
        print(step_1)
        print ("\n🟢️ Paso 2: wff 𝜓")
        print(step_2)
        print ("\n🟢️ Paso 3: wi")
        print(step_3)
        print ("\n🟢️ Paso 4: wi")
        print(step_4)
        print ("\n🟢️ Paso 5: Es Axioma")
        print (step_5)

    conclusion = step_5
    return conclusion

def ax_2(hyp: list, show_proof = False) -> str:
    """Axioma de Frege
    si 𝜑, 𝜓 y 𝜒 son wffs, entonces esta formula es un teorema
    ⊢ ((𝜑 → (𝜓 → 𝜒)) → ((𝜑 → 𝜓) → (𝜑 → 𝜒)))
    """

    # https://us.metamath.org/mpeuni/ax-2.html

    #-- Obtener las hipótesis
    wph, wps, wch = hyp

    #-- Comprobar que las hipotesis son wff
    assert_wff(wph)  #-- wph es una wff
    assert_wff(wps)  #-- wps es una wff
    assert_wff(wch)  #-- wch es una wff

    #-- Demostracion: Construir el teorema
    step_1 = wph
    step_2 = wps
    step_3 = wch
    step_4 = wi(wps, wch)
    step_5 = wi(wph, step_4)
    step_6 = wi(wph, wps)
    step_7 = wi(wph, wch)
    step_8 = wi(step_6, step_7)
    step_9 = wi(step_5, step_8)
    step_10 = theorem(step_9)

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
        print(step_10)

    
    conclusion = step_10
    return conclusion

def ax_3(hyp: list, show_proof = False) -> str:
    """Axiom Transposicion
    si 𝜑 y 𝜓  son wffs, entonces esta formula es un teorema
    ⊢ ((¬ 𝜑 → ¬ 𝜓) → (𝜓 → 𝜑))
    """

    # https://us.metamath.org/mpeuni/ax-3.html

    #-- Obtener las hipótesis
    wph, wps = hyp

    #-- Comprobar que las hipotesis son wff
    assert_wff(wph)  #-- wph es una wff
    assert_wff(wps)  #-- wps es una wff

    #-- Demostracion: Construir el teorema
    step_1 = wph
    step_2 = wn(step_1)
    step_3 = wps
    step_4 = wn(step_3)
    step_5 = wi(step_2, step_4)
    step_6 = wi(step_3, step_1)
    step_7 = wi(step_5, step_6)
    step_8 = theorem(step_7)

    if (show_proof):
        print("\n🟢️ Paso 1: wff 𝜑")
        print(step_1)
        print ("\n🟢️ Paso 2: wn")
        print(step_2)
        print ("\n🟢️ Paso 3: wff 𝜓")
        print(step_3)
        print ("\n🟢️ Paso 4: wn")
        print(step_4)
        print ("\n🟢️ Paso 5: wi")
        print(step_5)
        print ("\n🟢️ Paso 6: wi")
        print(step_6)
        print ("\n🟢️ Paso 7: wi")
        print(step_7)
        print ("\n🟢️ Paso 8: Es Axioma")
        print(step_8)
    

    conclusion = step_8
    return conclusion


#------- TEOREMAS
def mp2(hyp: list, show_proof = False) -> str:
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
    wph, wps, wch, mp2_1, mp2_2, mp2_3 = hyp

    #-- Paso 1
    # wff 𝜑
    # wff ( 𝜓 → 𝜒 )
    # ⊢ 𝜑
    # ⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )
    hyps = [wph, wi(wps, wch), mp2_1, mp2_3]
    step_1  = ax_mp(*hyps) 
    # ⊢ ( 𝜓 → 𝜒 )  Conclusion

    if (show_proof):
        print("\n🟢️ Paso 1: ax_mp")
        show_inference(hyps, step_1)

    #-- Paso 2
    # • wff 𝜓
    # • wff 𝜒
    # ⊢ 𝜓
    # ⊢ ( 𝜓 → 𝜒 )
    hyps = [wps, wch, mp2_2, step_1]
    step_2 = ax_mp(*hyps)      
    # ⊢ 𝜒   Conclusion

    if (show_proof):
        print("\n🟢️ Paso 2: ax_mp")
        show_inference(hyps, step_2)
    
    conclusion = step_2
    return conclusion

def mp2b(hyp: list, show_proof = False) -> str:
    """Teorema mp2b
       Hypotesis:
         wff 𝜑, wff 𝜓, wff 𝜒
         ⊢ 𝜑          (mp2b_1)
         ⊢ ( 𝜑 → 𝜓 )  (mp2b_2)
         ⊢ ( 𝜓 → 𝜒 )  (mp2b_3)
       Conclusion:
         ⊢ 𝜒
    """
    # https://us.metamath.org/mpeuni/mp2b.html
    
    #-- Obtener las hipótesis
    wph, wps, wch, mp2b_1, mp2b_2, mp2b_3 = hyp

    #-- Paso 1
    # wff 𝜑
    # wff 𝜓
    # ⊢ 𝜑
    # ⊢ ( 𝜑 → 𝜓 )
    hyps = [wph, wps, mp2b_1, mp2b_2]
    step_1  = ax_mp(*hyps) 
    # ⊢ 𝜓  Conclusion

    if (show_proof):
        print("\n🟢️ Paso 1: ax_mp")
        show_inference(hyps, step_1)

    #-- Paso 2
    # wff 𝜑
    # wff 𝜒
    # ⊢ 𝜓
    # ⊢ ( 𝜓 → 𝜒 )
    hyps = [wps, wch, step_1, mp2b_3]
    step_2  = ax_mp(*hyps)
    # ⊢ 𝜒  Conclusion

    if (show_proof):
        print("\n🟢️ Paso 2: ax_mp")
        show_inference(hyps, step_2)

    conclusion = step_2

    return conclusion

def a1i(hyp: list, show_proof = False) -> str:
    """
        wff 𝜑, wff 𝜓
        ⊢ 𝜑           (a1i.1)
        ─────
        ⊢ ( 𝜓 → 𝜑 )
    """

    # https://us.metamath.org/mpeuni/a1i.html

    #-- Obtener las hipótesis
    wph, wps, a1i_1 = hyp

    #-- Paso 1
    # wff 𝜑
    # wff 𝜓
    hyps = [wph, wps]
    step_1  = ax_1(hyps) 
    # ⊢ ( 𝜑 → ( 𝜓 → 𝜑 ) )  Conclusion

    if (show_proof):
        print("\n🟢️ Paso 1: ax_mp")
        show_inference(hyps, step_1)

    #-- Paso 2
    # wff 𝜑
    # wff ( 𝜓 → 𝜑 )
    # ⊢ 𝜑
    # ⊢ ( 𝜑 → ( 𝜓 → 𝜑 ) )
    hyps = [wph, wi(wps, wph), a1i_1, step_1]
    step_2 = ax_mp(*hyps)
    # ⊢ ( 𝜓 → 𝜑 ) Conclusion

    if (show_proof):
        print("\n🟢️ Paso 2: ax_mp")
        show_inference(hyps, step_2)

    conclusion = step_2
    return conclusion

def a2i(hyp: list, show_proof = False) -> str:
    """
        wff 𝜑, wff 𝜓, wff 𝜒
        ⊢ (𝜑 → (𝜓 → 𝜒))     (a2i.1)
        ────────────────
        ⊢ ( ( 𝜑 → 𝜓 ) → (𝜑 → 𝜒 ) )
    """ 
    
    # https://us.metamath.org/mpeuni/a2i.html

    #-- Obtener las hipótesis
    wph, wps, wch, a2i_1 = hyp
    
    #-- Paso 1
    # wff 𝜑
    # wff 𝜓
    # wff 𝜒
    hyps = [wph, wps, wch]
    step_1  = ax_2(hyps) 
    # ⊢ ( ( 𝜑 → ( 𝜓 → 𝜒 ) ) → ( ( 𝜑 → 𝜓 ) → ( 𝜑 → 𝜒 ) ) )  Conclusion

    if (show_proof):
        print("\n🟢️ Paso 1: ax_2")
        show_inference(hyps, step_1)
    
    #-- Paso 2
    # wff ( 𝜑 → ( 𝜓 → 𝜒 ) )
    # wff ( ( 𝜑 → 𝜓 ) → (𝜑 → 𝜒 ) )
    # ⊢ (𝜑 → (𝜓 → 𝜒))
    # ⊢ ( ( 𝜑 → ( 𝜓 → 𝜒 ) ) → ( ( 𝜑 → 𝜓 ) → ( 𝜑 → 𝜒 ) ) )
    hyps = [wi(wph, wi (wps, wch)), 
            wi(wi(wph, wps), wi(wph, wch)),
            a2i_1,
            step_1]
    step_2  = ax_mp(*hyps)
    #  ⊢ ( ( 𝜑 → 𝜓 ) → ( 𝜑 → 𝜒 ) ) ) Conclusion
    #  
    if (show_proof):
        print("\n🟢️ Paso 2: ax_mp")
        show_inference(hyps, step_2)                 

    conclusion = step_2
    return conclusion

def mpd(hyp: list, show_proof = False) -> str:
    """
        wff 𝜑, wff 𝜓, wff 𝜒 
        ⊢ ( 𝜑 → 𝜓 )           (mpd_1)
        ⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )   (mpd_2)
        ────────────────────
        ⊢ ( 𝜑 → 𝜒 )
    """
    
    # https://us.metamath.org/mpeuni/mpd.html

    #-- Obtener las hipótesis
    wph, wps, wch, mpd_1, mpd_2 = hyp
    
    #-- Paso 1
    # wff 𝜑
    # wff 𝜓
    # wff 𝜒
    # ⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )
    hyps = [wph, wps, wch, mpd_2]
    step_1  = a2i(hyps)
    # ⊢ ( ( 𝜑 → 𝜓 ) → ( 𝜑 → 𝜒 ) )
     
    if (show_proof):
        print("\n🟢️ Paso 1: a2i")
        show_inference(hyps, step_1)

    #-- Paso 2
    # wff ( 𝜑 → 𝜓 )
    # wff ( 𝜑 → 𝜒 )
    # ⊢ ( 𝜑 → 𝜓 )
    # ⊢ ( ( 𝜑 → 𝜓 ) → ( 𝜑 → 𝜒 ) )
    hyps = [wi(wph, wps), wi(wph,wch), mpd_1, step_1]
    step_2 = ax_mp(*hyps)

    if (show_proof):
        print("\n🟢️ Paso 2: ax_mp")
        show_inference(hyps, step_2)

    conclusion = step_2
    return conclusion

def id(hyp: list, show_proof = False) -> str:
    """
        wff 𝜑
        ──────────
        ⊢ (𝜑 → 𝜑)
    """

    # https://us.metamath.org/mpeuni/id.html

    #-- Obtener las hipótesis
    wph = hyp[0]

    #-- Paso 1
    # wff 𝜑
    hyps = [wph, wph]
    step_1  = ax_1(hyps)
    # ⊢ (𝜑 → (𝜑 → 𝜑))

    if (show_proof):
        print("\n🟢️ Paso 1: ax_1")
        show_inference(hyps, step_1)

    #-- Paso 2
    # wff 𝜑
    # wff (𝜑 → 𝜑)
    hyps = [wph, wi(wph, wph)]
    step_2 = ax_1(hyps)
    # ⊢ (𝜑 → ((𝜑 → 𝜑) → 𝜑))

    if (show_proof):
        print("\n🟢️ Paso 2: ax_1")
        show_inference(hyps, step_2)

    #-- Paso 3
    # wff 𝜑 
    # wff ( 𝜑 → 𝜑 )
    # wff 𝜑 
    # ⊢ (𝜑 → (𝜑 → 𝜑))
    # ⊢ (𝜑 → ((𝜑 → 𝜑) → 𝜑))
    hyps = [wph, wi(wph,wph), wph, step_1, step_2]
    step_3 = mpd(hyps)

    if (show_proof):
        print("\n🟢️ Paso 3: mpd")
        show_inference(hyps, step_3)

    conclusion = step_3
    return conclusion

def con4(hyp: list, show_proof = False) -> str:
    """
        wff 𝜑, wff 𝜓 
        ───────────────────────────
        ⊢ ((¬ 𝜑 → ¬ 𝜓) → (𝜓 → 𝜑))
    """

    # https://us.metamath.org/mpeuni/con4.html

    #-- Obtener las hipótesis
    wph, wps = hyp
    
    #-- Paso 1
    # wff 𝜑
    # wff 𝜓
    hyps = [wph, wps]
    step_1  = ax_3(hyps)
    # ⊢ ((¬ 𝜑 → ¬ 𝜓) → (𝜓 → 𝜑))

    if (show_proof):
        print("\n🟢️ Paso 1: ax_3")
        show_inference(hyps, step_1)

    conclusion = step_1
    return conclusion

def syl(hyp: list, show_proof = False) -> str:
    """
        wff 𝜑, wff 𝜓, wff 𝜒
        ⊢ ( 𝜑 → 𝜓 )  (syl.1)
        ⊢ ( 𝜓 → 𝜒 )  (syl.2)
        ─────────────────────
        ⊢ ( 𝜑 → 𝜒 )
    """

    # https://us.metamath.org/mpeuni/syl.html

    #-- Obtener las hipótesis
    wph, wps, wch, syl_1, syl_2 = hyp

    #-- Paso 1
    # wff (𝜓 → 𝜒 )
    # wff 𝜑
    # ⊢ ( 𝜓 → 𝜒 )
    hyps = [wi(wps, wch), wph, syl_2]
    step_1  = a1i(hyps)
    # ⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )

    if (show_proof):
        print("\n🟢️ Paso 1: a1i")
        show_inference(hyps, step_1)

    #-- Paso 2
    # wff 𝜑
    # wff 𝜓
    # wff 𝜒
    # ⊢ ( 𝜑 → 𝜓 )  (syl.1)
    # ⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )
    hyps = [wph, wps, wch, syl_1, step_1]
    step_2 = mpd(hyps)
    # ⊢ ( 𝜑 → 𝜒 )

    if (show_proof):
        print("\n🟢️ Paso 2: mpd")
        show_inference(hyps, step_2)


    conclusion = step_2
    return conclusion
    
def con4d(hyp: list, show_proof = False) -> str:
    """
        wff 𝜑, wff 𝜓, wff 𝜒
        ⊢ ( 𝜑 → ( ¬𝜓 → ¬𝜒 ) )  (con4d.1)
        ────────────────────
        ⊢ ( 𝜑 → ( 𝜒 → 𝜓 ) )
    """

    # https://us.metamath.org/mpeuni/con4d.html

    #-- Obtener las hipótesis
    wph, wps, wch, con4d_1 = hyp

    #-- Paso 1
    # wff 𝜓
    # wff 𝜒
    hyps = [wps, wch]
    step_1  = con4(hyps)
    # ⊢ ( ( ¬𝜓 → ¬𝜒 ) → ( 𝜒 → 𝜓 ) )

    if (show_proof):
        print("\n🟢️ Paso 1: con4")
        show_inference(hyps, step_1)

    #-- Paso 2
    # wff 𝜑
    # wff ( ¬𝜓 → ¬𝜒 )
    # wff ( 𝜒 → 𝜓 )
    # ⊢ ( 𝜑 → ( ¬𝜓 → ¬𝜒 ) ) (con4d.1)
    # ⊢ ( ( ¬𝜓 → ¬𝜒 ) → ( 𝜒 → 𝜓 ) ) (step_1)
    hyps = [wph, wi(wn(wps), wn(wch)), wi(wch,wps),
            con4d_1, step_1]
    step_2 = syl(hyps)
    # ⊢ ( 𝜑 → ( 𝜒 → 𝜓 ) )
      
    if (show_proof):
        print("\n🟢️ Paso 2: syl")
        show_inference(hyps, step_2)

    conclusion = step_2
    return conclusion
    
def a1d(hyp: list, show_proof = False) -> str:
    """
        wff 𝜑, wff 𝜓, wff 𝜒
        ⊢ ( 𝜑 → 𝜓 )  (a1d.1)
        ────────────────────
        ⊢ ( 𝜑 → ( 𝜒 → 𝜓 ) )
    """

    # https://us.metamath.org/mpeuni/a1d.html

    #-- Obtener las hipótesis
    wph, wps, wch, a1d_1 = hyp

    #-- Paso 1
    # wff 𝜓
    # wff 𝜒
    hyps = [wps, wch]
    step_1  = ax_1(hyps)
    # ⊢ ( 𝜓 → ( 𝜒 → 𝜓 ) )

    if (show_proof):
        print("\n🟢️ Paso 1: ax_1")
        show_inference(hyps, step_1)

    #-- Paso 2
    # wff 𝜑
    # wff 𝜓
    # wff ( 𝜒 → 𝜓 )
    # ⊢ ( 𝜑 → 𝜓 )
    # ⊢ ( 𝜓 → ( 𝜒 → 𝜓 ) )
    hyps = [wph, wps, wi(wch,wps),
            a1d_1, step_1]
    step_2  = syl(hyps)

    if (show_proof):
        print("\n🟢️ Paso 2: syl")
        show_inference(hyps, step_2)

    conclusion = step_2
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

def test_wn():
    """Prueba de la funcion wn()"""

    #-- Verificar que wn() retorna la cadena correcta
    assert wn("wff p") == "wff ¬p"
    print("✅️ wn. Test 1")

    assert wn("wff 𝜑") == "wff ¬𝜑"
    print("✅️ wn. Test 2")

    assert wn("wff 𝜓") == "wff ¬𝜓"
    print("✅️ wn. Test 3")

    assert wn("wff ( 𝜑 → 𝜓 )") == "wff ¬( 𝜑 → 𝜓 )"
    print("✅️ wn. Test 4")

    wff1 = wn(wi(wn(wφ()), wψ()))
    wff2 = wi(wn(wφ()), wff1)
    assert wff1 == "wff ¬( ¬𝜑 → 𝜓 )"
    assert wff2 == "wff ( ¬𝜑 → ¬( ¬𝜑 → 𝜓 ) )"
    print("✅️ wn. Test 5")

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

    assert ax_1(["wff 𝜑", "wff 𝜓"]) == "⊢ ( 𝜑 → ( 𝜓 → 𝜑 ) )"
    print("✅️ ax-1. Test 1")

    assert ax_1(["wff 𝜓", "wff 𝜒"]) == "⊢ ( 𝜓 → ( 𝜒 → 𝜓 ) )"
    print("✅️ ax-1. Test 2")

    assert ax_1(["wff 𝜑", "wff ( 𝜓 → 𝜒 )"]) == "⊢ ( 𝜑 → ( ( 𝜓 → 𝜒 ) → 𝜑 ) )"
    print("✅️ ax-1. Test 3")

    assert ax_1(["wff ( 𝜑 → 𝜒 )", "wff ( 𝜓 → 𝜑 )"]) == \
                "⊢ ( ( 𝜑 → 𝜒 ) → ( ( 𝜓 → 𝜑 ) → ( 𝜑 → 𝜒 ) ) )"
    print("✅️ ax-1. Test 4")

    assert ax_1([wφ(), wψ()]) == "⊢ ( 𝜑 → ( 𝜓 → 𝜑 ) )"
    print("✅️ ax-1. Test 5")

    assert ax_1([w𝜓(), w𝜒()]) == "⊢ ( 𝜓 → ( 𝜒 → 𝜓 ) )"
    print("✅️ ax-1. Test 6")

    assert ax_1([wφ(), wi( w𝜓(), w𝜒())]) == "⊢ ( 𝜑 → ( ( 𝜓 → 𝜒 ) → 𝜑 ) )"
    print("✅️ ax-1. Test 7")    
   
    wph = wi (wφ(), w𝜒())
    wps = wi( w𝜓(), w𝜒())
    assert ax_1([wph, wps]) == "⊢ ( ( 𝜑 → 𝜒 ) → ( ( 𝜓 → 𝜒 ) → ( 𝜑 → 𝜒 ) ) )"
    print("✅️ ax-1. Test 8")

def test_ax_2():
    """Prueba del axioma ax_2"""

    assert ax_2(["wff 𝜑", "wff 𝜓", "wff 𝜒"]) == \
      "⊢ ( ( 𝜑 → ( 𝜓 → 𝜒 ) ) → ( ( 𝜑 → 𝜓 ) → ( 𝜑 → 𝜒 ) ) )"
    print("✅️ ax-2. Test 1")

    assert ax_2(["wff 𝜓", "wff 𝜒", "wff 𝜑"]) == \
      "⊢ ( ( 𝜓 → ( 𝜒 → 𝜑 ) ) → ( ( 𝜓 → 𝜒 ) → ( 𝜓 → 𝜑 ) ) )"
    print("✅️ ax-2. Test 2")

    assert ax_2(["wff 𝜑", "wff ( 𝜓 → 𝜒 )", "wff 𝜒"]) == \
        "⊢ ( ( 𝜑 → ( ( 𝜓 → 𝜒 ) → 𝜒 ) ) → ( ( 𝜑 → ( 𝜓 → 𝜒 ) ) → ( 𝜑 → 𝜒 ) ) )"
    print("✅️ ax-2. Test 3")

    assert ax_2(["wff ( 𝜑 → 𝜓 )", "wff ( 𝜓 → 𝜒 )", "wff ( 𝜒 → 𝜑 )"]) == \
        "⊢ ( ( ( 𝜑 → 𝜓 ) → ( ( 𝜓 → 𝜒 ) → ( 𝜒 → 𝜑 ) ) ) → "\
        "( ( ( 𝜑 → 𝜓 ) → ( 𝜓 → 𝜒 ) ) → ( ( 𝜑 → 𝜓 ) → ( 𝜒 → 𝜑 ) ) ) )"
    print("✅️ ax-2. Test 4")

    assert ax_2([wφ(), wψ(), wχ()]) == \
        "⊢ ( ( 𝜑 → ( 𝜓 → 𝜒 ) ) → ( ( 𝜑 → 𝜓 ) → ( 𝜑 → 𝜒 ) ) )"
    print("✅️ ax-2. Test 5")

    assert ax_2([wi(wφ(), wψ()), wi(wψ(), wχ()), wi(wχ(),wφ())]) == \
        "⊢ ( ( ( 𝜑 → 𝜓 ) → ( ( 𝜓 → 𝜒 ) → ( 𝜒 → 𝜑 ) ) ) → "\
        "( ( ( 𝜑 → 𝜓 ) → ( 𝜓 → 𝜒 ) ) → ( ( 𝜑 → 𝜓 ) → ( 𝜒 → 𝜑 ) ) ) )"
    print("✅️ ax-2. Test 6")

def test_ax_3():
    """Prueba del axioma ax_3"""

    assert ax_3(["wff 𝜑", "wff 𝜓"]) == \
      "⊢ ( ( ¬𝜑 → ¬𝜓 ) → ( 𝜓 → 𝜑 ) )"
    print("✅️ ax-3. Test 1")

    assert ax_3(["wff 𝜓", "wff 𝜑"]) == \
      "⊢ ( ( ¬𝜓 → ¬𝜑 ) → ( 𝜑 → 𝜓 ) )"
    print("✅️ ax-3. Test 2")

    assert ax_3(["wff 𝜓", "wff 𝜑"]) == \
      "⊢ ( ( ¬𝜓 → ¬𝜑 ) → ( 𝜑 → 𝜓 ) )"
    print("✅️ ax-3. Test 3")

    assert ax_3(["wff ( 𝜑 → 𝜓 )", "wff ( 𝜓 → 𝜒 )"]) == \
      "⊢ ( ( ¬( 𝜑 → 𝜓 ) → ¬( 𝜓 → 𝜒 ) ) → ( ( 𝜓 → 𝜒 ) → ( 𝜑 → 𝜓 ) ) )"
    print("✅️ ax-3. Test 4")

    assert ax_3([wφ(), wψ()]) == \
        "⊢ ( ( ¬𝜑 → ¬𝜓 ) → ( 𝜓 → 𝜑 ) )"
    print("✅️ ax-3. Test 5")

    assert ax_3([wφ(), wn(wψ())]) == \
        "⊢ ( ( ¬𝜑 → ¬¬𝜓 ) → ( ¬𝜓 → 𝜑 ) )"
    print("✅️ ax-3. Test 6")

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

    print("-- Negacion:")
    test_wn()

    print("--Teorema: ")
    test_theorem()

    print("-- ax-mp:")
    test_ax_mp()

    print("-- ax-1:")
    test_ax_1()

    print("-- ax-2:")
    test_ax_2()

    print("-- ax-3:")
    test_ax_3()

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
def check_theorem(name: str):
    """Comprobar el teorema dado por su nombre en metamath"""

    #-- Obtener el nombre de la función asociada
    #-- Los caracteres '-' y '.' se convierten a '_'
    #-- Ya que los nombres de las funciones no pueden tener '-' ni '.'
    exec = globals()[name.replace("-", "_").replace(".", "_")]

    print(f"\n───────────────┤ TEOREMA {name} ├────────────────")

    #-- Mostrar el teorema
    show_inference(th[name]["hyp"], th[name]["conc"])

    #-- Calcular la conclusion
    conclusion = exec(th[name]["hyp"], show_proof=True)

    #-- Verificar si la conclusión es correcta
    if conclusion == th[name]["conc"]:
        print ("✅️ Prueba correcta")
    else:
        print("❌️ Prueba incorrecta")
        print(conclusion)
        print(th[name]["conc"])

def show_inference(hypotesis: list, conclusion: str):
    """Imprimir el razonamiento
      * list: Lista de hipotesis
      * conclusion: Conclusion obtenida
    """
    #-- Primero se imprimen las hipotesis
    for hyp in hypotesis:
        print(hyp)

    #-- Calcular el tamaño de la cadena mas larga
    tam = max([len(hyp) for hyp in hypotesis])

    #-- Imprimir linea horizontal
    #-- Su tamano es igual al de la cadena mas larga
    print(f"{"─" * tam}") #-- Dibujar linea

    #-- Imprimir conclusion
    print(conclusion)

def check_all():
    """Comprobar todos los teoremas disponibles en la base de datos"""

    #-- Obtener en name el nombre (cadena) del teorema
    for name in th:

        #-- Pasar esa funcion como parametro a check_theorem
        check_theorem(name)

#--------------------- MAIN ------------------
#-- Tests
unittest()
print("------- Main---------")
demo_wff()
demo_ax_mp()

#------------- TEOREMAS
print()
check_all()
check_theorem("ax-3")

print()

