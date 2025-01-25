import sys

#-- Pila
stack = []

#------ Diccionarios para asignar un numero a las hipotesis

#-- Diccionario de hipotesis Wff
HYP_WFF = {
    "wph": 0,
    "wps": 1,
    "wch": 2,
    "wth": 3,
    "wta": 4,
}

#-- Diccionario de hipotesis teoremas
HYP_TH = {
    "hyp.1": 0,
    "hyp.2": 1,
    "hyp.3": 2
}

#-- Base de datos de teoremas
th_db = {
    #--------- Reglas de construccion -----
    "wn": {
        "hyp": ["wff 𝜑"],
        "conc": "wff ¬𝜑"
    },
    "wi": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "wff ( 𝜑 → 𝜓 )"
    },
    "wb": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "wff ( 𝜑 ↔ 𝜓 )"
    },
    "wa": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "wff ( 𝜑 ∧ 𝜓 )"
    },
    "wo": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "wff ( 𝜑 ∨ 𝜓 )"
    },
    "ax-th": {
        "hyp": ["wff 𝜑"],
        "conc": "⊢ 𝜑"
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
    "mpd": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → 𝜓 )",
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )",
        "proof": ["wph", "wps", "wi", "wph", "wch", "wi", "hyp.1", "wph", "wps", "wch",
         "hyp.2", "a2i", "ax-mp"]
    },
    "id": {
        "hyp": ["wff 𝜑"],
        "conc":"⊢ ( 𝜑 → 𝜑 )",
        "proof": ["wph", "wph", "wph", "wi", "wph", "wph", "wph", "ax-1", "wph", 
         "wph", "wph", "wi", "ax-1", "mpd"],
    },
    "con4": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc":"⊢ ( ( ¬𝜑 → ¬𝜓 ) → ( 𝜓 → 𝜑 ) )",
        "proof": ["wph", "wps", "ax-3"]
    },
    "syl": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( 𝜑 → 𝜓 )", "⊢ ( 𝜓 → 𝜒 )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )",
        "proof": ["wph", "wps", "wch", "hyp.1", "wps", "wch", "wi", "wph", 
                  "hyp.2", "a1i", "mpd"]
    },
    "con4d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( ¬𝜓 → ¬𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜒 → 𝜓 ) )",
        "proof": ["wph", "wps", "wn", "wch", "wn", "wi", "wch", "wps", "wi",
                  "hyp.1", "wps", "wch", "con4", "syl"]                
    },
    "a1d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( 𝜑 → 𝜓 )"],
        "conc": "⊢ ( 𝜑 → ( 𝜒 → 𝜓 ) )",
        "proof": ["wph", "wps", "wch", "wps", "wi", "hyp.1", "wps", "wch",
                  "ax-1", "syl"]
    },
    "pm2.21d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( 𝜑 → ¬𝜓 )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
        "proof": ["wph", "wch", "wps", "wph", "wps", "wn", "wch", "wn", 
                  "hyp.1", "a1d", "con4d"]
    },
    "pm2.21": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ¬𝜑 → ( 𝜑 → 𝜓 ) )",
        "proof": ["wph", "wn", "wph", "wps", "wph", "wn", "id", "pm2.21d"]
    },
    "jarli": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( ( 𝜑 → 𝜓 ) → 𝜒 )"],
        "conc": "⊢ ( ¬𝜑 → 𝜒 )",
        "proof": ["wph", "wn", "wph", "wps", "wi", "wch", "wph", "wps", 
                  "pm2.21", "hyp.1", "syl"]
    },
    "mt4d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( 𝜑 → 𝜓 )", "⊢ ( 𝜑 → ( ¬𝜒 → ¬𝜓 ) )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )",
        "proof": ["wph", "wps", "wch", "hyp.1", "wph", "wch", "wps", "hyp.2",
                  "con4d", "mpd"]
    },
    "sylcom": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃",
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )", "⊢ ( 𝜓 → ( 𝜒 → 𝜃 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → 𝜃 ) )", 
        "proof": ["wph", "wps", "wch", "wi", "wps", "wth", "wi", "hyp.1",
                  "wps", "wch", "wth", "hyp.2", "a2i", "syl"]
    },
    "pm2.18d": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ( 𝜑 → ( ¬𝜓 → 𝜓 ) )"],
        "conc": "⊢ ( 𝜑 → 𝜓 )",
        "proof": ["wph", "wph", "wps", "wph", "id", "wph", "wps", "wn", "wps",
                  "wph", "wn", "hyp.1", "wps", "wph", "wn", "pm2.21",
                  "sylcom", "mt4d"]
    },
    "pm2.18": {
        "hyp": ["wff 𝜑"],
        "conc": "⊢ ( ( ¬𝜑 → 𝜑 ) → 𝜑 )",
        "proof": ["wph", "wn", "wph", "wi", "wph", "wph", "wn", "wph", "wi",
                  "id", "pm2.18d"]
    },
    "notnotr": {
        "hyp": ["wff 𝜑"],
        "conc": "⊢ ( ¬¬𝜑 → 𝜑 )",
        "proof": ["wph", "wn", "wph", "wph", "wph", "pm2.18", "jarli"]
    },
    "syl5com": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃",
                "⊢ ( 𝜑 → 𝜓 )", "⊢ ( 𝜒 → ( 𝜓 → 𝜃 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜒 → 𝜃 ) )",
        "proof": ["wph", "wch", "wps", "wth", "wph", "wps", "wch", "hyp.1",
                  "a1d", "hyp.2", "sylcom"]
    },
    "com12": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( 𝜓 → ( 𝜑 → 𝜒 ) )",
        "proof": ["wps", "wps", "wph", "wch", "wps", "id", "hyp.1", "syl5com"]
    },
    "syl5": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃",
                "⊢ ( 𝜑 → 𝜓 )", "⊢ ( 𝜒 → ( 𝜓 → 𝜃 ) )"],
        "conc": "⊢ ( 𝜒 → ( 𝜑 → 𝜃 ) )",
        "proof": ["wph", "wch", "wth", "wph", "wps", "wch", "wth", "hyp.1", 
                  "hyp.2", "syl5com", "com12"]
    },
    "con2d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( 𝜑 → ( 𝜓 → ¬𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜒 → ¬𝜓 ) )",
        "proof": ["wph", "wps", "wn", "wch", "wps", "wn", "wn", "wps", "wph",
                  "wch", "wn", "wps", "notnotr", "hyp.1", "syl5", "con4d"]
    },
    "mt2d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( 𝜑 → 𝜒 )", "⊢ ( 𝜑 → ( 𝜓 → ¬𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ¬𝜓 )",
        "proof": ["wph", "wch", "wps", "wn", "hyp.1", "wph", "wps", "wch",
                  "hyp.2", "con2d", "mpd"]
    },
    "nsyl3": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( 𝜑 → ¬𝜓 )", "⊢ ( 𝜒 → 𝜓 )"],
        "conc": "⊢ ( 𝜒 → ¬𝜑 )", 
        "proof": ["wch", "wph", "wps", "hyp.2", "wph", "wps", "wn", "wi", 
                  "wch", "hyp.1", "a1i", "mt2d"]
    },
    "con2i": {
        "hyp": ["wff 𝜑", "wff 𝜓",
                "⊢ ( 𝜑 → ¬𝜓 )"],
        "conc": "⊢ ( 𝜓 → ¬𝜑 )",
        "proof": ["wph", "wps", "wps", "hyp.1", "wps", "id", "nsyl3"]
    },
    "notnot": {
        "hyp": ["wff 𝜑"],
        "conc": "⊢ ( 𝜑 → ¬¬𝜑 )",
        "proof": ['wph', 'wn', 'wph', 'wph', 'wn', 'id', 'con2i']
    },
    "imim2i": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( 𝜑 → 𝜓 )" ],
        "conc": "⊢ ( ( 𝜒 → 𝜑 ) → ( 𝜒 → 𝜓 ) )",
        "proof": ['wch', 'wph', 'wps', 'wph', 'wps', 'wi', 'wch', 'hyp.1',
                   'a1i', 'a2i']
    },
    "a2d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃",
                "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )"],
        "conc": "⊢ ( 𝜑 → ( ( 𝜓 → 𝜒 ) → ( 𝜓 → 𝜃 ) ) )",
        "proof": ['wph', 'wps', 'wch', 'wth', 'wi', 'wi', 'wps', 'wch', 'wi',
                  'wps', 'wth', 'wi', 'wi', 'hyp.1', 'wps', 'wch', 'wth', 
                  'ax-2', 'syl']
    },
    "syl6": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃",
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )", 
                "⊢ ( 𝜒 → 𝜃 )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → 𝜃 ) )",
        "proof": ['wph', 'wps', 'wch', 'wth', 'hyp.1', 'wch', 'wth', 'wi',
                  'wps', 'hyp.2', 'a1i', 'sylcom']
    },
    "mpdd": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃",
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
                "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → 𝜃 ) )",
        "proof": ['wph', 'wps', 'wch', 'wi', 'wps', 'wth', 'wi', 'hyp.1',
                  'wph', 'wps', 'wch', 'wth', 'hyp.2', 'a2d', 'mpd']
    },
    "syld": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃",
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
                "⊢ ( 𝜑 → ( 𝜒 → 𝜃 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → 𝜃 ) )",
        "proof": ['wph', 'wps', 'wch', 'wth', 'hyp.1', 'wph', 'wch',
                   'wth', 'wi', 'wps', 'hyp.2', 'a1d', 'mpdd']
    },
    "con4i": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ( ¬𝜑 → ¬𝜓 )"],
        "conc": "⊢ ( 𝜓 → 𝜑 )",
        "proof": ['wph', 'wn', 'wps', 'wn', 'wi', 'wps', 'wph', 'wi',
                   'hyp.1', 'wph', 'wps', 'con4', 'ax-mp']
    },
    "pm2.18i": {
        "hyp": ["wff 𝜑",
                "⊢ ( ¬𝜑 → 𝜑 )"],
        "conc": "⊢ 𝜑",
        "proof": ['wph', 'wn', 'wph', 'wi', 'wph', 'hyp.1', 'wph',
                  'pm2.18', 'ax-mp']
    },
    "nsyl": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ¬𝜓 )",
                "⊢ ( 𝜒 → 𝜓 )"],
        "conc": "⊢ ( 𝜑 → ¬𝜒 )",
        "proof": ['wch', 'wph', 'wph', 'wps', 'wch', 'hyp.1', 'hyp.2',
                   'nsyl3', 'con2i']
    },
    "nsyl2": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ¬𝜓 )",
                "⊢ ( ¬𝜒 → 𝜓 )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )",
        "proof": ['wch', 'wph', 'wph', 'wps', 'wch', 'wn', 'hyp.1',
                  'hyp.2', 'nsyl3', 'con4i']
    },
    "con1d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( ¬𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( ¬𝜒 → 𝜓 ) )",
        "proof": ['wph', 'wps', 'wch', 'wn', 'wph', 'wps', 'wn', 'wch',
                  'wch', 'wn', 'wn', 'hyp.1', 'wch', 'notnot', 'syl6', 'con4d']
    },
    "con1i": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ( ¬𝜑 → 𝜓 )"],
        "conc": "⊢ ( ¬𝜓 → 𝜑 )",
        "proof": ['wps', 'wn', 'wps', 'wph', 'wps', 'wn', 'id', 'hyp.1',
                  'nsyl2']
    },
    "con3i": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ( 𝜑 → 𝜓 )"],
        "conc": "⊢ ( ¬𝜓 → ¬𝜑 )",
        "proof": ['wps', 'wn', 'wps', 'wph', 'wps', 'wn', 'id', 'hyp.1',
                  'nsyl']
    },
    "nsyl4": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → 𝜓 )",
                "⊢ ( ¬𝜑 → 𝜒 )"],
        "conc": "⊢ ( ¬𝜒 → 𝜓 )",
        "proof": ['wch', 'wn', 'wph', 'wps', 'wph', 'wch', 'hyp.2',
                  'con1i', 'hyp.1', 'syl']
    },
    "pm2.61d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
                "⊢ ( 𝜑 → ( ¬𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )",
        "proof": ['wph', 'wch', 'wph', 'wch', 'wn', 'wps', 'wch', 'wph',
                  'wps', 'wch', 'hyp.2', 'con1d', 'hyp.1', 'syld', 'pm2.18d']
    },
    "pm2.61d1": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
                "⊢ ( ¬𝜓 → 𝜒 )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )",
        "proof": ['wph', 'wps', 'wch', 'hyp.1', 'wps', 'wn', 'wch',
                  'wi', 'wph', 'hyp.2', 'a1i', 'pm2.61d']
    },
    "pm2.61i": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ( 𝜑 → 𝜓 )",
                "⊢ ( ¬𝜑 → 𝜓 )"],
        "conc": "⊢ 𝜓",
        "proof": ['wps', 'wph', 'wps', 'wps', 'hyp.1', 'hyp.2',
                  'nsyl4', 'pm2.18i']
    },
    "ja": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( ¬𝜑 → 𝜒 )",
                "⊢ ( 𝜓 → 𝜒 )"],
        "conc": "⊢ ( ( 𝜑 → 𝜓 ) → 𝜒 )",
        "proof": ['wph', 'wps', 'wi', 'wph', 'wch', 'wps', 'wch', 'wph',
                  'hyp.2', 'imim2i', 'hyp.1', 'pm2.61d1']
    },
    "pm2.65i": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ( 𝜑 → 𝜓 )",
                "⊢ ( 𝜑 → ¬𝜓 )"],
        "conc": "⊢ ¬𝜑",
        "proof": ['wps', 'wph', 'wn', 'wph', 'wps', 'hyp.2', 'con2i',
                  'wph', 'wps', 'hyp.1', 'con3i', 'pm2.61i']
    },
    "mt2": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ 𝜓",
                "⊢ ( 𝜑 → ¬𝜓 )"],
        "conc": "⊢ ¬𝜑",
        "proof": ['wph', 'wps', 'wps', 'wph', 'hyp.1', 'a1i', 'hyp.2',
                  'pm2.65i']
    },
    "pm2.01": {
        "hyp": ["wff 𝜑"],
        "conc": "⊢ ( ( 𝜑 → ¬𝜑 ) → ¬𝜑 )",
        "proof": ['wph', 'wph', 'wn', 'wph', 'wn', 'wph', 'wn', 'id', 'wph',
                   'wn', 'id', 'ja']
    },
    "bijust0": {
        "hyp": ["wff 𝜑"],
        "conc": "⊢ ¬( ( 𝜑 → 𝜑 ) → ¬( 𝜑 → 𝜑 ) )",
        "proof": ['wph', 'wph', 'wi', 'wph', 'wph', 'wi', 'wn', 'wi', 'wph',
                  'wph', 'wi', 'wph', 'id', 'wph', 'wph', 'wi', 'pm2.01', 
                  'mt2']
    },
    "bijust": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ¬( ( ¬( ( 𝜑 → 𝜓 ) → ¬( 𝜓 → 𝜑 ) ) → ¬( ( 𝜑 → 𝜓 ) → "
                "¬( 𝜓 → 𝜑 ) ) ) → ¬( ¬( ( 𝜑 → 𝜓 ) → ¬( 𝜓 → 𝜑 ) ) → "
                "¬( ( 𝜑 → 𝜓 ) → ¬( 𝜓 → 𝜑 ) ) ) )",
        "proof": ['wph', 'wps', 'wi', 'wps', 'wph', 'wi', 'wn', 'wi', 'wn',
                  'bijust0']
    },
    #--- DEFINICION ↔
    "df-bi": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ¬( ( ( 𝜑 ↔ 𝜓 ) → ¬( ( 𝜑 → 𝜓 ) → ¬( 𝜓 → 𝜑 ) ) ) → "
                "¬( ¬( ( 𝜑 → 𝜓 ) → ¬( 𝜓 → 𝜑 ) ) → ( 𝜑 ↔ 𝜓 ) ) )",
        "proof": ['wph', 'wps', 'wb', 'wph', 'wps', 'wi', 'wps', 'wph', 'wi',
                  'wn', 'wi', 'wn', 'wi', 'wph', 'wps', 'wi', 'wps', 'wph',
                  'wi', 'wn', 'wi', 'wn', 'wph', 'wps', 'wb', 'wi', 'wn',
                  'wi', 'wn', "ax-th"] 
    },
    #--- TEOREMAS
    "con3d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( ¬𝜒 → ¬𝜓 ) )",
        "proof": ['wph', 'wps', 'wn', 'wch', 'wps', 'wn', 'wn', 'wps', 'wph',
                  'wch', 'wps', 'notnotr', 'hyp.1', 'syl5', 'con1d']
    },
    "con3rr3": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( ¬𝜒 → ( 𝜑 → ¬𝜓 ) )",
        "proof": ['wph', 'wch', 'wn', 'wps', 'wn', 'wph', 'wps', 'wch',
                  'hyp.1', 'con3d', 'com12']
    },
    "impi": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( ¬( 𝜑 → ¬𝜓 ) → 𝜒 )",
        "proof": ['wch', 'wph', 'wps', 'wn', 'wi', 'wph', 'wps', 'wch',
                  'hyp.1', 'con3rr3', 'con1i']
    },
    "pm2.27": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( 𝜑 → ( ( 𝜑 → 𝜓 ) → 𝜓 ) )",
        "proof": ['wph', 'wps', 'wi', 'wph', 'wps', 'wph', 'wps', 'wi', 'id', 'com12']
    },
    "pm3.2im": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → ¬( 𝜑 → ¬𝜓 ) ) )",
        "proof": ['wph', 'wph', 'wps', 'wn', 'wi', 'wps', 'wph', 'wps',
                  'wn', 'pm2.27', 'con2d']
    },
    "expi": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( ¬( 𝜑 → ¬𝜓 ) → 𝜒 )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
        "proof": ['wph', 'wps', 'wph', 'wps', 'wn', 'wi', 'wn', 'wch',
                  'wph', 'wps', 'pm3.2im', 'hyp.1', 'syl6']
    },
    "idd": {
        "hyp": ["wff 𝜑", "wff 𝜓"], 
        "conc": "⊢ ( 𝜑 → ( 𝜓 → 𝜓 ) )",
        "proof": ['wps', 'wps', 'wi', 'wph', 'wps', 'id', 'a1i']
    },
    "simprim": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ¬( 𝜑 → ¬𝜓 ) → 𝜓 )",
        "proof": ['wph', 'wps', 'wps', 'wph', 'wps', 'idd', 'impi']
    },
    "impbi": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 → 𝜓 ) → ( ( 𝜓 → 𝜑 ) → ( 𝜑 ↔ 𝜓 ) ) )",
        "proof": ['wph', 'wps', 'wi', 'wps', 'wph', 'wi', 'wph', 'wps', 
                  'wb', 'wph', 'wps', 'wb', 'wph', 'wps', 'wi', 'wps', 
                  'wph', 'wi', 'wn', 'wi', 'wn', 'wi', 'wph', 'wps', 'wi', 
                  'wps', 'wph', 'wi', 'wn', 'wi', 'wn', 'wph', 'wps', 'wb', 
                  'wi', 'wn', 'wi', 'wn', 'wph', 'wps', 'wi', 'wps', 'wph', 
                  'wi', 'wn', 'wi', 'wn', 'wph', 'wps', 'wb', 'wi', 'wph', 
                  'wps', 'df-bi', 'wph', 'wps', 'wb', 'wph', 'wps', 'wi', 
                  'wps', 'wph', 'wi', 'wn', 'wi', 'wn', 'wi', 'wph', 'wps', 
                  'wi', 'wps', 'wph', 'wi', 'wn', 'wi', 'wn', 'wph', 'wps', 
                  'wb', 'wi', 'simprim', 'ax-mp', 'expi']

    },
    "impbii": {
        "hyp": ["wff 𝜑", "wff 𝜓",
                "⊢ ( 𝜑 → 𝜓 )",
                "⊢ ( 𝜓 → 𝜑 )"],
        "conc": "⊢ ( 𝜑 ↔ 𝜓 )",
        "proof": ['wph', 'wps', 'wi', 'wps', 'wph', 'wi', 'wph', 'wps', 'wb',
                  'hyp.1', 'hyp.2', 'wph', 'wps', 'impbi', 'mp2']
    },
    "biid": {
        "hyp": ["wff 𝜑"],
        "conc": "⊢ ( 𝜑 ↔ 𝜑 )",
        "proof": ['wph', 'wph', 'wph', 'id', 'wph', 'id', 'impbii']
    },
    "2th": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ 𝜑",
                "⊢ 𝜓"],
        "conc": "⊢ ( 𝜑 ↔ 𝜓 )",
        "proof": ['wph', 'wps', 'wps', 'wph', 'hyp.2', 'a1i', 'wph', 'wps',
                  'hyp.1', 'a1i', 'impbii']
    },
    "notnotb": {
        "hyp": ["wff 𝜑"],
        "conc": "⊢ ( 𝜑 ↔ ¬¬𝜑 )",
        "proof": ['wph', 'wph', 'wn', 'wn', 'wph', 'notnot', 'wph',
                  'notnotr', 'impbii']
    },
    "con3": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 → 𝜓 ) → ( ¬𝜓 → ¬𝜑 ) )",
        "proof": ['wph', 'wps', 'wi', 'wph', 'wps', 'wph', 'wps',
                  'wi', 'id', 'con3d']
    },
    "con34b": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 → 𝜓 ) ↔ ( ¬𝜓 → ¬𝜑 ) )",
        "proof": ['wph', 'wps', 'wi', 'wps', 'wn', 'wph', 'wn', 'wi', 'wph',
                  'wps', 'con3', 'wps', 'wph', 'con4', 'impbii']
    },
    #--- DEFINICION ∧
    "df-an": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 ∧ 𝜓 ) ↔ ¬( 𝜑 → ¬𝜓 ) )",
        "proof": ["wph", "wps", "wa", "wph", "wps", "wn", "wi", "wn", 
                  "wb", "ax-th"]
    },
    #---- TEOREMAS
    "syl2im": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", "wff 𝜏",
                "⊢ ( 𝜑 → 𝜓 )",
                "⊢ ( 𝜒 → 𝜃 )",
                "⊢ ( 𝜓 → ( 𝜃 → 𝜏 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜒 → 𝜏 ) )",
        "proof": ['wph', 'wps', 'wch', 'wta', 'wi', 'hyp.1', 'wch',
                  'wth', 'wps', 'wta', 'hyp.2', 'hyp.3',
                  'syl5', 'syl']
    },
    "syl2imc": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", "wff 𝜏",
                "⊢ ( 𝜑 → 𝜓 )",
                "⊢ ( 𝜒 → 𝜃 )",
                "⊢ ( 𝜓 → ( 𝜃 → 𝜏 ) )"],
        "conc": "⊢ ( 𝜒 → ( 𝜑 → 𝜏 ) )",
        "proof": ['wph', 'wch', 'wta', 'wph', 'wps', 'wch', 'wth', 'wta',
                  'hyp.1', 'hyp.2', 'hyp.3', 'syl2im', 'com12']
    },
    "pm2.43i": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ( 𝜑 → ( 𝜑 → 𝜓 ) )"],
        "conc": "⊢ ( 𝜑 → 𝜓 )",
        "proof": ['wph', 'wph', 'wps', 'wph', 'id', 'hyp.1', 'mpd']
    },
    "imim3i": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( ( 𝜃 → 𝜑 ) → ( ( 𝜃 → 𝜓 ) → ( 𝜃 → 𝜒 ) ) )",
        "proof": ['wth', 'wph', 'wi', 'wth', 'wps', 'wch', 'wph', 'wps',
                  'wch', 'wi', 'wth', 'hyp.1', 'imim2i', 'a2d']
    },
    "syl6c": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", "wff 𝜏",
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
                "⊢ ( 𝜑 → ( 𝜓 → 𝜃 ) )",
                "⊢ ( 𝜒 → ( 𝜃 → 𝜏 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → 𝜏 ) )",
        "proof": ['wph', 'wps', 'wth', 'wta', 'hyp.2', 'wph', 'wps', 'wch',
                  'wth', 'wta', 'wi', 'hyp.1', 'hyp.3', 'syl6', 'mpdd']
    },
    "imim2d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( ( 𝜃 → 𝜓 ) → ( 𝜃 → 𝜒 ) ) )",
        "proof": ['wph', 'wth', 'wps', 'wch', 'wph', 'wps', 'wch', 'wi',
                  'wth', 'hyp.1', 'a1d', 'a2d']
    },
    "imim2": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒"],
        "conc": "⊢ ( ( 𝜑 → 𝜓 ) → ( ( 𝜒 → 𝜑 ) → ( 𝜒 → 𝜓 ) ) )",
        "proof": ['wph', 'wps', 'wi', 'wph', 'wps', 'wch', 'wph', 'wps',
                  'wi', 'id', 'imim2d']
    },
    "syldd": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", "wff 𝜏",
                "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )",
                "⊢ ( 𝜑 → ( 𝜓 → ( 𝜃 → 𝜏 ) ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜏 ) ) )",
        "proof": ['wph', 'wps', 'wth', 'wta', 'wi', 'wch', 'wth', 'wi',
                  'wch', 'wta', 'wi', 'hyp.2', 'hyp.1', 'wth',
                  'wta', 'wch', 'imim2', 'syl6c']
    },
    "syl5d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", "wff 𝜏",
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
                "⊢ ( 𝜑 → ( 𝜃 → ( 𝜒 → 𝜏 ) ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜃 → ( 𝜓 → 𝜏 ) ) )",
        "proof": ['wph', 'wth', 'wps', 'wch', 'wta', 'wph', 'wps', 'wch',
                  'wi', 'wth', 'hyp.1', 'a1d', 'hyp.2', 'syldd']
    },
    "syl9": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", "wff 𝜏",
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
                "⊢ ( 𝜃 → ( 𝜒 → 𝜏 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜃 → ( 𝜓 → 𝜏 ) ) )",
        "proof": ['wph', 'wps', 'wch', 'wth', 'wta', 'hyp.1', 'wth',
                  'wch', 'wta', 'wi', 'wi', 'wph', 'hyp.2', 'a1i', 'syl5d']
    },
    "com23": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜒 → ( 𝜓 → 𝜃 ) ) )",
        "proof": ['wph', 'wps', 'wch', 'wth', 'wi', 'wch', 'wth', 'hyp.1',
                  'wch', 'wth', 'pm2.27', 'syl9']
    },
    "pm2.86d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( ( 𝜓 → 𝜒 ) → ( 𝜓 → 𝜃 ) ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )",
        "proof": ['wph', 'wch', 'wps', 'wth', 'wch', 'wps', 'wch', 'wi',
                  'wph', 'wps', 'wth', 'wi', 'wch', 'wps', 'ax-1',
                  'hyp.1', 'syl5', 'com23']
    },
    "simplim": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ¬( 𝜑 → 𝜓 ) → 𝜑 )",
        "proof": ['wph', 'wph', 'wps', 'wi', 'wph', 'wps', 'pm2.21', 
                  'con1i']
    },
    "impbidd": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )",
                "⊢ ( 𝜑 → ( 𝜓 → ( 𝜃 → 𝜒 ) ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 ↔ 𝜃 ) ) )",
        "proof": ['wph', 'wps', 'wch', 'wth', 'wi', 'wth', 'wch', 'wi',
                  'wch', 'wth', 'wb', 'hyp.1', 'hyp.2', 'wch',
                  'wth', 'impbi', 'syl6c']
    },
    "impbid21d": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜓 → ( 𝜒 → 𝜃 ) )",
                "⊢ ( 𝜑 → ( 𝜃 → 𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 ↔ 𝜃 ) ) )",
        "proof": ['wps', 'wch', 'wth', 'wi', 'wph', 'wth', 'wch', 'wi',
                  'wch', 'wth', 'wb', 'hyp.1', 'hyp.2',
                  'wch', 'wth', 'impbi', 'syl2imc']
    },
    "impbid": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
                "⊢ ( 𝜑 → ( 𝜒 → 𝜓 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜒 ) )",
        "proof": ['wph', 'wps', 'wch', 'wb', 'wph', 'wph', 'wps', 'wch',
                  'hyp.1', 'hyp.2', 'impbid21d', 'pm2.43i']
    },
    "biimp": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 ↔ 𝜓 ) → ( 𝜑 → 𝜓 ) )",
        "proof": ['wph', 'wps', 'wb', 'wph', 'wps', 'wi', 'wps', 'wph',
                  'wi', 'wn', 'wi', 'wn', 'wph', 'wps', 'wi', 'wph', 'wps',
                  'wb', 'wph', 'wps', 'wi', 'wps', 'wph', 'wi', 'wn', 'wi',
                  'wn', 'wi', 'wph', 'wps', 'wi', 'wps', 'wph', 'wi', 'wn',
                  'wi', 'wn', 'wph', 'wps', 'wb', 'wi', 'wn', 'wi', 'wn',
                  'wph', 'wps', 'wb', 'wph', 'wps', 'wi', 'wps', 'wph',
                  'wi', 'wn', 'wi', 'wn', 'wi', 'wph', 'wps', 'df-bi',
                  'wph', 'wps', 'wb', 'wph', 'wps', 'wi', 'wps', 'wph', 'wi',
                  'wn', 'wi', 'wn', 'wi', 'wph', 'wps', 'wi', 'wps', 'wph',
                  'wi', 'wn', 'wi', 'wn', 'wph', 'wps', 'wb', 'wi', 'wn',
                  'simplim', 'ax-mp', 'wph', 'wps', 'wi', 'wps', 'wph', 'wi',
                  'wn', 'simplim', 'syl']
    },
    "biimpi": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ( 𝜑 ↔ 𝜓 )"],
        "conc": "⊢ ( 𝜑 → 𝜓 )",
        "proof": ['wph', 'wps', 'wb', 'wph', 'wps', 'wi', 'hyp.1', 'wph',
                  'wps', 'biimp', 'ax-mp']
    },
    "sylbi": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 ↔ 𝜓 )",
                "⊢ ( 𝜓 → 𝜒 )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )",
        "proof": ['wph', 'wps', 'wch', 'wph', 'wps', 'hyp.1', 'biimpi',
                  'hyp.2', 'syl']
    },
    "sylib": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → 𝜓 )",
                "⊢ ( 𝜓 ↔ 𝜒 )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )",
        "proof": ['wph', 'wps', 'wch', 'hyp.1', 'wps', 'wch', 'hyp.2',
                  'biimpi', 'syl']
    },
    "sylbb": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 ↔ 𝜓 )",
                "⊢ ( 𝜓 ↔ 𝜒 )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )",
        "proof": ['wph', 'wps', 'wch', 'hyp.1', 'wps', 'wch', 'hyp.2',
                  'biimpi', 'sylbi']
    },
    "mto": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ¬𝜓",
                "⊢ ( 𝜑 → 𝜓 )"],
        "conc": "⊢ ¬𝜑",
        "proof": ['wph', 'wps', 'hyp.2', 'wps', 'wn', 'wph', 'hyp.1', 'a1i',
                  'pm2.65i']
    },
    "pm2.21i": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ¬𝜑"],
        "conc": "⊢ ( 𝜑 → 𝜓 )",
        "proof": ['wps', 'wph', 'wph', 'wn', 'wps', 'wn', 'hyp.1', 'a1i',
                  'con4i']
    },
    "mt4": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ 𝜑",
                "⊢ ( ¬𝜓 → ¬𝜑 )"],
        "conc": "⊢ 𝜓",
        "proof": ['wph', 'wps', 'hyp.1', 'wps', 'wph', 'hyp.2', 'con4i',
                  'ax-mp']
    },
    "notnotri": {
        "hyp": ["wff 𝜑", 
                "⊢ ¬¬𝜑"],
        "conc": "⊢ 𝜑",
        "proof": ['wph', 'wn', 'wn', 'wph', 'hyp.1', 'wph', 'wn', 'wph',
                  'wn', 'wn', 'wn', 'hyp.1', 'pm2.21i', 'mt4']
    },
    "mt3": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ¬𝜓",
                "⊢ ( ¬𝜑 → 𝜓 )"],
        "conc": "⊢ 𝜑",
        "proof": ['wph', 'wph', 'wn', 'wps', 'hyp.1', 'hyp.2', 'mto',
                  'notnotri']
    },
    "dfbi1": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 ↔ 𝜓 ) ↔ ¬( ( 𝜑 → 𝜓 ) → ¬( 𝜓 → 𝜑 ) ) )",
        "proof": ['wph', 'wps', 'wb', 'wph', 'wps', 'wi', 'wps', 'wph', 'wi',
                  'wn', 'wi', 'wn', 'wb', 'wph', 'wps', 'wb', 'wph', 'wps',
                  'wi', 'wps', 'wph', 'wi', 'wn', 'wi', 'wn', 'wi', 'wph',
                  'wps', 'wi', 'wps', 'wph', 'wi', 'wn', 'wi', 'wn', 'wph',
                  'wps', 'wb', 'wi', 'wn', 'wi', 'wph', 'wps', 'df-bi', 'wph',
                  'wps', 'wb', 'wph', 'wps', 'wi', 'wps', 'wph', 'wi', 'wn', 'wi',
                  'wn', 'wi', 'wph', 'wps', 'wi', 'wps', 'wph', 'wi', 'wn', 'wi',
                  'wn', 'wph', 'wps', 'wb', 'wi', 'wph', 'wps', 'wb', 'wph',
                  'wps', 'wi', 'wps', 'wph', 'wi', 'wn', 'wi', 'wn', 'wb', 'wph',
                  'wps', 'wb', 'wph', 'wps', 'wi', 'wps', 'wph', 'wi', 'wn', 'wi',
                  'wn', 'impbi', 'con3rr3', 'mt3']
    },
    "biimpr": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 ↔ 𝜓 ) → ( 𝜓 → 𝜑 ) )",
        "proof": ['wph', 'wps', 'wb', 'wph', 'wps', 'wi', 'wps', 'wph',
                  'wi', 'wn', 'wi', 'wn', 'wps', 'wph', 'wi', 'wph', 'wps',
                  'dfbi1', 'wph', 'wps', 'wi', 'wps', 'wph', 'wi', 'simprim',
                  'sylbi']
    },
    "bicom1": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 ↔ 𝜓 ) → ( 𝜓 ↔ 𝜑 ) )",
        "proof": ['wph', 'wps', 'wb', 'wps', 'wph', 'wph', 'wps', 'biimpr',
                  'wph', 'wps', 'biimp', 'impbid']
    },
    "bicom": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 ↔ 𝜓 ) ↔ ( 𝜓 ↔ 𝜑 ) )",
        "proof": ['wph', 'wps', 'wb', 'wps', 'wph', 'wb', 'wph', 'wps',
                  'bicom1', 'wps', 'wph', 'bicom1', 'impbii']
    },
    "bicomd": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜒 ↔ 𝜓 ) )",
        "proof": ['wph', 'wps', 'wch', 'wb', 'wch', 'wps', 'wb', 'hyp.1',
                  'wps', 'wch', 'bicom', 'sylib']
    },
    "bicomi": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ( 𝜑 ↔ 𝜓 )"],
        "conc": "⊢ ( 𝜓 ↔ 𝜑 )",
        "proof": ['wph', 'wps', 'wb', 'wps', 'wph', 'wb', 'hyp.1', 'wph',
                  'wps', 'bicom1', 'ax-mp']
    },
    "impcon4bid": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
                "⊢ ( 𝜑 → ( ¬𝜓 → ¬𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜒 ) )",
        "proof": ['wph', 'wps', 'wch', 'hyp.1', 'wph', 'wps', 'wch',
                  'hyp.2', 'con4d', 'impbid']
    },
    "biimpri": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ( 𝜑 ↔ 𝜓 )"],
        "conc": "⊢ ( 𝜓 → 𝜑 )",
        "proof": ['wps', 'wph', 'wph', 'wps', 'hyp.1', 'bicomi',
                  'biimpi']
    },
    "sylib": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → 𝜓 )",
                "⊢ ( 𝜓 ↔ 𝜒 )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )",
        "proof": ['wph', 'wps', 'wch', 'hyp.1', 'wps', 'wch', 'hyp.2',
                  'biimpi', 'syl']
    },
    "mpbi": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ 𝜑",
                "⊢ ( 𝜑 ↔ 𝜓 )"],
        "conc": "⊢ 𝜓",
        "proof": ['wph', 'wps', 'hyp.1', 'wph', 'wps', 'hyp.2',
                  'biimpi', 'ax-mp']
    },
    "mpbir": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ 𝜓",
                "⊢ ( 𝜑 ↔ 𝜓 )"],
        "conc": "⊢ 𝜑",
        "proof": ['wps', 'wph', 'hyp.1', 'wph', 'wps', 'hyp.2',
                  'biimpri', 'ax-mp']
    },
    "sylibr": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → 𝜓 )",
                "⊢ ( 𝜒 ↔ 𝜓 )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )",
        "proof": ['wph', 'wps', 'wch', 'hyp.1', 'wch', 'wps', 'hyp.2',
                  'biimpri', 'syl']
    },
    "sylbbr": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 ↔ 𝜓 )",
                "⊢ ( 𝜓 ↔ 𝜒 )"],
        "conc": "⊢ ( 𝜒 → 𝜑 )",
        "proof": ['wch', 'wps', 'wph', 'wps', 'wch', 'hyp.2', 'biimpri',
                  'hyp.1', 'sylibr'] 
    },
    "biimpd": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
        "proof": ['wph', 'wps', 'wch', 'wb', 'wps', 'wch', 'wi', 'hyp.1',
                  'wps', 'wch', 'biimp', 'syl']
    },
    "syl5ib": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → 𝜓 )",
                "⊢ ( 𝜒 → ( 𝜓 ↔ 𝜃 ) )"],
        "conc": "⊢ ( 𝜒 → ( 𝜑 → 𝜃 ) )",
        "proof": ['wph', 'wps', 'wch', 'wth', 'hyp.1', 'wch', 'wps',
                  'wth', 'hyp.2', 'biimpd', 'syl5']
    },
    "syl5ibr": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → 𝜃 )",
                "⊢ ( 𝜒 → ( 𝜓 ↔ 𝜃 ) )"],
        "conc": "⊢ ( 𝜒 → ( 𝜑 → 𝜓 ) )",
        "proof": ['wph', 'wth', 'wch', 'wps', 'hyp.1', 'wch', 'wps',
                  'wth', 'hyp.2', 'bicomd', 'syl5ib']
    },
    "biimprd": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜒 → 𝜓 ) )",
        "proof": ['wch', 'wps', 'wph', 'wch', 'wch', 'id', 'hyp.1',
                  'syl5ibr']
    },
    "pm5.74": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒"],
        "conc": "⊢ ( ( 𝜑 → ( 𝜓 ↔ 𝜒 ) ) ↔ ( ( 𝜑 → 𝜓 ) ↔ ( 𝜑 → 𝜒 ) ) )",
        "proof": ['wph', 'wps', 'wch', 'wb', 'wi', 'wph', 'wps', 'wi',
                  'wph', 'wch', 'wi', 'wb', 'wph', 'wps', 'wch', 'wb',
                  'wi', 'wph', 'wps', 'wi', 'wph', 'wch', 'wi', 'wps',
                  'wch', 'wb', 'wps', 'wch', 'wph', 'wps', 'wch', 'biimp',
                  'imim3i', 'wps', 'wch', 'wb', 'wch', 'wps', 'wph', 'wps',
                  'wch', 'biimpr', 'imim3i', 'impbid', 'wph', 'wps', 'wi',
                  'wph', 'wch', 'wi', 'wb', 'wph', 'wps', 'wch', 'wph',
                  'wps', 'wi', 'wph', 'wch', 'wi', 'wb', 'wph', 'wps',
                  'wch', 'wph', 'wps', 'wi', 'wph', 'wch', 'wi', 'biimp',
                  'pm2.86d', 'wph', 'wps', 'wi', 'wph', 'wch', 'wi', 'wb',
                  'wph', 'wch', 'wps', 'wph', 'wps', 'wi', 'wph', 'wch',
                  'wi', 'biimpr', 'pm2.86d', 'impbidd', 'impbii']
    },
    "pm5.74i": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜒 ) )"],
        "conc": "⊢ ( ( 𝜑 → 𝜓 ) ↔ ( 𝜑 → 𝜒 ) )",
        "proof": ['wph', 'wps', 'wch', 'wb', 'wi', 'wph', 'wps', 'wi',
                  'wph', 'wch', 'wi', 'wb', 'hyp.1', 'wph', 'wps', 
                  'wch', 'pm5.74', 'mpbi']
    },
    "pm5.74ri": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( ( 𝜑 → 𝜓 ) ↔ ( 𝜑 → 𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜒 ) )",
        "proof": ['wph', 'wps', 'wch', 'wb', 'wi', 'wph', 'wps', 'wi',
                  'wph', 'wch', 'wi', 'wb', 'hyp.1', 'wph', 'wps',
                  'wch', 'pm5.74', 'mpbir']
    },
    "bitri": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒",
                "⊢ ( 𝜑 ↔ 𝜓 )",
                "⊢ ( 𝜓 ↔ 𝜒 )"],
        "conc": "⊢ ( 𝜑 ↔ 𝜒 )",
        "proof": ['wph', 'wch', 'wph', 'wps', 'wch', 'hyp.1', 'hyp.2',
                  'sylbb', 'wph', 'wps', 'wch', 'hyp.1', 'hyp.2',
                  'sylbbr', 'impbii']
    },
    "bitrd": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜒 ) )",
                "⊢ ( 𝜑 → ( 𝜒 ↔ 𝜃 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜃 ) )",
        "proof": ['wph', 'wps', 'wth', 'wph', 'wps', 'wi', 'wph', 'wch',
                  'wi', 'wph', 'wth', 'wi', 'wph', 'wps', 'wch',
                  'hyp.1', 'pm5.74i', 'wph', 'wch', 'wth',
                  'hyp.2', 'pm5.74i', 'bitri', 'pm5.74ri']
    },
    "bitrid": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃",
                "⊢ ( 𝜑 ↔ 𝜓 )",
                "⊢ ( 𝜒 → ( 𝜓 ↔ 𝜃 ) )"],
        "conc": "⊢ ( 𝜒 → ( 𝜑 ↔ 𝜃 ) )",
        "proof": ['wch', 'wph', 'wps', 'wth', 'wph', 'wps', 'wb', 'wch',
                  'hyp.1', 'a1i', 'hyp.2', 'bitrd']
    },
    "bitr3id": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜓 ↔ 𝜑 )",
                "⊢ ( 𝜒 → ( 𝜓 ↔ 𝜃 ) )"],
        "conc": "⊢ ( 𝜒 → ( 𝜑 ↔ 𝜃 ) )",
        "proof": ['wph', 'wps', 'wch', 'wth', 'wps', 'wph', 'hyp.1',
                  'bicomi', 'hyp.2', 'bitrid']
    },
    "bitrdi": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜒 ) )",
                "⊢ ( 𝜒 ↔ 𝜃 )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜃 ) )",
        "proof": ['wph', 'wps', 'wch', 'wth', 'hyp.1', 'wch', 'wth', 'wb',
                  'wph', 'hyp.2', 'a1i', 'bitrd']
    },
    "3bitr3g": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", "wff 𝜏",
                "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜒 ) )",
                "⊢ ( 𝜓 ↔ 𝜃 )",
                "⊢ ( 𝜒 ↔ 𝜏 )"],
        "conc": "⊢ ( 𝜑 → ( 𝜃 ↔ 𝜏 ) )",
        "proof": ['wph', 'wth', 'wch', 'wta', 'wth', 'wps', 'wph', 'wch',
                   'hyp.2', 'hyp.1', 'bitr3id', 'hyp.3', 'bitrdi']
    },
    "con4bid": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( ¬𝜓 ↔ ¬𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜒 ) )",
        "proof": ['wph', 'wps', 'wch', 'wph', 'wch', 'wps', 'wph', 'wps',
                  'wn', 'wch', 'wn', 'hyp.1', 'biimprd', 'con4d', 'wph',
                  'wps', 'wn', 'wch', 'wn', 'hyp.1', 'biimpd',
                  'impcon4bid']
    },
    "notbid": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( ¬𝜓 ↔ ¬𝜒 ) )",
        "proof": ['wph', 'wps', 'wn', 'wch', 'wn', 'wph', 'wps', 'wch',
                  'wps', 'wn', 'wn', 'wch', 'wn', 'wn', 'hyp.1', 'wps',
                  'notnotb', 'wch', 'notnotb', '3bitr3g', 'con4bid']
    },
    "notbi": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 ↔ 𝜓 ) ↔ ( ¬𝜑 ↔ ¬𝜓 ) )",
        "proof": ['wph', 'wps', 'wb', 'wph', 'wn', 'wps', 'wn', 'wb', 'wph',
                  'wps', 'wb', 'wph', 'wps', 'wph', 'wps', 'wb', 'id',
                  'notbid', 'wph', 'wn', 'wps', 'wn', 'wb', 'wph', 'wps',
                  'wph', 'wn', 'wps', 'wn', 'wb', 'id', 'con4bid',
                  'impbii']
    },
    "notbii": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ( 𝜑 ↔ 𝜓 )"],
        "conc": "⊢ ( ¬𝜑 ↔ ¬𝜓 )",
        "proof": ['wph', 'wps', 'wb', 'wph', 'wn', 'wps', 'wn', 'wb',
                  'hyp.1', 'wph', 'wps', 'notbi', 'mpbi']
    },
    "xchbinx": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 ↔ ¬𝜓 )",
                "⊢ ( 𝜓 ↔ 𝜒 )"],
        "conc": "⊢ ( 𝜑 ↔ ¬𝜒 )",
        "proof": ['wph', 'wps', 'wn', 'wch', 'wn', 'hyp.1', 'wps', 'wch',
                  'hyp.2', 'notbii', 'bitri']
    },
    "xchbinxr": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 ↔ ¬𝜓 )",
                "⊢ ( 𝜒 ↔ 𝜓 )"],
        "conc": "⊢ ( 𝜑 ↔ ¬𝜒 )",
        "proof": ['wph', 'wps', 'wch', 'hyp.1', 'wch', 'wps',
                  'hyp.2', 'bicomi', 'xchbinx']
    },
    "imbi2i": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 ↔ 𝜓 )"],
        "conc": "⊢ ( ( 𝜒 → 𝜑 ) ↔ ( 𝜒 → 𝜓 ) )",
        "proof": ['wch', 'wph', 'wps', 'wph', 'wps', 'wb', 'wch', 'hyp.1',
                  'a1i', 'pm5.74i']
    },
    "con2bii": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ( 𝜑 ↔ ¬𝜓 )"],
        "conc": "⊢ ( 𝜓 ↔ ¬𝜑 )",
        "proof": ['wps', 'wps', 'wn', 'wph', 'wps', 'notnotb', 'hyp.1',
                  'xchbinxr']
    },
    "imnan": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 → ¬𝜓 ) ↔ ¬( 𝜑 ∧ 𝜓 ) )",
        "proof": ['wph', 'wps', 'wa', 'wph', 'wps', 'wn', 'wi', 'wph', 'wps',
                  'df-an', 'con2bii']
    },
    "iman": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 → 𝜓 ) ↔ ¬( 𝜑 ∧ ¬𝜓 ) )",
        "proof": ['wph', 'wps', 'wi', 'wph', 'wps', 'wn', 'wn', 'wi', 'wph',
                  'wps', 'wn', 'wa', 'wn', 'wps', 'wps', 'wn', 'wn', 'wph',
                  'wps', 'notnotb', 'imbi2i', 'wph', 'wps', 'wn', 'imnan',
                  'bitri']
    },
    "pm3.24": {
        "hyp": ["wff 𝜑"],
        "conc": "⊢ ¬( 𝜑 ∧ ¬𝜑 )",
        "proof": ['wph', 'wph', 'wi', 'wph', 'wph', 'wn', 'wa', 'wn', 'wph',
                  'id', 'wph', 'wph', 'iman', 'mpbi']
    },
    "sylbir": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜓 ↔ 𝜑 )",
                "⊢ ( 𝜓 → 𝜒 )"],
        "conc": "⊢ ( 𝜑 → 𝜒 )",
        "proof": ['wph', 'wps', 'wch', 'wps', 'wph', 'hyp.1', 'biimpri',
                  'hyp.2', 'syl']
    },
    "ex": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( ( 𝜑 ∧ 𝜓 ) → 𝜒 )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
        "proof": ['wph', 'wps', 'wch', 'wph', 'wps', 'wn', 'wi', 'wn', 'wph',
                  'wps', 'wa', 'wch', 'wph', 'wps', 'df-an', 'hyp.1',
                  'sylbir', 'expi']
    },
    "expcom": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( ( 𝜑 ∧ 𝜓 ) → 𝜒 )"],
        "conc": "⊢ ( 𝜓 → ( 𝜑 → 𝜒 ) )",
        "proof": ['wph', 'wps', 'wch', 'wph', 'wps', 'wch', 'hyp.1', 'ex',
                  'com12']
    },
    "imp": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( ( 𝜑 ∧ 𝜓 ) → 𝜒 )",
        "proof": ['wph', 'wps', 'wa', 'wph', 'wps', 'wn', 'wi', 'wn', 'wch',
                  'wph', 'wps', 'df-an', 'wph', 'wps', 'wch', 'hyp.1', 'impi',
                  'sylbi']
    },
    "ancoms": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( ( 𝜑 ∧ 𝜓 ) → 𝜒 )"],
        "conc": "⊢ ( ( 𝜓 ∧ 𝜑 ) → 𝜒 )",
        "proof": ['wps', 'wph', 'wch', 'wph', 'wps', 'wch', 'hyp.1',
                  'expcom', 'imp']
    },
    "pm3.22": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 ∧ 𝜓 ) → ( 𝜓 ∧ 𝜑 ) )",
        "proof": ['wps', 'wph', 'wps', 'wph', 'wa', 'wps', 'wph', 'wa',
                  'id', 'ancoms']
    },
    "ancom": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 ∧ 𝜓 ) ↔ ( 𝜓 ∧ 𝜑 ) )",
        "proof": ['wph', 'wps', 'wa', 'wps', 'wph', 'wa', 'wph', 'wps',
                  'pm3.22', 'wps', 'wph', 'pm3.22', 'impbii']
    },
    "expdcom": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( ( 𝜓 ∧ 𝜒 ) → 𝜃 ) )"],
        "conc": "⊢ ( 𝜓 → ( 𝜒 → ( 𝜑 → 𝜃 ) ) )",
        "proof": ['wps', 'wch', 'wph', 'wth', 'wi', 'wph', 'wps', 'wch',
                  'wa', 'wth', 'hyp.1', 'com12', 'ex']
    },
    "com3r": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )"],
        "conc": "⊢ ( 𝜒 → ( 𝜑 → ( 𝜓 → 𝜃 ) ) )",
        "proof": ['wph', 'wch', 'wps', 'wth', 'wi', 'wph', 'wps', 'wch',
                  'wth', 'hyp.1', 'com23', 'com12']
    },
    "expd": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃",
                "⊢ ( 𝜑 → ( ( 𝜓 ∧ 𝜒 ) → 𝜃 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )",
        "proof": ['wps', 'wch', 'wph', 'wth', 'wph', 'wps', 'wch', 'wth',
                  'hyp.1', 'expdcom', 'com3r']
    },
    "exp32": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( ( 𝜑 ∧ ( 𝜓 ∧ 𝜒 ) ) → 𝜃 )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )",
        "proof": ['wph', 'wps', 'wch', 'wth', 'wph', 'wps', 'wch', 'wa',
                  'wth', 'hyp.1', 'ex', 'expd']
    },
    "imp31": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )"],
        "conc": "⊢ ( ( ( 𝜑 ∧ 𝜓 ) ∧ 𝜒 ) → 𝜃 )",
        "proof": ['wph', 'wps', 'wa', 'wch', 'wth', 'wph', 'wps', 'wch',
                  'wth', 'wi', 'hyp.1', 'imp', 'imp']
    },
    "anassrs": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( ( 𝜑 ∧ ( 𝜓 ∧ 𝜒 ) ) → 𝜃 )"],
        "conc": "⊢ ( ( ( 𝜑 ∧ 𝜓 ) ∧ 𝜒 ) → 𝜃 )",
        "proof": ['wph', 'wps', 'wch', 'wth', 'wph', 'wps', 'wch', 'wth',
                  'hyp.1', 'exp32', 'imp31']
    },
    "impd": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )"],
        "conc": "⊢ ( 𝜑 → ( ( 𝜓 ∧ 𝜒 ) → 𝜃 ) )",
        "proof": ['wps', 'wch', 'wa', 'wph', 'wth', 'wps', 'wch', 'wph',
                  'wth', 'wi', 'wph', 'wps', 'wch', 'wth', 'hyp.1',
                  'com3l', 'imp', 'com12']
    },
    "com3l": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )"],
        "conc": "⊢ ( 𝜓 → ( 𝜒 → ( 𝜑 → 𝜃 ) ) )",
        "proof": ['wch', 'wph', 'wps', 'wth', 'wph', 'wps', 'wch', 'wth',
                  'hyp.1', 'com3r', 'com3r']
    },
    "imp32": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )"],
        "conc": "⊢ ( ( 𝜑 ∧ ( 𝜓 ∧ 𝜒 ) ) → 𝜃 )",
        "proof": ['wph', 'wps', 'wch', 'wa', 'wth', 'wph', 'wps', 'wch',
                  'wth', 'hyp.1', 'impd', 'imp']
    },
    "exp31": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( ( ( 𝜑 ∧ 𝜓 ) ∧ 𝜒 ) → 𝜃 )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → ( 𝜒 → 𝜃 ) ) )",
        "proof": ['wph', 'wps', 'wch', 'wth', 'wi', 'wph', 'wps', 'wa',
                  'wch', 'wth', 'hyp.1', 'ex', 'ex']
    },
    "anasss": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( ( ( 𝜑 ∧ 𝜓 ) ∧ 𝜒 ) → 𝜃 )"],
        "conc": "⊢ ( ( 𝜑 ∧ ( 𝜓 ∧ 𝜒 ) ) → 𝜃 )",
        "proof": ['wph', 'wps', 'wch', 'wth', 'wph', 'wps', 'wch', 'wth',
                  'hyp.1', 'exp31', 'imp32']
    },
    "anass": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒"],
        "conc": "⊢ ( ( ( 𝜑 ∧ 𝜓 ) ∧ 𝜒 ) ↔ ( 𝜑 ∧ ( 𝜓 ∧ 𝜒 ) ) )",
        "proof": ['wph', 'wps', 'wa', 'wch', 'wa', 'wph', 'wps',
                  'wch', 'wa', 'wa', 'wph', 'wps', 'wch', 'wph',
                  'wps', 'wch', 'wa', 'wa', 'wph', 'wps', 'wch', 'wa',
                  'wa', 'id', 'anassrs', 'wph', 'wps', 'wch', 'wph',
                  'wps', 'wa', 'wch', 'wa', 'wph', 'wps', 'wa', 'wch',
                  'wa', 'id', 'anasss', 'impbii']
    },
    "bitr4i": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 ↔ 𝜓 )", 
                "⊢ ( 𝜒 ↔ 𝜓 )"],
        "conc": "⊢ ( 𝜑 ↔ 𝜒 )",
        "proof": ['wph', 'wps', 'wch', 'hyp.1', 'wch', 'wps', 'hyp.2',
                  'bicomi', 'bitri']
    },
    "dfbi2": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 ↔ 𝜓 ) ↔ ( ( 𝜑 → 𝜓 ) ∧ ( 𝜓 → 𝜑 ) ) )",
        "proof": ['wph', 'wps', 'wb', 'wph', 'wps', 'wi', 'wps', 'wph', 'wi',
                  'wn', 'wi', 'wn', 'wph', 'wps', 'wi', 'wps', 'wph', 'wi',
                  'wa', 'wph', 'wps', 'dfbi1', 'wph', 'wps', 'wi', 'wps',
                  'wph', 'wi', 'df-an', 'bitr4i']
    },
    "adantr": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → 𝜓 )"],
        "conc": "⊢ ( ( 𝜑 ∧ 𝜒 ) → 𝜓 )",
        "proof": ['wph', 'wch', 'wps', 'wph', 'wps', 'wch', 'hyp.1',
                  'a1d', 'imp']
    },
    "simpl": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 ∧ 𝜓 ) → 𝜑 )",
        "proof": ['wph', 'wph', 'wps', 'wph', 'id', 'adantr']
    },
    "pm3.21": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 → ( 𝜓 ∧ 𝜑 ) ) )",
        "proof": ['wps', 'wph', 'wps', 'wph', 'wa', 'wps', 'wph', 'wa', 'id',
                  'expcom']
    },
    "impbid1": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( 𝜓 → 𝜒 ) )",
                "⊢ ( 𝜒 → 𝜓 )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 ↔ 𝜒 ) )",
        "proof": ['wph', 'wps', 'wch', 'hyp.1', 'wch', 'wps', 'wi', 'wph',
                  'hyp.2', 'a1i', 'impbid']
    },
    "iba": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 ↔ ( 𝜓 ∧ 𝜑 ) ) )",
        "proof": ['wph', 'wps', 'wps', 'wph', 'wa', 'wph', 'wps', 'pm3.21',
                  'wps', 'wph', 'simpl', 'impbid1']
    },
    "biantru": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ 𝜑"],
        "conc": "⊢ ( 𝜓 ↔ ( 𝜓 ∧ 𝜑 ) )",
        "proof": ['wph', 'wps', 'wps', 'wph', 'wa', 'wb', 'hyp.1', 'wph',
                  'wps', 'iba', 'ax-mp']
    },
    "biancomd": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 → ( 𝜓 ↔ ( 𝜃 ∧ 𝜒 ) ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 ↔ ( 𝜒 ∧ 𝜃 ) ) )",
        "proof": ['wph', 'wps', 'wth', 'wch', 'wa', 'wch', 'wth', 'wa',
                  'hyp.1', 'wth', 'wch', 'ancom', 'bitrdi']
    },
    "ibar": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 ↔ ( 𝜑 ∧ 𝜓 ) ) )",
        "proof": ['wph', 'wps', 'wph', 'wps', 'wph', 'wps', 'iba', 'biancomd']
    },
    "anclb": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 → 𝜓 ) ↔ ( 𝜑 → ( 𝜑 ∧ 𝜓 ) ) )",
        "proof": ['wph', 'wps', 'wph', 'wps', 'wa', 'wph', 'wps', 'ibar',
                  'pm5.74i']
    },
    "3bitr4i": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", 
                "⊢ ( 𝜑 ↔ 𝜓 )",
                "⊢ ( 𝜒 ↔ 𝜑 )",
                "⊢ ( 𝜃 ↔ 𝜓 )"],
        "conc": "⊢ ( 𝜒 ↔ 𝜃 )",
        "proof": ['wch', 'wph', 'wth', 'hyp.2', 'wph', 'wps', 'wth',
                  'hyp.1', 'hyp.3', 'bitr4i', 'bitri']
    },
    "pm4.71": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 → 𝜓 ) ↔ ( 𝜑 ↔ ( 𝜑 ∧ 𝜓 ) ) )",
        "proof": ['wph', 'wph', 'wps', 'wa', 'wi', 'wph', 'wph', 'wps', 'wa',
                  'wi', 'wph', 'wps', 'wa', 'wph', 'wi', 'wa', 'wph', 'wps',
                  'wi', 'wph', 'wph', 'wps', 'wa', 'wb', 'wph', 'wps', 'wa',
                  'wph', 'wi', 'wph', 'wph', 'wps', 'wa', 'wi', 'wph', 'wps',
                  'simpl', 'biantru', 'wph', 'wps', 'anclb', 'wph', 'wph',
                  'wps', 'wa', 'dfbi2', '3bitr4i']
    },
    "pm4.71i": {
        "hyp": ["wff 𝜑", "wff 𝜓", 
                "⊢ ( 𝜑 → 𝜓 )"],
        "conc": "⊢ ( 𝜑 ↔ ( 𝜑 ∧ 𝜓 ) )",
        "proof": ['wph', 'wps', 'wi', 'wph', 'wph', 'wps', 'wa', 'wb',
                  'hyp.1', 'wph', 'wps', 'pm4.71', 'mpbi']
    },
    "pm4.24": {
        "hyp": ["wff 𝜑"],
        "conc": "⊢ ( 𝜑 ↔ ( 𝜑 ∧ 𝜑 ) )",
        "proof": ['wph', 'wph', 'wph', 'id', 'pm4.71i']
    },
    "pm3.35": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 ∧ ( 𝜑 → 𝜓 ) ) → 𝜓 )",
        "proof": ['wph', 'wph', 'wps', 'wi', 'wps', 'wph', 'wps', 'pm2.27',
                  'imp']
    },
    "df-or": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( 𝜑 ∨ 𝜓 ) ↔ ( ¬𝜑 → 𝜓 ) )",
        "proof": ['wph', 'wps', 'wo', 'wph', 'wn', 'wps', 'wi', 'wb',
                  'ax-th']
    },
    "pm2.54": {
        "hyp": ["wff 𝜑", "wff 𝜓"],
        "conc": "⊢ ( ( ¬𝜑 → 𝜓 ) → ( 𝜑 ∨ 𝜓 ) )",
        "proof": ['wph', 'wps', 'wo', 'wph', 'wn', 'wps', 'wi', 'wph', 'wps',
                  'df-or', 'biimpri']
    },
    "orrd": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", 
                "⊢ ( 𝜑 → ( ¬𝜓 → 𝜒 ) )"],
        "conc": "⊢ ( 𝜑 → ( 𝜓 ∨ 𝜒 ) )",
        "proof": ['wph', 'wps', 'wn', 'wch', 'wi', 'wps', 'wch', 'wo',
                  'hyp.1', 'wps', 'wch', 'pm2.54', 'syl']
    },
    "test": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", "wff 𝜏",
                ""],
        "conc": "",
        "proof": []
    },
    "test": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", "wff 𝜏",
                ""],
        "conc": "",
        "proof": []
    },
    "test": {
        "hyp": ["wff 𝜑", "wff 𝜓", "wff 𝜒", "wff 𝜃", "wff 𝜏",
                ""],
        "conc": "",
        "proof": []
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

def wth():
    """La variable 𝜃 es una fórmula bien formada (wff)"""
    stack.append("wff 𝜃")

def wta():
    """La variable 𝜃 es una fórmula bien formada (wff)"""
    stack.append("wff 𝜏")

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

def wb(show_proof = False):
    """Si wa y wb son fórmulas bien formadas (wff), """
    """entonces (wa ↔ wb) es una fórmula bien formada (wff)"""
    
    #-- Leer formulas de la pila
    w2 = stack.pop()
    w1 = stack.pop()

    #-- Obtener las dos fórmulas
    𝜑 = assert_wff(w1)
    𝜓 = assert_wff(w2)

    #-- Crear la cadena wff
    w = f"wff ( {𝜑} ↔ {𝜓} )"

    #-- Meterla en la pila
    stack.append(w)

def wa(show_proof = False):
    """Si wa y wb son fórmulas bien formadas (wff), """
    """entonces (wa ∧ wb) es una fórmula bien formada (wff)"""
    
    #-- Leer formulas de la pila
    w2 = stack.pop()
    w1 = stack.pop()

    #-- Obtener las dos fórmulas
    𝜑 = assert_wff(w1)
    𝜓 = assert_wff(w2)

    #-- Crear la cadena wff
    w = f"wff ( {𝜑} ∧ {𝜓} )"

    #-- Meterla en la pila
    stack.append(w)

def wo(show_proof = False):
    """Si wa y wb son fórmulas bien formadas (wff), """
    """entonces (wa ∨ wb) es una fórmula bien formada (wff)"""
    
    #-- Leer formulas de la pila
    w2 = stack.pop()
    w1 = stack.pop()

    #-- Obtener las dos fórmulas
    𝜑 = assert_wff(w1)
    𝜓 = assert_wff(w2)

    #-- Crear la cadena wff
    w = f"wff ( {𝜑} ∨ {𝜓} )"

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

    #-- NOTA: No es necesaria esta funcion
    #-- Se deja para hacer pruebas

    proof_theorems(th_db["ax-1"]["proof"],2,2)
    
def ax_2(show_proof=False):
    """Axioma de Frege
    si 𝜑, 𝜓 y 𝜒 son wffs, entonces esta formula es un teorema
    ⊢ ((𝜑 → (𝜓 → 𝜒)) → ((𝜑 → 𝜓) → (𝜑 → 𝜒)))
    """

    #-- NOTA: No es necesaria esta funcion
    #-- Se deja para hacer pruebas

    proof_theorems(th_db["ax-2"]["proof"],3,3)

def ax_3(show_proof=False):
    """Axiom Transposicion
    si 𝜑 y 𝜓  son wffs, entonces esta formula es un teorema
    ⊢ ((¬ 𝜑 → ¬ 𝜓) → (𝜓 → 𝜑))
    """

    #-- NOTA: No es necesaria esta funcion
    #-- Se deja para hacer pruebas

    proof_theorems(th_db["ax-3"]["proof"],2,2)

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

    #--- Numeracion de los pasos mostrados
    step_shown = 1

    #-- Recorrer la lista de teoremas de una prueba
    for step,name in enumerate(proof, 1):

        #-- Meter las hipotesis wff en la pila
        if name in ["wph", "wps", "wch", "wth", "wta"]:
            stack.append(hyp_orig[HYP_WFF[name]])
            continue

        #-- Meter las hipotesis de teoremas en la pila
        #-- Su orden no es fijo, depende de la cantidad de hipotesis wff
        #-- que haya: 1,2 ó 3
        if name in ["hyp.1", "hyp.2", "hyp.3"]:
            stack.append(hyp_orig[wffs + HYP_TH[name]])
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

        #------------ Ejecutar el teorema
        #exec(name)
        #-- Obtener el numero de wffs
        _wffs = count_wff(th_db[name]["hyp"])

        #-- Numero total de hipotesis
        _nhyp = len(th_db[name]["hyp"])

        #-- Ejecutar!
        #-- Comprobar si el teorema tiene prueba
        if "proof" in th_db[name]:
            proof_theorems(th_db[name]["proof"], _nhyp, _wffs)
        else:
            #-- No hay prueba: Ejecutar el teorema
            exec(name, show_proof)

        #-- Leer la conclusion y meterla en hyp para calcular
        #-- su longitud
        hyp.append(stack[-1])

        #-- Calcular el tamaño de la fórmula mas larga
        #-- (hipotesis + conclusion)
        tam = max([len(f) for f in hyp])

        #-- Extraer la conclusion de la lista de hipotesis
        #-- (ya no la necesitamos)
        hyp.pop()

        #-- Modo verbose: Mostrar el paso actual
        if (show_proof):
            if name not in ["wn", "wi", "wb", "wa", "wo"]:
                #print(f"\n🟢️ Paso {step}: {name}")
                print(f"\n🟢️ Paso {step_shown}: {name}")
                step_shown += 1

                #-- Mostrar las hipotesis
                for i, h in enumerate(hyp, 1):
                    print(f"{h}")
                    #print(f"({i}){h}")

                #-- Imprimir linea horizontal
                print("─" * tam)                

                #-- Imprimir la conclusion
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
        print(stack)

        sys.exit(1)



#------------------ MAIN --------------------
print()

#-- Check all the theorems in the database
#for th in th_db:
#    check_theorem(th, True)

print("-----------------------")

check_theorem("orrd", True)
print(stack)

print()
 