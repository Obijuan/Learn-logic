$(
========================================
  Logica formal
========================================
$)

  $( -----------------Alfabeto (simbolos terminales)--------- $)
  $c ( ) -> -. wff |- $.

  $( -- Variables proposicionales. 
     NO se usan en las demostraciones. Se incluyen aqui para poder
     expresar formulas terminales, que se puedan utilizar en ejemplos $)
  $c p q r $.  $(  $)
  
  $( ----------------- Simbolos NO terminales ---------------- $)
  $( --- Variables para refereirse a wff ---- $)
  $( --- wff: Well formed formula $)
  $( psi chi theta tau eta $)
  $v ph ps ch th ta et $. 

  $( --- Reglas de contruccion de formulas (Gramatica) ------- $)

  $( Regla 0: las variables proposicionales son wff $)
  wpp $a wff p $.
  wpq $a wff q $.
  wpr $a wff r $.

  $( Regla 1: Estas variables son wffs $)
  wph $f wff ph $.  $( La variable ph es una wff $)
  wps $f wff ps $.
  wch $f wff ch $.
  wth $f wff th $.
  wta $f wff ta $.
  wet $f wff et $.
  
  $( Regla 2: Si ph es wff, entonces .- ph es una wff $)
  wn $a wff -. ph $.

  $( Regla 3: Si ph y ps son wffs, entonces ( ph -> ps ) es una wff $)
  wi $a wff ( ph -> ps ) $.

$( --------- AXIOMA para INFERENCIAS  --------------------------- $)

  $( Axioma para regla de inferencia. Indica como obtener un teorema a partir 
      de otras premisas que son teoremas. $)
  ${
    $( Premisas $)
    min $e |- ph $.
    maj $e |- ( ph -> ps ) $.

    $( Modus ponens $)
    ax-mp $a |- ps $.
  $}

$( --- EJEMPLOS DE PRUEBA del LENGUAJE TERMINAL ---- $)

  $( Para un sistema concreto, establecemos el significado de
     las proposiciones:
      p="Interruptor conectado"
      q="Luz encendida"
  $)

  $( Mediante los axiomas especificamos las relaciones
     preestablecidas entre las proposiciones $)
  $( Al activar este interruptor se enciende la luz $)
  ax-obi1 $a |- ( p -> q ) $.
  
  $( Los teoremas son las leyes que rigen en este universo, 
     que derivan de los axiomas $)
  $( Teorema deduccion: La luz esta encendida $)
  ${
    $( Premisa: Interruptor conectado $)
    th-obi1.1 $e |- p $.

    $( Deduccion: Concluimos que la luz se enciende 
       (Contributed by ?who?, 19-Jan-2025.) $)
    th-obi1 $p |- q $=
      wpp wpq th-obi1.1 ax-obi1 ax-mp $.
  $}


$( ----------------- AXIOMAS ------------------------------------ $)
  $( Axiom _Simp_.  "the principle of simplification" 
    "it enables us to pass from the joint assertion of ` ph ` and ` ps ` to 
     the assertion of ` ph ` simply".  $)
  ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

  $( Axiom _Frege_.  
     It "distributes" an antecedent over two consequents $)
  ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

  $( Axiom _Transp_.  "the principle of transposition"  
     It swaps or "transposes" the order of the consequents when negation is 
     removed  $)
  ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.

$(
=============================================================
  TEOREMAS. Implicacion logica. El axioma ax-3 no se usa
=============================================================
$)

  $( mp2: Inferencia modus pones encadenada $)
  ${
    mp2.1 $e |- ph $.
    mp2.2 $e |- ps $.
    mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.
    mp2 $p |- ch $=
      wps wch mp2.2 wph wps wch wi mp2.1 mp2.3 ax-mp ax-mp $.
  $}

  ${
    mp2b.1 $e |- ph $.
    mp2b.2 $e |- ( ph -> ps ) $.
    mp2b.3 $e |- ( ps -> ch ) $.
    $( A double modus ponens inference.  
       (Contributed by ?who?, 19-Jan-2025.) $)
    mp2b $p |- ch $=
      wps wch wph wps mp2b.1 mp2b.2 ax-mp mp2b.3 ax-mp $. 
  $}

  ${
    a1i.1 $e |- ph $.
    $( Inference introducing an antecedent.  Inference associated with ~ ax-1 .
       Its associated inference is ~ a1ii .  See ~ conventions for a definition
       of "associated inference".  (Contributed by NM, 29-Dec-1992.) $)
    a1i $p |- ( ps -> ph ) $=
      wph wps wph wi a1i.1 wph wps ax-1 ax-mp $.
  $}

  ${
    2a1i.1 $e |- ph $.
    $( Inference introducing two antecedents.  Two applications of ~ a1i .
       Inference associated with ~ 2a1 .  (Contributed by Jeff Hankins,
       4-Aug-2009.) $)
    2a1i $p |- ( ps -> ( ch -> ph ) ) $=
      wch wph wi wps wph wch 2a1i.1 a1i a1i $.
  $}

  ${
    mp1i.1 $e |- ph $.
    mp1i.2 $e |- ( ph -> ps ) $.
    $( Inference detaching an antecedent and introducing a new one.
       (Contributed by Stefan O'Rear, 29-Jan-2015.) $)
    mp1i $p |- ( ch -> ps ) $=
      wps wch wph wps mp1i.1 mp1i.2 ax-mp a1i $.
  $}

  ${
    a2i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference distributing an antecedent.  Inference associated with
       ~ ax-2 .  Its associated inference is ~ mpd .  (Contributed by NM,
       29-Dec-1992.) $)
    a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $=
      wph wps wch wi wi wph wps wi wph wch wi wi a2i.1 wph wps wch ax-2 ax-mp
      $.
  $}

  ${
    mpd.1 $e |- ( ph -> ps ) $.
    mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A modus ponens deduction.  A translation of natural deduction rule
       ` -> ` E ( ` -> ` elimination), see ~ natded .  Deduction form of
       ~ ax-mp .  Inference associated with ~ a2i .  Commuted form of ~ mpcom .
       (Contributed by NM, 29-Dec-1992.) $)
    mpd $p |- ( ph -> ch ) $=
      wph wps wi wph wch wi mpd.1 wph wps wch mpd.2 a2i ax-mp $.
  $}

  ${
    imim2i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common antecedents in an implication.  Inference
       associated with ~ imim2 .  Its associated inference is ~ syl .
       (Contributed by NM, 28-Dec-1992.) $)
    imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
      wch wph wps wph wps wi wch imim2i.1 a1i a2i $.
  $}

  ${
    $( First of 2 premises for ~ syl . $)
    syl.1 $e |- ( ph -> ps ) $.
    $( Second of 2 premises for ~ syl . $)
    syl.2 $e |- ( ps -> ch ) $.
    $( An inference version of the transitive laws for implication ~ imim2 and
       ~ imim1 (and ~ imim1i and ~ imim2i ), which Russell and Whitehead call
       "the principle of the syllogism ... because ... the syllogism in Barbara
       is derived from [[ ~ syl ]" (quote after Theorem *2.06 of
       [WhiteheadRussell] p. 101).  Some authors call this law a "hypothetical
       syllogism".  Its associated inference is ~ mp2b .

       (A bit of trivia: this is the most commonly referenced assertion in our
       database (13449 times as of 22-Jul-2021).  In second place is ~ eqid
       (9597 times), followed by ~ adantr (8861 times), ~ syl2anc (7421 times),
       ~ adantl (6403 times), and ~ simpr (5829 times).  The Metamath program
       command 'show usage' shows the number of references.)

       (Contributed by NM, 30-Sep-1992.)  (Proof shortened by Mel L. O'Cat,
       20-Oct-2011.)  (Proof shortened by Wolf Lammen, 26-Jul-2012.) $)
    syl $p |- ( ph -> ch ) $=
      wph wps wch syl.1 wps wch wi wph syl.2 a1i mpd $.
  $}

  ${
    3syl.1 $e |- ( ph -> ps ) $.
    3syl.2 $e |- ( ps -> ch ) $.
    3syl.3 $e |- ( ch -> th ) $.
    $( Inference chaining two syllogisms ~ syl .  Inference associated with
       ~ imim12i .  (Contributed by NM, 28-Dec-1992.) $)
    3syl $p |- ( ph -> th ) $=
      wph wch wth wph wps wch 3syl.1 3syl.2 syl 3syl.3 syl $.
  $}

  ${
    4syl.1 $e |- ( ph -> ps ) $.
    4syl.2 $e |- ( ps -> ch ) $.
    4syl.3 $e |- ( ch -> th ) $.
    4syl.4 $e |- ( th -> ta ) $.
    $( Inference chaining three syllogisms ~ syl .  (Contributed by BJ,
       14-Jul-2018.)  The use of this theorem is marked "discouraged" because
       it can cause the Metamath program "MM-PA> MINIMIZE__WITH *" command to
       have very long run times.  However, feel free to use "MM-PA>
       MINIMIZE__WITH 4syl / OVERRIDE" if you wish.  Remember to update the
       "discouraged" file if it gets used.  (New usage is discouraged.) $)
    4syl $p |- ( ph -> ta ) $=
      wph wth wta wph wps wch wth 4syl.1 4syl.2 4syl.3 3syl 4syl.4 syl $.
  $}

  ${
    mpi.1 $e |- ps $.
    mpi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A nested modus ponens inference.  Inference associated with ~ com12 .
       (Contributed by NM, 29-Dec-1992.)  (Proof shortened by Stefan Allan,
       20-Mar-2006.) $)
    mpi $p |- ( ph -> ch ) $=
      wph wps wch wps wph mpi.1 a1i mpi.2 mpd $.
  $}

  ${
    mpisyl.1 $e |- ( ph -> ps ) $.
    mpisyl.2 $e |- ch $.
    mpisyl.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( A syllogism combined with a modus ponens inference.  (Contributed by
       Alan Sare, 25-Jul-2011.) $)
    mpisyl $p |- ( ph -> th ) $=
      wph wps wth mpisyl.1 wps wch wth mpisyl.2 mpisyl.3 mpi syl $.
  $}

  $( Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  For
     another version of the proof directly from axioms, see ~ idALT .  Its
     associated inference, ~ idi , requires no axioms for its proof, contrary
     to ~ id .  Note that the second occurrences of ` ph ` in Steps 1 and 2 may
     be simultaneously replaced by any wff ` ps ` , which may ease the
     understanding of the proof.  (Contributed by NM, 29-Dec-1992.)  (Proof
     shortened by Stefan Allan, 20-Mar-2006.) $)
  id $p |- ( ph -> ph ) $=
    wph wph wph wi wph wph wph ax-1 wph wph wph wi ax-1 mpd $.

  $( Alternate proof of ~ id .  This version is proved directly from the axioms
     for demonstration purposes.  This proof is a popular example in the
     literature and is identical, step for step, to the proofs of Theorem 1 of
     [Margaris] p. 51, Example 2.7(a) of [Hamilton] p. 31, Lemma 10.3 of
     [BellMachover] p. 36, and Lemma 1.8 of [Mendelson] p. 36.  It is also "Our
     first proof" in Hirst and Hirst's _A Primer for Logic and Proof_ p. 17
     (PDF p. 23) at ~ http://www.appstate.edu/~~hirstjl/primer/hirst.pdf .
     Note that the second occurrences of ` ph ` in Steps 1 to 4 and the sixth
     in Step 3 may be simultaneously replaced by any wff ` ps ` , which may
     ease the understanding of the proof.  For a shorter version of the proof
     that takes advantage of previously proved theorems, see ~ id .
     (Contributed by NM, 30-Sep-1992.)  (Proof modification is discouraged.)
     Use ~ id instead.  (New usage is discouraged.) $)
  idALT $p |- ( ph -> ph ) $=
    wph wph wph wi wi wph wph wi wph wph ax-1 wph wph wph wi wph wi wi wph wph
    wph wi wi wph wph wi wi wph wph wph wi ax-1 wph wph wph wi wph ax-2 ax-mp
    ax-mp $.

  $( Principle of identity ~ id with antecedent.  (Contributed by NM,
     26-Nov-1995.) $)
  idd $p |- ( ph -> ( ps -> ps ) ) $=
    wps wps wi wph wps id a1i $.

  ${
    a1d.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing an embedded antecedent.  Deduction form of ~ ax-1
       and ~ a1i .  (Contributed by NM, 5-Jan-1993.)  (Proof shortened by
       Stefan Allan, 20-Mar-2006.) $)
    a1d $p |- ( ph -> ( ch -> ps ) ) $=
      wph wps wch wps wi a1d.1 wps wch ax-1 syl $.
  $}

  ${
    2a1d.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing two antecedents.  Two applications of ~ a1d .
       Deduction associated with ~ 2a1 and ~ 2a1i .  (Contributed by BJ,
       10-Aug-2020.) $)
    2a1d $p |- ( ph -> ( ch -> ( th -> ps ) ) ) $=
      wph wth wps wi wch wph wps wth 2a1d.1 a1d a1d $.
  $}

  ${
    a1i13.1 $e |- ( ps -> th ) $.
    $( Add two antecedents to a wff.  (Contributed by Jeff Hankins,
       4-Aug-2009.) $)
    a1i13 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      wps wch wth wi wi wph wps wth wch a1i13.1 a1d a1i $.
  $}

  $( A double form of ~ ax-1 .  Its associated inference is ~ 2a1i .  Its
     associated deduction is ~ 2a1d .  (Contributed by BJ, 10-Aug-2020.)
     (Proof shortened by Wolf Lammen, 1-Sep-2020.) $)
  2a1 $p |- ( ph -> ( ps -> ( ch -> ph ) ) ) $=
    wph wph wps wch wph id 2a1d $.

  ${
    a2d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Deduction distributing an embedded antecedent.  Deduction form of
       ~ ax-2 .  (Contributed by NM, 23-Jun-1994.) $)
    a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $=
      wph wps wch wth wi wi wps wch wi wps wth wi wi a2d.1 wps wch wth ax-2 syl
      $.
  $}

  ${
    sylcom.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylcom.2 $e |- ( ps -> ( ch -> th ) ) $.
    $( Syllogism inference with commutation of antecedents.  (Contributed by
       NM, 29-Aug-2004.)  (Proof shortened by Mel L. O'Cat, 2-Feb-2006.)
       (Proof shortened by Stefan Allan, 23-Feb-2006.) $)
    sylcom $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wi wps wth wi sylcom.1 wps wch wth sylcom.2 a2i syl $.
  $}

  ${
    syl5com.1 $e |- ( ph -> ps ) $.
    syl5com.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( Syllogism inference with commuted antecedents.  (Contributed by NM,
       24-May-2005.) $)
    syl5com $p |- ( ph -> ( ch -> th ) ) $=
      wph wch wps wth wph wps wch syl5com.1 a1d syl5com.2 sylcom $.
  $}

  ${
    com12.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference that swaps (commutes) antecedents in an implication.
       Inference associated with ~ pm2.04 .  Its associated inference is
       ~ mpi .  (Contributed by NM, 29-Dec-1992.)  (Proof shortened by Wolf
       Lammen, 4-Aug-2012.) $)
    com12 $p |- ( ps -> ( ph -> ch ) ) $=
      wps wps wph wch wps id com12.1 syl5com $.
  $}

  ${
    syl11.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl11.2 $e |- ( th -> ph ) $.
    $( A syllogism inference.  Commuted form of an instance of ~ syl .
       (Contributed by BJ, 25-Oct-2021.) $)
    syl11 $p |- ( ps -> ( th -> ch ) ) $=
      wth wps wch wth wph wps wch wi syl11.2 syl11.1 syl com12 $.
  $}

  ${
    syl5.1 $e |- ( ph -> ps ) $.
    syl5.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A syllogism rule of inference.  The first premise is used to replace the
       second antecedent of the second premise.  (Contributed by NM,
       27-Dec-1992.)  (Proof shortened by Wolf Lammen, 25-May-2013.) $)
    syl5 $p |- ( ch -> ( ph -> th ) ) $=
      wph wch wth wph wps wch wth syl5.1 syl5.2 syl5com com12 $.
  $}

  ${
    syl6.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6.2 $e |- ( ch -> th ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM, 5-Jan-1993.)
       (Proof shortened by Wolf Lammen, 30-Jul-2012.) $)
    syl6 $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth syl6.1 wch wth wi wps syl6.2 a1i sylcom $.
  $}

  ${
    syl56.1 $e |- ( ph -> ps ) $.
    syl56.2 $e |- ( ch -> ( ps -> th ) ) $.
    syl56.3 $e |- ( th -> ta ) $.
    $( Combine ~ syl5 and ~ syl6 .  (Contributed by NM, 14-Nov-2013.) $)
    syl56 $p |- ( ch -> ( ph -> ta ) ) $=
      wph wps wch wta syl56.1 wch wps wth wta syl56.2 syl56.3 syl6 syl5 $.
  $}

  ${
    syl6com.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6com.2 $e |- ( ch -> th ) $.
    $( Syllogism inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)
    syl6com $p |- ( ps -> ( ph -> th ) ) $=
      wph wps wth wph wps wch wth syl6com.1 syl6com.2 syl6 com12 $.
  $}

  ${
    mpcom.1 $e |- ( ps -> ph ) $.
    mpcom.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus ponens inference with commutation of antecedents.  Commuted form
       of ~ mpd .  (Contributed by NM, 17-Mar-1996.) $)
    mpcom $p |- ( ps -> ch ) $=
      wps wph wch mpcom.1 wph wps wch mpcom.2 com12 mpd $.
  $}

  ${
    syli.1 $e |- ( ps -> ( ph -> ch ) ) $.
    syli.2 $e |- ( ch -> ( ph -> th ) ) $.
    $( Syllogism inference with common nested antecedent.  (Contributed by NM,
       4-Nov-2004.) $)
    syli $p |- ( ps -> ( ph -> th ) ) $=
      wps wph wch wth syli.1 wch wph wth syli.2 com12 sylcom $.
  $}

  ${
    syl2im.1 $e |- ( ph -> ps ) $.
    syl2im.2 $e |- ( ch -> th ) $.
    syl2im.3 $e |- ( ps -> ( th -> ta ) ) $.
    $( Replace two antecedents.  Implication-only version of ~ syl2an .
       (Contributed by Wolf Lammen, 14-May-2013.) $)
    syl2im $p |- ( ph -> ( ch -> ta ) ) $=
      wph wps wch wta wi syl2im.1 wch wth wps wta syl2im.2 syl2im.3 syl5 syl $.

    $( A commuted version of ~ syl2im .  Implication-only version of
       ~ syl2anr .  (Contributed by BJ, 20-Oct-2021.) $)
    syl2imc $p |- ( ch -> ( ph -> ta ) ) $=
      wph wch wta wph wps wch wth wta syl2im.1 syl2im.2 syl2im.3 syl2im com12
      $.
  $}

  $( This theorem, sometimes called "Assertion" or "Pon" (for "ponens"), can be
     thought of as a closed form of modus ponens ~ ax-mp .  Theorem *2.27 of
     [WhiteheadRussell] p. 104.  (Contributed by NM, 15-Jul-1993.) $)
  pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
    wph wps wi wph wps wph wps wi id com12 $.

  ${
    mpdd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    mpdd.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction.  Double deduction associated with
       ~ ax-mp .  Deduction associated with ~ mpd .  (Contributed by NM,
       12-Dec-2004.) $)
    mpdd $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wi wps wth wi mpdd.1 wph wps wch wth mpdd.2 a2d mpd $.
  $}

  ${
    mpid.1 $e |- ( ph -> ch ) $.
    mpid.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction.  Deduction associated with ~ mpi .
       (Contributed by NM, 14-Dec-2004.) $)
    mpid $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wph wch wps mpid.1 a1d mpid.2 mpdd $.
  $}

  ${
    mpdi.1 $e |- ( ps -> ch ) $.
    mpdi.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction.  (Contributed by NM, 16-Apr-2005.)
       (Proof shortened by Mel L. O'Cat, 15-Jan-2008.) $)
    mpdi $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wps wch wi wph mpdi.1 a1i mpdi.2 mpdd $.
  $}

  ${
    mpii.1 $e |- ch $.
    mpii.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A doubly nested modus ponens inference.  (Contributed by NM,
       31-Dec-1993.)  (Proof shortened by Wolf Lammen, 31-Jul-2012.) $)
    mpii $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wch wps mpii.1 a1i mpii.2 mpdi $.
  $}

  ${
    syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syld.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Syllogism deduction.  Deduction associated with ~ syl .  See
       ~ conventions for the meaning of "associated deduction" or "deduction
       form".  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Mel L.
       O'Cat, 19-Feb-2008.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)
    syld $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth syld.1 wph wch wth wi wps syld.2 a1d mpdd $.

    $( Syllogism deduction.  Commuted form of ~ syld .  (Contributed by BJ,
       25-Oct-2021.) $)
    syldc $p |- ( ps -> ( ph -> th ) ) $=
      wph wps wth wph wps wch wth syld.1 syld.2 syld com12 $.
  $}

  ${
    mp2d.1 $e |- ( ph -> ps ) $.
    mp2d.2 $e |- ( ph -> ch ) $.
    mp2d.3 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A double modus ponens deduction.  Deduction associated with ~ mp2 .
       (Contributed by NM, 23-May-2013.)  (Proof shortened by Wolf Lammen,
       23-Jul-2013.) $)
    mp2d $p |- ( ph -> th ) $=
      wph wps wth mp2d.1 wph wps wch wth mp2d.2 mp2d.3 mpid mpd $.
  $}

  ${
    a1dd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Double deduction introducing an antecedent.  Deduction associated with
       ~ a1d .  Double deduction associated with ~ ax-1 and ~ a1i .
       (Contributed by NM, 17-Dec-2004.)  (Proof shortened by Mel L. O'Cat,
       15-Jan-2008.) $)
    a1dd $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $=
      wph wps wch wth wch wi a1dd.1 wch wth ax-1 syl6 $.
  $}

  ${
    2a1dd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Double deduction introducing two antecedents.  Two applications of
       ~ 2a1dd .  Deduction associated with ~ 2a1d .  Double deduction
       associated with ~ 2a1 and ~ 2a1i .  (Contributed by Jeff Hankins,
       5-Aug-2009.) $)
    2a1dd $p |- ( ph -> ( ps -> ( th -> ( ta -> ch ) ) ) ) $=
      wph wps wta wch wi wth wph wps wch wta 2a1dd.1 a1dd a1dd $.
  $}

  ${
    pm2.43i.1 $e |- ( ph -> ( ph -> ps ) ) $.
    $( Inference absorbing redundant antecedent.  Inference associated with
       ~ pm2.43 .  (Contributed by NM, 10-Jan-1993.)  (Proof shortened by Mel
       L. O'Cat, 28-Nov-2008.) $)
    pm2.43i $p |- ( ph -> ps ) $=
      wph wph wps wph id pm2.43i.1 mpd $.
  $}

  ${
    pm2.43d.1 $e |- ( ph -> ( ps -> ( ps -> ch ) ) ) $.
    $( Deduction absorbing redundant antecedent.  Deduction associated with
       ~ pm2.43 and ~ pm2.43i .  (Contributed by NM, 18-Aug-1993.)  (Proof
       shortened by Mel L. O'Cat, 28-Nov-2008.) $)
    pm2.43d $p |- ( ph -> ( ps -> ch ) ) $=
      wph wps wps wch wps id pm2.43d.1 mpdi $.
  $}

  ${
    pm2.43a.1 $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
    $( Inference absorbing redundant antecedent.  (Contributed by NM,
       7-Nov-1995.)  (Proof shortened by Mel L. O'Cat, 28-Nov-2008.) $)
    pm2.43a $p |- ( ps -> ( ph -> ch ) ) $=
      wps wph wps wch wps id pm2.43a.1 mpid $.
  $}

  ${
    pm2.43b.1 $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
    $( Inference absorbing redundant antecedent.  (Contributed by NM,
       31-Oct-1995.) $)
    pm2.43b $p |- ( ph -> ( ps -> ch ) ) $=
      wps wph wch wph wps wch pm2.43b.1 pm2.43a com12 $.
  $}

  $( Absorption of redundant antecedent.  Also called the "Contraction" or
     "Hilbert" axiom.  Theorem *2.43 of [WhiteheadRussell] p. 106.
     (Contributed by NM, 10-Jan-1993.)  (Proof shortened by Mel L. O'Cat,
     15-Aug-2004.) $)
  pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    wph wph wps wi wps wph wps pm2.27 a2i $.

  ${
    imim2d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding nested antecedents.  Deduction associated with ~ imim2
       and ~ imim2i .  (Contributed by NM, 10-Jan-1993.) $)
    imim2d $p |- ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) $=
      wph wth wps wch wph wps wch wi wth imim2d.1 a1d a2d $.
  $}

  $( A closed form of syllogism (see ~ syl ).  Theorem *2.05 of
     [WhiteheadRussell] p. 100.  Its associated inference is ~ imim2i .  Its
     associated deduction is ~ imim2d .  An alternate proof from more basic
     results is given by ~ ax-1 followed by ~ a2d .  (Contributed by NM,
     29-Dec-1992.)  (Proof shortened by Wolf Lammen, 6-Sep-2012.) $)
  imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    wph wps wi wph wps wch wph wps wi id imim2d $.

  ${
    embantd.1 $e |- ( ph -> ps ) $.
    embantd.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Deduction embedding an antecedent.  (Contributed by Wolf Lammen,
       4-Oct-2013.) $)
    embantd $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $=
      wph wps wch wi wps wth embantd.1 wph wch wth wps embantd.2 imim2d mpid $.
  $}

  ${
    3syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3syld.2 $e |- ( ph -> ( ch -> th ) ) $.
    3syld.3 $e |- ( ph -> ( th -> ta ) ) $.
    $( Triple syllogism deduction.  Deduction associated with ~ 3syld .
       (Contributed by Jeff Hankins, 4-Aug-2009.) $)
    3syld $p |- ( ph -> ( ps -> ta ) ) $=
      wph wps wth wta wph wps wch wth 3syld.1 3syld.2 syld 3syld.3 syld $.
  $}

  ${
    sylsyld.1 $e |- ( ph -> ps ) $.
    sylsyld.2 $e |- ( ph -> ( ch -> th ) ) $.
    sylsyld.3 $e |- ( ps -> ( th -> ta ) ) $.
    $( A double syllogism inference.  (Contributed by Alan Sare,
       20-Apr-2011.) $)
    sylsyld $p |- ( ph -> ( ch -> ta ) ) $=
      wph wch wth wta sylsyld.2 wph wps wth wta wi sylsyld.1 sylsyld.3 syl syld
      $.
  $}

  ${
    imim12i.1 $e |- ( ph -> ps ) $.
    imim12i.2 $e |- ( ch -> th ) $.
    $( Inference joining two implications.  Inference associated with
       ~ imim12 .  Its associated inference is ~ 3syl .  (Contributed by NM,
       12-Mar-1993.)  (Proof shortened by Mel L. O'Cat, 29-Oct-2011.) $)
    imim12i $p |- ( ( ps -> ch ) -> ( ph -> th ) ) $=
      wph wps wps wch wi wth imim12i.1 wch wth wps imim12i.2 imim2i syl5 $.
  $}

  ${
    imim1i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common consequents in an implication, thereby
       interchanging the original antecedent and consequent.  Inference
       associated with ~ imim1 .  Its associated inference is ~ syl .
       (Contributed by NM, 28-Dec-1992.)  (Proof shortened by Wolf Lammen,
       4-Aug-2012.) $)
    imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $=
      wph wps wch wch imim1i.1 wch id imim12i $.
  $}

  ${
    imim3i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference adding three nested antecedents.  (Contributed by NM,
       19-Dec-2006.) $)
    imim3i $p |- ( ( th -> ph ) -> ( ( th -> ps ) -> ( th -> ch ) ) ) $=
      wth wph wi wth wps wch wph wps wch wi wth imim3i.1 imim2i a2d $.
  $}

  ${
    sylc.1 $e |- ( ph -> ps ) $.
    sylc.2 $e |- ( ph -> ch ) $.
    sylc.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( A syllogism inference combined with contraction.  (Contributed by NM,
       4-May-1994.)  (Revised by NM, 13-Jul-2013.) $)
    sylc $p |- ( ph -> th ) $=
      wph wth wph wps wph wch wth sylc.1 sylc.2 sylc.3 syl2im pm2.43i $.
  $}

  ${
    syl3c.1 $e |- ( ph -> ps ) $.
    syl3c.2 $e |- ( ph -> ch ) $.
    syl3c.3 $e |- ( ph -> th ) $.
    syl3c.4 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    $( A syllogism inference combined with contraction.  (Contributed by Alan
       Sare, 7-Jul-2011.) $)
    syl3c $p |- ( ph -> ta ) $=
      wph wth wta syl3c.3 wph wps wch wth wta wi syl3c.1 syl3c.2 syl3c.4 sylc
      mpd $.
  $}

  ${
    syl6mpi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6mpi.2 $e |- th $.
    syl6mpi.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( A syllogism inference.  (Contributed by Alan Sare, 8-Jul-2011.)  (Proof
       shortened by Wolf Lammen, 13-Sep-2012.) $)
    syl6mpi $p |- ( ph -> ( ps -> ta ) ) $=
      wph wps wch wta syl6mpi.1 wch wth wta syl6mpi.2 syl6mpi.3 mpi syl6 $.
  $}

  ${
    mpsyl.1 $e |- ph $.
    mpsyl.2 $e |- ( ps -> ch ) $.
    mpsyl.3 $e |- ( ph -> ( ch -> th ) ) $.
    $( Modus ponens combined with a syllogism inference.  (Contributed by Alan
       Sare, 20-Apr-2011.) $)
    mpsyl $p |- ( ps -> th ) $=
      wps wph wch wth wph wps mpsyl.1 a1i mpsyl.2 mpsyl.3 sylc $.
  $}

  ${
    mpsylsyld.1 $e |- ph $.
    mpsylsyld.2 $e |- ( ps -> ( ch -> th ) ) $.
    mpsylsyld.3 $e |- ( ph -> ( th -> ta ) ) $.
    $( Modus ponens combined with a double syllogism inference.  (Contributed
       by Alan Sare, 22-Jul-2012.) $)
    mpsylsyld $p |- ( ps -> ( ch -> ta ) ) $=
      wps wph wch wth wta wph wps mpsylsyld.1 a1i mpsylsyld.2 mpsylsyld.3
      sylsyld $.
  $}

  ${
    syl6c.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6c.2 $e |- ( ph -> ( ps -> th ) ) $.
    syl6c.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( Inference combining ~ syl6 with contraction.  (Contributed by Alan Sare,
       2-May-2011.) $)
    syl6c $p |- ( ph -> ( ps -> ta ) ) $=
      wph wps wth wta syl6c.2 wph wps wch wth wta wi syl6c.1 syl6c.3 syl6 mpdd
      $.
  $}

  ${
    syl6ci.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ci.2 $e |- ( ph -> th ) $.
    syl6ci.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( A syllogism inference combined with contraction.  (Contributed by Alan
       Sare, 18-Mar-2012.) $)
    syl6ci $p |- ( ph -> ( ps -> ta ) ) $=
      wph wps wch wth wta syl6ci.1 wph wth wps syl6ci.2 a1d syl6ci.3 syl6c $.
  $}

  ${
    syldd.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syldd.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    $( Nested syllogism deduction.  Deduction associated with ~ syld .  Double
       deduction associated with ~ syl .  (Contributed by NM, 12-Dec-2004.)
       (Proof shortened by Wolf Lammen, 11-May-2013.) $)
    syldd $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      wph wps wth wta wi wch wth wi wch wta wi syldd.2 syldd.1 wth wta wch
      imim2 syl6c $.
  $}

  ${
    syl5d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl5d.2 $e |- ( ph -> ( th -> ( ch -> ta ) ) ) $.
    $( A nested syllogism deduction.  Deduction associated with ~ syl5 .
       (Contributed by NM, 14-May-1993.)  (Proof shortened by Josh Purinton,
       29-Dec-2000.)  (Proof shortened by Mel L. O'Cat, 2-Feb-2006.) $)
    syl5d $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $=
      wph wth wps wch wta wph wps wch wi wth syl5d.1 a1d syl5d.2 syldd $.
  $}

  ${
    syl7.1 $e |- ( ph -> ps ) $.
    syl7.2 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
    $( A syllogism rule of inference.  The first premise is used to replace the
       third antecedent of the second premise.  (Contributed by NM,
       12-Jan-1993.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)
    syl7 $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $=
      wch wph wps wth wta wph wps wi wch syl7.1 a1i syl7.2 syl5d $.
  $}

  ${
    syl6d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl6d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( A nested syllogism deduction.  Deduction associated with ~ syl6 .
       (Contributed by NM, 11-May-1993.)  (Proof shortened by Josh Purinton,
       29-Dec-2000.)  (Proof shortened by Mel L. O'Cat, 2-Feb-2006.) $)
    syl6d $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      wph wps wch wth wta syl6d.1 wph wth wta wi wps syl6d.2 a1d syldd $.
  $}

  ${
    syl8.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8.2 $e |- ( th -> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM, 1-Aug-1994.)
       (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)
    syl8 $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      wph wps wch wth wta syl8.1 wth wta wi wph syl8.2 a1i syl6d $.
  $}

  ${
    syl9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl9.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( A nested syllogism inference with different antecedents.  (Contributed
       by NM, 13-May-1993.)  (Proof shortened by Josh Purinton,
       29-Dec-2000.) $)
    syl9 $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $=
      wph wps wch wth wta syl9.1 wth wch wta wi wi wph syl9.2 a1i syl5d $.
  $}

  ${
    syl9r.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl9r.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( A nested syllogism inference with different antecedents.  (Contributed
       by NM, 14-May-1993.) $)
    syl9r $p |- ( th -> ( ph -> ( ps -> ta ) ) ) $=
      wph wth wps wta wi wph wps wch wth wta syl9r.1 syl9r.2 syl9 com12 $.
  $}

  ${
    syl10.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl10.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    syl10.3 $e |- ( ch -> ( ta -> et ) ) $.
    $( A nested syllogism inference.  (Contributed by Alan Sare,
       17-Jul-2011.) $)
    syl10 $p |- ( ph -> ( ps -> ( th -> et ) ) ) $=
      wph wps wth wta wet syl10.2 wph wps wch wta wet wi syl10.1 syl10.3 syl6
      syldd $.
  $}

  ${
    a1ddd.1 $e |- ( ph -> ( ps -> ( ch -> ta ) ) ) $.
    $( Triple deduction introducing an antecedent to a wff.  Deduction
       associated with ~ a1dd .  Double deduction associated with ~ a1d .
       Triple deduction associated with ~ ax-1 and ~ a1i .  (Contributed by
       Jeff Hankins, 4-Aug-2009.) $)
    a1ddd $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wta wth wta wi a1ddd.1 wta wth ax-1 syl8 $.
  $}

  ${
    imim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    imim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Deduction combining antecedents and consequents.  Deduction associated
       with ~ imim12 and ~ imim12i .  (Contributed by NM, 7-Aug-1994.)  (Proof
       shortened by Mel L. O'Cat, 30-Oct-2011.) $)
    imim12d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> ta ) ) ) $=
      wph wps wch wch wth wi wta imim12d.1 wph wth wta wch imim12d.2 imim2d
      syl5d $.
  $}

  ${
    imim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding nested consequents.  Deduction associated with ~ imim1
       and ~ imim1i .  (Contributed by NM, 3-Apr-1994.)  (Proof shortened by
       Wolf Lammen, 12-Sep-2012.) $)
    imim1d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> th ) ) ) $=
      wph wps wch wth wth imim1d.1 wph wth idd imim12d $.
  $}

  $( A closed form of syllogism (see ~ syl ).  Theorem *2.06 of
     [WhiteheadRussell] p. 100.  Its associated inference is ~ imim1i .
     (Contributed by NM, 29-Dec-1992.)  (Proof shortened by Wolf Lammen,
     25-May-2013.) $)
  imim1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    wph wps wi wph wps wch wph wps wi id imim1d $.

  $( Theorem *2.83 of [WhiteheadRussell] p. 108.  Closed form of ~ syld .
     (Contributed by NM, 3-Jan-2005.) $)
  pm2.83 $p |- ( ( ph -> ( ps -> ch ) )
      -> ( ( ph -> ( ch -> th ) ) -> ( ph -> ( ps -> th ) ) ) ) $=
    wps wch wi wch wth wi wps wth wi wph wps wch wth imim1 imim3i $.

  $( Over minimal implicational calculus, Peirce's axiom ~ peirce implies an
     axiom sometimes called "Roll",
     ` ( ( ( ph -> ps ) -> ch ) -> ( ( ch -> ph ) -> ph ) ) ` , of which
     ~ looinv is a special instance.  The converse also holds: substitute
     ` ( ph -> ps ) ` for ` ch ` in Roll and use ~ id and ~ ax-mp .
     (Contributed by BJ, 15-Jun-2021.) $)
  peirceroll $p |- ( ( ( ( ph -> ps ) -> ph ) -> ph )
                   -> ( ( ( ph -> ps ) -> ch ) -> ( ( ch -> ph ) -> ph ) ) ) $=
    wph wps wi wch wi wch wph wi wph wps wi wph wi wph wps wi wph wi wph wi wph
    wph wps wi wch wph imim1 wph wps wi wph wi wph wi id syl9r $.

  ${
    com3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Commutation of antecedents.  Swap 2nd and 3rd.  Deduction associated
       with ~ com12 .  (Contributed by NM, 27-Dec-1992.)  (Proof shortened by
       Wolf Lammen, 4-Aug-2012.) $)
    com23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
      wph wps wch wth wi wch wth com3.1 wch wth pm2.27 syl9 $.

    $( Commutation of antecedents.  Rotate right.  (Contributed by NM,
       25-Apr-1994.) $)
    com3r $p |- ( ch -> ( ph -> ( ps -> th ) ) ) $=
      wph wch wps wth wi wph wps wch wth com3.1 com23 com12 $.

    $( Commutation of antecedents.  Swap 1st and 3rd.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com13 $p |- ( ch -> ( ps -> ( ph -> th ) ) ) $=
      wch wph wps wth wph wps wch wth com3.1 com3r com23 $.

    $( Commutation of antecedents.  Rotate left.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com3l $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $=
      wch wph wps wth wph wps wch wth com3.1 com3r com3r $.
  $}

  $( Swap antecedents.  Theorem *2.04 of [WhiteheadRussell] p. 100.  This was
     the third axiom in Frege's logic system, specifically Proposition 8 of
     [Frege1879] p. 35.  Its associated inference is ~ com12 .  (Contributed by
     NM, 27-Dec-1992.)  (Proof shortened by Wolf Lammen, 12-Sep-2012.) $)
  pm2.04 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wph wps wch wph wps wch wi wi id com23 $.

  ${
    com4.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( Commutation of antecedents.  Swap 3rd and 4th.  Deduction associated
       with ~ com23 .  Double deduction associated with ~ com12 .  (Contributed
       by NM, 25-Apr-1994.) $)
    com34 $p |- ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) ) $=
      wph wps wch wth wta wi wi wth wch wta wi wi com4.1 wch wth wta pm2.04
      syl6 $.

    $( Commutation of antecedents.  Rotate left.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Mel L. O'Cat, 15-Aug-2004.) $)
    com4l $p |- ( ps -> ( ch -> ( th -> ( ph -> ta ) ) ) ) $=
      wps wch wph wth wta wph wps wch wth wta wi com4.1 com3l com34 $.

    $( Commutation of antecedents.  Rotate twice.  (Contributed by NM,
       25-Apr-1994.) $)
    com4t $p |- ( ch -> ( th -> ( ph -> ( ps -> ta ) ) ) ) $=
      wps wch wth wph wta wph wps wch wth wta com4.1 com4l com4l $.

    $( Commutation of antecedents.  Rotate right.  (Contributed by NM,
       25-Apr-1994.) $)
    com4r $p |- ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) $=
      wch wth wph wps wta wph wps wch wth wta com4.1 com4t com4l $.

    $( Commutation of antecedents.  Swap 2nd and 4th.  Deduction associated
       with ~ com13 .  (Contributed by NM, 25-Apr-1994.)  (Proof shortened by
       Wolf Lammen, 28-Jul-2012.) $)
    com24 $p |- ( ph -> ( th -> ( ch -> ( ps -> ta ) ) ) ) $=
      wch wth wph wps wta wi wph wps wch wth wta com4.1 com4t com13 $.

    $( Commutation of antecedents.  Swap 1st and 4th.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com14 $p |- ( th -> ( ps -> ( ch -> ( ph -> ta ) ) ) ) $=
      wps wch wth wph wta wi wph wps wch wth wta com4.1 com4l com3r $.
  $}

  ${
    com5.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
    $( Commutation of antecedents.  Swap 4th and 5th.  Deduction associated
       with ~ com34 .  Double deduction associated with ~ com23 .  Triple
       deduction associated with ~ com12 .  (Contributed by Jeff Hankins,
       28-Jun-2009.) $)
    com45 $p |- ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) $=
      wph wps wch wth wta wet wi wi wta wth wet wi wi com5.1 wth wta wet pm2.04
      syl8 $.

    $( Commutation of antecedents.  Swap 3rd and 5th.  Deduction associated
       with ~ com24 .  Double deduction associated with ~ com13 .  (Contributed
       by Jeff Hankins, 28-Jun-2009.) $)
    com35 $p |- ( ph -> ( ps -> ( ta -> ( th -> ( ch -> et ) ) ) ) ) $=
      wph wps wth wta wch wet wi wph wps wth wch wta wet wph wps wch wth wta
      wet wi com5.1 com34 com45 com34 $.

    $( Commutation of antecedents.  Swap 2nd and 5th.  Deduction associated
       with ~ com14 .  (Contributed by Jeff Hankins, 28-Jun-2009.) $)
    com25 $p |- ( ph -> ( ta -> ( ch -> ( th -> ( ps -> et ) ) ) ) ) $=
      wph wth wch wta wps wet wi wph wth wch wps wta wet wph wps wch wth wta
      wet wi com5.1 com24 com45 com24 $.

    $( Commutation of antecedents.  Rotate left.  (Contributed by Jeff Hankins,
       28-Jun-2009.)  (Proof shortened by Wolf Lammen, 29-Jul-2012.) $)
    com5l $p |- ( ps -> ( ch -> ( th -> ( ta -> ( ph -> et ) ) ) ) ) $=
      wps wch wth wph wta wet wph wps wch wth wta wet wi com5.1 com4l com45 $.

    $( Commutation of antecedents.  Swap 1st and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.)  (Proof shortened by Wolf Lammen,
       29-Jul-2012.) $)
    com15 $p |- ( ta -> ( ps -> ( ch -> ( th -> ( ph -> et ) ) ) ) ) $=
      wps wch wth wta wph wet wi wph wps wch wth wta wet com5.1 com5l com4r $.

    $( Commutation of antecedents.  Rotate left twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com52l $p |- ( ch -> ( th -> ( ta -> ( ph -> ( ps -> et ) ) ) ) ) $=
      wps wch wth wta wph wet wph wps wch wth wta wet com5.1 com5l com5l $.

    $( Commutation of antecedents.  Rotate right twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com52r $p |- ( th -> ( ta -> ( ph -> ( ps -> ( ch -> et ) ) ) ) ) $=
      wch wth wta wph wps wet wph wps wch wth wta wet com5.1 com52l com5l $.

    $( Commutation of antecedents.  Rotate right.  (Contributed by Wolf Lammen,
       29-Jul-2012.) $)
    com5r $p |- ( ta -> ( ph -> ( ps -> ( ch -> ( th -> et ) ) ) ) ) $=
      wch wth wta wph wps wet wph wps wch wth wta wet com5.1 com52l com52l $.
  $}

  $( Closed form of ~ imim12i and of ~ 3syl .  (Contributed by BJ,
     16-Jul-2019.) $)
  imim12 $p |- ( ( ph -> ps ) ->
                      ( ( ch -> th ) -> ( ( ps -> ch ) -> ( ph -> th ) ) ) ) $=
    wch wth wi wps wch wi wps wth wi wph wps wi wph wth wi wch wth wps imim2
    wph wps wth imim1 syl9r $.

  $( Elimination of a nested antecedent.  Sometimes called "Syll-Simp" since it
     is a syllogism applied to ~ ax-1 ("Simplification").  (Contributed by Wolf
     Lammen, 9-May-2013.) $)
  jarr $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    wps wph wps wi wch wps wph ax-1 imim1i $.

  ${
    jarri.1 $e |- ( ( ph -> ps ) -> ch ) $.
    $( Inference associated with ~ jarr .  Partial converse of ~ ja (the other
       partial converse being ~ jarli ).  (Contributed by Wolf Lammen,
       20-Sep-2013.) $)
    jarri $p |- ( ps -> ch ) $=
      wps wph wps wi wch wps wph ax-1 jarri.1 syl $.
  $}

  ${
    pm2.86d.1 $e |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $.
    $( Deduction associated with ~ pm2.86 .  (Contributed by NM, 29-Jun-1995.)
       (Proof shortened by Wolf Lammen, 3-Apr-2013.) $)
    pm2.86d $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      wph wch wps wth wch wps wch wi wph wps wth wi wch wps ax-1 pm2.86d.1 syl5
      com23 $.
  $}

  $( Converse of Axiom ~ ax-2 .  Theorem *2.86 of [WhiteheadRussell] p. 108.
     (Contributed by NM, 25-Apr-1994.)  (Proof shortened by Wolf Lammen,
     3-Apr-2013.) $)
  pm2.86 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) ->
                                                    ( ph -> ( ps -> ch ) ) ) $=
    wph wps wi wph wch wi wi wph wps wch wph wps wi wph wch wi wi id pm2.86d $.

  ${
    pm2.86i.1 $e |- ( ( ph -> ps ) -> ( ph -> ch ) ) $.
    $( Inference associated with ~ pm2.86 .  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Wolf Lammen, 3-Apr-2013.) $)
    pm2.86i $p |- ( ph -> ( ps -> ch ) ) $=
      wps wph wch wph wps wph wch wi pm2.86i.1 jarri com12 $.
  $}

  $( The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  See ~ loowoz for an alternate axiom.  (Contributed by Mel
     L. O'Cat, 12-Aug-2004.) $)
  loolin $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $=
    wph wps wi wps wph wi wi wps wph wph wps wps wph wi jarr pm2.43d $.

  $( An alternate for the Linearity Axiom of the infinite-valued sentential
     logic (L-infinity) of Lukasiewicz ~ loolin , due to Barbara Wozniakowska,
     _Reports on Mathematical Logic_ 10, 129-137 (1978).  (Contributed by Mel
     L. O'Cat, 8-Aug-2004.) $)
  loowoz $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) )
      -> ( ( ps -> ph ) -> ( ps -> ch ) ) ) $=
    wph wps wi wph wch wi wi wps wph wch wph wps wph wch wi jarr a2d $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical negation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section makes our first use of the third axiom of propositional
  calculus, ~ ax-3 .  It introduces logical negation.

$)

  $( Alias for ~ ax-3 to be used instead of it for labeling consistency.  Its
     associated inference is ~ con4i and its associated deduction is ~ con4d .
     (Contributed by BJ, 24-Dec-2020.) $)
  con4 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    wph wps ax-3 $.

  ${
    con4i.1 $e |- ( -. ph -> -. ps ) $.
    $( Inference associated with ~ con4 .  Its associated inference is ~ mt4 .

       Remark: this can also be proved using ~ notnot followed by ~ nsyl2 ,
       giving a shorter proof but depending on more axioms (namely, ~ ax-1 and
       ~ ax-2 ).  (Contributed by NM, 29-Dec-1992.) $)
    con4i $p |- ( ps -> ph ) $=
      wph wn wps wn wi wps wph wi con4i.1 wph wps con4 ax-mp $.
    $( $j usage 'con4i' avoids 'ax-1' 'ax-2'; $)
  $}

  ${
    con4d.1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( Deduction associated with ~ con4 .  (Contributed by NM, 26-Mar-1995.) $)
    con4d $p |- ( ph -> ( ch -> ps ) ) $=
      wph wps wn wch wn wi wch wps wi con4d.1 wps wch con4 syl $.
  $}

  ${
    mt4.1 $e |- ph $.
    mt4.2 $e |- ( -. ps -> -. ph ) $.
    $( The rule of modus tollens.  Inference associated with ~ con4i .
       (Contributed by Wolf Lammen, 12-May-2013.) $)
    mt4 $p |- ps $=
      wph wps mt4.1 wps wph mt4.2 con4i ax-mp $.
  $}

  ${
    mt4d.1 $e |- ( ph -> ps ) $.
    mt4d.2 $e |- ( ph -> ( -. ch -> -. ps ) ) $.
    $( Modus tollens deduction.  Deduction form of ~ mt4 .  (Contributed by NM,
       9-Jun-2006.) $)
    mt4d $p |- ( ph -> ch ) $=
      wph wps wch mt4d.1 wph wch wps mt4d.2 con4d mpd $.
  $}

  ${
    mt4i.1 $e |- ch $.
    mt4i.2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( Modus tollens inference.  (Contributed by Wolf Lammen, 12-May-2013.) $)
    mt4i $p |- ( ph -> ps ) $=
      wph wch wps wch wph mt4i.1 a1i mt4i.2 mt4d $.
  $}

  ${
    pm2.21i.1 $e |- -. ph $.
    $( A contradiction implies anything.  Inference associated with ~ pm2.21 .
       Its associated inference is ~ pm2.24ii .  (Contributed by NM,
       16-Sep-1993.) $)
    pm2.21i $p |- ( ph -> ps ) $=
      wps wph wph wn wps wn pm2.21i.1 a1i con4i $.
  $}

  ${
    pm2.24ii.1 $e |- ph $.
    pm2.24ii.2 $e |- -. ph $.
    $( A contradiction implies anything.  Inference associated with ~ pm2.21i
       and ~ pm2.24i .  (Contributed by NM, 27-Feb-2008.) $)
    pm2.24ii $p |- ps $=
      wph wps pm2.24ii.1 wph wps pm2.24ii.2 pm2.21i ax-mp $.
    $( $j usage 'pm2.24ii' avoids 'ax-2'; $)
  $}

  ${
    pm2.21d.1 $e |- ( ph -> -. ps ) $.
    $( A contradiction implies anything.  Deduction associated with ~ pm2.21 .
       (Contributed by NM, 10-Feb-1996.) $)
    pm2.21d $p |- ( ph -> ( ps -> ch ) ) $=
      wph wch wps wph wps wn wch wn pm2.21d.1 a1d con4d $.
  $}

  ${
    pm2.21ddALT.1 $e |- ( ph -> ps ) $.
    pm2.21ddALT.2 $e |- ( ph -> -. ps ) $.
    $( Alternate proof of ~ pm2.21dd .  (Contributed by Mario Carneiro,
       9-Feb-2017.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    pm2.21ddALT $p |- ( ph -> ch ) $=
      wph wps wch pm2.21ddALT.1 wph wps wch pm2.21ddALT.2 pm2.21d mpd $.
  $}

  $( From a wff and its negation, anything follows.  Theorem *2.21 of
     [WhiteheadRussell] p. 104.  Also called the Duns Scotus law.  Its commuted
     form is ~ pm2.24 and its associated inference is ~ pm2.21i .  (Contributed
     by NM, 29-Dec-1992.)  (Proof shortened by Wolf Lammen, 14-Sep-2012.) $)
  pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
    wph wn wph wps wph wn id pm2.21d $.

  $( Theorem *2.24 of [WhiteheadRussell] p. 104.  Its associated inference is
     ~ pm2.24i .  Commuted form of ~ pm2.21 .  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $=
    wph wn wph wps wph wps pm2.21 com12 $.

  $( Elimination of a nested antecedent.  (Contributed by Wolf Lammen,
     10-May-2013.) $)
  jarl $p |- ( ( ( ph -> ps ) -> ch ) -> ( -. ph -> ch ) ) $=
    wph wn wph wps wi wch wph wps pm2.21 imim1i $.

  ${
    jarli.1 $e |- ( ( ph -> ps ) -> ch ) $.
    $( Inference associated with ~ jarl .  Partial converse of ~ ja (the other
       partial converse being ~ jarri ).  (Contributed by Wolf Lammen,
       4-Oct-2013.) $)
    jarli $p |- ( -. ph -> ch ) $=
      wph wn wph wps wi wch wph wps pm2.21 jarli.1 syl $.
  $}

  ${
    pm2.18d.1 $e |- ( ph -> ( -. ps -> ps ) ) $.
    $( Deduction form of the Clavius law ~ pm2.18 .  (Contributed by FL,
       12-Jul-2009.)  (Proof shortened by Andrew Salmon, 7-May-2011.)  Revised
       to shorten ~ pm2.18 .  (Revised by Wolf Lammen, 17-Nov-2023.) $)
    pm2.18d $p |- ( ph -> ps ) $=
      wph wph wps wph id wph wps wn wps wph wn pm2.18d.1 wps wph wn pm2.21
      sylcom mt4d $.
  $}

  $( Clavius law, or "consequentia mirabilis" ("admirable consequence").  If a
     formula is implied by its negation, then it is true.  Can be used in
     proofs by contradiction.  Theorem *2.18 of [WhiteheadRussell] p. 103.  See
     also the weak Clavius law ~ pm2.01 .  (Contributed by NM, 29-Dec-1992.)
     (Proof shortened by Wolf Lammen, 17-Nov-2023.) $)
  pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $=
    wph wn wph wi wph wph wn wph wi id pm2.18d $.

  ${
    pm2.18i.1 $e |- ( -. ph -> ph ) $.
    $( Inference associated with the Clavius law ~ pm2.18 .  (Contributed by
       BJ, 30-Mar-2020.) $)
    pm2.18i $p |- ph $=
      wph wn wph wi wph pm2.18i.1 wph pm2.18 ax-mp $.
  $}

  $( Double negation elimination.  Converse of ~ notnot and one implication of
     ~ notnotb .  Theorem *2.14 of [WhiteheadRussell] p. 102.  This was the
     fifth axiom of Frege, specifically Proposition 31 of [Frege1879] p. 44.
     In classical logic (our logic) this is always true.  In intuitionistic
     logic this is not always true, and formulas for which it is true are
     called "stable".  (Contributed by NM, 29-Dec-1992.)  (Proof shortened by
     David Harvey, 5-Sep-1999.)  (Proof shortened by Josh Purinton,
     29-Dec-2000.) $)
  notnotr $p |- ( -. -. ph -> ph ) $=
    wph wn wph wph wph pm2.18 jarli $.

  ${
    notnotri.1 $e |- -. -. ph $.
    $( Inference associated with ~ notnotr .  For a shorter proof using
       ~ ax-2 , see ~ notnotriALT .  (Contributed by NM, 27-Feb-2008.)  (Proof
       shortened by Wolf Lammen, 15-Jul-2021.)  Remove dependency on ~ ax-2 .
       (Revised by Steven Nguyen, 27-Dec-2022.) $)
    notnotri $p |- ph $=
      wph wn wn wph notnotri.1 wph wn wph wn wn wn notnotri.1 pm2.21i mt4 $.
    $( $j usage 'notnotri' avoids 'ax-2'; $)

    $( Alternate proof of ~ notnotri .  The proof via ~ notnotr and ~ ax-mp
       also has three essential steps, but has a total number of steps equal to
       8, instead of the present 7, because it has to construct the formula
       ` ph ` twice and the formula ` -. -. ph ` once, whereas the present
       proof has to construct the formula ` ph ` twice and the formula
       ` -. ph ` once, and therefore makes only one use of ~ wn instead of two.
       This can be checked by running the Metamath command "MM> SHOW PROOF
       notnotri / NORMAL".  (Contributed by NM, 27-Feb-2008.)  (Proof shortened
       by Wolf Lammen, 15-Jul-2021.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    notnotriALT $p |- ph $=
      wph wph wn wph notnotri.1 pm2.21i pm2.18i $.
  $}

  ${
    notnotrd.1 $e |- ( ph -> -. -. ps ) $.
    $( Deduction associated with ~ notnotr and ~ notnotri .  Double negation
       elimination rule.  A translation of the natural deduction rule ` -. -. `
       C , ` _G |- -. -. ps => _G |- ps ` ; see ~ natded .  This is Definition
       NNC in [Pfenning] p. 17.  This rule is valid in classical logic (our
       logic), but not in intuitionistic logic.  (Contributed by DAW,
       8-Feb-2017.) $)
    notnotrd $p |- ( ph -> ps ) $=
      wph wps wn wn wps notnotrd.1 wps notnotr syl $.
  $}

  ${
    con2d.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 19-Aug-1993.) $)
    con2d $p |- ( ph -> ( ch -> -. ps ) ) $=
      wph wps wn wch wps wn wn wps wph wch wn wps notnotr con2d.1 syl5 con4d $.
  $}

  $( Contraposition.  Theorem *2.03 of [WhiteheadRussell] p. 100.  (Contributed
     by NM, 29-Dec-1992.)  (Proof shortened by Wolf Lammen, 12-Feb-2013.) $)
  con2 $p |- ( ( ph -> -. ps ) -> ( ps -> -. ph ) ) $=
    wph wps wn wi wph wps wph wps wn wi id con2d $.

  ${
    mt2d.1 $e |- ( ph -> ch ) $.
    mt2d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens deduction.  (Contributed by NM, 4-Jul-1994.) $)
    mt2d $p |- ( ph -> -. ps ) $=
      wph wch wps wn mt2d.1 wph wps wch mt2d.2 con2d mpd $.
  $}

  ${
    mt2i.1 $e |- ch $.
    mt2i.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens inference.  (Contributed by NM, 26-Mar-1995.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
    mt2i $p |- ( ph -> -. ps ) $=
      wph wps wch wch wph mt2i.1 a1i mt2i.2 mt2d $.
  $}

  ${
    nsyl3.1 $e |- ( ph -> -. ps ) $.
    nsyl3.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference.  (Contributed by NM, 1-Dec-1995.) $)
    nsyl3 $p |- ( ch -> -. ph ) $=
      wch wph wps nsyl3.2 wph wps wn wi wch nsyl3.1 a1i mt2d $.
  $}

  ${
    con2i.a $e |- ( ph -> -. ps ) $.
    $( A contraposition inference.  Its associated inference is ~ mt2 .
       (Contributed by NM, 10-Jan-1993.)  (Proof shortened by Mel L. O'Cat,
       28-Nov-2008.)  (Proof shortened by Wolf Lammen, 13-Jun-2013.) $)
    con2i $p |- ( ps -> -. ph ) $=
      wph wps wps con2i.a wps id nsyl3 $.
  $}

  ${
    nsyl.1 $e |- ( ph -> -. ps ) $.
    nsyl.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference.  (Contributed by NM, 31-Dec-1993.)
       (Proof shortened by Wolf Lammen, 2-Mar-2013.) $)
    nsyl $p |- ( ph -> -. ch ) $=
      wch wph wph wps wch nsyl.1 nsyl.2 nsyl3 con2i $.
  $}

  ${
    nsyl2.1 $e |- ( ph -> -. ps ) $.
    nsyl2.2 $e |- ( -. ch -> ps ) $.
    $( A negated syllogism inference.  (Contributed by NM, 26-Jun-1994.)
       (Proof shortened by Wolf Lammen, 14-Nov-2023.) $)
    nsyl2 $p |- ( ph -> ch ) $=
      wch wph wph wps wch wn nsyl2.1 nsyl2.2 nsyl3 con4i $.
  $}

  $( Double negation introduction.  Converse of ~ notnotr and one implication
     of ~ notnotb .  Theorem *2.12 of [WhiteheadRussell] p. 101.  This was the
     sixth axiom of Frege, specifically Proposition 41 of [Frege1879] p. 47.
     (Contributed by NM, 28-Dec-1992.)  (Proof shortened by Wolf Lammen,
     2-Mar-2013.) $)
  notnot $p |- ( ph -> -. -. ph ) $=
    wph wn wph wph wn id con2i $.

  ${
    notnoti.1 $e |- ph $.
    $( Inference associated with ~ notnot .  (Contributed by NM,
       27-Feb-2008.) $)
    notnoti $p |- -. -. ph $=
      wph wph wn wn notnoti.1 wph notnot ax-mp $.
  $}

  ${
    notnotd.1 $e |- ( ph -> ps ) $.
    $( Deduction associated with ~ notnot and ~ notnoti .  (Contributed by
       Jarvin Udandy, 2-Sep-2016.)  Avoid biconditional.  (Revised by Wolf
       Lammen, 27-Mar-2021.) $)
    notnotd $p |- ( ph -> -. -. ps ) $=
      wph wps wps wn wn notnotd.1 wps notnot syl $.
  $}

  ${
    con1d.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 27-Dec-1992.) $)
    con1d $p |- ( ph -> ( -. ch -> ps ) ) $=
      wph wps wch wn wph wps wn wch wch wn wn con1d.1 wch notnot syl6 con4d $.
  $}

  $( Contraposition.  Theorem *2.15 of [WhiteheadRussell] p. 102.  Its
     associated inference is ~ con1i .  (Contributed by NM, 29-Dec-1992.)
     (Proof shortened by Wolf Lammen, 12-Feb-2013.) $)
  con1 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $=
    wph wn wps wi wph wps wph wn wps wi id con1d $.

  ${
    con1i.1 $e |- ( -. ph -> ps ) $.
    $( A contraposition inference.  Inference associated with ~ con1 .  Its
       associated inference is ~ mt3 .  (Contributed by NM, 3-Jan-1993.)
       (Proof shortened by Mel L. O'Cat, 28-Nov-2008.)  (Proof shortened by
       Wolf Lammen, 19-Jun-2013.) $)
    con1i $p |- ( -. ps -> ph ) $=
      wps wn wps wph wps wn id con1i.1 nsyl2 $.
  $}

  ${
    mt3d.1 $e |- ( ph -> -. ch ) $.
    mt3d.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Modus tollens deduction.  (Contributed by NM, 26-Mar-1995.) $)
    mt3d $p |- ( ph -> ps ) $=
      wph wch wn wps mt3d.1 wph wps wch mt3d.2 con1d mpd $.
  $}

  ${
    mt3i.1 $e |- -. ch $.
    mt3i.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Modus tollens inference.  (Contributed by NM, 26-Mar-1995.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
    mt3i $p |- ( ph -> ps ) $=
      wph wps wch wch wn wph mt3i.1 a1i mt3i.2 mt3d $.
  $}

  ${
    pm2.24i.1 $e |- ph $.
    $( Inference associated with ~ pm2.24 .  Its associated inference is
       ~ pm2.24ii .  (Contributed by NM, 20-Aug-2001.) $)
    pm2.24i $p |- ( -. ph -> ps ) $=
      wps wph wph wps wn pm2.24i.1 a1i con1i $.
  $}

  ${
    pm2.24d.1 $e |- ( ph -> ps ) $.
    $( Deduction form of ~ pm2.24 .  (Contributed by NM, 30-Jan-2006.) $)
    pm2.24d $p |- ( ph -> ( -. ps -> ch ) ) $=
      wph wch wps wph wps wch wn pm2.24d.1 a1d con1d $.
  $}

  ${
    con3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A contraposition deduction.  Deduction form of ~ con3 .  (Contributed by
       NM, 10-Jan-1993.) $)
    con3d $p |- ( ph -> ( -. ch -> -. ps ) ) $=
      wph wps wn wch wps wn wn wps wph wch wps notnotr con3d.1 syl5 con1d $.
  $}

  $( Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  This was the
     fourth axiom of Frege, specifically Proposition 28 of [Frege1879] p. 43.
     Its associated inference is ~ con3i .  (Contributed by NM, 29-Dec-1992.)
     (Proof shortened by Wolf Lammen, 13-Feb-2013.) $)
  con3 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    wph wps wi wph wps wph wps wi id con3d $.

  ${
    con3i.a $e |- ( ph -> ps ) $.
    $( A contraposition inference.  Inference associated with ~ con3 .  Its
       associated inference is ~ mto .  (Contributed by NM, 3-Jan-1993.)
       (Proof shortened by Wolf Lammen, 20-Jun-2013.) $)
    con3i $p |- ( -. ps -> -. ph ) $=
      wps wn wps wph wps wn id con3i.a nsyl $.
  $}

  ${
    con3rr3.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Rotate through consequent right.  (Contributed by Wolf Lammen,
       3-Nov-2013.) $)
    con3rr3 $p |- ( -. ch -> ( ph -> -. ps ) ) $=
      wph wch wn wps wn wph wps wch con3rr3.1 con3d com12 $.
  $}

  ${
    nsyld.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    nsyld.2 $e |- ( ph -> ( ta -> ch ) ) $.
    $( A negated syllogism deduction.  (Contributed by NM, 9-Apr-2005.) $)
    nsyld $p |- ( ph -> ( ps -> -. ta ) ) $=
      wph wps wch wn wta wn nsyld.1 wph wta wch nsyld.2 con3d syld $.
  $}

 
 ${
    nsyl4.1 $e |- ( ph -> ps ) $.
    nsyl4.2 $e |- ( -. ph -> ch ) $.
    $( A negated syllogism inference.  (Contributed by NM, 15-Feb-1996.) $)
    nsyl4 $p |- ( -. ch -> ps ) $=
      wch wn wph wps wph wch nsyl4.2 con1i nsyl4.1 syl $.

    $( A negated syllogism inference.  (Contributed by Wolf Lammen,
       20-May-2024.) $)
    nsyl5 $p |- ( -. ps -> ch ) $=
      wch wps wph wps wch nsyl4.1 nsyl4.2 nsyl4 con1i $.
  $}

  $( Theorem *3.2 of [WhiteheadRussell] p. 111, expressed with primitive
     connectives (see ~ pm3.2 ).  (Contributed by NM, 29-Dec-1992.)  (Proof
     shortened by Josh Purinton, 29-Dec-2000.) $)
  pm3.2im $p |- ( ph -> ( ps -> -. ( ph -> -. ps ) ) ) $=
    wph wph wps wn wi wps wph wps wn pm2.27 con2d $.

  ${
    jc.1 $e |- ( ph -> ps ) $.
    jc.2 $e |- ( ph -> ch ) $.
    $( Deduction joining the consequents of two premises.  A deduction
       associated with ~ pm3.2im .  (Contributed by NM, 28-Dec-1992.) $)
    jc $p |- ( ph -> -. ( ps -> -. ch ) ) $=
      wph wps wch wps wch wn wi wn jc.1 jc.2 wps wch pm3.2im sylc $.
  $}

  $( Theorem joining the consequents of two premises.  Theorem 8 of [Margaris]
     p. 60.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Josh
     Purinton, 29-Dec-2000.) $)
  jcn $p |- ( ph -> ( -. ps -> -. ( ph -> ps ) ) ) $=
    wph wph wps wi wps wph wps pm2.27 con3d $.

  ${
    jcnd.1 $e |- ( ph -> ps ) $.
    jcnd.2 $e |- ( ph -> -. ch ) $.
    $( Deduction joining the consequents of two premises.  (Contributed by
       Glauco Siliprandi, 11-Dec-2019.)  (Proof shortened by Wolf Lammen,
       10-Apr-2024.) $)
    jcnd $p |- ( ph -> -. ( ps -> ch ) ) $=
      wph wps wch wn wps wch wi wn jcnd.1 jcnd.2 wps wch jcn sylc $.
  $}

  ${
    impi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( An importation inference.  (Contributed by NM, 29-Dec-1992.)  (Proof
       shortened by Wolf Lammen, 20-Jul-2013.) $)
    impi $p |- ( -. ( ph -> -. ps ) -> ch ) $=
      wch wph wps wn wi wph wps wch impi.1 con3rr3 con1i $.
  $}

  ${
    expi.1 $e |- ( -. ( ph -> -. ps ) -> ch ) $.
    $( An exportation inference.  (Contributed by NM, 29-Dec-1992.)  (Proof
       shortened by Mel L. O'Cat, 28-Nov-2008.) $)
    expi $p |- ( ph -> ( ps -> ch ) ) $=
      wph wps wph wps wn wi wn wch wph wps pm3.2im expi.1 syl6 $.
  $}

  $( Simplification.  Similar to Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 3-Jan-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)
  simprim $p |- ( -. ( ph -> -. ps ) -> ps ) $=
    wph wps wps wph wps idd impi $.

  $( Simplification.  Similar to Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 3-Jan-1993.)  (Proof shortened by Wolf
     Lammen, 21-Jul-2012.) $)
  simplim $p |- ( -. ( ph -> ps ) -> ph ) $=
    wph wph wps wi wph wps pm2.21 con1i $.

  $( General instance of Theorem *2.5 of [WhiteheadRussell] p. 107.
     (Contributed by NM, 3-Jan-2005.)  (Proof shortened by Wolf Lammen,
     9-Oct-2012.) $)
  pm2.5g $p |- ( -. ( ph -> ps ) -> ( -. ph -> ch ) ) $=
    wph wps wi wn wph wch wph wps simplim pm2.24d $.

  $( Theorem *2.5 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.5 $p |- ( -. ( ph -> ps ) -> ( -. ph -> ps ) ) $=
    wph wps wps pm2.5g $.

  $( Contrapositive of ~ ax-1 .  (Contributed by BJ, 28-Oct-2023.) $)
  conax1 $p |- ( -. ( ph -> ps ) -> -. ps ) $=
    wps wph wps wi wps wph ax-1 con3i $.

  $( Weakening of ~ conax1 .  General instance of ~ pm2.51 and of ~ pm2.52 .
     (Contributed by BJ, 28-Oct-2023.) $)
  conax1k $p |- ( -. ( ph -> ps ) -> ( ch -> -. ps ) ) $=
    wph wps wi wn wps wn wch wph wps conax1 a1d $.

  $( Theorem *2.51 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.51 $p |- ( -. ( ph -> ps ) -> ( ph -> -. ps ) ) $=
    wph wps wph conax1k $.

  $( Theorem *2.52 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 8-Oct-2012.) $)
  pm2.52 $p |- ( -. ( ph -> ps ) -> ( -. ph -> -. ps ) ) $=
    wph wps wph wn conax1k $.

  $( A general instance of Theorem *2.521 of [WhiteheadRussell] p. 107.
     (Contributed by BJ, 28-Oct-2023.) $)
  pm2.521g $p |- ( -. ( ph -> ps ) -> ( ps -> ch ) ) $=
    wph wps wi wn wps wch wph wps conax1 pm2.21d $.

  $( A general instance of Theorem *2.521 of [WhiteheadRussell] p. 107.
     (Contributed by NM, 3-Jan-2005.)  (Proof shortened by Wolf Lammen,
     8-Oct-2012.) $)
  pm2.521g2 $p |- ( -. ( ph -> ps ) -> ( ch -> ph ) ) $=
    wph wps wi wn wph wch wph wps simplim a1d $.

  $( Theorem *2.521 of [WhiteheadRussell] p. 107.  Instance of ~ pm2.521g and
     of ~ pm2.521g2 .  (Contributed by NM, 3-Jan-2005.) $)
  pm2.521 $p |- ( -. ( ph -> ps ) -> ( ps -> ph ) ) $=
    wph wps wph pm2.521g $.

  $( Exportation theorem ~ pm3.3 (closed form of ~ ex ) expressed with
     primitive connectives.  (Contributed by NM, 28-Dec-1992.) $)
  expt $p |- ( ( -. ( ph -> -. ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    wph wph wps wn wi wn wch wi wps wch wi wph wps wph wps wn wi wn wch wph wps
    pm3.2im imim1d com12 $.

  $( Importation theorem ~ pm3.1 (closed form of ~ imp ) expressed with
     primitive connectives.  (Contributed by NM, 25-Apr-1994.)  (Proof
     shortened by Wolf Lammen, 20-Jul-2013.) $)
  impt $p |- ( ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ch ) ) $=
    wph wps wch wi wi wph wps wn wi wn wps wch wph wps simprim wph wps wn wi wn
    wph wps wch wi wph wps wn simplim imim1i mpdi $.

  ${
    pm2.61d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61d.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Deduction eliminating an antecedent.  (Contributed by NM, 27-Apr-1994.)
       (Proof shortened by Wolf Lammen, 12-Sep-2013.) $)
    pm2.61d $p |- ( ph -> ch ) $=
      wph wch wph wch wn wps wch wph wps wch pm2.61d.2 con1d pm2.61d.1 syld
      pm2.18d $.
  $}

  ${
    pm2.61d1.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61d1.2 $e |- ( -. ps -> ch ) $.
    $( Inference eliminating an antecedent.  (Contributed by NM,
       15-Jul-2005.) $)
    pm2.61d1 $p |- ( ph -> ch ) $=
      wph wps wch pm2.61d1.1 wps wn wch wi wph pm2.61d1.2 a1i pm2.61d $.
  $}

  ${
    pm2.61d2.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    pm2.61d2.2 $e |- ( ps -> ch ) $.
    $( Inference eliminating an antecedent.  (Contributed by NM,
       18-Aug-1993.) $)
    pm2.61d2 $p |- ( ph -> ch ) $=
      wph wps wch wps wch wi wph pm2.61d2.2 a1i pm2.61d2.1 pm2.61d $.
  $}

  ${
    pm2.61i.1 $e |- ( ph -> ps ) $.
    pm2.61i.2 $e |- ( -. ph -> ps ) $.
    $( Inference eliminating an antecedent.  (Contributed by NM, 5-Apr-1994.)
       (Proof shortened by Wolf Lammen, 19-Nov-2023.) $)
    pm2.61i $p |- ps $=
      wps wph wps wps pm2.61i.1 pm2.61i.2 nsyl4 pm2.18i $.
  $}

  ${
    pm2.61ii.1 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
    pm2.61ii.2 $e |- ( ph -> ch ) $.
    pm2.61ii.3 $e |- ( ps -> ch ) $.
    $( Inference eliminating two antecedents.  (Contributed by NM, 4-Jan-1993.)
       (Proof shortened by Josh Purinton, 29-Dec-2000.) $)
    pm2.61ii $p |- ch $=
      wph wch pm2.61ii.2 wph wn wps wch pm2.61ii.1 pm2.61ii.3 pm2.61d2 pm2.61i
      $.
  $}

  ${
    pm2.61nii.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61nii.2 $e |- ( -. ph -> ch ) $.
    pm2.61nii.3 $e |- ( -. ps -> ch ) $.
    $( Inference eliminating two antecedents.  (Contributed by NM,
       13-Jul-2005.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
       shortened by Wolf Lammen, 13-Nov-2012.) $)
    pm2.61nii $p |- ch $=
      wph wch wph wps wch pm2.61nii.1 pm2.61nii.3 pm2.61d1 pm2.61nii.2 pm2.61i
      $.
  $}

  ${
    pm2.61iii.1 $e |- ( -. ph -> ( -. ps -> ( -. ch -> th ) ) ) $.
    pm2.61iii.2 $e |- ( ph -> th ) $.
    pm2.61iii.3 $e |- ( ps -> th ) $.
    pm2.61iii.4 $e |- ( ch -> th ) $.
    $( Inference eliminating three antecedents.  (Contributed by NM,
       2-Jan-2002.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
    pm2.61iii $p |- th $=
      wch wth pm2.61iii.4 wph wps wch wn wth wi pm2.61iii.1 wph wth wch wn
      pm2.61iii.2 a1d wps wth wch wn pm2.61iii.3 a1d pm2.61ii pm2.61i $.
  $}

  ${
    ja.1 $e |- ( -. ph -> ch ) $.
    ja.2 $e |- ( ps -> ch ) $.
    $( Inference joining the antecedents of two premises.  For partial
       converses, see ~ jarri and ~ jarli .  (Contributed by NM, 24-Jan-1993.)
       (Proof shortened by Mel L. O'Cat, 19-Feb-2008.) $)
    ja $p |- ( ( ph -> ps ) -> ch ) $=
      wph wps wi wph wch wps wch wph ja.2 imim2i ja.1 pm2.61d1 $.
  $}

  ${
    jad.1 $e |- ( ph -> ( -. ps -> th ) ) $.
    jad.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Deduction form of ~ ja .  (Contributed by Scott Fenton, 13-Dec-2010.)
       (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
    jad $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $=
      wps wch wi wph wth wps wch wph wth wi wph wps wn wth jad.1 com12 wph wch
      wth jad.2 com12 ja com12 $.
  $}

  $( Weak Clavius law.  If a formula implies its negation, then it is false.  A
     form of "reductio ad absurdum", which can be used in proofs by
     contradiction.  Theorem *2.01 of [WhiteheadRussell] p. 100.  Provable in
     minimal calculus, contrary to the Clavius law ~ pm2.18 .  (Contributed by
     NM, 18-Aug-1993.)  (Proof shortened by Mel L. O'Cat, 21-Nov-2008.)  (Proof
     shortened by Wolf Lammen, 31-Oct-2012.) $)
  pm2.01 $p |- ( ( ph -> -. ph ) -> -. ph ) $=
    wph wph wn wph wn wph wn id wph wn id ja $.

  ${
    pm2.01d.1 $e |- ( ph -> ( ps -> -. ps ) ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by Wolf Lammen, 5-Mar-2013.) $)
    pm2.01d $p |- ( ph -> -. ps ) $=
      wph wps wps wn pm2.01d.1 wps wn id pm2.61d1 $.
  $}

  $( Theorem *2.6 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.6 $p |- ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    wph wn wps wi wph wps wps wph wn wps wi id wph wn wps wi wps idd jad $.

  $( Theorem *2.61 of [WhiteheadRussell] p. 107.  Useful for eliminating an
     antecedent.  (Contributed by NM, 4-Jan-1993.)  (Proof shortened by Wolf
     Lammen, 22-Sep-2013.) $)
  pm2.61 $p |- ( ( ph -> ps ) -> ( ( -. ph -> ps ) -> ps ) ) $=
    wph wn wps wi wph wps wi wps wph wps pm2.6 com12 $.

  $( Theorem *2.65 of [WhiteheadRussell] p. 107.  Proof by contradiction.
     (Contributed by NM, 21-Jun-1993.)  (Proof shortened by Wolf Lammen,
     8-Mar-2013.) $)
  pm2.65 $p |- ( ( ph -> ps ) -> ( ( ph -> -. ps ) -> -. ph ) ) $=
    wph wps wi wph wps wn wph wn wph wps wi wph wn idd wph wps con3 jad $.

  ${
    pm2.65i.1 $e |- ( ph -> ps ) $.
    pm2.65i.2 $e |- ( ph -> -. ps ) $.
    $( Inference for proof by contradiction.  (Contributed by NM, 18-May-1994.)
       (Proof shortened by Wolf Lammen, 11-Sep-2013.) $)
    pm2.65i $p |- -. ph $=
      wps wph wn wph wps pm2.65i.2 con2i wph wps pm2.65i.1 con3i pm2.61i $.
  $}

  ${
    pm2.21dd.1 $e |- ( ph -> ps ) $.
    pm2.21dd.2 $e |- ( ph -> -. ps ) $.
    $( A contradiction implies anything.  Deduction from ~ pm2.21 .
       (Contributed by Mario Carneiro, 9-Feb-2017.)  (Proof shortened by Wolf
       Lammen, 22-Jul-2019.) $)
    pm2.21dd $p |- ( ph -> ch ) $=
      wph wch wph wps pm2.21dd.1 pm2.21dd.2 pm2.65i pm2.21i $.
  $}

  ${
    pm2.65d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.65d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Deduction for proof by contradiction.  (Contributed by NM, 26-Jun-1994.)
       (Proof shortened by Wolf Lammen, 26-May-2013.) $)
    pm2.65d $p |- ( ph -> -. ps ) $=
      wph wps wph wps wch wps pm2.65d.2 pm2.65d.1 nsyld pm2.01d $.
  $}

  ${
    mto.1 $e |- -. ps $.
    mto.2 $e |- ( ph -> ps ) $.
    $( The rule of modus tollens.  The rule says, "if ` ps ` is not true, and
       ` ph ` implies ` ps ` , then ` ph ` must also be not true".  Modus
       tollens is short for "modus tollendo tollens", a Latin phrase that means
       "the mode that by denying denies" - remark in [Sanford] p. 39.  It is
       also called denying the consequent.  Modus tollens is closely related to
       modus ponens ~ ax-mp .  Note that this rule is also valid in
       intuitionistic logic.  Inference associated with ~ con3i .  (Contributed
       by NM, 19-Aug-1993.)  (Proof shortened by Wolf Lammen, 11-Sep-2013.) $)
    mto $p |- -. ph $=
      wph wps mto.2 wps wn wph mto.1 a1i pm2.65i $.
  $}

  ${
    mtod.1 $e |- ( ph -> -. ch ) $.
    mtod.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus tollens deduction.  (Contributed by NM, 3-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 11-Sep-2013.) $)
    mtod $p |- ( ph -> -. ps ) $=
      wph wps wch mtod.2 wph wch wn wps mtod.1 a1d pm2.65d $.
  $}

  ${
    mtoi.1 $e |- -. ch $.
    mtoi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus tollens inference.  (Contributed by NM, 5-Jul-1994.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
    mtoi $p |- ( ph -> -. ps ) $=
      wph wps wch wch wn wph mtoi.1 a1i mtoi.2 mtod $.
  $}

  ${
    mt2.1 $e |- ps $.
    mt2.2 $e |- ( ph -> -. ps ) $.
    $( A rule similar to modus tollens.  Inference associated with ~ con2i .
       (Contributed by NM, 19-Aug-1993.)  (Proof shortened by Wolf Lammen,
       10-Sep-2013.) $)
    mt2 $p |- -. ph $=
      wph wps wps wph mt2.1 a1i mt2.2 pm2.65i $.
  $}

  ${
    mt3.1 $e |- -. ps $.
    mt3.2 $e |- ( -. ph -> ps ) $.
    $( A rule similar to modus tollens.  Inference associated with ~ con1i .
       (Contributed by NM, 18-May-1994.)  (Proof shortened by Wolf Lammen,
       11-Sep-2013.) $)
    mt3 $p |- ph $=
      wph wph wn wps mt3.1 mt3.2 mto notnotri $.
  $}

  $( Peirce's axiom.  A non-intuitionistic implication-only statement.  Added
     to intuitionistic (implicational) propositional calculus, it gives
     classical (implicational) propositional calculus.  For another
     non-intuitionistic positive statement, see ~ curryax .  When ` F. ` is
     substituted for ` ps ` , then this becomes the Clavius law ~ pm2.18 .
     (Contributed by NM, 29-Dec-1992.)  (Proof shortened by Wolf Lammen,
     9-Oct-2012.) $)
  peirce $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    wph wps wi wph wph wph wps simplim wph id ja $.

  $( The Inversion Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  Using ~ dfor2 , we can see that this essentially
     expresses "disjunction commutes".  Theorem *2.69 of [WhiteheadRussell]
     p. 108.  It is a special instance of the axiom "Roll", see ~ peirceroll .
     (Contributed by NM, 12-Aug-2004.) $)
  looinv $p |- ( ( ( ph -> ps ) -> ps ) -> ( ( ps -> ph ) -> ph ) ) $=
    wph wps wi wps wi wps wph wi wph wps wi wph wi wph wph wps wi wps wph imim1
    wph wps peirce syl6 $.

  $( A self-implication (see ~ id ) does not imply its own negation.  The
     justification theorem ~ bijust is one of its instances.  (Contributed by
     NM, 11-May-1999.)  (Proof shortened by Josh Purinton, 29-Dec-2000.)
     Extract ~ bijust0 from proof of ~ bijust .  (Revised by BJ,
     19-Mar-2020.) $)
  bijust0 $p |- -. ( ( ph -> ph ) -> -. ( ph -> ph ) ) $=
    wph wph wi wph wph wi wn wi wph wph wi wph id wph wph wi pm2.01 mt2 $.

  $( Theorem used to justify the definition of the biconditional ~ df-bi .
     Instance of ~ bijust0 .  (Contributed by NM, 11-May-1999.) $)
  bijust $p |- -. ( ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) )
                   -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
              -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) )
                   -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) ) $=
    wph wps wi wps wph wi wn wi wn bijust0 $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical equivalence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Definition ~ df-bi in this section is our first definition, which
  introduces and defines the biconditional connective ` <-> ` used to denote
  logical equivalence.  We define a wff of the form ` ( ph <-> ps ) ` as an
  abbreviation for ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` .

  Unlike most traditional developments, we have chosen not to have a separate
  symbol such as "Df." to mean "is defined as".  Instead, we will later use the
  biconditional connective for this purpose ( ~ df-an is its first use), as it
  allows us to use logic to manipulate definitions directly.  This greatly
  simplifies many proofs since it eliminates the need for a separate mechanism
  for introducing and eliminating definitions.

  A note on definitions: definitions are required to be eliminable (that is, a
  theorem stated in terms of the defined symbol can also be stated without it)
  and conservative (that is, a theorem whose statement does not contain the
  defined symbol can be proved without using that definition).  This means that
  a definition does not increase the expressive power nor the deductive power,
  respectively, of a theory.  On the other hand, definitions are often useful
  to write shorter proofs, so in (i)set.mm we will generally not try to avoid
  them.  This is why, for instance, some theorems which do not contain
  disjunction in their statement are placed after the section on disjunction
  because a shorter proof using disjunction is possible.

$)

  $( Declare the biconditional connective. $)
  $c <-> $.  $( Bidirectional arrow (read:  "if and only if" or
                "is logically equivalent to") $)

  $( Extend wff definition to include the biconditional connective. $)
  wb $a wff ( ph <-> ps ) $.

  $( Define the biconditional (logical "iff" or "if and only if"), also called
     biimplication.

     Definition ~ df-bi in this section is our first definition, which
     introduces and defines the biconditional connective ` <-> ` .  We define a
     wff of the form ` ( ph <-> ps ) ` as an abbreviation for
     ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` .

     Unlike most traditional developments, we have chosen not to have a
     separate symbol such as "Df." to mean "is defined as".  Instead, we will
     later use the biconditional connective for this purpose ( ~ df-or is its
     first use), as it allows us to use logic to manipulate definitions
     directly.  This greatly simplifies many proofs since it eliminates the
     need for a separate mechanism for introducing and eliminating definitions.
     Of course, we cannot use this mechanism to define the biconditional
     itself, since it hasn't been introduced yet.  Instead, we use a more
     general form of definition, described as follows.

     In its most general form, a definition is simply an assertion that
     introduces a new symbol (or a new combination of existing symbols, as in
     ~ df-3an ) that is eliminable and does not strengthen the existing
     language.  The latter requirement means that the set of provable
     statements not containing the new symbol (or new combination) should
     remain exactly the same after the definition is introduced.  Our
     definition of the biconditional may look unusual compared to most
     definitions, but it strictly satisfies these requirements.

     The justification for our definition is that if we mechanically replace
     ` ( ph <-> ps ) ` (the definiendum i.e. the thing being defined) with
     ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` (the definiens i.e. the
     defining expression) in the definition, the definition becomes the
     previously proved theorem ~ bijust .  It is impossible to use ~ df-bi to
     prove any statement expressed in the original language that can't be
     proved from the original axioms, because if we simply replace each
     instance of ~ df-bi in the proof with the corresponding ~ bijust instance,
     we will end up with a proof from the original axioms.

     Note that from Metamath's point of view, a definition is just another
     axiom - i.e. an assertion we claim to be true - but from our high level
     point of view, we are not strengthening the language.  To indicate this
     fact, we prefix definition labels with "df-" instead of "ax-".  (This
     prefixing is an informal convention that means nothing to the Metamath
     proof verifier; it is just a naming convention for human readability.)

     After we define the constant true ` T. ` ( ~ df-tru ) and the constant
     false ` F. ` ( ~ df-fal ), we will be able to prove these truth table
     values: ` ( ( T. <-> T. ) <-> T. ) ` ( ~ trubitru ),
     ` ( ( T. <-> F. ) <-> F. ) ` ( ~ trubifal ), ` ( ( F. <-> T. ) <-> F. ) `
     ( ~ falbitru ), and ` ( ( F. <-> F. ) <-> T. ) ` ( ~ falbifal ).

     See ~ dfbi1 , ~ dfbi2 , and ~ dfbi3 for theorems suggesting typical
     textbook definitions of ` <-> ` , showing that our definition has the
     properties we expect.  Theorem ~ dfbi1 is particularly useful if we want
     to eliminate ` <-> ` from an expression to convert it to primitives.
     Theorem ~ dfbi shows this definition rewritten in an abbreviated form
     after conjunction is introduced, for easier understanding.

     Contrast with ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), ` -/\ ` ( ~ df-nan ),
     and ` \/_ ` ( ~ df-xor ).  In some sense ` <-> ` returns true if two truth
     values are equal; ` = ` ( ~ df-cleq ) returns true if two classes are
     equal.  (Contributed by NM, 27-Dec-1992.) $)
  df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
        -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.

  $( $j justification 'bijust' for 'df-bi'; $)

  $( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.) $)
  impbi $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $=
    wph wps wi wps wph wi wph wps wb wph wps wb wph wps wi wps wph wi wn wi wn
    wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wi wps wph
    wi wn wi wn wph wps wb wi wph wps df-bi wph wps wb wph wps wi wps wph wi wn
    wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi simprim ax-mp expi $.

  ${
    impbii.1 $e |- ( ph -> ps ) $.
    impbii.2 $e |- ( ps -> ph ) $.
    $( Infer an equivalence from an implication and its converse.  Inference
       associated with ~ impbi .  (Contributed by NM, 29-Dec-1992.) $)
    impbii $p |- ( ph <-> ps ) $=
      wph wps wi wps wph wi wph wps wb impbii.1 impbii.2 wph wps impbi mp2 $.
  $}

  ${
    impbidd.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    impbidd.2 $e |- ( ph -> ( ps -> ( th -> ch ) ) ) $.
    $( Deduce an equivalence from two implications.  Double deduction
       associated with ~ impbi and ~ impbii .  Deduction associated with
       ~ impbid .  (Contributed by Rodolfo Medina, 12-Oct-2010.) $)
    impbidd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      wph wps wch wth wi wth wch wi wch wth wb impbidd.1 impbidd.2 wch wth
      impbi syl6c $.
  $}

  ${
    impbid21d.1 $e |- ( ps -> ( ch -> th ) ) $.
    impbid21d.2 $e |- ( ph -> ( th -> ch ) ) $.
    $( Deduce an equivalence from two implications.  (Contributed by Wolf
       Lammen, 12-May-2013.) $)
    impbid21d $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      wps wch wth wi wph wth wch wi wch wth wb impbid21d.1 impbid21d.2 wch wth
      impbi syl2imc $.
  $}

  ${
    impbid.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Deduce an equivalence from two implications.  Deduction associated with
       ~ impbi and ~ impbii .  (Contributed by NM, 24-Jan-1993.)  Revised to
       prove it from ~ impbid21d .  (Revised by Wolf Lammen, 3-Nov-2012.) $)
    impbid $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch wb wph wph wps wch impbid.1 impbid.2 impbid21d pm2.43i $.
  $}

  $( Relate the biconditional connective to primitive connectives.  See
     ~ dfbi1ALT for an unusual version proved directly from axioms.
     (Contributed by NM, 29-Dec-1992.) $)
  dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb wph wps wi wps wph
    wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wph wps
    df-bi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn
    wi wn wph wps wb wi wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb
    wph wps wi wps wph wi wn wi wn impbi con3rr3 mt3 $.

  $( Alternate proof of ~ dfbi1 .  This proof, discovered by Gregory Bush on
     8-Mar-2004, has several curious properties.  First, it has only 17 steps
     directly from the axioms and ~ df-bi , compared to over 800 steps were the
     proof of ~ dfbi1 expanded into axioms.  Second, step 2 demands only the
     property of "true"; any axiom (or theorem) could be used.  It might be
     thought, therefore, that it is in some sense redundant, but in fact no
     proof is shorter than this (measured by number of steps).  Third, it
     illustrates how intermediate steps can "blow up" in size even in short
     proofs.  Fourth, the compressed proof is only 182 bytes (or 17 bytes in
     D-proof notation), but the generated web page is over 200kB with
     intermediate steps that are essentially incomprehensible to humans (other
     than Gregory Bush).  If there were an obfuscated code contest for proofs,
     this would be a contender.  This "blowing up" and incomprehensibility of
     the intermediate steps vividly demonstrate the advantages of using many
     layered intermediate theorems, since each theorem is easier to understand.
     (Contributed by Gregory Bush, 10-Mar-2004.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  dfbi1ALT $p |-
                ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn
    wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps
    df-bi wch wth wch wi wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph
    wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps
    wph wi wn wi wn wb wi wch wth ax-1 wph wps wb wph wps wi wps wph wi wn wi
    wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph
    wps wi wps wph wi wn wi wn wb wi wn wch wth wch wi wi wn wi wch wth wch wi
    wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi
    wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi
    wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi
    wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi
    wn wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb wph wps wi wps
    wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wi
    wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn
    wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn
    wi wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn
    wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb
    wi wn wch wth wch wi wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wi
    wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi
    wps wph wi wn wi wn wb wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb
    wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn
    wph wps wb wi wn wi wn wi ax-1 wph wps wb wph wps wi wps wph wi wn wi wn wi
    wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi
    wps wph wi wn wi wn wb wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb
    wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn
    wph wps wb wi wn wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph
    wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps
    wph wi wn wi wn wb wi wn wi wch wth wch wi wi wn wi wi wph wps wb wph wps
    wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn
    wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn wph wps wb wph wps
    wi wps wph wi wn wi wn wb wph wps wb wph wps wi wps wph wi wn wi wn wi wph
    wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wi wph wps wb wph wps wi
    wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi
    wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn wi wi wph wps wb wph
    wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi
    wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn wch wth wch wi
    wi wn wi wi wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb wph wps
    wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn
    wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi
    wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn
    wb wi wn wi wch wth wch wi wi wn wi wph wps wb wph wps wi wps wph wi wn wi
    wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph
    wps wi wps wph wi wn wi wn wb wi wn wph wps wb wph wps wi wps wph wi wn wi
    wn wb wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn
    wi wn wph wps wb wi wn wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn
    wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps
    wi wps wph wi wn wi wn wb wi wn wi wch wth wch wi wi wn wi wi wch wth wch
    wi wi wn wn wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb wph wps
    wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn
    wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi
    wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn
    wb wi wn wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb
    wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb
    wi wn wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps
    wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn
    wi wn wb wi wn wi wch wth wch wi wi wn wi wph wps wb wph wps wi wps wph wi
    wn wi wn wb wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph
    wi wn wi wn wph wps wb wi wn wi wn wi wph wps wb wph wps wi wps wph wi wn
    wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb
    wph wps wi wps wph wi wn wi wn wb wi wn wi wn wch wth wch wi wi wn wn wph
    wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb wph wps wi wps wph wi
    wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wi wph
    wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph
    wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn wi wn
    wi wph wps wb wph wps wi wps wph wi wn wi wn df-bi wph wps wb wph wps wi
    wps wph wi wn wi wn wb wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps
    wi wps wph wi wn wi wn wph wps wb wi wn wi wn wi wph wps wb wph wps wi wps
    wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn
    wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn wi wn wch wth wch wi wi
    wn wn ax-1 ax-mp wch wth wch wi wi wn wph wps wb wph wps wi wps wph wi wn
    wi wn wb wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi
    wn wi wn wph wps wb wi wn wi wn wi wph wps wb wph wps wi wps wph wi wn wi
    wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph
    wps wi wps wph wi wn wi wn wb wi wn wi ax-3 ax-mp wph wps wb wph wps wi wps
    wph wi wn wi wn wb wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi
    wps wph wi wn wi wn wph wps wb wi wn wi wn wi wph wps wb wph wps wi wps wph
    wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn wph
    wps wb wph wps wi wps wph wi wn wi wn wb wi wn wi wch wth wch wi wi wn wi
    wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn
    wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wi wn
    ax-1 ax-mp wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph
    wi wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi
    wn wb wi wn wph wps wb wph wps wi wps wph wi wn wi wn wb wph wps wb wph wps
    wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn
    wi wn wi wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi
    wn wi wn wph wps wb wi wn wi wn wph wps wb wph wps wi wps wph wi wn wi wn
    wb wi wn wi wch wth wch wi wi wn ax-2 ax-mp ax-mp wph wps wb wph wps wi wps
    wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi wn
    wph wps wb wph wps wi wps wph wi wn wi wn wb wi wch wth wch wi wi ax-3
    ax-mp ax-mp ax-mp $.

  $( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.) $)
  biimp $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    wph wps wb wph wps wi wps wph wi wn wi wn wph wps wi wph wps wb wph wps wi
    wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb wi wn wi
    wn wph wps wb wph wps wi wps wph wi wn wi wn wi wph wps df-bi wph wps wb
    wph wps wi wps wph wi wn wi wn wi wph wps wi wps wph wi wn wi wn wph wps wb
    wi wn simplim ax-mp wph wps wi wps wph wi wn simplim syl $.

  ${
    biimpi.1 $e |- ( ph <-> ps ) $.
    $( Infer an implication from a logical equivalence.  Inference associated
       with ~ biimp .  (Contributed by NM, 29-Dec-1992.) $)
    biimpi $p |- ( ph -> ps ) $=
      wph wps wb wph wps wi biimpi.1 wph wps biimp ax-mp $.
  $}

  ${
    sylbi.1 $e |- ( ph <-> ps ) $.
    sylbi.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by NM, 3-Jan-1993.) $)
    sylbi $p |- ( ph -> ch ) $=
      wph wps wch wph wps sylbi.1 biimpi sylbi.2 syl $.
  $}

  ${
    sylib.1 $e |- ( ph -> ps ) $.
    sylib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       (Contributed by NM, 3-Jan-1993.) $)
    sylib $p |- ( ph -> ch ) $=
      wph wps wch sylib.1 wps wch sylib.2 biimpi syl $.
  $}

  ${
    sylbb.1 $e |- ( ph <-> ps ) $.
    sylbb.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from two biconditionals.  (Contributed by
       BJ, 30-Mar-2019.) $)
    sylbb $p |- ( ph -> ch ) $=
      wph wps wch sylbb.1 wps wch sylbb.2 biimpi sylbi $.
  $}

  $( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.)  (Proof shortened by Wolf Lammen, 11-Nov-2012.) $)
  biimpr $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $=
    wph wps wb wph wps wi wps wph wi wn wi wn wps wph wi wph wps dfbi1 wph wps
    wi wps wph wi simprim sylbi $.

  $( Commutative law for the biconditional.  (Contributed by Wolf Lammen,
     10-Nov-2012.) $)
  bicom1 $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
    wph wps wb wps wph wph wps biimpr wph wps biimp impbid $.

  $( Commutative law for the biconditional.  Theorem *4.21 of
     [WhiteheadRussell] p. 117.  (Contributed by NM, 11-May-1993.) $)
  bicom $p |- ( ( ph <-> ps ) <-> ( ps <-> ph ) ) $=
    wph wps wb wps wph wb wph wps bicom1 wps wph bicom1 impbii $.

  ${
    bicomd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Commute two sides of a biconditional in a deduction.  (Contributed by
       NM, 14-May-1993.) $)
    bicomd $p |- ( ph -> ( ch <-> ps ) ) $=
      wph wps wch wb wch wps wb bicomd.1 wps wch bicom sylib $.
  $}

  ${
    bicomi.1 $e |- ( ph <-> ps ) $.
    $( Inference from commutative law for logical equivalence.  (Contributed by
       NM, 3-Jan-1993.) $)
    bicomi $p |- ( ps <-> ph ) $=
      wph wps wb wps wph wb bicomi.1 wph wps bicom1 ax-mp $.
  $}

  ${
    impbid1.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid1.2 $e |- ( ch -> ps ) $.
    $( Infer an equivalence from two implications.  (Contributed by NM,
       6-Mar-2007.) $)
    impbid1 $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch impbid1.1 wch wps wi wph impbid1.2 a1i impbid $.
  $}

  ${
    impbid2.1 $e |- ( ps -> ch ) $.
    impbid2.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Infer an equivalence from two implications.  (Contributed by NM,
       6-Mar-2007.)  (Proof shortened by Wolf Lammen, 27-Sep-2013.) $)
    impbid2 $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wch wps wph wch wps impbid2.2 impbid2.1 impbid1 bicomd $.
  $}

  ${
    impcon4bid.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impcon4bid.2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( A variation on ~ impbid with contraposition.  (Contributed by Jeff
       Hankins, 3-Jul-2009.) $)
    impcon4bid $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch impcon4bid.1 wph wps wch impcon4bid.2 con4d impbid $.
  $}

  ${
    biimpri.1 $e |- ( ph <-> ps ) $.
    $( Infer a converse implication from a logical equivalence.  Inference
       associated with ~ biimpr .  (Contributed by NM, 29-Dec-1992.)  (Proof
       shortened by Wolf Lammen, 16-Sep-2013.) $)
    biimpri $p |- ( ps -> ph ) $=
      wps wph wph wps biimpri.1 bicomi biimpi $.
  $}

  ${
    biimpd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce an implication from a logical equivalence.  Deduction associated
       with ~ biimp and ~ biimpi .  (Contributed by NM, 11-Jan-1993.) $)
    biimpd $p |- ( ph -> ( ps -> ch ) ) $=
      wph wps wch wb wps wch wi biimpd.1 wps wch biimp syl $.
  $}

  ${
    mpbi.min $e |- ph $.
    mpbi.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens.
       (Contributed by NM, 11-May-1993.) $)
    mpbi $p |- ps $=
      wph wps mpbi.min wph wps mpbi.maj biimpi ax-mp $.
  $}

  ${
    mpbir.min $e |- ps $.
    mpbir.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens.
       (Contributed by NM, 28-Dec-1992.) $)
    mpbir $p |- ph $=
      wps wph mpbir.min wph wps mpbir.maj biimpri ax-mp $.
  $}

  ${
    mpbid.min $e |- ( ph -> ps ) $.
    mpbid.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 21-Jun-1993.) $)
    mpbid $p |- ( ph -> ch ) $=
      wph wps wch mpbid.min wph wps wch mpbid.maj biimpd mpd $.
  $}

  ${
    mpbii.min $e |- ps $.
    mpbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a nested biconditional, related to modus ponens.
       (Contributed by NM, 16-May-1993.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
    mpbii $p |- ( ph -> ch ) $=
      wph wps wch wps wph mpbii.min a1i mpbii.maj mpbid $.
  $}

  ${
    sylibr.1 $e |- ( ph -> ps ) $.
    sylibr.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition.  (Contributed by
       NM, 3-Jan-1993.) $)
    sylibr $p |- ( ph -> ch ) $=
      wph wps wch sylibr.1 wch wps sylibr.2 biimpri syl $.
  $}

  ${
    sylbir.1 $e |- ( ps <-> ph ) $.
    sylbir.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       (Contributed by NM, 3-Jan-1993.) $)
    sylbir $p |- ( ph -> ch ) $=
      wph wps wch wps wph sylbir.1 biimpri sylbir.2 syl $.
  $}

  ${
    sylbbr.1 $e |- ( ph <-> ps ) $.
    sylbbr.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from two biconditionals.

       Note on the various syllogism-like statements in set.mm.  The
       hypothetical syllogism ~ syl infers an implication from two implications
       (and there are ~ 3syl and ~ 4syl for chaining more inferences).  There
       are four inferences inferring an implication from one implication and
       one biconditional: ~ sylbi , ~ sylib , ~ sylbir , ~ sylibr ; four
       inferences inferring an implication from two biconditionals: ~ sylbb ,
       ~ sylbbr , ~ sylbb1 , ~ sylbb2 ; four inferences inferring a
       biconditional from two biconditionals: ~ bitri , ~ bitr2i , ~ bitr3i ,
       ~ bitr4i (and more for chaining more biconditionals).  There are also
       closed forms and deduction versions of these, like, among many others,
       ~ syld , ~ syl5 , ~ syl6 , ~ mpbid , ~ bitrd , ~ bitrid , ~ bitrdi and
       variants.  (Contributed by BJ, 21-Apr-2019.) $)
    sylbbr $p |- ( ch -> ph ) $=
      wch wps wph wps wch sylbbr.2 biimpri sylbbr.1 sylibr $.
  $}
  
  ${
    sylbb1.1 $e |- ( ph <-> ps ) $.
    sylbb1.2 $e |- ( ph <-> ch ) $.
    $( A mixed syllogism inference from two biconditionals.  (Contributed by
       BJ, 21-Apr-2019.) $)
    sylbb1 $p |- ( ps -> ch ) $=
      wps wph wch wph wps sylbb1.1 biimpri sylbb1.2 sylib $.
  $}

  ${
    sylbb2.1 $e |- ( ph <-> ps ) $.
    sylbb2.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from two biconditionals.  (Contributed by
       BJ, 21-Apr-2019.) $)
    sylbb2 $p |- ( ph -> ch ) $=
      wph wps wch sylbb2.1 wch wps sylbb2.2 biimpri sylbi $.
  $}

  ${
    sylibd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylibd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
    sylibd $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth sylibd.1 wph wch wth sylibd.2 biimpd syld $.
  $}

  ${
    sylbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylbid.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
    sylbid $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wph wps wch sylbid.1 biimpd sylbid.2 syld $.
  $}

  ${
    mpbidi.min $e |- ( th -> ( ph -> ps ) ) $.
    mpbidi.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 9-Aug-1994.) $)
    mpbidi $p |- ( th -> ( ph -> ch ) ) $=
      wth wph wps wch mpbidi.min wph wps wch mpbidi.maj biimpd sylcom $.
  $}

  ${
    biimtrid.1 $e |- ( ph <-> ps ) $.
    biimtrid.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded antecedent with a
       definition.  (Contributed by NM, 12-Jan-1993.) $)
    biimtrid $p |- ( ch -> ( ph -> th ) ) $=
      wph wps wch wth wph wps biimtrid.1 biimpi biimtrid.2 syl5 $.
  $}

  ${
    syl5bi.1 $e |- ( ph <-> ps ) $.
    syl5bi.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded antecedent with a
       definition.  This is in the process of being renamed to ~ biimtrid so
       use that name instead.  (Contributed by NM, 12-Jan-1993.) $)
    syl5bi $p |- ( ch -> ( ph -> th ) ) $=
      wph wps wch wth wph wps syl5bi.1 biimpi syl5bi.2 syl5 $.
  $}

  ${
    syl5bir.1 $e |- ( ps <-> ph ) $.
    syl5bir.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 21-Jun-1993.) $)
    syl5bir $p |- ( ch -> ( ph -> th ) ) $=
      wph wps wch wth wps wph syl5bir.1 biimpri syl5bir.2 syl5 $.
  $}

  ${
    syl5ib.1 $e |- ( ph -> ps ) $.
    syl5ib.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 12-Jan-1993.) $)
    syl5ib $p |- ( ch -> ( ph -> th ) ) $=
      wph wps wch wth syl5ib.1 wch wps wth syl5ib.2 biimpd syl5 $.

    $( A mixed syllogism inference.  (Contributed by NM, 19-Jun-2007.) $)
    syl5ibcom $p |- ( ph -> ( ch -> th ) ) $=
      wch wph wth wph wps wch wth syl5ib.1 syl5ib.2 syl5ib com12 $.
  $}

  ${
    syl5ibr.1 $e |- ( ph -> th ) $.
    syl5ibr.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 3-Apr-1994.) $)
    syl5ibr $p |- ( ch -> ( ph -> ps ) ) $=
      wph wth wch wps syl5ibr.1 wch wps wth syl5ibr.2 bicomd syl5ib $.

    $( A mixed syllogism inference.  (Contributed by NM, 20-Jun-2007.) $)
    syl5ibrcom $p |- ( ph -> ( ch -> ps ) ) $=
      wch wph wps wph wps wch wth syl5ibr.1 syl5ibr.2 syl5ibr com12 $.
  $}

  ${
    biimprd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce a converse implication from a logical equivalence.  Deduction
       associated with ~ biimpr and ~ biimpri .  (Contributed by NM,
       11-Jan-1993.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
    biimprd $p |- ( ph -> ( ch -> ps ) ) $=
      wch wps wph wch wch id biimprd.1 syl5ibr $.
  $}

  ${
    biimpcd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce a commuted implication from a logical equivalence.  (Contributed
       by NM, 3-May-1994.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
    biimpcd $p |- ( ps -> ( ph -> ch ) ) $=
      wps wps wph wch wps id biimpcd.1 syl5ibcom $.

    $( Deduce a converse commuted implication from a logical equivalence.
       (Contributed by NM, 3-May-1994.)  (Proof shortened by Wolf Lammen,
       20-Dec-2013.) $)
    biimprcd $p |- ( ch -> ( ph -> ps ) ) $=
      wch wps wph wch wch id biimpcd.1 syl5ibrcom $.
  $}

  ${
    syl6ib.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ib.2 $e |- ( ch <-> th ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 21-Jun-1993.) $)
    syl6ib $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth syl6ib.1 wch wth syl6ib.2 biimpi syl6 $.
  $}

  ${
    syl6ibr.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ibr.2 $e |- ( th <-> ch ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded consequent with a
       definition.  (Contributed by NM, 10-Jan-1993.) $)
    syl6ibr $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth syl6ibr.1 wth wch syl6ibr.2 biimpri syl6 $.
  $}

  ${
    syl6bi.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bi.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 2-Jan-1994.) $)
    syl6bi $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wph wps wch syl6bi.1 biimpd syl6bi.2 syl6 $.
  $}

  ${
    syl6bir.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    syl6bir.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 18-May-1994.) $)
    syl6bir $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wph wch wps syl6bir.1 biimprd syl6bir.2 syl6 $.
  $}

  ${
    syl7bi.1 $e |- ( ph <-> ps ) $.
    syl7bi.2 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
    $( A mixed syllogism inference from a doubly nested implication and a
       biconditional.  (Contributed by NM, 14-May-1993.) $)
    syl7bi $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $=
      wph wps wch wth wta wph wps syl7bi.1 biimpi syl7bi.2 syl7 $.
  $}

  ${
    syl8ib.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8ib.2 $e |- ( th <-> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM,
       1-Aug-1994.) $)
    syl8ib $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      wph wps wch wth wta syl8ib.1 wth wta syl8ib.2 biimpi syl8 $.
  $}

  ${
    mpbird.min $e |- ( ph -> ch ) $.
    mpbird.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 5-Aug-1993.) $)
    mpbird $p |- ( ph -> ps ) $=
      wph wch wps mpbird.min wph wps wch mpbird.maj biimprd mpd $.
  $}

  ${
    mpbiri.min $e |- ch $.
    mpbiri.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a nested biconditional, related to modus ponens.
       (Contributed by NM, 21-Jun-1993.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
    mpbiri $p |- ( ph -> ps ) $=
      wph wps wch wch wph mpbiri.min a1i mpbiri.maj mpbird $.
  $}

  ${
    sylibrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylibrd.2 $e |- ( ph -> ( th <-> ch ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
    sylibrd $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth sylibrd.1 wph wth wch sylibrd.2 biimprd syld $.
  $}

  ${
    sylbird.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    sylbird.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
    sylbird $p |- ( ph -> ( ps -> th ) ) $=
      wph wps wch wth wph wch wps sylbird.1 biimprd sylbird.2 syld $.
  $}

  $( Principle of identity for logical equivalence.  Theorem *4.2 of
     [WhiteheadRussell] p. 117.  This is part of Frege's eighth axiom per
     Proposition 54 of [Frege1879] p. 50; see also ~ eqid .  (Contributed by
     NM, 2-Jun-1993.) $)
  biid $p |- ( ph <-> ph ) $=
    wph wph wph id wph id impbii $.

  $( Principle of identity with antecedent.  (Contributed by NM,
     25-Nov-1995.) $)
  biidd $p |- ( ph -> ( ps <-> ps ) ) $=
    wps wps wb wph wps biid a1i $.

  $( Two propositions are equivalent if they are both true.  Closed form of
     ~ 2th .  Equivalent to a ~ biimp -like version of the xor-connective.
     This theorem stays true, no matter how you permute its operands.  This is
     evident from its sharper version ` ( ph <-> ( ps <-> ( ph <-> ps ) ) ) ` .
     (Contributed by Wolf Lammen, 12-May-2013.) $)
  pm5.1im $p |- ( ph -> ( ps -> ( ph <-> ps ) ) ) $=
    wph wps wph wps wps wph ax-1 wph wps ax-1 impbid21d $.

  ${
    2th.1 $e |- ph $.
    2th.2 $e |- ps $.
    $( Two truths are equivalent.  (Contributed by NM, 18-Aug-1993.) $)
    2th $p |- ( ph <-> ps ) $=
      wph wps wps wph 2th.2 a1i wph wps 2th.1 a1i impbii $.
  $}

  ${
    2thd.1 $e |- ( ph -> ps ) $.
    2thd.2 $e |- ( ph -> ch ) $.
    $( Two truths are equivalent.  Deduction form.  (Contributed by NM,
       3-Jun-2012.) $)
    2thd $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch wps wch wb 2thd.1 2thd.2 wps wch pm5.1im sylc $.
  $}

  $( Two self-implications (see ~ id ) are equivalent.  This theorem, rather
     trivial in our axiomatization, is (the biconditional form of) a standard
     axiom for monothetic BCI logic.  This is the most general theorem of which
     ~ trujust is an instance.  Relatedly, this would be the justification
     theorem if the definition of ` T. ` were ~ dftru2 .  (Contributed by BJ,
     7-Sep-2022.) $)
  monothetic $p |- ( ( ph -> ph ) <-> ( ps -> ps ) ) $=
    wph wph wi wps wps wi wph id wps id 2th $.

  ${
    ibi.1 $e |- ( ph -> ( ph <-> ps ) ) $.
    $( Inference that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 17-Oct-2003.) $)
    ibi $p |- ( ph -> ps ) $=
      wph wph wps wph id ibi.1 mpbid $.
  $}

  ${
    ibir.1 $e |- ( ph -> ( ps <-> ph ) ) $.
    $( Inference that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 22-Jul-2004.) $)
    ibir $p |- ( ph -> ps ) $=
      wph wps wph wps wph ibir.1 bicomd ibi $.
  $}

  ${
    ibd.1 $e |- ( ph -> ( ps -> ( ps <-> ch ) ) ) $.
    $( Deduction that converts a biconditional implied by one of its arguments,
       into an implication.  Deduction associated with ~ ibi .  (Contributed by
       NM, 26-Jun-2004.) $)
    ibd $p |- ( ph -> ( ps -> ch ) ) $=
      wps wph wps wch wb wch ibd.1 wps wch biimp syli $.
  $}

  $( Distribution of implication over biconditional.  Theorem *5.74 of
     [WhiteheadRussell] p. 126.  (Contributed by NM, 1-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 11-Apr-2013.) $)
  pm5.74 $p |- ( ( ph -> ( ps <-> ch ) ) <->
               ( ( ph -> ps ) <-> ( ph -> ch ) ) ) $=
    wph wps wch wb wi wph wps wi wph wch wi wb wph wps wch wb wi wph wps wi wph
    wch wi wps wch wb wps wch wph wps wch biimp imim3i wps wch wb wch wps wph
    wps wch biimpr imim3i impbid wph wps wi wph wch wi wb wph wps wch wph wps
    wi wph wch wi wb wph wps wch wph wps wi wph wch wi biimp pm2.86d wph wps wi
    wph wch wi wb wph wch wps wph wps wi wph wch wi biimpr pm2.86d impbidd
    impbii $.

  ${
    pm5.74i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Distribution of implication over biconditional (inference form).
       (Contributed by NM, 1-Aug-1994.) $)
    pm5.74i $p |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $=
      wph wps wch wb wi wph wps wi wph wch wi wb pm5.74i.1 wph wps wch pm5.74
      mpbi $.
  $}

  ${
    pm5.74ri.1 $e |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $.
    $( Distribution of implication over biconditional (reverse inference form).
       (Contributed by NM, 1-Aug-1994.) $)
    pm5.74ri $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch wb wi wph wps wi wph wch wi wb pm5.74ri.1 wph wps wch pm5.74
      mpbir $.
  $}

  ${
    pm5.74d.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction form).
       (Contributed by NM, 21-Mar-1996.) $)
    pm5.74d $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $=
      wph wps wch wth wb wi wps wch wi wps wth wi wb pm5.74d.1 wps wch wth
      pm5.74 sylib $.
  $}

  ${
    pm5.74rd.1 $e |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction form).
       (Contributed by NM, 19-Mar-1997.) $)
    pm5.74rd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      wph wps wch wi wps wth wi wb wps wch wth wb wi pm5.74rd.1 wps wch wth
      pm5.74 sylibr $.
  $}

  ${
    bitri.1 $e |- ( ph <-> ps ) $.
    bitri.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 3-Jan-1993.)  (Proof shortened by Wolf Lammen, 13-Oct-2012.) $)
    bitri $p |- ( ph <-> ch ) $=
      wph wch wph wps wch bitri.1 bitri.2 sylbb wph wps wch bitri.1 bitri.2
      sylbbr impbii $.
  $}

  ${
    bitr2i.1 $e |- ( ph <-> ps ) $.
    bitr2i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 12-Mar-1993.) $)
    bitr2i $p |- ( ch <-> ph ) $=
      wph wch wph wps wch bitr2i.1 bitr2i.2 bitri bicomi $.
  $}

  ${
    bitr3i.1 $e |- ( ps <-> ph ) $.
    bitr3i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 2-Jun-1993.) $)
    bitr3i $p |- ( ph <-> ch ) $=
      wph wps wch wps wph bitr3i.1 bicomi bitr3i.2 bitri $.
  $}

  ${
    bitr4i.1 $e |- ( ph <-> ps ) $.
    bitr4i.2 $e |- ( ch <-> ps ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 3-Jan-1993.) $)
    bitr4i $p |- ( ph <-> ch ) $=
      wph wps wch bitr4i.1 wch wps bitr4i.2 bicomi bitri $.
  $}

  $( Register '<->' as an equality for its type (wff). $)
  $( $j
    equality 'wb' from 'biid' 'bicomi' 'bitri';
    definition 'dfbi1' for 'wb';
  $)

  ${
    bitrd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitrd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( Deduction form of ~ bitri .  (Contributed by NM, 12-Mar-1993.)  (Proof
       shortened by Wolf Lammen, 14-Apr-2013.) $)
    bitrd $p |- ( ph -> ( ps <-> th ) ) $=
      wph wps wth wph wps wi wph wch wi wph wth wi wph wps wch bitrd.1 pm5.74i
      wph wch wth bitrd.2 pm5.74i bitri pm5.74ri $.
  $}

  ${
    bitr2d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr2d.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( Deduction form of ~ bitr2i .  (Contributed by NM, 9-Jun-2004.) $)
    bitr2d $p |- ( ph -> ( th <-> ps ) ) $=
      wph wps wth wph wps wch wth bitr2d.1 bitr2d.2 bitrd bicomd $.
  $}

  ${
    bitr3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    $( Deduction form of ~ bitr3i .  (Contributed by NM, 14-May-1993.) $)
    bitr3d $p |- ( ph -> ( ch <-> th ) ) $=
      wph wch wps wth wph wps wch bitr3d.1 bicomd bitr3d.2 bitrd $.
  $}

  ${
    bitr4d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr4d.2 $e |- ( ph -> ( th <-> ch ) ) $.
    $( Deduction form of ~ bitr4i .  (Contributed by NM, 30-Jun-1993.) $)
    bitr4d $p |- ( ph -> ( ps <-> th ) ) $=
      wph wps wch wth bitr4d.1 wph wth wch bitr4d.2 bicomd bitrd $.
  $}

  ${
    bitrid.1 $e |- ( ph <-> ps ) $.
    bitrid.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       12-Mar-1993.) $)
    bitrid $p |- ( ch -> ( ph <-> th ) ) $=
      wch wph wps wth wph wps wb wch bitrid.1 a1i bitrid.2 bitrd $.
  $}

  ${
    bitr2id.1 $e |- ( ph <-> ps ) $.
    bitr2id.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       1-Aug-1993.) $)
    bitr2id $p |- ( ch -> ( th <-> ph ) ) $=
      wch wph wth wph wps wch wth bitr2id.1 bitr2id.2 bitrid bicomd $.
  $}

  ${
    bitr3id.1 $e |- ( ps <-> ph ) $.
    bitr3id.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    bitr3id $p |- ( ch -> ( ph <-> th ) ) $=
      wph wps wch wth wps wph bitr3id.1 bicomi bitr3id.2 bitrid $.
  $}

  ${
    bitr3di.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr3di.2 $e |- ( ps <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)
    bitr3di $p |- ( ph -> ( ch <-> th ) ) $=
      wth wps wph wch wps wth bitr3di.2 bicomi bitr3di.1 bitr2id $.
  $}

  ${
    bitrdi.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitrdi.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       12-Mar-1993.) $)
    bitrdi $p |- ( ph -> ( ps <-> th ) ) $=
      wph wps wch wth bitrdi.1 wch wth wb wph bitrdi.2 a1i bitrd $.
  $}

  ${
    bitr2di.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr2di.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    bitr2di $p |- ( ph -> ( th <-> ps ) ) $=
      wph wps wth wph wps wch wth bitr2di.1 bitr2di.2 bitrdi bicomd $.
  $}

  ${
    bitr4di.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr4di.2 $e |- ( th <-> ch ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       12-Mar-1993.) $)
    bitr4di $p |- ( ph -> ( ps <-> th ) ) $=
      wph wps wch wth bitr4di.1 wth wch bitr4di.2 bicomi bitrdi $.
  $}

  ${
    bitr4id.2 $e |- ( ps <-> ch ) $.
    bitr4id.1 $e |- ( ph -> ( th <-> ch ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)
    bitr4id $p |- ( ph -> ( ps <-> th ) ) $=
      wph wth wch wps bitr4id.1 wps wch bitr4id.2 bicomi bitr2di $.
  $}

  ${
    3imtr3.1 $e |- ( ph -> ps ) $.
    3imtr3.2 $e |- ( ph <-> ch ) $.
    3imtr3.3 $e |- ( ps <-> th ) $.
    $( A mixed syllogism inference, useful for removing a definition from both
       sides of an implication.  (Contributed by NM, 10-Aug-1994.) $)
    3imtr3i $p |- ( ch -> th ) $=
      wch wps wth wch wph wps 3imtr3.2 3imtr3.1 sylbir 3imtr3.3 sylib $.
  $}

  ${
    3imtr4.1 $e |- ( ph -> ps ) $.
    3imtr4.2 $e |- ( ch <-> ph ) $.
    3imtr4.3 $e |- ( th <-> ps ) $.
    $( A mixed syllogism inference, useful for applying a definition to both
       sides of an implication.  (Contributed by NM, 3-Jan-1993.) $)
    3imtr4i $p |- ( ch -> th ) $=
      wch wps wth wch wph wps 3imtr4.2 3imtr4.1 sylbi 3imtr4.3 sylibr $.
  $}

  ${
    3imtr3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    3imtr3d.3 $e |- ( ph -> ( ch <-> ta ) ) $.
    $( More general version of ~ 3imtr3i .  Useful for converting conditional
       definitions in a formula.  (Contributed by NM, 8-Apr-1996.) $)
    3imtr3d $p |- ( ph -> ( th -> ta ) ) $=
      wph wth wps wta 3imtr3d.2 wph wps wch wta 3imtr3d.1 3imtr3d.3 sylibd
      sylbird $.
  $}

  ${
    3imtr4d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4d.2 $e |- ( ph -> ( th <-> ps ) ) $.
    3imtr4d.3 $e |- ( ph -> ( ta <-> ch ) ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting conditional
       definitions in a formula.  (Contributed by NM, 26-Oct-1995.) $)
    3imtr4d $p |- ( ph -> ( th -> ta ) ) $=
      wph wth wps wta 3imtr4d.2 wph wps wch wta 3imtr4d.1 3imtr4d.3 sylibrd
      sylbid $.
  $}

  ${
    3imtr3g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr3g.2 $e |- ( ps <-> th ) $.
    3imtr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3imtr3i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 20-May-1996.)  (Proof shortened by
       Wolf Lammen, 20-Dec-2013.) $)
    3imtr3g $p |- ( ph -> ( th -> ta ) ) $=
      wph wth wch wta wth wps wph wch 3imtr3g.2 3imtr3g.1 syl5bir 3imtr3g.3
      syl6ib $.
  $}

  ${
    3imtr4g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4g.2 $e |- ( th <-> ps ) $.
    3imtr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 20-May-1996.)  (Proof shortened by
       Wolf Lammen, 20-Dec-2013.) $)
    3imtr4g $p |- ( ph -> ( th -> ta ) ) $=
      wph wth wch wta wth wps wph wch 3imtr4g.2 3imtr4g.1 biimtrid 3imtr4g.3
      syl6ibr $.
  $}

  ${
    3bitri.1 $e |- ( ph <-> ps ) $.
    3bitri.2 $e |- ( ps <-> ch ) $.
    3bitri.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 3-Jan-1993.) $)
    3bitri $p |- ( ph <-> th ) $=
      wph wps wth 3bitri.1 wps wch wth 3bitri.2 3bitri.3 bitri bitri $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
    3bitrri $p |- ( th <-> ph ) $=
      wth wch wph 3bitri.3 wph wps wch 3bitri.1 3bitri.2 bitr2i bitr3i $.
  $}

  ${
    3bitr2i.1 $e |- ( ph <-> ps ) $.
    3bitr2i.2 $e |- ( ch <-> ps ) $.
    3bitr2i.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
    3bitr2i $p |- ( ph <-> th ) $=
      wph wch wth wph wps wch 3bitr2i.1 3bitr2i.2 bitr4i 3bitr2i.3 bitri $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
    3bitr2ri $p |- ( th <-> ph ) $=
      wph wch wth wph wps wch 3bitr2i.1 3bitr2i.2 bitr4i 3bitr2i.3 bitr2i $.
  $}

  ${
    3bitr3i.1 $e |- ( ph <-> ps ) $.
    3bitr3i.2 $e |- ( ph <-> ch ) $.
    3bitr3i.3 $e |- ( ps <-> th ) $.
    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 19-Aug-1993.) $)
    3bitr3i $p |- ( ch <-> th ) $=
      wch wps wth wch wph wps 3bitr3i.2 3bitr3i.1 bitr3i 3bitr3i.3 bitri $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 21-Jun-1993.) $)
    3bitr3ri $p |- ( th <-> ch ) $=
      wth wps wch 3bitr3i.3 wps wph wch 3bitr3i.1 3bitr3i.2 bitr3i bitr3i $.
  $}

  ${
    3bitr4i.1 $e |- ( ph <-> ps ) $.
    3bitr4i.2 $e |- ( ch <-> ph ) $.
    3bitr4i.3 $e |- ( th <-> ps ) $.
    $( A chained inference from transitive law for logical equivalence.  This
       inference is frequently used to apply a definition to both sides of a
       logical equivalence.  (Contributed by NM, 3-Jan-1993.) $)
    3bitr4i $p |- ( ch <-> th ) $=
      wch wph wth 3bitr4i.2 wph wps wth 3bitr4i.1 3bitr4i.3 bitr4i bitri $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 2-Sep-1995.) $)
    3bitr4ri $p |- ( th <-> ch ) $=
      wch wph wth 3bitr4i.2 wph wps wth 3bitr4i.1 3bitr4i.3 bitr4i bitr2i $.
  $}

  ${
    3bitrd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitrd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    3bitrd.3 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       13-Aug-1999.) $)
    3bitrd $p |- ( ph -> ( ps <-> ta ) ) $=
      wph wps wth wta wph wps wch wth 3bitrd.1 3bitrd.2 bitrd 3bitrd.3 bitrd $.

    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitrrd $p |- ( ph -> ( ta <-> ps ) ) $=
      wph wth wta wps 3bitrd.3 wph wps wch wth 3bitrd.1 3bitrd.2 bitr2d bitr3d
      $.
  $}

  ${
    3bitr2d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr2d.2 $e |- ( ph -> ( th <-> ch ) ) $.
    3bitr2d.3 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitr2d $p |- ( ph -> ( ps <-> ta ) ) $=
      wph wps wth wta wph wps wch wth 3bitr2d.1 3bitr2d.2 bitr4d 3bitr2d.3
      bitrd $.

    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitr2rd $p |- ( ph -> ( ta <-> ps ) ) $=
      wph wps wth wta wph wps wch wth 3bitr2d.1 3bitr2d.2 bitr4d 3bitr2d.3
      bitr2d $.
  $}

  ${
    3bitr3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    3bitr3d.3 $e |- ( ph -> ( ch <-> ta ) ) $.
    $( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula.  (Contributed by NM,
       24-Apr-1996.) $)
    3bitr3d $p |- ( ph -> ( th <-> ta ) ) $=
      wph wth wch wta wph wps wth wch 3bitr3d.2 3bitr3d.1 bitr3d 3bitr3d.3
      bitrd $.

    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitr3rd $p |- ( ph -> ( ta <-> th ) ) $=
      wph wch wta wth 3bitr3d.3 wph wps wch wth 3bitr3d.1 3bitr3d.2 bitr3d
      bitr3d $.
  $}

  ${
    3bitr4d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr4d.2 $e |- ( ph -> ( th <-> ps ) ) $.
    3bitr4d.3 $e |- ( ph -> ( ta <-> ch ) ) $.
    $( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula.  (Contributed by NM,
       18-Oct-1995.) $)
    3bitr4d $p |- ( ph -> ( th <-> ta ) ) $=
      wph wth wps wta 3bitr4d.2 wph wps wch wta 3bitr4d.1 3bitr4d.3 bitr4d
      bitrd $.

    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitr4rd $p |- ( ph -> ( ta <-> th ) ) $=
      wph wta wps wth wph wta wch wps 3bitr4d.3 3bitr4d.1 bitr4d 3bitr4d.2
      bitr4d $.
  $}

  ${
    3bitr3g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr3g.2 $e |- ( ps <-> th ) $.
    3bitr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3bitr3i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 4-Jun-1995.) $)
    3bitr3g $p |- ( ph -> ( th <-> ta ) ) $=
      wph wth wch wta wth wps wph wch 3bitr3g.2 3bitr3g.1 bitr3id 3bitr3g.3
      bitrdi $.
  $}

  ${
    3bitr4g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr4g.2 $e |- ( th <-> ps ) $.
    3bitr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3bitr4i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 11-May-1993.) $)
    3bitr4g $p |- ( ph -> ( th <-> ta ) ) $=
      wph wth wch wta wth wps wph wch 3bitr4g.2 3bitr4g.1 bitrid 3bitr4g.3
      bitr4di $.
  $}

  $( Double negation.  Theorem *4.13 of [WhiteheadRussell] p. 117.
     (Contributed by NM, 3-Jan-1993.) $)
  notnotb $p |- ( ph <-> -. -. ph ) $=
    wph wph wn wn wph notnot wph notnotr impbii $.

  $( A biconditional form of contraposition.  Theorem *4.1 of
     [WhiteheadRussell] p. 116.  (Contributed by NM, 11-May-1993.) $)
  con34b $p |- ( ( ph -> ps ) <-> ( -. ps -> -. ph ) ) $=
    wph wps wi wps wn wph wn wi wph wps con3 wps wph con4 impbii $.

  ${
    con4bid.1 $e |- ( ph -> ( -. ps <-> -. ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 21-May-1994.) $)
    con4bid $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch wph wch wps wph wps wn wch wn con4bid.1 biimprd con4d wph wps
      wn wch wn con4bid.1 biimpd impcon4bid $.
  $}

  ${
    notbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction negating both sides of a logical equivalence.  (Contributed by
       NM, 21-May-1994.) $)
    notbid $p |- ( ph -> ( -. ps <-> -. ch ) ) $=
      wph wps wn wch wn wph wps wch wps wn wn wch wn wn notbid.1 wps notnotb
      wch notnotb 3bitr3g con4bid $.
  $}

  $( Contraposition.  Theorem *4.11 of [WhiteheadRussell] p. 117.  (Contributed
     by NM, 21-May-1994.)  (Proof shortened by Wolf Lammen, 12-Jun-2013.) $)
  notbi $p |- ( ( ph <-> ps ) <-> ( -. ph <-> -. ps ) ) $=
    wph wps wb wph wn wps wn wb wph wps wb wph wps wph wps wb id notbid wph wn
    wps wn wb wph wps wph wn wps wn wb id con4bid impbii $.

  ${
    notbii.1 $e |- ( ph <-> ps ) $.
    $( Negate both sides of a logical equivalence.  (Contributed by NM,
       3-Jan-1993.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
    notbii $p |- ( -. ph <-> -. ps ) $=
      wph wps wb wph wn wps wn wb notbii.1 wph wps notbi mpbi $.

    $( Theorem notbii is the congruence law for negation. $)
    $( $j congruence 'notbii'; $)
  $}

  ${
    con4bii.1 $e |- ( -. ph <-> -. ps ) $.
    $( A contraposition inference.  (Contributed by NM, 21-May-1994.) $)
    con4bii $p |- ( ph <-> ps ) $=
      wph wps wb wph wn wps wn wb con4bii.1 wph wps notbi mpbir $.
  $}

  ${
    mtbi.1 $e |- -. ph $.
    mtbi.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens.
       (Contributed by NM, 15-Nov-1994.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
    mtbi $p |- -. ps $=
      wps wph mtbi.1 wph wps mtbi.2 biimpri mto $.
  $}

  ${
    mtbir.1 $e |- -. ps $.
    mtbir.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens.
       (Contributed by NM, 15-Nov-1994.)  (Proof shortened by Wolf Lammen,
       14-Oct-2012.) $)
    mtbir $p |- -. ph $=
      wps wph mtbir.1 wph wps mtbir.2 bicomi mtbi $.
  $}

  ${
    mtbid.min $e |- ( ph -> -. ps ) $.
    mtbid.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, similar to modus tollens.
       (Contributed by NM, 26-Nov-1995.) $)
    mtbid $p |- ( ph -> -. ch ) $=
      wph wch wps mtbid.min wph wps wch mtbid.maj biimprd mtod $.
  $}

  ${
    mtbird.min $e |- ( ph -> -. ch ) $.
    mtbird.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, similar to modus tollens.
       (Contributed by NM, 10-May-1994.) $)
    mtbird $p |- ( ph -> -. ps ) $=
      wph wps wch mtbird.min wph wps wch mtbird.maj biimpd mtod $.
  $}

  ${
    mtbii.min $e |- -. ps $.
    mtbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens.
       (Contributed by NM, 27-Nov-1995.) $)
    mtbii $p |- ( ph -> -. ch ) $=
      wph wch wps mtbii.min wph wps wch mtbii.maj biimprd mtoi $.
  $}

  ${
    mtbiri.min $e |- -. ch $.
    mtbiri.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens.
       (Contributed by NM, 24-Aug-1995.) $)
    mtbiri $p |- ( ph -> -. ps ) $=
      wph wps wch mtbiri.min wph wps wch mtbiri.maj biimpd mtoi $.
  $}

  ${
    sylnib.1 $e |- ( ph -> -. ps ) $.
    sylnib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
    sylnib $p |- ( ph -> -. ch ) $=
      wph wps wch sylnib.1 wps wch sylnib.2 biimpri nsyl $.
  $}

  ${
    sylnibr.1 $e |- ( ph -> -. ps ) $.
    sylnibr.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition.  (Contributed by
       Wolf Lammen, 16-Dec-2013.) $)
    sylnibr $p |- ( ph -> -. ch ) $=
      wph wps wch sylnibr.1 wch wps sylnibr.2 bicomi sylnib $.
  $}

  ${
    sylnbi.1 $e |- ( ph <-> ps ) $.
    sylnbi.2 $e |- ( -. ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by Wolf Lammen, 16-Dec-2013.) $)
    sylnbi $p |- ( -. ph -> ch ) $=
      wph wn wps wn wch wph wps sylnbi.1 notbii sylnbi.2 sylbi $.
  $}

  ${
    sylnbir.1 $e |- ( ps <-> ph ) $.
    sylnbir.2 $e |- ( -. ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
    sylnbir $p |- ( -. ph -> ch ) $=
      wph wps wch wps wph sylnbir.1 bicomi sylnbir.2 sylnbi $.
  $}

  ${
    xchnxbi.1 $e |- ( -. ph <-> ps ) $.
    xchnxbi.2 $e |- ( ph <-> ch ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchnxbi $p |- ( -. ch <-> ps ) $=
      wch wn wph wn wps wph wch xchnxbi.2 notbii xchnxbi.1 bitr3i $.
  $}

  ${
    xchnxbir.1 $e |- ( -. ph <-> ps ) $.
    xchnxbir.2 $e |- ( ch <-> ph ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchnxbir $p |- ( -. ch <-> ps ) $=
      wph wps wch xchnxbir.1 wch wph xchnxbir.2 bicomi xchnxbi $.
  $}

  ${
    xchbinx.1 $e |- ( ph <-> -. ps ) $.
    xchbinx.2 $e |- ( ps <-> ch ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchbinx $p |- ( ph <-> -. ch ) $=
      wph wps wn wch wn xchbinx.1 wps wch xchbinx.2 notbii bitri $.
  $}

  ${
    xchbinxr.1 $e |- ( ph <-> -. ps ) $.
    xchbinxr.2 $e |- ( ch <-> ps ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchbinxr $p |- ( ph <-> -. ch ) $=
      wph wps wch xchbinxr.1 wch wps xchbinxr.2 bicomi xchbinx $.
  $}

  ${
    imbi2i.1 $e |- ( ph <-> ps ) $.
    $( Introduce an antecedent to both sides of a logical equivalence.  This
       and the next three rules are useful for building up wff's around a
       definition, in order to make use of the definition.  (Contributed by NM,
       3-Jan-1993.)  (Proof shortened by Wolf Lammen, 6-Feb-2013.) $)
    imbi2i $p |- ( ( ch -> ph ) <-> ( ch -> ps ) ) $=
      wch wph wps wph wps wb wch imbi2i.1 a1i pm5.74i $.
  $}

  ${
    jcndOLD.1 $e |- ( ph -> ps ) $.
    jcndOLD.2 $e |- ( ph -> -. ch ) $.
    $( Obsolete version of ~ jcnd as of 10-Apr-2024.  (Contributed by Glauco
       Siliprandi, 11-Dec-2019.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    jcndOLD $p |- ( ph -> -. ( ps -> ch ) ) $=
      wph wps wch wn wn wi wps wch wi wph wps wch wn jcndOLD.1 jcndOLD.2 jc wch
      wch wn wn wps wch notnotb imbi2i sylnibr $.
  $}

  ${
    bibi2i.1 $e |- ( ph <-> ps ) $.
    $( Inference adding a biconditional to the left in an equivalence.
       (Contributed by NM, 26-May-1993.)  (Proof shortened by Andrew Salmon,
       7-May-2011.)  (Proof shortened by Wolf Lammen, 16-May-2013.) $)
    bibi2i $p |- ( ( ch <-> ph ) <-> ( ch <-> ps ) ) $=
      wch wph wb wch wps wb wch wph wb wch wph wps wch wph wb id bibi2i.1
      bitrdi wch wps wb wch wps wph wch wps wb id bibi2i.1 bitr4di impbii $.

    $( Inference adding a biconditional to the right in an equivalence.
       (Contributed by NM, 26-May-1993.) $)
    bibi1i $p |- ( ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      wph wch wb wch wph wb wch wps wb wps wch wb wph wch bicom wph wps wch
      bibi2i.1 bibi2i wch wps bicom 3bitri $.

    ${
      bibi12i.2 $e |- ( ch <-> th ) $.
      $( The equivalence of two equivalences.  (Contributed by NM,
         26-May-1993.) $)
      bibi12i $p |- ( ( ph <-> ch ) <-> ( ps <-> th ) ) $=
        wph wch wb wph wth wb wps wth wb wch wth wph bibi12i.2 bibi2i wph wps
        wth bibi2i.1 bibi1i bitri $.
    $}
  $}

  ${
    imbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding an antecedent to both sides of a logical equivalence.
       (Contributed by NM, 11-May-1993.) $)
    imbi2d $p |- ( ph -> ( ( th -> ps ) <-> ( th -> ch ) ) ) $=
      wph wth wps wch wph wps wch wb wth imbid.1 a1d pm5.74d $.

    $( Deduction adding a consequent to both sides of a logical equivalence.
       (Contributed by NM, 11-May-1993.)  (Proof shortened by Wolf Lammen,
       17-Sep-2013.) $)
    imbi1d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) ) $=
      wph wps wth wi wch wth wi wph wch wps wth wph wps wch imbid.1 biimprd
      imim1d wph wps wch wth wph wps wch imbid.1 biimpd imim1d impbid $.

    $( Deduction adding a biconditional to the left in an equivalence.
       (Contributed by NM, 11-May-1993.)  (Proof shortened by Wolf Lammen,
       19-May-2013.) $)
    bibi2d $p |- ( ph -> ( ( th <-> ps ) <-> ( th <-> ch ) ) ) $=
      wph wth wps wb wth wch wb wph wth wi wph wps wi wb wph wth wi wph wch wi
      wb wph wth wps wb wi wph wth wch wb wi wph wps wi wph wch wi wph wth wi
      wph wps wch imbid.1 pm5.74i bibi2i wph wth wps pm5.74 wph wth wch pm5.74
      3bitr4i pm5.74ri $.

    $( Deduction adding a biconditional to the right in an equivalence.
       (Contributed by NM, 11-May-1993.) $)
    bibi1d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> th ) ) ) $=
      wph wth wps wb wth wch wb wps wth wb wch wth wb wph wps wch wth imbid.1
      bibi2d wps wth bicom wch wth bicom 3bitr4g $.
  $}

  ${
    imbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    imbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of implications.
       (Contributed by NM, 16-May-1993.) $)
    imbi12d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) ) $=
      wph wps wth wi wch wth wi wch wta wi wph wps wch wth imbi12d.1 imbi1d wph
      wth wta wch imbi12d.2 imbi2d bitrd $.

    $( Deduction joining two equivalences to form equivalence of
       biconditionals.  (Contributed by NM, 26-May-1993.) $)
    bibi12d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> ta ) ) ) $=
      wph wps wth wb wch wth wb wch wta wb wph wps wch wth imbi12d.1 bibi1d wph
      wth wta wch imbi12d.2 bibi2d bitrd $.
  $}

  $( Closed form of ~ imbi12i .  Was automatically derived from its "Virtual
     Deduction" version and the Metamath program "MM-PA> MINIMIZE__WITH *"
     command.  (Contributed by Alan Sare, 18-Mar-2012.) $)
  imbi12 $p |- ( ( ph <-> ps ) ->
                    ( ( ch <-> th ) -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) ) $=
    wph wps wb wch wth wb wph wch wi wps wth wi wb wph wps wb wch wth wb wn wi
    wn wph wps wch wth wph wps wb wch wth wb wn simplim wph wps wb wch wth wb
    simprim imbi12d expi $.

  $( Theorem *4.84 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  imbi1 $p |- ( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) ) $=
    wph wps wb wph wps wch wph wps wb id imbi1d $.

  $( Theorem *4.85 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
  imbi2 $p |- ( ( ph <-> ps ) -> ( ( ch -> ph ) <-> ( ch -> ps ) ) ) $=
    wph wps wb wph wps wch wph wps wb id imbi2d $.

  ${
    imbi1i.1 $e |- ( ph <-> ps ) $.
    $( Introduce a consequent to both sides of a logical equivalence.
       (Contributed by NM, 3-Jan-1993.)  (Proof shortened by Wolf Lammen,
       17-Sep-2013.) $)
    imbi1i $p |- ( ( ph -> ch ) <-> ( ps -> ch ) ) $=
      wph wps wb wph wch wi wps wch wi wb imbi1i.1 wph wps wch imbi1 ax-mp $.
  $}

  ${
    imbi12i.1 $e |- ( ph <-> ps ) $.
    imbi12i.2 $e |- ( ch <-> th ) $.
    $( Join two logical equivalences to form equivalence of implications.
       (Contributed by NM, 1-Aug-1993.) $)
    imbi12i $p |- ( ( ph -> ch ) <-> ( ps -> th ) ) $=
      wph wps wb wch wth wb wph wch wi wps wth wi wb imbi12i.1 imbi12i.2 wph
      wps wch wth imbi12 mp2 $.

    $( Theorem imbi12i is the congruence law for implication. $)
    $( $j congruence 'imbi12i'; $)
  $}

  $( Theorem *4.86 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  bibi1 $p |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) <-> ( ps <-> ch ) ) ) $=
    wph wps wb wph wps wch wph wps wb id bibi1d $.

  $( Closed nested implication form of ~ bitr3i .  Derived automatically from
     ~ bitr3VD .  (Contributed by Alan Sare, 31-Dec-2011.) $)
  bitr3 $p |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) -> ( ps <-> ch ) ) ) $=
    wph wps wb wph wch wb wps wch wb wph wps wch bibi1 biimpd $.

  $( Contraposition.  Theorem *4.12 of [WhiteheadRussell] p. 117.  (Contributed
     by NM, 15-Apr-1995.)  (Proof shortened by Wolf Lammen, 3-Jan-2013.) $)
  con2bi $p |- ( ( ph <-> -. ps ) <-> ( ps <-> -. ph ) ) $=
    wph wps wn wb wph wn wps wn wn wb wph wn wps wb wps wph wn wb wph wps wn
    notbi wps wps wn wn wph wn wps notnotb bibi2i wph wn wps bicom 3bitr2i $.

  ${
    con2bid.1 $e |- ( ph -> ( ps <-> -. ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 15-Apr-1995.) $)
    con2bid $p |- ( ph -> ( ch <-> -. ps ) ) $=
      wph wps wch wn wb wch wps wn wb con2bid.1 wch wps con2bi sylibr $.
  $}

  ${
    con1bid.1 $e |- ( ph -> ( -. ps <-> ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 9-Oct-1999.) $)
    con1bid $p |- ( ph -> ( -. ch <-> ps ) ) $=
      wph wps wch wn wph wch wps wph wps wn wch con1bid.1 bicomd con2bid bicomd
      $.
  $}

  ${
    con1bii.1 $e |- ( -. ph <-> ps ) $.
    $( A contraposition inference.  (Contributed by NM, 12-Mar-1993.)  (Proof
       shortened by Wolf Lammen, 13-Oct-2012.) $)
    con1bii $p |- ( -. ps <-> ph ) $=
      wph wps wn wph wph wn wps wph notnotb con1bii.1 xchbinx bicomi $.
  $}

  ${
    con2bii.1 $e |- ( ph <-> -. ps ) $.
    $( A contraposition inference.  (Contributed by NM, 12-Mar-1993.) $)
    con2bii $p |- ( ps <-> -. ph ) $=
      wps wps wn wph wps notnotb con2bii.1 xchbinxr $.
  $}

  $( Contraposition.  Bidirectional version of ~ con1 .  (Contributed by NM,
     3-Jan-1993.) $)
  con1b $p |- ( ( -. ph -> ps ) <-> ( -. ps -> ph ) ) $=
    wph wn wps wi wps wn wph wi wph wps con1 wps wph con1 impbii $.

  $( Contraposition.  Bidirectional version of ~ con2 .  (Contributed by NM,
     12-Mar-1993.) $)
  con2b $p |- ( ( ph -> -. ps ) <-> ( ps -> -. ph ) ) $=
    wph wps wn wi wps wph wn wi wph wps con2 wps wph con2 impbii $.

  $( A wff is equivalent to itself with true antecedent.  (Contributed by NM,
     28-Jan-1996.) $)
  biimt $p |- ( ph -> ( ps <-> ( ph -> ps ) ) ) $=
    wph wps wph wps wi wps wph ax-1 wph wps pm2.27 impbid2 $.

  $( Theorem *5.5 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.5 $p |- ( ph -> ( ( ph -> ps ) <-> ps ) ) $=
    wph wps wph wps wi wph wps biimt bicomd $.

  ${
    a1bi.1 $e |- ph $.
    $( Inference introducing a theorem as an antecedent.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 11-Nov-2012.) $)
    a1bi $p |- ( ps <-> ( ph -> ps ) ) $=
      wph wps wph wps wi wb a1bi.1 wph wps biimt ax-mp $.
  $}

  ${
    mt2bi.1 $e |- ph $.
    $( A false consequent falsifies an antecedent.  (Contributed by NM,
       19-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Nov-2012.) $)
    mt2bi $p |- ( -. ps <-> ( ps -> -. ph ) ) $=
      wps wn wph wps wn wi wps wph wn wi wph wps wn mt2bi.1 a1bi wph wps con2b
      bitri $.
  $}

  $( Modus-tollens-like theorem.  (Contributed by NM, 7-Apr-2001.)  (Proof
     shortened by Wolf Lammen, 12-Nov-2012.) $)
  mtt $p |- ( -. ph -> ( -. ps <-> ( ps -> ph ) ) ) $=
    wph wn wps wn wph wn wps wn wi wps wph wi wph wn wps wn biimt wps wph
    con34b bitr4di $.

  $( If a proposition is false, then implying it is equivalent to being false.
     One of four theorems that can be used to simplify an implication
     ` ( ph -> ps ) ` , the other ones being ~ ax-1 (true consequent), ~ pm2.21
     (false antecedent), ~ pm5.5 (true antecedent).  (Contributed by Mario
     Carneiro, 26-Apr-2019.)  (Proof shortened by Wolf Lammen, 26-May-2019.) $)
  imnot $p |- ( -. ps -> ( ( ph -> ps ) <-> -. ph ) ) $=
    wps wn wph wn wph wps wi wps wph mtt bicomd $.

  $( Theorem *5.501 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.501 $p |- ( ph -> ( ps <-> ( ph <-> ps ) ) ) $=
    wph wps wph wps wb wph wps pm5.1im wph wps wb wph wps wph wps biimp com12
    impbid $.

  $( Implication in terms of implication and biconditional.  (Contributed by
     NM, 31-Mar-1994.)  (Proof shortened by Wolf Lammen, 24-Jan-2013.) $)
  ibib $p |- ( ( ph -> ps ) <-> ( ph -> ( ph <-> ps ) ) ) $=
    wph wps wph wps wb wph wps pm5.501 pm5.74i $.

  $( Implication in terms of implication and biconditional.  (Contributed by
     NM, 29-Apr-2005.)  (Proof shortened by Wolf Lammen, 21-Dec-2013.) $)
  ibibr $p |- ( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) ) $=
    wph wps wps wph wb wph wps wph wps wb wps wph wb wph wps pm5.501 wph wps
    bicom bitrdi pm5.74i $.

  ${
    tbt.1 $e |- ph $.
    $( A wff is equivalent to its equivalence with a truth.  (Contributed by
       NM, 18-Aug-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
    tbt $p |- ( ps <-> ( ps <-> ph ) ) $=
      wph wps wps wph wb wb tbt.1 wph wps wps wph wb wph wps ibibr pm5.74ri
      ax-mp $.
  $}

  $( The negation of a wff is equivalent to the wff's equivalence to falsehood.
     (Contributed by Juha Arpiainen, 19-Jan-2006.)  (Proof shortened by Wolf
     Lammen, 28-Jan-2013.) $)
  nbn2 $p |- ( -. ph -> ( -. ps <-> ( ph <-> ps ) ) ) $=
    wph wn wps wn wph wn wps wn wb wph wps wb wph wn wps wn pm5.501 wph wps
    notbi bitr4di $.

  $( Transfer negation via an equivalence.  (Contributed by NM, 3-Oct-2007.)
     (Proof shortened by Wolf Lammen, 28-Jan-2013.) $)
  bibif $p |- ( -. ps -> ( ( ph <-> ps ) <-> -. ph ) ) $=
    wps wn wph wn wps wph wb wph wps wb wps wph nbn2 wps wph bicom bitr2di $.

  ${
    nbn.1 $e |- -. ph $.
    $( The negation of a wff is equivalent to the wff's equivalence to
       falsehood.  (Contributed by NM, 21-Jun-1993.)  (Proof shortened by Wolf
       Lammen, 3-Oct-2013.) $)
    nbn $p |- ( -. ps <-> ( ps <-> ph ) ) $=
      wps wph wb wps wn wph wn wps wph wb wps wn wb nbn.1 wps wph bibif ax-mp
      bicomi $.
  $}

  ${
    nbn3.1 $e |- ph $.
    $( Transfer falsehood via equivalence.  (Contributed by NM,
       11-Sep-2006.) $)
    nbn3 $p |- ( -. ps <-> ( ps <-> -. ph ) ) $=
      wph wn wps wph nbn3.1 notnoti nbn $.
  $}

  $( Two propositions are equivalent if they are both false.  Closed form of
     ~ 2false .  Equivalent to a ~ biimpr -like version of the xor-connective.
     (Contributed by Wolf Lammen, 13-May-2013.) $)
  pm5.21im $p |- ( -. ph -> ( -. ps -> ( ph <-> ps ) ) ) $=
    wph wn wps wn wph wps wb wph wps nbn2 biimpd $.

  ${
    2false.1 $e |- -. ph $.
    2false.2 $e |- -. ps $.
    $( Two falsehoods are equivalent.  (Contributed by NM, 4-Apr-2005.)  (Proof
       shortened by Wolf Lammen, 19-May-2013.) $)
    2false $p |- ( ph <-> ps ) $=
      wph wps wph wn wps wn 2false.1 2false.2 2th con4bii $.
  $}

  ${
    2falsed.1 $e |- ( ph -> -. ps ) $.
    2falsed.2 $e |- ( ph -> -. ch ) $.
    $( Two falsehoods are equivalent (deduction form).  (Contributed by NM,
       11-Oct-2013.)  (Proof shortened by Wolf Lammen, 11-Apr-2024.) $)
    2falsed $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch wph wps wn wch wn 2falsed.1 2falsed.2 2thd con4bid $.

    $( Obsolete version of ~ 2falsed as of 11-Apr-2024.  (Contributed by NM,
       11-Oct-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    2falsedOLD $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wch wph wps wch 2falsed.1 pm2.21d wph wch wps 2falsed.2 pm2.21d
      impbid $.
  $}

  ${
    pm5.21ni.1 $e |- ( ph -> ps ) $.
    pm5.21ni.2 $e |- ( ch -> ps ) $.
    $( Two propositions implying a false one are equivalent.  (Contributed by
       NM, 16-Feb-1996.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
    pm5.21ni $p |- ( -. ps -> ( ph <-> ch ) ) $=
      wps wn wph wch wph wps pm5.21ni.1 con3i wch wps pm5.21ni.2 con3i 2falsed
      $.

    ${
      pm5.21nii.3 $e |- ( ps -> ( ph <-> ch ) ) $.
      $( Eliminate an antecedent implied by each side of a biconditional.
         (Contributed by NM, 21-May-1999.) $)
      pm5.21nii $p |- ( ph <-> ch ) $=
        wps wph wch wb pm5.21nii.3 wph wps wch pm5.21ni.1 pm5.21ni.2 pm5.21ni
        pm2.61i $.
    $}
  $}

  ${
    pm5.21ndd.1 $e |- ( ph -> ( ch -> ps ) ) $.
    pm5.21ndd.2 $e |- ( ph -> ( th -> ps ) ) $.
    pm5.21ndd.3 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Eliminate an antecedent implied by each side of a biconditional,
       deduction version.  (Contributed by Paul Chapman, 21-Nov-2012.)  (Proof
       shortened by Wolf Lammen, 6-Oct-2013.) $)
    pm5.21ndd $p |- ( ph -> ( ch <-> th ) ) $=
      wph wps wch wth wb pm5.21ndd.3 wph wps wn wch wn wth wn wch wth wb wph
      wch wps pm5.21ndd.1 con3d wph wth wps pm5.21ndd.2 con3d wch wth pm5.21im
      syl6c pm2.61d $.
  $}

  ${
    bija.1 $e |- ( ph -> ( ps -> ch ) ) $.
    bija.2 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
    $( Combine antecedents into a single biconditional.  This inference,
       reminiscent of ~ ja , is reversible:  The hypotheses can be deduced from
       the conclusion alone (see ~ pm5.1im and ~ pm5.21im ).  (Contributed by
       Wolf Lammen, 13-May-2013.) $)
    bija $p |- ( ( ph <-> ps ) -> ch ) $=
      wph wps wb wps wch wps wph wps wb wph wch wph wps biimpr bija.1 syli wps
      wn wph wps wb wph wn wch wph wps wb wph wps wph wps biimp con3d bija.2
      syli pm2.61d $.
  $}

  $( Theorem *5.18 of [WhiteheadRussell] p. 124.  This theorem says that
     logical equivalence is the same as negated "exclusive or".  (Contributed
     by NM, 28-Jun-2002.)  (Proof shortened by Andrew Salmon, 20-Jun-2011.)
     (Proof shortened by Wolf Lammen, 15-Oct-2013.) $)
  pm5.18 $p |- ( ( ph <-> ps ) <-> -. ( ph <-> -. ps ) ) $=
    wph wph wps wb wph wps wn wb wn wb wph wph wps wn wb wn wps wph wps wb wph
    wps wph wps wn wb wph wps wn pm5.501 con1bid wph wps pm5.501 bitr2d wph wn
    wph wps wn wb wn wps wn wph wps wb wph wn wps wn wph wps wn wb wph wps wn
    nbn2 con1bid wph wps nbn2 bitr2d pm2.61i $.

  $( Two ways to express "exclusive or".  (Contributed by NM, 1-Jan-2006.) $)
  xor3 $p |- ( -. ( ph <-> ps ) <-> ( ph <-> -. ps ) ) $=
    wph wps wn wb wph wps wb wn wph wps wb wph wps wn wb wph wps pm5.18 con2bii
    bicomi $.

  $( Move negation outside of biconditional.  Compare Theorem *5.18 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 27-Jun-2002.)  (Proof
     shortened by Wolf Lammen, 20-Sep-2013.) $)
  nbbn $p |- ( ( -. ph <-> ps ) <-> -. ( ph <-> ps ) ) $=
    wph wps wb wn wph wps wn wb wps wph wn wb wph wn wps wb wph wps xor3 wph
    wps con2bi wps wph wn bicom 3bitrri $.

  $( Associative law for the biconditional.  An axiom of system DS in Vladimir
     Lifschitz, "On calculational proofs", Annals of Pure and Applied Logic,
     113:207-224, 2002,
     ~ http://www.cs.utexas.edu/users/ai-lab/pub-view.php?PubID=26805 .
     Interestingly, this law was not included in _Principia Mathematica_ but
     was apparently first noted by Jan Lukasiewicz circa 1923.  (Contributed by
     NM, 8-Jan-2005.)  (Proof shortened by Juha Arpiainen, 19-Jan-2006.)
     (Proof shortened by Wolf Lammen, 21-Sep-2013.) $)
  biass $p |- ( ( ( ph <-> ps ) <-> ch ) <-> ( ph <-> ( ps <-> ch ) ) ) $=
    wph wph wps wb wch wb wph wps wch wb wb wb wph wps wch wb wph wps wb wch wb
    wph wps wch wb wb wph wps wph wps wb wch wph wps pm5.501 bibi1d wph wps wch
    wb pm5.501 bitr3d wph wn wps wch wb wn wph wps wb wch wb wph wps wch wb wb
    wps wch wb wn wps wn wch wb wph wn wph wps wb wch wb wps wch nbbn wph wn
    wps wn wph wps wb wch wph wps nbn2 bibi1d bitr3id wph wps wch wb nbn2
    bitr3d pm2.61i $.

  $( Lukasiewicz's shortest axiom for equivalential calculus.  Storrs McCall,
     ed., _Polish Logic 1920-1939_ (Oxford, 1967), p. 96.  (Contributed by NM,
     10-Jan-2005.) $)
  biluk $p |- ( ( ph <-> ps ) <-> ( ( ch <-> ps ) <-> ( ph <-> ch ) ) ) $=
    wph wps wb wch wps wph wch wb wb wb wch wps wb wph wch wb wb wph wps wb wch
    wb wps wph wch wb wb wb wph wps wb wch wps wph wch wb wb wb wb wph wps wb
    wch wb wps wph wb wch wb wps wph wch wb wb wph wps wb wps wph wb wch wph
    wps bicom bibi1i wps wph wch biass bitri wph wps wb wch wps wph wch wb wb
    biass mpbi wch wps wph wch wb biass bitr4i $.

  $( Theorem *5.19 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.19 $p |- -. ( ph <-> -. ph ) $=
    wph wph wb wph wph wn wb wn wph biid wph wph pm5.18 mpbi $.

  $( Logical equivalence of commuted antecedents.  Part of Theorem *4.87 of
     [WhiteheadRussell] p. 122.  (Contributed by NM, 11-May-1993.) $)
  bi2.04 $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wps wph wch wi wi wph wps wch pm2.04 wps wph wch pm2.04
    impbii $.

  $( Antecedent absorption implication.  Theorem *5.4 of [WhiteheadRussell]
     p. 125.  (Contributed by NM, 5-Aug-1993.) $)
  pm5.4 $p |- ( ( ph -> ( ph -> ps ) ) <-> ( ph -> ps ) ) $=
    wph wph wps wi wps wph wps pm5.5 pm5.74i $.

  $( Distributive law for implication.  Compare Theorem *5.41 of
     [WhiteheadRussell] p. 125.  (Contributed by NM, 5-Aug-1993.) $)
  imdi $p |- ( ( ph -> ( ps -> ch ) ) <->
               ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wph wps wi wph wch wi wi wph wps wch ax-2 wph wps wch
    pm2.86 impbii $.

  $( Theorem *5.41 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 12-Oct-2012.) $)
  pm5.41 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) <->
                ( ph -> ( ps -> ch ) ) ) $=
    wph wps wch wi wi wph wps wi wph wch wi wi wph wps wch imdi bicomi $.

  $( The antecedent of one side of a biconditional can be moved out of the
     biconditional to become the antecedent of the remaining biconditional.
     (Contributed by BJ, 1-Jan-2025.)  (Proof shortened by Wolf Lammen,
     5-Jan-2025.) $)
  imbibi $p |- ( ( ( ph -> ps ) <-> ch ) -> ( ph -> ( ps <-> ch ) ) ) $=
    wph wps wi wch wb wph wps wch wph wps wi wph wph wps wi wi wph wps wi wch
    wb wph wch wi wph wps pm5.4 wph wps wi wch wph imbi2 bitr3id pm5.74rd $.

  $( Theorem *4.8 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.8 $p |- ( ( ph -> -. ph ) <-> -. ph ) $=
    wph wph wn wi wph wn wph pm2.01 wph wn wph ax-1 impbii $.

  $( A formula is equivalent to its negation implying it.  Theorem *4.81 of
     [WhiteheadRussell] p. 122.  Note that the second step, using ~ pm2.24 ,
     could also use ~ ax-1 .  (Contributed by NM, 3-Jan-2005.) $)
  pm4.81 $p |- ( ( -. ph -> ph ) <-> ph ) $=
    wph wn wph wi wph wph pm2.18 wph wph pm2.24 impbii $.

  $( Simplify an implication between two implications when the antecedent of
     the first is a consequence of the antecedent of the second.  The reverse
     form is useful in producing the successor step in induction proofs.
     (Contributed by Paul Chapman, 22-Jun-2011.)  (Proof shortened by Wolf
     Lammen, 14-Sep-2013.) $)
  imim21b $p |- ( ( ps -> ph ) ->
           ( ( ( ph -> ch ) -> ( ps -> th ) ) <-> ( ps -> ( ch -> th ) ) ) ) $=
    wph wch wi wps wth wi wi wps wph wch wi wth wi wi wps wph wi wps wch wth wi
    wi wph wch wi wps wth bi2.04 wps wph wi wps wph wch wi wth wi wch wth wi
    wph wph wch wi wth wi wch wth wi wb wps wph wph wch wi wch wth wph wch
    pm5.5 imbi1d imim2i pm5.74d bitrid $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical conjunction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section defines conjunction of two formulas, denoted by infix " ` /\ ` "
  and read "and".  It is defined in terms of implication and negation, which is
  possible in classical logic (but not in intuitionistic logic: see iset.mm).

  After the definition, we briefly introduce conversion of simple expressions
  to and from conjunction.  Two simple operations called importation ( ~ imp )
  and exportation ( ~ ex ) follow.  In the propositions-as-types
  interpretation, they correspond to uncurrying and currying respectively. They
  are foundational for this section.  Most of the theorems proved here trace
  back to them, mostly indirectly, in a layered fashion, where more complex
  expressions are built from simpler ones.  Here are some of these successive
  layers:
  importation and exportation,
  commutativity and associativity laws,
  adding antecedents and simplifying,
  conjunction of consequents,
  syllogisms,
  etc.

  As indicated in the "note on definitions" in the section comment for logical
  equivalence, some theorems containing only implication, negation and
  conjunction are placed in the section after disjunction since theirs proofs
  use disjunction (although this is not required since definitions are
  conservative, see said section comment).

$)

  $( Declare connective for conjunction ("and"). $)
  $c /\ $.  $( Wedge (read:  "and") $)

  $( Extend wff definition to include conjunction ("and"). $)
  wa $a wff ( ph /\ ps ) $.

  $( Define conjunction (logical "and").  Definition of [Margaris] p. 49.  When
     both the left and right operand are true, the result is true; when either
     is false, the result is false.  For example, it is true that
     ` ( 2 = 2 /\ 3 = 3 ) ` .  After we define the constant true ` T. `
     ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be able
     to prove these truth table values: ` ( ( T. /\ T. ) <-> T. ) `
     ( ~ truantru ), ` ( ( T. /\ F. ) <-> F. ) ` ( ~ truanfal ),
     ` ( ( F. /\ T. ) <-> F. ) ` ( ~ falantru ), and
     ` ( ( F. /\ F. ) <-> F. ) ` ( ~ falanfal ).

     This is our first use of the biconditional connective in a definition; we
     use the biconditional connective in place of the traditional "<=def=>",
     which means the same thing, except that we can manipulate the
     biconditional connective directly in proofs rather than having to rely on
     an informal definition substitution rule.  Note that if we mechanically
     substitute ` -. ( ph -> -. ps ) ` for ` ( ph /\ ps ) ` , we end up with an
     instance of previously proved theorem ~ biid .  This is the justification
     for the definition, along with the fact that it introduces a new symbol
     ` /\ ` .  Contrast with ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), ` -/\ `
     ( ~ df-nan ), and ` \/_ ` ( ~ df-xor ).  (Contributed by NM,
     5-Jan-1993.) $)
  df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.

  $( Theorem *4.63 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.63 $p |- ( -. ( ph -> -. ps ) <-> ( ph /\ ps ) ) $=
    wph wps wa wph wps wn wi wn wph wps df-an bicomi $.

  $( Theorem *4.67 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.67 $p |- ( -. ( -. ph -> -. ps ) <-> ( -. ph /\ ps ) ) $=
    wph wn wps pm4.63 $.

  $( Express an implication in terms of a negated conjunction.  (Contributed by
     NM, 9-Apr-1994.) $)
  imnan $p |- ( ( ph -> -. ps ) <-> -. ( ph /\ ps ) ) $=
    wph wps wa wph wps wn wi wph wps df-an con2bii $.

  ${
    imnani.1 $e |- -. ( ph /\ ps ) $.
    $( Infer an implication from a negated conjunction.  (Contributed by Mario
       Carneiro, 28-Sep-2015.) $)
    imnani $p |- ( ph -> -. ps ) $=
      wph wps wn wi wph wps wa wn imnani.1 wph wps imnan mpbir $.
  $}

  $( Implication in terms of conjunction and negation.  Theorem 3.4(27) of
     [Stoll] p. 176.  (Contributed by NM, 12-Mar-1993.)  (Proof shortened by
     Wolf Lammen, 30-Oct-2012.) $)
  iman $p |- ( ( ph -> ps ) <-> -. ( ph /\ -. ps ) ) $=
    wph wps wi wph wps wn wn wi wph wps wn wa wn wps wps wn wn wph wps notnotb
    imbi2i wph wps wn imnan bitri $.

  $( Law of noncontradiction.  Theorem *3.24 of [WhiteheadRussell] p. 111 (who
     call it the "law of contradiction").  (Contributed by NM, 16-Sep-1993.)
     (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
  pm3.24 $p |- -. ( ph /\ -. ph ) $=
    wph wph wi wph wph wn wa wn wph id wph wph iman mpbi $.

  $( Express a conjunction in terms of a negated implication.  (Contributed by
     NM, 2-Aug-1994.) $)
  annim $p |- ( ( ph /\ -. ps ) <-> -. ( ph -> ps ) ) $=
    wph wps wi wph wps wn wa wph wps iman con2bii $.

  $( Theorem *4.61 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.61 $p |- ( -. ( ph -> ps ) <-> ( ph /\ -. ps ) ) $=
    wph wps wn wa wph wps wi wn wph wps annim bicomi $.

  $( Theorem *4.65 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.65 $p |- ( -. ( -. ph -> ps ) <-> ( -. ph /\ -. ps ) ) $=
    wph wn wps pm4.61 $.

  ${
    imp.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Importation inference.  (Contributed by NM, 3-Jan-1993.)  (Proof
       shortened by Eric Schmidt, 22-Dec-2006.) $)
    imp $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wa wph wps wn wi wn wch wph wps df-an wph wps wch imp.1 impi
      sylbi $.

    $( Importation inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)
    impcom $p |- ( ( ps /\ ph ) -> ch ) $=
      wps wph wch wph wps wch imp.1 com12 imp $.
  $}

  ${
    con3dimp.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Variant of ~ con3d with importation.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
    con3dimp $p |- ( ( ph /\ -. ch ) -> -. ps ) $=
      wph wch wn wps wn wph wps wch con3dimp.1 con3d imp $.
  $}

  ${
    mpnanrd.1 $e |- ( ph -> ps ) $.
    mpnanrd.2 $e |- ( ph -> -. ( ps /\ ch ) ) $.
    $( Eliminate the right side of a negated conjunction in an implication.
       (Contributed by ML, 17-Oct-2020.) $)
    mpnanrd $p |- ( ph -> -. ch ) $=
      wph wps wch wn mpnanrd.1 wph wps wch wa wn wps wch wn wi mpnanrd.2 wps
      wch imnan sylibr mpd $.
  $}

  ${
    impd.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Importation deduction.  (Contributed by NM, 31-Mar-1994.) $)
    impd $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      wps wch wa wph wth wps wch wph wth wi wph wps wch wth impd.1 com3l imp
      com12 $.

    $( Importation deduction with commuted antecedents.  (Contributed by Peter
       Mazsa, 24-Sep-2022.)  (Proof shortened by Wolf Lammen, 22-Oct-2022.) $)
    impcomd $p |- ( ph -> ( ( ch /\ ps ) -> th ) ) $=
      wph wch wps wth wph wps wch wth impd.1 com23 impd $.
  $}

  ${
    ex.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Exportation inference.  (This theorem used to be labeled "exp" but was
       changed to "ex" so as not to conflict with the math token "exp", per the
       June 2006 Metamath spec change.)  A translation of natural deduction
       rule ` -> ` I ( ` -> ` introduction), see ~ natded .  (Contributed by
       NM, 3-Jan-1993.)  (Proof shortened by Eric Schmidt, 22-Dec-2006.) $)
    ex $p |- ( ph -> ( ps -> ch ) ) $=
      wph wps wch wph wps wn wi wn wph wps wa wch wph wps df-an ex.1 sylbir
      expi $.

    $( Exportation inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)
    expcom $p |- ( ps -> ( ph -> ch ) ) $=
      wph wps wch wph wps wch ex.1 ex com12 $.
  $}

  ${
    expd.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Commuted form of ~ expd .  (Contributed by Alan Sare, 18-Mar-2012.)
       Shorten ~ expd .  (Revised by Wolf Lammen, 28-Jul-2022.) $)
    expdcom $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $=
      wps wch wph wth wi wph wps wch wa wth expd.1 com12 ex $.

    $( Exportation deduction.  (Contributed by NM, 20-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 28-Jul-2022.) $)
    expd $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      wps wch wph wth wph wps wch wth expd.1 expdcom com3r $.
  $}

  ${
    expcomd.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Deduction form of ~ expcom .  (Contributed by Alan Sare,
       22-Jul-2012.) $)
    expcomd $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
      wph wps wch wth wph wps wch wth expcomd.1 expd com23 $.
  $}

  ${
    imp31.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp31 $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      wph wps wa wch wth wph wps wch wth wi imp31.1 imp imp $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp32 $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      wph wps wch wa wth wph wps wch wth imp31.1 impd imp $.
  $}

  ${
    exp31.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp31 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      wph wps wch wth wi wph wps wa wch wth exp31.1 ex ex $.
  $}

  ${
    exp32.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp32 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      wph wps wch wth wph wps wch wa wth exp32.1 ex expd $.
  $}

  ${
    imp4.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( An importation inference.  (Contributed by NM, 26-Apr-1994.)  Shorten
       ~ imp4a .  (Revised by Wolf Lammen, 19-Jul-2021.) $)
    imp4b $p |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $=
      wph wps wa wch wth wta wph wps wch wth wta wi wi imp4.1 imp impd $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 19-Jul-2021.) $)
    imp4a $p |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $=
      wph wps wch wth wa wta wi wph wps wch wth wta imp4.1 imp4b ex $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp4c $p |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $=
      wph wps wch wa wth wta wph wps wch wth wta wi imp4.1 impd impd $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp4d $p |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $=
      wph wps wch wth wa wta wph wps wch wth wta imp4.1 imp4a impd $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp41 $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $=
      wph wps wa wch wth wta wph wps wch wth wta wi wi imp4.1 imp imp31 $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp42 $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $=
      wph wps wch wa wa wth wta wph wps wch wth wta wi imp4.1 imp32 imp $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp43 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $=
      wph wps wa wch wth wa wta wph wps wch wth wta imp4.1 imp4b imp $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp44 $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $=
      wph wps wch wa wth wa wta wph wps wch wth wta imp4.1 imp4c imp $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp45 $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $=
      wph wps wch wth wa wa wta wph wps wch wth wta imp4.1 imp4d imp $.
  $}

  ${
    exp4b.1 $e |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 23-Nov-2012.)  Shorten ~ exp4a .  (Revised by
       Wolf Lammen, 20-Jul-2021.) $)
    exp4b $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wi wi wph wps wa wch wth wta exp4b.1 expd ex $.
  $}

  ${
    exp4a.1 $e |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 20-Jul-2021.) $)
    exp4a $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wph wps wch wth wa wta wi exp4a.1 imp exp4b $.
  $}

  ${
    exp4c.1 $e |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp4c $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wi wph wps wch wa wth wta exp4c.1 expd expd $.
  $}

  ${
    exp4d.1 $e |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp4d $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wph wps wch wth wa wta exp4d.1 expd exp4a $.
  $}

  ${
    exp41.1 $e |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp41 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wi wph wps wa wch wa wth wta exp41.1 ex exp31 $.
  $}

  ${
    exp42.1 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp42 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wi wph wps wch wa wth wta exp42.1 exp31 expd $.
  $}

  ${
    exp43.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp43 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wph wps wa wch wth wa wta exp43.1 ex exp4b $.
  $}

  ${
    exp44.1 $e |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp44 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wi wph wps wch wa wth wta exp44.1 exp32 expd $.
  $}

  ${
    exp45.1 $e |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp45 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      wph wps wch wth wta wph wps wch wth wa wta exp45.1 exp32 exp4a $.
  $}

  ${
    imp5.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5d $p |- ( ( ( ph /\ ps ) /\ ch ) -> ( ( th /\ ta ) -> et ) ) $=
      wph wps wa wch wa wth wta wet wph wps wch wth wta wet wi wi imp5.1 imp31
      impd $.

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.)
       (Proof shortened by Wolf Lammen, 2-Aug-2022.) $)
    imp5a $p |- ( ph -> ( ps -> ( ch -> ( ( th /\ ta ) -> et ) ) ) ) $=
      wph wps wch wth wta wa wet wi wph wps wch wth wta wet imp5.1 imp5d exp31
      $.

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5g $p |- ( ( ph /\ ps ) -> ( ( ( ch /\ th ) /\ ta ) -> et ) ) $=
      wph wps wa wch wth wa wta wet wph wps wch wth wta wet wi imp5.1 imp4b
      impd $.

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp55 $p |- ( ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) /\ ta ) -> et ) $=
      wph wps wch wth wa wta wet wph wps wch wth wta wet wi imp5.1 imp4a imp42
      $.

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp511 $p |- ( ( ph /\ ( ( ps /\ ( ch /\ th ) ) /\ ta ) ) -> et ) $=
      wph wps wch wth wa wta wet wph wps wch wth wta wet wi imp5.1 imp4a imp44
      $.
  $}

  ${
    exp5c.1 $e |- ( ph -> ( ( ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp5c $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      wph wps wch wth wta wet wi wi wph wps wch wa wth wta wet exp5c.1 exp4a
      expd $.
  $}

  ${
    exp5j.1 $e |- ( ph -> ( ( ( ( ps /\ ch ) /\ th ) /\ ta ) -> et ) ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp5j $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      wph wps wch wth wta wet wi wph wps wch wa wth wa wta wet exp5j.1 expd
      exp4c $.
  $}

  ${
    exp5l.1 $e |- ( ph -> ( ( ( ps /\ ch ) /\ ( th /\ ta ) ) -> et ) ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp5l $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      wph wps wch wth wta wet wph wps wch wa wth wta wa wet exp5l.1 expd exp5c
      $.
  $}

  ${
    exp53.1 $e |- ( ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) /\ ta ) -> et ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    exp53 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      wph wps wch wth wta wet wi wph wps wa wch wth wa wa wta wet exp53.1 ex
      exp43 $.
  $}

  $( Theorem *3.3 (Exp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
  pm3.3 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    wph wps wa wch wi wph wps wch wph wps wa wch wi id expd $.

  $( Theorem *3.31 (Imp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
  pm3.31 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) ) $=
    wph wps wch wi wi wph wps wch wph wps wch wi wi id impd $.

  $( Import-export theorem.  Part of Theorem *4.87 of [WhiteheadRussell]
     p. 122.  (Contributed by NM, 10-Jan-1993.)  (Proof shortened by Wolf
     Lammen, 24-Mar-2013.) $)
  impexp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) $=
    wph wps wa wch wi wph wps wch wi wi wph wps wch pm3.3 wph wps wch pm3.31
    impbii $.

  ${
    impancom.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Mixed importation/commutation inference.  (Contributed by NM,
       22-Jun-2013.) $)
    impancom $p |- ( ( ph /\ ch ) -> ( ps -> th ) ) $=
      wph wch wps wth wi wph wps wch wth wph wps wch wth wi impancom.1 ex com23
      imp $.
  $}

  ${
    expdimp.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction version of exportation, followed by importation.
       (Contributed by NM, 6-Sep-2008.) $)
    expdimp $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      wph wps wch wth wi wph wps wch wth expdimp.1 expd imp $.
  $}

  ${
    expimpd.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Exportation followed by a deduction version of importation.
       (Contributed by NM, 6-Sep-2008.) $)
    expimpd $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      wph wps wch wth wph wps wch wth wi expimpd.1 ex impd $.
  $}

  ${
    impr.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Import a wff into a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    impr $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      wph wps wch wth wph wps wch wth wi impr.1 ex imp32 $.
  $}

  ${
    impl.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Export a wff from a left conjunct.  (Contributed by Mario Carneiro,
       9-Jul-2014.) $)
    impl $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      wph wps wch wth wph wps wch wth impl.1 expd imp31 $.
  $}

  ${
    expr.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Export a wff from a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    expr $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      wph wps wch wth wi wph wps wch wth expr.1 exp32 imp $.
  $}

  ${
    expl.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Export a wff from a left conjunct.  (Contributed by Jeff Hankins,
       28-Aug-2009.) $)
    expl $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      wph wps wch wth wph wps wch wth expl.1 exp31 impd $.
  $}

  ${
    ancoms.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Inference commuting conjunction in antecedent.  (Contributed by NM,
       21-Apr-1994.) $)
    ancoms $p |- ( ( ps /\ ph ) -> ch ) $=
      wps wph wch wph wps wch ancoms.1 expcom imp $.
  $}

  $( Theorem *3.22 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 13-Nov-2012.) $)
  pm3.22 $p |- ( ( ph /\ ps ) -> ( ps /\ ph ) ) $=
    wps wph wps wph wa wps wph wa id ancoms $.

  $( Commutative law for conjunction.  Theorem *4.3 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 25-Jun-1998.)  (Proof shortened by Wolf
     Lammen, 4-Nov-2012.) $)
  ancom $p |- ( ( ph /\ ps ) <-> ( ps /\ ph ) ) $=
    wph wps wa wps wph wa wph wps pm3.22 wps wph pm3.22 impbii $.

  ${
    ancomd.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Commutation of conjuncts in consequent.  (Contributed by Jeff Hankins,
       14-Aug-2009.) $)
    ancomd $p |- ( ph -> ( ch /\ ps ) ) $=
      wph wps wch wa wch wps wa ancomd.1 wps wch ancom sylib $.
  $}

  ${
    biancomi.1 $e |- ( ph <-> ( ch /\ ps ) ) $.
    $( Commuting conjunction in a biconditional.  (Contributed by Peter Mazsa,
       17-Jun-2018.) $)
    biancomi $p |- ( ph <-> ( ps /\ ch ) ) $=
      wph wch wps wa wps wch wa biancomi.1 wps wch ancom bitr4i $.
  $}

  ${
    biancomd.1 $e |- ( ph -> ( ps <-> ( th /\ ch ) ) ) $.
    $( Commuting conjunction in a biconditional, deduction form.  (Contributed
       by Peter Mazsa, 3-Oct-2018.) $)
    biancomd $p |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $=
      wph wps wth wch wa wch wth wa biancomd.1 wth wch ancom bitrdi $.
  $}

  $( Closed form of ~ ancoms .  (Contributed by Alan Sare, 31-Dec-2011.) $)
  ancomst $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ps /\ ph ) -> ch ) ) $=
    wph wps wa wps wph wa wch wph wps ancom imbi1i $.

  ${
    ancomsd.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Deduction commuting conjunction in antecedent.  (Contributed by NM,
       12-Dec-2004.) $)
    ancomsd $p |- ( ph -> ( ( ch /\ ps ) -> th ) ) $=
      wph wch wps wth wph wps wch wth ancomsd.1 expcomd impd $.
  $}

  ${
    anasss.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by NM, 15-Nov-2002.) $)
    anasss $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      wph wps wch wth wph wps wch wth anasss.1 exp31 imp32 $.
  $}

  ${
    anassrs.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by NM, 15-Nov-2002.) $)
    anassrs $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      wph wps wch wth wph wps wch wth anassrs.1 exp32 imp31 $.
  $}

  $( Associative law for conjunction.  Theorem *4.32 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 21-Jun-1993.)  (Proof shortened by Wolf
     Lammen, 24-Nov-2012.) $)
  anass $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $=
    wph wps wa wch wa wph wps wch wa wa wph wps wch wph wps wch wa wa wph wps
    wch wa wa id anassrs wph wps wch wph wps wa wch wa wph wps wa wch wa id
    anasss impbii $.

  $( Join antecedents with conjunction ("conjunction introduction").  Theorem
     *3.2 of [WhiteheadRussell] p. 111.  Its associated inference is ~ pm3.2i
     and its associated deduction is ~ jca (and the double deduction is
     ~ jcad ).  See ~ pm3.2im for a version using only implication and
     negation.  (Contributed by NM, 5-Jan-1993.)  (Proof shortened by Wolf
     Lammen, 12-Nov-2012.) $)
  pm3.2 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $=
    wph wps wph wps wa wph wps wa id ex $.

  ${
    pm3.2i.1 $e |- ph $.
    pm3.2i.2 $e |- ps $.
    $( Infer conjunction of premises.  Inference associated with ~ pm3.2 .  Its
       associated deduction is ~ jca (and the double deduction is ~ jcad ).
       (Contributed by NM, 21-Jun-1993.) $)
    pm3.2i $p |- ( ph /\ ps ) $=
      wph wps wph wps wa pm3.2i.1 pm3.2i.2 wph wps pm3.2 mp2 $.
  $}

  $( Join antecedents with conjunction.  Theorem *3.21 of [WhiteheadRussell]
     p. 111.  (Contributed by NM, 5-Aug-1993.) $)
  pm3.21 $p |- ( ph -> ( ps -> ( ps /\ ph ) ) ) $=
    wps wph wps wph wa wps wph wa id expcom $.

  $( Nested conjunction of antecedents.  (Contributed by NM, 4-Jan-1993.) $)
  pm3.43i $p |- ( ( ph -> ps )
      -> ( ( ph -> ch ) -> ( ph -> ( ps /\ ch ) ) ) ) $=
    wps wch wps wch wa wph wps wch pm3.2 imim3i $.

  $( Theorem *3.43 (Comp) of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.43 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) )
      -> ( ph -> ( ps /\ ch ) ) ) $=
    wph wps wi wph wch wi wph wps wch wa wi wph wps wch pm3.43i imp $.

  $( A theorem similar to the standard definition of the biconditional.
     Definition of [Margaris] p. 49.  (Contributed by NM, 24-Jan-1993.) $)
  dfbi2 $p |- ( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) $=
    wph wps wb wph wps wi wps wph wi wn wi wn wph wps wi wps wph wi wa wph wps
    dfbi1 wph wps wi wps wph wi df-an bitr4i $.

  $( Definition ~ df-bi rewritten in an abbreviated form to help intuitive
     understanding of that definition.  Note that it is a conjunction of two
     implications; one which asserts properties that follow from the
     biconditional and one which asserts properties that imply the
     biconditional.  (Contributed by NM, 15-Aug-2008.) $)
  dfbi $p |- ( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) )
        /\ ( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $=
    wph wps wb wph wps wi wps wph wi wa wb wph wps wb wph wps wi wps wph wi wa
    wi wph wps wi wps wph wi wa wph wps wb wi wa wph wps dfbi2 wph wps wb wph
    wps wi wps wph wi wa dfbi2 mpbi $.

  ${
    biimpa.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Importation inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
    biimpa $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wch wph wps wch biimpa.1 biimpd imp $.

    $( Importation inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
    biimpar $p |- ( ( ph /\ ch ) -> ps ) $=
      wph wch wps wph wps wch biimpa.1 biimprd imp $.

    $( Importation inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
    biimpac $p |- ( ( ps /\ ph ) -> ch ) $=
      wps wph wch wph wps wch biimpa.1 biimpcd imp $.

    $( Importation inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
    biimparc $p |- ( ( ch /\ ph ) -> ps ) $=
      wch wph wps wph wps wch biimpa.1 biimprcd imp $.
  $}

  ${
    adantr.1 $e |- ( ph -> ps ) $.
    $( Inference adding a conjunct to the right of an antecedent.  (Contributed
       by NM, 30-Aug-1993.) $)
    adantr $p |- ( ( ph /\ ch ) -> ps ) $=
      wph wch wps wph wps wch adantr.1 a1d imp $.
  $}

  ${
    adantl.1 $e |- ( ph -> ps ) $.
    $( Inference adding a conjunct to the left of an antecedent.  (Contributed
       by NM, 30-Aug-1993.)  (Proof shortened by Wolf Lammen, 23-Nov-2012.) $)
    adantl $p |- ( ( ch /\ ph ) -> ps ) $=
      wph wch wps wph wps wch adantl.1 adantr ancoms $.
  $}

  $( Elimination of a conjunct.  Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 3-Jan-1993.)  (Proof shortened by Wolf
     Lammen, 14-Jun-2022.) $)
  simpl $p |- ( ( ph /\ ps ) -> ph ) $=
    wph wph wps wph id adantr $.

  ${
    simpli.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct.  (Contributed by NM, 15-Jun-1994.) $)
    simpli $p |- ph $=
      wph wps wa wph simpli.1 wph wps simpl ax-mp $.
  $}

  $( Elimination of a conjunct.  Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 3-Jan-1993.)  (Proof shortened by Wolf
     Lammen, 14-Jun-2022.) $)
  simpr $p |- ( ( ph /\ ps ) -> ps ) $=
    wps wps wph wps id adantl $.

  ${
    simpri.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct.  (Contributed by NM, 15-Jun-1994.) $)
    simpri $p |- ps $=
      wph wps wa wps simpri.1 wph wps simpr ax-mp $.
  $}

  ${
    intnan.1 $e |- -. ph $.
    $( Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       16-Sep-1993.) $)
    intnan $p |- -. ( ps /\ ph ) $=
      wps wph wa wph intnan.1 wps wph simpr mto $.

    $( Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       3-Apr-1995.) $)
    intnanr $p |- -. ( ph /\ ps ) $=
      wph wps wa wph intnan.1 wph wps simpl mto $.
  $}

  ${
    intnand.1 $e |- ( ph -> -. ps ) $.
    $( Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       10-Jul-2005.) $)
    intnand $p |- ( ph -> -. ( ch /\ ps ) ) $=
      wph wps wch wps wa intnand.1 wch wps simpr nsyl $.

    $( Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       10-Jul-2005.) $)
    intnanrd $p |- ( ph -> -. ( ps /\ ch ) ) $=
      wph wps wps wch wa intnand.1 wps wch simpl nsyl $.
  $}

  ${
    adantld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding a conjunct to the left of an antecedent.  (Contributed
       by NM, 4-May-1994.)  (Proof shortened by Wolf Lammen, 20-Dec-2012.) $)
    adantld $p |- ( ph -> ( ( th /\ ps ) -> ch ) ) $=
      wth wps wa wps wph wch wth wps simpr adantld.1 syl5 $.
  $}

  ${
    adantrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding a conjunct to the right of an antecedent.  (Contributed
       by NM, 4-May-1994.) $)
    adantrd $p |- ( ph -> ( ( ps /\ th ) -> ch ) ) $=
      wps wth wa wps wph wch wps wth simpl adantrd.1 syl5 $.
  $}

  $( Theorem *3.41 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.41 $p |- ( ( ph -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $=
    wph wps wa wph wch wph wps simpl imim1i $.

  $( Theorem *3.42 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.42 $p |- ( ( ps -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $=
    wph wps wa wps wch wph wps simpr imim1i $.

  ${
    simpld.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  A translation of natural deduction
       rule ` /\ ` EL ( ` /\ ` elimination left), see ~ natded .  (Contributed
       by NM, 26-May-1993.) $)
    simpld $p |- ( ph -> ps ) $=
      wph wps wch wa wps simpld.1 wps wch simpl syl $.
  $}

  ${
    simprd.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 14-May-1993.)  A
       translation of natural deduction rule ` /\ ` ER ( ` /\ ` elimination
       right), see ~ natded .  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
    simprd $p |- ( ph -> ch ) $=
      wph wch wps wph wps wch simprd.1 ancomd simpld $.
  $}

  ${
    simprbi.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 27-May-1998.) $)
    simprbi $p |- ( ph -> ch ) $=
      wph wps wch wph wps wch wa simprbi.1 biimpi simprd $.
  $}

  ${
    simplbi.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 27-May-1998.) $)
    simplbi $p |- ( ph -> ps ) $=
      wph wps wch wph wps wch wa simplbi.1 biimpi simpld $.
  $}

  ${
    pm3.26bda.1 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 22-Oct-2007.) $)
    simprbda $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wa wch wth wph wps wch wth wa pm3.26bda.1 biimpa simpld $.

    $( Deduction eliminating a conjunct.  (Contributed by NM, 22-Oct-2007.) $)
    simplbda $p |- ( ( ph /\ ps ) -> th ) $=
      wph wps wa wch wth wph wps wch wth wa pm3.26bda.1 biimpa simprd $.
  $}

  ${
    simplbi2.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by Alan Sare,
       31-Dec-2011.) $)
    simplbi2 $p |- ( ps -> ( ch -> ph ) ) $=
      wps wch wph wph wps wch wa simplbi2.1 biimpri ex $.
  $}

  $( Closed form of ~ simplbi2com .  (Contributed by Alan Sare,
     22-Jul-2012.) $)
  simplbi2comt $p |- ( ( ph <-> ( ps /\ ch ) ) -> ( ch -> ( ps -> ph ) ) ) $=
    wph wps wch wa wb wps wch wph wph wps wch wa biimpr expcomd $.

  ${
    simplbi2com.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( A deduction eliminating a conjunct, similar to ~ simplbi2 .
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof shortened by Wolf
       Lammen, 10-Nov-2012.) $)
    simplbi2com $p |- ( ch -> ( ps -> ph ) ) $=
      wps wch wph wph wps wch simplbi2com.1 simplbi2 com12 $.
  $}

  ${
    simpl2im.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    simpl2im.2 $e |- ( ch -> th ) $.
    $( Implication from an eliminated conjunct implied by the antecedent.
       (Contributed by BJ/AV, 5-Apr-2021.)  (Proof shortened by Wolf Lammen,
       26-Mar-2022.) $)
    simpl2im $p |- ( ph -> th ) $=
      wph wch wth wph wps wch simpl2im.1 simprd simpl2im.2 syl $.
  $}

  ${
    simplbiim.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    simplbiim.2 $e |- ( ch -> th ) $.
    $( Implication from an eliminated conjunct equivalent to the antecedent.
       (Contributed by Jonathan Ben-Naim, 3-Jun-2011.)  (Proof shortened by
       Wolf Lammen, 26-Mar-2022.) $)
    simplbiim $p |- ( ph -> th ) $=
      wph wch wth wph wps wch simplbiim.1 simprbi simplbiim.2 syl $.
  $}

  ${
    impel.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impel.2 $e |- ( th -> ps ) $.
    $( An inference for implication elimination.  (Contributed by Giovanni
       Mascellani, 23-May-2019.)  (Proof shortened by Wolf Lammen,
       2-Sep-2020.) $)
    impel $p |- ( ( ph /\ th ) -> ch ) $=
      wph wth wch wth wps wph wch impel.2 impel.1 syl5 imp $.
  $}

  ${
    mpan9.1 $e |- ( ph -> ps ) $.
    mpan9.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( Modus ponens conjoining dissimilar antecedents.  (Contributed by NM,
       1-Feb-2008.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    mpan9 $p |- ( ( ph /\ ch ) -> th ) $=
      wch wph wth wph wps wch wth mpan9.1 mpan9.2 syl5 impcom $.
  $}

  ${
    sylan9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan9.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 14-May-1993.)  (Proof shortened by Andrew Salmon,
       7-May-2011.) $)
    sylan9 $p |- ( ( ph /\ th ) -> ( ps -> ta ) ) $=
      wph wth wps wta wi wph wps wch wth wta sylan9.1 sylan9.2 syl9 imp $.
  $}

  ${
    sylan9r.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan9r.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 14-May-1993.) $)
    sylan9r $p |- ( ( th /\ ph ) -> ( ps -> ta ) ) $=
      wth wph wps wta wi wph wps wch wth wta sylan9r.1 sylan9r.2 syl9r imp $.
  $}

  ${
    sylan9bb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylan9bb.2 $e |- ( th -> ( ch <-> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 4-Mar-1995.) $)
    sylan9bb $p |- ( ( ph /\ th ) -> ( ps <-> ta ) ) $=
      wph wth wa wps wch wta wph wps wch wb wth sylan9bb.1 adantr wth wch wta
      wb wph sylan9bb.2 adantl bitrd $.
  $}

  ${
    sylan9bbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylan9bbr.2 $e |- ( th -> ( ch <-> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 4-Mar-1995.) $)
    sylan9bbr $p |- ( ( th /\ ph ) -> ( ps <-> ta ) ) $=
      wph wth wps wta wb wph wps wch wth wta sylan9bbr.1 sylan9bbr.2 sylan9bb
      ancoms $.
  $}

  ${
    jca.1 $e |- ( ph -> ps ) $.
    jca.2 $e |- ( ph -> ch ) $.
    $( Deduce conjunction of the consequents of two implications ("join
       consequents with 'and'").  Deduction form of ~ pm3.2 and ~ pm3.2i .  Its
       associated deduction is ~ jcad .  Equivalent to the natural deduction
       rule ` /\ ` I ( ` /\ ` introduction), see ~ natded .  (Contributed by
       NM, 3-Jan-1993.)  (Proof shortened by Wolf Lammen, 25-Oct-2012.) $)
    jca $p |- ( ph -> ( ps /\ ch ) ) $=
      wph wps wch wps wch wa jca.1 jca.2 wps wch pm3.2 sylc $.
  $}

  ${
    jcad.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jcad.2 $e |- ( ph -> ( ps -> th ) ) $.
    $( Deduction conjoining the consequents of two implications.  Deduction
       form of ~ jca and double deduction form of ~ pm3.2 and ~ pm3.2i .
       (Contributed by NM, 15-Jul-1993.)  (Proof shortened by Wolf Lammen,
       23-Jul-2013.) $)
    jcad $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      wph wps wch wth wch wth wa jcad.1 jcad.2 wch wth pm3.2 syl6c $.
  $}

  ${
    jca2.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jca2.2 $e |- ( ps -> th ) $.
    $( Inference conjoining the consequents of two implications.  (Contributed
       by Rodolfo Medina, 12-Oct-2010.) $)
    jca2 $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      wph wps wch wth jca2.1 wps wth wi wph jca2.2 a1i jcad $.
  $}

  ${
    jca31.1 $e |- ( ph -> ps ) $.
    jca31.2 $e |- ( ph -> ch ) $.
    jca31.3 $e |- ( ph -> th ) $.
    $( Join three consequents.  (Contributed by Jeff Hankins, 1-Aug-2009.) $)
    jca31 $p |- ( ph -> ( ( ps /\ ch ) /\ th ) ) $=
      wph wps wch wa wth wph wps wch jca31.1 jca31.2 jca jca31.3 jca $.

    $( Join three consequents.  (Contributed by FL, 1-Aug-2009.) $)
    jca32 $p |- ( ph -> ( ps /\ ( ch /\ th ) ) ) $=
      wph wps wch wth wa jca31.1 wph wch wth jca31.2 jca31.3 jca jca $.
  $}

  ${
    jcai.1 $e |- ( ph -> ps ) $.
    jcai.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction replacing implication with conjunction.  (Contributed by NM,
       15-Jul-1993.) $)
    jcai $p |- ( ph -> ( ps /\ ch ) ) $=
      wph wps wch jcai.1 wph wps wch jcai.1 jcai.2 mpd jca $.
  $}

  $( Distributive law for implication over conjunction.  Compare Theorem *4.76
     of [WhiteheadRussell] p. 121.  (Contributed by NM, 3-Apr-1994.)  (Proof
     shortened by Wolf Lammen, 27-Nov-2013.) $)
  jcab $p |- ( ( ph -> ( ps /\ ch ) )
      <-> ( ( ph -> ps ) /\ ( ph -> ch ) ) ) $=
    wph wps wch wa wi wph wps wi wph wch wi wa wph wps wch wa wi wph wps wi wph
    wch wi wps wch wa wps wph wps wch simpl imim2i wps wch wa wch wph wps wch
    simpr imim2i jca wph wps wch pm3.43 impbii $.

  $( Theorem *4.76 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.76 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) <->
                ( ph -> ( ps /\ ch ) ) ) $=
    wph wps wch wa wi wph wps wi wph wch wi wa wph wps wch jcab bicomi $.

  ${
    jctil.1 $e |- ( ph -> ps ) $.
    jctil.2 $e |- ch $.
    $( Inference conjoining a theorem to left of consequent in an implication.
       (Contributed by NM, 31-Dec-1993.) $)
    jctil $p |- ( ph -> ( ch /\ ps ) ) $=
      wph wch wps wch wph jctil.2 a1i jctil.1 jca $.

    $( Inference conjoining a theorem to right of consequent in an implication.
       (Contributed by NM, 31-Dec-1993.) $)
    jctir $p |- ( ph -> ( ps /\ ch ) ) $=
      wph wps wch jctil.1 wch wph jctil.2 a1i jca $.
  $}

  ${
    jccir.1 $e |- ( ph -> ps ) $.
    jccir.2 $e |- ( ps -> ch ) $.
    $( Inference conjoining a consequent of a consequent to the right of the
       consequent in an implication.  See also ~ ex-natded5.3i .  (Contributed
       by Mario Carneiro, 9-Feb-2017.)  (Revised by AV, 20-Aug-2019.) $)
    jccir $p |- ( ph -> ( ps /\ ch ) ) $=
      wph wps wch jccir.1 wph wps wch jccir.1 jccir.2 syl jca $.

    $( Inference conjoining a consequent of a consequent to the left of the
       consequent in an implication.  Remark:  One can also prove this theorem
       using ~ syl and ~ jca (as done in ~ jccir ), which would be 4 bytes
       shorter, but one step longer than the current proof.
       (Proof modification is discouraged.)  (Contributed by AV,
       20-Aug-2019.) $)
    jccil $p |- ( ph -> ( ch /\ ps ) ) $=
      wph wps wch wph wps wch jccir.1 jccir.2 jccir ancomd $.
  $}

  ${
    jctl.1 $e |- ps $.
    $( Inference conjoining a theorem to the left of a consequent.
       (Contributed by NM, 31-Dec-1993.)  (Proof shortened by Wolf Lammen,
       24-Oct-2012.) $)
    jctl $p |- ( ph -> ( ps /\ ph ) ) $=
      wph wph wps wph id jctl.1 jctil $.

    $( Inference conjoining a theorem to the right of a consequent.
       (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Wolf Lammen,
       24-Oct-2012.) $)
    jctr $p |- ( ph -> ( ph /\ ps ) ) $=
      wph wph wps wph id jctl.1 jctir $.
  $}

  ${
    jctild.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jctild.2 $e |- ( ph -> th ) $.
    $( Deduction conjoining a theorem to left of consequent in an implication.
       (Contributed by NM, 21-Apr-2005.) $)
    jctild $p |- ( ph -> ( ps -> ( th /\ ch ) ) ) $=
      wph wps wth wch wph wth wps jctild.2 a1d jctild.1 jcad $.
  $}

  ${
    jctird.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jctird.2 $e |- ( ph -> th ) $.
    $( Deduction conjoining a theorem to right of consequent in an implication.
       (Contributed by NM, 21-Apr-2005.) $)
    jctird $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      wph wps wch wth jctird.1 wph wth wps jctird.2 a1d jcad $.
  $}

  $( Introduction of antecedent as conjunct.  Theorem *4.73 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 30-Mar-1994.) $)
  iba $p |- ( ph -> ( ps <-> ( ps /\ ph ) ) ) $=
    wph wps wps wph wa wph wps pm3.21 wps wph simpl impbid1 $.

  $( Introduction of antecedent as conjunct.  (Contributed by NM,
     5-Dec-1995.) $)
  ibar $p |- ( ph -> ( ps <-> ( ph /\ ps ) ) ) $=
    wph wps wph wps wph wps iba biancomd $.

  ${
    biantru.1 $e |- ph $.
    $( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       26-May-1993.) $)
    biantru $p |- ( ps <-> ( ps /\ ph ) ) $=
      wph wps wps wph wa wb biantru.1 wph wps iba ax-mp $.
  $}

  ${
    biantrur.1 $e |- ph $.
    $( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       3-Aug-1994.) $)
    biantrur $p |- ( ps <-> ( ph /\ ps ) ) $=
      wps wph wps wph wps biantrur.1 biantru biancomi $.
  $}

  ${
    biantrud.1 $e |- ( ph -> ps ) $.
    $( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       2-Aug-1994.)  (Proof shortened by Wolf Lammen, 23-Oct-2013.) $)
    biantrud $p |- ( ph -> ( ch <-> ( ch /\ ps ) ) ) $=
      wph wps wch wch wps wa wb biantrud.1 wps wch iba syl $.

    $( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       1-May-1995.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    biantrurd $p |- ( ph -> ( ch <-> ( ps /\ ch ) ) ) $=
      wph wps wch wps wch wa wb biantrud.1 wps wch ibar syl $.
  $}

  ${
    bianfi.1 $e |- -. ph $.
    $( A wff conjoined with falsehood is false.  (Contributed by NM,
       21-Jun-1993.)  (Proof shortened by Wolf Lammen, 26-Nov-2012.) $)
    bianfi $p |- ( ph <-> ( ps /\ ph ) ) $=
      wph wps wph wa bianfi.1 wph wps bianfi.1 intnan 2false $.
  $}

  ${
    bianfd.1 $e |- ( ph -> -. ps ) $.
    $( A wff conjoined with falsehood is false.  (Contributed by NM,
       27-Mar-1995.)  (Proof shortened by Wolf Lammen, 5-Nov-2013.) $)
    bianfd $p |- ( ph -> ( ps <-> ( ps /\ ch ) ) ) $=
      wph wps wps wch wa bianfd.1 wph wps wch bianfd.1 intnanrd 2falsed $.
  $}

  ${
    baib.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Move conjunction outside of biconditional.  (Contributed by NM,
       13-May-1999.) $)
    baib $p |- ( ps -> ( ph <-> ch ) ) $=
      wps wph wps wch wa wch baib.1 wps wch ibar bitr4id $.

    $( Move conjunction outside of biconditional.  (Contributed by NM,
       11-Jul-1994.) $)
    baibr $p |- ( ps -> ( ch <-> ph ) ) $=
      wps wph wch wph wps wch baib.1 baib bicomd $.

    $( Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.)  (Proof shortened by Wolf Lammen,
       19-Jan-2020.) $)
    rbaibr $p |- ( ch -> ( ps <-> ph ) ) $=
      wph wch wps wph wch wps baib.1 biancomi baibr $.

    $( Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.)  (Proof shortened by Wolf Lammen,
       19-Jan-2020.) $)
    rbaib $p |- ( ch -> ( ph <-> ps ) ) $=
      wch wps wph wph wps wch baib.1 rbaibr bicomd $.
  $}

  ${
    baibd.1 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)
    baibd $p |- ( ( ph /\ ch ) -> ( ps <-> th ) ) $=
      wph wps wch wth wa wch wth baibd.1 wch wth wch wth wa wch wth ibar bicomd
      sylan9bb $.

    $( Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)
    rbaibd $p |- ( ( ph /\ th ) -> ( ps <-> ch ) ) $=
      wph wps wth wch wph wps wth wch baibd.1 biancomd baibd $.
  $}

  ${
    bianabs.1 $e |- ( ph -> ( ps <-> ( ph /\ ch ) ) ) $.
    $( Absorb a hypothesis into the second member of a biconditional.
       (Contributed by FL, 15-Feb-2007.) $)
    bianabs $p |- ( ph -> ( ps <-> ch ) ) $=
      wph wps wph wch wa wch bianabs.1 wph wch ibar bitr4d $.
  $}

  $( Theorem *5.44 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.44 $p |- ( ( ph -> ps ) -> ( ( ph -> ch ) <->
                ( ph -> ( ps /\ ch ) ) ) ) $=
    wph wps wch wa wi wph wps wi wph wch wi wph wps wch jcab baibr $.

  $( Theorem *5.42 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.42 $p |- ( ( ph -> ( ps -> ch ) ) <->
                ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $=
    wph wps wch wi wps wph wch wa wi wph wch wph wch wa wps wph wch ibar imbi2d
    pm5.74i $.

  $( Conjoin antecedent to left of consequent.  (Contributed by NM,
     15-Aug-1994.) $)
  ancl $p |- ( ( ph -> ps ) -> ( ph -> ( ph /\ ps ) ) ) $=
    wph wps wph wps wa wph wps pm3.2 a2i $.

  $( Conjoin antecedent to left of consequent.  Theorem *4.7 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 25-Jul-1999.)  (Proof
     shortened by Wolf Lammen, 24-Mar-2013.) $)
  anclb $p |- ( ( ph -> ps ) <-> ( ph -> ( ph /\ ps ) ) ) $=
    wph wps wph wps wa wph wps ibar pm5.74i $.

  $( Conjoin antecedent to right of consequent.  (Contributed by NM,
     15-Aug-1994.) $)
  ancr $p |- ( ( ph -> ps ) -> ( ph -> ( ps /\ ph ) ) ) $=
    wph wps wps wph wa wph wps pm3.21 a2i $.

  $( Conjoin antecedent to right of consequent.  (Contributed by NM,
     25-Jul-1999.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
  ancrb $p |- ( ( ph -> ps ) <-> ( ph -> ( ps /\ ph ) ) ) $=
    wph wps wps wph wa wph wps iba pm5.74i $.

  ${
    ancli.1 $e |- ( ph -> ps ) $.
    $( Deduction conjoining antecedent to left of consequent.  (Contributed by
       NM, 12-Aug-1993.) $)
    ancli $p |- ( ph -> ( ph /\ ps ) ) $=
      wph wph wps wph id ancli.1 jca $.
  $}

  ${
    ancri.1 $e |- ( ph -> ps ) $.
    $( Deduction conjoining antecedent to right of consequent.  (Contributed by
       NM, 15-Aug-1994.) $)
    ancri $p |- ( ph -> ( ps /\ ph ) ) $=
      wph wps wph ancri.1 wph id jca $.
  $}

  ${
    ancld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to left of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 1-Nov-2012.) $)
    ancld $p |- ( ph -> ( ps -> ( ps /\ ch ) ) ) $=
      wph wps wps wch wph wps idd ancld.1 jcad $.
  $}

  ${
    ancrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to right of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 1-Nov-2012.) $)
    ancrd $p |- ( ph -> ( ps -> ( ch /\ ps ) ) ) $=
      wph wps wch wps ancrd.1 wph wps idd jcad $.
  $}

  ${
    impac.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Importation with conjunction in consequent.  (Contributed by NM,
       9-Aug-1994.) $)
    impac $p |- ( ( ph /\ ps ) -> ( ch /\ ps ) ) $=
      wph wps wch wps wa wph wps wch impac.1 ancrd imp $.
  $}

  $( Conjoin antecedent to left of consequent in nested implication.
     (Contributed by NM, 10-Aug-1994.)  (Proof shortened by Wolf Lammen,
     14-Jul-2013.) $)
  anc2l $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $=
    wph wps wch wi wi wph wps wph wch wa wi wi wph wps wch pm5.42 biimpi $.

  $( Conjoin antecedent to right of consequent in nested implication.
     (Contributed by NM, 15-Aug-1994.) $)
  anc2r $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ch /\ ph ) ) ) ) $=
    wph wps wch wi wps wch wph wa wi wph wch wch wph wa wps wph wch pm3.21
    imim2d a2i $.
