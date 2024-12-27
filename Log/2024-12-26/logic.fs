\ -- Alfabeto: wff. Formula correcta!
01 CONSTANT wff
02 CONSTANT ->
CHAR ) CONSTANT ) \ -- Meter ')' en la pila
CHAR ( CONSTANT ( \ -- Meter '(' en la pila


\ -- Variables. Definidas con su codigo ascii  ok
CHAR p CONSTANT p  \ -- Meter 'p' en la pila
CHAR q CONSTANT q  \ -- Meter 'q' en la pila

\ -- Reglas de construccion de formulas
: wp p wff ; \ -- Construir la formula p
: wq q wff ; \ -- Construir la formula q


\ -- Imprimir un salto de linea
: nl 10 emit ;

\ -- Imprimir el siguiente simbolo de la pila
\ -- Se asume que la pila no esta vacia
: ._symbol
  CASE \ -- Segun el valor que haya en la pila
    wff OF ." wff " ENDOF \ -- Es el simbolo wff
    ->  OF ." -> " ENDOF \ -- Es el simbolo ->

    \ -- Si no es wff, imprimir el simbolo ascii
    emit space \ -- Imprimir el simbolo
    0 \ -- valor dummy para que lo elimina enccase
  ENDCASE 
;

\ -- Imprimir un simbolo desde la pila
\ -- Se comprueba si la pila esta vacia o no
: .symbol depth 0=  \ -- Pila vacia?
   IF 
     ." EMPTY! "   \ -- Si esta vacia, imprimir mensaje 
   ELSE 
     ._symbol     \ -- Si no, imprimir el simbolo 
   THEN 
;

\ -- Imprimir todos los símbolos hasta que la pila este vacia
: .symbols 
  nl \ -- Imprimir un salto de linea
  BEGIN
    depth 0= \ -- Pila vacia?
    IF
      EXIT \ -- Si esta vacia, salir del bucle
    THEN
    .symbol \ -- Imprimir el simbolo
  AGAIN
;

\ -- Consumir el símbolo wff de la pila
: wff> 
  depth 0= \ -- Pila vacia?
  IF
    ." EMPTY! "
    nl
    ."   ok "
    QUIT  \ -- Terminar
  THEN
    wff = \ -- Es el simbolo wff?
    IF
      ." wff "  \ -- Es wff, imprimirlo!
    ELSE
      ." ERROR: wff expected!" nl \ -- Si no, error
      ."  ok "
      QUIT  \ -- Terminar
    THEN  
;

\ -- Imprimir la formula que hay en la pila
: .wff
    nl
    wff> \ -- Consumir el simbolo wff
  BEGIN

    depth 0= \ -- Pila vacia?
    IF
      EXIT \ -- Si esta vacia, salir del bucle
    THEN

    dup wff = \ -- Es el simbolo wff?
    IF
      EXIT  \ -- Terminar
    THEN

    .symbol \ -- Imprimir el simbolo

    AGAIN
;

\ --- Palabras para hacer pruebas
: fi ) q -> p ( wff ; \ -- Formula wff ( p -> q )



