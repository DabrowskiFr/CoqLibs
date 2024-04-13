# Temporal properties for reactive programs

## Reactive programs 

## Streams 

    - partial streams 
        - keep the same yampa term 
        - change the eval function to map bot to bot 
            - synchronous function, length preserving 

### Functions over streams 
    - Domain theory
    - Expressivity of functions / stream functions / yampa

### Subset of reasonnable functions, 
    - monotonicity, continuity, reactivity, productivity

## YAMPA 
    - Iterator, each yampa construct can be expressed as an iterator
    - Transformation as iterators as equivalence 
        function for bisimilarity
        define an equivalence relation based on transforming into
        iterators, prove it implies bisimulation
    -   This co-iterative semantics interprets a stream as a process made of an initial state and a step function.
    - Arrows, category
    - Expressive power

### Bisimulation 
    based on the fact that the two elements can produce
    the same sequence of i/o 
    un processus est déterministe mais pour un état plusieurs
    transitions possibles en fonction de l'entrée.

### Properties 
- liveness, infinite to finite, invariant

# Other 
-Monad, MSF, category

Deux traces bisimilaire vérifie les mêmes formules LTL


Bisimulation YAMPA

see functions as processes 

f : A -> B x g

Système de transition 

f -> (i,o) -> f' si f i = (o, f')


fix : 
    ecriture d'une fonction, type forall n, e
    nat -> nat 
    forall (n : nat), P 
    n doit être inductif -> Cannot do a fixpoint on a non inductive type
    P peut être coinductif 
cofix 

    n peut être inductif 
    P doit être coinductif 
        -> All methods must construct elements in coinductive types

    |   param/result    |   ind     |   coind       |
    |   ind             |   fix     |   fix/cofix   |
    |   coind           |    X      |   cofix       |

    Pour le cas X, la propriété doit être redéfinie de manière coinductive.


    Explain why we need unroll.

    Stream, destructor, constructor 
    inductive definition : constructors, generate elements
    coinductive definition : destructors, observe elements, 
    induction, on ne prend que les éléments qui correspondent
    coinduction, on prend tous les éléments qui ne contredisent pas les règles

    congruence, bisimulation equivalence (bisimulation which is an equivalenc)

    Properties 
    Functions over streams 
    Prefix 

    stream functions as processes, bisimulation 

    with process syntactical equivalence -> bisimulation 
    for stream functions ??? 


# Papers 

##### The semantics of a simple language for parallel programming, Gilles Kahn, 1974 

    - Semantics as stream functions

##### Circuits as streams in Coq Verification of a sequantial multiplier, Christine Paulin-Mohring, 1995

    - circuits as stream transformer 
##### A Co-iterative characterization of Synchronous Stream Functions, Paul Caspi, Marc Pouzet, 1998
    - Co-iteration for stream functions
    - 
