From mathcomp Require Import fintype.
From reactive.streams Require Import stream.

(* Moore machine, output dependes only on state *)

(* Streams *)
(*
CoInductive stream (A : Type) :=
    str : A -> stream A -> stream A.

Arguments str [A].

Definition hd {A : Type} (s : stream A) : A :=
    match s with str a _ => a end.

Definition tl {A : Type} (s : stream A) : stream A :=
    match s with str _ s => s end.

Fixpoint nth {A : Type} (s : stream A) (n : nat) : A :=
    match n with 0 => hd s | S n => nth (tl s) n end.

CoFixpoint map {A B : Type} (f : A -> B) (s : stream A) : stream B :=
    match s with str a s => str (f a) (map f s) end.
*)
(* Moore machine *)

Record moore (state input output : finType) : Type := {
    mo_init : state;
    mo_transfert : state -> input -> state;
    mo_output : state -> output 
}.

(* Mealy machine *)

Record mealy (state input output : finType) : Type := {
    me_initial : state;
    me_transfert : state -> input -> state;
    me_output : state -> input -> output
}.

Arguments me_initial [state input output].
Arguments me_transfert [state input output].
Arguments me_output [state input output].

Definition mealy_step {state input output : finType} 
    (m : mealy state input output) 
    (s : state) (i : input) (o : output) (s' : state) :=
    me_transfert m s i = s' /\ me_output m s i = o.

(* add start symbol in mealy sequence *)

CoInductive mealy_sequence {state input output : finType}
    (m : mealy state input output) : 
    stream state -> stream input -> stream output -> Prop :=
    mealy_sequence_ : forall (s s' : stream state) (i : stream input) 
        (o : stream output),
        mealy_step m (hd s) (hd i) (hd o) (hd (tl s')) ->
        mealy_sequence m (tl s) (tl i) (tl o) ->
        mealy_sequence m s i o.

Record mealy_execution 
    (state input output : finType) 
    (m : mealy state input output) : Type := {
    me_path : stream state;    
    me_inputs : stream input;
    me_outputs : stream output;
    me_is_valid : mealy_sequence m me_path me_inputs me_outputs;
    
}.

(* Bucchi automaton *)
(* Language : infinite words *)

Record bucchi (state alphabet : finType) : Type := {
    bu_initial : state -> Prop;
    bu_transfert : state -> alphabet -> state -> Prop;
    bu_final : state -> Prop
}.

Arguments bu_initial [state alphabet].
Arguments bu_transfert [state alphabet].
Arguments bu_final [state alphabet].

CoInductive bucchi_sequence {state alphabet : finType}
    (bu : bucchi state alphabet) : state ->
    stream state -> stream alphabet -> Prop :=
    bucchi_sequence_ : forall (a b : state) 
        (s : stream state) (w : stream alphabet),
        hd s = a ->
        hd (tl s) = b ->
        bu_transfert bu a (hd w) b -> 
        bucchi_sequence bu b (tl s) (tl w) ->
        bucchi_sequence bu a s w.


(* not a path, two streams *)
Record bucchi_execution {state alphabet : finType}
    (b : bucchi state alphabet): Type := {
    bu_path : stream state;
    bu_word : stream alphabet;
    bu_is_init : bu_initial b (hd bu_path);
    bu_is_sequence : bucchi_sequence b (hd (bu_path)) bu_path bu_word;
}.

(* Kripke structure *)

(* Model Checking. Cyber Physical Systems Series. MIT Press *)
(* Clarke, Edmund M. Jr *)

(* may be identified with a Moore machine 
    with a singleton input alphabet and with the output function
    being the labelling function *)

(* atomic propositions are boolean-valued expressions formed from 
    variables, constants and predicate symbols.*)

Record kripke (state proposition : finType) : Type := {
    kr_initial : state -> Prop;
    kr_transition : state -> state -> Prop;
    kr_transition_prop : forall s : state, exists s', 
        kr_transition s s';
    kr_labelling : state -> proposition -> Prop
}.

Arguments kr_initial [state proposition].
Arguments kr_transition [state proposition].
Arguments kr_transition_prop [state proposition].
Arguments kr_labelling [state proposition].

CoInductive kripke_sequence {state alphabet : finType}
    (k : kripke state alphabet) : state -> stream state -> Prop := 
    kripke_exec_ : 
        forall s s' st,
        hd st = s -> hd (tl st) = s' ->
        kr_transition k s s' ->
        kripke_sequence k s' (tl st) ->
        kripke_sequence k s st.

Record kripke_path {state alphabet : finType} 
    (k : kripke state alphabet) :=
    {
        kr_path_path : stream state;
        kr_is_init : kr_initial k (hd kr_path_path);
        kr_path_valid : kripke_sequence k (hd kr_path_path) kr_path_path;
    }.

Coercion kr_path_path : kripke_path >-> stream.

Definition kripke_word {state alphabet : finType}
    {k : kripke state alphabet} (p : kripke_path k)
    : stream (alphabet -> Prop) :=
        map (kr_labelling k) p.

(* Pour LTL, l'alphabet est l'ensemble des propositions atomiques *)
(* mots acceptés *)





(* Définition predicat initial / type class *)



(* state,i -> o,state state,i -> o,state*)