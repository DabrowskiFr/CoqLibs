(** Reactive machines and automata *)

From mathcomp Require Import fintype.
From reactive.streams Require Import stream.


(** Mealy machine, output dependes both on state and input *)

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



(* Pour LTL, l'alphabet est l'ensemble des propositions atomiques *)
(* mots acceptés *)





(* Définition predicat initial / type class *)



(* state,i -> o,state state,i -> o,state*)