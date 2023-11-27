From mathcomp Require Import fintype.
From reactive.streams Require Import stream.

(** Kripke structure *)

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
    (k : kripke state alphabet) : stream state -> Prop := 
    kripke_exec_ : 
        forall s s' st,
        hd st = s -> hd (tl st) = s' ->
        kr_transition k s s' ->
        kripke_sequence k (tl st) ->
        kripke_sequence k st.

Record kripke_path {state proposition : finType} 
    (k : kripke state proposition) :=
    {
        kr_path_path : stream state;
        kr_is_init : kr_initial k (hd kr_path_path);
        kr_path_valid : kripke_sequence k kr_path_path;
    }.

Coercion kr_path_path : kripke_path >-> stream.

Definition kripke_word {state proposition : finType}
    {k : kripke state proposition} (p : kripke_path k)
    : stream (proposition -> Prop) :=
        map (kr_labelling k) p.
