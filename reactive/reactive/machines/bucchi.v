From mathcomp Require Import fintype.
From reactive.streams Require Import stream.

(** Bucchi automaton *)
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
