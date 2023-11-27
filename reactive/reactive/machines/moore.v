From mathcomp Require Import fintype.
From reactive.streams Require Import stream.

(** Moore machine, output dependes only on state *)

Record moore (state input output : finType) : Type := {
    mo_init : state;
    mo_transfert : state -> input -> state;
    mo_output : state -> output 
}.