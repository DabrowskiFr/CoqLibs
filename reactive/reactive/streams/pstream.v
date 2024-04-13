From Coq.Setoids Require Import Setoid.
From reactive.utils Require Import Notations.
From reactive.utils Require Import Functor.
From reactive.utils Require Import Algebra.

Declare Scope stream_scope.
Open Scope type_scope.
(** * Streams *)
(** Streams for a coalgebra *)

Section PStream.

    CoInductive pstream (A : Type) : Type := 
        | bot : pstream A
        | pstr : A -> pstream A -> pstream A.

    Global Arguments pstr {A}.
End PStream.