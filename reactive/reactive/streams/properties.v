From reactive.streams Require Import stream.


Definition safety_prop {A : Type} (p : stream A -> Prop) := True.

Definition liveness_prop {A : Type} (p : stream A -> Prop) := True.

(* Safety property can be proved on finite prefix *)
(* How to relate the property over finite prefixes (list) and streams *)