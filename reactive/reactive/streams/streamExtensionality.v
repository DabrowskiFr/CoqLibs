From reactive.streams Require Import stream.

Axiom stream_extensionality : 
    forall A (s₁ s₂ : stream A), s₁ ∼ s₂ -> s₁ = s₂.
