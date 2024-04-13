From reactive.streams Require Import stream.

CoFixpoint plusStr (s₁ s₂ : stream nat) : stream nat :=
    match s₁, s₂ with 
        str n s₁, str m s₂ => str (plus n m) (plusStr s₁ s₂)
    end.

CoFixpoint pre {A : Set} (v : A) (s : stream A) : stream A :=
    match s with 
        str a s => str v (pre a s)
    end.
    
CoFixpoint even {A : Set} (s : stream A) : stream A :=
    match s with 
        str a (str b s) => str a (even s)
    end.

CoFixpoint dup {A : Set} (s : stream A) : stream A :=
    match s with 
        str a s => str a (str a (dup s))
    end.