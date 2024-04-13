Record family (X : Type) := { 
    family_index :> Type; 
    family_element :> family_index -> X
}.