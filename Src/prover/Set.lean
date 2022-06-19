import Src.Prover.Logic

namespace test

-- Set

constant Set : Type
constant mem : Set → Set → Prop

infix:50 (priority := high) " ∈ " => mem

-- Definitions

-- Axioms

axiom set_ext {a b : Set} (h : ∀ (c : Set), c ∈ a ↔ c ∈ b) : a = b

-- Theorems

-----

end test