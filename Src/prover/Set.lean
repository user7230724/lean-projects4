import Src.Prover.Logic

namespace test

-- Set

constant Set : Type
constant mem : Set → Set → Prop

infix:50 (priority := high) " ∈ " => mem

-- Definitions

def not_mem (a b : Set) : Prop :=
¬a ∈ b

infix:50 (priority := high) " ∉ " => not_mem

def empty (a : Set) : Prop :=
¬∃ (b : Set), b ∈ a

def nonempty (a : Set) : Prop :=
¬empty a

-- Axioms

axiom ax_ext {a b} : (∀ c, c ∈ a ↔ c ∈ b) → a = b
axiom ax_reg {a} : nonempty a → ∃ b, b ∈ a ∧ ¬∃ c, c ∈ b ∧ c ∈ a
axiom ax_spec (P : Set → Prop) a : ∃ b, ∀ c, c ∈ b ↔ c ∈ a ∧ P c
axiom ax_union a : ∃ b, ∀ c d, (d ∈ c ∧ c ∈ a) → d ∈ b
-- axiom ax_rep (P : Set → Set → Prop) {a} :

-- Theorems

-----

end test