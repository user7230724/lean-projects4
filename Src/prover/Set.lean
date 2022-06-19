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
¬∃ b, b ∈ a

def nonempty (a : Set) : Prop :=
¬empty a

def is_set_succ (n n1 : Set) : Prop :=
∀ a, a ∈ n1 ↔ a ∈ n ∨ a = n1

def subset (a b : Set) : Prop :=
∀ c, c ∈ a → c ∈ b

infix:50 (priority := high) " ⊆ " => subset

-- Axioms

axiom ax_ext {a b} : (∀ c, c ∈ a ↔ c ∈ b) → a = b
axiom ax_reg {a} : nonempty a → ∃ b, b ∈ a ∧ ¬∃ c, c ∈ b ∧ c ∈ a
axiom ax_spec (P : Set → Prop) a : ∃ b, ∀ c, c ∈ b ↔ c ∈ a ∧ P c
axiom ax_union a : ∃ b, ∀ c d, (d ∈ c ∧ c ∈ a) → d ∈ b
axiom ax_rep (P : Set → Set → Prop) {a} : (∀ b, b ∈ a → ∃! c, P b c) →
  ∃ b, ∀ c, c ∈ a → ∃ d, d ∈ b ∧ P c d
axiom ax_inf : ∃ a b, empty b ∧ b ∈ a ∧ ∀ c, c ∈ a → ∀ d, is_set_succ c d → d ∈ a
axiom ax_pow : ∀ a, ∃ b, ∀ c, c ⊆ a → c ∈ b

-- Choice

axiom some {α : Type} {P : α → Prop} : (∃ (x : α), P x) → α
axiom some_spec {α : Type} {P : α → Prop} (h : ∃ (x : α), P x) : P (some h)

-- Theorems

theorem not_empty a : ¬empty a ↔ nonempty a :=
iff_refl

theorem not_nonempty a : ¬nonempty a ↔ empty a :=
iff_intro not_not_elim not_not_intro

theorem subset_refl a : a ⊆ a :=
λ _ => id

-----

end test