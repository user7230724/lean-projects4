import Src.Prover.Choice

namespace prover
noncomputable section

constant Set : Type
constant mem : Set → Set → Prop

infix:50 (priority := high) " ∈ " => mem

-- Definitions

def not_mem (a b : Set) : Prop :=
¬a ∈ b

infix:50 (priority := high) " ∉ " => not_mem

def empty (a : Set) : Prop :=
¬∃ b, b ∈ a

def nempty (a : Set) : Prop :=
¬empty a

def is_set_succ (n n1 : Set) : Prop :=
∀ a, a ∈ n1 ↔ a ∈ n ∨ a = n1

def subset (a b : Set) : Prop :=
∀ c, c ∈ a → c ∈ b

infix:50 (priority := high) " ⊆ " => subset

-- Axioms

axiom ax_ext {a b} : (∀ c, c ∈ a ↔ c ∈ b) → a = b
axiom ax_reg {a} : nempty a → ∃ b, b ∈ a ∧ ¬∃ c, c ∈ b ∧ c ∈ a
axiom ax_spec a (P : Set → Prop) : ∃ b, ∀ c, c ∈ b ↔ c ∈ a ∧ P c
axiom ax_union a : ∃ b, ∀ c d, (d ∈ c ∧ c ∈ a) → d ∈ b
axiom ax_rep a (P : Set → Set → Prop) : (∀ b, b ∈ a → ∃! c, P b c) →
  ∃ b, ∀ c, c ∈ a → ∃ d, d ∈ b ∧ P c d
axiom ax_inf : ∃ a b, empty b ∧ b ∈ a ∧ ∀ c, c ∈ a → ∀ d, is_set_succ c d → d ∈ a
axiom ax_pow : ∀ a, ∃ b, ∀ c, c ⊆ a → c ∈ b

-- Theorems

theorem not_empty {a} : ¬empty a ↔ nempty a :=
iff_refl

theorem not_nempty {a} : ¬nempty a ↔ empty a :=
iff_intro not_not_elim not_not_intro

theorem subset_refl {a} : a ⊆ a :=
λ _ => id

theorem subset_trans {a b c} (h₁ : a ⊆ b) (h₂ : b ⊆ c) : a ⊆ c :=
λ d h₃ => h₂ d # h₁ d h₃