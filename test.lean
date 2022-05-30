constant F : Nat → Prop

axiom h₁ : F 1
axiom h₂ : ∀ (P : Prop), F 0 → P
axiom h₃ : ∀ (P : Nat → Prop) (n : Nat), F n → P 1 → P n

def f : Nat → Nat
| (n + 2) => 0
| _ => 1

example {P : Prop} {n : Nat} (h : F (n + 2)) : P :=
h₂ P (h₃ (λ x => F (f x)) (n + 2) h h₁)

example {P : Prop} {n : Nat} (h : F (n + 2)) : P :=
h₂ P (id h₃ (λ x => F (f x)) (n + 2) h h₁)