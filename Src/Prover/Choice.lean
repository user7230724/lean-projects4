import Src.Prover.Logic

namespace prover
noncomputable section

axiom some {α : Type} [Inhabited α] (P : α → Prop) : α
axiom some_spec {α : Type} [Inhabited α] {P : α → Prop}
  (h : ∃ (x : α), P x) : P (some P)

def someu {α : Type} [Inhabited α] (P : α → Prop) : α :=
some # λ a => P a ∧ ∀ b, P b → b = a

def some' {α : Type} [Inhabited α] {P : α → Prop} (h : ∃ (x : α), P x) : α :=
some P

def someu' {α : Type} [Inhabited α] {P : α → Prop} (h : ∃! (x : α), P x) : α :=
someu P

theorem someu_spec {α : Type} [Inhabited α] {P : α → Prop}
  (h : ∃! (x : α), P x) : P (someu P) :=
and_left # !some_spec # mp exiu_iff h

section Conditional

theorem exi_ite_val {α : Type} (P : Prop) (x y : α) :
  ∃ (z : α), (P → z = x) ∧ (¬P → z = y) :=
prop_rec (λ m => ∃ (z : α), (m → z = x) ∧ (¬m → z = y))
(exi_intro x # and_intro (λ _ => rfl) (λ h => exfalso # h trivial))
(exi_intro y # and_intro exfalso (λ _ => rfl))

def ite {α : Type} [Inhabited α] (P : Prop) (x y : α) : α :=
some' # exi_ite_val P x y

theorem if_pos {α : Type} [Inhabited α] {P : Prop} {x y : α} (h : P) : ite P x y = x :=
and_left (!some_spec # exi_ite_val P x y) h

theorem if_neg {α : Type} [Inhabited α] {P : Prop} {x y : α} (h : ¬P) : ite P x y = y :=
and_right (!some_spec # exi_ite_val P x y) h

theorem split_ifs {α : Type} [Inhabited α] (F : α → Prop) {P : Prop} {x y : α}
  (h₁ : P → F x) (h₂ : ¬P → F y) : F (ite P x y) :=
or_elim (@em P)
(λ h₃ => eq_rec' F (if_pos h₃) # h₁ h₃)
(λ h₃ => eq_rec' F (if_neg h₃) # h₂ h₃)

end Conditional