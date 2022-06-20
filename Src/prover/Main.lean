import Src.Prover.Set

namespace prover
noncomputable section

theorem empty_intro {a} (h : ∀ b, b ∉ a) : empty a :=
λ h₁ => exi_elim h₁ # λ b h₂ => h b h₂

theorem not_mem_of_empty {a b} (h : empty a) : b ∉ a :=
λ h₁ => h # exi_intro b h₁

theorem empty_iff {a} : empty a ↔ ∀ b, b ∉ a :=
iff_intro (λ h _ => not_mem_of_empty h) (λ h h₁ => exi_elim h₁ h)

theorem nonempty_intro {a} b (h : b ∈ a) : nonempty a :=
not_not_intro # exi_intro b h

theorem nonempty_elim {P : Prop} {a} (h₁ : nonempty a) (h₂ : ∀ b, b ∈ a → P) : P :=
exi_elim (not_not_elim h₁) h₂

theorem nonempty_iff {a} : nonempty a ↔ ∃ b, b ∈ a :=
iff_intro not_not_elim not_not_intro

theorem exi_empty : ∃ a, empty a :=
exi_elim ax_inf # λ a h₁ => exi_elim h₁ # λ b h₂ => exi_intro b # and_left h₂

def emp : Set :=
some exi_empty

notation (priority := high) "∅" => emp

theorem empty_emp : empty ∅ :=
some_spec exi_empty

theorem exi_nonempty : ∃ a, nonempty a :=
exi_elim ax_inf # λ a h₁ => exi_elim h₁ # λ b h₂ => exi_intro a #
nonempty_intro b # and_left # and_right h₂

def spec (a : Set) (P : Set → Prop) : Set :=
some # ax_spec a P

theorem mem_spec {a b} {P : Set → Prop} : b ∈ spec a P ↔ b ∈ a ∧ P b :=
some_spec (ax_spec a P) b

def fun_to_pred {α β : Type} (f : α → β) (x : α) (y : β) : Prop :=
f x = y

theorem fun_to_pred_iff {α β : Type} {f : α → β} {x : α} {y : β} :
  fun_to_pred f x y ↔ f x = y :=
iff_refl

theorem exiu_fun_to_pred {α β : Type} {f : α → β} {x : α} :
  ∃! (y : β), fun_to_pred f x y :=
exiu_intro (f x) rfl # λ y h => eq_symm h

def image_aux (a : Set) (f : Set → Set) : Set :=
some # ax_rep a (fun_to_pred f) # λ b h => exiu_fun_to_pred

theorem mem_image_aux_of {a b : Set} {f : Set → Set}
  (h : ∃ c, c ∈ a ∧ f c = b) : b ∈ image_aux a f :=
sorry

#exit

def image (a : Set) (f : Set → Set) : Set :=
spec (image_aux a f) # λ b => ∃ c, c ∈ a ∧ f c = b

theorem mem_image {a b : Set} {f : Set → Set} :
  b ∈ image a f ↔ ∃ c, c ∈ a ∧ f c = b :=
iff_intro
(λ h => and_right # mp mem_spec h)
(λ h => mpr mem_spec # and_intro _ h)

#exit

theorem mem_irrefl {a} : a ∉ a :=
_