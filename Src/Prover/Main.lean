import Src.Prover.Set

namespace prover
noncomputable section

theorem empty_intro {a} (h : ∀ b, b ∉ a) : empty a :=
λ h₁ => exi_elim h₁ # λ b h₂ => h b h₂

theorem not_mem_of_empty {a b} (h : empty a) : b ∉ a :=
λ h₁ => h # exi_intro b h₁

theorem empty_iff {a} : empty a ↔ ∀ b, b ∉ a :=
iff_intro (λ h _ => not_mem_of_empty h) (λ h h₁ => exi_elim h₁ h)

theorem nempty_intro {a} b (h : b ∈ a) : nempty a :=
not_not_intro # exi_intro b h

theorem nempty_elim {P : Prop} {a} (h₁ : nempty a) (h₂ : ∀ b, b ∈ a → P) : P :=
exi_elim (not_not_elim h₁) h₂

theorem nempty_iff {a} : nempty a ↔ ∃ b, b ∈ a :=
iff_intro not_not_elim not_not_intro

theorem exi_empty : ∃ a, empty a :=
exi_elim ax_inf # λ a h₁ => exi_elim h₁ # λ b h₂ => exi_intro b # and_left h₂

def emp : Set :=
some exi_empty

notation (priority := high) "∅" => emp

theorem empty_emp : empty ∅ :=
some_spec exi_empty

theorem exi_nempty : ∃ a, nempty a :=
exi_elim ax_inf # λ a h₁ => exi_elim h₁ # λ b h₂ => exi_intro a #
nempty_intro b # and_left # and_right h₂

def filter (a : Set) (P : Set → Prop) : Set :=
some # ax_spec a P

theorem mem_filter {a b} {P : Set → Prop} : b ∈ filter a P ↔ b ∈ a ∧ P b :=
some_spec (ax_spec a P) b

def pred_of_fun {α β : Type} (f : α → β) (x : α) (y : β) : Prop :=
f x = y

theorem pred_of_fun_iff {α β : Type} {f : α → β} {x : α} {y : β} :
  pred_of_fun f x y ↔ f x = y :=
iff_refl

theorem exiu_pred_of_fun {α β : Type} {f : α → β} {x : α} :
  ∃! (y : β), pred_of_fun f x y :=
exiu_intro (f x) rfl # λ y h => eq_symm h

def image_aux (a : Set) (f : Set → Set) : Set :=
some # ax_rep a (pred_of_fun f) # λ b h => exiu_pred_of_fun

theorem mem_image_aux_of {a b : Set} {f : Set → Set}
  (h : ∃ c, c ∈ a ∧ f c = b) : b ∈ image_aux a f :=
exi_elim h # λ c h₁ => and_elim h₁ # λ h₂ h₃ =>
exi_elim (some_spec (ax_rep a (pred_of_fun f) (λ b h => exiu_pred_of_fun)) c h₂) #
λ d h₄ => and_elim h₄ # λ h₅ h₆ =>
eq_rec' (λ x => x ∈ image_aux a f) (eq_trans (eq_symm h₃) h₆) h₅

def image (a : Set) (f : Set → Set) : Set :=
filter (image_aux a f) # λ b => ∃ c, c ∈ a ∧ f c = b

theorem mem_image {a b : Set} {f : Set → Set} :
  b ∈ image a f ↔ ∃ c, c ∈ a ∧ f c = b :=
iff_intro
(λ h => and_right # mp mem_filter h)
(λ h => mpr mem_filter # and_intro (mem_image_aux_of h) h)

def singleton (a : Set) : Set :=
image (some exi_nempty) # λ b => a

theorem mem_singleton {a b} : b ∈ singleton a ↔ b = a :=
iff_intro
(λ h => exi_elim (mp mem_image h) # λ c h₁ => eq_symm # and_right h₁)
(λ h => mpr mem_image # exi_elim (mp nempty_iff # some_spec exi_nempty) #
  λ c h₁ => exi_intro c # and_intro h₁ # eq_symm h)

theorem mem_singleton_self {a} : a ∈ singleton a :=
mpr mem_singleton rfl

theorem nempty_singleton {a} : nempty (singleton a) :=
nempty_intro a mem_singleton_self

theorem mem_irrefl {a} : a ∉ a :=
exi_elim (ax_reg nempty_singleton) # λ b h => and_elim h # λ h₁ h₂ h₃ => h₂ #
exi_intro a # and_intro (eq_rec' (λ x => a ∈ x) (mp mem_singleton h₁) h₃)
mem_singleton_self

-- Conditional

theorem exi_ite_val {α : Type} (P : Prop) (x y : α) :
  ∃ (z : α), (P → z = x) ∧ (¬P → z = y) :=
prop_rec (λ m => ∃ (z : α), (m → z = x) ∧ (¬m → z = y))
(exi_intro x # and_intro (λ _ => rfl) (λ h => false_elim # h trivial))
(exi_intro y # and_intro false_elim (λ _ => rfl))

def ite {α : Type} (P : Prop) (x y : α) : α :=
some # exi_ite_val P x y

theorem if_pos {α : Type} {P : Prop} {x y : α} (h : P) : ite P x y = x :=
and_left (some_spec # exi_ite_val P x y) h

theorem if_neg {α : Type} {P : Prop} {x y : α} (h : ¬P) : ite P x y = y :=
and_right (some_spec # exi_ite_val P x y) h

theorem split_ifs {α : Type} (F : α → Prop) {P : Prop} {x y : α}
  (h₁ : P → F x) (h₂ : ¬P → F y) : F (ite P x y) :=
or_elim (@em P)
(λ h₃ => eq_rec' F (if_pos h₃) # h₁ h₃)
(λ h₃ => eq_rec' F (if_neg h₃) # h₂ h₃)

-- Unordered pair

def upair (a b : Set) : Set :=
image (some ax_inf) # λ c => ite (empty c) a b

theorem nempty_image {a} {f : Set → Set} : nempty (image a f) ↔ nempty a :=
iff_intro
(λ h => nempty_elim h # λ b h₁ => exi_elim (mp mem_image h₁) #
  λ c h₂ => nempty_intro c # and_left h₂)
(λ h => nempty_elim h # λ b h₁ => nempty_intro (f b) # mpr mem_image #
  exi_intro b # and_intro h₁ rfl)

theorem not_mem_emp {a} : a ∉ ∅ :=
not_mem_of_empty empty_emp

theorem empty_iff_eq_emp {a} : empty a ↔ a = ∅ :=
iff_intro
(λ h => ax_ext # λ b => iff_intro
  (λ h₁ => false_elim # not_mem_of_empty h h₁) (λ h₁ => false_elim # not_mem_emp h₁))
(λ h => eq_rec' empty h empty_emp)

theorem empty_elim (P : Set → Prop) {a} (h₁ : empty a) (h₂ : P ∅) : P a :=
eq_rec' P (mp empty_iff_eq_emp h₁) h₂

theorem nempty_upair {a b : Set} : nempty (upair a b) :=
mpr nempty_image # nempty_intro ∅ # exi_elim (some_spec ax_inf) # λ c h =>
eq_rec (λ x => x ∈ some ax_inf) (mp empty_iff_eq_emp # and_left h) #
and_left # and_right h