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

theorem mem_filter {P : Set → Prop} {a b} : b ∈ filter a P ↔ b ∈ a ∧ P b :=
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

theorem mem_image_aux_of {f : Set → Set} {a b}
  (h : ∃ c, c ∈ a ∧ f c = b) : b ∈ image_aux a f :=
exi_elim h # λ c h₁ => and_elim h₁ # λ h₂ h₃ =>
exi_elim (some_spec (ax_rep a (pred_of_fun f) (λ b h => exiu_pred_of_fun)) c h₂) #
λ d h₄ => and_elim h₄ # λ h₅ h₆ =>
eq_rec' (λ x => x ∈ image_aux a f) (eq_trans (eq_symm h₃) h₆) h₅

def image (a : Set) (f : Set → Set) : Set :=
filter (image_aux a f) # λ b => ∃ c, c ∈ a ∧ f c = b

theorem mem_image {f : Set → Set} {a b} :
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

def some_inf : Set :=
some ax_inf

theorem emp_mem_some_inf : ∅ ∈ some_inf :=
exi_elim (some_spec ax_inf) # λ d h =>
eq_rec (λ x => x ∈ some_inf) (mp empty_iff_eq_emp # and_left h) #
and_left # and_right h

theorem nempty_some_inf : nempty some_inf :=
nempty_intro ∅ emp_mem_some_inf

theorem ne_singleton_self {a} : a ≠ singleton a :=
λ h => mem_irrefl # eq_symm h (λ x => a ∈ x) mem_singleton_self

def pwset (a : Set) : Set :=
filter (some # ax_pow a) # λ b => b ⊆ a

theorem mem_pwset {a b} : b ∈ pwset a ↔ b ⊆ a :=
iff_intro
(λ h => and_right (mp (@mem_filter (λ x => x ⊆ a) _ _) h))
(λ h => mpr mem_filter # and_intro (some_spec (ax_pow a) b h) h)

theorem mem_pwset_self {a} : a ∈ pwset a :=
mpr mem_pwset subset_refl

section Conditional

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

end Conditional

section Natural_numbers

def zero : Set := ∅

instance : OfNat Set (nat_lit 0) := ⟨zero⟩

theorem empty_zero : empty 0 :=
empty_emp

theorem not_mem_zero {a} : a ∉ 0 :=
not_mem_emp

def one : Set :=
pwset 0

instance : OfNat Set (nat_lit 1) := ⟨one⟩

theorem zero_mem_one : 0 ∈ 1 :=
mem_pwset_self

theorem nempty_one : nempty 1 :=
nempty_intro 0 zero_mem_one

theorem subset_emp {a} : a ⊆ ∅ ↔ a = ∅ :=
iff_intro
(λ h => mp empty_iff_eq_emp # contra # λ h₁ => nempty_elim (mp not_empty h₁) #
  λ b h₂ => not_mem_emp # h b h₂)
(λ h => eq_rec' (λ x => x ⊆ ∅) h subset_refl)

theorem mem_one {a} : a ∈ 1 ↔ a = 0 :=
iff_intro
(λ h => mp subset_emp # mp mem_pwset h)
(λ h => eq_rec' (λ x => x ∈ 1) h zero_mem_one)

def two : Set :=
pwset 1

instance : OfNat Set (nat_lit 2) := ⟨two⟩

theorem emp_subset {a} : ∅ ⊆ a :=
λ b h => false_elim # not_mem_emp h

theorem emp_mem_pwset {a} : emp ∈ pwset a :=
mpr mem_pwset emp_subset

theorem zero_mem_two : 0 ∈ 2 :=
emp_mem_pwset

theorem one_mem_two : 1 ∈ 2 :=
mpr mem_pwset subset_refl

theorem zero_ne_one : (0 : Set) ≠ 1 :=
λ h => mem_irrefl # mpr (mp eq_iff h (λ x => 0 ∈ x)) zero_mem_one

theorem zero_ne_two : (0 : Set) ≠ 2 :=
λ h => mem_irrefl # mpr (mp eq_iff h (λ x => 0 ∈ x)) zero_mem_two

theorem one_ne_two : (1 : Set) ≠ 2 :=
λ h => mem_irrefl # mpr (mp eq_iff h (λ x => 1 ∈ x)) one_mem_two

theorem eq_iff_mem {a b} : a = b ↔ ∀ c, c ∈ a ↔ c ∈ b :=
iff_intro
(λ h c => mp eq_iff h (λ x => c ∈ x))
(λ h => ax_ext h)

theorem one_eq_singleton_zero : 1 = singleton 0 :=
mpr eq_iff_mem # λ a => iff_rec' (λ x => x ↔ a ∈ singleton 0) mem_one #
iff_rec' (λ x => a = 0 ↔ x) mem_singleton iff_refl

def subsingleton (a : Set) : Prop :=
∀ (b c : Set), b ∈ a → c ∈ a → b = c

theorem subsingleton_emp : subsingleton ∅ :=
λ b c h => false_elim # not_mem_emp h

theorem subsingleton_singleton {a} : subsingleton (singleton a) :=
λ b c h₁ h₂ => eq_trans (mp mem_singleton h₁) (eq_symm # mp mem_singleton h₂)

theorem subsingleton_zero : subsingleton 0 :=
subsingleton_emp

theorem subsingleton_one : subsingleton 1 :=
eq_rec' subsingleton one_eq_singleton_zero subsingleton_singleton

theorem subsingleton_iff {a} : subsingleton a ↔ a = ∅ ∨ ∃ b, a = singleton b :=
iff_intro
(λ h => by_cases (empty a)
  (λ h₁ => or_inl # mp empty_iff_eq_emp h₁)
  (λ h₁ => or_inr # nempty_elim (mp not_empty h₁) # λ b h₂ => exi_intro b #
    mpr eq_iff_mem # λ c => iff_rec' (λ x => c ∈ a ↔ x) mem_singleton # iff_intro
      (λ h₃ => h c b h₃ h₂) (λ h₃ => eq_rec' (λ x => x ∈ a) h₃ h₂)))
(λ h => or_elim h
  (λ h₁ => eq_rec' subsingleton h₁ subsingleton_emp)
  (λ h₁ => exi_elim h₁ # λ b h₂ => eq_rec' subsingleton h₂ subsingleton_singleton))

theorem subsingleton_elim (P : Set → Prop) {a}
  (h₁ : subsingleton a) (h₂ : P ∅) (h₃ : ∀ b, P (singleton b)) : P a :=
or_elim (mp subsingleton_iff h₁)
(λ h₄ => eq_rec' P h₄ h₂)
(λ h₄ => exi_elim h₄ # λ b h₅ => eq_rec' P h₅ # h₃ b)

theorem subset_singleton {a b} : b ⊆ singleton a ↔ b = ∅ ∨ b = singleton a :=
iff_intro
(λ h => by_cases (empty b)
  (λ h₂ => or_inl # mp empty_iff_eq_emp h₂)
  (λ h₂ => or_inr # nempty_elim (mp not_empty h₂) # λ c h₃ => mpr eq_iff_mem # λ d =>
    iff_intro (h d) # λ h₄ => eq_rec' (λ x => x ∈ b) (mp mem_singleton h₄) #
      eq_rec' (λ x => x ∈ b) (eq_symm # mp mem_singleton # h c h₃) h₃))
(λ h => or_elim h
  (λ h₁ => eq_rec' (λ x => x ⊆ singleton a) h₁ emp_subset)
  (λ h₁ => eq_rec' (λ x => x ⊆ singleton a) h₁ subset_refl))

theorem subset_of_subsingleton {a b} (h : subsingleton a) : b ⊆ a ↔ b = ∅ ∨ b = a :=
iff_intro
(λ h₁ => subsingleton_elim (λ x => b ⊆ x → b = ∅ ∨ b = x) h
  (λ h₂ => or_inl # mp subset_emp h₂) (λ c h₂ => mp subset_singleton h₂) h₁)
(λ h₁ => or_elim h₁
  (λ h₂ => eq_rec' (λ x => x ⊆ a) h₂ emp_subset)
  (λ h₂ => eq_rec' (λ x => x ⊆ a) h₂ subset_refl))

theorem mem_pwset_of_subsingleton {a b} (h : subsingleton a) :
  b ∈ pwset a ↔ b = ∅ ∨ b = a :=
iff_rec' (λ x => x ↔ b = ∅ ∨ b = a) mem_pwset # subset_of_subsingleton h

theorem mem_two {a} : a ∈ 2 ↔ a = 0 ∨ a = 1 :=
mem_pwset_of_subsingleton subsingleton_one

end Natural_numbers

section Unordered_pair

def upair (a b : Set) : Set :=
image some_inf # λ c => ite (empty c) a b

theorem empty_elim (P : Set → Prop) {a} (h₁ : empty a) (h₂ : P ∅) : P a :=
eq_rec' P (mp empty_iff_eq_emp h₁) h₂

theorem nempty_upair {a b : Set} : nempty (upair a b) :=
mpr nempty_image # nempty_some_inf

theorem zero_mem_some_inf : 0 ∈ some_inf :=
emp_mem_some_inf

theorem is_succ_one_zero : is_succ 1 0 :=
λ a => iff_intro (λ h => or_inr # mp mem_one h)
(λ h => or_elim h (λ h₁ => false_elim # not_mem_zero h₁) (mpr mem_one))

theorem one_mem_some_inf : 1 ∈ some_inf :=
exi_elim (some_spec ax_inf) # λ a h => and_right (and_right h) 0
zero_mem_some_inf 1 is_succ_one_zero

theorem mem_upair {a b c} : c ∈ upair a b ↔ c = a ∨ c = b :=
iff_intro
(λ h => exi_elim (mp mem_image h) # λ d h₁ => split_ifs (λ x => x = c → c = a ∨ c = b)
  (λ h₂ h₃ => or_inl # eq_symm h₃) (λ h₂ h₃ => or_inr # eq_symm h₃) # and_right h₁)
(λ h => mpr mem_image # or_elim h
  (λ h₁ => exi_intro ∅ # and_intro emp_mem_some_inf #
    eq_trans (if_pos empty_emp) (eq_symm h₁))
  (λ h₁ => exi_intro 1 # and_intro one_mem_some_inf #
    eq_rec' (λ x => ite (empty 1) a b = x) h₁ # if_neg # mpr not_empty nempty_one))

end Unordered_pair

theorem ne_pwset_self {a} : a ≠ pwset a :=
λ h => @mem_irrefl a # mpr (mp eq_iff_mem h a) mem_pwset_self