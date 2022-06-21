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
some' exi_empty

notation (priority := high) "∅" => emp

theorem empty_emp : empty ∅ :=
some_spec exi_empty

theorem exi_nonempty : ∃ a, nonempty a :=
exi_elim ax_inf # λ a h₁ => exi_elim h₁ # λ b h₂ => exi_intro a #
nonempty_intro b # and_left # and_right h₂

def filter (a : Set) (P : Set → Prop) : Set :=
some' # ax_spec a P

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
some' # ax_rep a (pred_of_fun f) # λ b h => exiu_pred_of_fun

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
image (some' exi_nonempty) # λ b => a

theorem mem_singleton {a b} : b ∈ singleton a ↔ b = a :=
iff_intro
(λ h => exi_elim (mp mem_image h) # λ c h₁ => eq_symm # and_right h₁)
(λ h => mpr mem_image # exi_elim (mp nonempty_iff # some_spec exi_nonempty) #
  λ c h₁ => exi_intro c # and_intro h₁ # eq_symm h)

theorem mem_singleton_self {a} : a ∈ singleton a :=
mpr mem_singleton rfl

theorem nonempty_singleton {a} : nonempty (singleton a) :=
nonempty_intro a mem_singleton_self

theorem mem_irrefl {a} : a ∉ a :=
exi_elim (ax_reg nonempty_singleton) # λ b h => and_elim h # λ h₁ h₂ h₃ => h₂ #
exi_intro a # and_intro (eq_rec' (λ x => a ∈ x) (mp mem_singleton h₁) h₃)
mem_singleton_self

theorem nonempty_image {a} {f : Set → Set} : nonempty (image a f) ↔ nonempty a :=
iff_intro
(λ h => nonempty_elim h # λ b h₁ => exi_elim (mp mem_image h₁) #
  λ c h₂ => nonempty_intro c # and_left h₂)
(λ h => nonempty_elim h # λ b h₁ => nonempty_intro (f b) # mpr mem_image #
  exi_intro b # and_intro h₁ rfl)

theorem not_mem_emp {a} : a ∉ ∅ :=
not_mem_of_empty empty_emp

theorem empty_iff_eq_emp {a} : empty a ↔ a = ∅ :=
iff_intro
(λ h => ax_ext # λ b => iff_intro
  (λ h₁ => exfalso # not_mem_of_empty h h₁) (λ h₁ => exfalso # not_mem_emp h₁))
(λ h => eq_rec' empty h empty_emp)

def some_inf : Set :=
some' ax_inf

theorem emp_mem_some_inf : ∅ ∈ some_inf :=
exi_elim (some_spec ax_inf) # λ d h =>
eq_rec (λ x => x ∈ some_inf) (mp empty_iff_eq_emp # and_left h) #
and_left # and_right h

theorem nonempty_some_inf : nonempty some_inf :=
nonempty_intro ∅ emp_mem_some_inf

theorem ne_singleton_self {a} : a ≠ singleton a :=
λ h => mem_irrefl # eq_symm h (λ x => a ∈ x) mem_singleton_self

def powerset (a : Set) : Set :=
filter (some' # ax_pow a) # λ b => b ⊆ a

theorem mem_powerset {a b} : b ∈ powerset a ↔ b ⊆ a :=
iff_intro
(λ h => and_right (!mp mem_filter h))
(λ h => mpr mem_filter # and_intro (some_spec (ax_pow a) b h) h)

theorem mem_powerset_self {a} : a ∈ powerset a :=
mpr mem_powerset subset_refl

theorem eq_iff_mem {a b} : a = b ↔ ∀ c, c ∈ a ↔ c ∈ b :=
iff_intro
(λ h c => mp eq_iff h (λ x => c ∈ x))
(λ h => ax_ext h)

theorem ne_powerset_self {a} : a ≠ powerset a :=
λ h => !mem_irrefl # mpr (mp eq_iff_mem h a) mem_powerset_self

section Natural_numbers

def zero : Set := ∅

instance : OfNat Set (nat_lit 0) := ⟨zero⟩

theorem empty_zero : empty 0 :=
empty_emp

theorem not_mem_zero {a} : a ∉ 0 :=
not_mem_emp

def one : Set :=
powerset 0

instance : OfNat Set (nat_lit 1) := ⟨one⟩

theorem zero_mem_one : 0 ∈ 1 :=
mem_powerset_self

theorem nonempty_one : nonempty 1 :=
nonempty_intro 0 zero_mem_one

theorem subset_emp {a} : a ⊆ ∅ ↔ a = ∅ :=
iff_intro
(λ h => mp empty_iff_eq_emp # contra # λ h₁ => nonempty_elim (mp not_empty h₁) #
  λ b h₂ => not_mem_emp # h b h₂)
(λ h => eq_rec' (λ x => x ⊆ ∅) h subset_refl)

theorem mem_one {a} : a ∈ 1 ↔ a = 0 :=
iff_intro
(λ h => mp subset_emp # mp mem_powerset h)
(λ h => eq_rec' (λ x => x ∈ 1) h zero_mem_one)

def two : Set :=
powerset 1

instance : OfNat Set (nat_lit 2) := ⟨two⟩

theorem emp_subset {a} : ∅ ⊆ a :=
λ b h => exfalso # not_mem_emp h

theorem emp_mem_powerset {a} : emp ∈ powerset a :=
mpr mem_powerset emp_subset

theorem zero_mem_two : 0 ∈ 2 :=
emp_mem_powerset

theorem one_mem_two : 1 ∈ 2 :=
mpr mem_powerset subset_refl

theorem zero_ne_one : (0 : Set) ≠ 1 :=
λ h => mem_irrefl # mpr (mp eq_iff h (λ x => 0 ∈ x)) zero_mem_one

theorem zero_ne_two : (0 : Set) ≠ 2 :=
λ h => mem_irrefl # mpr (mp eq_iff h (λ x => 0 ∈ x)) zero_mem_two

theorem one_ne_two : (1 : Set) ≠ 2 :=
λ h => mem_irrefl # mpr (mp eq_iff h (λ x => 1 ∈ x)) one_mem_two

theorem one_eq_singleton_zero : 1 = singleton 0 :=
mpr eq_iff_mem # λ a => iff_rec' (λ x => x ↔ a ∈ singleton 0) mem_one #
iff_rec' (λ x => a = 0 ↔ x) mem_singleton iff_refl

def subsingleton (a : Set) : Prop :=
∀ (b c : Set), b ∈ a → c ∈ a → b = c

theorem subsingleton_emp : subsingleton ∅ :=
λ b c h => exfalso # not_mem_emp h

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
  (λ h₁ => or_inr # nonempty_elim (mp not_empty h₁) # λ b h₂ => exi_intro b #
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
  (λ h₂ => or_inr # nonempty_elim (mp not_empty h₂) # λ c h₃ => mpr eq_iff_mem # λ d =>
    iff_intro (h d) # λ h₄ => eq_rec' (λ x => x ∈ b)
      (eq_trans (mp mem_singleton h₄) (eq_symm # mp mem_singleton # h c h₃)) h₃))
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

theorem mem_powerset_of_subsingleton {a b} (h : subsingleton a) :
  b ∈ powerset a ↔ b = ∅ ∨ b = a :=
iff_rec' (λ x => x ↔ b = ∅ ∨ b = a) mem_powerset # subset_of_subsingleton h

theorem mem_two {a} : a ∈ 2 ↔ a = 0 ∨ a = 1 :=
mem_powerset_of_subsingleton subsingleton_one

end Natural_numbers

section Unordered_pair

def upair (a b : Set) : Set :=
image some_inf # λ c => ite (empty c) a b

theorem empty_elim (P : Set → Prop) {a} (h₁ : empty a) (h₂ : P ∅) : P a :=
eq_rec' P (mp empty_iff_eq_emp h₁) h₂

theorem nonempty_upair {a b : Set} : nonempty (upair a b) :=
mpr nonempty_image # nonempty_some_inf

theorem zero_mem_some_inf : 0 ∈ some_inf :=
emp_mem_some_inf

theorem is_succ_one_zero : is_succ 1 0 :=
λ a => iff_intro (λ h => or_inr # mp mem_one h)
(λ h => or_elim h (λ h₁ => exfalso # not_mem_zero h₁) (mpr mem_one))

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
    eq_rec' (λ x => ite (empty 1) a b = x) h₁ # if_neg # mpr not_empty nonempty_one))

theorem upair_comm {a b} : upair a b = upair b a :=
mpr eq_iff_mem # λ c => iff_rec' (λ x => x ↔ _) mem_upair #
iff_rec' (λ x => _ ↔ x) mem_upair or_symm'

theorem upair_self_eq {a} : upair a a = singleton a :=
mpr eq_iff_mem # λ b => iff_rec' (λ x => x ↔ _) (iff_trans mem_upair or_self) #
iff_rec' (λ x => _ ↔ x) mem_singleton iff_refl

theorem subsingleton_upair_iff {a b} : subsingleton (upair a b) ↔ a = b :=
iff_intro
(λ h => or_elim (mp subsingleton_iff h)
  (λ h₁ => exfalso # mpr not_nonempty (mpr empty_iff_eq_emp h₁) nonempty_upair)
  (λ h₁ => exi_elim h₁ # λ c h₂ => eq_trans' c
    (mp mem_singleton # mp (mp eq_iff_mem h₂ a) # mpr mem_upair # or_inl rfl)
    (eq_symm # mp mem_singleton # mp (mp eq_iff_mem h₂ b) #
       mpr mem_upair # or_inr rfl)))
(λ h => eq_rec' (λ x => subsingleton (upair x b)) h #
  eq_rec' subsingleton upair_self_eq subsingleton_singleton)

theorem left_mem_upair {a b} : a ∈ upair a b :=
mpr mem_upair # or_inl rfl

theorem right_mem_upair {a b} : b ∈ upair a b :=
mpr mem_upair # or_inr rfl

theorem mem_asymm {a b} (h : a ∈ b) : b ∉ a :=
λ h₁ => exi_elim (ax_reg # nonempty_intro a left_mem_upair) # λ c h₂ =>
and_elim h₂ # λ h₃ h₄ => h₄ # or_elim (mp mem_upair h₃)
  (λ h₅ => exi_intro b # and_intro (eq_rec' (λ x => b ∈ x) h₅ h₁) right_mem_upair)
  (λ h₅ => exi_intro a # and_intro (eq_rec' (λ x => a ∈ x) h₅ h) left_mem_upair)

theorem mem_antisymm {a b} (h₁ : a ∈ b) (h₂ : b ∈ a) : a = b :=
false_elim # mem_asymm h₁ h₂

theorem ne_of_mem {a b} (h : a ∈ b) : a ≠ b :=
cpos_pn h # λ h₁ => eq_rec' (λ x => x ∉ b) h₁ mem_irrefl

end Unordered_pair

section Ordered_pair

def pair (a b : Set) : Set :=
upair a (upair a b)

theorem nonempty_pair {a b} : nonempty (pair a b) :=
nonempty_upair

theorem not_subsingleton_pair {a b} : ¬subsingleton (pair a b) :=
λ h => not_not_intro (mp subsingleton_upair_iff h) # ne_of_mem left_mem_upair

theorem left_eq_of_pair_eq_pair {a b c d} (h : pair a b = pair c d) : a = c :=
or_elim (mp mem_upair # mp (mp eq_iff_mem h a) left_mem_upair) id #
λ h₁ => exfalso #
or_elim (mp mem_upair # mp (mp eq_iff_mem h (upair a b)) right_mem_upair)
(λ h₂ => hv (eq_rec' (λ x => c ∈ x) h₁ left_mem_upair) # λ h₃ =>
  mem_asymm h₃ # eq_rec (λ x => a ∈ x) h₂ left_mem_upair)
(λ h₂ => hv (eq_trans h₁ # eq_symm h₂) # λ h₃ =>
  mem_irrefl # eq_rec' (λ x => a ∈ x) h₃ left_mem_upair)

theorem right_eq_of_pair_eq_pair {a b c d} (h : pair a b = pair c d) : b = d :=
hv (left_eq_of_pair_eq_pair h) # λ h₁ =>
or_elim (mp mem_upair # mp (mp eq_iff_mem h # upair a b) right_mem_upair)
(λ h₂ => exfalso # mem_irrefl #
  eq_rec' (λ x => a ∈ x) (eq_trans h₁ # eq_symm h₂) left_mem_upair)
(λ h₂ => hv (mp (iff_rec (λ x => x ↔ _) mem_upair # mp eq_iff_mem h₂ b) # or_inr rfl) #
  λ h₃ => or_elim (or_symm # mp mem_upair h₃) id #
  λ h₄ => hv (eq_rec (λ x => upair c x = _) h₄ # eq_rec (λ x => upair x b = _) h₁ h₂) #
  λ h₆ => hv (eq_rec (λ x => upair c d = x) upair_self_eq # eq_symm h₆) #
  λ h₇ => eq_trans h₄ # mp subsingleton_upair_iff #
  eq_rec' subsingleton h₇ subsingleton_singleton)

theorem eq_and_eq_of_pair_eq_pair {a b c d} (h : pair a b = pair c d) : a = c ∧ b = d :=
and_intro (left_eq_of_pair_eq_pair h) (right_eq_of_pair_eq_pair h)

theorem pair_ext {a b c d} : pair a b = pair c d ↔ a = c ∧ b = d :=
iff_intro eq_and_eq_of_pair_eq_pair #
λ h₁ => eq_rec' (λ x => pair x b = pair c d) (and_left h₁) #
eq_rec' (λ x => pair c x = pair c d) (and_right h₁) rfl

def fst (a : Set) : Set :=
some # λ b => ∃ c, a = pair b c

def snd (a : Set) : Set :=
some # λ b => ∃ c, a = pair c b

theorem fst_eq {a b} : fst (pair a b) = a :=
exi_elim (some_spec (exi_intro a # exi_intro b rfl : ∃ c d, pair a b = pair c d)) #
λ c h => eq_symm # left_eq_of_pair_eq_pair h

theorem snd_eq {a b} : snd (pair a b) = b :=
exi_elim (some_spec (exi_intro b # exi_intro a rfl : ∃ c d, pair a b = pair d c)) #
λ c h => eq_symm # right_eq_of_pair_eq_pair h

end Ordered_pair