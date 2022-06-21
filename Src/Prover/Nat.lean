import Src.Prover.Func

namespace prover
noncomputable section

section union

def Union (a : Set) : Set :=
filter (some' # ax_union a) # λ b => ∃ c, c ∈ a ∧ b ∈ c

prefix:110 (priority := high) "⋃ " => Union

theorem mem_Union {a b} : b ∈ ⋃ a ↔ ∃ c, c ∈ a ∧ b ∈ c :=
iff_intro
(λ h => and_elim (mp mem_filter h) # λ _ => id)
(λ h => mpr mem_filter # and_intro
  (exi_elim h # λ c h₁ => some_spec (ax_union a) c b # and_symm h₁) h)

def union (a b : Set) : Set :=
⋃ upair a b

infixl:65 (priority := high) " ∪ " => union

theorem mem_union {a b c} : c ∈ a ∪ b ↔ c ∈ a ∨ c ∈ b :=
iff_trans mem_Union # iff_intro
(λ h => exi_elim h # λ d h₁ => and_elim h₁ # λ h₂ h₃ => or_elim (mp mem_upair h₂)
  (λ h₄ => or_inl # mp (mp eq_iff_mem h₄ c) h₃)
  (λ h₄ => or_inr # mp (mp eq_iff_mem h₄ c) h₃))
(λ h => or_elim h
  (λ h₁ => exi_intro a # and_intro left_mem_upair h₁)
  (λ h₁ => exi_intro b # and_intro right_mem_upair h₁))

theorem Union_emp : ⋃ ∅ = ∅ :=
mp empty_iff_eq_emp # mpr empty_iff # λ a h => exi_elim (mp mem_Union h) # λ b h₁ =>
not_mem_emp # and_left h₁

theorem Union_singleton {a} : ⋃ singleton a = a :=
mpr eq_iff_mem # λ b => iff_trans mem_Union # iff_intro
(λ h => exi_elim h # λ c h₁ => and_elim h₁ # λ h₂ h₃ =>
  mp (mp eq_iff_mem (mp mem_singleton h₂) b) h₃)
(λ h => exi_intro a # and_intro mem_singleton_self h)

theorem union_self {a} : a ∪ a = a :=
mpr eq_iff_mem # λ b => iff_trans mem_union or_self

theorem union_comm {a b} : a ∪ b = b ∪ a :=
mpr eq_iff_mem # λ c => iff_trans mem_union # iff_trans' mem_union or_symm'

end union

section insert

def insert (a b : Set) : Set :=
a ∪ singleton b

theorem mem_insert {a b c} : c ∈ insert a b ↔ c ∈ a ∨ c = b :=
iff_trans mem_union # iff_rec' (λ x => _ ∨ x ↔ _) mem_singleton iff_refl

theorem mem_of_mem_of_eq {a b c} (h₁ : a = b) (h₂ : c ∈ a) : c ∈ b :=
mp (mp eq_iff_mem h₁ c) h₂

theorem mem_of_mem_of_eq' {a b c} (h₁ : a = b) (h₂ : c ∈ b) : c ∈ a :=
mp (mp eq_iff_mem (eq_symm h₁) c) h₂

theorem insert_eq_of_mem {a b} (h : b ∈ a) : insert a b = a :=
mpr eq_iff_mem # λ c => iff_trans mem_insert # iff_intro
(λ h₁ => or_elim h₁ id # λ h₂ => eq_rec' (λ x => x ∈ a) h₂ h) (λ h₁ => or_inl h₁)

end insert

section inter

def Inter (a : Set) : Set :=
filter (⋃ a) # λ b => ∀ c, c ∈ a → b ∈ c

prefix:110 (priority := high) "⋂ " => Inter

theorem mem_Inter {a b} : b ∈ ⋂ a ↔ b ∈ ⋃ a ∧ ∀ c, c ∈ a → b ∈ c :=
iff_trans mem_filter iff_refl

def inter (a b : Set) : Set :=
⋂ upair a b

infixl:65 (priority := high) " ∩ " => inter

theorem mem_inter {a b c} : c ∈ a ∩ b ↔ c ∈ a ∧ c ∈ b :=
iff_trans mem_Inter # iff_intro
(λ h => and_elim h # λ h₁ h₂ => and_intro (h₂ a left_mem_upair) (h₂ b right_mem_upair))
(λ h => and_intro (mpr mem_union # or_of_and h) # λ d h₁ => or_elim (mp mem_upair h₁)
  (λ h₂ => mem_of_mem_of_eq' h₂ # and_left h)
  (λ h₂ => mem_of_mem_of_eq' h₂ # and_right h))

theorem inter_self {a} : a ∩ a = a :=
mpr eq_iff_mem # λ b => iff_trans mem_inter and_self

theorem inter_comm {a b} : a ∩ b = b ∩ a :=
mpr eq_iff_mem # λ c => iff_trans mem_inter # iff_trans' mem_inter and_symm'

end inter

def succ (n : Set) : Set :=
insert n n

theorem mem_succ {n a} : a ∈ succ n ↔ a ∈ n ∨ a = n :=
mem_insert

def succ_is_succ {n} : is_succ (succ n) n :=
λ _ => mem_succ

theorem succ_zero : succ 0 = 1 :=
mpr eq_iff_mem # λ a => iff_trans mem_succ # iff_symm # iff_trans mem_one #
iff_intro or_inr # λ h => or_elim h (λ h₁ => exfalso # not_mem_zero h₁) id

theorem succ_one : succ 1 = 2 :=
mpr eq_iff_mem # λ a => iff_trans mem_succ # iff_symm # iff_trans mem_two #
or_iff_or_right # iff_symm mem_one

theorem is_succ_iff {n1 n} : is_succ n1 n ↔ n1 = succ n :=
iff_intro
(λ h => mpr eq_iff_mem # λ a => iff_symm # iff_trans mem_succ # iff_symm # h a)
(λ h => eq_rec' (λ x => is_succ x n) h succ_is_succ)

def Nat_like (S : Set) : Prop :=
0 ∈ S ∧ ∀ n, n ∈ S → succ n ∈ S

def ℕ : Set :=
⋂ filter (powerset some_inf) Nat_like

theorem Nat_like_some_inf : Nat_like some_inf :=
and_intro zero_mem_some_inf # λ n h => exi_elim (some_spec ax_inf') # λ a h₁ =>
and_right (and_right h₁) n h (succ n) succ_is_succ

theorem Nat_subset_some_inf : ℕ ⊆ some_inf :=
λ n h => and_right (mp mem_filter h) some_inf # mpr mem_filter #
and_intro mem_powerset_self Nat_like_some_inf

theorem zero_mem_Nat : 0 ∈ ℕ :=
mpr mem_Inter # and_intro
(mpr mem_Union # exi_intro some_inf # and_symm # and_intro zero_mem_some_inf #
  mpr mem_filter # and_intro mem_powerset_self Nat_like_some_inf)
(λ a h => and_left # and_right # mp mem_filter h)

theorem zero_mem_of_Nat_like {a} (h : Nat_like a) : 0 ∈ a :=
and_left h

theorem succ_mem_of_Nat_like {a n} (h₁ : Nat_like a) (h₂ : n ∈ a) : succ n ∈ a :=
and_right h₁ n h₂

theorem Nat_subset_of_subset_some_inf_of_Nat_like {a}
  (h₁ : Nat_like a) (h₂ : a ⊆ some_inf) : ℕ ⊆ a :=
λ n h₃ => and_right (mp mem_filter h₃) a # mpr mem_filter #
and_intro (mpr mem_powerset h₂) h₁

theorem succ_mem_Nat {n} (h : n ∈ ℕ) : succ n ∈ ℕ :=
mpr mem_Inter # and_intro
(mpr mem_Union # exi_intro some_inf # and_intro
  (mpr mem_filter # and_intro mem_powerset_self Nat_like_some_inf)
  (succ_mem_of_Nat_like Nat_like_some_inf # Nat_subset_some_inf n h))
(λ a h₁ => and_elim (mp mem_filter h₁) # λ h₂ h₃ =>
  hv (Nat_subset_of_subset_some_inf_of_Nat_like h₃ (mp mem_powerset h₂) n h) #
  succ_mem_of_Nat_like h₃)

theorem Nat_like_Nat : Nat_like ℕ :=
and_intro zero_mem_Nat # λ _ => succ_mem_Nat

theorem Nat_subset_of_Nat_like {a} (h : Nat_like a) : ℕ ⊆ a :=
λ n h₁ => hv (and_right (mp mem_filter h₁) some_inf) # λ h₂ => sorry

theorem Nat_like_of_subset {a b} (h₁ : Nat_like a) (h₂ : a ⊆ b) : Nat_like b :=
sorry

theorem Nat_ind (P : Set → Prop) (h₁ : P 0) (h₂ : ∀ n, n ∈ ℕ → P n → P (succ n)) :
  ∀ n, n ∈ ℕ → P n :=
sorry