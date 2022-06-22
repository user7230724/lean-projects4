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
mem_of_mem_of_eq (eq_symm h₁) h₂

theorem mem_of_mem_of_eq₁ {a b c} (h₁ : a = b) (h₂ : a ∈ c) : b ∈ c :=
eq_rec (λ x => x ∈ c) h₁ h₂

theorem mem_of_mem_of_eq₁' {a b c} (h₁ : a = b) (h₂ : b ∈ c) : a ∈ c :=
mem_of_mem_of_eq₁ (eq_symm h₁) h₂

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

theorem succ_ne_zero {n} : succ n ≠ 0 :=
λ h => mpr empty_iff_eq_emp h # exi_intro n # mpr mem_succ # or_inr rfl

theorem zero_ne_succ {n} : 0 ≠ succ n :=
ne_symm succ_ne_zero

theorem succ_inj_aux {m n a} (h₁ : succ m = succ n) (h₂ : a ∈ m) : a ∈ n :=
hv (iff_trans (mp eq_iff_mem h₁ a) mem_succ) # λ h₃ =>
hv (iff_symm # iff_trans (iff_symm h₃) mem_succ) # λ h₄ =>
or_elim (mp h₄ # or_inl h₂) id # λ h₅ => exfalso #
hv (iff_trans (mp eq_iff_mem h₁ m) mem_succ) # λ h₆ =>
hv (iff_symm # iff_trans (iff_symm h₆) mem_succ) # λ h₇ =>
or_elim (mp h₇ # or_inr rfl)
(λ h₈ => mem_asymm h₈ # mem_of_mem_of_eq₁ h₅ h₂)
(λ h₈ => @mem_irrefl a # mem_of_mem_of_eq' (eq_trans h₅ # eq_symm h₈) h₂)

theorem succ_inj {m n} (h : succ m = succ n) : m = n :=
mpr eq_iff_mem # λ a => iff_intro (succ_inj_aux h) (succ_inj_aux # eq_symm h)

theorem Nat_like_filter_of_ind (P : Set → Prop) {a} (h : Nat_like a)
  (h₁ : P 0) (h₂ : ∀ n, n ∈ a → P n → P (succ n)) : Nat_like (filter a P) :=
and_intro (mpr mem_filter # and_intro (zero_mem_of_Nat_like h) h₁) #
λ n h₃ => mpr mem_filter # and_elim (mp mem_filter h₃) # λ h₄ h₅ =>
and_symm # and_intro (h₂ n h₄ h₅) # succ_mem_of_Nat_like h h₄

theorem filter_subset_self {P : Set → Prop} {a} : filter a P ⊆ a :=
λ b h => and_left # mp mem_filter h

theorem filter_subset_of_subset {P : Set → Prop} {a b} (h : a ⊆ b) : filter a P ⊆ b :=
λ c h₁ => h c # and_left # mp mem_filter h₁

theorem Nat_ind (P : Set → Prop) {n}
  (h : n ∈ ℕ) (h₁ : P 0) (h₂ : ∀ n, n ∈ ℕ → P n → P (succ n)) : P n :=
hv (Nat_like_filter_of_ind P Nat_like_Nat h₁ h₂) # λ h₄ =>
hv (Nat_subset_of_subset_some_inf_of_Nat_like h₄
(filter_subset_of_subset Nat_subset_some_inf)) # λ h₅ =>
and_right # mp mem_filter (h₅ n h)

theorem ne_succ_self {n} (h : n ∈ ℕ) : n ≠ succ n :=
Nat_ind (λ x => x ≠ succ x) h zero_ne_succ #
λ n h₁ h₂ => cpos_nn h₂ # λ h₂ => succ_inj h₂

section pred

def pred (n : Set) : Set :=
some (λ k => succ k = n)

theorem pred_succ {n} : pred (succ n) = n :=
succ_inj # @some_spec _ _ (λ k => succ k = succ n) # exi_intro n rfl

theorem pred_one : pred 1 = 0 :=
eq_rec (λ x => pred x = 0) succ_zero pred_succ

end pred

section le

def le (m n : Set) : Prop :=
∃ (f : Set → Set), f 0 = m ∧ (∀ (k : Set), k ∈ ℕ → f (succ k) = succ (f k)) ∧
∃ (k : Set), k ∈ ℕ ∧ f k = n

infix:50 (priority := high) " ≤ " => le

theorem zero_le {n} (h : n ∈ ℕ) : 0 ≤ n :=
exi_intro id # and_intro rfl # and_intro (λ _ _ => rfl) # exi_intro n # and_intro h rfl

theorem le_of_succ_le_succ {m n}
  (h₁ : m ∈ ℕ) (h₂ : n ∈ ℕ) (h : succ m ≤ succ n) : m ≤ n :=
exi_elim h # λ f h₃ => exi_intro (λ x => pred (f x)) # and_elim h₃ # λ h₃ h₄ =>
and_elim h₄ # λ h₄ h₅ => and_intro (eq_rec' (λ x => pred x = m) h₃ pred_succ) #
and_intro
(λ k hk => eq_rec' (λ x => pred x = succ (pred (f k))) (h₄ k hk) #
  eq_rec' (λ x => x = succ (pred (f k))) pred_succ # eq_symm #
  Nat_ind (λ x => succ (pred (f x)) = f x) hk
  (eq_rec' (λ x => succ (pred x) = x) h₃ # congr_arg pred_succ) #
  λ k hk ih => eq_rec' (λ x => succ (pred x) = x) (h₄ k hk) # congr_arg pred_succ)
(exi_elim h₅ # λ k hk => and_elim hk # λ hk h₆ => exi_intro k # and_intro hk #
  eq_rec' (λ x => pred x = n) h₆ pred_succ)

theorem succ_le_succ_of_le {m n}
  (h₁ : m ∈ ℕ) (h₂ : n ∈ ℕ) (h : m ≤ n) : succ m ≤ succ n :=
exi_elim h # λ f h₃ => exi_intro (λ x => succ (f x)) # and_elim h₃ # λ h₃ h₄ =>
and_elim h₄ # λ h₄ h₅ => and_intro (congr_arg h₃) # and_intro
(λ k hk => eq_rec' (λ x => succ x = _) (h₄ k hk) rfl)
(exi_elim h₅ # λ k hk => and_elim hk # λ hk h₆ => exi_intro k # and_intro hk #
  congr_arg h₆)

theorem succ_le_succ_iff {m n} (h₁ : m ∈ ℕ) (h₂ : n ∈ ℕ) : succ m ≤ succ n ↔ m ≤ n :=
iff_intro (le_of_succ_le_succ h₁ h₂) (succ_le_succ_of_le h₁ h₂)

theorem le_refl {n} (h : n ∈ ℕ) : n ≤ n :=
Nat_ind (λ x => x ≤ x) h (zero_le zero_mem_Nat) #
λ n h ih => succ_le_succ_of_le h h ih

theorem le_succ_of_le {m n} (h₁ : m ∈ ℕ) (h₂ : n ∈ ℕ) (h₃ : m ≤ n) : m ≤ succ n :=
exi_elim h₃ # λ f h₁ => exi_intro f # and_elim h₁ # λ h₁ h₂ => and_elim h₂ #
λ h₂ h₃ => and_intro h₁ # and_intro h₂ # exi_elim h₃ # λ k hk => and_elim hk #
λ hk h₄ => exi_intro (succ k) # and_intro (succ_mem_Nat hk) # eq_trans (h₂ k hk) #
congr_arg h₄

theorem le_succ_self {n} (h : n ∈ ℕ) : n ≤ succ n :=
le_succ_of_le h h # le_refl h

theorem not_succ_le_zero {n} (h : n ∈ ℕ) : ¬succ n ≤ 0 :=
λ h₁ => exi_elim h₁ # λ f h₁ => and_elim h₁ # λ h₁ h₂ => and_elim h₂ # λ h₂ h₃ =>
exi_elim h₃ # λ k h₃ => and_elim h₃ # λ h₃ h₄ => Nat_ind (λ x => f x ≠ 0) h₃
(eq_rec' (λ x => x ≠ 0) h₁ succ_ne_zero)
(λ k h₃ ih => eq_rec' (λ x => x ≠ 0) (h₂ k h₃) succ_ne_zero) h₄

def lt (m n : Set) : Prop :=
m ≤ n ∧ m ≠ n

infix:50 (priority := high) " < " => lt

theorem lt_iff_le_and_ne {m n} (h₁ : m ∈ ℕ) (h₂ : n ∈ ℕ) : m < n ↔ m ≤ n ∧ m ≠ n :=
iff_refl

theorem le_of_eq {m n} (h₁ : m ∈ ℕ) (h₂ : n ∈ ℕ) (h₃ : m = n) : m ≤ n :=
eq_rec' (λ x => x ≤ n) h₃ # le_refl h₂

theorem eq_iff_lt_or_eq {m n} (h₁ : m ∈ ℕ) (h₂ : n ∈ ℕ) : m ≤ n ↔ m < n ∨ m = n :=
iff_intro (λ h => by_cases (m = n) or_inr # λ h₃ => or_inl # and_intro h h₃)
(λ h => or_elim h and_left # le_of_eq h₁ h₂)

theorem not_succ_le_self {n} (h : n ∈ ℕ) : ¬succ n ≤ n :=
Nat_ind (λ x => ¬succ x ≤ x) h (not_succ_le_zero zero_mem_Nat) #
λ n h ih => cpos_nn ih # λ ih => le_of_succ_le_succ (succ_mem_Nat h) h ih

theorem Nat_cases (P : Set → Prop) {n}
  (h₁ : n ∈ ℕ) (h₂ : P 0) (h₃ : ∀ n, n ∈ ℕ → P (succ n)) : P n :=
Nat_ind P h₁ h₂ # λ n h ih => h₃ n h

theorem eq_zero_or_succ {n} (h : n ∈ ℕ) : n = 0 ∨ ∃ m, n = succ m :=
Nat_cases (λ x => x = 0 ∨ ∃ m, x = succ m) h (or_inl rfl) #
λ n h => or_inr # exi_intro n rfl

-- theorem lt_succ_iff_le {m n} (h₁ : m ∈ ℕ) (h₂ : n ∈ ℕ) : m < succ n ↔ m ≤ n :=
-- sorry

-- theorem Nat_strong_ind (P : Set → Prop) {n} (h : n ∈ ℕ)
--   (h₁ : )

-- theorem le_trans {m n k} (h₁ : m ∈ ℕ) (h₂ : n ∈ ℕ) (h₃ : k ∈ ℕ)
--   (h₄ : m ≤ n) (h₅ : n ≤ k) : m ≤ k :=
-- _

end le