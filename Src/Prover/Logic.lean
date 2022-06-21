import Lean

section
open Lean Elab Term
elab "!" tm:term : term => elabTermEnsuringType tm none
end

namespace prover
noncomputable section

def id.{u} {α : Sort u} (x : α) : α := x

infixr:1 (priority := high) " # " => id

-- Definitions

def true : Prop :=
∀ (P : Prop), P → P

def false : Prop :=
∀ (P : Prop), P

def not (P : Prop) : Prop :=
P → false

prefix:40 (priority := high) "¬" => not

def or (P Q : Prop) : Prop :=
¬P → Q

infixr:30 (priority := high) " ∨ " => or

def and (P Q : Prop) : Prop :=
¬(¬P ∨ ¬Q)

infixr:35 (priority := high) " ∧ " => and

def iff (P Q : Prop) : Prop :=
(P → Q) ∧ (Q → P)

infixl:20 (priority := high) " ↔ " => iff

def eq {α : Type} (x y : α) : Prop :=
∀ (P : α → Prop), P x → P y

infixl:50 (priority := high) " = " => eq

def ne {α : Type} (x y : α) : Prop :=
¬(x = y)

infixl:50 (priority := high) " ≠ " => ne

def exi {α : Type} (P : α → Prop) : Prop :=
¬(∀ (x : α), ¬P x)

section open Lean
macro (priority := high) "∃ " xs:explicitBinders ", " b:term : term =>
expandExplicitBinders ``exi xs b end

def exiu {α : Type} (P : α → Prop) : Prop :=
(∃ (x : α), P x) ∧ (∀ (x y : α), P x → P y → x = y)

section open Lean
macro (priority := high) "∃! " xs:explicitBinders ", " b:term : term =>
expandExplicitBinders ``exiu xs b end

-- Axioms

axiom prop_rec (F : Prop → Prop) {P : Prop} : F true → F false → F P

-- Theorems

theorem trivial : true :=
λ _ => id

theorem not_false : not false :=
id

theorem not_not_intro {P : Prop} (h : P) : ¬¬P :=
λ h₁ => h₁ h

theorem not_not_elim {P : Prop} (h : ¬¬P) : P :=
prop_rec (λ x => ¬¬x → x) (λ _ => trivial) (λ h₁ => h₁ not_false) h

theorem contra {P : Prop} (h : ¬¬P) : P :=
not_not_elim h

theorem em {P : Prop} : P ∨ ¬P := id

theorem false_elim {P : Prop} (h : false) : P :=
h P

theorem exfalso {P : Prop} (h : false) : P :=
false_elim h

theorem mt {P Q : Prop} (h₁ : P → Q) (h₂ : ¬Q) : ¬P :=
λ h₃ => h₂ # h₁ h₃

theorem or_intro₁ {P Q : Prop} (h : P) : P ∨ Q :=
λ h₁ => false_elim (h₁ h)

theorem or_intro₂ {P Q : Prop} (h : Q) : P ∨ Q :=
λ _ => h

theorem or_elim {P Q R : Prop} (h₁ : P ∨ Q) (h₂ : P → R) (h₃ : Q → R) : R :=
not_not_elim # λ h₄ => h₄ # h₃ # h₁ # mt h₂ h₄

theorem or_inl {P Q : Prop} (h : P) : P ∨ Q :=
or_intro₁ h

theorem or_inr {P Q : Prop} (h : Q) : P ∨ Q :=
or_intro₂ h

theorem and_intro {P Q : Prop} (h₁ : P) (h₂ : Q) : P ∧ Q :=
λ h₃ => or_elim h₃ (λ h₄ => h₄ h₁) (λ h₄ => h₄ h₂)

theorem and_elim₁ {P Q : Prop} (h : P ∧ Q) : P :=
not_not_elim # λ h₁ => h # or_intro₁ h₁

theorem and_elim₂ {P Q : Prop} (h : P ∧ Q) : Q :=
not_not_elim # λ h₁ => h # or_intro₂ h₁

theorem and_left {P Q : Prop} (h : P ∧ Q) : P :=
and_elim₁ h

theorem and_right {P Q : Prop} (h : P ∧ Q) : Q :=
and_elim₂ h

theorem iff_intro {P Q : Prop} (h₁ : P → Q) (h₂ : Q → P) : P ↔ Q :=
and_intro h₁ h₂

theorem iff_elim₁ {P Q : Prop} (h : P ↔ Q) : P → Q :=
and_elim₁ h

theorem iff_elim₂ {P Q : Prop} (h : P ↔ Q) : Q → P :=
and_elim₂ h

theorem mp {P Q : Prop} (h : P ↔ Q) : P → Q :=
iff_elim₁ h

theorem mpr {P Q : Prop} (h : P ↔ Q) : Q → P :=
iff_elim₂ h

theorem true_ne_false : true ≠ false :=
λ h => h id trivial

theorem not_not {P : Prop} : ¬¬P ↔ P :=
iff_intro not_not_elim not_not_intro

theorem iff_rec (F : Prop → Prop) {P Q : Prop} (h₁ : P ↔ Q) (h₂ : F P) : F Q :=
prop_rec (λ x => (x ↔ Q) → F x → F Q)
(prop_rec (λ x => (true ↔ x) → F true → F x) (λ _ => id)
  (λ h₃ => false_elim # mp h₃ trivial))
(prop_rec (λ x => (false ↔ x) → F false → F x)
  (λ h₃ => false_elim # mpr h₃ trivial) (λ _ => id))
h₁ h₂

theorem eq_refl {α : Type} {x : α} : x = x :=
λ _ => id

theorem rfl {α : Type} {x : α} : x = x :=
eq_refl

theorem eq_symm {α : Type} {x y : α} (h : x = y) : y = x :=
not_not_elim # λ h₁ => mt (h (λ z => z = x)) h₁ rfl

theorem eq_iff {α : Type} {x y : α} : x = y ↔ (∀ (P : α → Prop), P x ↔ P y) :=
iff_intro (λ h P => iff_intro (h P) (eq_symm h P)) (λ h => mp (h (λ z => x = z)) rfl)

theorem eq_rec {α : Type} (P : α → Prop) {x y : α} (h₁ : x = y) (h₂ : P x) : P y :=
h₁ P h₂

theorem imp_refl {P : Prop} : P → P :=
id

theorem iff_refl {P : Prop} : P ↔ P :=
iff_intro id id

theorem or_self {P : Prop} : P ∨ P ↔ P :=
iff_intro (λ h => or_elim h id id) (λ h => or_inl h)

theorem and_self {P : Prop} : P ∧ P ↔ P :=
iff_intro and_left (λ h => and_intro h h)

theorem not_or {P Q : Prop} : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
iff_intro
(λ h => and_intro (λ h₁ => h # or_inl h₁) (λ h₁ => h # or_inr h₁))
(λ h h₁ => or_elim h₁ (λ h₂ => and_left h h₂) (λ h₂ => and_right h h₂))

theorem not_and {P Q : Prop} : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
iff_intro
(λ h => not_not_elim # λ h₁ => (λ h₂ => h # and_intro
  (not_not_elim # and_left h₂) (not_not_elim # and_right h₂)) (mp not_or h₁))
(λ h h₁ => or_elim h (λ h₂ => h₂ # and_left h₁) (λ h₂ => h₂ # and_right h₁))

theorem not_iff_not_self {P : Prop} : ¬(P ↔ ¬P) :=
λ h => or_elim em (λ h₁ => mp h h₁ h₁) (λ h₁ => h₁ # mpr h h₁)

theorem or_symm {P Q : Prop} (h : P ∨ Q) : Q ∨ P :=
or_elim h or_inr or_inl

theorem and_symm {P Q : Prop} (h : P ∧ Q) : Q ∧ P :=
and_intro (and_right h) (and_left h)

theorem iff_symm {P Q : Prop} (h : P ↔ Q) : Q ↔ P :=
iff_intro (mpr h) (mp h)

theorem not_iff {P Q : Prop} : ¬(P ↔ Q) ↔ (¬P ↔ Q) :=
iff_intro
(λ h => iff_intro (λ h₁ => not_not_elim # λ h₂ => h # iff_intro
  (λ h₃ => false_elim # h₁ h₃) (λ h₃ => false_elim # h₂ h₃))
  (λ h₁ h₂ => h # iff_intro (λ _ => h₁) (λ _ => h₂)))
(λ h h₁ => not_iff_not_self # iff_symm # iff_rec (λ x => ¬x ↔ Q) h₁ h)

theorem iff_true_intro {P : Prop} (h : P) : P ↔ true :=
iff_intro (λ _ => trivial) (λ _ => h)

theorem iff_true_elim {P : Prop} (h : P ↔ true) : P :=
mpr h trivial

theorem iff_true {P : Prop} : (P ↔ true) ↔ P :=
iff_intro iff_true_elim iff_true_intro

theorem iff_false_intro {P : Prop} (h : ¬P) : P ↔ false :=
iff_intro h false_elim

theorem iff_false_elim {P : Prop} (h : P ↔ false) : ¬P :=
mp h

theorem iff_false {P : Prop} : (P ↔ false) ↔ ¬P :=
iff_intro iff_false_elim iff_false_intro

theorem prop_eq {P Q : Prop} : P = Q ↔ (P ↔ Q) :=
iff_intro
(λ h => eq_rec (λ x => P ↔ x) h iff_refl)
(λ h => iff_rec (λ x => P = x) h rfl)

theorem iff_rec' (F : Prop → Prop) {P Q : Prop} (h₁ : P ↔ Q) (h₂ : F Q) : F P :=
iff_rec F (iff_symm h₁) h₂

theorem eq_rec' {α : Type} (P : α → Prop) {x y : α} (h₁ : x = y) (h₂ : P y) : P x :=
eq_rec P (eq_symm h₁) h₂

theorem eq_true {P : Prop} : P = true ↔ P :=
iff_rec' (λ x => x ↔ P) prop_eq iff_true

theorem eq_false {P : Prop} : P = false ↔ ¬P :=
iff_rec' (λ x => x ↔ ¬P) prop_eq iff_false

theorem eq_true_or_false {P : Prop} : P = true ∨ P = false :=
iff_rec' (λ x => x ∨ P = false) eq_true #
iff_rec' (λ x => P ∨ x) eq_false em

theorem exi_intro {α : Type} {P : α → Prop} (x : α) (h : P x) : ∃ (x : α), P x :=
λ h₁ => h₁ x h

theorem exi_elim {α : Type} {P : α → Prop} {Q : Prop}
  (h₁ : ∃ (x : α), P x) (h₂ : ∀ (x : α), P x → Q) : Q :=
not_not_elim # λ h₃ => h₁ # λ x => mt (h₂ x) h₃

theorem not_forall {α : Type} {P : α → Prop} : ¬(∀ (x : α), P x) ↔ ∃ (x : α), ¬P x :=
iff_intro
(λ h h₁ => h # λ x => not_not_elim # h₁ x)
(λ h h₁ => h # λ x => not_not_intro # h₁ x)

theorem not_exi {α : Type} {P : α → Prop} : ¬(∃ (x : α), P x) ↔ ∀ (x : α), ¬P x :=
iff_intro
(λ h x h₁ => h # exi_intro x h₁)
(λ h h₁ => exi_elim h₁ h)

theorem exiu_intro' {α : Type} {P : α → Prop} (h₁ : ∃ (x : α), P x)
  (h₂ : ∀ (x y : α), P x → P y → x = y) : ∃! (x : α), P x :=
and_intro h₁ h₂

theorem and_elim {P Q R : Prop} (h₁ : P ∧ Q) (h₂ : P → Q → R) : R :=
h₂ (and_left h₁) (and_right h₁)

theorem iff_elim {P Q R : Prop} (h₁ : P ↔ Q) (h₂ : (P → Q) → (Q → P) → R) : R :=
h₂ (mp h₁) (mpr h₁)

theorem exiu_elim {α : Type} {P : α → Prop} {Q : Prop} (h₁ : ∃! (x : α), P x)
  (h₂ : ∀ (x : α), P x → (∀ (y : α), P y → y = x) → Q) : Q :=
and_elim h₁ # λ h₃ h₄ => exi_elim h₃ # λ x h₅ => h₂ x h₅ # λ y h₆ => h₄ y x h₆ h₅

theorem imp_trans {P Q R : Prop} (h₁ : P → Q) (h₂ : Q → R) : P → R :=
λ h => h₂ # h₁ h

theorem or_assoc {P Q R : Prop} : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
iff_intro
(λ h => or_elim h
  (λ h₁ => or_elim h₁ or_inl (λ h₂ => or_inr # or_inl h₂))
  (λ h₁ => or_inr # or_inr h₁))
(λ h => or_elim h
  (λ h₁ => or_inl # or_inl h₁)
  (λ h₁ => or_elim h₁ (λ h₂ => or_inl # or_inr h₂) or_inr))

theorem and_assoc {P Q R : Prop} : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) :=
iff_intro
(λ h => and_elim h # λ h₁ h₂ =>
  and_intro (and_left h₁) (and_intro (and_right h₁) h₂))
(λ h => and_elim h # λ h₁ h₂ =>
  and_intro (and_intro h₁ (and_left h₂)) (and_right h₂))

theorem or_symm' {P Q : Prop} : P ∨ Q ↔ Q ∨ P :=
iff_intro or_symm or_symm

theorem and_symm' {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
iff_intro and_symm and_symm

theorem iff_symm' {P Q : Prop} : (P ↔ Q) ↔ (Q ↔ P) :=
iff_intro iff_symm iff_symm

theorem eq_symm' {α : Type} {x y : α} : x = y ↔ y = x :=
iff_intro eq_symm eq_symm

theorem iff_iff_cancel {P Q : Prop} (h : (P ↔ Q) ↔ Q) : P :=
contra # λ h₁ => iff_rec (λ x => ¬((x ↔ Q) ↔ Q))
(iff_symm # iff_false_intro h₁)
(λ h₂ => iff_rec (λ x => ¬(x ↔ Q))
  (iff_intro (λ h₃ => iff_symm # iff_false_intro h₃) mpr)
  (λ h₄ => not_iff_not_self # iff_symm h₄) h₂) h

theorem iff_assoc_aux {P Q R : Prop} (h : (P ↔ Q) ↔ R) : P ↔ (Q ↔ R) :=
iff_elim h # λ h₁ h₂ => iff_intro
(λ h₃ => iff_intro
  (λ h₄ => h₁ # iff_intro (λ _ => h₄) (λ _ => h₃))
  (λ h₄ => mp (h₂ h₄) h₃))
(λ h₃ => iff_iff_cancel # iff_rec (λ x => (P ↔ x) ↔ R) h₃ h)

theorem iff_assoc {P Q R : Prop} : ((P ↔ Q) ↔ R) ↔ (P ↔ (Q ↔ R)) :=
iff_intro iff_assoc_aux
(λ h => iff_symm # iff_rec' (λ x => R ↔ x) iff_symm' #
  iff_assoc_aux # iff_rec' (λ x => x ↔ P) iff_symm' # iff_symm h)

theorem and_trans {P Q R  : Prop} (h₁ : P ∧ Q) (h₂ : Q ∧ R) : P ∧ R :=
and_intro (and_left h₁) (and_right h₂)

theorem iff_trans {P Q R  : Prop} (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R :=
iff_intro (λ h₃ => mp h₂ # mp h₁ h₃) (λ h₃ => mpr h₁ # mpr h₂ h₃)

theorem iff_trans' (Q : Prop) {P R  : Prop} (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R :=
iff_trans h₁ h₂

theorem eq_trans {α : Type} {x y z : α} (h₁ : x = y) (h₂ : y = z) : x = z :=
eq_rec' (λ x => x = z) h₁ h₂

theorem eq_trans' {α : Type} (y : α) {x z : α} (h₁ : x = y) (h₂ : y = z) : x = z :=
eq_trans h₁ h₂

theorem exiu_iff {α : Type} {P : α → Prop} :
  (∃! (x : α), P x) ↔ ∃ (x : α), P x ∧ ∀ (y : α), P y → y = x :=
iff_intro
(λ h => exiu_elim h # λ x h₁ h₂ => exi_intro x # and_intro h₁ h₂)
(λ h => exi_elim h # λ x h₁ => exiu_intro' (exi_intro x # and_left h₁)
  (λ y z h₃ h₄ => and_elim h₁ # λ h₅ h₆ => eq_trans (h₆ y h₃) # eq_symm # h₆ z h₄))

theorem exiu_intro {α : Type} {P : α → Prop} (x : α)
  (h₁ : P x) (h₂ : ∀ (y : α), P y → y = x) : ∃! (x : α), P x :=
mpr exiu_iff # exi_intro x # and_intro h₁ h₂

theorem by_cases (P : Prop) {Q : Prop} (h₁ : P → Q) (h₂ : ¬P → Q) : Q :=
or_elim em h₁ h₂

theorem cpos {P Q : Prop} (h₁ : P) (h₂ : ¬Q → ¬P) : Q :=
contra # λ h₃ => h₂ h₃ h₁

theorem cpos' {P Q : Prop} (h₁ : ¬P) (h₂ : Q → P) : ¬Q :=
mt h₂ h₁

theorem ne_symm {α : Type} {x y : α} (h : x ≠ y) : y ≠ x :=
cpos' h eq_symm

theorem ne_symm' {α : Type} {x y : α} : x ≠ y ↔ y ≠ x :=
iff_intro ne_symm ne_symm

theorem cpos_pp {P Q : Prop} (h₁ : P) (h₂ : ¬Q → ¬P) : Q :=
cpos h₁ h₂

theorem cpos_pn {P Q : Prop} (h₁ : P) (h₂ : Q → ¬P) : ¬Q :=
cpos h₁ # λ h₃ => h₂ # not_not_elim h₃

theorem cpos_np {P Q : Prop} (h₁ : ¬P) (h₂ : ¬Q → P) : Q :=
cpos h₁ # λ h₃ => not_not_intro # h₂ h₃

theorem cpos_nn {P Q : Prop} (h₁ : ¬P) (h₂ : Q → P) : ¬Q :=
cpos' h₁ h₂

theorem hv {P Q : Prop} (h₁ : P) (h₂ : P → Q) : Q :=
h₂ h₁