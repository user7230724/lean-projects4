namespace test

def id.{u} {α : Sort u} (x : α) : α := x

infixr:1 (priority := high) " # " => id

-----

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

-----

axiom prop_rec (F : Prop → Prop) {P : Prop} (h₁ : F true) (h₂ : F false) : F P

-----

theorem trivial : true :=
λ _ => id

theorem not_false : not false :=
id

theorem not_not_intro {P : Prop} (h : P) : ¬¬P :=
λ h₁ => h₁ h

theorem not_not_elim {P : Prop} (h : ¬¬P) : P :=
prop_rec (λ x => ¬¬x → x) (λ _ => trivial) (λ h₁ => h₁ not_false) h

theorem em {P : Prop} : P ∨ ¬P := id

theorem false_elim {P : Prop} (h : false) : P :=
h P

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
(@prop_rec (λ x => (true ↔ x) → F true → F x) Q (λ _ => id)
  (λ h₃ => false_elim # mp h₃ trivial))
(@prop_rec (λ x => (false ↔ x) → F false → F x) Q
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
λ h => or_elim (@em P) (λ h₁ => mp h h₁ h₁) (λ h₁ => h₁ # mpr h h₁)

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
(λ h h₁ => @not_iff_not_self Q # iff_symm # @iff_rec (λ x => ¬x ↔ Q) P Q h₁ h)

theorem iff_true_intro {P : Prop} (h : P) : P ↔ true :=
iff_intro (λ _ => trivial) (λ _ => h)

-- theorem iff_true_elim {P : Prop} (h : P ↔ true) : P :=
-- _

-- theorem eq_true_or_false {P : Prop} : P = true ∨ P = false :=
-- _

-----

end test