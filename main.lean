namespace test

inductive nat : Type
  | zero : nat
  | succ : nat → nat
open nat

def rec {t : Type} (z : t) (f : nat → t → t) : nat → t
  | nat.zero => z
  | (nat.succ n) => f n (rec z f n)

def Nat_of_nat : Nat → nat
  | Nat.zero => nat.zero
  | (Nat.succ n) => nat.succ (Nat_of_nat n)

instance {n : Nat} : OfNat nat n where
  ofNat := Nat_of_nat n

-----

def Pf : nat → Prop
| 1 => True
| _ => False

instance : CoeSort nat Prop where
  coe := Pf

theorem triv : (1 : nat) := trivial

theorem elim {P : Prop} (h : (0 : nat)) : P := by cases h

theorem psub {P : nat → Prop} (h₁ : P 1) (n : nat) (h₂ : n) : P n := by
  match n with
  | 0 => cases h₂
  | 1 => exact h₁
  | nat.succ (nat.succ _) => cases h₂

theorem ind {P : nat → Prop} (h₁ : P 0)
(h₂ : (n : nat) → P n → P (succ n)) (n : nat) : P n := by
  induction n with
  | zero => exact h₁
  | succ n ih => exact h₂ n ih

-----

def id' {t : Type} (a : t) : t := a
def const {t s : Type} (a : t) (b : s) : t := a

def cases {t : Type} (z : t) (f : nat → t) (n : nat) : t :=
rec z (λ k _ => f k) n

def pred (n : nat) : nat :=
cases 0 id n

def prop (p : nat) : nat :=
cases 1 (cases 1 (const 0)) p

def true : nat := 1
def false : nat := 0

def ite {t : Type} (p : nat) (a b : t) : t :=
cases b (const a) p

def not (p : nat) : nat :=
ite p false true

def and (P Q : nat) : nat :=
ite P Q false

def or (P Q : nat) : nat :=
ite P true Q

def imp (P Q : nat) : nat :=
ite P Q true

def iff (P Q : nat) : nat :=
ite P Q (not Q)

def nat_eq (a b : nat) : nat :=
rec not (λ n f k => ite k (f (pred k)) 0) a b

-----

theorem elim' {P : Prop} {n : nat} (h : succ (succ n)) : P := by
  apply elim
  apply @psub (λ n => not (pred n)) triv _ h

theorem cs {P : nat → Prop} (h₁ : P 0)
(h₂ : (n : nat) → P (succ n)) (n : nat) : P n := by
  induction n using ind with
  | h₁ => exact h₁
  | h₂ => apply h₂

theorem psub' {P : nat → Prop} {n : nat} (h₁ : n) (h₂ : P n) : P 1 := by
  induction n using cs with
  | h₁ => apply elim h₁
  | h₂ n => induction n using cs with
    | h₁ => apply h₂
    | h₂ => apply elim' h₁

theorem prop_cs {P : nat → Prop}
(h₁ : P true) (h₂ : P false) (n : nat) (hp : prop n) : P n := by
  induction n using cs with
  | h₁ => apply h₂
  | h₂ n => induction n using cs with
    | h₁ => apply h₁
    | h₂ n => apply elim hp

theorem imp_intro {P Q : nat} (hp : prop P) (hq : prop Q) (h : P → Q) : imp P Q := by
  induction P using prop_cs with
  | h₁ => apply h triv
  | h₂ => apply triv

theorem imp_elim {P Q : nat}, prop P → prop Q → imp P Q → P → Q :=
@λ P Q hp hq h₁ h₂ => psub' (λ x => imp x Q) h₂ h₁

theorem eq_refl : ∀ {a : nat}, nat_eq a a :=
ind (λ x => nat_eq x x) triv id

theorem prop_prop : ∀ {a : nat}, prop (prop a) :=
cs (λ x => prop (prop x)) triv (cs (λ x => prop (prop (succ x))) triv triv)

theorem prop_not : ∀ {a : nat}, prop (not a) :=
cs (λ x => prop (not x)) triv triv

-- theorem nat_eq_type : ∀ (a b : nat), prop (nat_eq a b) :=
-- λ a => ind (λ x => ∀ b, prop (nat_eq x b)) @prop_not
-- (@λ a ih b => cs (λ x => prop (nat_eq (succ a) x)) triv (ih (succ b)))

theorem not_type : ∀ {a : nat}, prop a → prop (not a) :=
λ a _, prop_not

theorem imp_type : ∀ {P Q : nat}, prop P → prop Q → prop (imp P Q) :=
λ P Q _ h, @cs (λ x, prop (imp x Q)) triv (λ n, h) _

theorem and_type : ∀ {P Q : nat}, prop P → prop Q → prop (and P Q) :=
λ P Q _ h, @cs (λ x, prop (and x Q)) triv (λ n, h) _

theorem or_type : ∀ {P Q : nat}, prop P → prop Q → prop (or P Q) :=
λ P Q _ h, @cs (λ x, prop (or x Q)) h (λ n, triv) _

theorem iff_type : ∀ {P Q : nat}, prop P → prop Q → prop (iff P Q) :=
λ P Q h₁ h₂, id prop_cs (λ x, prop (iff x Q)) h₂ (not_type h₂) h₁

theorem and_intro : ∀ {P Q : nat}, P → Q → and P Q :=
λ P Q h₁ h₂, id psub (λ x, and x Q) h₁ (id psub (λ x, and 1 x) h₂ triv)

theorem and_elim₁ : ∀ {P Q : nat}, prop P → prop Q → and P Q → P :=
λ P Q h₁ h₂, id prop_cs (λ x, and x Q → x) (λ _, triv) (λ h, elim h) h₁

theorem and_elim₂ : ∀ {P Q : nat}, prop P → prop Q → and P Q → Q :=
λ P Q h₁ h₂, id prop_cs (λ x, and x Q → Q) (λ h, h) (λ h, elim h) h₁

theorem or_intro₁ : ∀ {P Q : nat}, P → prop Q → or P Q :=
λ P Q h₁ h₂, id psub (λ x, or x Q) h₁ triv

theorem or_intro₂ : ∀ {P Q : nat}, prop P → Q → or P Q :=
λ P Q h₁ h₂, id prop_cs (λ x, or x Q) triv h₂ h₁

theorem or_elim : ∀ {F : Prop} {P Q : nat}, prop P → prop Q → or P Q → (P → F) → (Q → F) → F :=
λ F P Q hp hq, prop_cs (λ x, or x Q → (x → F) → (Q → F) → F)
(λ h₁ h₂ h₃, h₂ triv) (λ h₁ h₂ h₃, h₃ h₁) hp

theorem iff_intro : ∀ {P Q : nat}, prop P → prop Q → imp P Q → imp Q P → iff P Q :=
λ P Q hp hq, prop_cs (λ x, imp x Q → imp Q x → iff x Q) (λ h₁ h₂, h₁)
(λ h₁, prop_cs (λ x, imp x false → iff false x) (λ h₂, elim h₂) (λ _, triv) hq) hp

theorem iff_elim₁ : ∀ {P Q : nat}, prop P → prop Q → iff P Q → imp P Q :=
λ P Q hp hq, prop_cs (λ x, iff x Q → imp x Q) (λ h, h) (λ _, triv) hp

theorem iff_elim₂ : ∀ {P Q : nat}, prop P → prop Q → iff P Q → imp Q P :=
λ P Q hp hq, prop_cs (λ x, iff x Q → imp Q x)
(λ _, id prop_cs (λ x, imp x true) triv triv hq)
(id prop_cs (λ x, iff false x → imp x false) (λ h, h) (λ h, triv) hq) hp

theorem not_not : ∀ {P : nat}, prop P → iff (not (not P)) P :=
prop_cs (λ x, iff (not (not x)) x) triv triv

theorem iff_sub : ∀ (F : nat → Prop) ⦃P Q : nat⦄, prop P → prop Q → iff P Q → F P → F Q :=
λ F P Q hp hq, prop_cs (λ x, iff x Q → F x → F Q)
(λ h₁ h₂, psub F (@imp_elim true Q triv hq (@iff_elim₁ true Q triv hq h₁) triv) h₂)
(id prop_cs (λ x, iff false x → F false → F x) (λ h, elim h) (λ _ h, h) hq) hp

theorem imp_refl : ∀ {P : nat}, prop P → imp P P :=
λ P hp, imp_intro hp hp (λ h, h)

theorem iff_refl : ∀ {P : nat}, prop P → iff P P :=
λ P hp, iff_intro hp hp (imp_refl hp) (imp_refl hp)

theorem and_symm : ∀ {P Q : nat}, prop P → prop Q → and P Q → and Q P :=
λ P Q hp hq h, and_intro (and_elim₂ hp hq h) (and_elim₁ hp hq h)

theorem or_symm : ∀ {P Q : nat}, prop P → prop Q → or P Q → or Q P :=
λ P Q hp hq h, or_elim hp hq h (λ h₁, or_intro₂ hq h₁) (λ h₁, or_intro₁ h₁ hp)

theorem iff_symm : ∀ {P Q : nat}, prop P → prop Q → iff P Q → iff Q P :=
λ P Q hp hq h, iff_intro hq hp (iff_elim₂ hp hq h) (iff_elim₁ hp hq h)

theorem imp_tran : ∀ {P Q R : nat}, prop P → prop Q → prop R → imp P Q → imp Q R → imp P R :=
λ P Q R hp hq hr h₁ h₂, imp_intro hp hr
(λ h₃, imp_elim hq hr h₂ (imp_elim hp hq h₁ h₃))

theorem not_zero_eq_succ {n : nat} : not (nat_eq 0 (succ n)) := triv

theorem not_succ_eq_zero {n : nat} : not (nat_eq (succ n) 0) :=
@ind (λ x, not (nat_eq (succ x) 0)) triv (λ n ih, ih) n

theorem eq_of_succ_eq_succ {a b : nat} : nat_eq (succ a) (succ b) → nat_eq a b := id

theorem eq_sub {a b : nat} (P : nat → Prop) (h₁ : nat_eq a b) (h₂ : P a) : P b :=
begin
  induction a using test.ind with a ih generalizing P b,
  { induction b using test.cs with b,
    { exact h₂ },
    { exact elim h₁ }},
  { specialize @ih (λ x, P (succ x)) (pred b),
    induction b using test.cs with b,
    { exact elim h₁ },
    { exact ih h₁ h₂ }},
end

theorem eq_symm {a b : nat} (h : nat_eq a b) : nat_eq b a :=
by apply eq_sub (λ x, nat_eq x a) h eq_refl

theorem eq_tran {a b c : nat} (h₁ : nat_eq a b) (h₂ : nat_eq b c) : nat_eq a c :=
by apply eq_sub _ (eq_symm h₁) h₂

end test