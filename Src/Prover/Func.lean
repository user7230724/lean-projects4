import Src.Prover.Pair

namespace prover
noncomputable section

def fn (A : Set) (f : Set → Set) : Set :=
image A # λ b => pair b (f b)

section open Lean
macro "FN " "(" a:explicitBinders "∈" b:term ")" "," f:term : term =>
expandExplicitBinders ``id a f >>= λ v => `(fn $b $v) end

def app (f a : Set) : Set :=
someu # λ b => pair a b ∈ f

infixl:100 (priority := high) " ~ " => app

theorem exiu_fn_ret {A : Set} {f : Set → Set} {a : Set} (h : a ∈ A) :
  ∃! b, pair a b ∈ FN (x ∈ A), f x :=
exiu_intro (f a) (mpr mem_image # exi_intro a # and_intro h rfl)
(λ b h₁ => exi_elim (mp mem_image h₁) # λ c h₂ =>
and_elim (mp pair_ext # and_right h₂) # λ h₃ h₄ =>
eq_rec (λ x => b = f x) h₃ # eq_symm h₄)

theorem fn_app {A : Set} {f : Set → Set} {a : Set} (h : a ∈ A) :
  (FN (x ∈ A), f x) ~ a = f a :=
hv (@someu_spec _ _ (λ b => pair a b ∈ FN (x ∈ A), f x) # exiu_fn_ret h) #
λ h₁ => exi_elim (mp mem_image h₁) # λ x h₂ =>
and_elim (mp pair_ext # and_right h₂) # λ h₃ h₄ =>
eq_rec (λ x => fn A f ~ a = f x) h₃ # eq_symm h₄