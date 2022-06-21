import Src.Prover.Pair

namespace prover
noncomputable section

def fn (A : Set) (f : Set → Set) : Set :=
image A # λ b => pair b (f b)

-- section open Lean
-- open Lean Elab Term
-- elab "FN " "(" x:term " ∈ " A:term ")" "," f:term : term =>
-- elabTermEnsuringType ``(fn `A (λ x => `f)) none
-- end

#exit

#check FN (x ∈ 1), x

def app (a b : Set) : Set :=
someu # λ c => pair b c ∈ a

theorem app_fn {A : Set} {f : Set → Set} {a : Set} : app (FN A x, f x) a = f a :=
_