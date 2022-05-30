inductive T
| z : T
| s : T → T

def f : Nat → T
| 0 => T.z
| (n+1) => T.s (f n)

instance {n : Nat} : OfNat T n where
  ofNat := f n

instance : CoeSort T Prop where
  coe := fun
  | 1 => True
  | _ => False

-- example {n : T} (P : T → Prop) (h₁ : n) (h₂ : P 1) : P n := by
--   match n with
--   | 1 => exact h₂
--   | _ => cases h₁