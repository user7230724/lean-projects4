import Src.Prover.Logic

namespace prover
noncomputable section

axiom some {α : Type} {P : α → Prop} : (∃ (x : α), P x) → α
axiom some_spec {α : Type} {P : α → Prop} (h : ∃ (x : α), P x) : P (some h)