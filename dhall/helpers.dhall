let id
    : ∀(x : Type) → x → x
    = λ(t : Type) → λ(x : t) → x

let const
    : ∀(b : Type) → ∀(a : Type) → a → b → a
    = λ(r : Type) → λ(a : Type) → λ(x : a) → λ(y : r) → x

in  { id, const }
