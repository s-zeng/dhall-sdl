let Map
    : (Type → Type) → Type
    = λ(f : Type → Type) → ∀(a : Type) → ∀(b : Type) → (a → b) → f a → f b

let Unit
    : (Type → Type) → Type
    = λ(m : Type → Type) → ∀(a : Type) → a → m a

let Join
    : (Type → Type) → Type
    = λ(m : Type → Type) → ∀(a : Type) → m (m a) → m a

let Bind
    : (Type → Type) → Type
    = λ(m : Type → Type) → ∀(a : Type) → ∀(b : Type) → m a → (a → m b) → m b

let Ap
    : (Type → Type) → Type
    = λ(f : Type → Type) → ∀(a : Type) → ∀(b : Type) → f (a → b) → f a → f b

let Monad
    : (Type → Type) → Type
    = λ(m : Type → Type) →
        { bind : Bind m
        , return : Unit m
        , map : Map m
        , ap : Ap m
        , join : Join m
        }

let Function
    : Type → Type → Type
    = λ(r : Type) → λ(b : Type) → r → b

let Either
    : Type → Type → Type
    = λ(a : Type) → λ(b : Type) → < Left : a | Right : b >

let types = { Map, Unit, Join, Bind, Ap, Monad, Function, Either }

in  types
