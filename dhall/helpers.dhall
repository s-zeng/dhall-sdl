let compose
    : ∀(r : Type) → ∀(a : Type) → ∀(b : Type) → (a → b) → (r → a) → r → b
    = λ(r : Type) →
      λ(a : Type) →
      λ(b : Type) →
      λ(f : a → b) →
      λ(g : r → a) →
      λ(x : r) →
        f (g x)

let id
    : ∀(x : Type) → x → x
    = λ(t : Type) → λ(x : t) → x

let const
    : ∀(b : Type) → ∀(a : Type) → a → b → a
    = λ(r : Type) → λ(a : Type) → λ(x : a) → λ(y : r) → x

let fac
    : ∀(n : Natural) → Natural
    = λ(n : Natural) →
        let factorial =
              λ(f : Natural → Natural → Natural) →
              λ(n : Natural) →
              λ(i : Natural) →
                if Natural/isZero i then n else f (i * n) (Natural/subtract 1 i)

        in  Natural/fold
              n
              (Natural → Natural → Natural)
              factorial
              (const Natural Natural)
              1
              n

let fib
    : ∀(n : Natural) → Natural
    = λ(n : Natural) →
        let fibFunc = Natural → Natural → Natural → Natural

        let fibonacci =
              λ(f : fibFunc) →
              λ(a : Natural) →
              λ(b : Natural) →
              λ(i : Natural) →
                if    Natural/isZero i
                then  a
                else  f b (a + b) (Natural/subtract 1 i)

        in  Natural/fold
              n
              fibFunc
              fibonacci
              (λ(a : Natural) → λ(_ : Natural) → λ(_ : Natural) → a)
              0
              1
              n

in  { id, const, compose, fac, fib }
