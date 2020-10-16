let t = ./types.dhall

let h = ./helpers.dhall

let makeMonad
    : ∀(m : Type → Type) → t.Unit m → t.Map m → t.Join m → t.Monad m
    = λ(m : Type → Type) →
      λ(return : t.Unit m) →
      λ(map : t.Map m) →
      λ(join : t.Join m) →
        let bind =
              λ(a : Type) →
              λ(b : Type) →
              λ(l : m a) →
              λ(f : a → m b) →
                join b (map a (m b) f l)

        let ap =
              λ(a : Type) →
              λ(b : Type) →
              λ(fs : m (a → b)) →
              λ(xs : m a) →
                bind
                  (a → b)
                  b
                  fs
                  (λ(f : a → b) → bind a b xs (λ(x : a) → return b (f x)))

        in  { return, map, bind, ap, join }

let makeMonad3 =
      λ(m : Type → Type → Type) →
      λ(return : ∀(r : Type) → t.Unit (m r)) →
      λ(map : ∀(r : Type) → t.Map (m r)) →
      λ(join : ∀(r : Type) → t.Join (m r)) →
      λ(r : Type) →
        makeMonad (m r) (return r) (map r) (join r)

let eunit
    : ∀(e : Type) → t.Unit (t.Either e)
    = λ(e : Type) → λ(a : Type) → (t.Either e a).Right

let emap
    : ∀(e : Type) → t.Map (t.Either e)
    = λ(e : Type) →
      λ(a : Type) →
      λ(b : Type) →
      λ(f : a → b) →
      λ(xs : t.Either e a) →
        let either = t.Either e b

        in  merge
              { Left = either.Left, Right = λ(x : a) → either.Right (f x) }
              xs

let ejoin
    : ∀(e : Type) → t.Join (t.Either e)
    = λ(e : Type) →
      λ(a : Type) →
      λ(xs : t.Either e (t.Either e a)) →
        let either = t.Either e a

        in  merge { Left = either.Left, Right = h.id either } xs

let lunit
    : t.Unit List
    = λ(a : Type) → λ(x : a) → [ x ]

let lmap
    : t.Map List
    = λ(a : Type) →
      λ(b : Type) →
      λ(f : a → b) →
      λ(xs : List a) →
        List/build
          b
          ( λ(list : Type) →
            λ(cons : b → list → list) →
              List/fold a xs list (λ(x : a) → cons (f x))
          )

let ljoin
    : t.Join List
    = λ(a : Type) →
      λ(l : List (List a)) →
        List/fold
          (List a)
          l
          (List a)
          (λ(x : List a) → λ(y : List a) → x # y)
          ([] : List a)

let ounit
    : t.Unit Optional
    = λ(a : Type) → λ(x : a) → Some x

let omap
    : t.Map Optional
    = λ(a : Type) →
      λ(b : Type) →
      λ(f : a → b) →
      λ(xs : Optional a) →
        merge { None = None b, Some = λ(x : a) → Some (f x) } xs

let ojoin
    : t.Join Optional
    = λ(a : Type) →
      λ(l : Optional (Optional a)) →
        merge { None = None a, Some = λ(x : Optional a) → x } l

let funcunit
    : ∀(r : Type) → t.Unit (t.Function r)
    = h.const

let funcmap
    : ∀(r : Type) → t.Map (t.Function r)
    = λ(r : Type) →
      λ(a : Type) →
      λ(b : Type) →
      λ(f : a → b) →
      λ(g : r → a) →
      λ(x : r) →
        f (g x)

let funcjoin
    : ∀(r : Type) → t.Join (t.Function r)
    = λ(r : Type) → λ(a : Type) → λ(f : r → r → a) → λ(x : r) → f x x

let optMonad
    : t.Monad Optional
    = makeMonad Optional ounit omap ojoin

let listMonad
    : t.Monad List
    = makeMonad List lunit lmap ljoin

let funcMonad
    : ∀(r : Type) → t.Monad (t.Function r)
    = makeMonad3 t.Function funcunit funcmap funcjoin

let eMonad
    : ∀(e : Type) → t.Monad (t.Either e)
    = makeMonad3 t.Either eunit emap ejoin

let monads =
      { Function = funcMonad
      , Either = eMonad
      , Optional = optMonad
      , List = listMonad
      }

in  monads
