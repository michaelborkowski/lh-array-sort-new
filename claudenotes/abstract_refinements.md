# Abstract Refinements in LiquidHaskell — a practical guide

A reference for the `forall <p :: ...>` mechanism: what it is, how to write it, what it
means, how LiquidHaskell instantiates it, and the traps that bite in practice.

Verified examples are drawn from this repo (`alloc`, `allocScratch` in `src/Array.hs`,
checked with liquidhaskell 0.9.10.1, GHC 9.10.1, `--reflection --ple`). Canonical idioms
(lists, `foldr`, `compose`) are standard LH from Vazou et al., *Abstract Refinement Types*
(ESOP 2013) and the LH tutorial; they are labelled as such.

---

## Contents

1. [What problem they solve](#1-what-problem-they-solve)
2. [Declaring an abstract refinement](#2-declaring-an-abstract-refinement)
3. [Applying one: the `t<...>` syntax](#3-applying-one-the-t-syntax)
4. [Semantics: what `t<p>` desugars to](#4-semantics-what-tp-desugars-to)
5. [Abstract refinements in data types](#5-abstract-refinements-in-data-types)
6. [The tuple/pair encoding (read this)](#6-the-tuplepair-encoding-read-this)
7. [How LH instantiates `p` (inference)](#7-how-lh-instantiates-p-inference)
8. [Core usage patterns](#8-core-usage-patterns)
9. [Bounds: composing abstract refinements](#9-bounds-composing-abstract-refinements)
10. [Pitfalls & gotchas](#10-pitfalls--gotchas)
11. [Case study: `allocScratch`](#11-case-study-allocscratch)
12. [Cheat sheet](#12-cheat-sheet)

---

## 1. What problem they solve

A normal refinement type fixes a *concrete* predicate: `{v:Int | v > 0}`. An **abstract
refinement** lets a type or function be *polymorphic over the predicate itself* — you
quantify over an unknown refinement `p` and let each call site choose it. This is to
refinements what parametric polymorphism is to types.

The payoff: you write one reusable spec whose postcondition adapts to the caller. The
classic motivating example is `max`:

```haskell
{-@ max :: forall <p :: Int -> Bool>. Int<p> -> Int<p> -> Int<p> @-}
max x y = if x >= y then x else y
```

If both inputs satisfy *any* property `p` (being positive, being even, being prime…), so
does the output — without writing a spec per property. LH picks `p` at each use.

---

## 2. Declaring an abstract refinement

Quantify with `forall <name :: sort>` at the front of a spec. The "sort" is a function
type ending in `Bool`:

```haskell
{-@ f :: forall <p :: a -> Bool>. ... @-}              -- unary predicate on an a
{-@ g :: forall <p :: a -> b -> Bool>. ... @-}         -- binary relation
{-@ h :: forall <p :: a -> a -> Bool, q :: a -> Bool>. ... @-}   -- several at once
```

- The arguments to `p` are *value* sorts (the logical sort of an `a`, an `Int`, an
  `Array a`, etc.), and the result is always `Bool`.
- Multiple refinements are comma-separated inside one `< >`.
- The names live for the rest of that one signature.

Real examples from this repo (`src/Array.hs`):

```haskell
{-@ alloc :: forall <p :: Ur b -> Bool>. n:Nat -> x:_
              -> f:({ ys:(Array a) | size ys == n && left ys == 0 && right ys == n }
                          -> Ur<p> b) -> ret:Ur<p> b @-}

{-@ allocScratch :: forall <p :: Array a -> Array a -> Bool>. n:Nat -> x:_ -> ... @-}
```

---

## 3. Applying one: the `t<...>` syntax

You **apply** an abstract refinement by attaching `<...>` to a type constructor:

```haskell
a<p>          -- {v:a | p v}                       (p unary)
Ur<p> b       -- {v:(Ur b) | p v}                  (<...> goes on the head ctor; args follow)
[a]<p>        -- a list whose elements are <p>-related (see §5)
```

You can also **partially apply** a higher-arity refinement in the same position:

```haskell
Array<p xs> a -- {v:(Array a) | p xs v}            (p binary, first arg fixed to xs)
b<p y>        -- {v:b | p y v}
c<r x>        -- {v:c | r x v}
```

This partial-application-via-`<...>` is the *only* officially supported way to apply an
abstract-refinement variable inside a type. **Do not** write a bare `p xs v` inside an
ordinary refinement predicate — see [§10](#10-pitfalls--gotchas).

You can layer an extra ordinary refinement on top of a `<...>`-refined base type:

```haskell
{zs:(Array<p xs> a) | token zs == token xs && size zs == size xs}
-- {v:(Array a) | p xs v && token v == token xs && size v == size xs}
```

---

## 4. Semantics: what `t<p>` desugars to

`t<p>` is sugar for `{v:t | p ... v}`. For a unary `p`, `a<p>` is literally `{v:a | p v}`.
`p` is an uninterpreted predicate symbol in the logic until it is instantiated.

Two ends of every abstract refinement:

- **Covariant (output) position** — e.g. the result `ret:Ur<p> b`. Here LH must *prove*
  `p ret`. Because `p` is abstract, the proof has to come from somewhere upstream (an
  argument typed `<p>`). This is how a property is *propagated*.
- **Contravariant (input) position** — e.g. an argument `x:a<p>`. Here LH may *assume*
  `p x`. This is how a property is *consumed*.

When a function both consumes `<p>` on an argument and produces `<p>` on its result, it
becomes a *conduit*: whatever `p` the caller picks flows through. That is the essence of
`max` and of `alloc`.

---

## 5. Abstract refinements in data types

A datatype can be parameterized by a refinement that relates its fields. The canonical
example is the LH list (built in):

```haskell
{-@ data [] a <p :: a -> a -> Bool>
      = [] | (:) { h :: a, t :: [a<p h>]<p> } @-}
```

Reading the `Cons` field `t :: [a<p h>]<p>`:

- every element `v` of the tail satisfies `a<p h>`, i.e. `p h v` — the head is related to
  **every** later element; and
- the tail is itself `<p>`-refined, recursively.

So `[a]<p>` is a list in which `p x y` holds for **every** pair where `x` precedes `y`
(not just adjacent ones). Hence:

```haskell
{-@ type IncrList a = [a]<{\x y -> x <= y}> @-}   -- sorted ascending
{-@ type DecrList a = [a]<{\x y -> x >= y}> @-}   -- sorted descending
{-@ type UniqList a = [a]<{\x y -> x /= y}> @-}   -- all-distinct
```

and a sort can advertise its result shape with one alias:

```haskell
{-@ insertSort :: Ord a => [a] -> IncrList a @-}
```

The `\x y -> ...` between `< >` is an **anonymous concrete refinement** supplied for the
datatype's abstract parameter — i.e. you *instantiate* `p` by writing the lambda inline.

---

## 6. The tuple/pair encoding (read this)

The 2-tuple carries an abstract refinement that relates its two components. Conceptually:

```haskell
data (,)<p :: a -> b -> Bool> a b = (,) { fst :: a, snd :: b<p fst> }
```

So writing

```haskell
(Array a, Array a)<{\zs ts -> toBag xs == toBag zs && isSorted' zs && right ts == right ys}>
```

means a pair `(zs, ts)` for which that body holds. **Crucially, LH attaches the whole
relation to the *second* field, referencing the first.** The first component is left bare
(`Array a`, no refinement of its own); everything — including facts that are *about* `zs`
like `isSorted' zs` — lives in `snd`'s refinement.

Practical consequences (both confirmed in this repo):

- On an **un-deconstructed** pair `tup`, projecting `fst tup` recovers *nothing* beyond the
  bare component type. A spec that reads guarantees back via `... (fst tup) ...` will fail
  even though they "are in" the pair refinement — they are syntactically on `snd`.
- You only get the relation by **pattern-matching** the pair (`let (zs, ts) = tup`), which
  introduces `ts` with its refinement (which mentions `zs`).
- If you need the *first* component's facts to be visible on the component itself (e.g. to
  let an abstract refinement on that component be inferred), prefer a **component-refined
  tuple** over a pair abstract refinement:

  ```haskell
  -- pair abstract refinement: facts land on snd, fst is bare
  (Array a, Array a)<{\zs ts -> P zs && Q ts}>

  -- component-refined tuple: each field carries its own refinement
  ( {zs:Array a | P zs}, {ts:Array a | Q ts} )
  ```

  These are interchangeable **only** when the relation factors with no cross-component
  conjunct (no term mentions both `zs` and `ts`). When it factors, the component form is
  friendlier to inference. (This is exactly the change that fixed `allocScratch`; see §11.)

---

## 7. How LH instantiates `p` (inference)

At a use site, `p` becomes a **Horn/refinement variable** (a `κ`) that LH solves by liquid
type inference:

1. **Constraints.** Each covariant occurrence yields an *upper bound* (`κ` must imply the
   goal); each contravariant occurrence / argument yields a *lower bound* (`κ` must be
   implied by what the argument guarantees). LH seeks a `κ` between them.
2. **Qualifiers.** Candidate conjuncts for `κ` are drawn from the *qualifier set*: predicate
   templates scraped from the program's specs (and imports, with `--scrape-imports`), plus
   any `{-@ qualif ... @-}` you declare. If the conjunct you need (say `toBag x == toBag y`)
   never appears as a qualifier, LH cannot conjure it.
3. **Matching against the argument.** When you pass a function whose result is `<p>`-typed,
   LH reads `p` off that argument's declared type. The shapes must line up — if the
   argument states its facts on a component LH isn't looking at (the `snd`-encoding issue),
   inference comes up empty.

**The silent-weakening trap.** If LH can find *no* useful instantiation it does not always
error — it may solve `κ := True` (the weakest refinement) and move on. The signature still
"type-checks" at that spot, but the propagated postcondition is empty, and the error
surfaces *later* where the result is actually used. When an abstract refinement "isn't
doing anything", suspect `κ := True`.

---

## 8. Core usage patterns

### 8a. Propagate a postcondition through a combinator (the `alloc` pattern)

`p` on an argument's result *and* on the combinator's result makes the combinator transparent
to whatever the argument guarantees:

```haskell
{-@ alloc :: forall <p :: Ur b -> Bool>. n:Nat -> x:_
              -> f:({ys:(Array a) | size ys == n && left ys == 0 && right ys == n} -> Ur<p> b)
              -> ret:Ur<p> b @-}
alloc i a f = f (make i a)
```

Whatever postcondition `p` the caller's `f` establishes on its `Ur b` result, `alloc`
republishes on `ret`. `alloc` itself never mentions sortedness, bags, etc. — so it can live
in `Array.hs` even though those measures are defined in modules that *import* `Array`.

### 8b. Relate input to output (use a *binary* `p`)

A *unary* `p :: T -> Bool` can only state intrinsic facts about one value. To propagate a
relation between an input and an output (e.g. "same multiset"), make `p` **binary** and apply
it with the input fixed:

```haskell
forall <p :: Array a -> Array a -> Bool>.
   ... f:(... -> ({zs:Array<p xs> a | ...}, ...))    -- guarantees p xs zs
   ... -> {dst:Array<p src> a | ...}                 -- republishes p src dst
```

At the call site LH infers a **closed** relation such as
`p := \x z -> toBag x == toBag z && isSorted' z` (it mentions only its own parameters), so
there is no scoping problem. A unary `p` cannot express this, because the "input side" of
the relation is bound inside `f` and is out of scope where `p` is instantiated. (See §10
and §11.)

### 8c. Inductive invariants (the `foldr` pattern, canonical LH)

`p` can relate "the part of the structure consumed so far" to an accumulator:

```haskell
{-@ foldr :: forall <p :: [a] -> b -> Bool>.
       (xs:[a] -> x:a -> b<p xs> -> b<p (x:xs)>)   -- step preserves the invariant
    -> b<p []>                                      -- base establishes it
    -> ys:[a]
    -> b<p ys> @-}                                  -- result holds it for the whole list
```

Instantiating `p` recovers strong results (e.g. that `foldr (:) []` is the identity, or
length facts) from one generic spec.

---

## 9. Bounds: composing abstract refinements

Sometimes the relationship between several abstract refinements can't be inferred and must
be *assumed* as a side condition. LH provides **bounds** — Horn constraints over the
refinement variables — written with `|-` ("entails") at the front of the spec. The textbook
case is function composition (canonical LH):

```haskell
{-@ compose :: forall <p :: b -> c -> Bool, q :: a -> b -> Bool, r :: a -> c -> Bool>.
       {x::a, w::b<q x> |- c<p w> <: c<r x>}
       (y:b -> c<p y>) -> (z:a -> b<q z>) -> x:a -> c<r x> @-}
compose f g x = f (g x)
```

Read the bound `{x::a, w::b<q x> |- c<p w> <: c<r x>}` as: *for all `x` and any `w` with
`q x w`, the type `c<p w>` is a subtype of `c<r x>`* — i.e. `q x w => p w v => r x v`. That
is precisely what's needed to chain `g`'s guarantee (`q`) and `f`'s guarantee (`p`) into the
result guarantee (`r`).

Bounds may also be declared and named with `{-@ bound ... @-}` and referenced like a class
constraint; the inline `|-` form above is the most self-contained. Bounds are an advanced
feature — reach for them only when plain instantiation can't connect the refinements.

---

## 10. Pitfalls & gotchas

Hard-won, several confirmed against liquidhaskell 0.9.10.1 in this repo.

- **Bare application is "Unbound symbol p".** Inside an ordinary refinement predicate you
  *cannot* write the abstract variable applied directly:

  ```haskell
  -- ✗ rejected: "Unbound symbol p --- perhaps you meant: x, n ?"
  -> (Array a, Array a)<{\zs ts -> p xs zs && ...}>

  -- ✓ apply through the type: partial application in <...> position
  -> ({zs:Array<p xs> a | ...}, ...)
  ```

  Apply abstract refinements only via the `t<...>` syntax (`Array<p xs>`, `b<q x>`, …). The
  one place you write the relation out longhand is a `bound` definition (§9).

- **The pair refinement lands on `snd`** (§6). Reading guarantees back through `fst tup`
  fails; either pattern-match, or use a component-refined tuple.

- **A unary `p` can't relate input to output through a HOF** (§8b). The input is bound
  inside the function argument and isn't in scope at the instantiation site, so a closed
  unary `p` can never mention it. Use a binary `p` applied with the input fixed.

- **Silent `κ := True`** (§7). A "successful" check at the abstract-refinement site can
  still propagate nothing; the failure appears downstream.

- **Type-variable sorts must line up.** An abstract refinement's argument sorts are fixed
  by its declaration. `p :: Array dsts -> Bool` cannot mention `toBag xs :: BBag srcs` when
  `srcs` and `dsts` are *distinct* type variables — the sorts don't match. If a single
  concrete type is intended at every use, declare it with one type variable rather than
  several, so relations across the arguments are expressible.

- **Module layering forces abstraction.** If `Module A` defines a combinator but the
  measures you want to propagate (`toBag`, `isSorted'`) live in modules that *import* `A`,
  `A` can't name them. An abstract `p` is the way to stay generic across that boundary — and
  the instantiation (which *does* mention the measures) happens in the importing module,
  where they're in scope.

- **`<...>` parsing.** Use `&&`/`||`/`==>` inside the lambda body, not single `&`/`|`.
  Keep the metric annotation outside the type: `( {zs|...}, {ts|...} ) / [size xs]`.

---

## 11. Case study: `allocScratch`

`allocScratch i a f arr` runs an in-place sort `f` (which sorts `arr` using a freshly
allocated scratch buffer), then frees the scratch and returns the sorted array. We want the
result to inherit `f`'s guarantee `toBag arr == toBag dst && isSorted' dst`, but `Array.hs`
can't name `toBag`/`isSorted'` (they live in `Properties.*`, which import `Array`). So the
guarantee must ride on an abstract `p`.

**The version that failed** used a unary `p :: Array dsts -> Bool`, four distinct type
variables, and read `f`'s result via `fst tup`/`snd tup`:

```haskell
{-@ allocScratch :: forall <p :: Array dsts -> Bool>. n:Nat -> x:_
      -> f:({xs:_ | size xs == n} -> {ys:_ | size ys == n}
              -> { tup:(Array<p> dsts, Array tmpdsts) |
                      token (fst tup) == token xs && ... && right (fst tup) == right xs && ... })
      -> {src:_ | size src == n} -> { dst:Array<p> dsts | token src == token dst } @-}
```

It hit *both* central traps:

1. `f`'s guarantees came from a **pair abstract refinement** on the sort's side, so they sat
   on `snd`; reading `right (fst tup) == right xs` off the bare `fst` was unprovable.
2. A **unary** `p` couldn't carry `toBag xs == toBag zs` (input↔output) — so `p` collapsed
   to `True` and the result lost `toBag`/`isSorted'`.

**The fix** (now `LIQUID: SAFE`, `src/Array.hs`):

```haskell
{-@ allocScratch :: forall <p :: Array a -> Array a -> Bool>. n:Nat -> x:_
      -> f:({xs:_ | size xs == n && left xs == 0 && right xs == n }
              -> { ys:_ | size ys == n && left ys == 0 && right ys == n }
              -> ( {zs:(Array<p xs> a) | token zs == token xs && size zs == size xs &&
                                         left zs == left xs && right zs == right xs}
                 , {ts:(Array a) | token ts == token ys && size ts == size ys &&
                                   left ts == left ys && right ts == right ys} ))
      -> { src:_ | size src == n && left src == 0 && right src == n }
      -> { dst:(Array<p src> a) | token src == token dst &&
                      size src == size dst && left src == left dst && right src == right dst } @-}
```

What each change buys, mapped to the rules above:

- **binary `p`, applied as `Array<p xs>` / `Array<p src>`** — §8b + the "apply via `<...>`"
  rule. Captures the input↔output relation; LH infers the closed
  `p := \x z -> toBag x == toBag z && isSorted' z`.
- **component-refined tuple instead of a pair abstract refinement** — §6. Puts `zs`'s facts
  on `zs`'s own component so `p` is inferable (the sort's relation factors cleanly across
  `zs`/`ts`, so this is sound). The sort modules' `msortInplace`/`go` were switched to the
  same component-refined return shape to match.
- **one type variable `a`** — fixes the cross-sort issue so the relation is expressible.
- **`left = 0, right = n` bounds** — discharge the sort's tmp precondition
  `left xs == left ys && right xs == right ys` (the `makeArray` scratch is always `0..n`).

---

## 12. Cheat sheet

```haskell
-- DECLARE
forall <p :: a -> Bool>.            -- unary predicate
forall <p :: a -> b -> Bool>.       -- binary relation
forall <p :: ..., q :: ...>.        -- several

-- APPLY (only through <...> ; never a bare  p x v  in a predicate)
a<p>             -- {v:a | p v}
Ur<p> b          -- {v:Ur b | p v}
Array<p xs> a    -- {v:Array a | p xs v}     (partial application)
[a]<{\x y->x<=y}>-- instantiate a datatype's abstract param with a lambda

-- PROPAGATE  (conduit: consume <p> on input, produce <p> on output)
f:(... -> Ur<p> b) -> Ur<p> b

-- RELATE input↔output  -> binary p, fix the input
f:(... -> {z:T<p x> | ...}) -> {out:T<p src> | ...}

-- DATATYPE relation (refinement lands on later fields)
{-@ data [] a <p :: a -> a -> Bool> = [] | (:) { h::a, t::[a<p h>]<p> } @-}

-- BOUND (assume a relationship between refinements)
{x::a, w::b<q x> |- c<p w> <: c<r x>}

-- REMEMBER
-- * pair (a,b)<\zs ts -> R> puts R on snd; fst is bare until you pattern-match
-- * un-inferable p quietly becomes True; the error shows up downstream
-- * argument sorts of p are fixed at declaration — keep type vars consistent
-- * abstract p lets a low-layer module stay generic over measures it can't import
```

---

*Companion note: `claudenotes/abstract.md` walks through the original `allocScratch`
failure and fix in detail.*
