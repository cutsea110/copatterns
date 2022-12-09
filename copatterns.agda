{-# OPTIONS --sized-types #-}
module copatterns where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A
open Stream

record _≈_ {A : Set}(xs ys : Stream A) : Set where
  coinductive
  field
    hd-≈ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl ys
open _≈_

repeat : {A : Set} (a : A) → Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

triv : repeat 0 ≈ repeat 0
hd-≈ triv = refl
tl-≈ triv = triv

lemma : repeat 0 ≈ record { hd = 0 ; tl = repeat 0 }
hd-≈ lemma = refl
tl-≈ lemma = record { hd-≈ = refl ; tl-≈ = triv }

even : ∀ {A} → Stream A → Stream A
hd (even xs) = hd xs
tl (even xs) = even (tl (tl xs))

odd : ∀ {A} → Stream A → Stream A
odd xs = even (tl xs)

split : ∀ {A} → Stream A → Stream A × Stream A
split xs = even xs , odd xs

merge : ∀ {A} → Stream A × Stream A → Stream A
hd (merge (fst , snd)) = hd fst
tl (merge (fst , snd)) = merge (snd , tl fst)

merge-split-id : ∀ {A} (xs : Stream A) → merge (split xs) ≈ xs
hd-≈ (merge-split-id xs) = refl
tl-≈ (merge-split-id xs) = merge-split-id (tl xs)

open import Size
open import Codata.Thunk

data coℕ (i : Size) : Set where
  zero : coℕ i
  suc  : Thunk coℕ i → coℕ i

inf : ∀ {i} → coℕ i
inf = suc λ where .force → inf
-- same as this
-- inf = suc λ { .force → inf }

data Bool : Set where
  true : Bool
  false : Bool

and : Bool → Bool → Bool
and = λ { true x → x; false x → false }

or : Bool → Bool → Bool
or = λ where true x → true; false x → x

record Foo : Set where
  field
    x : ℕ
    y : ℕ

open Foo

foo : Foo → ℕ
-- foo record { x = x; y = y } = x + y
foo = λ { a → x a + y a }

ex1 : Foo
ex1 = record { x = 3 ; y = 4 }

ex1' : ℕ
ex1' = foo ex1
