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

lem : repeat 0 ≈ record { hd = 0 ; tl = repeat 0 }
hd-≈ lem = refl
tl-≈ lem = record { hd-≈ = refl ; tl-≈ = triv }

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
tl-≈ (merge-split-id xs) = record { hd-≈ = refl ; tl-≈ = {!!} }