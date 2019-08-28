-- | ref.) https://gist.github.com/gallais/e0e2597fa3393f6b12d7c35361d0d74f
-- | thread : https://stackoverflow.com/questions/55347900/agda-simplifying-recursive-definitions-involving-thunk
open import Size
open import Codata.Thunk

data BinaryTreePath (i : Size) : Set where
  here : BinaryTreePath i
  branchL : Thunk BinaryTreePath i → BinaryTreePath i
  branchR : Thunk BinaryTreePath i → BinaryTreePath i

zero : ∀ {i} → BinaryTreePath i
zero = branchL λ where .force → zero

infinity : ∀ {i} → BinaryTreePath i
infinity = branchR λ where .force → infinity

data Choice : Set where
  L R : Choice

choice : ∀ {i} → Choice → Thunk BinaryTreePath i → BinaryTreePath i
choice L t = branchL t
choice R t = branchR t

open import Data.List
open import Data.List.NonEmpty

_<|_ : ∀ {i} → List Choice → BinaryTreePath i → BinaryTreePath i
[] <| t       = t
(c ∷ cs) <| t = choice c (λ where .force → cs <| t)

_⁺<|_ : ∀ {i} → List⁺ Choice → Thunk BinaryTreePath i → BinaryTreePath i
(c ∷ cs) ⁺<| t = choice c (λ where .force → cs <| t .force)

cycle : ∀ {i} → List⁺ Choice → BinaryTreePath i
cycle cs = cs ⁺<| λ where .force → cycle cs

sqrt2 : ∀ {i} → BinaryTreePath i
sqrt2 = cycle (L ∷ R ∷ R ∷ L ∷ [])
