module Structures.Properties where

open import Structures
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (+-comm)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)


open Field {{...}}

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C F : Set ℓ
  m n i j k l : ℕ

