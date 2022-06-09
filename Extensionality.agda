module Extensionality where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Level using (Level) renaming (suc to lsuc; zero to lzero)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C D E F : Set ℓ
  m n i j k l : ℕ

postulate
  ∀-extensionality : ∀ {A : Set ℓ} {B : A → Set ℓ₁} {f g : ∀(x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g

  ext : ∀ {A : Set ℓ} {B : Set ℓ₁} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g


record _×_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    proj₁ : A
    proj₂ : B
open _×_

curry : (A × B → C) → A → B → C
curry f x y = f ⟨ x , y ⟩

uncurry : (A → B → C) → (A × B → C)
uncurry f ⟨ x , y ⟩ = f x y



≡-curry : ∀ (f g : A → B → C) → uncurry f ≡ uncurry g → f ≡ g
≡-curry f g unf≡ung = ext λ x → ext λ y →
  cong (λ unfg → unfg ⟨ x , y ⟩ ) unf≡ung

Λ′-syntax = ext
infix 0 Λ′-syntax
syntax Λ′-syntax (λ x → y) = Λ′ x ⇒ y

ext₂ : ∀ {A B C : Set ℓ} {f g : A → B → C} → (∀ (x : A) (y : B) → f x y ≡ g x y) → f ≡ g
ext₂ fxy≡gxy = Λ′ x ⇒ Λ′ y ⇒ fxy≡gxy x y

Λ′₂-syntax = ext₂
infix 0 Λ′₂-syntax
syntax Λ′₂-syntax (λ x y → z) = Λ′ x y ⇒ z

ext₃ : ∀ {A B C D : Set ℓ} {f g : A → B → C → D} → (∀ (x : A) (y : B) (z : C) → f x y z ≡ g x y z) → f ≡ g
ext₃ fxyz≡gxyz = Λ′ x ⇒ Λ′ y z ⇒ fxyz≡gxyz x y z

Λ′₃-syntax = ext₃
infix 0 Λ′₃-syntax
syntax Λ′₃-syntax (λ x y z → w) = Λ′ x y z ⇒ w

ext₄ : ∀ {A B C D E : Set ℓ} {f g : A → B → C → D → E} → (∀ (x : A) (y : B) (z : C) (w : D)→ f x y z w ≡ g x y z w) → f ≡ g
ext₄ f≡g = Λ′ x ⇒ Λ′ y z w ⇒ f≡g x y z w

Λ′₄-syntax = ext₄
infix 0 Λ′₄-syntax
syntax Λ′₄-syntax (λ x y z w → r) = Λ′ x y z w ⇒ r


∀-ext : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : A → Set ℓ₂} → ∀ {f g : (x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g
∀-ext = ∀-extensionality

Λ-syntax = ∀-ext
infix 0 Λ-syntax
syntax Λ-syntax (λ x → eq) = Λ x ⇒ eq

∀-ext₂ : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (x : A) → B x → Set ℓ₃} →
       ∀ {f g : (x : A) → (y : B x) → C x y}
       → (∀ (x : A) (y : B x) → f x y ≡ g x y) → f ≡ g
∀-ext₂ fxy≡gxy = Λ x ⇒ Λ y ⇒ fxy≡gxy x y

Λ₂-syntax = ∀-ext₂
infix 0 Λ₂-syntax
syntax Λ₂-syntax (λ x y → eq) = Λ x y ⇒ eq

∀-ext₃ : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
       {A : Set ℓ₁}
       {B : A → Set ℓ₂}
       {C : (x : A) → B x → Set ℓ₃}
       {D : (x : A) → (y : B x) →  C x y → Set ℓ₄} →
       ∀ {f g : (x : A) → (y : B x) → (z : C x y) → D x y z}
       → (∀ (x : A) (y : B x) (z : C x y) → f x y z ≡ g x y z) → f ≡ g
∀-ext₃ eq =  Λ x y ⇒ Λ z ⇒ eq x y z

Λ₃-syntax = ∀-ext₃
infix 0 Λ₃-syntax
syntax Λ₃-syntax (λ x y z → eq) = Λ x y z ⇒ eq

∀-ext₄ : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level}
       {A : Set ℓ₁}
       {B : A → Set ℓ₂}
       {C : (x : A) → B x → Set ℓ₃}
       {D : (x : A) → (y : B x) → C x y → Set ℓ₄}
       {E : (x : A) → (y : B x) → (z : C x y) → D x y z → Set ℓ₅}→
       ∀ {f g : (x : A) → (y : B x) → (z : C x y) → (w : D x y z) → E x y z w}
       → (∀ (x : A) (y : B x) (z : C x y) (w : D x y z) → f x y z w ≡ g x y z w) → f ≡ g
∀-ext₄ eq =  Λ x y z ⇒ Λ w ⇒ eq x y z w

Λ₄-syntax = ∀-ext₄
infix 0 Λ₄-syntax
syntax Λ₄-syntax (λ x y z w → eq) = Λ x y z w ⇒ eq


