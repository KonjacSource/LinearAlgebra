module Structures where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Level using (Level) renaming (suc to lsuc; zero to lzero)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Extensionality

private
  variable
    ℓ ℓ₁ : Level
    A : Set ℓ

record Field (F : Set ℓ) : Set ℓ where

  infixl 6 _+_
  infixl 7 _*_
  infix 9 -_
  infix 10 _⁻¹

  field
    _+_ : F → F → F
    _*_ : F → F → F

    0ᶠ  : F
    1ᶠ  : F
    
    -_  : F → F
    _⁻¹ : F → F

  
    +-assoc    : ∀ {a b c : F} → (a + b) + c ≡ a + (b + c)
    +-comm     : ∀ {a b   : F} → a + b ≡ b + a
    +-id       : ∀ {a     : F} → 0ᶠ + a ≡ a
    +-inv      : ∀ {a     : F} → - a + a ≡ 0ᶠ
    -1-inv     : ∀ {a     : F} → a * (- 1ᶠ) ≡ - a

    *-assoc    : ∀ {a b c : F} → (a * b) * c ≡ a * (b * c)
    *-comm     : ∀ {a b   : F} → a * b ≡ b * a
    *-id       : ∀ {a     : F} → 1ᶠ * a ≡ a
    *-inv      : ∀ {a     : F} → (a ≢ 0ᶠ) → a ⁻¹ * a ≡ 1ᶠ
    *-distri-+ : ∀ {k a b : F} → k * (a + b) ≡ k * a + k * b
open Field {{...}}

record VecSpc (V : Set ℓ) {F : Set ℓ} (Field-F : Field F) : Set ℓ where

  infixl 6 _⟨+⟩_
  infixl 7 _∙_
  infixl 9 -ᵛ_
  field 
    _⟨+⟩_ : V → V → V
    _∙_   : F → V → V

    0ᵛ    : V
    -ᵛ_   : V → V

    ⟨+⟩-comm     : ∀ {u v   : V} → u ⟨+⟩ v ≡ v ⟨+⟩ u
    ⟨+⟩-assoc    : ∀ {u v w : V} → u ⟨+⟩ v ⟨+⟩ w ≡ u ⟨+⟩ (v ⟨+⟩ w)
    ⟨+⟩-id       : ∀ {u     : V} → 0ᵛ ⟨+⟩ u ≡ u
    ⟨+⟩-inv      : ∀ {u     : V} → -ᵛ u ⟨+⟩ u ≡ 0ᵛ
 
    ∙-id         : ∀ {u     : V} → (Field.1ᶠ Field-F) ∙ u ≡ u
    ∙-distri-⟨+⟩ : ∀ {k : F} {u v : V} → k ∙ (u ⟨+⟩ v) ≡ k ∙ u ⟨+⟩ k ∙ v
    ∙-distri-+   : ∀ {a b : F} {v : V} → let _+_ = Field._+_ Field-F in (a + b) ∙ v ≡ a ∙ v ⟨+⟩ b ∙ v

data Vec (A : Set ℓ) : ℕ → Set ℓ where
  []  : Vec A zero
  _∷_ : ∀ {n : ℕ} → A → Vec A n → Vec A (suc n)

infix 10 _^_
_^_ : ∀ (A : Set ℓ) (n : ℕ) → Set ℓ
_^_ = Vec



-- 1.24 S → F 是向量空间
s→f : ∀(S : Set ℓ) {F : Set ℓ} {{f : Field F}} → VecSpc (S → F) {F = F} f
s→f S {F = F} = record -- V = S → F
  {  _⟨+⟩_       = λ u v s   → u s + v s
  ; _∙_          = λ k v s   → k * v s
  ; 0ᵛ           = λ s       → 0ᶠ
  ; -ᵛ_          = λ v s     → v s * (- 1ᶠ)
  ; ⟨+⟩-comm     = λ {u v}   → ∀-extensionality λ x → +-comm
  ; ⟨+⟩-assoc    = λ {u v w} → ∀-extensionality λ x → +-assoc
  ; ⟨+⟩-id       = λ {u}     → ∀-extensionality λ x → +-id
  ; ⟨+⟩-inv      = λ {u}     → ∀-extensionality (helper u)
  ; ∙-id         = λ {u}     → ∀-extensionality λ x → *-id
  ; ∙-distri-⟨+⟩ = λ {k u v} → ∀-extensionality λ x → *-distri-+
  ; ∙-distri-+   = λ {a b v} → ∀-extensionality (helper′ a b v) 
  }
  where
  helper : (u : S → F) → ∀ (x : S) → (u x) * (- 1ᶠ) + (u x) ≡ 0ᶠ
  helper u x rewrite -1-inv {a = u x} = +-inv {a = u x}

  helper′ : (a b : F) (v : S → F) → ∀ (x : S) → (a + b) * v x ≡ a * v x + b * v x
  helper′ a b v x
    rewrite *-comm {a = a + b} {b = v x}
          | *-comm {a = a}     {b = v x}
          | *-comm {a = b}     {b = v x}
          = *-distri-+


0*n≡0 : ∀ {F : Set ℓ} {{fld : Field F}} {n : F} → 0ᶠ * n ≡ 0ᶠ
0*n≡0 {n = n} =
  begin
    0ᶠ * n
  ≡⟨ cong (_* n) (sym (+-inv {a = 1ᶠ})) ⟩
    (- 1ᶠ + 1ᶠ) * n
  ≡⟨ *-comm ⟩
    n * (- 1ᶠ + 1ᶠ)
  ≡⟨ *-distri-+ ⟩
    n * (- 1ᶠ) + n * 1ᶠ
  ≡⟨ cong (_+ n * 1ᶠ) -1-inv ⟩
    (- n) + n * 1ᶠ
  ≡⟨ cong (- n +_) (trans *-comm *-id) ⟩
    (- n) + n
  ≡⟨ +-inv ⟩
    0ᶠ
  ∎
