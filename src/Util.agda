module Util where

open import Structures
open import Structures.Properties
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; sym)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
-- open import Data.Nat.Properties using (+-comm)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Extensionality
open Field {{...}}

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C D E F : Set ℓ
  m n i j k l : ℕ

infixr 20 _∘_
_∘_ : ∀ {ℓ} {A B C : Set ℓ} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

-- 依赖类型apply
infixr -20 _$_
_$_ : ∀ {A : Set ℓ} {B : A → Set ℓ} → (∀ (x : A) → B x) → ∀ (y : A) → B y
f $ x = f x

id : ∀ {ℓ : Level} {A : Set ℓ} → A → A
id x = x
   
infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  z<s : zero  < suc n
  s<s : m < n → suc m < suc n
  
n<sn : ∀ {n : ℕ} → n < suc n
n<sn {n = zero}  = z<s
n<sn {n = suc n} = s<s n<sn


m<sn : m < n → m < suc n
m<sn {m = zero}  _          = z<s
m<sn {m = suc m} (s<s m<n⁻) = s<s (m<sn m<n⁻)

infix 4 _≤_ 
data _≤_ : ℕ → ℕ → Set where
  <→≤ : ∀ {a b : ℕ} → a < b → a ≤ b
  ≡→≤ : ∀ {a b : ℕ} → a ≡ b → a ≤ b

sigma-< : {F : Set ℓ} {{fld : Field F}} → (n : ℕ) → ((i : ℕ) → i < n → F) → F
sigma-< zero    _ = 0ᶠ
sigma-< (suc i) f = f i n<sn + sigma-< i (λ i′ i′<i → f i′ (m<sn i′<i))

syntax sigma-< n (λ i i<n → fᵢ) = Σ[ i < n , i<n ] fᵢ

infixr 5 _∷_
data Vect {ℓ : Level} : ℕ → Set ℓ → Set ℓ where
  []  : {A : Set ℓ} → Vect zero A
  _∷_ : {A : Set ℓ} → A → Vect n A → Vect (suc n) A


-- 按索引取Vect中的元素, 要在⟦⟧中提供小于证明
infix 9 _!_⟦_⟧
_!_⟦_⟧ : Vect n A → ∀ (m : ℕ) → m < n → A
(x ∷ _)  ! zero  ⟦ z<s     ⟧ = x
(_ ∷ xs) ! suc m ⟦ s<s m<n ⟧ = xs ! m ⟦ m<n ⟧

_ : (5 ∷ 3 ∷ 2 ∷ []) ! 1 ⟦ s<s z<s ⟧ ≡ 3
_ = refl

Table : ℕ → ℕ → Set ℓ → Set ℓ
Table m n A = Vect m (Vect n A)

_-_⟨_⟩ : (i j : ℕ) → j ≤ i → ℕ
_-_⟨_⟩ i       j       (≡→≤ _)       = zero
_-_⟨_⟩ (suc i) zero    (<→≤ _)       = suc i
_-_⟨_⟩ (suc i) (suc j) (<→≤ (s<s p)) = i - j ⟨ <→≤ p ⟩


pred : (n : ℕ) → zero < n → ℕ
pred (suc n) z<s = n

-- 向量点积
infix 20 ⟨_∙_⟩
⟨_∙_⟩ : {F : Set ℓ} {{fld : Field F}} → Vect m F → Vect m F → F
⟨ []     ∙ []     ⟩ = 0ᶠ
⟨ a ∷ as ∙ b ∷ bs ⟩ = a * b + ⟨ as ∙ bs ⟩


Σ0≡0 : {F : Set ℓ} {{fld : Field F}} → ∀ {n : ℕ} → Σ[ i < n , i<n ] 0ᶠ ≡ 0ᶠ
Σ0≡0 {n = 0}     = refl
Σ0≡0 {n = suc n} =
  begin
    0ᶠ + Σ[ i < n , i<n ] 0ᶠ
  ≡⟨ +-id ⟩
    Σ[ i < n , i<n ] 0ᶠ
  ≡⟨ Σ0≡0 {n = n} ⟩
    0ᶠ
  ∎

-- Σ 有分配律
Σ-distri-+ : {F : Set ℓ} {{fld : Field F}} →
         ∀ {n : ℕ} (f g : (i : ℕ) → i < n → F)
         → sigma-< n (λ i i<n → f i i<n + g i i<n) ≡ sigma-< n f + sigma-< n g
Σ-distri-+ {n = 0}     f g rewrite +-id {a = 0ᶠ} = refl
Σ-distri-+ {n = suc n} f g =
  begin
    f n n<sn + g n n<sn + Σ[ i < n , i<n ] (f i (m<sn i<n) + g i (m<sn i<n))
  ≡⟨ cong ((f n n<sn + g n n<sn) +_) (Σ-distri-+ {n = n} (λ i i<n → f i (m<sn i<n)) (λ i i<n → g i (m<sn i<n)))⟩
    (f n n<sn + g n n<sn) + ((Σ[ i < n , i<n ] f i (m<sn i<n)) + (Σ[ i < n , i<n ] g i (m<sn i<n)))
  ≡⟨ sym (+-assoc {a = f n n<sn + g n n<sn} {b = Σ[ i < n , i<n ] f i (m<sn i<n)} {c = Σ[ i < n , i<n ] g i (m<sn i<n)}) ⟩
    f n n<sn + g n n<sn + (Σ[ i < n , i<n ] f i (m<sn i<n)) + (Σ[ i < n , i<n ] g i (m<sn i<n))
  ≡⟨ helper (f n n<sn) (g n n<sn) (Σ[ i < n , i<n ] f i (m<sn i<n)) (Σ[ i < n , i<n ] g i (m<sn i<n)) ⟩
    (f n n<sn + (Σ[ i < n , i<n ] f i (m<sn i<n))) + (g n n<sn + (Σ[ i < n , i<n ] g i (m<sn i<n)))
  ∎
  where
  helper : {F : Set ℓ} {{fld : Field F}} → (a b c d : F) → a + b + c + d ≡ (a + c) + (b + d)
  helper a b c d =
    begin
      a + b + c + d
    ≡⟨ cong (_+ d) +-assoc ⟩
      a + (b + c) + d
    ≡⟨ cong (λ{bc → a + bc + d}) +-comm ⟩
      a + (c + b) + d
    ≡⟨ cong (_+ d) (sym +-assoc)⟩
      a + c + b + d
    ≡⟨ +-assoc ⟩
      a + c + (b + d)
    ∎

-- 双重Σ可以交换顺序
sum-swap : {F : Set ℓ} {{fld : Field F}} →
         ∀ {m n : ℕ} (f : (i j : ℕ) → i < m → j < n → F)
         → Σ[ i < m , i<m ] Σ[ j < n , j<n ] (f i j i<m j<n) ≡ Σ[ j < n , j<n ] Σ[ i < m , i<m ] (f i j i<m j<n)
sum-swap {m = 0} {n = n} f =
  begin
    0ᶠ
  ≡⟨ sym (Σ0≡0 {n = n}) ⟩
    sigma-< n (λ j j<n → sigma-< 0 (λ i i<m → 0ᶠ))
  ∎
sum-swap {m = suc m} {n = n} f =
  begin
    (Σ[ j < n , j<n ] f m j n<sn j<n) + (Σ[ i < m , i<m ] (Σ[ j < n , j<n ] f i j (m<sn i<m) j<n))
  ≡⟨ cong ((Σ[ j < n , j<n ] f m j n<sn j<n) +_) (sum-swap {m = m} {n = n} (λ{i j i<m j<n → f i j (m<sn i<m) j<n})) ⟩
    (Σ[ j < n , j<n ] f m j n<sn j<n) + (Σ[ j < n , j<n ] (Σ[ i < m , i<m ] f i j (m<sn i<m) j<n))
  ≡⟨ sym (Σ-distri-+ {n = n} (λ j j<n → f m j n<sn j<n) (λ j j<n → Σ[ i < m , i<m ] f i j (m<sn i<m) j<n)) ⟩
    Σ[ j < n , j<n ] (f m j n<sn j<n + (Σ[ i < m , i<m ] f i j (m<sn i<m) j<n))
  ∎
  
Σf*k : {F : Set ℓ} {{fld : Field F}} → ∀ {n : ℕ} (f : (i : ℕ) → i < n → F) (k : F)
      → Σ[ i < n , i<n ] (f i i<n * k) ≡ (Σ[ i < n , i<n ] f i i<n) * k
      
Σf*k {n = 0}     f k rewrite 0*n≡0 {n = k} = refl
Σf*k {n = suc n} f k =
  begin
    (f n n<sn * k) + Σ[ i < n , i<n ] (f i (m<sn i<n) * k)
  ≡⟨ cong (f n n<sn * k +_) (Σf*k {n = n} (λ i z → f i (m<sn z)) k) ⟩
    (f n n<sn * k) + (Σ[ i < n , i<n ] f i (m<sn i<n)) * k
  ≡⟨ cong (_+ (Σ[ i < n , i<n ] f i (m<sn i<n)) * k) *-comm ⟩
    (k * f n n<sn) + (Σ[ i < n , i<n ] f i (m<sn i<n)) * k
  ≡⟨ cong (k * f n n<sn +_) *-comm ⟩
    (k * f n n<sn) + (k * (Σ[ i < n , i<n ] f i (m<sn i<n)))
  ≡⟨ sym *-distri-+ ⟩
    k * (f n n<sn + (Σ[ i < n , i<n ] f i (m<sn i<n)))
  ≡⟨ *-comm ⟩
    (f n n<sn + (Σ[ i < n , i<n ] f i (m<sn i<n))) * k
  ∎

Σk*f : {F : Set ℓ} {{fld : Field F}} → ∀ {n : ℕ} (f : (i : ℕ) → i < n → F) (k : F)
      → Σ[ i < n , i<n ] (k * f i i<n) ≡ k * (Σ[ i < n , i<n ] f i i<n)
Σk*f {n = n} f k =
  begin
    Σ[ i < n , i<n ] (k * f i i<n)
    -- sigma-< n (λ i i<n → ⋯)
  ≡⟨ cong (sigma-< n) (Λ i i<n ⇒ *-comm) ⟩
    Σ[ i < n , i<n ] (f i i<n * k)
  ≡⟨ Σf*k f k ⟩
    (Σ[ i < n , i<n ] f i i<n) * k
  ≡⟨ *-comm ⟩
    k * (Σ[ i < n , i<n ] f i i<n)
  ∎
