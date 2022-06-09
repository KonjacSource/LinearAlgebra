module Matrix.Properties where
open import Matrix
open import Structures
open import Util
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (+-comm)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Extensionality renaming (_×_ to _∧_)

open Field {{...}}

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C F : Set ℓ
  m n h i j k l : ℕ

-- 转置两次为自身
Mᵀᵀ≡M : ∀ (M : Mat m n A) → M ᵀ ᵀ ≡ M
Mᵀᵀ≡M ⟦ f ⟧ = refl

-- 矩阵乘法结合律
×-assoc : {{fld : Field F}} → ∀ (A : Mat m n F) (B : Mat n k F) (C : Mat k l F) → A × B × C ≡ A × (B × C)
×-assoc {F = F} {m = m} {n = n} {k = k} ⟦ a ⟧ ⟦ b ⟧ ⟦ c ⟧ =
  begin 
    ⟦ (λ i j i<m j<n →
         Σ[ i′ < k , i′<k ] (
           (Σ[ j′ < n , j′<n ] (a i j′ i<m j′<n * b j′ i′ j′<n i′<k))
           * (c i′ j i′<k j<n)))
    ⟧
  ≡⟨ cong ⟦_⟧ (helper {F = F} m n k a b c) ⟩  
    ⟦
      (λ i j i<m j<n →
        Σ[ i′ < n , i′<n ] (
         (a i i′ i<m i′<n)
         * (Σ[ j′ < k , j′<k ] (b i′ j′ i′<n j′<k * c j′ j j′<k j<n))))
    ⟧
  ∎
  where
  helper : {F : Set ℓ} {{fld : Field F}} → 
         ∀ (m n k : ℕ) (a : matFunc m n F) (b : matFunc n k F) (c : matFunc k l F)
         → (λ i j i<m j<n →
              Σ[ i′ < k , i′<k ] (
                (Σ[ j′ < n , j′<n ] (a i j′ i<m j′<n * b j′ i′ j′<n i′<k))
                * (c i′ j i′<k j<n)))
           ≡
           (λ i j i<m j<n →
             Σ[ j′ < n , j′<n ] (
               (a i j′ i<m j′<n)
               * (Σ[ i′ < k , i′<k ] (b j′ i′ j′<n i′<k * c i′ j i′<k j<n))))
               
  helper m n k a b c = Λ i j i<m j<n ⇒
    begin
      Σ[ i′ < k , i′<k ] (
        (Σ[ j′ < n , j′<n ] (a i j′ i<m j′<n * b j′ i′ j′<n i′<k))
        * (c i′ j i′<k j<n))
      -- sigma-< k (λ i′ i′<k → (sigma-< n (λ j′ j′<n → ⋯)) * ⋯ )
    ≡⟨ cong (sigma-< k) (Λ i′ i′<k ⇒ sym (Σf*k {n = n} (λ j′ j′<n → a i j′ i<m j′<n * b j′ i′ j′<n i′<k) (c i′ j i′<k j<n))) ⟩
      Σ[ i′ < k , i′<k ] Σ[ j′ < n , j′<n ]
        (a i j′ i<m j′<n * b j′ i′ j′<n i′<k * c i′ j i′<k j<n)
    ≡⟨ sum-swap {m = k} {n = n} (λ i′ j′ i′<k j′<n → a i j′ i<m j′<n * b j′ i′ j′<n i′<k * c i′ j i′<k j<n) ⟩
      Σ[ j′ < n , j′<n ] Σ[ i′ < k , i′<k ]
        (a i j′ i<m j′<n * b j′ i′ j′<n i′<k * c i′ j i′<k j<n)
      -- sigma-< n (λ j′ j′<n → sigma-< k (λ i′ i′<k → ⋯ ))
    ≡⟨ cong (sigma-< n) (Λ j′ j′<n ⇒ cong (sigma-< k) (Λ i′ i′<k ⇒ *-assoc)) ⟩
      Σ[ j′ < n , j′<n ] Σ[ i′ < k , i′<k ]
        (a i j′ i<m j′<n * (b j′ i′ j′<n i′<k * c i′ j i′<k j<n))
      -- sigma-< n (λ j′ j′<n → sigma-< k (λ i′ i′<k → a i j′ i<m j′<n * ( ⋯ ) )) 
    ≡⟨ cong (sigma-< n) (Λ j′ j′<n ⇒ Σk*f {n = k} (λ i′ i′<k → b j′ i′ j′<n i′<k * c i′ j i′<k j<n) (a i j′ i<m j′<n) ) ⟩
      Σ[ j′ < n , j′<n ] (a i j′ i<m j′<n * Σ[ i′ < k , i′<k ]
        (b j′ i′ j′<n i′<k * c i′ j i′<k j<n))
    ∎
    




data SymMat {ℓ} : Mat m m A → Set ℓ where
  sym-mat : ∀ {A : Set ℓ} (mat : Mat m m A) → mat ᵀ ≡ mat → SymMat mat
  

