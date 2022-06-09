module Matrix where

open import Structures
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (+-comm)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Util

open Field {{...}}

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C F : Set ℓ
  m n i j k l : ℕ


matFunc : {ℓ : Level} → (m n : ℕ) (A : Set ℓ) → Set ℓ
matFunc m n A = ∀ (m′ n′ : ℕ) → m′ < m → n′ < n → A

-- 矩阵, 其中蕴含一个索引函数
infix 10 ⟦_⟧
data Mat {ℓ : Level} : ℕ {-行-} → ℕ {-列-} → Set ℓ → Set ℓ where
  ⟦_⟧ : ∀ {A : Set ℓ} {m₀ n₀ : ℕ} → (∀ (m n : ℕ) → m < m₀ → n < n₀ → A) → Mat m₀ n₀ A


-- 转置
infix 20 _ᵀ
_ᵀ : Mat m n A → Mat n m A
⟦ f ⟧ ᵀ = ⟦ (λ n m n< m< → f m n m< n<) ⟧


-- 1 × n 矩阵转为向量
Mat1n→Vect : ∀ {A : Set ℓ} {n : ℕ} → Mat 1 n A → Vect n A
Mat1n→Vect         {n = zero}  _     = []
Mat1n→Vect {A = A} {n = suc n} ⟦ f ⟧ = f zero n z<s n<sn ∷ Mat1n→Vect {n = n} ⟦ helper ⟧
  where
  helper : ∀ (m′ n′ : ℕ) → m′ < 1 → n′ < n → A
  helper m′ n′ m<1 n′<n = f m′ n′ m<1 (m<sn n′<n)

-- m × 1 矩阵转为向量
Matm1→Vect : ∀ {A : Set ℓ} {m : ℕ} → Mat m 1 A → Vect m A
Matm1→Vect mat = Mat1n→Vect (mat ᵀ)


-- 取矩阵的第m′行, ─ 代表行, 要在⟦⟧中提供小于证明
-- \--- ─
infix 9 _─_⟦_⟧
_─_⟦_⟧ : ∀ {A : Set ℓ} {m n : ℕ} → Mat m n A → ∀ (m′ : ℕ) → m′ < m → Mat 1 n A
_─_⟦_⟧ {A = A} {m = m} {n = n} ⟦ f ⟧ m′ m′<m = ⟦ helper ⟧
  where
  helper : ∀ (m₁ n₁ : ℕ) → m₁ < 1 → n₁ < n → A
  helper _ n₁ m₁<1 n₁<n = f m′ n₁ m′<m n₁<n

-- 取矩阵的第n′列, ∣代表列, 要在⟦⟧中提供小于证明
-- \| ∣
infix 9 _∣_⟦_⟧
_∣_⟦_⟧ : ∀ {A : Set ℓ} {m n : ℕ} → Mat m n A → ∀ (n′ : ℕ) → n′ < n → Mat m 1 A
mat ∣ n′ ⟦ n′<n ⟧ = (mat ᵀ ─ n′ ⟦ n′<n ⟧) ᵀ

-- 删掉矩阵顶行
infix 20 _↓
_↓ : Mat (suc m) n A → Mat m n A
_↓ ⟦ f ⟧ = ⟦ (λ m n m<m₀⁻ n<n₀ → f m n (m<sn m<m₀⁻) n<n₀) ⟧


-- 1 × n 矩阵乘 n × 1 矩阵
infix 20 [_∙_]
[_∙_] : {n : ℕ} {F : Set ℓ} {{fld : Field F}} → Mat 1 n F → Mat n 1 F → F
[_∙_] {n = n} ⟦ a ⟧ ⟦ b ⟧ = Σ[ i < n , i<n ] (a zero i z<s i<n * b i zero i<n z<s)


-- 表转为矩阵
tab→mat : ∀ {A : Set ℓ} {m n : ℕ} → Table m n A → Mat m n A
tab→mat {A = A} {m = m} {n = n} table = ⟦ f ⟧
  where
  f : ∀ (m′ n′ : ℕ) → m′ < m → n′ < n → A
  f m′ n′ m<m n<n = (table ! m′ ⟦ m<m ⟧) ! n′ ⟦ n<n ⟧
  
-- 矩阵转为表
mat→tab : Mat m n A → Table m n A
mat→tab {m = zero}  _     = []
mat→tab {m = suc m} ⟦ f ⟧ = Mat1n→Vect (⟦ f ⟧ ─ m ⟦ n<sn ⟧) ∷ mat→tab {m = m} (⟦ f ⟧ ↓)

postulate
  mat→tab→mat : tab→mat{A = A}{m = m}{n = n} ∘ mat→tab ≡ id

data NumberCase : ℕ → ℕ → Set where
  lt  : k < i → NumberCase k i 
  gte : i ≤ k → NumberCase k i


-- 余子式
infix 10 _[_,_]⟦_,_⟧
_[_,_]⟦_,_⟧ : Mat (suc m) (suc n) A → (i : ℕ) → (j : ℕ) → i < suc m → j < suc n →  Mat m n A
_[_,_]⟦_,_⟧ {m = m} {n = n} {A = A} ⟦ f ⟧ i j i<m j<n = ⟦ g ⟧
  where
  number-case : ∀ (k i : ℕ) → NumberCase k i
  number-case zero    (suc i) = lt z<s
  number-case (suc k) zero    = gte (<→≤ z<s)
  number-case zero    zero    = gte (≡→≤ refl)
  number-case (suc k) (suc i) with number-case k i
  ...                            | lt  k<i       = lt (s<s k<i)
  ...                            | gte (<→≤ i<k) = gte (<→≤ (s<s i<k))
  ...                            | gte (≡→≤ k≡i) = gte (≡→≤ (cong suc k≡i))
  g : (k l : ℕ) → k < m → l < n → A
  g k l k<m l<n with number-case k i | number-case l j
  ...              | lt  k<i          | lt  l<j = f k       l       (m<sn k<m) (m<sn l<n)
  ...              | gte i≤k          | lt  l<j = f (suc k) l       (s<s k<m)  (m<sn l<n)
  ...              | lt  k<i          | gte j≤l = f k       (suc l) (m<sn k<m) (s<s l<n)
  ...              | gte i≤k          | gte j≤l = f (suc k) (suc l) (s<s k<m)  (s<s l<n)


infixl 6 _+ᵐ_
_+ᵐ_ : {{fld : Field F}} → Mat m n F → Mat m n F → Mat m n F
⟦ f ⟧ +ᵐ ⟦ g ⟧ = ⟦ (λ m n m< n< →  (f m n m< n<) + (g m n m< n<) ) ⟧

infixl 7 _*ᵐ_
_*ᵐ_ : {{fld : Field F}} → F → Mat m n F → Mat m n F
λ₀ *ᵐ ⟦ f ⟧ = ⟦ (λ m n m< n< → λ₀ * f m n m< n<) ⟧

infixl 6 _-ᵐ_
_-ᵐ_ : {{fld : Field F}} → Mat m n F → Mat m n F → Mat m n F
a -ᵐ b = a +ᵐ (- 1ᶠ *ᵐ b)

infixl 7 _×_
_×_ : {m n : ℕ} {F : Set ℓ} {{fld : Field F}} → Mat m k F → Mat k n F → Mat m n F
_×_ {m = m} {n = n} {F = F} f g  = ⟦ h ⟧
  where
  h : matFunc m n F
  h i j i<m j<n = [ f ─ i ⟦ i<m ⟧ ∙ g ∣ j ⟦ j<n ⟧ ]

zero-mat : {{fld : Field F}} {m n : ℕ} → Mat m n F
zero-mat {{fld = fld}} {m = m} {n = n} = ⟦ f ⟧
  where
  f : {{fld : Field F}} (x x₁ : ℕ) → x < m → x₁ < n → F
  f _ _ _ _ = 0ᶠ


-- 行列式
infix 10 ∣_∣
∣_∣ : ∀ {F : Set ℓ} {m : ℕ} {{fld : Field F}} → Mat m m F → F
∣_∣ {m = zero}  _     = 1ᶠ
∣_∣ {m = suc m} mat = Σ[ i < suc m , i<n ] ((is-even i) * ∣ mat [ zero , i ]⟦ z<s , i<n ⟧ ∣)
  where
  is-even : {F : Set ℓ} {{fld : Field F}} → ℕ → F
  is-even zero = 1ᶠ
  is-even (suc zero) = - 1ᶠ
  is-even (suc (suc n)) = is-even n

det :  ∀ {F : Set ℓ} {m : ℕ} {{fld : Field F}} → Mat m m F → F
det m = ∣ m ∣

