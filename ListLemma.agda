{-# OPTIONS --without-K --safe #-}

module ListLemma where

open import Data.Empty
open import Data.Fin.Base as Fin using (Fin; suc; zero; fromℕ; toℕ)
open import Data.Fin.Properties
open import Data.List.Base as List
open import Data.List.Properties
open import Data.List.Relation.Unary.First as First using (First)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat.Base hiding (_^_)
open import Data.Nat.Properties
open import Data.Product
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable; ∁)

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B : Set a

infix 20 _^_

_^_ : List A → ℕ → List A
α ^ zero = []
α ^ suc n = α ++ α ^ n

length-^ : ∀ (xs : List A) n → length (xs ^ n) ≡ n * length xs
length-^ xs zero = refl
length-^ xs (suc n) = trans (length-++ xs) (cong (length xs +_) (length-^ xs n))

take-++-= : ∀ (xs ys : List A) → take (length xs) (xs ++ ys) ≡ xs
take-++-= [] ys = refl
take-++-= (x ∷ xs) ys = cong (x ∷_) (take-++-= xs ys)

take-++-≤ : ∀ (xs ys : List A) n → length xs ≤ n → take n (xs ++ ys) ≡ xs ++ take (n ∸ length xs) ys
take-++-≤ [] ys n ∣xs∣≤n = refl
take-++-≤ (x ∷ xs) ys (ℕ.suc n) (s≤s ∣xs∣≤n) = cong (x ∷_) (take-++-≤ xs ys n ∣xs∣≤n)

take-++-≥ : ∀ (xs ys : List A) n → length xs ≥ n → take n (xs ++ ys) ≡ take n xs
take-++-≥ xs ys zero ∣xs∣≥n = refl
take-++-≥ (x ∷ xs) ys (suc n) (s≤s ∣xs∣≥n) = cong (x ∷_) (take-++-≥ xs ys n ∣xs∣≥n)

-- drop-++-= : ∀ (xs ys : List A) → drop (length xs) (xs ++ ys) ≡ ys
-- drop-++-= [] ys = refl
-- drop-++-= (x ∷ xs) ys = drop-++-= xs ys

≢[]⇒length≥1 : ∀ {xs : List A} → xs ≢ [] → length xs ≥ 1
≢[]⇒length≥1 {xs = []} []≢[] = ⊥-elim ([]≢[] refl)
≢[]⇒length≥1 {xs = x ∷ xs} _ = s≤s z≤n

lookup-any : ∀ {P : Pred A ℓ} xs i → P (lookup xs i) → Any P xs
lookup-any (x ∷ xs) zero px = here px
lookup-any (x ∷ xs) (suc i) pxs = there (lookup-any xs i pxs)

toℕ-subst : ∀ {m n} (p : m ≡ n) i → toℕ (subst Fin p i) ≡ toℕ i
toℕ-subst refl i = refl

subst-zero : ∀ {m n} (p : m ≡ n) → subst Fin (cong ℕ.suc p) Fin.zero ≡ Fin.zero
subst-zero refl = refl

subst-suc : ∀ {m n} (p : m ≡ n) (i : Fin m) → subst Fin (cong ℕ.suc p) (Fin.suc i) ≡ Fin.suc (subst Fin p i)
subst-suc refl i  = refl

lookup-subst : ∀ {xs ys : List A} (p : xs ≡ ys) i → lookup xs i ≡ lookup ys (subst Fin (cong length p) i)
lookup-subst refl i = refl

inits′′ : ∀ (xs : List A) → List (List A)
inits′′ [] = []
inits′′ (x ∷ xs) = List.map (x ∷_) (inits xs)

lookup-map : ∀ (f : A → B) (xs : List A) i →
             lookup (List.map f xs) i ≡ f (lookup xs (subst Fin (length-map f xs) i))
lookup-map f (x ∷ xs) zero = sym (cong (f ∘ lookup (x ∷ xs)) (subst-zero (length-map f xs)))
lookup-map f (x ∷ xs) (suc i) = begin
  lookup (List.map f xs) i                                                   ≡⟨ lookup-map f xs i ⟩
  f (lookup (x ∷ xs) (Fin.suc (subst Fin (length-map f xs) i)))              ≡˘⟨ cong (f ∘ lookup (x ∷ xs)) (subst-suc (length-map f xs) i) ⟩
  f (lookup (x ∷ xs) (subst Fin (cong ℕ.suc (length-map f xs)) (Fin.suc i))) ∎
  where open ≡-Reasoning

indexOfInits[_++_] : ∀ (xs ys : List A) → Fin (length (inits (xs ++ ys)))
indexOfInits[ [] ++ [] ] = Fin.zero
indexOfInits[ [] ++ y ∷ ys ] = Fin.zero
indexOfInits[ x ∷ xs ++ ys ] = Fin.suc (subst Fin (sym (length-map (x ∷_) (inits (xs ++ ys)))) indexOfInits[ xs ++ ys ])

indexOfInits′′[_++_] : ∀ (xs ys : List A) → xs ≢ [] → Fin (length (inits′′ (xs ++ ys)))
indexOfInits′′[ [] ++ ys ] []≢[] = ⊥-elim ([]≢[] refl)
indexOfInits′′[ x ∷ xs ++ ys ] _ = subst Fin (sym (length-map (x ∷_) (inits (xs ++ ys)))) indexOfInits[ xs ++ ys ]

lookup-indexOfInits[_++_] : ∀ (xs ys : List A) → lookup (inits (xs ++ ys)) indexOfInits[ xs ++ ys ] ≡ xs
lookup-indexOfInits[ [] ++ [] ] = refl
lookup-indexOfInits[ [] ++ x ∷ ys ] = refl
lookup-indexOfInits[ x ∷ xs ++ ys ] = begin
  lookup (List.map (x ∷_) (inits (xs ++ ys))) (subst Fin (sym p) i) ≡⟨ lookup-map (x ∷_) (inits (xs ++ ys)) (subst Fin (sym p) i) ⟩
  x ∷ lookup (inits (xs ++ ys)) (subst Fin p (subst Fin (sym p) i)) ≡⟨ cong (_∷_ x ∘ lookup (inits (xs ++ ys))) (subst-subst-sym p) ⟩
  x ∷ lookup (inits (xs ++ ys)) i                                   ≡⟨ cong (x ∷_) lookup-indexOfInits[ xs ++ ys ] ⟩
  x ∷ xs                                                            ∎
  where
    open ≡-Reasoning
    i = indexOfInits[ xs ++ ys ]
    p = length-map (x ∷_) (inits (xs ++ ys))

lookup-indexOfInits′′[_++_] : ∀ (xs ys : List A) (xs≢[] : xs ≢ []) → lookup (inits′′ (xs ++ ys)) (indexOfInits′′[ xs ++ ys ] xs≢[]) ≡ xs
lookup-indexOfInits′′[ [] ++ ys ] []≢[] = ⊥-elim ([]≢[] refl)
lookup-indexOfInits′′[ x ∷ xs ++ ys ] xs≢[] = lookup-indexOfInits[ x ∷ xs ++ ys ]

lookup-inits : ∀ (xs : List A) i → lookup (inits xs) i ≡ take (toℕ i) xs
lookup-inits [] Fin.zero = refl
lookup-inits (x ∷ xs) Fin.zero = refl
lookup-inits (x ∷ xs) (Fin.suc i) = begin
  lookup (List.map (_∷_ x) (inits xs)) i ≡⟨ lookup-map (x ∷_) (inits xs) i ⟩
  x ∷ lookup (inits xs) (subst Fin p i)  ≡⟨ cong (x ∷_) (lookup-inits xs (subst Fin p i)) ⟩
  x ∷ take (toℕ (subst Fin p i)) xs      ≡⟨ cong (λ i → x ∷ take i xs) (toℕ-subst p i) ⟩
  x ∷ take (toℕ i) xs                    ∎
  where
    open ≡-Reasoning
    p = length-map (x ∷_) (inits xs)

lookup-inits′′ : ∀ (xs : List A) i → lookup (inits′′ xs) i ≡ take (ℕ.suc (toℕ i)) xs
lookup-inits′′ (x ∷ xs) i = lookup-inits (x ∷ xs) (Fin.suc i)

length-inits : ∀ (xs : List A) → length (inits xs) ≡ ℕ.suc (length xs)
length-inits [] = refl
length-inits (x ∷ xs) = cong ℕ.suc (trans (length-map (x ∷_) (inits xs)) (length-inits xs))

length-inits′′ : ∀ (xs : List A) → length (inits′′ xs) ≡ length xs
length-inits′′ [] = refl
length-inits′′ (x ∷ xs) = +-cancelˡ-≡ _ (length-inits (x ∷ xs))

length-lookup-inits′′ : ∀ (xs : List A) i → length (lookup (inits′′ xs) i) ≡ ℕ.suc (toℕ i)
length-lookup-inits′′ xs i = begin
  length (lookup (inits′′ xs) i)      ≡⟨ cong length (lookup-inits′′ xs i) ⟩
  length (take (ℕ.suc (toℕ i)) xs)    ≡⟨ length-take (ℕ.suc (toℕ i)) xs ⟩
  ℕ.suc (toℕ i) ⊓ length xs           ≡˘⟨ cong (ℕ.suc (toℕ i) ⊓_) (length-inits′′ xs) ⟩
  ℕ.suc (toℕ i) ⊓ length (inits′′ xs) ≡⟨ m≤n⇒m⊓n≡m (toℕ<n i) ⟩
  ℕ.suc (toℕ i)                       ∎
  where open ≡-Reasoning

take≢[] : ∀ {n} {xs : List A} → n ≢ 0 → xs ≢ [] → take n xs ≢ []
take≢[] {n = ℕ.zero} 0≢0 _ = ⊥-elim (0≢0 refl)
take≢[] {n = ℕ.suc n} {xs = []} _ []≢[] = ⊥-elim ([]≢[] refl)

≡[]-dec : Decidable {A = List A} (_≡ [])
≡[]-dec [] = yes refl
≡[]-dec (x ∷ xs) = no λ ()

index-min : ∀ {P : Pred A ℓ₁} {Q : Pred A ℓ₂} xs (pqxs : First P Q xs) i → ¬ P (lookup xs i) → First.index pqxs Fin.≤ i
index-min (x ∷ xs) First.[ qx ] i ¬p = z≤n
index-min (x ∷ xs) (px First.∷ pqxs) Fin.zero ¬p = ⊥-elim (¬p px)
index-min (x ∷ xs) (px First.∷ pqxs) (Fin.suc i) ¬p = s≤s (index-min xs pqxs i ¬p)

m>0∧n>0⇒m∸n<m : ∀ {m n} → m > 0 → n > 0 → m ∸ n < m
m>0∧n>0⇒m∸n<m {m = suc m} {n = suc n} (s≤s _) (s≤s _) = s≤s (m∸n≤m m n)

cong-sym : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} (p : x ≡ y) →
           cong f (sym p) ≡ sym (cong f p)
cong-sym f refl = refl
