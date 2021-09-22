{-# OPTIONS --without-K --safe #-}

module ListLemma where

open import Data.Empty
open import Data.Fin.Base using (Fin; suc; zero; fromℕ)
open import Data.List.Base as List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat.Base hiding (_^_)
open import Data.Product
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties
open import Relation.Unary using (Pred)

private
  variable
    a ℓ : Level
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

inits′ : ∀ (xs : List A) → xs ≢ [] → List (List A)
inits′ [] []≢[] = ⊥-elim ([]≢[] refl)
inits′ (x ∷ xs) _ = List.map (x ∷_) (inits xs)

private
  subst-zero : ∀ {m n} (p : m ≡ n) → subst Fin (cong ℕ.suc p) Fin.zero ≡ Fin.zero
  subst-zero refl = refl

  subst-suc : ∀ {m n} (p : m ≡ n) (i : Fin m) → subst Fin (cong ℕ.suc p) (Fin.suc i) ≡ Fin.suc (subst Fin p i)
  subst-suc refl i  = refl

lookup-map : ∀ (f : A → B) (xs : List A) i →
             lookup (List.map f xs) i ≡ f (lookup xs (subst Fin (length-map f xs) i))
lookup-map f (x ∷ xs) zero = sym (cong (f ∘ lookup (x ∷ xs)) (subst-zero (length-map f xs)))
lookup-map f (x ∷ xs) (suc i) = begin
  lookup (List.map f xs) i                                                   ≡⟨ lookup-map f xs i ⟩
  f (lookup xs (subst Fin (length-map f xs) i))                              ≡⟨⟩
  f (lookup (x ∷ xs) (Fin.suc (subst Fin (length-map f xs) i)))              ≡˘⟨ cong (f ∘ lookup (x ∷ xs)) (subst-suc (length-map f xs) i) ⟩
  f (lookup (x ∷ xs) (subst Fin (cong ℕ.suc (length-map f xs)) (Fin.suc i))) ∎
  where open ≡-Reasoning

lastIndexOfInits : ∀ (xs : List A) → Fin (length (inits xs))
lastIndexOfInits [] = Fin.zero
lastIndexOfInits (x ∷ xs) = Fin.suc (subst Fin (sym (length-map (x ∷_) (inits xs))) (lastIndexOfInits xs))

lookup-lastIndexOfInits : ∀ (xs : List A) → lookup (inits xs) (lastIndexOfInits xs) ≡ xs
lookup-lastIndexOfInits [] = refl
lookup-lastIndexOfInits (x ∷ xs) = begin
  lookup (inits (x ∷ xs)) (lastIndexOfInits (x ∷ xs))                           ≡⟨⟩
  lookup (List.map (x ∷_) (inits xs)) (subst Fin (sym p) (lastIndexOfInits xs)) ≡⟨ lookup-map (x ∷_) (inits xs) _ ⟩
  x ∷ lookup (inits xs) (subst Fin p (subst Fin (sym p) (lastIndexOfInits xs))) ≡⟨ cong (_∷_ x ∘ lookup (inits xs)) (subst-subst-sym p) ⟩
  x ∷ lookup (inits xs) (lastIndexOfInits xs)                                   ≡⟨ cong (x ∷_) (lookup-lastIndexOfInits xs) ⟩
  x ∷ xs                                                                        ∎
  where
    open ≡-Reasoning
    p : length (List.map (x ∷_) (inits xs)) ≡ length (inits xs)
    p = length-map (x ∷_) (inits xs)

lastIndexOfInits′ : ∀ (xs : List A) (xs≢[] : xs ≢ []) → Fin (length (inits′ xs xs≢[]))
lastIndexOfInits′ [] []≢[] = ⊥-elim ([]≢[] refl)
lastIndexOfInits′ (x ∷ xs) xs≢[] = subst Fin (sym (length-map (x ∷_) (inits xs))) (lastIndexOfInits xs)

lookup-lastIndexOfInits′ : ∀ (xs : List A) (xs≢[] : xs ≢ []) → lookup (inits′ xs xs≢[]) (lastIndexOfInits′ xs xs≢[]) ≡ xs
lookup-lastIndexOfInits′ [] []≢[] = ⊥-elim ([]≢[] refl)
lookup-lastIndexOfInits′ (x ∷ xs) xs≢[] = begin
  lookup (inits′ (x ∷ xs) xs≢[]) (lastIndexOfInits′ (x ∷ xs) xs≢[])             ≡⟨⟩
  lookup (List.map (x ∷_) (inits xs)) (subst Fin (sym p) (lastIndexOfInits xs)) ≡⟨ lookup-map (x ∷_) (inits xs) _ ⟩
  x ∷ lookup (inits xs) (subst Fin p (subst Fin (sym p) (lastIndexOfInits xs))) ≡⟨ cong (_∷_ x ∘ lookup (inits xs)) (subst-subst-sym p) ⟩
  x ∷ lookup (inits xs) (lastIndexOfInits xs)                                   ≡⟨ cong (x ∷_) (lookup-lastIndexOfInits xs) ⟩
  x ∷ xs                                                                        ∎
  where
    open ≡-Reasoning
    p : length (List.map (x ∷_) (inits xs)) ≡ length (inits xs)
    p = length-map (x ∷_) (inits xs)

x∷xs≢[] : ∀ {x : A} {xs} → x ∷ xs ≢ []
x∷xs≢[] ()

inits′-≢[] : ∀ (xs : List A) (xs≢[] : xs ≢ []) i → lookup (inits′ xs xs≢[]) i ≢ []
inits′-≢[] [] []≢[] _ = ⊥-elim ([]≢[] refl)
inits′-≢[] (x ∷ xs) _ i p = x∷xs≢[] $ begin
  x ∷ lookup (inits xs) (subst Fin (length-map (x ∷_) (inits xs)) i) ≡˘⟨ lookup-map (x ∷_) (inits xs) i ⟩
  lookup (List.map (x ∷_) (inits xs)) i                              ≡⟨ p ⟩
  []                                                                 ∎
  where open ≡-Reasoning
