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

indexOfInits : ∀ (xs : List A) {ys} zs → xs ++ ys ≡ zs → Fin (length (inits zs))
indexOfInits [] [] p = Fin.zero
indexOfInits [] (z ∷ zs) p = Fin.zero
indexOfInits (x ∷ xs) (x ∷ zs) refl = Fin.suc (subst Fin (sym (length-map (x ∷_) (inits zs))) (indexOfInits xs zs refl))

lookup-indexOfInits : ∀ (xs : List A) {ys} zs (p : xs ++ ys ≡ zs) → lookup (inits zs) (indexOfInits xs zs p) ≡ xs
lookup-indexOfInits [] [] _ = refl
lookup-indexOfInits [] (x ∷ zs) _ = refl
lookup-indexOfInits (x ∷ xs) (x ∷ zs) refl = begin
  lookup (List.map (x ∷_) (inits zs)) (subst Fin (sym p) i) ≡⟨ lookup-map (x ∷_) (inits zs) (subst Fin (sym p) i) ⟩
  x ∷ lookup (inits zs) (subst Fin p (subst Fin (sym p) i)) ≡⟨ cong (_∷_ x ∘ lookup (inits zs)) (subst-subst-sym p) ⟩
  x ∷ lookup (inits zs) (indexOfInits xs zs refl)           ≡⟨ cong (x ∷_) (lookup-indexOfInits xs zs refl) ⟩
  x ∷ xs                                                    ∎
  where
    open ≡-Reasoning
    i = indexOfInits xs zs refl
    p = length-map (x ∷_) (inits zs)

indexOfInits′ : ∀ (xs : List A) {ys} zs (xs≢[] : xs ≢ []) (zs≢[] : zs ≢ []) → xs ++ ys ≡ zs → Fin (length (inits′ zs zs≢[]))
indexOfInits′ [] zs []≢[] zs≢[] _ = ⊥-elim ([]≢[] refl)
indexOfInits′ (x ∷ xs) (x ∷ zs) xs≢[] zs≢[] refl = subst Fin (sym (length-map (x ∷_) (inits zs))) (indexOfInits xs zs refl)

lookup-indexOfInits′ : ∀ (xs : List A) {ys} zs (xs≢[] : xs ≢ []) (zs≢[] : zs ≢ []) (p : xs ++ ys ≡ zs) →
                       lookup (inits′ zs zs≢[]) (indexOfInits′ xs zs xs≢[] zs≢[] p) ≡ xs
lookup-indexOfInits′ [] zs []≢[] zs≢[] _ = ⊥-elim ([]≢[] refl)
lookup-indexOfInits′ (x ∷ xs) (x ∷ zs) xs≢[] zs≢[] refl = begin
  lookup (List.map (_∷_ x) (inits zs)) (subst Fin (sym p) i) ≡⟨ lookup-map (x ∷_) (inits zs) (subst Fin (sym p) i) ⟩
  x ∷ lookup (inits zs) (subst Fin p (subst Fin (sym p) i))  ≡⟨ cong (_∷_ x ∘ lookup (inits zs)) (subst-subst-sym p) ⟩
  x ∷ lookup (inits zs) i                                    ≡⟨ cong (x ∷_) (lookup-indexOfInits xs zs refl) ⟩
  x ∷ xs                                                     ∎
  where
    open ≡-Reasoning
    i = indexOfInits xs zs refl
    p = length-map (x ∷_) (inits zs)

-- lastIndexOfInits : ∀ (xs : List A) → Fin (length (inits xs))
-- lastIndexOfInits xs = indexOfInits xs xs (++-identityʳ xs)
--
-- lookup-lastIndexOfInits : ∀ (xs : List A) → lookup (inits xs) (lastIndexOfInits xs) ≡ xs
-- lookup-lastIndexOfInits xs = lookup-indexOfInits xs xs (++-identityʳ xs)

lastIndexOfInits′ : ∀ (xs : List A) (xs≢[] : xs ≢ []) → Fin (length (inits′ xs xs≢[]))
lastIndexOfInits′ xs xs≢[] = indexOfInits′ xs xs xs≢[] xs≢[] (++-identityʳ xs)

lookup-lastIndexOfInits′ : ∀ (xs : List A) (xs≢[] : xs ≢ []) → lookup (inits′ xs xs≢[]) (lastIndexOfInits′ xs xs≢[]) ≡ xs
lookup-lastIndexOfInits′ xs xs≢[] = lookup-indexOfInits′ xs xs xs≢[] xs≢[] (++-identityʳ xs)

private
  toℕ-subst : ∀ {m n} (p : m ≡ n) i → toℕ (subst Fin p i) ≡ toℕ i
  toℕ-subst refl i = refl

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

private
  lookup-inits-sublist' : ∀ (xs : List A) i → lookup (inits xs) i ++ drop (toℕ i) xs ≡ xs
  lookup-inits-sublist' xs i = subst (λ ts → ts ++ drop (toℕ i) xs ≡ xs) (sym (lookup-inits xs i)) (take++drop (toℕ i) xs)

lookup-inits′ : ∀ (xs : List A) (xs≢[] : xs ≢ []) i → ∃[ ys ] lookup (inits′ xs xs≢[]) i ++ ys ≡ xs
lookup-inits′ [] []≢[] i = ⊥-elim ([]≢[] refl)
lookup-inits′ (x ∷ xs) xs≢[] i = ys , (begin
  lookup (List.map (x ∷_) (inits xs)) i ++ ys ≡⟨ cong (_++ ys) (lookup-map (x ∷_) (inits xs) i) ⟩
  x ∷ lookup (inits xs) j ++ ys               ≡⟨ cong (x ∷_) (lookup-inits-sublist' xs j) ⟩
  x ∷ xs                                      ∎)
  where
    open ≡-Reasoning
    p = length-map (x ∷_) (inits xs)
    j = subst Fin p i
    ys = drop (toℕ j) xs

length-inits : ∀ (xs : List A) → length (inits xs) ≡ ℕ.suc (length xs)
length-inits [] = refl
length-inits (x ∷ xs) = cong ℕ.suc (trans (length-map (x ∷_) (inits xs)) (length-inits xs))

length-lookup-inits′ : ∀ (xs : List A) (xs≢[] : xs ≢ []) i → length (lookup (inits′ xs xs≢[]) i) ≡ ℕ.suc (toℕ i)
length-lookup-inits′ [] []≢[] i = ⊥-elim ([]≢[] refl)
length-lookup-inits′ (x ∷ xs) xs≢[] i = begin
  length (lookup (List.map (_∷_ x) (inits xs)) i) ≡⟨ cong length (lookup-map (x ∷_) (inits xs) i) ⟩
  length (x ∷ lookup (inits xs) (subst Fin p i)) ≡⟨⟩
  ℕ.suc (length (lookup (inits xs) (subst Fin p i))) ≡⟨ cong (ℕ.suc ∘ length) (lookup-inits xs (subst Fin p i)) ⟩
  ℕ.suc (length (take (toℕ (subst Fin p i)) xs)) ≡⟨ cong ℕ.suc (length-take (toℕ (subst Fin p i)) xs) ⟩
  ℕ.suc (toℕ (subst Fin p i) ⊓ length xs) ≡⟨ cong ℕ.suc (m≤n⇒m⊓n≡m i≤∣xs∣) ⟩
  ℕ.suc (toℕ (subst Fin p i)) ≡⟨ cong ℕ.suc (toℕ-subst p i) ⟩
  ℕ.suc (toℕ i) ∎
  where
    open ≡-Reasoning
    p = length-map (x ∷_) (inits xs)

    i≤∣xs∣ : toℕ (subst Fin p i) ≤ length xs
    i≤∣xs∣ = +-cancelˡ-≤ 1 (subst (toℕ (subst Fin p i) <_) (length-inits xs) (toℕ<n (subst Fin p i)))

x∷xs≢[] : ∀ {x : A} {xs} → x ∷ xs ≢ []
x∷xs≢[] ()

inits′-≢[] : ∀ (xs : List A) (xs≢[] : xs ≢ []) i → lookup (inits′ xs xs≢[]) i ≢ []
inits′-≢[] [] []≢[] _ = ⊥-elim ([]≢[] refl)
inits′-≢[] (x ∷ xs) _ i p = x∷xs≢[] $ begin
  x ∷ lookup (inits xs) (subst Fin (length-map (x ∷_) (inits xs)) i) ≡˘⟨ lookup-map (x ∷_) (inits xs) i ⟩
  lookup (List.map (x ∷_) (inits xs)) i                              ≡⟨ p ⟩
  []                                                                 ∎
  where open ≡-Reasoning

≡[]-dec : Decidable {A = List A} (_≡ [])
≡[]-dec [] = yes refl
≡[]-dec (x ∷ xs) = no λ ()

index-min : ∀ {P : Pred A ℓ} xs (pqxs : First (∁ P) P xs) i → P (lookup xs i) → First.index pqxs Fin.≤ i
index-min (x ∷ xs) First.[ px ] Fin.zero p = z≤n
index-min (x ∷ xs) (¬px First.∷ pqxs) Fin.zero p = ⊥-elim (¬px p)
index-min (x ∷ xs) First.[ px ] (Fin.suc i) p = z≤n
index-min (x ∷ xs) (¬px First.∷ pqxs) (Fin.suc i) p = s≤s (index-min xs pqxs i p)
