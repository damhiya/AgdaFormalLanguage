{-# OPTIONS --without-K --safe #-}

module FormalLanguage where

open import Data.Empty
open import Data.Fin.Base using (Fin; suc; zero; fromℕ)
open import Data.List.Base as List hiding ([_])
open import Data.List.Properties
open import Data.List.Relation.Unary.First as First using (First; first)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Unary.All.Properties using (All¬⇒¬Any)
open import Data.Nat.Base hiding (_^_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Base
open import Level using (Level)
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary
open import Relation.Unary hiding (Decidable)

open import ListLemma

private
  variable
    a ℓ : Level
    V : Set a

_* : Set a → Set a
_* = List

[_]* : V * → Pred (V *) _
[ α ]* = λ β → Σ[ n ∈ ℕ ] β ≡ α ^ n

[_,_] : Rel (V *) _
[ α ,  β ] = α ++ β ≡ β ++ α

++-commute : Pred (V *) ℓ → Set _
++-commute S = ∀ {α β} → S α → S β → [ α , β ]

[,]-refl : ∀ (α : V *) → [ α , α ]
[,]-refl _ = refl

[,]-sym : ∀ (α β : V *) → [ α , β ] → [ β , α ]
[,]-sym _ _ = sym

[ε,_] : ∀ (α : V *) → [ [] , α ]
[ε, α ] = sym (++-identityʳ α)

[_,ε] : ∀ (α : V *) → [ α , [] ]
[ α ,ε] = ++-identityʳ α

++-[,]ˡ : ∀ {α β : V *} ω → [ α , ω ] → [ β , ω ] → [ α ++ β , ω ]
++-[,]ˡ {α = α} {β = β} ω [α,ω] [β,ω] = begin
  (α ++ β) ++ ω ≡⟨ ++-assoc α β ω ⟩
  α ++ (β ++ ω) ≡⟨ cong (α ++_) [β,ω] ⟩
  α ++ (ω ++ β) ≡˘⟨ ++-assoc α ω β ⟩
  (α ++ ω) ++ β ≡⟨ cong (_++ β) [α,ω] ⟩
  (ω ++ α) ++ β ≡⟨ ++-assoc ω α β ⟩
  ω ++ α ++ β ∎
  where open ≡-Reasoning

++-[,]ʳ : ∀ {α β : V *} ω → [ ω , α ] → [ ω , β ] → [ ω , α ++ β ]
++-[,]ʳ {α = α} {β = β}ω [ω,α] [ω,β] = [,]-sym (α ++ β) ω (++-[,]ˡ ω ([,]-sym ω α [ω,α]) ([,]-sym ω β [ω,β]))

^-preserves-[,] : ∀ {α ω : V *} → [ α , ω ] → ∀ n → [ α , ω ^ n ]
^-preserves-[,] {α = α} [α,ω] zero = [ α ,ε]
^-preserves-[,] {α = α} {ω = ω} [α,ω] (suc n) = ++-[,]ʳ α [α,ω] (^-preserves-[,] [α,ω] n)

[,]-trans : ∀ {α β γ : V *} → β ≢ [] → [ α , β ] → [ β , γ ] → [ α , γ ]
[,]-trans {V = V} {α = α} {β = β} {γ = γ} β≢[] [α,β] [β,γ] = [α,γ]
  where
    n : ℕ
    n = length α + length γ

    ω : V *
    ω = β ^ n

    ∣αγ∣≡n : length (α ++ γ) ≡ n
    ∣αγ∣≡n = length-++ α

    ∣γα∣≡n : length (γ ++ α) ≡ n
    ∣γα∣≡n = trans (length-++ γ) (+-comm (length γ) (length α))

    ∣ω∣≥n : length ω ≥ n
    ∣ω∣≥n = begin
      n            ≡˘⟨ *-identityʳ n ⟩
      n * 1        ≤⟨ *-monoʳ-≤ n (≢[]⇒length≥1 β≢[]) ⟩
      n * length β ≡˘⟨ length-^ β n ⟩
      length ω     ∎
      where open ≤-Reasoning

    [α,ω] : [ α , ω ]
    [α,ω] = ^-preserves-[,] [α,β] n

    [γ,ω] : [ γ , ω ]
    [γ,ω] = ^-preserves-[,] ([,]-sym β γ [β,γ]) n

    αγ≡prefix[ω] : α ++ γ ≡ take n ω
    αγ≡prefix[ω] = begin
      α ++ γ                                 ≡˘⟨ take-++-= (α ++ γ) ω ⟩
      take (length (α ++ γ)) ((α ++ γ) ++ ω) ≡⟨ cong (λ n → take n ((α ++ γ) ++ ω)) ∣αγ∣≡n ⟩
      take n ((α ++ γ) ++ ω)                 ≡⟨ cong (take n) (++-[,]ˡ ω [α,ω] [γ,ω]) ⟩
      take n (ω ++ α ++ γ)                   ≡⟨ take-++-≥ ω (α ++ γ) n ∣ω∣≥n ⟩
      take n ω                               ∎
      where open ≡-Reasoning

    γα≡prefix[ω] : γ ++ α ≡ take n ω
    γα≡prefix[ω] = begin
      γ ++ α                                 ≡˘⟨ take-++-= (γ ++ α) ω ⟩
      take (length (γ ++ α)) ((γ ++ α) ++ ω) ≡⟨ cong (λ n → take n ((γ ++ α) ++ ω)) ∣γα∣≡n ⟩
      take n ((γ ++ α) ++ ω)                 ≡⟨ cong (take n) (++-[,]ˡ ω [γ,ω] [α,ω]) ⟩
      take n (ω ++ γ ++ α)                   ≡⟨ take-++-≥ ω (γ ++ α) n ∣ω∣≥n ⟩
      take n ω                               ∎
      where open ≡-Reasoning

    [α,γ] : [ α , γ ]
    [α,γ] = begin
      α ++ γ   ≡⟨ αγ≡prefix[ω] ⟩
      take n ω ≡˘⟨ γα≡prefix[ω] ⟩
      γ ++ α   ∎
      where open ≡-Reasoning

subtract : ∀ (α β : V *) → V *
subtract α β = take (length β ∸ length α) β

module _ (α β : V *) (∣α∣≤∣β∣ : length α ≤ length β) ([α,β] : [ α , β ]) where

  private
    η : V *
    η = subtract α β

    β≡αη : β ≡ α ++ η
    β≡αη = begin
      β                        ≡˘⟨ take-++-= β α ⟩
      take (length β) (β ++ α) ≡˘⟨ cong (take (length β)) [α,β] ⟩
      take (length β) (α ++ β) ≡⟨ take-++-≤ α β (length β) ∣α∣≤∣β∣ ⟩
      α ++ η                   ∎
      where open ≡-Reasoning

    [α,αη] : [ α , α ++ η ]
    [α,αη] = subst [ α ,_] β≡αη [α,β]

    ααη≡αηα : α ++ α ++ η ≡ α ++ η ++ α
    ααη≡αηα = trans [α,αη] (++-assoc α η α)

    [α,η] : [ α , η ]
    [α,η] = ++-cancelˡ α ααη≡αηα

    β≡ηα : β ≡ η ++ α
    β≡ηα = trans β≡αη [α,η]

  subtract-++ˡ : η ++ α ≡ β
  subtract-++ˡ = sym β≡ηα

  subtract-++ʳ : α ++ η ≡ β
  subtract-++ʳ = sym β≡αη

  subtract-commute₁ : [ subtract α β , α ]
  subtract-commute₁ = [,]-sym α η [α,η]

module _ (V : Set a) (_≟_ : DecidableEquality V) where

  [_,_]? : Decidable ([_,_] {V = V})
  [_,_]? α β = ≡-dec _≟_ (α ++ β) (β ++ α)

  module _ (α : V *) (α≢ε : α ≢ [] ) where
    private
      αs : List (V *)
      αs = inits′ α α≢ε

      αs-any : Any ([ α ,_]) αs
      αs-any = lookup-any αs (lastIndexOfInits′ α α≢ε) (subst [ α ,_] (sym (lookup-lastIndexOfInits′ α α≢ε)) ([,]-refl α))

      αs-first : First (∁ [ α ,_]) [ α ,_] αs
      αs-first with first (Sum.swap ∘ Sum.fromDec ∘ [ α ,_]?) αs
      ... | inj₁ p = p
      ... | inj₂ q = ⊥-elim (All¬⇒¬Any q αs-any)

      ω : V *
      ω = lookup αs (First.index αs-first)

    generator : V *
    generator = ω

    generator≢ε : ω ≢ []
    generator≢ε = inits′-≢[] α α≢ε (First.index αs-first)

    generator-[,] : [ ω , α ]
    generator-[,] = [,]-sym α ω (First.index-satisfied αs-first)

    generator-min : ∀ δ → length δ < length ω → [ ω , δ ] → δ ≡ []
    generator-min δ ∣δ∣<∣ω∣ [ω,δ] = {!!}

  theorem : ∀ (S : Pred (V *) ℓ) → Dec ∃⟨ S ∩ (_≢ []) ⟩ → ++-commute S → Σ[ ω ∈ V * ] S ⊆ [ ω ]*
  theorem S (no ∄) _ = [] , λ
    { {[]} _ → 0 , refl
    ; {x ∷ xs} x∷xs∈S → ⊥-elim (∄ (x ∷ xs , x∷xs∈S , λ ()))
    }
  theorem S (yes (ω̃ , ω̃∈S , ω̃≢ε)) S[_,_] = {!!}
    where
      ω : V *
      ω = generator ω̃ ω̃≢ε

      ω≢ε : ω ≢ []
      ω≢ε = generator≢ε ω̃ ω̃≢ε

      [ω,ω̃] : [ ω , ω̃ ]
      [ω,ω̃] = generator-[,] ω̃ ω̃≢ε

      S̅ : Pred (V *) _
      S̅ = [ ω ,_]

      S⊆S̅ : S ⊆ S̅
      S⊆S̅ α∈S = [,]-trans ω̃≢ε [ω,ω̃] S[ ω̃∈S , α∈S ]

      S̅⊆[ω]* : S̅ ⊆ [ ω ]*
      S̅⊆[ω]* {α} [ω,α] = {!!}
