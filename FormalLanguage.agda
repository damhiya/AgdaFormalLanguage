{-# OPTIONS --without-K --safe #-}

module FormalLanguage where

open import Data.Empty
open import Data.Fin.Base as Fin using (Fin; suc; zero; fromℕ; toℕ)
open import Data.List.Base as List hiding ([_])
open import Data.List.Properties
open import Data.List.Relation.Unary.First as First using (First; first)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Unary.All.Properties using (All¬⇒¬Any)
open import Data.Nat.Base hiding (_^_)
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Base
open import Induction.WellFounded
open import Level using (Level)
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties
open import Relation.Nullary
open import Relation.Nullary.Negation
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

  subtract-commute : [ α , subtract α β ]
  subtract-commute = [α,η]

module _ (V : Set a) (_≟_ : DecidableEquality V) where

  [_,_]? : Decidable ([_,_] {V = V})
  [_,_]? α β = ≡-dec _≟_ (α ++ β) (β ++ α)

  module _ (α : V *) (α≢ε : α ≢ [] ) where

    private
      αs : List (V *)
      αs = inits′′ α

      αs-Any : Any ([ α ,_]) αs
      αs-Any = subst (Any [ α ,_]) (cong inits′′ (++-identityʳ α)) (lookup-any (inits′′ (α ++ [])) i p)
        where
          i = indexOfInits′′[ α ++ [] ] α≢ε
          eq = lookup-indexOfInits′′[ α ++ [] ] α≢ε
          p = subst [ α ,_] (sym eq) ([,]-refl α)

      αs-First : First (∁ [ α ,_]) [ α ,_] αs
      αs-First = Sum.[ id , (λ αs-All → ⊥-elim (All¬⇒¬Any αs-All αs-Any)) ]′ (first (Sum.swap ∘ Sum.fromDec ∘ [ α ,_]?) αs)

      i : Fin (length αs)
      i = First.index αs-First

      ω : V *
      ω = lookup αs i

      ω≢ε : ω ≢ []
      ω≢ε = subst (_≢ []) (sym (lookup-inits′′ α i)) (take≢[] 1+n≢0 α≢ε)

      [α,ω] : [ α , ω ]
      [α,ω] = First.index-satisfied αs-First

    generator : V *
    generator = ω

    generator≢ε : ω ≢ []
    generator≢ε = ω≢ε

    generator-[,] : [ ω , α ]
    generator-[,] = [,]-sym α ω [α,ω]

    generator-min : ∀ δ (∣δ∣<∣ω∣ : length δ < length ω) ([ω,δ] : [ ω , δ ]) → δ ≡ []
    generator-min δ ∣δ∣<∣ω∣ [ω,δ] = decidable-stable (≡[]-dec δ) ¬¬δ≡ε
      where
        [α,δ] : [ α , δ ]
        [α,δ] = [,]-trans ω≢ε [α,ω] [ω,δ]

        η₁ : V *
        η₁ = subtract δ ω

        δη₁≡ω : δ ++ η₁ ≡ ω
        δη₁≡ω = subtract-++ʳ δ ω (<⇒≤ ∣δ∣<∣ω∣) ([,]-sym ω δ [ω,δ])

        η₂ : V *
        η₂ = drop (ℕ.suc (toℕ i)) α

        ωη₂≡α : ω ++ η₂ ≡ α
        ωη₂≡α = subst (λ ω → ω ++ η₂ ≡ α) (sym (lookup-inits′′ α i)) (take++drop (ℕ.suc (toℕ i)) α)

        η : V *
        η = η₁ ++ η₂

        δη≡α : δ ++ η ≡ α
        δη≡α = begin
          δ ++ η₁ ++ η₂   ≡˘⟨ ++-assoc δ η₁ η₂ ⟩
          (δ ++ η₁) ++ η₂ ≡⟨ cong (_++ η₂) δη₁≡ω ⟩
          ω ++ η₂         ≡⟨ ωη₂≡α ⟩
          α               ∎
          where open ≡-Reasoning

        ¬¬δ≡ε : δ ≢ [] → ⊥
        ¬¬δ≡ε δ≢ε = <⇒≱ ∣δ∣<∣ω∣ ∣ω∣≤∣δ∣
          where
            ȷ : Fin (length (inits′′ (δ ++ η)))
            ȷ = indexOfInits′′[ δ ++ η ] δ≢ε

            j : Fin (length αs)
            j = subst Fin (cong (length ∘ inits′′) δη≡α) ȷ

            αs[j]≡δ : lookup αs j ≡ δ
            αs[j]≡δ = begin
              lookup αs j                                                                     ≡⟨ lookup-subst (sym (cong inits′′ δη≡α)) j ⟩
              lookup (inits′′ (δ ++ η)) (subst Fin (cong length (sym (cong inits′′ δη≡α))) j) ≡⟨ cong (λ p → lookup (inits′′ (δ ++ η)) (subst Fin p j)) 𝕡 ⟩
              lookup (inits′′ (δ ++ η)) (subst Fin (sym p) (subst Fin p ȷ))                   ≡⟨ cong (lookup (inits′′ (δ ++ η))) (subst-sym-subst p) ⟩
              lookup (inits′′ (δ ++ η)) ȷ                                                     ≡⟨ lookup-indexOfInits′′[ δ ++ η ] δ≢ε ⟩
              δ                                                                               ∎
              where
                open ≡-Reasoning
                p = cong (length ∘ inits′′) δη≡α
                𝕡 = begin
                  cong length (sym (cong inits′′ δη≡α)) ≡⟨ cong-sym length _ ⟩
                  sym (cong length (cong inits′′ δη≡α)) ≡⟨ cong sym (sym (cong-∘ δη≡α)) ⟩
                  sym p                                 ∎

            ∣αs[j]∣≡1+j : length (lookup αs j) ≡ suc (toℕ j)
            ∣αs[j]∣≡1+j = length-lookup-inits′′ α j

            ∣δ∣≡1+j : length δ ≡ suc (toℕ j)
            ∣δ∣≡1+j = subst (λ δ → length δ ≡ suc (toℕ j)) αs[j]≡δ ∣αs[j]∣≡1+j

            ∣ω∣≡1+i : length ω ≡ suc (toℕ i)
            ∣ω∣≡1+i = length-lookup-inits′′ α i

            i≤j : i Fin.≤ j
            i≤j = index-min αs αs-First j (contradiction (subst [ α ,_] (sym αs[j]≡δ) [α,δ]))

            ∣ω∣≤∣δ∣ : length ω ≤ length δ
            ∣ω∣≤∣δ∣ = begin
              length ω  ≡⟨ ∣ω∣≡1+i ⟩
              1 + toℕ i ≤⟨ s≤s i≤j ⟩
              1 + toℕ j ≡˘⟨ ∣δ∣≡1+j ⟩
              length δ  ∎
              where open ≤-Reasoning

    generator-factorize-rec : ∀ α → Acc _<_ (length α) → [ ω , α ] → ∃[ n ] α ≡ ω ^ n
    generator-factorize-rec α (acc rs) [ω,α] with length α <? length ω
    ... | yes ∣α∣<∣ω∣ = 0 , generator-min α ∣α∣<∣ω∣ [ω,α]
    ... | no  ∣α∣≮∣ω∣ = suc (proj₁ n,η≡ω^n) , trans α≡ωη (cong (ω ++_) (proj₂ n,η≡ω^n))
      where
        ∣ω∣>0 : length ω > 0
        ∣ω∣>0 = ≢[]⇒length≥1 ω≢ε

        ∣ω∣≤∣α∣ : length ω ≤ length α
        ∣ω∣≤∣α∣ = ≮⇒≥ ∣α∣≮∣ω∣

        η : V *
        η = subtract ω α

        ∣η∣<∣α∣ : length η < length α
        ∣η∣<∣α∣ = begin-strict
          length η                              ≡⟨⟩
          length (take (length α ∸ length ω) α) ≡⟨ length-take (length α ∸ length ω) α ⟩
          (length α ∸ length ω) ⊓ length α      ≡⟨ m≤n⇒m⊓n≡m (m∸n≤m (length α) (length ω)) ⟩
          length α ∸ length ω                   <⟨ m>0∧n>0⇒m∸n<m (<-transˡ ∣ω∣>0 ∣ω∣≤∣α∣) ∣ω∣>0 ⟩
          length α                              ∎
          where open ≤-Reasoning

        [ω,η] : [ ω , η ]
        [ω,η] = subtract-commute ω α ∣ω∣≤∣α∣ [ω,α]

        α≡ωη : α ≡ ω ++ η
        α≡ωη = sym (subtract-++ʳ ω α ∣ω∣≤∣α∣ [ω,α])

        n,η≡ω^n : ∃[ n ] η ≡ ω ^ n
        n,η≡ω^n = generator-factorize-rec η (rs (length η) ∣η∣<∣α∣) [ω,η]

    generator-factorize : ∀ α → [ ω , α ] → ∃[ n ] α ≡ ω ^ n
    generator-factorize α [ω,α] = generator-factorize-rec α (<-wellFounded (length α)) [ω,α]

  theorem : ∀ (S : Pred (V *) ℓ) → Dec ∃⟨ S ∩ (_≢ []) ⟩ → ++-commute S → Σ[ ω ∈ V * ] S ⊆ [ ω ]*
  theorem S (no ∄) _ = [] , λ
    { {[]} _ → 0 , refl
    ; {x ∷ xs} x∷xs∈S → ⊥-elim (∄ (x ∷ xs , x∷xs∈S , λ ()))
    }
  theorem S (yes (ω̃ , ω̃∈S , ω̃≢ε)) S[_,_] = ω , S̅⊆[ω]* ∘ S⊆S̅
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
      S̅⊆[ω]* {α} [ω,α] = generator-factorize ω̃ ω̃≢ε α [ω,α]
