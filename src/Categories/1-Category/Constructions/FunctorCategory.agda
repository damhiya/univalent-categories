module Categories.1-Category.Constructions.FunctorCategory where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Categories.1-Category.Core

module _
  {a b c d}
  {C : Category a b}
  {D : Category c d}
  where

  id : ∀ (F : Functor C D) → NatTrans F F
  id F =
    record
    { fun = λ x → idD (F₀ x)
    ; natural = λ f → ⋆-identityʳ (F₁ f) ∙ sym (⋆-identityˡ (F₁ f))
    }
    where
      open Category D renaming (id to idD)
      open Functor F

  _⋆_ : ∀ {F G H : Functor C D} → NatTrans F G → NatTrans G H → NatTrans F H
  _⋆_ {F = F} {G = G} {H = H} α β =
    record
    { fun = λ x → α .fun x ⋆D β .fun x
    ; natural = λ {x} {y} f →
        sym (⋆-assoc (F₁ f) (α .fun y) (β .fun y)) ∙
        cong (_⋆D β .fun y) (α .natural f) ∙
        ⋆-assoc (α .fun x) (G₁ f) (β .fun y) ∙
        cong (α .fun x ⋆D_) (β .natural f) ∙
        sym (⋆-assoc (α .fun x) (β .fun x) (H₁ f))
    }
    where
      open Category D renaming (_⋆_ to _⋆D_)
      open Functor F renaming (F₁ to F₁)
      open Functor G renaming (F₁ to G₁)
      open Functor H renaming (F₁ to H₁)

  ⋆-identityˡ : ∀ {F G : Functor C D} (α : NatTrans F G) → id F ⋆ α ≡ α
  ⋆-identityˡ {F = F} {G = G} α = NatTrans≡.isInjectiveFun F G (id F ⋆ α) α (funExt λ x → ⋆D-identityˡ (α .fun x))
    where
      open Category D renaming (id to idD; _⋆_ to _⋆D_; ⋆-identityˡ to ⋆D-identityˡ)
      open Functor F

  ⋆-identityʳ : ∀ {F G : Functor C D} (α : NatTrans F G) → α ⋆ id G ≡ α
  ⋆-identityʳ {F = F} {G = G} α = NatTrans≡.isInjectiveFun F G (α ⋆ id G) α (funExt λ x → ⋆D-identityʳ (α .fun x))
    where
      open Category D renaming (id to idD; _⋆_ to _⋆D_; ⋆-identityʳ to ⋆D-identityʳ)
      open Functor G renaming (F₀ to G₀; F₁ to G₁)

  ⋆-assoc : ∀ {F G H K : Functor C D} (α : NatTrans F G) (β : NatTrans G H) (γ : NatTrans H K) → (α ⋆ β) ⋆ γ ≡ α ⋆ (β ⋆ γ)
  ⋆-assoc {F = F} {K = K} α β γ = NatTrans≡.isInjectiveFun F K ((α ⋆ β) ⋆ γ) (α ⋆ (β ⋆ γ)) (funExt λ x → ⋆D-assoc (α .fun x) (β .fun x) (γ .fun x))
    where
      open Category D renaming (id to idD; _⋆_ to _⋆D_; ⋆-assoc to ⋆D-assoc)

[_,_] : ∀ {c₀ c₁ d₀ d₁} → Category c₀ c₁ → Category d₀ d₁ → Category (ℓ-suc (c₀ ⊔ c₁ ⊔ d₀ ⊔ d₁)) (c₀ ⊔ c₁ ⊔ d₁)
[ C , D ] =
  record
  { Ob = Functor C D
  ; Hom = NatTrans
  ; id = id
  ; _⋆_ = _⋆_
  ; ⋆-identityˡ = ⋆-identityˡ
  ; ⋆-identityʳ = ⋆-identityʳ
  ; ⋆-assoc = ⋆-assoc
  ; isSet-Hom = λ {F G} → NatTrans≡.isSet-NatTrans F G
  }
