module Categories.1-Category.Constructions where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Cubical.Foundations.HLevels

open import Categories.1-Category.Core

import Cubical.Data.Unit as U
import Cubical.Data.Sigma as Σ

Unit : Category ℓ-zero ℓ-zero
Unit = record
  { Ob = U.Unit
  ; Hom = λ x y → U.Unit
  ; id = λ x → U.tt
  ; _⋆_ = λ f g → U.tt
  ; ⋆-identityˡ = λ f → refl
  ; ⋆-identityʳ = λ f → refl
  ; ⋆-assoc = λ f g h → refl
  ; isSet-Hom = U.isSetUnit
  }

_×_ : ∀ {a b c d} → Category a b → Category c d → Category (a ⊔ c) (b ⊔ d)
C × D =
  record
  { Ob = C .Ob Σ.× D .Ob
  ; Hom = λ (c , d) (c′ , d′) → C .Hom c c′ Σ.× D .Hom d d′
  ; id = λ (c , d) → id₁ c , id₂ d
  ; _⋆_ = λ (f , g) (f′ , g′) → f ⋆₁ f′ , g ⋆₂ g′
  ; ⋆-identityˡ = λ (f , g) → cong₂ _,_ (C .⋆-identityˡ f) (D .⋆-identityˡ g)
  ; ⋆-identityʳ = λ (f , g) → cong₂ _,_ (C .⋆-identityʳ f) (D .⋆-identityʳ g)
  ; ⋆-assoc = λ (f₁ , f₂) (g₁ , g₂) (h₁ , h₂) → cong₂ _,_ (C .⋆-assoc f₁ g₁ h₁) (D .⋆-assoc f₂ g₂ h₂)
  ; isSet-Hom = isSet× (C .isSet-Hom) (D .isSet-Hom)
  }
  where
    open Category C renaming (id to id₁; _⋆_ to _⋆₁_)
    open Category D renaming (id to id₂; _⋆_ to _⋆₂_)

Id : ∀ {a b} (C : Category a b) → Functor C C
Id C = record
  { F₀ = λ x → x
  ; F₁ = λ f → f
  ; F-id = λ x → refl
  ; F-⋆ = λ f g → refl
  }

module FunctorCategory
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
  ⋆-identityˡ {F = F} {G = G} α = isInjectiveFun F G (id F ⋆ α) α (funExt λ x → ⋆D-identityˡ (α .fun x))
    where
      open Category D renaming (id to idD; _⋆_ to _⋆D_; ⋆-identityˡ to ⋆D-identityˡ)
      open Functor F

  ⋆-identityʳ : ∀ {F G : Functor C D} (α : NatTrans F G) → α ⋆ id G ≡ α
  ⋆-identityʳ {F = F} {G = G} α = isInjectiveFun F G (α ⋆ id G) α (funExt λ x → ⋆D-identityʳ (α .fun x))
    where
      open Category D renaming (id to idD; _⋆_ to _⋆D_; ⋆-identityʳ to ⋆D-identityʳ)
      open Functor G renaming (F₀ to G₀; F₁ to G₁)

  ⋆-assoc : ∀ {F G H K : Functor C D} (α : NatTrans F G) (β : NatTrans G H) (γ : NatTrans H K) → (α ⋆ β) ⋆ γ ≡ α ⋆ (β ⋆ γ)
  ⋆-assoc {F = F} {K = K} α β γ = isInjectiveFun F K ((α ⋆ β) ⋆ γ) (α ⋆ (β ⋆ γ)) (funExt λ x → ⋆D-assoc (α .fun x) (β .fun x) (γ .fun x))
    where
      open Category D renaming (id to idD; _⋆_ to _⋆D_; ⋆-assoc to ⋆D-assoc)

[_,_] : ∀ {c₀ c₁ d₀ d₁} → Category c₀ c₁ → Category d₀ d₁ → Category (ℓ-suc (c₀ ⊔ c₁ ⊔ d₀ ⊔ d₁)) (c₀ ⊔ c₁ ⊔ d₁)
[ C , D ] =
  record
  { Ob = Functor C D
  ; Hom = NatTrans
  ; id = FunctorCategory.id
  ; _⋆_ = FunctorCategory._⋆_
  ; ⋆-identityˡ = FunctorCategory.⋆-identityˡ
  ; ⋆-identityʳ = FunctorCategory.⋆-identityʳ
  ; ⋆-assoc = FunctorCategory.⋆-assoc
  ; isSet-Hom = λ {F G} → isSet-NatTrans F G
  }
