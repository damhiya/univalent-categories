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

module Cat
  {a b : Level}
  where

  id : ∀ (C : Category a b) → Functor C C
  id C = record
    { F₀ = λ x → x
    ; F₁ = λ f → f
    ; F-id = λ x → refl
    ; F-⋆ = λ f g → refl
    }
