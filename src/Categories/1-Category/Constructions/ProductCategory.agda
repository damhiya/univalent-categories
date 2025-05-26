module Categories.1-Category.Constructions.ProductCategory where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Cubical.Foundations.HLevels
import Cubical.Data.Sigma as Σ
open import Categories.1-Category.Core

infixr 5 _×_

_×_ : ∀ {a b c d} → Category a b → Category c d → Category (a ⊔ c) (b ⊔ d)
C × D =
  record
  { Ob = C.Ob Σ.× D.Ob
  ; Hom = λ (c , d) (c′ , d′) → C.Hom c c′ Σ.× D.Hom d d′
  ; id = λ (c , d) → C.id c , D.id d
  ; _⋆_ = λ (f , g) (f′ , g′) → f C.⋆ f′ , g D.⋆ g′
  ; ⋆-identityˡ = λ (f , g) → cong₂ _,_ (C.⋆-identityˡ f) (D.⋆-identityˡ g)
  ; ⋆-identityʳ = λ (f , g) → cong₂ _,_ (C.⋆-identityʳ f) (D.⋆-identityʳ g)
  ; ⋆-assoc = λ (f₁ , f₂) (g₁ , g₂) (h₁ , h₂) → cong₂ _,_ (C.⋆-assoc f₁ g₁ h₁) (D.⋆-assoc f₂ g₂ h₂)
  ; isSet-Hom = isSet× C.isSet-Hom D.isSet-Hom
  }
  where
    module C = Category C
    module D = Category D
