module Categories.1-Category.Constructions.HomFunctor where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
import Cubical.Data.Sigma.Base as Σ

open import Categories.1-Category.Core
open import Categories.1-Category.Constructions.HSet
open import Categories.1-Category.Constructions.Opposite
open import Categories.1-Category.Constructions.ProductCategory

Hom[-,-] : ∀ {a b} (C : Category a b) → Functor (C ^op × C) (HSet b)
Hom[-,-] C = record
  { F₀ = λ (x , y) → C.Hom x y , C.isSet-Hom
  ; F₁ = λ (f , g) → λ { .fun h → f C.⋆ (h C.⋆ g) }
  ; respect-id = λ (x , y) → Function≡.isInjectiveFun _ _ (funExt λ h → cong (C.id x C.⋆_) (C.⋆-identityʳ h) ∙ C.⋆-identityˡ h)
  ; respect-⋆ = λ (f₁ , f₂) (g₁ , g₂) → Function≡.isInjectiveFun _ _ (funExt λ h → C.⋆-assoc _ _ _ ∙ cong (g₁ C.⋆_) (sym (C.⋆-assoc _ _ _ ∙ cong (f₁ C.⋆_) (C.⋆-assoc _ _ _))))
  }
  where
    module C = Category C
