module Categories.1-Category.Constructions.HomFunctor where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
import Cubical.Data.Sigma.Base as Σ

open import Categories.1-Category.Core hiding (Hom)
open import Categories.1-Category.Constructions.HSet
open import Categories.1-Category.Constructions.Opposite
open import Categories.1-Category.Constructions.ProductCategory

Hom[-,-] : ∀ {a b} (C : Category a b) → Functor (C ^op × C) (hSet b)
Hom[-,-] C = record
  { F₀ = λ (x , y) → C[ x , y ] , C .isSet-Hom
  ; F₁ = λ (f , g) → λ h → f ⋆ (h ⋆ g)
  ; respect-id = λ (x , y) → funExt λ h → cong (id x ⋆_) (⋆-identityʳ h) ∙ ⋆-identityˡ h
  ; respect-⋆ = λ (f₁ , f₂) (g₁ , g₂) → funExt λ h → ⋆-assoc _ _ _ ∙ cong (g₁ ⋆_) (sym (⋆-assoc _ _ _ ∙ cong (f₁ ⋆_) (⋆-assoc _ _ _)))
  }
  where open Category C renaming (Hom to C[_,_])
