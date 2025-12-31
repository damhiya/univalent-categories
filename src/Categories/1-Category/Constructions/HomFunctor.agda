module Categories.1-Category.Constructions.HomFunctor where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
import Cubical.Data.Sigma.Base as Σ

open import Categories.1-Category.Core
open import Categories.1-Category.Constructions.Set
open import Categories.1-Category.Constructions.Opposite
open import Categories.1-Category.Constructions.ProductCategory

Hom[-,-] : ∀ {a b} (C : Category a b) → Functor (C ^op × C) (Set b)
Hom[-,-] C = record
  { F₀ = λ (x , y) → C.Hom x y , C.isSet-Hom
  ; F₁ = λ (f , g) → λ { .fun h → g C.∘ (h C.∘ f) }
  ; respect-id = λ (x , y) → Function≡.isInjective-fun (funExt λ h → C.∘-identityˡ (h C.∘ C.id x) ∙ C.∘-identityʳ h)
  ; respect-∘ = λ (f₁ , f₂) (g₁ , g₂) → Function≡.isInjective-fun (funExt λ h → C.∘-assoc _ _ _ ∙ cong (g₂ C.∘_) (cong (f₂ C.∘_) (sym (C.∘-assoc _ _ _)) ∙ sym (C.∘-assoc _ _ _)))
  }
  where
    module C = Category C
