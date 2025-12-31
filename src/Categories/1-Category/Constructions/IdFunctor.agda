module Categories.1-Category.Constructions.IdFunctor where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Categories.1-Category.Core

id : ∀ {a b} (C : Category a b) → Functor C C
id C = record
  { F₀ = λ x → x
  ; F₁ = λ f → f
  ; respect-id = λ x → refl
  ; respect-∘ = λ f g → refl
  }
