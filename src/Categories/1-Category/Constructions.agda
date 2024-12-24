module Categories.1-Category.Constructions where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)

open import Categories.1-Category.Core

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
