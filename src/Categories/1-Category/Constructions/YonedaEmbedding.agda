module Categories.1-Category.Constructions.YonedaEmbedding where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Categories.1-Category.Core hiding (Hom)
open import Categories.1-Category.Constructions.Opposite
open import Categories.1-Category.Constructions.FunctorCategory using ([_,_])
open import Categories.1-Category.Constructions.HSet
open import Categories.1-Category.Constructions.HomFunctor

open Functor renaming (F₀ to ₀)

module _ {a b} (C : Category a b) where

  open Category C hiding (Hom)

  よ : Functor C [ C ^op , hSet b ]
  よ = record
    { F₀ = λ y → record { F₀ = λ x → Hom[-,-] C .₀ (x , y)
                        ; F₁ = λ f g → f ⋆ g
                        ; respect-id = λ x → funExt λ f → ⋆-identityˡ f
                        ; respect-⋆ = λ f g → funExt λ h → ⋆-assoc g f h
                        }
    ; F₁ = λ f → record { fun = λ x g → g ⋆ f; natural = λ g → funExt λ h → ⋆-assoc g h f }
    ; respect-id = λ x → isInjectiveFun _ _ _ _ (funExt λ x → funExt λ f → ⋆-identityʳ f)
    ; respect-⋆ = λ f g → isInjectiveFun _ _ _ _ (funExt λ x → funExt λ h → sym (⋆-assoc h f g))
    }

module _ {a b} (C : Category a b) where

  よcov : Functor (C ^op) [ C , hSet b ]
  よcov = subst (λ X → Functor (C ^op) [ X , hSet b ])
                (^op-involutive C)
                (よ (C ^op))
