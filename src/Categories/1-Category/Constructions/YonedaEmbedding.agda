module Categories.1-Category.Constructions.YonedaEmbedding where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Categories.1-Category.Core
open import Categories.1-Category.Constructions.Opposite
open import Categories.1-Category.Constructions.FunctorCategory using ([_,_])
open import Categories.1-Category.Constructions.HSet
open import Categories.1-Category.Constructions.HomFunctor

module _ {a b} (C : Category a b) where

  private
    module C = Category C

  よ : Functor C [ C ^op , HSet b ]
  よ = record
    { F₀ = λ y → record { F₀ = λ x → Hom.₀ (x , y)
                        ; F₁ = λ f → λ { .fun g → f C.⋆ g }
                        ; respect-id = λ x → Function≡.isInjectiveFun _ _ (funExt λ f → C.⋆-identityˡ f)
                        ; respect-⋆ = λ f g → Function≡.isInjectiveFun _ _ (funExt λ h → C.⋆-assoc g f h)
                        }
    ; F₁ = λ f → record { fun = λ x → λ { .fun g → g C.⋆ f }
                        ; natural = λ g → Function≡.isInjectiveFun _ _ (funExt λ h → C.⋆-assoc g h f)
                        }
    ; respect-id = λ x → NatTrans≡.isInjectiveFun _ _ _ _ (funExt λ x → Function≡.isInjectiveFun _ _ (funExt λ f → C.⋆-identityʳ f))
    ; respect-⋆ = λ f g → NatTrans≡.isInjectiveFun _ _ _ _ (funExt λ x → Function≡.isInjectiveFun _ _ (funExt λ h → sym (C.⋆-assoc h f g)))
    }
    where
      module Hom = FunctorNotation (Hom[-,-] C)

module _ {a b} (C : Category a b) where

  よcov : Functor (C ^op) [ C , HSet b ]
  よcov = subst (λ X → Functor (C ^op) [ X , HSet b ])
                (^op-involutive C)
                (よ (C ^op))
