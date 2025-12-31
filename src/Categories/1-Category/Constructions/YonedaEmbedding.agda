module Categories.1-Category.Constructions.YonedaEmbedding where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Categories.1-Category.Core
open import Categories.1-Category.Constructions.Opposite
open import Categories.1-Category.Constructions.FunctorCategory using ([_,_])
open import Categories.1-Category.Constructions.HSet

module _ {a b} (C : Category a b) where

  private
    module C = Category C

  よ₀ : C.Ob → Functor (C ^op) (HSet b)
  よ₀ y = record
    { F₀ = λ x → C.Hom x y , C.isSet-Hom
    ; F₁ = λ f → λ { .fun g → g C.∘ f }
    ; respect-id = λ x → Function≡.isInjective-fun (funExt λ f → C.∘-identityʳ f)
    ; respect-∘ = λ f g → Function≡.isInjective-fun (funExt λ h → sym (C.∘-assoc g f h))
    }

  よ₁ : ∀ {x y} → C.Hom x y → NatTrans (よ₀ x) (よ₀ y)
  よ₁ f = record
    { fun = λ x → λ { .fun g → f C.∘ g }
    ; natural = λ g → Function≡.isInjective-fun (funExt λ h → sym (C.∘-assoc g h f))
    }

  よ : Functor C [ C ^op , HSet b ]
  よ = record
    { F₀ = よ₀
    ; F₁ = よ₁
    ; respect-id = λ x → NatTrans≡.isInjective-fun _ _ _ _ (funExt λ x → Function≡.isInjective-fun (funExt λ f → C.∘-identityˡ f))
    ; respect-∘ = λ f g → NatTrans≡.isInjective-fun _ _ _ _ (funExt λ x → Function≡.isInjective-fun (funExt λ h → C.∘-assoc h f g))
    }

module _ {a b} (C : Category a b) where

  よcov : Functor (C ^op) [ C , HSet b ]
  よcov = subst (λ X → Functor (C ^op) [ X , HSet b ])
                (^op-involutive C)
                (よ (C ^op))
