module Categories.1-Category.Constructions.HSet where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Categories.1-Category.Core

record Function {a} (A B : hSet a) : Type a where
  field
    fun : typ A → typ B

open Function public

module Function≡ {a} {A B : hSet a} where

  isInjectiveFun : ∀ (f g : Function A B) → f .fun ≡ g .fun → f ≡ g
  isInjectiveFun f g p i .fun = p i

  isInjectiveFun-refl : ∀ (f : Function A B) → isInjectiveFun f f refl ≡ refl
  isInjectiveFun-refl f = refl

  isEmbedding-fun : ∀ (f g : Function A B) → isEquiv (λ (p : f ≡ g) → cong fun p)
  isEmbedding-fun f g .equiv-proof e = center , contract
    where
      center : fiber (λ (p : f ≡ g) → cong fun p) e
      center = isInjectiveFun f g e , refl

      contract : ∀ z → center ≡ z
      contract (p , q) = J (λ e q → (isInjectiveFun f g e , refl) ≡ (p , q))
                           (J (λ g p → (isInjectiveFun f g (cong fun p) , refl) ≡ (p , refl {x = cong fun p}))
                              (λ i → isInjectiveFun-refl f i , refl)
                              p)
                           q

  Function≡Equiv : ∀ (f g : Function A B) → (f ≡ g) ≃ (f .fun ≡ g .fun)
  Function≡Equiv f g = cong fun , isEmbedding-fun f g

  isSet-Function : isSet (Function A B)
  isSet-Function f g = subst isProp (sym (ua (Function≡Equiv f g))) (isSet→ (str B) (f .fun) (g .fun))

HSet : ∀ a → Category (ℓ-suc a) a
HSet a = record
  { Ob = hSet a
  ; Hom = Function
  ; id = λ x → λ { .fun a → a }
  ; _⋆_ = λ f g → λ { .fun a → (g .fun (f .fun a)) }
  ; ⋆-identityˡ = λ f → refl
  ; ⋆-identityʳ = λ f → refl
  ; ⋆-assoc = λ f g h → refl
  ; isSet-Hom = λ {x} {y} → Function≡.isSet-Function
  }
