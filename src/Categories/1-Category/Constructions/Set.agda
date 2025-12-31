module Categories.1-Category.Constructions.Set where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Reflection.StrictEquiv
open import Categories.1-Category.Core

record Function {a} (A B : hSet a) : Type a where
  constructor function
  field
    fun : typ A → typ B

open Function public

module Function≡ {a} {A B : hSet a} where

  funEquiv : Function A B ≃ (typ A → typ B)
  funEquiv = strictEquiv fun function

  congFunEquiv : ∀ {f g : Function A B} → (f ≡ g) ≃ (f .fun ≡ g .fun)
  congFunEquiv = congEquiv funEquiv

  isInjective-fun : ∀ {f g : Function A B} → f .fun ≡ g .fun → f ≡ g
  isInjective-fun = invEq congFunEquiv

  isSet-Function : isSet (Function A B)
  isSet-Function = isOfHLevelRespectEquiv 2 (invEquiv funEquiv) (isSet→ (str B))

Set : ∀ a → Category (ℓ-suc a) a
Set a = record
  { Ob = hSet a
  ; Hom = Function
  ; id = λ x → λ { .fun a → a }
  ; _∘_ = λ f g → λ { .fun a → (f .fun (g .fun a)) }
  ; ∘-identityˡ = λ f → refl
  ; ∘-identityʳ = λ f → refl
  ; ∘-assoc = λ f g h → refl
  ; isSet-Hom = λ {x} {y} → Function≡.isSet-Function
  }
