module Categories.1-Category.Constructions.Opposite where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Categories.1-Category.Core

_^op : ∀ {a b} (C : Category a b) → Category a b
C ^op = record
  { Ob = C .Ob
  ; Hom = λ x y → C .Hom y x
  ; id = id
  ; _⋆_ = λ f g → g ⋆ f
  ; ⋆-identityˡ = ⋆-identityʳ
  ; ⋆-identityʳ = ⋆-identityˡ
  ; ⋆-assoc = λ f g h → sym (⋆-assoc h g f)
  ; isSet-Hom = C .isSet-Hom
  }
  where open Category C

^op-involutive : ∀ {a b} (C : Category a b) → C ^op ^op ≡ C
^op-involutive C = refl
