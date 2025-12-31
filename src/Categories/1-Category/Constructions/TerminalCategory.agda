module Categories.1-Category.Constructions.TerminalCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Categories.1-Category.Core

𝟏 : Category ℓ-zero ℓ-zero
𝟏 = record
  { Ob = Unit
  ; Hom = λ x y → Unit
  ; id = λ x → tt
  ; _∘_ = λ f g → tt
  ; ∘-identityˡ = λ f → refl
  ; ∘-identityʳ = λ f → refl
  ; ∘-assoc = λ f g h → refl
  ; isSet-Hom = isSetUnit
  }
