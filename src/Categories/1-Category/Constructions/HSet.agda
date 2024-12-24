module Categories.1-Category.Constructions.HSet where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels renaming (hSet to ⟨hSet⟩)
open import Categories.1-Category.Core

hSet : ∀ a → Category (ℓ-suc a) a
hSet a = record
  { Ob = ⟨hSet⟩ a
  ; Hom = λ x y → typ x → typ y
  ; id = λ x → λ a → a
  ; _⋆_ = λ f g → λ a → g (f a)
  ; ⋆-identityˡ = λ f → refl
  ; ⋆-identityʳ = λ f → refl
  ; ⋆-assoc = λ f g h → refl
  ; isSet-Hom = λ {x} {y} → isSet→ (str y)
  }
