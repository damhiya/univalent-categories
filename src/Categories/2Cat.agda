module Categories.2Cat where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_) hiding (_∙_)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

import Categories.1Cat as C¹

record Category a b c : Type (ℓ-suc (a ⊔ b ⊔ c)) where

  infix 5 _≅²_
  infixr 7 _∙_

  field
    Ob : Type a

  field
    Hom¹ : Ob → Ob → Type b
    Hom² : ∀ {x y} → Hom¹ x y → Hom¹ x y → Type c
    id² : ∀ {x y} (f : Hom¹ x y) → Hom² f f
    _∙_ : ∀ {x y} {f g h : Hom¹ x y} → Hom² f g → Hom² g h → Hom² f h
    ∙-identityˡ : ∀ {x y} {f g : Hom¹ x y} (α : Hom² f g) → id² f ∙ α ≡ α
    ∙-identityʳ : ∀ {x y} {f g : Hom¹ x y} (α : Hom² f g) → α ∙ id² g ≡ α
    ∙-assoc : ∀ {x y} {f g h i : Hom¹ x y} (α : Hom² f g) (β : Hom² g h) (γ : Hom² h i) → (α ∙ β) ∙ γ ≡ α ∙ (β ∙ γ)
    isSet-Hom² : ∀ {x y} {f g : Hom¹ x y} → isSet (Hom² f g)

  Hom : ∀ (x y : Ob) → C¹.Category b c
  Hom x y =
    record
    { Ob = Hom¹ x y
    ; Hom = Hom²
    ; id = id²
    ; _⋆_ = _∙_
    ; ⋆-identityˡ = ∙-identityˡ
    ; ⋆-identityʳ = ∙-identityʳ
    ; ⋆-assoc = ∙-assoc
    ; isSet-Hom = isSet-Hom²
    }

  _≅²_ : ∀ {x y : Ob} (f g : Hom¹ x y) → Type c
  _≅²_ {x} {y} = C¹._≅_ (Hom x y)

  field
    id¹ : ∀ x → Hom¹ x x

  field
    _⋆¹_ : ∀ {x y z} → Hom¹ x y → Hom¹ y z → Hom¹ x z
    _⋆²_ : ∀ {x y z} {f f′ : Hom¹ x y} {g g′ : Hom¹ y z} → Hom² f f′ → Hom² g g′ → Hom² (f ⋆¹ g) (f′ ⋆¹ g′)
    ⋆-preserve-id² : ∀ {x y z} {f : Hom¹ x y} {g : Hom¹ y z} → id² f ⋆² id² g ≡ id² (f ⋆¹ g)
    ⋆-preserve-∙ : ∀ {x y z} {f f′ f″ : Hom¹ x y} {g g′ g″ : Hom¹ y z} (α : Hom² f f′) (α′ : Hom² f′ f″) (β : Hom² g g′) (β′ : Hom² g′ g″) →
                   (α ∙ α′) ⋆² (β ∙ β′) ≡ (α ⋆² β) ∙ (α′ ⋆² β′)

  compose : ∀ {x y z} → C¹.Functor (Hom x y C¹.× Hom y z) (Hom x z)
  compose {x} {y} {z} =
    record
    { F₀ = λ (f , g) → f ⋆¹ g
    ; F₁ = λ (α , β) → α ⋆² β
    ; F-id = ⋆-preserve-id²
    ; F-⋆ = λ f g → ⋆-preserve-∙ (f .fst) (g .fst) (f .snd) (g .snd)
    }

  field
    lunit : ∀ {x y} (f : Hom¹ x y) → id¹ x ⋆¹ f ≅² f
    lunit-natural : ∀ {x y} {f f′ : Hom¹ x y} (α : Hom² f f′) →
                    (id² (id¹ x) ⋆² α) ∙ lunit f′ .C¹.fwd ≡ lunit f .C¹.fwd ∙ α
    runit : ∀ {x y} (f : Hom¹ x y) → f ⋆¹ id¹ y ≅² f
    runit-natural : ∀ {x y} {f f′ : Hom¹ x y} (α : Hom² f f′) →
                    (α ⋆² id² (id¹ y)) ∙ runit f′ .C¹.fwd ≡ runit f .C¹.fwd ∙ α
    assoc : ∀ {x y z w} (f : Hom¹ x y) (g : Hom¹ y z) (h : Hom¹ z w) →
            (f ⋆¹ g) ⋆¹ h ≅² f ⋆¹ (g ⋆¹ h)
    assoc-natural : ∀ {x y z w} {f f′ : Hom¹ x y} {g g′ : Hom¹ y z} {h h′ : Hom¹ z w} (α : Hom² f f′) (β : Hom² g g′) (γ : Hom² h h′) →
                    ((α ⋆² β) ⋆² γ) ∙ assoc f′ g′ h′ .C¹.fwd ≡ assoc f g h .C¹.fwd ∙ ((α ⋆² (β ⋆² γ)))

  field
    pentagon : ∀ {a b c d e} (f : Hom¹ a b) (g : Hom¹ b c) (h : Hom¹ c d) (i : Hom¹ d e) →
               assoc (f ⋆¹ g) h i .C¹.fwd ∙ assoc f g (h ⋆¹ i) .C¹.fwd
                 ≡ ((assoc f g h .C¹.fwd ⋆² id² i) ∙ assoc f (g ⋆¹ h) i .C¹.fwd ∙ (id² f ⋆² assoc g h i .C¹.fwd))
    triangle : ∀ {x y z} (f : Hom¹ x y) (g : Hom¹ y z) →
               runit f .C¹.fwd ⋆² id² g ≡ assoc f (id¹ y) g .C¹.fwd ∙ (id² f ⋆² lunit g .C¹.fwd)
