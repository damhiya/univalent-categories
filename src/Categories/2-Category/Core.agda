module Categories.2-Category.Core where

open import Cubical.Foundations.Prelude as P renaming (ℓ-max to _⊔_) hiding (_∙_)

import Categories.1-Category.Core as C¹
import Categories.1-Category.Constructions as C¹

record Category a b c : Type (ℓ-suc (a ⊔ b ⊔ c)) where

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

  field
    id¹ : ∀ x → Hom¹ x x
    _⋆¹_ : ∀ {x y z} → Hom¹ x y → Hom¹ y z → Hom¹ x z
    _⋆²_ : ∀ {x y z} {f f′ : Hom¹ x y} {g g′ : Hom¹ y z} → Hom² f f′ → Hom² g g′ → Hom² (f ⋆¹ g) (f′ ⋆¹ g′)
    ⋆-preserve-id² : ∀ {x y z} (f : Hom¹ x y) (g : Hom¹ y z) → id² f ⋆² id² g ≡ id² (f ⋆¹ g)
    ⋆-preserve-∙ : ∀ {x y z} {f f′ f″ : Hom¹ x y} {g g′ g″ : Hom¹ y z} (α : Hom² f f′) (α′ : Hom² f′ f″) (β : Hom² g g′) (β′ : Hom² g′ g″) →
                   (α ∙ α′) ⋆² (β ∙ β′) ≡ (α ⋆² β) ∙ (α′ ⋆² β′)

  id : ∀ x → C¹.Functor C¹.Unit (Hom x x)
  id x =
    record
    { F₀ = λ _ → id¹ x
    ; F₁ = λ _ → id² (id¹ x)
    ; F-id = λ _ → refl
    ; F-⋆ = λ _ _ → sym (∙-identityˡ (id² (id¹ x)))
    }

  [-⋆-] : ∀ {x y z} → C¹.Functor (Hom x y C¹.× Hom y z) (Hom x z)
  [-⋆-] {x} {y} {z} =
    record
    { F₀ = λ (f , g) → f ⋆¹ g
    ; F₁ = λ (α , β) → α ⋆² β
    ; F-id = λ (f , g) → ⋆-preserve-id² f g
    ; F-⋆ = λ α β → ⋆-preserve-∙ (α .fst) (β .fst) (α .snd) (β .snd)
    }

  [id⋆-] : ∀ {x y} → C¹.Functor (Hom x y) (Hom x y)
  [id⋆-] {x} {y} =
    record
    { F₀ = λ f → id¹ x ⋆¹ f
    ; F₁ = λ α → id² (id¹ x) ⋆² α
    ; F-id = λ f → ⋆-preserve-id² (id¹ x) f
    ; F-⋆ = λ α β → cong (_⋆² (α ∙ β)) (sym (∙-identityˡ (id² (id¹ x)))) P.∙ ⋆-preserve-∙ (id² (id¹ x)) (id² (id¹ x)) α β
    }

  [-⋆id] : ∀ {x y} → C¹.Functor (Hom x y) (Hom x y)
  [-⋆id] {x} {y} =
    record
    { F₀ = λ f → f ⋆¹ id¹ y
    ; F₁ = λ α → α ⋆² id² (id¹ y)
    ; F-id = λ f → ⋆-preserve-id² f (id¹ y)
    ; F-⋆ = λ α β → cong ((α ∙ β) ⋆²_) (sym (∙-identityˡ (id² (id¹ y)))) P.∙ ⋆-preserve-∙ α β (id² (id¹ y)) (id² (id¹ y))
    }

  [[-⋆-]⋆-] : ∀ x y z w → C¹.Functor (Hom x y C¹.× (Hom y z C¹.× Hom z w)) (Hom x w)
  [[-⋆-]⋆-] x y z w =
    record
    { F₀ = λ (f , (g , h)) → (f ⋆¹ g) ⋆¹ h
    ; F₁ = λ (α , (β , γ)) → (α ⋆² β) ⋆² γ
    ; F-id = λ (f , (g , h)) → cong (_⋆² (id² h)) (⋆-preserve-id² f g) P.∙ ⋆-preserve-id² (f ⋆¹ g) h
    ; F-⋆ = λ (α₁ , (β₁ , γ₁)) (α₂ , (β₂ , γ₂)) → cong (_⋆² (γ₁ ∙ γ₂)) (⋆-preserve-∙ α₁ α₂ β₁ β₂) P.∙ ⋆-preserve-∙ (α₁ ⋆² β₁) (α₂ ⋆² β₂) γ₁ γ₂
    }

  [-⋆[-⋆-]] : ∀ x y z w → C¹.Functor (Hom x y C¹.× (Hom y z C¹.× Hom z w)) (Hom x w)
  [-⋆[-⋆-]] x y z w =
    record
    { F₀ = λ (f , (g , h)) → f ⋆¹ (g ⋆¹ h)
    ; F₁ = λ (α , (β , γ)) → α ⋆² (β ⋆² γ)
    ; F-id = λ (f , (g , h)) → cong ((id² f) ⋆²_) (⋆-preserve-id² g h) P.∙ ⋆-preserve-id² f (g ⋆¹ h)
    ; F-⋆ = λ (α₁ , (β₁ , γ₁)) (α₂ , (β₂ , γ₂)) → cong ((α₁ ∙ α₂) ⋆²_) (⋆-preserve-∙ β₁ β₂ γ₁ γ₂) P.∙ ⋆-preserve-∙ α₁ α₂ (β₁ ⋆² γ₁) (β₂ ⋆² γ₂) 
    }

  field
    lunit : ∀ {x y} (f : Hom¹ x y) → Hom² (id¹ x ⋆¹ f) f
    lunitInv : ∀ {x y} (f : Hom¹ x y) → Hom² f (id¹ x ⋆¹ f)
    lunit-rightInv : ∀ {x y} (f : Hom¹ x y) → lunit f ∙ lunitInv f ≡ id² (id¹ x ⋆¹ f)
    lunit-leftInv : ∀ {x y} (f : Hom¹ x y) → lunitInv f ∙ lunit f ≡ id² f
    lunit-natural : ∀ {x y} {f f′ : Hom¹ x y} (α : Hom² f f′) →
                    (id² (id¹ x) ⋆² α) ∙ lunit f′ ≡ lunit f ∙ α

    runit : ∀ {x y} (f : Hom¹ x y) → Hom² (f ⋆¹ id¹ y) f
    runitInv : ∀ {x y} (f : Hom¹ x y) → Hom² f (f ⋆¹ id¹ y)
    runit-rightInv : ∀ {x y} (f : Hom¹ x y) → runit f ∙ runitInv f ≡ id² (f ⋆¹ id¹ y)
    runit-leftInv : ∀ {x y} (f : Hom¹ x y) → runitInv f ∙ runit f ≡ id² f
    runit-natural : ∀ {x y} {f f′ : Hom¹ x y} (α : Hom² f f′) →
                    (α ⋆² id² (id¹ y)) ∙ runit f′ ≡ runit f ∙ α

    assoc : ∀ {x y z w} (f : Hom¹ x y) (g : Hom¹ y z) (h : Hom¹ z w) →
            Hom² ((f ⋆¹ g) ⋆¹ h) (f ⋆¹ (g ⋆¹ h))
    assocInv : ∀ {x y z w} (f : Hom¹ x y) (g : Hom¹ y z) (h : Hom¹ z w) →
               Hom² (f ⋆¹ (g ⋆¹ h)) ((f ⋆¹ g) ⋆¹ h)
    assoc-rightInv : ∀ {x y z w} (f : Hom¹ x y) (g : Hom¹ y z) (h : Hom¹ z w) →
                     assoc f g h ∙ assocInv f g h ≡ id² ((f ⋆¹ g) ⋆¹ h)
    assoc-leftInv : ∀ {x y z w} (f : Hom¹ x y) (g : Hom¹ y z) (h : Hom¹ z w) →
                    assocInv f g h ∙ assoc f g h ≡ id² (f ⋆¹ (g ⋆¹ h))
    assoc-natural : ∀ {x y z w} {f f′ : Hom¹ x y} {g g′ : Hom¹ y z} {h h′ : Hom¹ z w} (α : Hom² f f′) (β : Hom² g g′) (γ : Hom² h h′) →
                    ((α ⋆² β) ⋆² γ) ∙ assoc f′ g′ h′ ≡ assoc f g h ∙ ((α ⋆² (β ⋆² γ)))

  λ* : ∀ {x y} → C¹.NatIso [id⋆-] (C¹.Id (Hom x y))
  λ* {x} {y} =
    record
    { fun = lunit
    ; inv = lunitInv
    ; rightInv = lunit-rightInv
    ; leftInv = lunit-leftInv
    ; natural = lunit-natural
    }

  ρ* : ∀ {x y} → C¹.NatIso [-⋆id] (C¹.Id (Hom x y))
  ρ* =
    record
    { fun = runit
    ; inv = runitInv
    ; rightInv = runit-rightInv
    ; leftInv = runit-leftInv
    ; natural = runit-natural
    }

  α* : ∀ {x y z w} → C¹.NatIso ([[-⋆-]⋆-] x y z w) ([-⋆[-⋆-]] x y z w)
  α* {x} {y} {z} {w} =
    record
    { fun = λ (f , (g , h)) → assoc f g h
    ; inv = λ (f , (g , h)) → assocInv f g h
    ; rightInv = λ (f , (g , h)) → assoc-rightInv f g h
    ; leftInv = λ (f , (g , h)) → assoc-leftInv f g h
    ; natural = λ (α , (β , γ)) → assoc-natural α β γ
    }

  field
    pentagon : ∀ {a b c d e} (f : Hom¹ a b) (g : Hom¹ b c) (h : Hom¹ c d) (i : Hom¹ d e) →
               assoc (f ⋆¹ g) h i ∙ assoc f g (h ⋆¹ i)
                 ≡ ((assoc f g h ⋆² id² i) ∙ assoc f (g ⋆¹ h) i ∙ (id² f ⋆² assoc g h i))
    triangle : ∀ {x y z} (f : Hom¹ x y) (g : Hom¹ y z) →
               runit f ⋆² id² g ≡ assoc f (id¹ y) g ∙ (id² f ⋆² lunit g)
