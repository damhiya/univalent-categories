module Categories.1-Category.Core where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Cubical.Foundations.Equiv

record Category a b : Type (ℓ-suc (a ⊔ b)) where
  field
    Ob : Type a
    Hom : Ob → Ob → Type b
    id : ∀ x → Hom x x
    _⋆_ : ∀ {x y z} → Hom x y → Hom y z → Hom x z
    ⋆-identityˡ : ∀ {x y} (f : Hom x y) → id x ⋆ f ≡ f
    ⋆-identityʳ : ∀ {x y} (f : Hom x y) → f ⋆ id y ≡ f
    ⋆-assoc : ∀ {x y z w} (f : Hom x y) (g : Hom y z) (h : Hom z w) → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
    isSet-Hom : ∀ {x y} → isSet (Hom x y)

open Category using (Ob; Hom; isSet-Hom) public

module _ {a} {b} (C : Category a b) where

  open Category C using (id; _⋆_; ⋆-identityˡ)

  record Iso (x y : C .Ob) : Type b where
    field
      fun : C .Hom x y
      inv : C .Hom y x
      rightInv : fun ⋆ inv ≡ id x
      leftInv : inv ⋆ fun ≡ id y

  idIso : ∀ x → Iso x x
  idIso x =
    record
    { fun = id x
    ; inv = id x
    ; rightInv = ⋆-identityˡ (id x)
    ; leftInv = ⋆-identityˡ (id x)
    }

  pathToIso : ∀ {x y} → x ≡ y → Iso x y
  pathToIso {x} {y} p = subst (λ y → Iso x y) p (idIso x)

  pathToIso-refl : ∀ {x} → pathToIso refl ≡ idIso x
  pathToIso-refl {x} = substRefl {B = λ y → Iso x y} (idIso x)

  isUnivalent : Type (a ⊔ b)
  isUnivalent = ∀ {x y} → isEquiv (pathToIso {x} {y})

open Iso public

record Functor
  {c₀ c₁ d₀ d₁}
  (C : Category c₀ c₁)
  (D : Category d₀ d₁)
  : Type (ℓ-suc (c₀ ⊔ c₁ ⊔ d₀ ⊔ d₁)) where
  open Category C renaming (_⋆_ to _⋆₁_)
  open Category D renaming (_⋆_ to _⋆₂_)
  field
    F₀ : C .Ob → D .Ob
    F₁ : ∀ {x y} → C .Hom x y → D .Hom (F₀ x) (F₀ y)
    F-id : ∀ x → F₁ (C .id x) ≡ D .id (F₀ x)
    F-⋆ : ∀ {x y z} (f : C .Hom x y) (g : C .Hom y z) → F₁ (f ⋆₁ g) ≡ F₁ f ⋆₂ F₁ g

record NatTrans
  {c₀ c₁ d₀ d₁}
  {C : Category c₀ c₁}
  {D : Category d₀ d₁}
  (F G : Functor C D)
  : Type (c₀ ⊔ c₁ ⊔ d₁) where
  open Category D using (_⋆_)
  open Functor F renaming (F₀ to F₀; F₁ to F₁)
  open Functor G renaming (F₀ to G₀; F₁ to G₁)
  field
    fun : ∀ x → D .Hom (F₀ x) (G₀ x)
    natural : ∀ {x y} (f : C .Hom x y) → F₁ f ⋆ fun y ≡ fun x ⋆ G₁ f

open NatTrans public

record NatIso
  {c₀ c₁ d₀ d₁}
  {C : Category c₀ c₁}
  {D : Category d₀ d₁}
  (F G : Functor C D)
  : Type (c₀ ⊔ c₁ ⊔ d₁) where
  open Category D using (id; _⋆_)
  open Functor F renaming (F₀ to F₀; F₁ to F₁)
  open Functor G renaming (F₀ to G₀; F₁ to G₁)
  field
    fun : ∀ x → Hom D (F₀ x) (G₀ x)
    inv : ∀ x → Hom D (G₀ x) (F₀ x)
    rightInv : ∀ x → fun x ⋆ inv x ≡ id (F₀ x)
    leftInv : ∀ x → inv x ⋆ fun x ≡ id (G₀ x)
    natural : ∀ {x y} (f : C .Hom x y) → F₁ f ⋆ fun y ≡ fun x ⋆ G₁ f

open NatIso public
