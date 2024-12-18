module Categories.1Cat where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

import Cubical.Data.Sigma as Σ

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

  record _≅_ (x y : Ob) : Type b where
    field
      fwd : Hom x y
      bwd : Hom y x
      fwd-bwd : fwd ⋆ bwd ≡ id x
      bwd-fwd : bwd ⋆ fwd ≡ id y

  ≅-refl : ∀ x → x ≅ x
  ≅-refl x = record
    { fwd = id x
    ; bwd = id x
    ; fwd-bwd = ⋆-identityˡ (id x)
    ; bwd-fwd = ⋆-identityˡ (id x)
    }

  pathToIso : ∀ {x y} → x ≡ y → x ≅ y
  pathToIso {x} {y} p = subst (λ y → x ≅ y) p (≅-refl x)

  pathToIso-refl : ∀ {x} → pathToIso refl ≡ (≅-refl x)
  pathToIso-refl {x} = substRefl {B = λ y → x ≅ y} (≅-refl x)

open Category public
open _≅_ public

isUnivalent : ∀ {a b} → Category a b → Type (a ⊔ b)
isUnivalent C = ∀ {x y} → isEquiv (pathToIso C {x} {y})

_×_ : ∀ {a b c d} → Category a b → Category c d → Category (a ⊔ c) (b ⊔ d)
C × D =
  record
  { Ob = C .Ob Σ.× D .Ob
  ; Hom = λ (c , d) (c′ , d′) → C .Hom c c′ Σ.× D .Hom d d′
  ; id = λ (c , d) → id₁ c , id₂ d
  ; _⋆_ = λ (f , g) (f′ , g′) → f ⋆₁ f′ , g ⋆₂ g′
  ; ⋆-identityˡ = λ (f , g) → cong₂ _,_ (C .⋆-identityˡ f) (D .⋆-identityˡ g)
  ; ⋆-identityʳ = λ (f , g) → cong₂ _,_ (C .⋆-identityʳ f) (D .⋆-identityʳ g)
  ; ⋆-assoc = λ (f₁ , f₂) (g₁ , g₂) (h₁ , h₂) → cong₂ _,_ (C .⋆-assoc f₁ g₁ h₁) (D .⋆-assoc f₂ g₂ h₂)
  ; isSet-Hom = isSet× (C .isSet-Hom) (D .isSet-Hom)
  }
  where
    open Category C renaming (id to id₁; _⋆_ to _⋆₁_)
    open Category D renaming (id to id₂; _⋆_ to _⋆₂_)

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
    F-id : ∀ {x} → F₁ (C .id x) ≡ D .id (F₀ x)
    F-⋆ : ∀ {x y z} (f : C .Hom x y) (g : C .Hom y z) → F₁ (f ⋆₁ g) ≡ F₁ f ⋆₂ F₁ g

open Functor public

Id : ∀ {a b} (C : Category a b) → Functor C C
Id C = record
  { F₀ = λ x → x
  ; F₁ = λ f → f
  ; F-id = λ {x} → refl
  ; F-⋆ = λ f g → refl
  }

record NatTrans
  {c₀ c₁ d₀ d₁}
  {C : Category c₀ c₁}
  {D : Category d₀ d₁}
  (F G : Functor C D)
  : Type (c₀ ⊔ c₁ ⊔ d₁) where
  open Category C renaming (_⋆_ to _⋆₁_)
  open Category D renaming (_⋆_ to _⋆₂_)
  field
    mor : ∀ x → D .Hom (F .F₀ x) (G .F₀ x)
    natural : ∀ {x y} (f : C .Hom x y) → F .F₁ f ⋆₂ mor y ≡ mor x ⋆₂ G .F₁ f

record NatIso
  {c₀ c₁ d₀ d₁}
  {C : Category c₀ c₁}
  {D : Category d₀ d₁}
  (F G : Functor C D)
  : Type (c₀ ⊔ c₁ ⊔ d₁) where
  open Category C renaming (_⋆_ to _⋆₁_)
  open Category D renaming (_⋆_ to _⋆₂_; _≅_ to _≅₂_)
  field
    mor : ∀ x → F .F₀ x ≅₂ G .F₀ x
    natural : ∀ {x y} (f : C .Hom x y) → F .F₁ f ⋆₂ mor y .fwd ≡ mor x .fwd ⋆₂ G .F₁ f
