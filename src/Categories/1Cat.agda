module Categories.1Cat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

record Category a b : Type (ℓ-suc (ℓ-max a b)) where
  field
    Ob : Type a
    Hom : Ob → Ob → Type b
    id : ∀ x → Hom x x
    _⋆_ : ∀ {x y z} → Hom x y → Hom y z → Hom x z
    ⋆-identityˡ : ∀ {x y} (f : Hom x y) → id x ⋆ f ≡ f
    ⋆-identityʳ : ∀ {x y} (f : Hom x y) → f ⋆ id y ≡ f
    ⋆-assoc : ∀ {x y z w} (f : Hom x y) (g : Hom y z) (h : Hom z w) → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
    isSet-Hom : ∀ {x y} → isSet (Hom x y)

  _≅_ : Ob → Ob → Type b
  x ≅ y = Σ[ f ∈ Hom x y ] Σ[ g ∈ Hom y x ] (f ⋆ g ≡ id x) × (g ⋆ f ≡ id y)

  ≅-refl : ∀ x → x ≅ x
  ≅-refl x = id x , id x , ⋆-identityˡ (id x) , ⋆-identityˡ (id x)

  pathToIso : ∀ {x y} → x ≡ y → x ≅ y
  pathToIso {x} {y} p = subst (λ y → x ≅ y) p (≅-refl x)

  pathToIso-refl : ∀ {x} → pathToIso refl ≡ (≅-refl x)
  pathToIso-refl {x} = substRefl {B = λ y → x ≅ y} (≅-refl x)

private
  variable
    a b : Level

isUnivalent : Category a b → Type (ℓ-max a b)
isUnivalent C = ∀ {x y} → isEquiv (Category.pathToIso C {x} {y})
