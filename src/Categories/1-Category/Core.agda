module Categories.1-Category.Core where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

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
    respect-id : ∀ x → F₁ (C .id x) ≡ D .id (F₀ x)
    respect-⋆ : ∀ {x y z} (f : C .Hom x y) (g : C .Hom y z) → F₁ (f ⋆₁ g) ≡ F₁ f ⋆₂ F₁ g

module _
  {c₀ c₁ d₀ d₁}
  {C : Category c₀ c₁}
  {D : Category d₀ d₁}
  (F G : Functor C D)
  where

  open Category D using (_⋆_)
  open Functor F renaming (F₀ to F₀; F₁ to F₁)
  open Functor G renaming (F₀ to G₀; F₁ to G₁)

  isNatural : ∀ (α : ∀ x → D .Hom (F₀ x) (G₀ x)) → Type (c₀ ⊔ c₁ ⊔ d₁)
  isNatural α = ∀ {x y} (f : C .Hom x y) → F₁ f ⋆ α y ≡ α x ⋆ G₁ f

  isProp-isNatural : ∀ α → isProp (isNatural α)
  isProp-isNatural α p q = λ i → λ {x y} (f : C .Hom x y) → D .isSet-Hom _ _ (p f) (q f) i

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
    natural : isNatural F G fun

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
    natural : isNatural F G fun

open NatIso public

module NatTrans≡
  {c₀ c₁ d₀ d₁}
  {C : Category c₀ c₁}
  {D : Category d₀ d₁}
  (F G : Functor C D)
  where

  open Category D using (_⋆_)
  open Functor F renaming (F₀ to F₀; F₁ to F₁)
  open Functor G renaming (F₀ to G₀; F₁ to G₁)

  isInjectiveFun : ∀ (α β : NatTrans F G) → α .fun ≡ β .fun → α ≡ β
  isInjectiveFun α β p i = record
    { fun = p i
    ; natural = isProp→PathP (λ j → isProp-isNatural F G (p j)) (α .natural) (β .natural) i
    }

  isInjectiveFun-refl : ∀ (α : NatTrans F G) → isInjectiveFun α α refl ≡ refl
  isInjectiveFun-refl α i j = record
    { fun = α .fun
    ; natural = isProp→isSet
                  (isProp-isNatural F G (α .fun))
                  (α .natural) (α .natural)
                  (λ k → isInjectiveFun α α refl k .natural) refl
                  i j
    }

  isEmbedding-fun : ∀ (α β : NatTrans F G) → isEquiv (λ (p : α ≡ β) → cong fun p)
  isEmbedding-fun α β .equiv-proof e = center , contract
    where
      center : fiber (λ (p : α ≡ β) → cong fun p) e
      center = isInjectiveFun α β e , refl

      contract : ∀ z → center ≡ z
      contract (p , q) = J (λ e q → (isInjectiveFun α β e , refl) ≡ (p , q))
                           (J (λ β p → (isInjectiveFun α β (cong fun p) , refl) ≡ (p , refl {x = cong fun p}))
                              (λ i → isInjectiveFun-refl α i , refl)
                              p)
                           q

  NatTrans≡Equiv : ∀ (α β : NatTrans F G) → (α ≡ β) ≃ (α .fun ≡ β .fun)
  NatTrans≡Equiv α β = cong fun , isEmbedding-fun α β

  isSet-NatTrans : isSet (NatTrans F G)
  isSet-NatTrans α β = subst isProp (sym (ua (NatTrans≡Equiv α β ∙ₑ LiftEquiv {ℓ' = c₁}))) λ p q →
                         cong lift (isSetΠ (λ x → D .isSet-Hom {F₀ x} {G₀ x}) (α .fun) (β .fun) (p .lower) (q .lower))
