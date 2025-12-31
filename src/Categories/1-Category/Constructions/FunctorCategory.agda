module Categories.1-Category.Constructions.FunctorCategory where

open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)
open import Categories.1-Category.Core

module _
  {a b c d}
  {C : Category a b}
  {D : Category c d}
  where

  id : ∀ (F : Functor C D) → NatTrans F F
  id F =
    record
    { fun = λ x → D.id (F.₀ x)
    ; natural = λ f → D.∘-identityˡ (F.₁ f) ∙ sym (D.∘-identityʳ (F.₁ f))
    }
    where
      module D = Category D
      module F = FunctorNotation F

  _∘_ : ∀ {F G H : Functor C D} → NatTrans G H → NatTrans F G → NatTrans F H
  _∘_ {F = F} {G = G} {H = H} α β =
    record
    { fun = λ x → α .fun x D.∘ β .fun x
    ; natural = λ {x} {y} f →
        D.∘-assoc (F.₁ f) (β .fun y) (α .fun y) ∙
        cong (α .fun y D.∘_) (β .natural f) ∙
        sym (D.∘-assoc (β .fun x) (G.₁ f) (α .fun y)) ∙
        cong (D._∘ β .fun x) (α .natural f) ∙
        D.∘-assoc (β .fun x) (α .fun x) (H.₁ f)
    }
    where
      module D = Category D
      module F = FunctorNotation F
      module G = FunctorNotation G
      module H = FunctorNotation H

  ∘-identityˡ : ∀ {F G : Functor C D} (α : NatTrans F G) → id G ∘ α ≡ α
  ∘-identityˡ {F = F} {G = G} α = NatTrans≡.isInjective-fun F G (id G ∘ α) α (funExt λ x → D.∘-identityˡ (α .fun x))
    where
      module D = Category D

  ∘-identityʳ : ∀ {F G : Functor C D} (α : NatTrans F G) → α ∘ id F ≡ α
  ∘-identityʳ {F = F} {G = G} α = NatTrans≡.isInjective-fun F G (α ∘ id F) α (funExt λ x → D.∘-identityʳ (α .fun x))
    where
      module D = Category D

  ∘-assoc : ∀ {F G H K : Functor C D} (α : NatTrans F G) (β : NatTrans G H) (γ : NatTrans H K) → (γ ∘ β) ∘ α ≡ γ ∘ (β ∘ α)
  ∘-assoc {F = F} {K = K} α β γ = NatTrans≡.isInjective-fun F K ((γ ∘ β) ∘ α) (γ ∘ (β ∘ α)) (funExt λ x → D.∘-assoc (α .fun x) (β .fun x) (γ .fun x))
    where
      module D = Category D

[_,_] : ∀ {c₀ c₁ d₀ d₁} → Category c₀ c₁ → Category d₀ d₁ → Category (ℓ-suc (c₀ ⊔ c₁ ⊔ d₀ ⊔ d₁)) (c₀ ⊔ c₁ ⊔ d₁)
[ C , D ] =
  record
  { Ob = Functor C D
  ; Hom = NatTrans
  ; id = id
  ; _∘_ = _∘_
  ; ∘-identityˡ = ∘-identityˡ
  ; ∘-identityʳ = ∘-identityʳ
  ; ∘-assoc = ∘-assoc
  ; isSet-Hom = λ {F G} → NatTrans≡.isSet-NatTrans F G
  }
