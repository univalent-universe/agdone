{-# OPTIONS --no-import-sorts --without-K #-}
module Foundations.Logic.Disjunction.Base where

open import Foundations.Universes.Base

data _⊎_ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ Level.⊔ ℓ') where
  left : A → A ⊎ B
  right : B → A ⊎ B

infixr 30 _⊎_

module _ {ℓ} {A : Type ℓ} where
  codiag-⊎ : A ⊎ A → A
  codiag-⊎ (left x) = x
  codiag-⊎ (right x) = x

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  induction-⊎ : ∀ {ℓ''} {P : A ⊎ B → Type ℓ''} → ((x : A) → P (left x)) →
    ((y : B) → P (right y)) → (x : A ⊎ B) → P x
  induction-⊎ proof-left proof-right (left x) = proof-left x
  induction-⊎ proof-left proof-right (right x) = proof-right x

  recursion-⊎ : ∀ {ℓ''} {C : Type ℓ''} → (A → C) → (B → C) → (x : A ⊎ B) → C
  recursion-⊎ value-left value-right (left x) = value-left x
  recursion-⊎ value-left value-right (right x) = value-right x

  introduction-⊎-left : ∀ {ℓ''} {C : Type ℓ''} → (C → A) → C → A ⊎ B
  introduction-⊎-left f a = left (f a)
  
  introduction-⊎-right : ∀ {ℓ''} {C : Type ℓ''} → (C → B) → C → A ⊎ B
  introduction-⊎-right f a = right (f a)

  map-⊎-left : ∀ {ℓ''} {C : Type ℓ''} → (A → C) → A ⊎ B → C ⊎ B
  map-⊎-left f (left x) = left (f x)
  map-⊎-left f (right x) = right x

  map-⊎-right : ∀ {ℓ''} {C : Type ℓ''} → (B → C) → A ⊎ B → A ⊎ C
  map-⊎-right f (left x) = left x
  map-⊎-right f (right x) = right (f x)

  commutative-⊎ : A ⊎ B → B ⊎ A
  commutative-⊎ (left x) = right x
  commutative-⊎ (right x) = left x

  bimap-⊎ : ∀ {ℓ'' ℓ'''} {C : Type ℓ''} {D : Type ℓ'''} → (A → C) → (B → D) →
    A ⊎ B → C ⊎ D
  bimap-⊎ f g (left x) = left (f x)
  bimap-⊎ f g (right x) = right (g x)

  extract-map-out-of-⊎-left : ∀ {ℓ''} {C : Type ℓ''} → (A ⊎ B → C) → A → C
  extract-map-out-of-⊎-left f x = f (left x)

  extract-map-out-of-⊎-right : ∀ {ℓ''} {C : Type ℓ''} → (A ⊎ B → C) → B → C
  extract-map-out-of-⊎-right f x = f (right x)
  
module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} where
  assoc-right-to-left-⊎ : A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
  assoc-right-to-left-⊎ (left x) = left (left x)
  assoc-right-to-left-⊎ (right (left x)) = left (right x)
  assoc-right-to-left-⊎ (right (right x)) = right x

  assoc-left-to-right-⊎ : (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
  assoc-left-to-right-⊎ (left (left x)) = left x
  assoc-left-to-right-⊎ (left (right x)) = right (left x)
  assoc-left-to-right-⊎ (right x) = right (right x)
