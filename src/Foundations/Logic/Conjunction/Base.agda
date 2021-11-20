{-# OPTIONS --no-import-sorts --without-K #-}

module Foundations.Logic.Conjunction.Base where

open import Foundations.Universes.Base

record _×_ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ Level.⊔ ℓ') where
  constructor _,_
  field
    first : A
    second : B

infixr 30 _×_

module _ {ℓ} {A : Type ℓ} where
  diag-× : A → A × A
  diag-× x = x , x

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  induction-× : ∀ {ℓ''} {P : A × B → Type ℓ''} → ((x : A) → (y : B) → P (x , y)) → (x : A × B) → P x
  induction-× proof (first , second) = proof first second

  recursion-× : ∀ {ℓ''} {C : Type ℓ''} → (A → B → C) → A × B → C
  recursion-× value (first , second) = value first second

  hom-adjunct-× : ∀ {ℓ''} {C : Type ℓ''} → (A × B → C) → A → B → C
  hom-adjunct-× f x y = f (x , y)

  introduction-× : ∀ {ℓ''} {C : Type ℓ''} → (C → A) → (C → B) → C → A × B
  introduction-× f g = λ z → f z , g z

  map-×-left : ∀ {ℓ''} {C : Type ℓ''} → (A → C) → A × B → C × B
  map-×-left f (first , second) = f first , second

  map-×-right : ∀ {ℓ''} {C : Type ℓ''} → (B → C) → A × B → A × C
  map-×-right f (first , second) = first , f second

  swap-× : A × B → B × A
  swap-× (first , second) = second , first

  bimap-× : ∀ {ℓ'' ℓ'''} {C : Type ℓ''} {D : Type ℓ'''} → (A → C) → (B → D)
    → A × B → C × D
  bimap-× f g (first , second) = f first , g second

  extract-map-into-×-left : ∀ {ℓ''} {C : Type ℓ''} → (C → A × B) → C → A
  extract-map-into-×-left p z with p z
  ... | first , second = first

  extract-map-into-×-right : ∀ {ℓ''} {C : Type ℓ''} → (C → A × B) → C → B
  extract-map-into-×-right p z with p z
  ... | first , second = second

module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} where
  assoc-right-to-left-× : A × (B × C) → (A × B) × C
  assoc-right-to-left-× (first , (first₁ , second)) = (first , first₁) , second

  assoc-left-to-right-× : (A × B) × C → A × (B × C)
  assoc-left-to-right-× ((first , second₁) , second) = first , (second₁ , second)
