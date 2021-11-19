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
