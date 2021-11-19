{-# OPTIONS --no-import-sorts --without-K #-}
module Foundations.Logic.Conjunction.Falsehood where

open import Foundations.Logic.Conjunction.Base
open import Foundations.Logic.Falsehood.Base
open import Foundations.Universes.Base

module _ {ℓ} {A : Type ℓ} where
  induction-×-⊥-right : ∀ {ℓ'} {P : A × ⊥ → Type ℓ'} → (x : A × ⊥) → P x
  induction-×-⊥-right (left , ())

  induction-×-⊥-left : ∀ {ℓ'} {P : ⊥ × A → Type ℓ'} → (x : ⊥ × A) → P x
  induction-×-⊥-left (() , right)

induction-⊥-×-⊥ : ∀ {ℓ'} {P : ⊥ × ⊥ → Type ℓ'} → (x : ⊥ × ⊥) → P x
induction-⊥-×-⊥ (() , ())
