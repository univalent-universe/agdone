{-# OPTIONS --no-import-sorts --without-K #-}
module Foundations.Logic.Conjunction.Properties where

open import Foundations.Logic.Conjunction.Base

open import Foundations.Universes.Base

module _ where
  open import Foundations.Logic.Truth.Base
  module _ {ℓ} {A : Type ℓ} where
    introduction-×-⊤-right : A → A × ⊤
    introduction-×-⊤-right x = x , truth-is-true

    introduction-×-⊤-left : A → ⊤ × A
    introduction-×-⊤-left x = truth-is-true , x

    induction-×-⊤-right : ∀ {ℓ'} {P : A × ⊤ → Type ℓ'} → ((x : A) → P (x , truth-is-true)) → (x : A × ⊤) → P x
    induction-×-⊤-right proof (first , truth-is-true) = proof first

    induction-×-⊤-left : ∀ {ℓ'} {P : ⊤ × A → Type ℓ'} → ((x : A) → P (truth-is-true , x)) → (x : ⊤ × A) → P x
    induction-×-⊤-left proof (truth-is-true , second) = proof second

  induction-⊤-×-⊤ : ∀ {ℓ'} {P : ⊤ × ⊤ → Type ℓ'} → P (truth-is-true , truth-is-true) → (x : ⊤ × ⊤) → P x
  induction-⊤-×-⊤ prf (truth-is-true , truth-is-true) = prf

module _ where
  open import Foundations.Logic.Falsehood.Base
  module _ {ℓ} {A : Type ℓ} where

    induction-×-⊥-right : ∀ {ℓ'} {P : A × ⊥ → Type ℓ'} → (x : A × ⊥) → P x
    induction-×-⊥-right (left , ())

    induction-×-⊥-left : ∀ {ℓ'} {P : ⊥ × A → Type ℓ'} → (x : ⊥ × A) → P x
    induction-×-⊥-left (() , right)

  induction-⊥-×-⊥ : ∀ {ℓ'} {P : ⊥ × ⊥ → Type ℓ'} → (x : ⊥ × ⊥) → P x
  induction-⊥-×-⊥ (() , ())
