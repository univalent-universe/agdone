{-# OPTIONS --no-import-sorts --without-K #-}
module Foundations.Logic.Disjunction.Properties where

open import Foundations.Logic.Disjunction.Base

open import Foundations.Universes.Base

module _ where
  open import Foundations.Logic.Truth.Base
  module _ {ℓ} {A : Type ℓ} where
    induction-⊎-⊤-right : ∀ {ℓ'} {P : A ⊎ ⊤ → Type ℓ'} →
      ((x : A) → P (left x)) → P (right truth-is-true) → (x : _) → P x
    induction-⊎-⊤-right proof-left proof-right (left x) = proof-left x
    induction-⊎-⊤-right proof-left proof-right (right truth-is-true) =
      proof-right
    induction-⊎-⊤-left : ∀ {ℓ'} {P : ⊤ ⊎ A → Type ℓ'} →
      P (left truth-is-true) → ((x : A) → P (right x)) → (x : _) → P x
    induction-⊎-⊤-left proof-left proof-right (left truth-is-true) =
      proof-left
    induction-⊎-⊤-left proof-left proof-right (right x) = proof-right x

  induction-⊤-⊎-⊤ : ∀ {ℓ'} {P : ⊤ ⊎ ⊤ → Type ℓ'} → P (left truth-is-true)
    → P (right truth-is-true) → (x : _) → P x
  induction-⊤-⊎-⊤ proof-left proof-right (left truth-is-true) = proof-left
  induction-⊤-⊎-⊤ proof-left proof-right (right truth-is-true) = proof-right

 
module _ where
  open import Foundations.Logic.Falsehood.Base
  module _ {ℓ} {A : Type ℓ} where
    induction-⊎-⊥-right : ∀ {ℓ'} {P : A ⊎ ⊥ → Type ℓ'} →
      ((x : A) → P (left x)) → (x : A ⊎ ⊥) → P x
    induction-⊎-⊥-right proof-left (left x) = proof-left x
    induction-⊎-⊥-left : ∀ {ℓ'} {P : ⊥ ⊎ A → Type ℓ'} →
      ((x : A) → P (right x)) → (x : ⊥ ⊎ A) → P x
    induction-⊎-⊥-left proof-right (right x) = proof-right x

  induction-⊥-⊎-⊥ : ∀ {ℓ'} {P : ⊥ ⊎ ⊥ → Type ℓ'} → (x : ⊥ ⊎ ⊥) → P x
  induction-⊥-⊎-⊥ (left ())
  induction-⊥-⊎-⊥ (right ())
