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

module _ where
  open import Foundations.Logic.Disjunction.Base
  module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} where
    distributive-left-sum-to-product-×-⊎ : (A × B) ⊎ (A × C) → A × (B ⊎ C)
    distributive-left-sum-to-product-×-⊎ (left (first , second)) =
      first , left second
    distributive-left-sum-to-product-×-⊎ (right (first , second)) =
      first , right second
    distributive-right-sum-to-product-×-⊎ : (B × A) ⊎ (C × A) → (B ⊎ C) × A
    distributive-right-sum-to-product-×-⊎ (left (first , second)) =
      left first , second
    distributive-right-sum-to-product-×-⊎ (right (first , second)) =
      right first , second
    distributive-left-product-to-sum-×-⊎ : A × (B ⊎ C) → (A × B) ⊎ (A × C)
    distributive-left-product-to-sum-×-⊎ (first , left x) = left (first , x)
    distributive-left-product-to-sum-×-⊎ (first , right x) =
      right (first , x)
    distributive-right-product-to-sum-×-⊎ : (B ⊎ C) × A → (B × A) ⊎ (C × A)
    distributive-right-product-to-sum-×-⊎ (left x , second) =
      left (x , second)
    distributive-right-product-to-sum-×-⊎ (right x , second) =
      right (x , second)
    
