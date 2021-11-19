{-# OPTIONS --no-import-sorts --without-K #-}

module Foundations.Logic.Truth.Base where

open import Agda.Builtin.Unit public renaming (tt to truth-is-true)

open import Foundations.Universes.Base

induction-⊤ : ∀{ℓ} → {P : ⊤ → Type ℓ} → P truth-is-true → (x : ⊤) → P x
induction-⊤ proof truth-is-true = proof

recursion-⊤ : ∀{ℓ} → {A : Type ℓ} → A → ⊤ → A
recursion-⊤ value-at-truth-is-true truth-is-true = value-at-truth-is-true

introduction-⊤ : ⊤
introduction-⊤ = truth-is-true

module _ {ℓ} {A : Type ℓ} where
  apply-at-truth-is-true : (⊤ → A) → A
  apply-at-truth-is-true = λ z → z truth-is-true
