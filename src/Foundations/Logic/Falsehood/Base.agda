{-# OPTIONS --no-import-sorts --without-K #-}

module Foundations.Logic.Falsehood.Base where

open import Foundations.Universes.Base

data ⊥ : Type where

induction-⊥ : ∀{ℓ} → {P : ⊥ → Type ℓ} → (x : ⊥) → P x
induction-⊥ ()

recursion-⊥ : ∀{ℓ} → {A : Type ℓ} → (x : ⊥) → A
recursion-⊥ ()
