{-# OPTIONS --no-import-sorts --without-K #-}

module Foundations.Logic.Implication.Base where

open import Foundations.Universes.Base
module _ {ℓ} {A : Type ℓ} where
  identity : A → A
  identity = λ z → z

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  →-recursion : (A → B) → A → B
  →-recursion = λ z → z

  ignore-second : A → B → A
  ignore-second = λ z _ → z

  ignore-first : A → B → B
  ignore-first = λ _ z → z

  apply-flipped : A → (A → B) → B
  apply-flipped = λ z z₁ → z₁ z

  apply-duplicate : (A → A → B) → A → B
  apply-duplicate = λ z z₁ → z z₁ z₁

module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} where
  apply-ignore-second : (A → C) → A → B → C
  apply-ignore-second = λ z z₁ _ → z z₁

  ignore-second-third : A → B → C → A
  ignore-second-third = λ z _ _ → z

  compose-flipped : (A → B) → (B → C) → A → C
  compose-flipped = λ z z₁ z₂ → z₁ (z z₂)

  compose : (B → C) → (A → B) → A → C
  compose = λ z z₁ z₂ → z (z₁ z₂)

  map-→ : (A → C) → (B → A) → (B → C)
  map-→ = λ z z₁ z₂ → z (z₁ z₂)

  comap-→ : (C → A) → (A → B) → (C → B)
  comap-→ = λ z z₁ z₂ → z₁ (z z₂)

  flip : (A → B → C) → (B → A → C)
  flip = λ z z₁ z₂ → z z₂ z₁

  compose-use : (A → B) → (A → B → C) → A → C
  compose-use = λ z z₁ z₂ → z₁ z₂ (z z₂)

  compose-[use-flipped] : (A → B) → (B → A → C) → A → C
  compose-[use-flipped] = λ z z₁ z₂ → z₁ (z z₂) z₂


module _ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''} where
  compose-3 : (C → D) → (B → C) → (A → B) → (A → D)
  compose-3 = λ z z₁ z₂ z₃ → z (z₁ (z₂ z₃))

  promap-→ : (D → A) → (B → C) → (A → B) → (D → C)
  promap-→ f g a = λ z → g (a (f z))
