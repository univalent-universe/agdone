
{-# OPTIONS --no-import-sorts --without-K #-}
module Foundations.Logic.Negation.Base where

open import Foundations.Logic.Falsehood.Base
open import Foundations.Universes.Base

record ¬_ {ℓ} (A : Type ℓ) : Type ℓ where
  constructor is-absurd
  field
    implies-falsehood : A → ⊥

  implies-anything : ∀ {ℓ'} {B : Type ℓ'} → A → B
  implies-anything x with implies-falsehood x
  ... | ()

infix 40 ¬_ 

module _ {ℓ} {A : Type ℓ} where
  double-¬ : A → ¬ ¬ A
  double-¬ x = is-absurd (λ z → ¬_.implies-falsehood z x)

  ¬-self-implies-anything : ∀ {ℓ'} {B : Type ℓ'} → A → ¬ A → B
  ¬-self-implies-anything x y = ¬_.implies-anything (is-absurd (λ z → z))
                                  (¬_.implies-falsehood y x)
    where open ¬_ y

  triple-¬-to-¬ : ¬ ¬ ¬ A → ¬ A
  triple-¬-to-¬ x = is-absurd
                      (λ z →
                         ¬_.implies-falsehood x
                         (is-absurd (λ z₁ → ¬_.implies-falsehood z₁ z)))

  ¬-to-triple-¬ : ¬ A → ¬ ¬ ¬ A
  ¬-to-triple-¬ x = is-absurd
                      (λ z → ¬_.implies-falsehood z
                      (is-absurd (¬_.implies-falsehood x)))

  
module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  to-self-and-neg-to-neg : (A → B) → (A → ¬ B) → ¬ A
  to-self-and-neg-to-neg f g =
    is-absurd (λ z → ¬_.implies-falsehood (g z) (f z))
  
