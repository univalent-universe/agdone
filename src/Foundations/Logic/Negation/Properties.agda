{-# OPTIONS --no-import-sorts --without-K #-}

module Foundations.Logic.Negation.Properties where

open import Foundations.Universes.Base
open import Foundations.Logic.Negation.Base

module _ {ℓ} {A : Type ℓ} where
  open import Foundations.Universes.Lift.Base
  open import Foundations.Logic.Falsehood.Base
  to-all-to-¬ : ∀ {ℓ'} → ((B : Type ℓ') → A → B) → ¬ A
  to-all-to-¬ {ℓ'} f = is-absurd (λ x → extract-value (f (Lift-to ⊥ ℓ') x))
    where open Lift-to

module _ where
  open import Foundations.Logic.Truth.Base
  open import Foundations.Logic.Falsehood.Base
  ¬¬⊤ : ¬ ¬ ⊤
  ¬¬⊤ = double-¬ truth-is-true
  ¬⊥ : ¬ ⊥
  ¬⊥ = is-absurd (λ z → z)
  
module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  open import Foundations.Logic.Disjunction.Base
  open import Foundations.Logic.Conjunction.Base
  contrapose : (A → B) → ¬ B → ¬ A
  contrapose f x = is-absurd (λ z → ¬_.implies-falsehood x (f z))
  
  ¬--⊎-to-¬-left : ¬ (A ⊎ B) → ¬ A
  ¬--⊎-to-¬-left a = is-absurd (λ z → ¬_.implies-falsehood a (left z))

  ¬--⊎-to-¬-right : ¬ (A ⊎ B) → ¬ B
  ¬--⊎-to-¬-right a = is-absurd (λ z → ¬_.implies-falsehood a (right z))

  ¬--⊎-to-×-¬ : ¬ (A ⊎ B) → ¬ A × ¬ B
  ¬--⊎-to-×-¬ a = is-absurd (λ z → ¬_.implies-falsehood a (left z)) ,
                    is-absurd (λ z → ¬_.implies-falsehood a (right z))

  ¬-→-to-¬ : ¬ (A → B) → ¬ B
  ¬-→-to-¬ a = is-absurd (λ z → ¬_.implies-falsehood a (λ x → z))


