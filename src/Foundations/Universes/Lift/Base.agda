{-# OPTIONS --no-import-sorts --without-K #-}


module Foundations.Universes.Lift.Base where

open import Foundations.Universes.Base

record Lift-to {ℓ : Level} (A : Type ℓ) (ℓ' : Level) :
  Type (ℓ Level.⊔ ℓ') where
  constructor lift
  field extract-value : A
  
