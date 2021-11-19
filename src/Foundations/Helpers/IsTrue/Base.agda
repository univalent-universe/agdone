{-# OPTIONS --no-import-sorts --without-K #-}

module Foundations.Helpers.IsTrue.Base where

open import Foundations.Universes.Base

record is-true {ℓ} (A : Type ℓ) : Type ℓ where
  constructor is-true-by
  field proof-of : A

open is-true public
open is-true ⦃...⦄ public renaming (proof-of to trivially)
