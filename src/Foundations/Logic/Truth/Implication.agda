{-# OPTIONS --no-import-sorts --without-K #-}

module Foundations.Logic.Truth.Implication where

open import Foundations.Universes.Base
open import Foundations.Logic.Implication.Base
open import Foundations.Logic.Truth.Base

module _ {ℓ} {A : Type ℓ} where
  apply-at-truth-is-true : (⊤ → A) → A
  apply-at-truth-is-true = λ z → z truth-is-true
