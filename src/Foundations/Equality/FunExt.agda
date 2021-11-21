{-# OPTIONS --no-import-sorts --without-K #-}

module Foundations.Equality.FunExt where

open import Foundations.Universes.Base
open import Foundations.Equality.Base

record FunExt : Typeω where
  field
    dep-extensionality : ∀ {ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'}
      (f g : (a : A) → P a) → ((x : A) → f x ≡ g x) → f ≡ g
  extensionality : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f g : A → B) →
    ((x : A) → f x ≡ g x) → f ≡ g
  extensionality f g prf = dep-extensionality f g prf
