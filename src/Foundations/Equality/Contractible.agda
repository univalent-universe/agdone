{-# OPTIONS --no-import-sorts --without-K #-}

module Foundations.Equality.Contractible where

open import Foundations.Universes.Base
open import Foundations.Equality.Base

record Contractible {ℓ} (A : Type ℓ) : Type ℓ where
  constructor contract-around
  field
    point : A
    contracts-to : (x : A) → x ≡ point

{-
open import Foundations.Equality.FunExt
module _ {ℓ} {A : Type ℓ} (funext : FunExt) where
  open FunExt funext

  contractible-pi : Contractible A → 

  contractible-contractible : Contractible A → Contractible (Contractible A)
  contractible-contractible a@(contract-around point contracts-to) =
    contract-around a proof
    where proof : (x : Contractible A) →
            x ≡ contract-around point contracts-to
          proof (contract-around point' contracts-to')
            with contracts-to' point | contracts-to point'
          ... | p | refl = dep-2-apply-eq-2 contract-around refl
            (dep-extensionality contracts-to' contracts-to {!!})
-}
