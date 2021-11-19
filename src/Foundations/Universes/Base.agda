{-# OPTIONS --no-import-sorts --without-K #-}

module Foundations.Universes.Base where

open import Agda.Primitive public using ( Level ) renaming
  ( Set to Type ;
    Setω to Typeω )

open import Agda.Primitive using (lsuc; lzero) renaming (_⊔_ to lmax)

module Level where
  suc : Level → Level
  suc = lsuc
  zero : Level
  zero = lzero
  _⊔_ : Level → Level → Level
  _⊔_ = lmax


