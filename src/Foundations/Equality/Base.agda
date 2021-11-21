{-# OPTIONS --no-import-sorts --without-K #-}

module Foundations.Equality.Base where

open import Foundations.Universes.Base

data _≡_ {ℓ} {A : Type ℓ} (a : A) : A → Type ℓ where
  instance refl : a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

infix 60 _≡_
reflexive-≡ : ∀ {ℓ} {A : Type ℓ} {a : A} → a ≡ a
reflexive-≡ = refl

module _ {ℓ} {A : Type ℓ} where
  symmetric-≡ sym : ∀ {a b : A} → a ≡ b → b ≡ a
  symmetric-≡ refl = refl
  sym = symmetric-≡
  
  transitive-≡ _·_ : ∀ {a b c : A} → b ≡ c → a ≡ b → a ≡ c
  transitive-≡ refl refl = refl
  _·_ = transitive-≡
  
  infixr 80 _·_
  
  involutive-sym : ∀ {a b : A} → (p : a ≡ b) →
    sym (sym p) ≡ p
  involutive-sym refl = refl

  neutral-inv-sym-refl : (a : A) → sym (refl {a = a}) ≡ refl
  neutral-inv-sym-refl a = refl

  neutral-·-refl-left : {a b : A} → (p : a ≡ b) → refl · p ≡ p
  neutral-·-refl-left refl = refl

  neutral-·-refl-right : {a b : A} → (p : a ≡ b) → p · refl ≡ p
  neutral-·-refl-right refl = refl

  associative-· : {a b c d : A} → (p : c ≡ d) → (q : b ≡ c) → (r : a ≡ b) →
    p · (q · r) ≡ (p · q) · r
  associative-· refl refl refl = refl
  
  antihom-·-sym : {a b c : A} → (p : b ≡ c) → (q : a ≡ b) →
    sym (p · q) ≡ sym q · sym p
  antihom-·-sym refl refl = refl

  _◼_ : {a b c : A} {p p' : b ≡ c} {q q' : a ≡ b} → p ≡ p' → q ≡ q' →
    p · q ≡ p' · q'
  refl ◼ refl = refl

  infixr 75 _◼_

module _ {ℓ} {A : Type ℓ} where
  interchange-◼-· : {a b c : A} {q q' q'' : a ≡ b}
                         {p p' p'' : b ≡ c} (α : p' ≡ p'')
                         (α' : p ≡ p') (β : q' ≡ q'') (β' : q ≡ q') →
                         α · α' ◼ (β · β') ≡ (α ◼ β) · (α' ◼ β')
  interchange-◼-· refl refl refl refl = refl
