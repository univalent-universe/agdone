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

  inverse-·-sym-left : {a b : A} → (p : a ≡ b) → sym p · p ≡ refl
  inverse-·-sym-left refl = refl

  inverse-·-sym-right : {a b : A} → (p : a ≡ b) → p · sym p ≡ refl
  inverse-·-sym-right refl = refl
  
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
  associative-◼ : {a b c d : A} {p p' : c ≡ d} {q q' : b ≡ c} {r r' : a ≡ b}
    → (α : p ≡ p') → (β : q ≡ q') → (γ : r ≡ r') →
        associative-· p' q' r' · (α ◼ (β ◼ γ))
        · sym (associative-· p q r)  ≡ (α ◼ β) ◼ γ
  associative-◼ {p = refl} {q = refl} {r = refl} refl refl refl = refl

  neutral-◼-refl-left : {a b c : A} {p : b ≡ c} {q q' : a ≡ b}
   (α : q ≡ q') → neutral-·-refl-left q' · (refl {a = refl} ◼ α) ·
     sym (neutral-·-refl-left q) ≡ α
  neutral-◼-refl-left {q = refl} refl = refl

  neutral-◼-refl-right : {a b c : A} {p p' : b ≡ c} {q : a ≡ b}
   (α : p ≡ p') → neutral-·-refl-right p' · (α ◼ refl {a = refl}) ·
     sym (neutral-·-refl-right p) ≡ α
  neutral-◼-refl-right {p = refl} refl = refl

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  apply-eq : (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
  apply-eq f refl = refl

module _ {ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'} where
  subst : {x y : A} → P x → x ≡ y → P y
  subst prf refl = prf

  dep-apply-eq : (f : (a : A) → P a) → {x y : A} → (p : x ≡ y) →
    subst (f x) p ≡ f y
  dep-apply-eq f refl = refl

module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} where
  apply-eq-2 : (f : A → B → C) → {x x' : A} → {y y' : B} → x ≡ x' →
    y ≡ y' → f x y ≡ f x' y'
  apply-eq-2 f refl refl = refl

module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {P : A → Type ℓ'} {C : Type ℓ''} where
  dep-2-apply-eq-2 : (f : (a : A) → P a → C) → {x x' : A} → {y : P x} →
    {y' : P x'} → (p : x ≡ x') → subst y p ≡ y' → f x y ≡ f x' y'
  dep-2-apply-eq-2 f refl refl = refl
