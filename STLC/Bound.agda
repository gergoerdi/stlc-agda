module STLC.Bound (Type : Set) where

open import STLC.Syntax Type as S hiding (Expr; module Expr)

open import Data.Nat hiding (_≟_)
open import Data.Fin
open import Data.Vec
open import Data.String
open import Relation.Nullary.Decidable

data Expr (n : ℕ) : Set where
  var : (k : Fin n) → Expr n
  lam : (τ : Type) → Expr (suc n) → Expr n
  _·_ : Expr n → Expr n → Expr n
infixl 20 _·_

Binder : ℕ → Set
Binder = Vec Name

data _⊢_↝_ : ∀ {n} → Binder n → S.Expr → Expr n → Set where
  var-zero : ∀ {n x} → {Γ : Binder n} → (x ∷ Γ) ⊢ var x ↝ var zero
  var-suc : ∀ {n x y k} → {Γ : Binder n} → {p : False (x ≟ y)} → Γ ⊢ var x ↝ var k → (y ∷ Γ) ⊢ var x ↝ var (suc k)
  lam : ∀ {n x τ E E′} → {Γ : Binder n} → (x ∷ Γ) ⊢ E ↝ E′ → Γ ⊢ (lam (x ∶ τ) E) ↝ (lam τ E′)
  _·_ : ∀ {n E E′ F F′} → {Γ : Binder n} → Γ ⊢ E ↝ E′ → Γ ⊢ F ↝ F′ → Γ ⊢ E · F ↝ E′ · F′
