module STLC.Syntax (U : Set) where

open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Function using (_∘_)

data Type : Set where
  el : (A : U) → Type
  _↣_ : Type → Type → Type

infixr 20 _↣_

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data Expr (n : ℕ) : Set where
  var : (x : Fin n) → Expr n
  lam : (τ : Type) → Expr (suc n) → Expr n
  _·_ : Expr n → Expr n → Expr n

infixl 20 _·_

Ctxt : ℕ → Set
Ctxt = Vec Type

data _⊢_∷_ : ∀ {n} → Ctxt n → Expr n → Type → Set where
  tVar : ∀ {n Γ} {x : Fin n} → Γ ⊢ var x ∷ lookup x Γ
  tLam : ∀ {n} {Γ : Ctxt n} {τ E τ′} → ((τ ∷ Γ) ⊢ E ∷ τ′) → (Γ ⊢ lam τ E ∷ τ ↣ τ′)
  _·_ : ∀ {n} {Γ : Ctxt n} {E τ τ′} {F} → (Γ ⊢ E ∷ τ ↣ τ′) → (Γ ⊢ F ∷ τ) → (Γ ⊢ E · F ∷ τ′)
