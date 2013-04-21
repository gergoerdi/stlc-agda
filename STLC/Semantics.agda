open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module STLC.Semantics {U : Set} (UEq : IsDecEquivalence {A = U} _≡_) (Prim : U → Set) where

open import STLC.Syntax U
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.Product
open import Data.Unit

El : Type → Set
El (el A) = Prim A
El (τ ↣ τ′) = El τ → El τ′

private
  data TExpr {n : ℕ} : Ctxt n → Type → Set where
    var : (x : Fin n) → {Γ : Ctxt n} → TExpr Γ (lookup x Γ)
    lam : (τ : Type) → ∀ {Γ τ′} → TExpr (τ ∷ Γ) τ′ → TExpr Γ (τ ↣ τ′)
    _·_ : ∀ {Γ τ τ′} → (E : TExpr Γ (τ ↣ τ′)) → (F : TExpr Γ τ) → TExpr Γ τ′

  ctxt : ∀ {n} → Ctxt n → Set
  ctxt [] = ⊤
  ctxt (τ ∷ Γ) = El τ × ctxt Γ

  eval₀ : ∀ {n} → {Γ : Ctxt n} → (γ : ctxt Γ) → ∀ {τ} → TExpr Γ τ → El τ
  eval₀ {Γ = []} γ (var ())
  eval₀ {Γ = τ ∷ Γ} (x , γ) (var zero) = x
  eval₀ {Γ = τ ∷ Γ} (x , γ) (var (suc k)) = eval₀ γ (var k)
  eval₀ γ (lam τ E) = λ x → eval₀ (x , γ) E
  eval₀ γ (E · F) = (eval₀ γ E) (eval₀ γ F)

  semantics : ∀ {n} → {E : Expr n} → {Γ : Ctxt n} → {τ : Type} → (Γ ⊢ E ∷ τ ) → TExpr Γ τ
  semantics {E = var x} tVar = var x
  semantics {E = lam τ _} (tLam t) = lam τ (semantics t)
  semantics (t₁ · t₂) = semantics t₁ · semantics t₂

open import STLC.Infer UEq
open import Relation.Nullary.Decidable

eval : ∀ (E : Expr 0) → {p : True (infer [] E)} → El (proj₁ (toWitness p))
eval E {p} = eval₀ tt (semantics (proj₂ (toWitness p)))
