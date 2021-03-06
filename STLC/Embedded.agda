module STLC.Embedded where

open import Data.Nat
open import Data.Vec
open import Data.Fin

Ctxt : ℕ → Set₁
Ctxt = Vec Set

data Expr {n : ℕ} : Ctxt n → Set → Set₁ where
  var : (k : Fin n) → {Γ : Ctxt n} → Expr Γ (lookup k Γ)
  lam : {A : Set} → ∀ {Γ B} → (E : Expr (A ∷ Γ) B) → Expr Γ (A → B)
  _·_ : ∀ {Γ A B} → (F : Expr Γ (A → B)) → (E : Expr Γ A) → Expr Γ B

data Env : {n : ℕ} → Ctxt n → Set₁ where
  [] : Env []
  _∷_ : ∀ {n A} {Γ : Ctxt n} → (x : A) → (γ : Env Γ) → Env (A ∷ Γ)

eval : ∀ {n} {Γ : Ctxt n} (γ : Env Γ) {A : Set} → Expr Γ A → A
eval []      (var ())
eval (x ∷ γ) (var zero)    = x
eval (x ∷ γ) (var (suc k)) = eval γ (var k)
eval γ       (lam E)       = λ x → eval (x ∷ γ) E
eval γ       (E · F)       = (eval γ E) (eval γ F)

eval₀ : ∀ {A : Set} → Expr [] A → A
eval₀ = eval []

private
  open import Function using (_$_)

  ex₁ : ℕ → Fin 42 → ℕ
  ex₁ = eval₀ $ lam $ lam $ var (suc zero)
