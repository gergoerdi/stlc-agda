module Names where

open import Data.Nat
open import Data.Fin
open import Data.Vec

Name : Set
Name = ℕ

data RawExpr : Set where
  var : Name → RawExpr
  lam : Name → RawExpr → RawExpr
  _·_ : RawExpr → RawExpr → RawExpr

data Expr (n : ℕ) : Set where
  var : Fin n → Expr n
  lam : Expr (suc n) → Expr n
  _·_ : Expr n → Expr n → Expr n

infixl 20 _·_

Binder : ℕ → Set
Binder = Vec Name

data _⊢_↝_ : ∀ {n} → Binder n → RawExpr → Expr n → Set where
  var-zero : ∀ {n x} → {Γ : Binder n} → (x ∷ Γ) ⊢ var x ↝ var zero
  var-suc : ∀ {n x y k} → {Γ : Binder n} → Γ ⊢ var x ↝ var k → (y ∷ Γ) ⊢ var x ↝ var (suc k)
  lam : ∀ {n x E E′} → {Γ : Binder n} → (x ∷ Γ) ⊢ E ↝ E′ → Γ ⊢ lam x E ↝ lam E′
  _·_ : ∀ {n E E′ F F′} → {Γ : Binder n} → Γ ⊢ E ↝ E′ → Γ ⊢ F ↝ F′ → Γ ⊢ E · F ↝ E′ · F′

appˡ : ∀ {n} {Γ : Binder n} {E E′ F F′} → Γ ⊢ (E · F) ↝ (E′ · F′) → Γ ⊢ E ↝ E′
appˡ (Σ · _) = Σ

appʳ : ∀ {n} {Γ : Binder n} {E E′ F F′} → Γ ⊢ (E · F) ↝ (E′ · F′) → Γ ⊢ F ↝ F′
appʳ (_ · Σ) = Σ

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Data.Sum

name-dec : ∀ {n} → {Γ : Binder n} → {x y : Name} → {E : Expr (suc n)} → (y ∷ Γ) ⊢ var x ↝ E → x ≡ y ⊎ (∃ λ E′ → Γ ⊢ var x ↝ E′)
name-dec var-zero = inj₁ refl
name-dec (var-suc p) = inj₂ (_ , p)

find-name : ∀ {n} → (Γ : Binder n) → (x : Name) → Dec (∃ λ E′ → Γ ⊢ var x ↝ E′)
find-name [] x = no lem
  where
  lem : ¬ ∃ λ E′ → [] ⊢ var x ↝ E′
  lem (_ , ())
find-name (y ∷ Γ) x with x ≟ y
find-name (y ∷ Γ) .y | yes refl = yes (var zero , var-zero)
find-name (y ∷ Γ) x | no x≢y with find-name Γ x
find-name (y ∷ Γ) x | no x≢y | yes (var k , Σ) = yes (var (suc k) , var-suc Σ)
find-name (y ∷ Γ) x | no x≢y | yes (lam _ , ())
find-name (y ∷ Γ) x | no x≢y | yes (_ · _ , ())
find-name (y ∷ Γ) x | no x≢y | no ¬p = no lem
  where
  lem : ¬ ∃ λ E′ → (y ∷ Γ) ⊢ var x ↝ E′
  lem (E′ , Σ) with name-dec Σ
  lem (E′ , Σ) | inj₁ x≡y = x≢y x≡y
  lem (E′ , Σ) | inj₂ p = ¬p p

check : ∀ {n} → (Γ : Binder n) → (E : RawExpr) → Dec (∃ λ E′ → Γ ⊢ E ↝ E′)
check Γ (var x) = find-name Γ x
check Γ (lam x E) with check (x ∷ Γ) E
check Γ (lam x E) | yes (E′ , Σ) = yes (lam E′ , lam Σ)
check Γ (lam x E) | no ¬p = no lem
  where
  lem : ¬ ∃ λ E′ → Γ ⊢ lam x E ↝ E′
  lem (var _ , ())
  lem (_ · _ , ())
  lem (lam E′ , lam Σ) = ¬p (E′ , Σ)
check Γ (E · F) with check Γ E
check Γ (E · F) | yes (E′ , Σ₁) with check Γ F
check Γ (E · F) | yes (E′ , Σ₁) | yes (F′ , Σ₂) = yes (E′ · F′ , Σ₁ · Σ₂)
check Γ (E · F) | yes (E′ , Σ₁) | no ¬p = no lem
  where
  lem : ¬ ∃ λ E′ → Γ ⊢ E · F ↝ E′
  lem (var _ , ())
  lem (lam _ , ())
  lem (E₁ · E₂ , Σ) = ¬p (E₂ , appʳ Σ)
check Γ (E · F) | no ¬p = no lem
  where
  lem : ¬ ∃ λ E′ → Γ ⊢ (E · F) ↝ E′
  lem (var _ , ())
  lem (lam _ , ())
  lem (E₁ · E₂ , Σ) = ¬p (E₁ , appˡ Σ)

open import Relation.Nullary.Decidable

scope : (E : RawExpr) → {p : True (check [] E)} → Expr 0
scope E {p} = proj₁ (toWitness p)

module Example where
  open import Relation.Nullary.Decidable
  open import Function using (_$_)

  ID : Expr 0
  ID = scope $ lam 0 (var 0)

  CONST : Expr 0
  CONST = scope $ lam 0 (lam 42 (var 0))

  -- CONST = scope $ lam "x" (lam "y" (var "x"))
