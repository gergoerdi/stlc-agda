module STLC.Scopecheck (Type : Set) where

open import STLC.Syntax Type as S hiding (Expr; module Expr)
open import STLC.Bound Type
open import Data.Nat hiding (_≟_)
open import Data.Fin
open import Data.Vec using ([]; _∷_; lookup; reverse)
open import Data.String
open import Relation.Nullary.Decidable

appˡ : ∀ {n} {Γ : Binder n} {E E′ F F′} → Γ ⊢ (E · F) ↝ (E′ · F′) → Γ ⊢ E ↝ E′
appˡ (δ · _) = δ

appʳ : ∀ {n} {Γ : Binder n} {E E′ F F′} → Γ ⊢ (E · F) ↝ (E′ · F′) → Γ ⊢ F ↝ F′
appʳ (_ · δ) = δ

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum
open import STLC.Utils

name-dec : ∀ {n} {Γ : Binder n} {x y : Name} {E : Expr (suc n)} →
           (y ∷ Γ) ⊢ var x ↝ E →
           x ≡ y ⊎ (∃[ E′ ] Γ ⊢ var x ↝ E′)
name-dec var-zero = inj₁ refl
name-dec (var-suc p) = inj₂ (_ , p)

find-name : ∀ {n} → (Γ : Binder n) → (x : Name) → Dec (∃[ E′ ] Γ ⊢ var x ↝ E′)
find-name [] x = no lem
  where
  lem : ∄[ E′ ] [] ⊢ var x ↝ E′
  lem (_ , ())
find-name (y ∷ Γ) x with x ≟ y
find-name (y ∷ Γ) .y | yes refl = yes (var zero , var-zero)
find-name (y ∷ Γ) x | no x≢y with find-name Γ x
find-name (y ∷ Γ) x | no x≢y | yes (var k , δ) = yes (var (suc k) , var-suc {p = fromWitnessFalse x≢y} δ)
find-name (y ∷ Γ) x | no x≢y | yes (lam _ _ , ())
find-name (y ∷ Γ) x | no x≢y | yes (_ · _ , ())
find-name (y ∷ Γ) x | no x≢y | no ¬p = no lem
  where
  lem : ∄[ E′ ] (y ∷ Γ) ⊢ var x ↝ E′
  lem (E′ , δ) with name-dec δ
  lem (E′ , δ) | inj₁ x≡y = x≢y x≡y
  lem (E′ , δ) | inj₂ p = ¬p p

check : ∀ {n} → (Γ : Binder n) → (E : S.Expr) → Dec (∃[ E′ ] Γ ⊢ E ↝ E′)
check Γ (var x) = find-name Γ x
check Γ (lam (x ∶ τ) E) with check (x ∷ Γ) E
check Γ (lam (x ∶ τ) E) | yes (E′ , δ) = yes (lam _ E′ , lam δ)
check Γ (lam (x ∶ τ) E) | no ¬p = no lem
  where
  lem : ∄[ E′ ] Γ ⊢ lam (x ∶ τ) E ↝ E′
  lem (var _ , ())
  lem (_ · _ , ())
  lem (lam .τ E′ , lam δ) = ¬p (E′ , δ)
check Γ (E · F) with check Γ E
check Γ (E · F) | yes (E′ , δ₁) with check Γ F
check Γ (E · F) | yes (E′ , δ₁) | yes (F′ , δ₂) = yes (E′ · F′ , δ₁ · δ₂)
check Γ (E · F) | yes (E′ , δ₁) | no ¬p = no lem
  where
  lem : ∄[ E′ ] Γ ⊢ E · F ↝ E′
  lem (var _ , ())
  lem (lam _ _ , ())
  lem (E₁ · E₂ , δ) = ¬p (E₂ , appʳ δ)
check Γ (E · F) | no ¬p = no lem
  where
  lem : ∄[ E′ ] Γ ⊢ (E · F) ↝ E′
  lem (var _ , ())
  lem (lam _ _ , ())
  lem (E₁ · E₂ , δ) = ¬p (E₁ , appˡ δ)

-- Go from a representation that uses Names to one that uses de Bruijn indices
scope : (E : S.Expr) → {p : True (check [] E)} → Expr 0
scope E {p} = proj₁ (toWitness p)
