module STLC.Embed {U : Set} (Prim : U → Set) where

open import STLC.Typing U
open import STLC.Bound Type
open import STLC.Embedded as E hiding (Expr; Ctxt)

open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality

embed-type : Type → Set
embed-type (el A) = Prim A
embed-type (τ₁ ↣ τ₂) = embed-type τ₁ → embed-type τ₂

embed-ctxt : ∀ {n} → Ctxt n → E.Ctxt n
embed-ctxt [] = []
embed-ctxt (τ ∷ Γ) = embed-type τ ∷ embed-ctxt Γ

embed-hom : ∀ {n} x → (Γ : Ctxt n) → lookup x (embed-ctxt Γ) ≡ embed-type (lookup x Γ)
embed-hom () []
embed-hom zero (y ∷ Γ) = refl
embed-hom (suc x) (y ∷ Γ) = embed-hom x Γ

embed : ∀ {n} {E : Expr n} {Γ : Ctxt n} {τ : Type} → Γ ⊢ E ∶ τ → E.Expr (embed-ctxt Γ) (embed-type τ)
embed {E = var x} {Γ} tVar = subst (E.Expr _) (embed-hom x Γ) (var x)
embed {E = lam τ _} (tLam t) = lam {A = embed-type τ} (embed t)
embed (t₁ · t₂) = embed t₁ · embed t₂
