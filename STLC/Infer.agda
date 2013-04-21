open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module STLC.Infer {U : Set} (UEq : IsDecEquivalence {A = U} _≡_) where

open import STLC.Syntax U
open IsDecEquivalence UEq using (_≟_)

open import Data.Nat hiding (_≟_)
open import Data.Fin
open import Data.Vec
open import Function using (_∘_; _$_)
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

el-inj : ∀ {A B} → el A ≡ el B → A ≡ B
el-inj refl = refl

arr-injˡ : ∀ {τ τ′ τ₂ τ₂′} → τ ↣ τ₂ ≡ τ′ ↣ τ₂′ → τ ≡ τ′
arr-injˡ refl = refl

arr-injʳ : ∀ {τ τ′ τ″} → τ ↣ τ′ ≡ τ ↣ τ″ → τ′ ≡ τ″
arr-injʳ refl = refl

_T≟_ : (τ τ′ : Type) → Dec (τ ≡ τ′)
el A T≟ el B with A ≟ B
el A T≟ el .A | yes refl = yes refl
el A T≟ el B | no A≢B = no (A≢B ∘ el-inj)
el A T≟ (_ ↣ _) = no (λ ())
(τ₁ ↣ τ₂) T≟ el B = no (λ ())
(τ₁ ↣ τ₂) T≟ (τ₁′ ↣ τ₂′) with τ₁ T≟ τ₁′
(τ₁ ↣ τ₂) T≟ (τ₁′ ↣ τ₂′) | no ¬p = no (¬p ∘ arr-injˡ)
(τ₁ ↣ τ₂) T≟ (.τ₁ ↣ τ₂′) | yes refl with τ₂ T≟ τ₂′
(τ₁ ↣ τ₂) T≟ (.τ₁ ↣ .τ₂) | yes refl | yes refl = yes refl
(τ₁ ↣ τ₂) T≟ (.τ₁ ↣ τ₂′) | yes refl | no ¬p = no (¬p ∘ arr-injʳ)

⊢-inj : ∀ {n Γ} {E : Expr n} → ∀ {τ τ′} → Γ ⊢ E ∷ τ → Γ ⊢ E ∷ τ′ → τ ≡ τ′
⊢-inj tVar tVar = refl
⊢-inj {E = lam τ E} (tLam t) (tLam t′) = cong (_↣_ τ) (⊢-inj t t′)
⊢-inj (t₁ · t₂) (t₁′ · t₂′) with ⊢-inj t₁ t₁′
⊢-inj (t₁ · t₂) (t₁′ · t₂′) | refl with ⊢-inj t₂ t₂′
⊢-inj (t₁ · t₂) (t₁′ · t₂′) | refl | refl = refl

lam-injˡ : ∀ {n τ₁ τ₂ τ} {Γ : Ctxt n} {E : Expr (suc n)} →
           Γ ⊢ lam τ E ∷ (τ₁ ↣ τ₂) → τ₁ ≡ τ
lam-injˡ (tLam t) = refl

mutual
  infer : ∀ {n} Γ → (E : Expr n) → Dec (∃ λ τ → Γ ⊢ E ∷ τ)
  infer Γ (var x) = yes (lookup x Γ , tVar)
  infer Γ (lam τ E) with infer (τ ∷ Γ) E
  infer Γ (lam τ E) | yes (τ′ , E∷τ′) = yes (τ ↣ τ′ , tLam E∷τ′)
  infer Γ (lam τ E) | no ¬p = no lem
    where
    lem : ¬ ∃ λ τ′ → (Γ ⊢ lam τ E ∷ τ′)
    lem (el A , ())
    lem (.τ ↣ _ , tLam t) = ¬p (_ , t)
  infer Γ (E · F) with infer Γ E
  infer Γ (E · F) | yes (el A , t) = no lem
    where
    lem : ¬ ∃ λ τ → Γ ⊢ E · F ∷ τ
    lem (_ , t₁ · _) with ⊢-inj t t₁
    lem (_ , t₁ · _) | ()
  infer Γ (E · F) | yes (τ₁ ↣ τ₂ , tE) with check Γ F τ₁
  infer Γ (E · F) | yes (τ₁ ↣ τ₂ , tE) | yes tF = yes (τ₂ , tE · tF)
  infer Γ (E · F) | yes (τ₁ ↣ τ₂ , tE) | no ¬p = no lem
    where
    lem : ¬ ∃ λ τ → (Γ ⊢ E · F ∷ τ)
    lem (_ , t₁ · _) with ⊢-inj t₁ tE
    lem (.τ₂ , _ · t₂) | refl = ¬p t₂
  infer Γ (E · F) | no ¬p = no lem
    where
    lem : ¬ ∃ λ τ → (Γ ⊢ E · F ∷ τ)
    lem (_ , t · _) = ¬p (_ , t)

  check : ∀ {n} Γ → (E : Expr n) → ∀ τ → Dec (Γ ⊢ E ∷ τ)
  check Γ (var x) τ with lookup x Γ T≟ τ
  check Γ (var x) .(lookup x Γ) | yes refl = yes tVar
  check Γ (var x) τ | no ¬p = no (¬p ∘ ⊢-inj tVar)
  check Γ (lam τ′ E) (el A) = no (λ ())
  check Γ (lam τ′ E) (τ₁ ↣ τ₂) with τ₁ T≟ τ′
  check Γ (lam τ′ E) (.τ′ ↣ τ₂) | yes refl with check (τ′ ∷ Γ) E τ₂
  check Γ (lam τ′ E) (.τ′ ↣ τ₂) | yes refl | yes t = yes (tLam t)
  check Γ (lam τ′ E) (.τ′ ↣ τ₂) | yes refl | no ¬p = no lem
    where
    lem : ¬ Γ ⊢ lam τ′ E ∷ τ′ ↣ τ₂
    lem (tLam t) = ¬p t
  check Γ (lam τ′ E) (τ₁ ↣ τ₂) | no ¬p = no (¬p ∘ lam-injˡ)
  check Γ (E · F) τ with infer Γ F
  check Γ (E · F) τ | yes (τ′ , F∷τ′) with check Γ E (τ′ ↣ τ)
  check Γ (E · F) τ | yes (τ′ , F∷τ′) | yes E∷τ′↣τ = yes (E∷τ′↣τ · F∷τ′)
  check Γ (E · F) τ | yes (τ′ , F∷τ′) | no ¬p = no lem
    where
    lem : ¬ Γ ⊢ E · F ∷ τ
    lem (_·_ {τ = τ₀} t t′) with ⊢-inj F∷τ′ t′
    lem (t · t′) | refl = ¬p t
  check Γ (E · F) τ | no ¬tF = no lem
    where
    lem : ¬ Γ ⊢ E · F ∷ τ
    lem (_·_ {τ = τ} t t′) = ¬tF (τ , t′)
