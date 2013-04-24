module STLC.Utils where

open import Data.Product

∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set _
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ] B

∄-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set _
∄-syntax = ∄

syntax ∄-syntax (λ x → B) = ∄[ x ] B
