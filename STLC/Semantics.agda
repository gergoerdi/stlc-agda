open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary.Decidable

module STLC.Semantics {U} (UEq : IsDecEquivalence {A = U} _≡_) (El : U → Set) where

open import STLC.Typing U
open import STLC.Syntax Type as Raw
open import STLC.Scopecheck Type as Scope
open import STLC.Typecheck UEq as TC
open import STLC.Embed El
open import STLC.Embedded

open import Data.Vec
open import Data.Product

semantics : (E : Raw.Expr) →
            {scope-prf : True (Scope.check [] E)} → let E′ = proj₁ (toWitness scope-prf) in
            {type-prf : True (TC.infer [] E′)} → let τ = proj₁ (toWitness type-prf) in
            embed-type τ
semantics E {scope-prf} {type-prf} = eval₀ (embed (proj₂ (toWitness type-prf)))
