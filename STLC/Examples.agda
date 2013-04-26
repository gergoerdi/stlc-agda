module STLC.Examples where

open import Data.Fin
open import Function using (_$_)

-- Our base types -- these could be anything. We don't really care here.
postulate A B : Set

module Embedded where
  open import STLC.Embedded

  ID : A → A
  ID = eval₀ $ lam $ var zero

  CONST : A → B → A
  CONST = eval₀ $ lam $ lam $ var (suc zero)

-- But let's do it without the shortcut. Our universe of base types is very simple:
U : Set
U = Fin 2

open import Data.Vec

El : U → Set
El k = lookup k (A ∷ B ∷ [])

-- it even has a decidable equality!
open import Relation.Binary
open import Relation.Binary.Core

isDecEquivalence : IsDecEquivalence {A = U} _≡_
isDecEquivalence = DecSetoid.isDecEquivalence (decSetoid _)
  where
  open import Data.Fin.Props

open import STLC.Typing using (Type; el)

⟪A⟫ ⟪B⟫ : Type U
⟪A⟫ = el (# 0)
⟪B⟫ = el (# 1)

open import STLC.Syntax (Type U)
module Raw where
  ID CONST : Expr -- Look ma, no types!
  ID = lam ("x" ∶ ⟪A⟫) $ var "x"
  CONST = lam ("x" ∶ ⟪A⟫) $ lam ("y" ∶ ⟪B⟫) $ var "x"

module Embed where
  open import Relation.Binary
  open import STLC.Semantics {U} isDecEquivalence El

  ID : A → A
  ID = semantics Raw.ID

  CONST : A → B → A
  CONST = semantics Raw.CONST

-- module StepByStep where
--   open STLC.Bound (Type U)
--   open STLC.Scopecheck (Type U)

--   module Scoping where
--     ID = scope Raw.ID
--     CONST = scope Raw.CONST

--   open import Data.Vec
--   open import Relation.Binary
--   open import Data.Fin.Props

--   open STLC.Typecheck {U} (DecSetoid.isDecEquivalence (decSetoid _))

--   module Typing where
--     ID-type = infer [] Scoping.ID
--     CONST-type = infer [] Scoping.CONST

--   open STLC.Embed {U} (\u → lookup u (A ∷ B ∷ C ∷ []))
--   open STLC.Embedded
--   open import Relation.Nullary.Decidable
--   open import Data.Product

--   module Embed where
--     ID : _
--     ID = eval₀ $ embed $ proj₂ (from-yes Typing.ID-type)

--     CONST : _
--     CONST = eval₀ $ embed $ proj₂ (from-yes Typing.CONST-type)

--   module Roundtrip where
--     open import Relation.Binary.PropositionalEquality

--     ID-eq : Embed.ID ≡ Embedded.ID
--     ID-eq = refl

--     CONST-eq : Embed.CONST ≡ Embedded.CONST
--     CONST-eq = refl
