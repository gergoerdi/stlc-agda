module STLC.Example where

open import Data.Nat
open import Relation.Binary
open import Function using (_$_)
open import Data.Fin
open import Data.Fin.Props
open import Data.Bool
module Fin-DecSetoid = DecSetoid (Data.Fin.Props.decSetoid 2)

El : Fin 2 → Set
El zero = ℕ
El (suc zero) = Bool
El (suc (suc ()))

open import STLC.Syntax (Fin 2)
open import STLC.Semantics Fin-DecSetoid.isDecEquivalence El

N B : Type
N = el zero
B = el (suc zero)

ID : ℕ → ℕ
ID = eval $ lam N $ var zero

CONST : ℕ → Bool → ℕ
CONST = eval $ lam N $ lam B $ var (suc zero)
