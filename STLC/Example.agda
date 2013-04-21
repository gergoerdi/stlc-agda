module STLC.Example where

open import Data.Nat
open import Relation.Binary
open import Function using (_$_)
module ℕ-DTO = DecTotalOrder Data.Nat.decTotalOrder

open import STLC.Syntax ℕ

open import Data.Fin
open import STLC.Semantics ℕ-DTO.Eq.isDecEquivalence Fin

A B C : Type
A = el 0
B = el 1
C = el 2

ID : Fin 0 → Fin 0
ID = eval $ lam A $ var zero

CONST : Fin 0 → Fin 1 → Fin 0
CONST = eval $ lam A $ lam B $ var (suc zero)
