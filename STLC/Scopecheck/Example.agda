module STLC.Scopecheck.Example where

open import Data.Unit

Type : Set
Type = ⊤

open import STLC.Syntax Type hiding (Expr)
open import STLC.Bound Type
open import STLC.Scopecheck Type
open import Function using (_$_)

ID : Expr 0
ID = scope $ lam ("x" ∷ _) (var "x")

CONST : Expr 0
CONST = scope $ lam ("x" ∷ _) (lam ("y" ∷ _) (var "x"))

BAD : Expr 0
BAD = scope $ lam ("x" ∷ _) (var "y")
