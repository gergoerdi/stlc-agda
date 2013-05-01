module STLC.Syntax (Type : Set) where

open import Data.String

Name : Set
Name = String

data Formal : Set where
  _∶_ : Name → Type → Formal

data Expr : Set where
  var : Name → Expr
  lam : Formal → Expr → Expr
  _·_ : Expr → Expr → Expr
infixl 20 _·_
