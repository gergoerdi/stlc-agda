module STLC.README where

-- Come on, everyone can embed STLC into Agda!
import STLC.Embedded

-- But isn't that cheating? What if Agda's type system wasn't a
-- straightforward extension of the STLC type system?

-- Let's take the long way instead!

-- Raw syntax: references are Names
import STLC.Syntax

-- Bound variable syntax: references are de Bruijn indices
import STLC.Bound

-- We can go between the two via scope checking
import STLC.Scopecheck

-- Define the type system...
import STLC.Typing

-- ... which is decidable
import STLC.Typecheck

-- ... and enables us to embed a type-checked lambda expression into Agda
import STLC.Embed

-- So what does this all give us?
import STLC.Examples
