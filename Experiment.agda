module Experiment where

open import Study

-- First task would be writing a term in the meta-syntax

-- Let's begin with the S combinator, because I can be guided by the types.
-- Being a Tm, this is what I would call the de Bruijn version.

tyS2 : (A B C : Ty) → Tm LTyD ((A >> B >> C) >> (A >> B) >> (A >> C)) B0
-- This means that I'm defining a Tm, using the description function for typed
-- terms, and then I also have to give a term which is used in my interpretation
-- function, and then I have to give the context I intend this term to be
-- indexed with (in this case B0 as this is a closed combinator).

-- Let's recall that S = λx. λy. λz. xz(yz)

-- So the first thing I want to construct is a lambda application, which is part
-- of the syntax I intend. So I have to use the [_] operator
tyS2 A B C = [ lam , [ lam ,  [ lam ,  [ app , _ , [ app , _ , oz os o' o' #$ <>
                                                             , oz o' o' os #$ <> ]
                                                 , [ app , _ , oz o' os o' #$ <>
                                                             , oz o' o' os #$ <> ] ] ] ] ]
