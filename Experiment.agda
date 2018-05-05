module Experiment where

open import Study

-- Preliminary study: combinators in the untyped lambda calculus
-- The K combinator, as a LamTm
kTm : LamTm B0
kTm = lam (lam (var (oz os o')))

-- Now the K combinator, as a LamTmR
-- Why is it LamTmR / B0 and not LamTmR B0?
-- λx. λy. x
kTmR : LamTmR / B0
kTmR = lam (oz os \\ lam (oz o' \\ var only)) ^ oz

-- Let's do the same thing for the s combinator
-- s : (x >> y >> z) >> (x >> y) >> (x >> z)
-- s = λf.λg.λx.f x (g x)
sTm : LamTm B0
sTm = lam (lam (lam ((var (oz os o' o') $ var (oz o' o' os))
                    $(var (oz o' os o') $ var (oz o' o' os)))))

sTmR : LamTmR / B0
sTmR = lam (oz os \\
        lam (oz os \\
         lam (oz os \\
          app (pair (app (pair (var only ^ oz os o')
                               (var only ^ oz o' os)
                               (czz cs' c's)) ^ oz os o' os)
                    (app (pair (var only ^ oz os o')
                               (var only ^ oz o' os)
                               (czz cs' c's)) ^ oz o' os os)
                    (czz cs' c's css))))) ^ oz

-- Let's recall that S = λx. λy. λz. xz(yz)
tySTm : (A B C : Ty) → Tm LTyD ((A >> B >> C) >> (A >> B) >> (A >> C)) B0
tySTm A B C = [ lam , [ lam ,  [ lam ,  [ app , _ , [ app , _ , oz os o' o' #$ <>
                                                             , oz o' o' os #$ <> ]
                                                 , [ app , _ , oz o' os o' #$ <>
                                                             , oz o' o' os #$ <> ] ] ] ] ]

tySTmR : (A B C : Ty) → TmR LTyD ((A >> B >> C) >> (A >> B) >> (A >> C)) B0
tySTmR A B C = [ lam , oz os \\
                [ (lam , oz os \\
                 [ (lam , oz os \\
                  [ (app , B , pair
                   ( ( oz \\ [ (app , A , pair
                    ((oz \\ # (pair (only ^ oz os) (<> ^ oz o') (czz cs'))) ^ oz os o')
                    ((oz \\ # (pair (only ^ oz os) (<> ^ oz o') (czz cs'))) ^ oz o' os)
                    (czz cs' c's)) ]) ^ oz os o' os )
                   ((oz \\ [ (app , A , pair
                    ((oz \\ # (pair (only ^ oz os) (<> ^ oz o') (czz cs'))) ^ oz os o')
                    ((oz \\ # ((pair (only ^ oz os) (<> ^ oz o') (czz cs')))) ^ oz o' os)
                    (czz cs' c's)) ]) ^ oz o' os os)
                   (czz cs' c's css)) ]) ]) ] ]

-- Now a simpler example, λx.(λy.y)x
ex2Tm : (A : Ty) → Tm LTyD (A >> A) B0
ex2Tm A = [ lam , [ app , _ , [ lam , oz o' os #$ <> ] , oz os #$ <> ] ]

-- The same example, written as a TmR
ex2TmR : (A : Ty) → TmR LTyD (A >> A) B0
ex2TmR A = [ lam , oz os \\ [ app , A , pair
            ((oz \\ [ lam , oz os \\ # (pair (only ^ oz os) (<> ^ oz o') (czz cs')) ]) ^ oz o')
            ((oz \\ # (pair (only ^ oz os) (<> ^ oz o') (czz cs'))) ^ oz os)
            (czz c's) ] ]


--------------------------------------------------------------------------------
-- Experiments with substitutions
--------------------------------------------------------------------------------

-- What would be a great term to toy with substitution?
-- We'd like a term with which we can implement a language

-- The same example as before, written with concrete types
ex2TmRConc : TmR LTyD (base >> base) B0
ex2TmRConc = [ lam , oz os \\
              [ app , base , pair
               ((oz \\ [ lam , oz os \\ # (pair (only ^ oz os) (<> ^ oz o') (czz cs')) ]) ^ oz o')
               ((oz \\ # (pair (only ^ oz os) (<> ^ oz o') (czz cs'))) ^ oz os)
               (czz c's) ] ]

-- So what would we need to perform the substitution in this term? To do the
-- application (λy.y)x, we'd actually want to substitute the y in the body with
-- the x. How would this be said in this framework?

s : HSub LTyD (B0 - (B0 => base)) (B0 - (B0 => base)) (B0 - (B0 => base))
s = record
      { pass    = B0
      ; act     = B0 - (B0 => base)
      ; passive = oz o'
      ; active  = oz os
      ; parti   = czz c's
      ; passTrg = oz o'
      ; actBnd  = oz os
      ; images  = B0 - ((oz \\ # (pair (only ^ oz os) (<> ^ oz o') (czz cs'))) ^ oz os)
      }

-- How can I write the whole evaluation process?

-- Something like
-- ev : ∀{a ctx} → TmR LTyD a ctx → TmR LTyD a ctx
-- ev (# x) = # x
-- ev [ app , tgtType , pair ((x \\ # x₁) ^ thinning) t2 cover ]   =
--    [ app , tgtType , pair ((x \\ # x₁) ^ thinning) ({!ev t2!} ^ _) cover ]
-- ev [ app , tgtType , pair ((x \\ [ x₁ ]) ^ thinning) t2 cover ] = {!!}
-- ev [ lam , snd ] = {!!}


-- ev : ∀{a ctx} → TmR LTyD a / ctx → TmR LTyD a / ctx
-- ev (# x ^ thinning) = # x ^ thinning
-- ev ([ app , t2Type , pair ((x \\ # x₁) ^ thinning₁) ((oz \\ x₃) ^ thinning₂) cover ] ^ thinning) = {!!}
--   -- = [ app , t2Type , pair ((x \\ # x₁) ^ thinning₁) {!t2!} {!!} ] ^ {!!}
-- ev ([ app , t2Type , pair ((x \\ [ x₁ ]) ^ thinning₁) t2 cover ] ^ thinning) = {!!}
-- ev ([ lam , snd ] ^ thinning) = {!!}

ev : ∀{a ctx} → TmR LTyD a ctx → TmR LTyD a / ctx
ev (# x) = # x ^ oi
ev [ app , t2T , pair ((oz \\ # x₁) ^ thinning) ((oz \\ x₂) ^ thinning₁) cover ] -- = {!!}
  = [ (app , t2T , pair {!!} {!!} {!!}) ] ^ oi
ev [ app , t2T , pair ((oz \\ [ x ]) ^ thinning) t2 cover ] = {!!}
ev [ lam , snd ] = {!!}
