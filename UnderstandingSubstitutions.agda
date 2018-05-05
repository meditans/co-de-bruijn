module UnderstandingSubstitutions where

open import Study
open HSub

-- Here I will do a personal rewrite of Conor's hereditary substitution, to
-- understand it better.

--------------------------------------------------------------------------------
-- Weakening substitutions
--------------------------------------------------------------------------------
-- Crucially, φ indicates which iz of the jz occur in the source term. So the
-- point here is that all the variables in iz are added to the passive variables
-- while the active variables remain the same, and passive and active are
-- similarly extended. Also the partition is updated to note that all the iz
-- have gone in the passive variables. The other significant change is that all
-- the images have been thinned to account for the fact that they are throwing
-- away the things in jz (that they don't need).
wkHSub' : ∀ {I}{D : I → Desc I}{src trg bnd iz jz}
        → HSub D src trg bnd
        → iz <= jz
        → HSub D (src ++ iz) (trg ++ jz) bnd
wkHSub' {iz = iz} {jz = jz} h φ =
  record
    { pass    = pass h ++ iz
    ; act     = act h
    ; passive = passive h <++= oi {kz = iz}
    ; active  = active  h <++= oe {kz = iz}
    ; parti   = bindPassive iz
    ; passTrg = passTrg h <++= φ
    ; actBnd  = actBnd h
    ; images  = all (thin/ (oi <++= oe {kz = jz})) (images h)
    }
  where
    -- bindPassive extends the partition with a cs' for each variable in iz
    -- (because they are active)
    bindPassive : forall iz -> Cover ff (passive h <++= oi {kz = iz}) (active h <++= oe {kz = iz})
    bindPassive B0       = parti h
    bindPassive (iz - _) = bindPassive iz cs'

--------------------------------------------------------------------------------
-- Whittling them down
--------------------------------------------------------------------------------
mutual
  -- The type of this is fairly straightforward, and the implementation
  -- essentially uses selPart'
  selHSub' :  forall {I}{D : I -> Desc I}{src src' trg bnd}
           -> src <= src' -> HSub D src' trg bnd -> HSub D src trg bnd
  selHSub' ψ s with selPart' ψ (parti s)
  selHSub' ψ s | iz , jz , th , ph , ps0 , ps1 , c
    = record
        { pass    = iz
        ; act     = jz
        ; passive = th
        ; active  = ph
        ; parti   = c
        ; passTrg = ps0 <&= passTrg s
        ; actBnd  = ps1 <&= actBnd s
        ; images  = ps1 <?= images s
        }

  -- A bit difficult to read here because Sg is the paper's internal notation
  -- for Σ, but the gist of it is that if I give you a kz <= kz' and a
  -- partitioning of kz' in th' and ph', then I can give you a partitioning of
  -- kz, just "reading" the corresponding choices in kz'. This function, in
  -- retrospective, is obvious.
  selPart' : forall {K}{iz' jz' kz kz' : Bwd K}{th' : iz' <= kz'}{ph' : jz' <= kz'}
             (ps : kz <= kz')
             -> Cover ff th' ph'
             -> Sg _ \ iz
             -> Sg _ \ jz
             -> Sg (iz <= kz) \ th
             -> Sg (jz <= kz) \ ph
             -> Sg (iz <= iz') \ ps0
             -> Sg (jz <= jz') \ ps1
             -> Cover ff th ph
           -- ps o' means that the new element is not in kz, the cover specifies where it was in kz'
  selPart' (ps o') (c' c's) = let ! ! ! ! ps0 , ps1 , c = selPart' ps c' in ! ! ! ! ps0 , ps1 o' , c
  selPart' (ps o') (c' cs') = let ! ! ! ! ps0 , ps1 , c = selPart' ps c' in ! ! ! ! ps0 o' , ps1 , c
  selPart' (ps o') (_css {both = ()} _)
  selPart' (ps os) (c' c's) = let ! ! ! ! ps0 , ps1 , c = selPart' ps c' in ! ! ! ! ps0 , ps1 os , c c's
  selPart' (ps os) (c' cs') = let ! ! ! ! ps0 , ps1 , c = selPart' ps c' in ! ! ! ! ps0 os , ps1 , c cs'
  selPart' (ps os) (_css {both = ()} _)
  selPart' oz czz = ! ! ! ! oz , oz , czz

--------------------------------------------------------------------------------
-- allLeft
--------------------------------------------------------------------------------
-- If the right part of a partition is empty, then the left must be full. The
-- proof is simple induction.
allLeft' : forall {K}{iz kz : Bwd K}{ov}{th : iz <= kz}{ph : B0 <= kz} -> Cover ov th ph -> iz == kz
allLeft' czz                        = refl
allLeft' (c cs') rewrite allLeft' c = refl

--------------------------------------------------------------------------------
-- The main functions
--------------------------------------------------------------------------------

-- hSub is the main operation on terms: given a substitution between contexts,
-- and a term, it applies the substitution. Let's notice here that the term uses
-- all his variables in a relevant way, while the resulting term may not use all
-- of them.
hSub'    : forall {I D src trg bnd}{i : I}
         -> HSub D src trg bnd -> TmR D i src -> TmR D i / trg
-- This function is used to apply a substitution to a description in the
-- co-de-Bruijn syntax.
hSubs'   : forall {I D src trg bnd}(S : Desc I)
         -> HSub D src trg bnd -> [! S !! TmR D !]R src -> [! S !! TmR D !]R / trg
-- This is the lifted version of the preceding function: the source term doesn't
-- need to use all the variables in src.
hSubs/'  : forall {I D src trg bnd}(S : Desc I)
         -> HSub D src trg bnd -> [! S !! TmR D !]R / src -> [! S !! TmR D !]R / trg
-- This is to substitute the variable hereditarily: it is the part that
-- explicitly involves the spine construction
hered'   : forall {I D jz trg bnd}{i : I}
         -> (jz !- TmR D i) / trg -> B0 - (jz => i) <= bnd -> [! SpD jz !! TmR D !]R / trg -> TmR D i / trg

-- We can have two constructs here: a syntax construct or a variable. In the
-- first case, we will continue substituting into the structure. In the second
-- case, we have to understand whether the variable we're talking about is
-- passive or active, so we pattern match on selHSub', with a first argument,
-- th, which has been refined enough to admit only one variable (the other
-- argument is of course the substitution). We also compute the substitution in
-- the spine, via hSubs/'. Next, if the variable is passive, we just return the
-- variable with the new computed interpretation of the spine, while if the
-- variable is active, we substitute hereditarily using the image.
hSub' {D = D}{i = i} h [ ts ] = map/ [_] (hSubs' (D i) h ts)
hSub' h (# {jz} (pair (only ^ th) ts _)) with selHSub' th h | hSubs/' (SpD jz) h ts
... | record { parti = _css {both = ()} _ }                        | ts'
... | record { parti = czz cs' ; passTrg = ph }                    | ts' = map/ # (vaR ph ,R ts')
... | record { parti = czz c's ; actBnd = th' ; images = B0 - im } | ts' = hered im th' ts'

hSubs'   = {!!}
hSubs/'  = {!!}
hered'   = {!!}
