module Study where

data    Zero  : Set where
record  One   : Set where constructor <>
data    Two   : Set where tt ff : Two

Tt : Two -> Set
Tt tt  = One
Tt ff  = Zero

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field fst : S; snd : T fst

_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
pattern !_ t = _ , t

infixr 4 !_ _,_ _*_
open Sg

data _==_ {X : Set}(x : X) : X -> Set where refl : x == x
{-# BUILTIN EQUALITY _==_ #-}
infixr 6 _==_

data Bwd (K : Set) : Set where
  _-_  : Bwd K -> K -> Bwd K
  B0   : Bwd K
infixl 7 _-_
data _<=_ {K} : Bwd K -> Bwd K -> Set where
  _o'  : forall {iz jz k} ->  iz <= jz ->     iz          <=  (jz  -   k)
  _os  : forall {iz jz k} ->  iz <= jz ->  (  iz  -   k)  <=  (jz  -   k)
  oz   :                                          B0      <=       B0
infixl 8 _o' _os
src trg : forall {K}{iz jz : Bwd K} -> iz <= jz -> Bwd K
src {iz = iz} th = iz
trg {jz = jz} th = jz
oi :  forall {K}{kz : Bwd K} ->
      kz <= kz
oi {kz = iz - k}  = oi os -- |os| preserves |oi|
oi {kz = B0}      = oz

_<&=_ :  forall {K}{iz jz kz : Bwd K} ->
         iz <= jz -> jz <= kz -> iz <= kz
th     <&= ph o'  = (th <&= ph) o'
th o'  <&= ph os  = (th <&= ph) o'
th os  <&= ph os  = (th <&= ph) os -- |os| preserves |<&=|
oz     <&= oz     = oz
infixr 7 _<&=_
infixr 6 _<=_
law-oi<&=   :  forall {K}{iz jz : Bwd K}        (th : iz <= jz) ->  oi <&= th == th
law-<&=oi   :  forall {K}{iz jz : Bwd K}        (th : iz <= jz) ->  th <&= oi == th
law-<&=<&=  :  forall {K}{iz jz kz lz : Bwd K}  (th : iz <= jz)(ph : jz <= kz)(ps : kz <= lz) ->
                                                                    th <&= (ph <&= ps) == (th <&= ph) <&= ps
law-oi<&= oz = refl
law-oi<&= (th os) rewrite law-oi<&= th = refl
law-oi<&= (th o') rewrite law-oi<&= th = refl

law-<&=oi oz = refl
law-<&=oi (th os) rewrite law-<&=oi th = refl
law-<&=oi (th o') rewrite law-<&=oi th = refl

law-<&=<&= th ph (ps o') rewrite law-<&=<&= th ph ps = refl
law-<&=<&= th (ph o') (ps os) rewrite law-<&=<&= th ph ps = refl
law-<&=<&= (th o') (ph os) (ps os) rewrite law-<&=<&= th ph ps = refl
law-<&=<&= (th os) (ph os) (ps os) rewrite law-<&=<&= th ph ps = refl
law-<&=<&= oz oz oz = refl
antisym :  forall {K}{iz jz : Bwd K}(th : iz <= jz)(ph : jz <= iz) ->
           Sg (iz == jz) \ { refl -> th == oi * ph == oi }
antisym oz oz = refl , refl , refl
antisym (th os) (ph os) with antisym th ph
antisym (.oi os) (.oi os) | refl , refl , refl = refl , refl , refl
antisym (th os) (ph o') with antisym (th o') ph
antisym (th os) (ph o') | refl , () , c
antisym (th o') (ph os) with antisym th (ph o')
antisym (th o') (ph os) | refl , b , ()
antisym (th o') (ph o') with antisym (oi o' <&= th) (oi o' <&= ph)
antisym (th os o') (ph o') | refl , () , c
antisym (th o' o') (ph o') | refl , () , c
Cix_ : Set -> Set1
Cix K = Bwd K -> Set

_<-_ : forall {K} -> K -> (Cix K)
k <- kz = B0 - k <= kz
data LamTm (iz : Bwd One) : Set where          -- |LamTm : (Cix One)|
  var  : (x : <> <- iz)  ->         LamTm iz   -- \emph{finds} a variable
  _$_  : (f s : LamTm iz) ->        LamTm iz   -- associates left
  lam  : (t : LamTm (iz - <>)) ->   LamTm iz   -- \emph{binds} a variable
infixl 5 _$_
_^L_ : forall {iz jz} -> LamTm iz -> iz <= jz -> LamTm jz
var i    ^L th = var (i <&= th)
(f $ s)  ^L th = (f ^L th) $ (s ^L th)
lam t    ^L th = lam (t ^L th os)
infixl 7 _^L_
data Tri {K} : {iz jz kz : Bwd K} -> iz <= jz -> jz <= kz -> iz <= kz -> Set where
  _t-''  : forall {iz jz kz k}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
             Tri th ph ps -> Tri {kz = _ - k}    th      (ph o')  (ps o')
  _t's'  : forall {iz jz kz k}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
             Tri th ph ps -> Tri {kz = _ - k} (  th o')  (ph os)  (ps o')
  _tsss  : forall {iz jz kz k}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
             Tri th ph ps -> Tri {kz = _ - k} (  th os)  (ph os)  (ps os)
  tzzz   : Tri oz oz oz
infixl 8 _t-'' _t's' _tsss
tri   :  forall {K}{iz jz kz : Bwd K}(th : iz <= jz)(ph : jz <= kz) -> Tri th ph (th <&= ph)
comp  :  forall {K}{iz jz kz : Bwd K}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
           Tri th ph ps -> ps == (th <&= ph)

tri    th       (ph  o')  = (tri th ph)  t-''
tri (  th  o')  (ph  os)  = (tri th ph)  t's'
tri (  th  os)  (ph  os)  = (tri th ph)  tsss
tri        oz        oz   =              tzzz

comp (t  t-'')  rewrite comp t  = refl
comp (t  t's')  rewrite comp t  = refl
comp (t  tsss)  rewrite comp t  = refl
comp     tzzz                   = refl
egTri :  forall {K}{k0 k1 k2 k3 k4 : K} ->  Tri {kz = B0 - k0 - k1 - k2 - k3 - k4}
                                            (oz os o' os) (oz os o' os o' os) (oz os o' o' o' os)
egTri = tzzz tsss t-'' t's' t-'' tsss
_->/_ :  forall {K}{iz jz kz : Bwd K} -> (iz <= kz) -> (jz <= kz) -> Set
ps ->/ ph = Sg _ \ th -> Tri th ph ps
triU :  forall {K}{iz jz kz : Bwd K}{th th' : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
        Tri th ph ps -> Tri th' ph ps -> th == th'
triU (t  t-'')  (t'  t-'')  rewrite triU t t'  = refl
triU (t  t's')  (t'  t's')  rewrite triU t t'  = refl
triU (t  tsss)  (t'  tsss)  rewrite triU t t'  = refl
triU     tzzz        tzzz                      = refl
_-:>_ : {I : Set}(S T : I -> Set) -> Set
S -:> T = forall {i} -> S i -> T i
data  All {K}     (P  : K      -> Set) : Bwd K  -> Set where
  B0   :                                      All P B0
  _-_  : forall {kz k} -> All P kz -> P k ->  All P (kz - k)

all  :   forall {K}{P Q : K -> Set} -> (P -:> Q) -> (All P -:> All Q)
all f B0        = B0
all f (pz - p)  = all f pz - f p
_<?=_ : forall {K P}{jz iz : Bwd K}  -> iz <= jz -> All P jz -> All P iz
oz       <?= B0        = B0
(th os)  <?= (pz - p)  = (th <?= pz) - p
(th o')  <?= (pz - p)  = th <?= pz
law-oi : forall {K}{kz : Bwd K}(th : kz <= kz) -> th == oi
law-oi th with antisym th th
law-oi .oi | refl , refl , refl = refl
record _/_ {K}(T : (Cix K))(scope : Bwd K) : Set where -- |(T /_) : (Cix K)|
  constructor _^_
  field {support} : Bwd K; thing : T support; thinning : support <= scope

map/ :  forall {K}{S T : (Cix K)} -> (S -:> T) -> ((S /_) -:> (T /_))
map/ f (s ^ th) = f s ^ th
infixl 7 _^_
open _/_
unit/ : forall {K}{T : (Cix K)} -> T -:> (T /_)
unit/ t = t ^ oi
mult/ : forall {K}{T : (Cix K)} -> ((T /_) /_) -:> (T /_)
mult/ ((t ^ th) ^ ph) = t ^ (th <&= ph)
thin/ : forall {K T}{iz jz : Bwd K} -> iz <= jz -> T / iz -> T / jz
thin/ th t = mult/ (t ^ th)
oe : forall {K}{kz : Bwd K} -> B0 <= kz
oe {kz = iz - k}  = oe o'
oe {kz = B0}      = oz
law-oe :  forall {K}{kz : Bwd K}
          (th : B0 <= kz) -> th == oe
law-oe oz = refl
law-oe (th o') rewrite law-oe th = refl
oe/ : forall {K}{iz kz : Bwd K}(th : iz <= kz) -> oe ->/ th
oe/ th with tri oe th
... | t rewrite law-oe (oe <&= th) = oe , t
data OneR {K} : (Cix K) where  <> : OneR B0
<>R : forall {K}{kz : Bwd K} -> OneR / kz; <>R = <> ^ oe
data Cover {K}(ov : Two) : {iz jz ijz : Bwd K} -> iz <= ijz -> jz <= ijz -> Set where
  _c's  : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
            Cover ov th ph -> Cover ov {ijz = _ - k}  (th o')  (ph os)
  _cs'  : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
            Cover ov th ph -> Cover ov {ijz = _ - k}  (th os)  (ph o')
  _css  : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz}{both : Tt ov} ->
            Cover ov th ph -> Cover ov {ijz = _ - k}  (th os)  (ph os)
  czz   : Cover ov oz oz
infixl 8 _c's _cs' _css
cop   :  forall {K}{kz iz jz : Bwd K}
         (th : iz <= kz)(ph : jz <= kz) ->
         Sg _ \ ijz -> Sg (ijz <= kz) \ ps ->
         Sg (iz <= ijz) \ th' -> Sg (jz <= ijz) \ ph' ->
         Tri th' ps th * Cover tt th' ph' * Tri ph' ps ph
cop (th  o') (ph  o')  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  t-''  , c       , tr  t-''
cop (th  o') (ph  os)  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  t's'  , c  c's  , tr  tsss
cop (th  os) (ph  o')  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  tsss  , c  cs'  , tr  t's'
cop (th  os) (ph  os)  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  tsss  , c  css  , tr  tsss
cop      oz       oz   =                                         ! ! ! !     tzzz  ,    czz  ,     tzzz
copU :  forall {K}{kz iz jz ijz : Bwd K}
        {th : iz <= kz}{ph : jz <= kz}{ps : ijz <= kz}{th' : iz <= ijz}{ph' : jz <= ijz}->
        Tri th' ps th -> Cover tt th' ph' -> Tri ph' ps ph ->
        forall {ijz'}{ps' : ijz' <= kz} -> th ->/ ps' -> ph ->/ ps' -> ps ->/ ps'
copU (tl t-'') c (tr t-'') (_ , ul t-'') (_ , ur t-'') with copU tl c tr (! ul) (! ur)
... | ! v = ! v t-''
copU (tl t's') () (tr t's') (! ul t-'') (! ur t-'')
copU (tl t-'') c (tr t-'') (! ul t's') (! ur t's') with copU tl c tr (! ul) (! ur)
... | ! v = ! v t's'
copU (tl t's') () (tr t's') (! ul t's') (! ur t's')
copU (tl t's') (c c's) (tr tsss) (! ul t's') (! ur tsss) with copU tl c tr (! ul) (! ur)
... | ! v = ! v tsss
copU (tl tsss) (c cs') (tr t's') (! ul tsss) (! ur t's') with copU tl c tr (! ul) (! ur)
... | ! v = ! v tsss
copU (tl tsss) (c css) (tr tsss) (! ul tsss) (! ur tsss) with copU tl c tr (! ul) (! ur)
... | ! v = ! v tsss
copU tzzz czz tzzz (_ , tzzz) (_ , tzzz) = ! tzzz
record _*R_ {K}(S T : (Cix K))(ijz : Bwd K) : Set where
  constructor pair
  field  outl : S / ijz ; outr   : T / ijz
         cover  : Cover tt (thinning outl) (thinning outr)

_,R_ : forall {K}{S T : (Cix K)}{kz} -> S / kz -> T / kz -> (S *R T) / kz
(s ^ th) ,R (t ^ ph) =
  let  ! ps , th' , ph' , _ , c , _ = cop th ph
  in   pair (s ^ th') (t ^ ph') c ^ ps
_++_ : forall {K}(kz jz : Bwd K) -> Bwd K
kz ++ B0        = kz
kz ++ (iz - j)  = (kz ++ iz) - j
infixl 7 _++_
_<++=_ :  forall {K}{iz jz iz' jz' : Bwd K} ->
  iz <= jz -> iz' <= jz' -> (iz ++ iz') <= (jz ++ jz')
th <++=      oz   =    th
th <++= (ph  os)  = (  th <++= ph) os
th <++= (ph  o')  = (  th <++= ph) o'
_-!_ : forall {K}{iz kz}(jz : Bwd K)(ps : iz <= (kz ++ jz)) ->
       Sg _ \ kz' -> Sg _ \ jz' -> Sg (kz' <= kz) \ th -> Sg (jz' <= jz) \ ph ->
       Sg (iz == (kz' ++ jz')) \ { refl -> ps == (th <++= ph) }
B0        -! ps                                               = ! ! ps , oz , refl , refl
(kz - k)  -! (ps os)             with kz -! ps
(kz - k)  -! (.(th <++= ph) os)  | ! ! th , ph , refl , refl  = ! ! th , ph os , refl , refl
(kz - k)  -! (ps o')             with kz -! ps
(kz - k)  -! (.(th <++= ph) o')  | ! ! th , ph , refl , refl  = ! ! th , ph o' , refl , refl
data _!-_ {K}(jz : Bwd K)(T : (Cix K))(kz : Bwd K) : Set where -- |jz !- T : (Cix K)|
  _\\_ : forall {iz} -> iz <= jz -> T (kz ++ iz) -> (jz !- T) kz

_\\R_ : forall {K T}{kz}(jz : Bwd K) -> T / (kz ++ jz) -> (jz !- T) / kz
jz \\R (t ^ ps) with jz -! ps
jz \\R (t ^ .(th <++= ph)) | ! ! th , ph , refl , refl = (ph \\ t) ^ th
infixr 5 _!-_
infixr 6 _\\_
infixr 6 _\\R_
data VaR {K}(k : K) : (Cix K) where only : VaR k (B0 - k)

vaR : forall {K}{k}{kz : Bwd K} -> k <- kz -> VaR k / kz
vaR x = only ^ x
data LamTmR : (Cix One) where
  var  : VaR <>               -:>  LamTmR
  app  : (LamTmR *R LamTmR)   -:>  LamTmR
  lam  : (B0 - <> !- LamTmR)  -:>  LamTmR
lamTmR : LamTm -:> (LamTmR /_)
lamTmR (var x)  = map/ var  (vaR x)
lamTmR (f $ s)  = map/ app  (lamTmR f ,R lamTmR s)
lamTmR (lam t)  = map/ lam  (_ \\R lamTmR t)
record Kind (I : Set) : Set where  inductive; constructor _=>_
                                   field scope : Bwd (Kind I); sort : I
infix 6 _=>_
open Kind
data Decide (X : Set) : Set where
  yes  : X ->            Decide X
  no   : (X -> Zero) ->  Decide X
record Datoid : Set1 where
  field  Data    : Set
         decide  : (x y : Data) -> Decide (x == y)
open Datoid

data Desc (I : Set) : Set1 where
  RecD   : Kind I ->  Desc I ;  SgD    : (S : Datoid) -> (Data S -> Desc I) ->  Desc I
  OneD   :            Desc I ;  _*D_   : Desc I -> Desc I ->                    Desc I
data LamTag : Set where app lam : LamTag

LAMTAG : Datoid
Data    LAMTAG = LamTag
decide  LAMTAG app  app  = yes refl
decide  LAMTAG app  lam  = no \ ()
decide  LAMTAG lam  app  = no \ ()
decide  LAMTAG lam  lam  = yes refl
LamD : One -> Desc One
LamD <> = SgD LAMTAG \  { app  -> RecD (B0 => <>) *D RecD (B0 => <>)
                        ; lam  -> RecD (B0 - (B0 => <>) => <>) }
data Ty : Set where base : Ty ; _>>_ : Ty -> Ty -> Ty
infixr 4 _>>_
TY : Datoid
Data TY = Ty
decide TY base base = yes refl
decide TY base (_ >> _) = no \ ()
decide TY (_ >> _) base = no \ ()
decide TY (sx >> tx) (sy >> ty) with decide TY sx sy | decide TY tx ty
decide TY (sx >> tx) (.sx >> .tx) | yes refl | yes refl = yes refl
decide TY (sx >> tx) (sy >> ty) | yes _ | no p = no \ { refl -> p refl }
decide TY (sx >> tx) (sy >> ty) | no p | _ = no \ { refl -> p refl }

data TyLTag : Ty -> Set where
  app : forall {T} -> TyLTag T
  lam : forall {S T} -> TyLTag (S >> T)

TYLTAG : Ty -> Datoid
Data (TYLTAG T) = TyLTag T
decide (TYLTAG T) app app = yes refl
decide (TYLTAG .(_ >> _)) app lam = no \ ()
decide (TYLTAG .(_ >> _)) lam app = no \ ()
decide (TYLTAG .(_ >> _)) lam lam = yes refl

LTyD : Ty -> Desc Ty
LTyD T = SgD (TYLTAG T) \  { app -> SgD TY \ S -> RecD (B0 => (S >> T)) *D RecD (B0 => S)
                           ; (lam {S}{T}) -> RecD (B0 - (B0 => S) => T) }
[!_!!_!] : forall {I} -> Desc I -> (I -> (Cix (Kind I))) -> (Cix (Kind I))
[! RecD k   !! R !] kz = R (sort k) (kz ++ scope k)
[! SgD S T  !! R !] kz = Sg (Data S) \ s -> [! T s !! R !] kz
[! OneD     !! R !] kz = One
[! S *D T   !! R !] kz = [! S !! R !] kz * [! T !! R !] kz
SpD : forall {I} -> Bwd (Kind I) -> Desc I
SpD      B0      =          OneD
SpD (kz  -   k)  = SpD kz   *D    RecD k
data Tm {I}(D : I -> Desc I)(i : I) kz : Set where -- |Tm D i : (Cix (Kind I))|
  _#$_  : forall {jz} -> (jz => i) <- kz ->  [! SpD jz  !! Tm D !] kz ->  Tm D i kz
  [_]   :                                    [! D i     !! Tm D !] kz ->  Tm D i kz
infixr 5 _#$_
[!_!!_!]R : forall {I} -> Desc I -> (I -> (Cix (Kind I))) -> (Cix (Kind I))
[! RecD k   !! R !]R = scope k !- R (sort k)
[! SgD S T  !! R !]R = \ kz -> Sg (Data S) \ s -> [! T s !! R !]R kz
[! OneD     !! R !]R = OneR
[! S *D T   !! R !]R = [! S !! R !]R *R [! T !! R !]R

data TmR {I}(D : I -> Desc I)(i : I) : (Cix (Kind I)) where
  #     : forall {jz} -> (VaR (jz => i) *R  [! SpD jz  !! TmR D !]R)  -:>  TmR D i
  [_]   :                                   [! D i     !! TmR D !]R   -:>  TmR D i
code   : forall {I}{D : I -> Desc I}{i}  ->  Tm D i           -:>  (TmR D i /_)
codes  : forall {I}{D : I -> Desc I} S   ->  [! S !! Tm D !]  -:>  ([! S !! TmR D !]R /_)
code                    (_#$_ {jz} x ts)  = map/ #    (vaR x ,R codes (SpD jz) ts)
code {D = D}{i = i}     [ ts ]            = map/ [_]  (codes (D i) ts)
codes (RecD k)          t                 = scope k \\R code t
codes (SgD S T)         (s , ts)          = map/ (s ,_) (codes (T s) ts)
codes OneD              <>                = <>R
codes (S *D T)          (ss , ts)         = codes S ss ,R codes T ts
tyS : (A B C : Ty) -> Tm LTyD ((A >> B >> C) >> (A >> B) >> (A >> C)) B0
tyS A B C = [ lam , [ lam , [ lam , [ app , _ , [ app , _ , oz os o' o' #$ <> , oz o' o' os #$ <> ] , [ app , _ , oz o' os o' #$ <> , oz o' o' os #$ <> ] ] ] ] ]
record HSub {I} D (src trg bnd : Bwd (Kind I)) : Set where
  field  pass act   : Bwd (Kind I);           passive  : pass  <= src;  active  : act <= src
         parti  : Cover ff passive active  ;  passTrg  : pass  <= trg;  actBnd  : act <= bnd
         images     : All (\ k -> (scope k !- TmR D (sort k)) / trg) act
open HSub
wkHSub :  forall {I}{D : I -> Desc I}{src trg bnd iz jz} ->
          HSub D src trg bnd -> iz <= jz -> HSub D (src ++ iz) (trg ++ jz) bnd
wkHSub {iz = iz}{jz = jz} h ph = record
  { parti = bindPassive iz ; actBnd = actBnd h ; passTrg = passTrg h <++= ph
  ; images = all (thin/ (oi <++= oe {kz = jz})) (images h) } where
  bindPassive : forall iz -> Cover ff (passive h <++= oi {kz = iz}) (active h <++= oe {kz = iz})
  bindPassive B0       = parti h
  bindPassive (iz - _) = bindPassive iz cs'
mutual
  selHSub :  forall {I}{D : I -> Desc I}{src src' trg bnd} ->
             src <= src' -> HSub D src' trg bnd -> HSub D src trg bnd
  selHSub ps (record { parti = c' ; actBnd = th' ; images = tz' ; passTrg = ph' }) =
    let ! ! ! ! ph , th , c = selPart ps c' in record
      { parti = c ; actBnd = th <&= th' ; images = th <?= tz' ; passTrg = ph <&= ph' }

  selPart :  forall {K}{iz' jz' kz kz' : Bwd K}{th' : iz' <= kz'}{ph' : jz' <= kz'}
             (ps : kz <= kz') -> Cover ff th' ph' ->
             Sg _ \ iz -> Sg _ \ jz -> Sg (iz <= kz) \ th -> Sg (jz <= kz) \ ph ->
             Sg (iz <= iz') \ ps0 -> Sg (jz <= jz') \ ps1 -> Cover ff th ph

  selPart (ps o') (c' c's) = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0    , ps1 o' , c
  selPart (ps o') (c' cs') = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0 o' , ps1 , c
  selPart (ps o') (c' css) = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0 o' , ps1 o' , c
  selPart (ps os) (c' c's) = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0 , ps1 os , c c's
  selPart (ps os) (c' cs') = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0 os , ps1 , c cs'
  selPart (ps os) (_css {both = ()} _)
  selPart oz czz = ! ! ! ! oz , oz , czz
allLeft : forall {K}{iz kz : Bwd K}{ov}{th : iz <= kz}{ph : B0 <= kz} -> Cover ov th ph -> iz == kz
allLeft (c cs') rewrite allLeft c = refl
allLeft czz = refl
hSub    : forall {I D src trg bnd}{i : I} ->
  HSub D src trg bnd -> TmR D i src              -> TmR D i / trg
hSubs   : forall {I D src trg bnd}(S : Desc I) ->
  HSub D src trg bnd -> [! S !! TmR D !]R src    -> [! S !! TmR D !]R / trg
hSubs/  : forall {I D src trg bnd}(S : Desc I) ->
  HSub D src trg bnd -> [! S !! TmR D !]R / src  -> [! S !! TmR D !]R / trg
hered   : forall {I D jz trg bnd}{i : I} ->
  (jz !- TmR D i) / trg -> B0 - (jz => i) <= bnd -> [! SpD jz !! TmR D !]R / trg -> TmR D i / trg
hSub {D = D}{i = i} h [ ts ] = map/ [_] (hSubs (D i) h ts)
hSub h (# {jz} (pair (only ^ th) ts _)) with selHSub th h | hSubs/ (SpD jz) h ts
... | record { parti = _css {both = ()} _ }                         | ts'
... | record { parti = czz cs' ; passTrg = ph }                     | ts' = map/ # (vaR ph ,R ts')
... | record { parti = czz c's ; actBnd = th' ; images = B0 - im }  | ts' = hered im th' ts'
hered                     im                (th' o') ts' = hered im th' ts'
hered {D = D}{trg = trg}  ((ph \\ t) ^ ps)  (th' os) ts' = let ! ! c = part _ _ in
  hSub (record { parti = c ; actBnd = ph ; images = ph <?= spAll ts' ; passTrg = ps }) t where
    spAll  :  forall {kz} -> [! SpD kz !! TmR D !]R / trg -> All _ kz
    part   :  forall kz iz -> Sg (kz <= (kz ++ iz)) \ th -> Sg (iz <= (kz ++ iz)) \ th' -> Cover ff th th'
    spAll {B0}              _                    = B0
    spAll {kz - (jz => i)}  (pair ts' t _ ^ ps)  = spAll (thin/ ps ts') - thin/ ps t
    part kz (iz - _) = let ! ! c = part kz iz in ! ! c c's
    part (kz - _) B0 = let ! ! c = part kz B0 in ! ! c cs'
    part B0 B0 = ! ! czz
hSubs (RecD k)   h (ph \\ t)     = scope k \\R hSub (wkHSub h ph) t
hSubs (SgD S T)  h (s , ts)      = map/ (s ,_) (hSubs (T s) h ts)
hSubs OneD       h <>            = <>R
hSubs (S *D T)   h (pair s t _)  = hSubs/ S h s ,R hSubs/ T h t
hSubs/ S h' (ts ^ th) with selHSub th h'
hSubs/ S h' (ts ^ th) | record { parti = c ; images = B0 ; passTrg = ph } rewrite allLeft c = ts ^ ph
hSubs/ S h' (ts ^ th) | h = hSubs S h ts
