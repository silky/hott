module Hott

infix 40 ~~
infix 40 ~=

data (~~) : t -> t -> Type where
  refl : a ~~ a 

refl_ : (a:t) -> a ~~ a
refl_ x = refl {a=x}

lhs : {a:t} -> {b:t} -> a ~~ b -> t
lhs {a} {b} p = a

rhs : {a:t} -> {b:t} -> a ~~ b -> t
rhs {a} {b} p = b

reify : (p : a ~~ b) -> (lhs p ~~ rhs p)
reify p = p

symm : a ~~ b -> b ~~ a
symm refl = refl


infixl 50 @
(@) : a ~~ b -> b ~~ c -> a ~~ c
(@) refl p = p

tran : a ~~ b -> b ~~ c -> a ~~ c
tran = (@)

tran_assoc : (p:a~~b) -> (q:b~~c) -> (r:c~~d) -> (p@(q@r) ~~ (p@q)@r)
tran_assoc refl refl refl = refl

tran_refl : (p:a~~b) -> (p ~~ p@refl)
tran_refl refl = refl

tran_symm : (p:a~~b) -> (q:b~~c) -> q ~~ symm p @ (p @ q)
tran_symm refl q = refl

ap : (f : t1 -> t2) -> a ~~ b -> f a ~~ f b
ap f refl = refl

rw : a ~~ b -> a -> b
rw refl = id

tr : (p:t->Type) -> a ~~ b -> p a -> p b
tr p q = rw (ap p q)


tr_tran : (p:t->Type) -> (p1 : a ~~ b) -> (p2 : b ~~ c) -> (x : p a) ->
          tr p p2 (tr p p1 x) ~~ (tr p (p1 @ p2) x)
tr_tran p refl refl x = refl

apd : (t2:t1->Type) -> (f : (x:t1) -> t2 x) -> (p: a ~~ b)
                    -> tr t2 p (f a)  ~~ f b
apd t2 f refl = refl

funrefl : (f : t1 -> t2) -> (a:t1) -> (f a ~~ f a)
funrefl f a = refl

lemma_2_4_3 : (f:a->b) -> (g:a->b) -> (h : (x:a) -> f x ~~ g x) ->
              (p:x1 ~~ x2) -> (h x1 @ ap g p ~~ ap f p @ h x2)
lemma_2_4_3 f g h refl = symm (tran_refl _)

lemma_2_4_4 : {x:a} -> (f:a->a) -> (h : (x:a) -> f x ~~ x) -> h (f x) ~~ ap f (h x)
lemma_2_4_4 {x} f h = part1 (h x) @ part2 (h x) (symm (h x)) @ part3 (h x)
  where part1 : (p : f x ~~ x2) -> h (f x) ~~ h (f x) @ p @ symm p
        part1 refl = tran_refl _ @ tran_refl _
        part2 : (p : f x1 ~~ x2) -> (q:x2~~x3) ->
                h (f x1) @ p @ q ~~ ap f p @ h x2 @ q
        part2 refl q = ap (@ q) (symm (tran_refl _))
        part3 : (p : f x ~~ x2) -> ap f (h x) @ p @ symm p ~~ ap f (h x)
        part3 refl = symm (tran_refl _) @ symm (tran_refl _)


------------------------
-- Contractible Types --
------------------------

data Contraction : Type -> Type where
  contraction : (a:t) -> ((b:t) -> (a ~~ b)) -> (Contraction t)

contraction_center : Contraction t -> t
contraction_center (contraction a ps) = a

contraction_path : (c : Contraction t) -> (b:t)
                 -> (contraction_center c ~~ b)
contraction_path (contraction a ps) b = ps b

isContr : Type -> Type
isContr = Contraction


------------
-- Fibers --
------------

data Fiber : (a -> b) -> b -> Type where
  fiber : (f:a->b) -> (x:a) -> (f x ~~ y) -> Fiber f y

fiber_value : {f:a->b} -> Fiber f y -> a
fiber_value (fiber f x p) = x

fiber_image : {y:b} -> {f:a->b} -> Fiber f y -> b 
fiber_image (fiber f x p) = rhs p

fiber_path : {f:a->b} -> (m:Fiber f y) -> f (fiber_value m) ~~ y
fiber_path (fiber f x p) = p

fiber_eq  : (m1 : Fiber f y) -> (m2 : Fiber f y) ->
            (p : fiber_value m1 ~~ fiber_value m2) ->
            (fiber_path m1 ~~ ap f p @ fiber_path m2) ->
            (m1 ~~ m2)
fiber_eq (fiber f x p) (fiber f x p) refl refl = refl


------------------
-- Equivalences --
------------------

isEquiv : {t2:Type} -> (f : t1 -> t2) -> Type
isEquiv {t2} f = (b:t2) -> Contraction (Fiber f b)

data (~=) : Type -> Type -> Type where
  equiv : (f : a -> b) -> isEquiv f -> (a ~= b)

eqf : (a ~= b) -> a -> b
eqf (equiv f fcs) a = f a

eqg : (a ~= b) -> b -> a
eqg (equiv f fcs) y = fiber_value (contraction_center (fcs y))

eqgf : (q : a ~= b) -> (x:a) -> eqg q (eqf q x) ~~ x
eqgf (equiv f fcs) x = ap fiber_value fpath
  where fpath : contraction_center (fcs (f x)) ~~ fiber f x refl
        fpath = contraction_path (fcs (f x)) (fiber f x refl)

eqfg : (q : a ~= b) -> (y:b) -> eqf q (eqg q y) ~~ y
eqfg (equiv f fcs) y = fiber_path (contraction_center (fcs y))

identity_is_equiv : isEquiv id
identity_is_equiv b = contraction idfiber idfiberpath
  where idfiber : Fiber id b
        idfiber = fiber id b refl
        idfiberpath (fiber _ _ refl) = refl

eq_refl : a ~= a
eq_refl = equiv id identity_is_equiv


-----------------------
-- Semi-isomorphisms --
-----------------------

data Iso : Type -> Type -> Type where
  iso : (f : a -> b) ->
        (g : b -> a) ->
        ((x:a) -> g (f x) ~~ x) ->
        ((y:b) -> f (g y) ~~ y) ->
        Iso a b

isof  : Iso a b -> a -> b
isof (iso f g gf fg) = f
isog  : Iso a b -> b -> a
isog (iso f g gf fg) = g
isogf : (i:Iso a b) -> (x:a) -> isog i (isof i x) ~~ x
isogf (iso f g gf fg) = gf
isofg : (i:Iso a b) -> (y:b) -> isof i (isog i y) ~~ y
isofg (iso f g gf fg) = fg

iso_symm : Iso a b -> Iso b a
iso_symm (iso f g gf fg) = iso g f fg gf

iso_tran : Iso a b -> Iso b c -> Iso a c
iso_tran (iso f1 g1 gf1 fg1) (iso f2 g2 gf2 fg2) =
  iso (f2 . f1) (g1 . g2) 
      (\ x => ap g1 (gf2 (f1 x)) @ gf1 x)
      (\ z => ap f2 (fg1 (g2 z)) @ fg2 z)

iso_lemma1 : (f:a->b) -> (g:b->a) ->
             (gf:(x:a)->g(f x)~~x) -> (fg:(y:b)->f(g y)~~y) ->
             (x:a) -> (gf (g (f x))) ~~ ap g (ap f (gf x))
iso_lemma1 f g gf fg x = lemma_2_4_4 (g . f) gf @ part1 (gf x)
  where part1 : (p : x1 ~~ x2) -> ap (g . f) p ~~ ap g (ap f p)
        part1 refl = refl
        
iso_fgfgf : (f:a->b) -> (g:b->a) ->
            (gf:(x:a)->g(f x)~~x) -> (fg:(y:b)->f(g y)~~y) -> (x:a) ->
            (ap f (gf (g (f x))) @ fg (f x) ~~ fg (f (g (f x))) @ ap f (gf x))
iso_fgfgf f g gf fg x = part1 @ part2
  where part1 : ap f (gf (g (f x))) @ fg (f x) ~~ ap f(ap g(ap f(gf x))) @ fg (f x)
        part1 = ap (\p => ap f p @ fg (f x)) (iso_lemma1 f g gf fg x)
        part2g : (y1:b) -> (y2:b) -> (p : f (g y1) ~~ y2) ->
                 ap f (ap g p) @ fg y2 ~~ fg (f (g y1)) @ p
        part2g y1 _ refl = tran_refl (fg (f (g y1)))
        part2 : ap f(ap g(ap f(gf x))) @ fg (f x) ~~ fg(f(g(f x))) @ ap f (gf x)
        part2 = part2g (f x) (f x) (ap f (gf x))

iso_isNormal : Iso a b -> Type
iso_isNormal (iso f g gf fg) = (x:a) -> fg (f x) ~~ ap f (gf x)

isodeep1 : (i:Iso a b) -> (x:a) -> (y:b) ->
           (isof i x ~~ y) -> (isog i y ~~ x)
isodeep1 (iso f g gf fg) x (f x) refl = gf x

isodeep2 : (i:Iso a b) -> (iso_isNormal i) ->
           (x:a) -> (y:b) -> (p : isof i x ~~ y) ->
           (isofg i y ~~ ap (isof i) (isodeep1 i x y p) @ p)
isodeep2 (iso f g gf fg) n x (f x) refl = n x @ tran_refl (ap f (gf x))

eq_to_iso : (t1 ~= t2) -> Iso t1 t2
eq_to_iso q = iso (eqf q) (eqg q) (eqgf q) (eqfg q) 


-------------------------------
-- Half-adjoint equivalences --
-------------------------------

data HAE : Type -> Type -> Type where
   hae : (f   : a -> b) -> 
         (g   : b -> a) ->
         (gf  : (x:a) -> g (f x) ~~ x) ->
         (fg  : (y:b) -> f (g y) ~~ y) ->
         (fgf : (x:a) -> fg (f x) ~~ ap f (gf x)) -> HAE a b

haef : HAE a b -> a -> b
haef (hae f g gf fg fgf) = f
haeg : HAE a b -> b -> a
haeg (hae f g gf fg fgf) = g
haegf : (h:HAE a b) -> (x:a) -> haeg h (haef h x) ~~ x
haegf (hae f g gf fg fgf) = gf
haefg : (h:HAE a b) -> (y:b) -> haef h (haeg h y) ~~ y
haefg (hae f g gf fg fgf) = fg
haefgf : (h:HAE a b) -> (x:a) -> haefg h (haef h x) ~~ ap (haef h) (haegf h x)
haefgf (hae f g gf fg fgf) = fgf

iso_to_hae : Iso a b -> HAE a b
iso_to_hae (iso f g gf fg) = (hae f g gf fg' fgf')
  where fg' : (y:b) -> f (g y) ~~ y
        fg' y = symm (fg (f (g y))) @ ap f (gf (g y)) @ fg y
        fgf1 : (p1:t1~~t2) -> (p2:t1~~t3) -> (p3:t3~~t4) -> (p4:t2~~t4) ->
               (p2 @ p3 ~~ p1 @ p4) -> (symm p1 @ p2 @ p3 ~~ p4)
        fgf1 refl p2 p3 p4 q = q
        fgf2 : (x:a) -> ap f (gf (g (f x))) @ fg (f x)
                     ~~ fg (f (g (f x))) @ ap f (gf x)
        fgf2 x = iso_fgfgf f g gf fg x
        fgf' : (x:a) -> fg' (f x) ~~ ap f (gf x)
        fgf' x = fgf1 _ _ _ _ (fgf2 x)


hae_to_eq : HAE a b -> (a ~= b)
hae_to_eq (hae f g gf fg n) = 
  equiv f (\y => contraction (fiber f (g y) (fg y)) (\m =>
     case m of
       fiber f x p =>
           fiber_eq (fiber f (g y) (fg y)) (fiber f x p)
                             (isodeep1 (iso f g gf fg) x y p)
                             (isodeep2 (iso f g gf fg) n x y p)))

hae_to_iso : HAE a b -> Iso a b
hae_to_iso (hae f g gf fg fgf) = iso f g gf fg

iso_to_eq : Iso a b -> (a ~= b)
iso_to_eq i = hae_to_eq (iso_to_hae i)

eq_symm : (a ~= b) -> (b ~= a)
eq_symm = iso_to_eq . iso_symm . eq_to_iso

eq_tran : (a ~= b) -> (b ~= c) -> (a ~= c)
eq_tran e1 e2 = iso_to_eq (iso_tran (eq_to_iso e1) (eq_to_iso e2))


----------------
-- Univalence --
----------------

path_to_eq : (a ~~ b) -> (a ~= b)
path_to_eq refl = eq_refl

univalence : isEquiv path_to_eq
univalence = ?univalence_axiom

univalence_eq : (a ~~ b) ~= (a ~= b)
univalence_eq = equiv path_to_eq univalence

eq_to_path : (a ~= b) -> (a ~~ b)
eq_to_path = eqg univalence_eq

eq_to_path_to_eq : (e : a ~= b) -> path_to_eq (eq_to_path e) ~~ e
eq_to_path_to_eq = eqfg univalence_eq

path_to_eq_to_path : (p : a ~~ b) -> eq_to_path (path_to_eq p) ~~ p
path_to_eq_to_path = eqgf univalence_eq

univalence_path : (a ~~ b) ~~ (a ~= b)
univalence_path = eq_to_path univalence_eq

rw_path : (p : a ~~ b) -> (x:a) -> (rw p x ~~ eqf (path_to_eq p) x)
rw_path refl x = refl

rw_eqpath : (e : a ~= b) -> (x:a) -> (rw (eq_to_path e) x ~~ eqf e x)
rw_eqpath e x = part1 @ part2
  where part1 : rw (eq_to_path e) x ~~ eqf (path_to_eq (eq_to_path e)) x
        part1 = rw_path (eq_to_path e) x
        part2 : eqf (path_to_eq (eq_to_path e)) x ~~ eqf e x
        part2 = ap (\e' => eqf e' x) (eq_to_path_to_eq e)

iso_to_path : Iso a b -> (a ~~ b)
iso_to_path = eq_to_path . iso_to_eq

-----------------------------
-- Function Extensionality --
-----------------------------

-- TODO: Prove funext from univalence.
-- funext : (f:a->b) -> (g:a->b) -> ((x:a) -> (f x ~~ g x)) -> (f ~~ g)
-- funext = ?funext_axiom


