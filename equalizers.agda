-- questions
  -- why can't we use a similar construction to this, why isn't it "good enough" to at least prove things up to isomorphism
            -- why do we need equality at all? if isomorhpism is substitutive then why can't we just use that?

open import Agda.Primitive

data _==_ {n : Level} {A : Set n} : A -> A -> Set n where
  refl : {x : A} -> x == x
  

data Sigma {n : Level} (A : Set n) (B : A -> Set n) : Set n where
  _,_ : (a : A) -> B a -> Sigma A B


postulate -- this is like a meta-theoretic for all if you get me
  n : Level
  A : Set n
  B : Set n
  f : A -> B
  g : A -> B


-- i start by constructing equalizers in type theory (up to extensionality)

equal-func : A -> Set n
equal-func x = f x == g x

E : Set n
E = Sigma A equal-func

i : E -> A
i (x , prf) = x


-- ext :( , not sure how to fix? (this is caused by my definition of E not being not extensional)
-- maybe make use of axiom k or something???
commutes : (X : Set n) (h : X -> A) -> Set n
commutes X h = (x : X) -> f (h x) == g (h x)

Ei-commutes : commutes E i -- the same as (x : E) -> f (i x) == g (i x)
Ei-commutes (a , prf) = prf

E-universal : {X : Set n} {h : X -> A} -> (commutes X h) -> X -> E
E-universal {X} {h} comm x = ( h(x) , comm x )

-- hehe nice :)

-- below here is the attmept at coequalizers / quotient types

relation : {a : Level} -> Set a -> Set (lsuc a)
relation {a} A = A -> A -> Set a

record Equivalence {a} {A : Set a} (_R_ : relation A) : Set a where
  field
    reflexivity : {x : A} -> x R x
    symmetry : {x y : A} -> x R y -> y R x
    transitivity : {x y z : A} -> x R y -> y R z -> x R z
    irrelevance : {x y : A} {p1 p2 : x R y} -> p1 == p2 -- has to be proof irrelevant (this solves everything :)

open Equivalence {{...}} public

postulate
  _R_ : relation A -- to remove all the extra {}
  _ : Equivalence _R_

-- coequalizing pr1 and pr2 is a quotient type
fst :  {x y : A} -> x R y -> A
fst {x} _ = x
snd : {x y : A} -> x R y -> A
snd {x} {y} _ = y

-- this is fR
quot : A -> Set n
quot a = Sigma A (_R_ a) -- is Sigma (b : A) (a R b) roughly


co-eq-subt1 : {{_ : Equivalence _R_}} {a b : A} {p : a R b} -> quot (fst p) -> quot (snd p)
co-eq-subt1 {a} {b} {p} (x , prf) = (x , symmetry (transitivity (symmetry prf) p))

co-eq-subt2 : {{_ : Equivalence _R_}} {a b : A} {p : a R b} -> quot (snd p) -> quot (fst p)
co-eq-subt2 {a} {b} {p} (x , prf) = (x , transitivity p prf)

-- in my head the co-eq-subt1 and co-eq-subt2 form the two halves of the subseteq set equality extensionality proofs (consider proof irrelevance)
-- they aren't literally equal in ITT but close enough to it that it shouldn't matter?

-- the following isomorphism is my attempt to formalise the above, although I think we have something strictly more powerful than isomorphism
-- co-eq-iso1 : {{_ : Equivalence _R_}} {a b : A} {p : a R b} {x : quot (fst p)}
--               -> co-eq-subt2 (co-eq-subt1 x) == x
-- co-eq-iso1 = {!!} -- I should be able to apply irrelvance here but I'm not sure how

-- co-eq-iso2 follows the same as co-eq-iso1 but i'll wait till I have co-eq-iso1 done before writing this


postulate
  C : Set n
  h : A -> C
  -- h-commutes : ?

-- universal property holds? hehe
-- this might be a bad thing actually
-- because this only works with the extra proofs or something?
k : {a : A} -> (quot a) -> C
k {a} _ = h(a)

