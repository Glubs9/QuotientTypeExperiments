-- questions
  -- why can't we use a similar construction to this, why isn't it "good enough" to at least prove things up to isomorphism

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

open Equivalence {{...}} public

-- coequalizing pr1 and pr2 is a quotient type
pr1 : {a : Level} {_R_ : relation A} {x y : A} -> x R y -> A
pr1 {a} {_R_} {x} _ = x
pr2 : {a : Level} {_R_ : relation A} {x y : A} -> x R y -> A
pr2 {a} {_R_} {y} _ = y

postulate
  _R_ : relation A -- to remove all the extra {}

-- DARN :( this is wrong. I'm very grumpy
quot : Set n
quot = (a : A) -> Sigma A (_R_ a) -- is Sigma (b : A) (a R b) roughly



-- [ a ] = Sigma 
