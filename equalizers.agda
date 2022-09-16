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
    reflexivity : (x : A) -> x R x
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


-- examples of quotients to show that it's practical to some extent

-- modulus 2

data N : Set where
  Z : N
  S : N -> N

-- bad names here
-- also this definiitions doesnt work
data _mod2_ : N -> N -> Set where
  baseZ : Z mod2 Z
  baseSZ : (S Z) mod2 (S Z)
  stepL : {a b : N} -> a mod2 b -> (S (S a)) mod2 b
  stepR : {a b : N} -> a mod2 b -> a mod2 (S (S b))

postulate
  mod2irr : {a b : N} -> (p1 : a mod2 b) -> (p2 : a mod2 b) -> p1 == p2
  -- not sure how to do this 
  -- maybe this is where HITs are necersarry
  -- I want to put this in definition for mod2 but it wont let me

-- proofs of reflexivity, symmetry, transitivity
mod2refl : (a : N) -> a mod2 a
mod2refl Z = baseZ
mod2refl (S Z) = baseSZ
mod2refl (S (S n)) = stepR (stepL (mod2refl n))

mod2symm : {a b : N} -> a mod2 b -> b mod2 a
mod2symm baseZ = baseZ
mod2symm baseSZ = baseSZ
mod2symm (stepL prf) = stepR (mod2symm prf)
mod2symm (stepR prf) = stepL (mod2symm prf)

-- mod2trans is gonna be really annoying to write so I will hold off for now
-- but it should be obvious (maybe prove ftom which makes this way easier)
postulate
  mod2trans : {a b c : N} -> a mod2 b -> b mod2 c -> a mod2 c


-- I need integers to do ftom2 

_x2 : N -> N
(Z x2) = Z
((S n) x2) = S (S (n x2))

-- data ftom2 : Set -> Set where
--   ftom2 : {a b : N} -> Sigma N ((== a - b) . x2) -- if you get what i'm saying

-- cause then irrelveance becomes irr (ftom2 (n , refl)) (ftom2 (n , refl)) = refl  -- uses K but still
