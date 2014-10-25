module AgdaSort where

infixr 5 _∷_
data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

foldr : ∀ {A} {B : Set} → (A → B → B) → B → List A → B
foldr f b []       = b
foldr f b (a ∷ as) = f a (foldr f b as)


data Either (A : Set) (B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

[_,_] : ∀ {A B} {C : Set} → (A → C) → (B → C) → Either A B → C
[ f , g ] (left x)  = f x
[ f , g ] (right x) = g x


data Empty : Set where

absurd : {X : Set} → Empty → X
absurd ()

infix 3 ¬_
¬_ : Set → Set
¬ X = X → Empty


-- This defines Rel to be the set of relations on X 
-- it is given by a function from X to X to some type
Rel : Set →  Set₁
Rel X = X → X → Set

Decidable : ∀ {X} → Rel X → Set
Decidable R = ∀ x y → Either (R x y) (¬ (R x y))

-- This declares what an equivalence is
-- An equivalence record/type class is a Rel to which the following operations have been specified 
record Equivalence {X} (_≈_ : Rel X) : Set1 where
  field
    refl  : ∀ {x}     → x ≈ x
    sym   : ∀ {x y}   → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

-- A Total Order is a couple of relation endowed with the following operations
record TotalOrder {X} (_≈_ : Rel X) (_≤_ : Rel X) : Set₁ where
  field
    antisym     : ∀ {x y}   → x ≤ y → y ≤ x → x ≈ y
    trans       : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    total       : ∀ x y     → Either (x ≤ y) (y ≤ x)
    reflexive   : ∀ {x y}   → x ≈ y → x ≤ y
    equivalence : Equivalence _≈_

-- The module sort contains some functions
-- it needs to be provided a decidable relation and a total order 
module Sort {X} {_≈_ _≤_ : Rel X}
            (_≤?_ : Decidable _≤_) (ord : TotalOrder _≈_ _≤_) where
  open TotalOrder ord using (total; equivalence)
  open Equivalence equivalence using (refl)

  --  we lift our type `X` in a data type that contains a
  -- top and bottom elements, that are respectively greater or equal and lower or
  -- equal than all the other elements.
  -- X is bound by the module

  data ⊥X⊤ : Set where
    ⊤ ⊥ : ⊥X⊤
    ⟦_⟧ : X → ⊥X⊤

  data _≤̂_ : Rel ⊥X⊤ where
    ⊥≤̂     : ∀ {x} → ⊥ ≤̂ x
    ≤̂⊤     : ∀ {x} → x ≤̂ ⊤
    ≤-lift : ∀ {x y} → x ≤ y → ⟦ x ⟧ ≤̂ ⟦ y ⟧

  -- nil works with any bounds, takes a proof that l is less than u and construct an element
  -- Cons takes any x
  --            an xs who belongs to the set of OList from lifted x to some upper bound u
  --            a proof that some element l is lower that lifted x
  --            ad gives back an OList from l to u
  data OList (l u : ⊥X⊤) : Set where
    nil  : l ≤̂ u → OList l u
    cons : ∀ x (xs : OList ⟦ x ⟧ u) → l ≤̂ ⟦ x ⟧ → OList l u

  -- takes a proof that x is in l u, and insert the element to give back an ordered list
  -- here l<y is the binding for the variable which is the lifted proof specified in the type signature
  -- this is the important part of the programm where dependent types are put in action !
  -- works this out !
  insert : ∀ {l u} y → OList l u → l ≤̂ ⟦ y ⟧ → ⟦ y ⟧ ≤̂ u → OList l u
  insert y (nil _)         l≤y y≤u = cons y (nil y≤u) l≤y
  insert y (cons x xs l≤x) l≤y y≤u with y ≤? x  --l is bound. we have --l---y--u-- and ---l--x----

  insert y (cons x xs l≤x) l≤y y≤u | left  y≤x = cons y (cons x xs (≤-lift y≤x)) l≤y  
  -- above  y≤x is a just a binding
  -- the inner expression has type OList y u 
  -- the outer expression has type Olist l u

  insert y (cons x xs l≤x) l≤y y≤u | right y>x =
    cons x (insert y xs ([ ≤-lift , (λ y≤x → absurd (y>x y≤x)) ] (total x y)) y≤u) l≤x
  -- recursive definition - we insert y further, in xs 
  -- so that the second argument of insert should be the proof that y is higher than the new lower bound of xs
  -- that new lower bound is x
  -- we make a case split by hand : total tells us wether x is less equal than y
  -- in the first case, we just lift the proof
  -- in the second case, we proove a  contradiction

  toList : ∀ {l u} → OList l u → List X
  toList (nil _)       = []
  toList (cons x xs _) = x ∷ toList xs







