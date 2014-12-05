
module AbelEquality  where

open import Data.Bool hiding (_∨_)
open import Data.List


data Step : Set where
  Left  : Step
  Right : Step

data Bintree (A : Set) : Set  where
  Tip : (a : A) ->  Bintree A
  Node : Bintree A -> Bintree A -> Bintree A
  
member : {A : Set} -> Bintree A -> A -> Bool
member (Tip a) x = {!!}
member (Node t t₁) x = {!!} 

_∨_ : Bool → Bool → Bool
false ∨ false  = false
true ∨ false  = true
x ∨ true = true   -- no definitional equality

testV : Bool -> Bool
testV = λ x -> x ∨ true  -- does not normalize C-c C-n

-- Because the first clause did not have a variable as first argument but the constructor
-- false, Agda splits the first argument of all clauses into the two cases false and true. To
-- get the correct behavior, we need to change the order of the clauses


_∨'_ : Bool → Bool → Bool
x ∨' true = true
false ∨' false  = false
true ∨' false  = true


testV' : Bool -> Bool
testV' = λ x -> x ∨' true  -- normalizes !
-- agda splits the case in the second argument
-- here it sees true and can reduce


-- propositional equality
-- a proof is a program which take a term and construct a
-- tautology
-- tautology is the least relation R /  aRa forall a

-- ps : refl a is the same as refl b is a and b are definitionally equal

-- this module is parameterised by A : Set.
-- every function inside it will refer to that same A
module Level0Equality (A : Set) where
  data _Tauto_ :  A → A → Set where
    refl2 : (a : A) → a Tauto a

  fsym : ∀ x y → x Tauto y → y Tauto x
  fsym .a .a (refl2 a) =  refl2 a

-- We match on x ≡ y, and since refl is the only constructor of this data type, refl a for
-- some variable a is only matching pattern. By this in turn forces x ≡ y to be definitionally
-- equal to a ≡ a meaning that both x and y must be definitionally equal to a.

open import Relation.Binary.PropositionalEquality

--The definition in the standard library is universe polymorphic.
-- It is hidden in a .Coremodule
-- such modules do not need to be imported explicitly
open import Data.List

++-assoc' : ∀ {a} {A : Set a} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc' [] yx zs = refl
++-assoc' (x ∷ xs) ys zs = cong ((λ l -> x ∷ l)) ( ++-assoc' xs ys zs)

open ≡-Reasoning
++-assoc : ∀ {a} {A : Set a} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =  begin
                     ([] ++ ys) ++ zs                   ≡⟨ refl ⟩
                     ys ++ zs                           ≡⟨ refl ⟩
                     [] ++ (ys ++ zs)
                     ∎
++-assoc (x ∷ xs) ys zs = begin
                          ((x ∷ xs) ++ ys) ++ zs  ≡⟨ refl ⟩
                          (x ∷ (xs ++ ys)) ++ zs  ≡⟨ refl ⟩
                          x ∷ ((xs ++ ys) ++ zs)  ≡⟨ cong (_∷_ x) (++-assoc xs ys zs) ⟩
                          x ∷ (xs ++ (ys ++ zs))  ≡⟨ refl ⟩
                          (x ∷ xs) ++ (ys ++ zs)
                          ∎


--http://people.inf.elte.hu/divip/AgdaTutorial/Functions.Equality_Proofs.html

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_)         --

+-right-identity' : ∀ n → n + 0 ≡ n
+-right-identity' zero    = refl
+-right-identity' (suc n) = cong suc (+-right-identity' n)


+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity zero =  begin
                           zero + zero     ≡⟨ refl ⟩
                           zero
                         ∎
+-right-identity (suc n) = begin
                            (suc n) + 0    ≡⟨ refl ⟩
                            suc (n + 0)    ≡⟨ cong suc (+-right-identity n) ⟩
                            suc n 
                            ∎

+-left-identity  : ∀ a → 0 + a ≡ a
+-left-identity a = refl


+-assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c -- hint: use cong
+-assoc zero b c = begin zero + (b + c )  ≡⟨ refl ⟩
                         (b + c)
                   ∎
+-assoc (suc a) b c = begin
                      (suc a) + (b + c)    ≡⟨ refl ⟩
                      suc (a + (b + c))    ≡⟨ cong suc (+-assoc a b c) ⟩
                      suc ((a + b) + c )   ≡⟨ refl ⟩  
                      (suc ( a + b )) + c  ≡⟨ refl ⟩
                      (suc a + b) + c
                      ∎

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero n = refl
m+1+n≡1+m+n (suc m) n = begin (suc m) + (suc n)    ≡⟨ refl ⟩
                               suc ( m + suc n)    ≡⟨ cong suc (m+1+n≡1+m+n m n) ⟩
                               suc ( suc (m + n )) ≡⟨ refl ⟩
                               suc ( suc m + n) 
                         ∎
--direct style
+-comut : ∀ m n → m +  n ≡  n + m
+-comut  m  zero  =  +-right-identity m 
+-comut  m  (suc n) = trans (m+1+n≡1+m+n m n)  (cong suc  (+-comut m n))

-- direct style with binders
+-comut''' : ∀ m n → m +  n ≡  n + m
+-comut'''  m  zero  =  +-right-identity m 
+-comut'''  m  (suc n) with (cong suc  (+-comut m n))|  m+1+n≡1+m+n m n 
+-comut'''  m  (suc n) | p | p2 =  trans p2 p 

-- other pm
+-comut'' : ∀ m n → m +  n ≡  n + m
+-comut''  zero    n =  sym (+-right-identity n)
+-comut''  (suc m) n =  sym ( trans (m+1+n≡1+m+n n m)  (cong suc (+-comut n m)) )

--equivalence
+-comut' : ∀ m n → m +  n ≡  n + m
+-comut'  m  zero  =  +-right-identity m 
+-comut'  m  (suc n)  = begin
                        m + suc n ≡⟨ m+1+n≡1+m+n m n ⟩
                        suc (m + n) ≡⟨ cong suc  (+-comut' m n) ⟩
                        suc (n + m) ≡⟨ refl ⟩
                        suc n + m
                        ∎
                   


fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList zero = []
toList (suc n) = tt ∷ toList n

p : toList 3 ≡ tt ∷ ( tt ∷ ( tt ∷ [] ))
p = begin  toList 3 ≡⟨ refl ⟩
           toList (suc 2) ≡⟨ refl ⟩
           tt ∷ toList 2 ≡⟨ refl ⟩
           tt ∷ toList (suc 1) ≡⟨ refl ⟩
           tt ∷ ( tt ∷ ( tt ∷  (toList 0 ))) ≡⟨ refl ⟩
           tt ∷ ( tt ∷ ( tt ∷  [] ))
           ∎

from-to : ∀ a → fromList (toList a) ≡ a
from-to zero = refl
from-to (suc a) = begin
                   fromList ( toList (suc a))  ≡⟨ refl ⟩
                   fromList ( tt ∷ toList a)   ≡⟨ refl ⟩
                   suc (fromList (toList a))   ≡⟨ cong suc (from-to a) ⟩
                   suc a
                   ∎

to-from : ∀ a → toList (fromList a) ≡ a
to-from [] = refl
to-from (tt ∷ a) =  begin toList(fromList (tt ∷ a) ) ≡⟨ refl ⟩
                          toList(suc(fromList a) ) ≡⟨ refl ⟩
                          tt ∷ (toList ( fromList a) ) ≡⟨ cong ( _∷_ tt) (to-from a) ⟩
                          tt ∷ a 
                          ∎
                                   

fromPreserves++ : ∀ (a b : List ⊤) → fromList (a ++ b) ≡ fromList a + fromList b
fromPreserves++ [] b = refl
fromPreserves++ (x ∷ a) b =  begin
                   fromList( ( x ∷ a ) ++ b ) ≡⟨ refl ⟩
                   fromList ( x ∷ ( a ++ b ) ) ≡⟨ refl ⟩
                   suc ( fromList (a ++ b) ) ≡⟨ cong suc (fromPreserves++ a b ) ⟩
                   suc ( fromList a + fromList b) ≡⟨ refl ⟩
                   suc ( fromList a) + fromList b ≡⟨ refl ⟩
                   fromList(x ∷ a) + fromList b
                   ∎
                                

toPreserves+ : ∀ (a b : ℕ) → toList (a + b) ≡ toList a ++ toList b
toPreserves+ zero b = refl
toPreserves+ (suc a) b =
                        begin
                        toList(suc a + b)           ≡⟨ refl ⟩
                        toList(suc (a + b))         ≡⟨ refl ⟩
                        tt ∷ toList(a + b)          ≡⟨ cong (_∷_ tt) (toPreserves+ a b) ⟩
                        tt ∷ (toList a ++ toList b) ≡⟨ refl ⟩
                        (tt ∷ toList a) ++ toList b ≡⟨ refl ⟩
                        toList (suc a) ++ toList b
                        ∎


distribʳ-*-+ : ∀ a b c → (a + b) * c ≡ a * c + b * c
distribʳ-*-+ zero b c = refl
distribʳ-*-+ (suc a) b c =
  begin --c + (a + b) * c is definitionally equal !
  c + (a + b) * c      ≡⟨ cong (λ x → c + x) (distribʳ-*-+ a b c) ⟩
  c + (a * c + b * c)  ≡⟨ +-assoc c (a * c) (b * c) ⟩
  c + a * c + b * c
  ∎

*-assoc        : ∀ a b c → a * (b * c) ≡ (a * b) * c
*-assoc zero b c = refl
*-assoc (suc a) b c = begin
    --(suc a) * (b * c ) ≡⟨ refl ⟩
    b * c  + a * (b * c) ≡⟨ refl ⟩
    b * c  + a * (b * c) ≡⟨ cong (λ x ->  ( b * c)  + x ) (*-assoc a b c)  ⟩ 
    b * c  + (a * b ) * c ≡⟨ sym (distribʳ-*-+ b  (a * b)  c)   ⟩
    (b + a * b ) * c      ≡⟨  refl  ⟩
    ((suc a) * b) * c     
    ∎
 
*-left-identity  : ∀ a → 1 * a ≡ a
*-left-identity a =  +-right-identity a

*-right-identity : ∀ a → a * 1 ≡ a
*-right-identity zero = refl
*-right-identity (suc a) =  cong suc (*-right-identity a)
                                  

-- helper functions:
n*0=0 : ∀ n → n * 0 ≡ 0
n*0=0 zero = refl
n*0=0 (suc n) =   n*0=0 n

*-suc : ∀ n m → n + n * m ≡ n * suc m
*-suc zero m = refl
*-suc (suc n) m =  cong suc (begin
                        n + ( m + ( n * m )) ≡⟨ +-assoc n m  ( n * m ) ⟩
                        (n + m) + ( n * m ) ≡⟨ cong (λ x -> x + n * m) (+-comut n m) ⟩
                        (m + n) + (n * m) ≡⟨ sym ( +-assoc m n  ( n * m )) ⟩
                        m + (n + n * m) ≡⟨ cong (λ x -> m + x) (*-suc n m) ⟩
                        m + n * (suc  m)
                        ∎ )
                        
*-comm : ∀ m n → m * n ≡ n * m
*-comm zero n = sym ( n*0=0 n)
*-comm (suc m) n =  begin  n + m * n ≡⟨ cong (λ x -> n + x) ( *-comm m n) ⟩
                           n + n * m ≡⟨  *-suc n m ⟩
                           n * (suc m)
                           ∎
                    
