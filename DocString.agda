--open import Data.Product
open import Data.Char
open import Data.String  hiding (_==_)
open import Data.Integer
open import Data.Bool
open import Function
open import Doc
import Data.List as List

module DocString where 

  module Other where
    record _×_  (A B : Set) : Set where
      constructor _,′_ 
      field
        proj1 : A
        proj2 : B

    open _×_


    open List
    map' : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → (A → B) → List A → List B
    map' f1 f2 []       = []
    map' f1 f2 (x ∷ xs) = f1 x ∷ List.map f2 xs

    lines : String → List String
    lines s =  List.map fromList ( let x = ( foldl (λ x  e -> let lines ,′ cur = x in
                                                             if '\n' == e then
                                                               ( _,′_ (reverse cur ∷ lines)  [] )
                                                             else
                                                               ( _,′_ lines  (e ∷ cur))
                                                            
                                                  ) ([] ,′ [] ) (toList s))
                                   in reverse (proj2 x) ∷ proj1 x )
    lines' : String → List String
    lines' s = s ∷ []
  --  ([] , []) ( ) 
  open Other
  
DocString = record { Doc = String
                     ; _<>_ = (λ ds1 ds2 ->  ds1 ++ ds2)
                     ; nil = ""
                     ; text =  id
                     ; line = "\n"
                     ; nest = (λ i s -> let spaces = fromList (List.replicate i ' ')
                                        in let r = unlines (List.reverse (map' id (λ s -> spaces ++ s) 
                                                                               (lines s) ))
                                           in r) 
                     ; layout = (λ x -> x) }


