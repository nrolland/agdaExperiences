
open import Data.List
open import Data.Product
open import Data.Char
open import Data.String
open import Data.Integer
open import Function
open import IO.Primitive
open import Doc


module Pretty(doc : Docs) where
  open Docs doc
  
  data Tree : Set where
    Node : String  -> List Tree -> Tree

  showBracket : List Tree -> Doc
  showTree : Tree -> Doc
  showTrees : List Tree -> Doc

  showTree (Node s lt)  =  (text (s)) <> nest ( length (toList s)) ( showBracket lt)

  showBracket [] = nil
  showBracket (ts) = text ( "[" ) <> nest 1 (showTrees ts ) <>   (text ( "]" ))

  showTrees ([]) =  nil
  showTrees (x ∷ []) =  showTree x
  showTrees (x ∷ t) =  showTree x <> text "," <> line <> showTrees t 
 
 
  a = Node  "aaa"   (Node "bbbbb" (Node "ccc" [] ∷ Node "dd" [] ∷ []) ∷ Node "eee" []  ∷ Node "fff" (Node "gg" [] ∷ Node "hhh" [] ∷ Node "ii" []  ∷ [] )  ∷ [])

  s = layout ( showTree a )
