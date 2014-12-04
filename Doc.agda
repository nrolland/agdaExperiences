
open import Data.List
open import Data.Product
open import Data.Char
open import Data.Nat
open import Function


record Docs : Set₁ where
  field
    Doc : Set
    <>  : Doc -> Doc -> Doc
    nil : Doc
    text : List Char -> Doc
    line : Doc
    nest : ℕ -> Doc -> Doc
    layout : Doc -> List Char

