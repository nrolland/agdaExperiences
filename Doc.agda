
open import Data.List
open import Data.Product
open import Data.Char
open import Data.Nat
open import Function
open import Data.String


record Docs : Set₁ where
  infixl 5 _<>_
  field
    Doc : Set
    _<>_  : Doc -> Doc -> Doc
    nil : Doc
    text : String -> Doc
    line : Doc
    nest : ℕ -> Doc -> Doc
    layout : Doc -> String

