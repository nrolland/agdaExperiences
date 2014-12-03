open import Data.List
open import Data.Product
open import Data.Char
open import Data.Integer
open import Function
open import Doc


DocString = record { Doc = List Char
                     ; <> = ++
                     ; nil = []
                     ; nest  i s = s
                     ; layout x = x  }
