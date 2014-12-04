open import Data.List
open import Data.Product
open import Data.Char
open import Data.Integer
open import Function
open import Doc



DocString = record { Doc = List Char
                     ; <> = (λ ds1 ds2 ->  ds1 ++ ds2)
                     ; nil = []
                     ; text =  id
                     ; line = [ '\n']
                     ; nest = (λ i s -> ' ' ∷ s)
                     ; layout = (λ x -> x) }


