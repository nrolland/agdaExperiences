open import Data.List
open import Data.Product
open import Data.Char
open import Data.String
open import Data.Integer
open import Function
open import IO.Primitive
open import Doc
open import DocString
--open import Pretty -- adds s to MainPretty._.s
import Pretty


module MainPretty where


  open Pretty DocString.DocString renaming (s to ts)
  tts = let open Pretty DocString.DocString in s

  import Foreign.Haskell as Hask
  

  main : IO Hask.Unit
  main = putStrLn (toCostring (ts))
