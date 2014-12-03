
module Logic where

data _∧_ (A B : Set) : Set where
  _,_ : A -> B -> A ∧ B

data _∨_ (A B : Set) : Set where
  inl : A -> A ∨ B
  inr : B -> A ∨ B
