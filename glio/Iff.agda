module Iff where

-- NOTE: The definition of `iff` in PLFA is simpler and nicer to use than the one in agda-stdlib.
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
