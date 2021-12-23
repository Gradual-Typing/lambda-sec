module Heap where

open import Data.List using (List)
open import Data.Product using (_×_)

open import Addr public
open import CC renaming (Term to CCTerm)

Heap = List (Addr × CCTerm)
