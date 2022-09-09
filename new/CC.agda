module CC where

open import TypeBasedCast using (Cast_⇒_)

open import CCSyntax Cast_⇒_ public
open import CCTyping Cast_⇒_ public

open import Values            public
open import ApplyCast         public
open import ApplyCastRelation public
open import ProxyElimination  public
