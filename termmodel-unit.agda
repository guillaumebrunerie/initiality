{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import typetheory
open import reflection hiding (proj)
open import syntx
open import rules
open import contextualcat
open import quotients
open import termmodel-common
open import termmodel-synccat
open import termmodel-uuel

open CCat hiding (Mor) renaming (id to idC)
