module Data.Var where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Function using (const; _∘_)

open import Level using (Level; 0ℓ)

open import Relation.Unary using (IUniversal; _⇒_; _⊢_)

-- ------------------------------------------------------------------------
-- Vars and Contexts

private
  variable
    a b : Level

_-Scoped[_] : Set a → (b : Level) → Set _
I -Scoped[ b ] = I → List I → Set b

private
  variable
    I J : Set a
    i j : I
    Γ : List I

data Var : I -Scoped[ 0ℓ ] where
  zero : ∀[ (i ∷_) ⊢ Var i ]
  suc : ∀[ Var i ⇒ (j ∷_) ⊢ Var i ]

get : {P : I → Set b} → ∀[ Var i ⇒ All P ⇒ const (P i) ]
get zero (p  ∷ _) = p
get (suc v) (_  ∷ ps) = get v ps

_<$>_ : (f : I → J) → ∀[ Var i ⇒ map f ⊢ Var (f i) ]
f <$> zero = zero
f <$> suc v = suc (f <$> v)

tabulate : {P : I → Set b} → (∀ {i} → Var i Γ → P i) → All P Γ
tabulate {Γ = []} f = []
tabulate {Γ = i ∷ Γ} f = f zero ∷ tabulate (f ∘ suc)