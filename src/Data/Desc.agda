-- ----------------------------------------------------------------------
-- The Agda Descriptor Library
-- 
-- (Open) Descriptors
-- ----------------------------------------------------------------------

module Data.Desc where

open import Data.Product using (Σ; _×_)

open import Relation.Unary.Predicate.Transformation 
  using (_►_)
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    A : Set 
    
-- ----------------------------------------------------------------------
-- Definition 
-- 
-- An open description is a open dependent type theory of 
-- pattern functors of the form Set/A → Set/A
-- 
-- (Slices and exponentials):
-- Slice category Set/A = Σ (X : Set) (X → A). Note that equiv to 
-- exponential Set^A. Henceforth we use exponentials

infixr 6 _⟶_

data Desc (A : Set) : Set₁ where
  Π : (B : Set) → (B → Desc A) → Desc A
  _⟶_ : Desc A → Desc A → Desc A
  -- _%_ : (Set → Desc A) → A → Desc A
  # : A → Desc A

-- ----------------------------------------------------------------------
-- Interpretation

-- Note that by currying:
--  Set^A → Set^A ≅ A → (A → Set) → Set
-- 
-- This allows us to define the interpretation function (or denotation)
-- for descriptors as two functions:
--  ⟦_⟧₀ : (A → Set) → Set
--  ⟦_⦄₁ : (A → Set) → (A → Set)

-- The implementation of ⟦_⟧₀ is taken from the indexed descriptions formalization
-- and are described in
-- https://pages.lip6.fr/Pierre-Evariste.Dagand/stuffs/thesis-2011-phd/thesis.pdf

data μ (d : Desc A) (a : A) : Set

⟦_⟧₀ : Desc A → (A → Set) → Set
⟦ Π B d ⟧₀ X = Σ B (λ b → ⟦ d b ⟧₀ X)
⟦ d₁ ⟶ d₂ ⟧₀ X = ⟦ d₁ ⟧₀ X × ⟦ d₂ ⟧₀ X
-- ⟦ f % a ⟧₀ X = ⟦ f (X a) ⟧₀ X
⟦ # a ⟧₀ X = X a


-- We use ⟦_⟧₀ to implement ⟦_⟧₁. Which describes our 
-- pattern functor: Set^A → Set^A
-- Using the degenerate formalization: (A → Set) → Set
-- We now describe pattern functors formalization
-- of the form Set^A → Set^A
-- 
-- This is implemented using the ⟦_⟧₁ denotation


⟦_⟧₁ : Desc A → A ► A
⟦ Π B d ⟧₁ X a = Σ B (λ b → ⟦ d b ⟧₁ X a)
⟦ d₁ ⟶ d₂ ⟧₁ X a = ⟦ d₁ ⟧₀ X × ⟦ d₂ ⟧₁ X a
-- ⟦ f % a′ ⟧₁ X a = ⟦ f (a ≡ a′) ⟧₁ X a
⟦ # a′ ⟧₁ X a = a ≡ a′

⟦_⟧ : Desc A → A ► A
⟦_⟧ = ⟦_⟧₁


-- ----------------------------------------------------------------------
-- Fixpoint
-- 
-- The formal model of least fixed points is as usual:
-- μ : (Set^A → Set^A) → Set^A

data μ d a where
  node : ⟦ d ⟧ (μ d) a → μ d a