-- ----------------------------------------------------------------------
-- The Agda Descriptor Library
-- 
-- (Closed) Sets
-- ----------------------------------------------------------------------

module Data.Set where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ)
open import Data.Unit using (⊤)

open import Data.Desc using (Desc; μ; _##_; _⟶_; Π)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)


-- ----------------------------------------------------------------------
-- Definition
-- 
-- A `Desc is a closed dependent type theory of
-- strictly positive functors : Set/A → Set/A 
-- 
-- A `Set is a open dependent type theory of 
-- the Agda model
-- 
-- To ensure a closed universe, we use 
-- induction recursion.


data `Set : Set
⟦_⟧ : `Set → Set


private
  variable
    A : `Set 

data `Desc (A : `Set) : Set
⟪_⟫ : `Desc A → Desc ⟦ A ⟧

data `Set where
  `Fin : ℕ → `Set
  `Σ `Π : (B : `Set) → (⟦ B ⟧ → `Set) → `Set
  `μ : `Desc A → ⟦ A ⟧ → `Set

⟦ `Fin n ⟧ = Fin n
⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧ )
⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
⟦ `μ d a ⟧ = μ ⟪ d ⟫ a

infixr 6 _⟶_

data `Desc A where
  `Π : (B : `Set) → (⟦ B ⟧ → `Desc A) → `Desc A
  _⟶_ : `Desc A → `Desc A → `Desc A
  _`##_ : (`Set → `Set) → ⟦ A ⟧ → `Desc A

⟪ `Π B d ⟫ = Π ⟦ B ⟧ (λ b → ⟪ d b ⟫)
⟪ d₁ ⟶ d₂ ⟫ = ⟪ d₁ ⟫ ⟶ ⟪ d₂ ⟫
⟪ f `## a ⟫ = {!   !} ## a


-- ----------------------------------------------------------------------
-- Example (Basic)

-- `⊤ : `Set
-- `⊤ = `Fin 1

-- `tt : ⟦ `⊤ ⟧
-- `tt = zero

-- `const : `Set → `Desc `⊤
-- `const A = `Π A λ _ → `# `tt

-- _`≡_ : ⟦ A ⟧ → ⟦ A ⟧ → `Set
-- x `≡ y = `μ (`# x) y



-- ----------------------------------------------------------------------

-- pattern nil = zero
-- pattern cons = (suc zero)

-- TODO: First order isomorphisms

-- _ : ⟦ zero `≡ zero ⟧
-- _ = {! refl  !}


-- ListD : `Set → `Desc `⊤
-- ListD A = `Π (`Fin 2) 
--   λ{ nil → `# `tt
--    ; cons → `const A ⟶ `# `tt ⟶ `# `tt }

-- `List : `Set → `Set
-- `List A = `μ (ListD A) `tt

-- RoseD : `Set → `Desc `⊤
-- RoseD A = `const A ⟶ `List $ (`# `tt) ⟶ `# `tt

-- _#_ : (Set → Set) → A → Desc A
-- 
-- Computional:
-- f (X a)
-- 
-- Propositional:
-- f (a′ ≡ a)
