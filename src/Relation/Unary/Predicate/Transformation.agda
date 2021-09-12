-- ----------------------------------------------------------------------
-- The Agda Descriptor Library
-- 
-- Natural transformations on indexed families (predicates)
-- ----------------------------------------------------------------------

module Relation.Unary.Predicate.Transformation where

open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤)
open import Function using (_∘_)
open import Level using (Level; _⊔_; 0ℓ)
open import Relation.Unary

private
  variable
    a b c d ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Set a 
    B : Set b
    C : Set c
    D : Set d

-- ----------------------------------------------------------------------
-- Definition

-- A predicate transformation is a morphism between 2 predicates 
-- indexed by A and B (w/ levels ℓ₁ ℓ₂ for universe polymorphism)

infixr 0 _▷_ _►_

_▷_ : Set a → Set b → (ℓ₁ ℓ₂ : Level) → Set _
(A ▷ B) ℓ₁ ℓ₂ = Pred A ℓ₁ → Pred B ℓ₂

_►_ : Set a → Set b → Set _
(A ► B) = Pred A 0ℓ → Pred B 0ℓ


-- ----------------------------------------------------------------------
-- Composition and Identity

id : (A ▷ A) ℓ₁ ℓ₁
id = Function.id

_○_ : (B ▷ C) ℓ₂ ℓ₃ → (A ▷ B) ℓ₁ ℓ₂ → (A ▷ C) ℓ₁ _
X ○ Y = X ∘ Y

-- TODO: Cateogrical view

-- ----------------------------------------------------------------------
-- Special transformations

empty : (A ▷ B) ℓ₁ ℓ₂
empty = λ _ _ → ⊥

univ : (A ▷ B) ℓ₁ ℓ₂
univ = λ _ _ → ⊤

-- ----------------------------------------------------------------------
-- Operations on transformations

infixr 8 _⇉_
infixl 7 _⋏_
infixl 6 _⋎_

-- Negation
∼ : (A ▷ B) ℓ₁ ℓ₂ → (A ▷ B) ℓ₁ ℓ₂
∼ X = ∁ ∘ X

-- Implication
_⇉_ : (A ▷ B) ℓ₁ ℓ₂ → (A ▷ B) ℓ₁ ℓ₂ → (A ▷ B) ℓ₁ ℓ₂ 
X ⇉ Y = λ P → X P ⇒ Y P

-- Intersection
_⋏_ : (A ▷ B) ℓ₁ ℓ₂ → (A ▷ B) ℓ₁ ℓ₂ → (A ▷ B) ℓ₁ ℓ₂ 
X ⋏ Y = λ P → X P ∩ Y P

-- Union
_⋎_ : (A ▷ B) ℓ₁ ℓ₂ → (A ▷ B) ℓ₁ ℓ₂ → (A ▷ B) ℓ₁ ℓ₂
X ⋎ Y = λ P → X P ∪ Y P

-- TODO: Infinitary union + intersection

-- ----------------------------------------------------------------------
-- Combinators on transformations

-- Disjoint sum
_∣∣_ : (A ▷ C) ℓ₁ ℓ₂ → (B ▷ D) ℓ₁ ℓ₂ → (A ⊎ B ▷ C ⊎ D) ℓ₁ ℓ₂ 
(X ∣∣ Y) P (inj₁ x) = X (P ∘ inj₁) x
(X ∣∣ Y) P (inj₂ y) = Y (P ∘ inj₂) y

-- TODO: Product, etc



