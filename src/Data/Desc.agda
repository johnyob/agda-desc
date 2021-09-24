-- ----------------------------------------------------------------------
-- The Agda Descriptor Library
-- 
-- (Open) Descriptors
-- ----------------------------------------------------------------------

module Data.Desc where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there) 
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _,_)
open import Data.Var using (_-Scoped[_]; Var; get; zero; suc; tabulate)
open import Data.Unit.Polymorphic using (⊤; tt)

open import Level using (Level; 0ℓ; _⊔_)

open import Relation.Unary using (IUniversal; _⇒_)

private
  variable
    A : Set 

1ℓ : Level
1ℓ = Level.suc 0ℓ

-- ----------------------------------------------------------------------
-- Definition 
-- 
-- An open description is a open dependent type theory. 
-- Our theoretic model is described by:
-- 
-- Metatheoretic terms:
-- 
-- Agda sets          A, B ∷= ...
-- Agda values        x, y ∷= ...
-- 
-- Open object terms:
-- 
-- kinds              κ ∷= Set | Π A κ
-- types              T ∷= a | T x | Π A T | T ⟶ T
-- 
-- A descriptor is a set of well-kinded constructor types. 

data Kind : Set₁ where
  `Set₀ : Kind
  `Π : (A : Set) → (A → Kind) → Kind


private
  variable
    κ κ′ : Kind
    Γ : List Kind
    B : A → Kind

infixr 6 _⟶_

data Type : Kind -Scoped[ 1ℓ ] where
  `_ : ∀[ Var κ ⇒ Type κ ]
  _·_ : Type (`Π A B) Γ → (a : A) → Type (B a) Γ
  `Π : (A : Set) → (A → Type `Set₀ Γ) → Type `Set₀ Γ
  _⟶_ : Type `Set₀ Γ → Type `Set₀ Γ → Type `Set₀ Γ


mutual

  data Pos : Type κ Γ → Set where
    
    `_ : ∀ (x : Var κ Γ) 
      -- ----------------
      → Pos (` x)

    _·_ : ∀ {T : Type (`Π A B) Γ} 
      → Pos T
      → (a : A)
      -- ------------------------
      → Pos (T · a)

    `Π : (A : Set) {T : A → Type `Set₀ Γ}
      → ((a : A) → Pos (T a)) 
      -- --------------------------------
      → Pos (`Π A T)
    
    _⟶_ : ∀ {T T′ : Type `Set₀ Γ}
      → Neg T
      → Pos T′
      -- --------------------------
      → Pos (T ⟶ T′)
    
  data Neg : Type κ Γ → Set where

    _·_ : ∀ {T : Type (`Π A B) Γ} 
      → Neg T
      → (a : A)
      -- ------------------------
      → Neg (T · a)

    `Π : (A : Set) {T : A → Type `Set₀ Γ}
      → ((a : A) → Neg (T a)) 
      -- --------------------------------
      → Neg (`Π A T)
    
    _⟶_ : ∀ {T T′ : Type `Set₀ Γ}
      → Pos T
      → Neg T′
      -- --------------------------
      → Neg (T ⟶ T′)
    

data StrictPos : Type κ Γ → Set where

  `_ : ∀ (x : Var κ Γ) 
    -- ----------------
    → StrictPos (` x)

  _·_ : ∀ {T : Type (`Π A B) Γ} 
    → StrictPos T
    → (a : A)
    -- ------------------------
    → StrictPos (T · a)

  `Π : (A : Set) {T : A → Type `Set₀ Γ}
    → ((a : A) → StrictPos (T a)) 
    -- --------------------------------
    → StrictPos (`Π A T)


data Con : Type κ Γ → Set where

  `_ : ∀ (x : Var κ Γ) 
  -- ----------------
    → Con (` x)

  _·_ : ∀ {T : Type (`Π A B) Γ} 
    → Con T
    → (a : A)
    -- ------------------------
    → Con (T · a)

  `Π : (A : Set) {T : A → Type `Set₀ Γ}
    → ((a : A) → Con (T a)) 
    -- --------------------------------
    → Con (`Π A T)

  _⟶_ : ∀ {T T′ : Type `Set₀ Γ}
    → StrictPos T
    → Con T′
    -- --------------------------
    → Con (T ⟶ T′)


data Constr : Kind -Scoped[ 1ℓ ] where
  ! : {T : Type κ Γ} → Con T → Constr κ Γ

++⇒C : ∀{T : Type κ Γ} → StrictPos T → Con T
++⇒C (` x) = ` x
++⇒C (P · a) = ++⇒C P · a
++⇒C (`Π A P) = `Π A (λ a → ++⇒C (P a))

Desc : List Kind → Set₁
Desc Γ = List (Constr `Set₀ Γ)


-- ----------------------------------------------------------------------
-- Interpretation

lift⟦_⟧ᴷ : Kind → (ℓ : Level) → Set (Level.suc ℓ)
lift⟦ `Set₀ ⟧ᴷ ℓ = Set ℓ
lift⟦ `Π A κ ⟧ᴷ ℓ = (a : A) → lift⟦ κ a ⟧ᴷ ℓ

-- Lifting of lift⟦_⟧ᴷ to a context
lift⟪_⟫ᴷ : List Kind → (ℓ : Level) → Set (Level.suc ℓ)
lift⟪ Γ ⟫ᴷ ℓ = All (λ κ → lift⟦ κ ⟧ᴷ ℓ) Γ

⟦_⟧ᴷ : Kind → Set₁
⟦ `Set₀ ⟧ᴷ = Set
⟦ `Π A κ ⟧ᴷ = (a : A) → ⟦ κ a ⟧ᴷ

⟪_⟫ᴷ : List Kind → Set₁
⟪ Γ ⟫ᴷ = All ⟦_⟧ᴷ Γ


-- ----------------------------------------------------------------------
-- Fixpoint
-- 

-- To define the fixed point, we're looking for a fixpoint of the form:
--  μ : Desc Γ → ⟪ Γ ⟫ᴷ
-- 
-- To consider the interpretation of constructors and type formers, 
-- we first describe the terms formed by constructors and 
-- positive types:
-- 
-- constructor terms    c ∷= Constrᵢ | c · a | c · p


private
  variable
    C : Constr `Set₀ Γ
    D : Desc Γ

data Term : Constr `Set₀ Γ -Scoped[ 1ℓ ] where
  `Constr : ∀[ Var C ⇒ Term C ]
  _·_ : ∀ {A} {T : A → Type `Set₀ Γ} {C : (a : A) → Con (T a)} 
    → Term (! (`Π A C)) D → (a : A) → Term (! (C a)) D
  _•_ :  ∀ {T T′ : Type `Set₀ Γ} {P : StrictPos T} {C : Con T′}
    → Term (! (P ⟶ C)) D → Term (! (++⇒C P)) D → Term (! C) D


μᵏ : Constr κ Γ → Desc Γ → lift⟦ κ ⟧ᴷ 1ℓ
μᵏ {κ = `Set₀} C D = Term C D
μᵏ {κ = `Π _ _} (! C) D = λ a → μᵏ (! (C · a)) D


μᴰ : Desc Γ → lift⟪ Γ ⟫ᴷ 1ℓ
μᴰ D = tabulate λ x → μᵏ (! (` x)) D

-- ----------------------------------------------------------------------
-- Examples

ℕᴰ : Desc (`Set₀ ∷ [])
ℕᴰ = ! (` zero) ∷ ! ((` zero) ⟶ (` zero)) ∷ []

`ℕ : Set₁
`ℕ = get zero (μᴰ ℕᴰ)

pattern `zero = `Constr zero
pattern `suc n = `Constr (suc zero) • n

_ : `ℕ
_ = `suc (`suc `zero)
