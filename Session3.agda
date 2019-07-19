
{-

|---------------------------------------------------|
| Formal systems and their applications: exercises  |
| Session 3: Formalization of programming languages |
|---------------------------------------------------|

In this exercise session, the goal will be to see how Agda can be used to formalize
syntax, evaluation rules, and typing rules of programming languages. In this session,
you will do this for a very simple calculus, typed arithmetic expressions from
chapter 8 of "Types and Programming Languages". In the project for this course, you
will have to do the same for a more complicated language.
So you can see this exercise session as a kind of warm-up for the project.

-}

open import Data.Nat renaming (ℕ to Nat ; _≟_ to equalNat?) hiding (pred ; _≤_ ; compare)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum hiding (map) renaming (inj₁ to left ; inj₂ to right)


-- Part 1: Untyped boolean terms
--==============================
-- First, we will define the basic syntax of a very simple untyped language of boolean
-- expressions (see TAPL p. 34):
data Term : Set where
  tmTrue   : Term
  tmFalse  : Term
  tmIf     : (t1 t2 t3 : Term) → Term
  tmZero   : Term
  tmSuc    : Term → Term
  tmIsZero : Term → Term
  tmPred   : Term → Term


-- As a Warm-up exercise, define a function to calculate the size of a term
-- (see TAPL p. 29):
size : Term → Nat
size tmTrue         = 1
size tmFalse        = 1
size tmZero         = 1
size (tmSuc t1)     = 1 + (size t1)
size (tmIsZero t1)  = 1 + (size t1)
size (tmPred t1)    = 1 + (size t1)
size (tmIf t t₁ t₂) = size t + size t₁ + size t₂

-- In contrast to the TAPL book, in Agda we usually don't define a separate syntactic
-- class of values. Instead, we define a predicate "IsValue t" on terms that expresses
-- that the term t is a value.

data IsNum : Term → Set where
  numZero  : IsNum tmZero
  numSuc   : {t1 : Term} → IsNum t1 → IsNum (tmSuc t1)


data IsValue : Term → Set where
  valTrue  : IsValue tmTrue
  valFalse : IsValue tmFalse
  valNum   : {t1 : Term} → IsNum t1 → IsValue t1



-- To give the operational semantics of our language, we define the one-step evaluation
-- relation ↝ (unicode input: \r~) as an indexed datatype in Agda.
data _↝_ : Term → Term → Set where
  e-IfTrue     : {t2 t3 : Term} → ((tmIf tmTrue t2 t3) ↝ t2)
  e-IfFalse    : {t2 t3 : Term} → ((tmIf tmFalse t2 t3) ↝ t3)
  e-If         : {t1 t2 t3 t1' : Term} → (t1 ↝ t1') → tmIf t1 t2 t3 ↝ tmIf t1' t2 t3
  e-IsZeroZero : tmIsZero tmZero ↝ tmTrue
  e-IsZeroSuc  : {t1 : Term} → (IsNum t1) → tmIsZero (tmSuc t1) ↝ tmFalse
  e-IsZero     : {t1 t2 : Term} → t1 ↝ t2 → tmIsZero t1 ↝ tmIsZero t2
  e-PredSuc    : {t1 : Term} → (IsNum t1) → tmPred (tmSuc t1) ↝ t1
  e-Suc        : {t1 t2 : Term} → t1 ↝ t2 → tmSuc t1 ↝ tmSuc t2
  e-PredZero   : tmPred tmZero ↝ tmZero
  e-Pred       : {t1 t2 : Term} → t1 ↝ t2 → tmPred t1 ↝ tmPred t2

  -- Add more constructors here, one for each evaluation rule

-- A term is normal if it doesn't evaluate any further
IsNormal : Term → Set
IsNormal t = {t' : Term} → (t ↝ t') → ⊥

-- Prove that all values are normal (Theorem 3.5.7 of TAPL):
values-normal : {t : Term} → IsValue t → IsNormal t
values-normal {.tmTrue} valTrue ()
values-normal {.tmFalse} valFalse ()
values-normal {.tmZero} (valNum numZero) ()
values-normal {.(tmSuc _)} (valNum (numSuc x)) (e-Suc t1-t2) = values-normal (valNum x) t1-t2 

-- _↝*_ is the multi-step evaluation relation:
-- x ↝* y means that x ↝ x1 ↝ x2 ↝ ... ↝ y
data _↝*_ : Term → Term → Set where
  done : {x : Term} → (x ↝* x)
  step_,_ : {x x1 y : Term} → (x ↝ x1) → (x1 ↝* y) → (x ↝* y)
infixr 0 step_,_

-- Exercise: as a test, state and prove that
--   if t then false else false ↝* false
-- where
--   s = if true then false else false
--   t = if s then true else true
-- Note: proving should be possible using C-c C-a.

s : Term
s = tmIf tmTrue tmFalse tmFalse

t' : Term
t' = tmIf s tmTrue tmTrue

test-eval1 : tmIf t' tmFalse tmFalse ↝* tmFalse
test-eval1 = step e-If (e-If e-IfTrue) ,
               step e-If e-IfFalse , step e-IfTrue , done


-- Part 2: Untyped arithmetic terms
--=================================

-- As an exercise, add new syntactic forms and evaluation rules for natural numbers
-- to the definitions above (see TAPL p. 41). Also add extra cases to the other 
-- functions so that everything typechecks again. You will need to define a new
-- datatype IsNumValue : Term → Set that describes when a term is a numeric value.
--   (When making changes, it is best to comment out all that follows, to make Agda
--   stop complaining. That way, you can make your document consistent again
--   definition by definition.)

-- Exercise: as a test, state and prove that
--   if false then 0 else (pred (suc (pred 0))) ↝* 0

test-eval2 : tmIf tmFalse tmZero (tmPred (tmSuc (tmPred tmZero))) ↝* tmZero
test-eval2 = step e-IfFalse ,
               step e-Pred (e-Suc e-PredZero) , step e-PredSuc numZero , done



-- Part 3: Typed arithmetic terms
--===============================

-- Now we will define a type system for this simple language of booleans and
-- natural numbers. It has two types: Bool and Nat.
data Type : Set where
  tyBool : Type
  tyNat  : Type

-- As with the evaluation rules, we encode the typing rules as a data type
-- We use the unicode symbol ∈ (input \in) instead of a colon because the colon
-- is already reserved by Agda.
-- We use the prefix d- for elements of this type, which are called [d]erivations.
data _∈_ : Term → Type → Set where
  d-True : tmTrue ∈ tyBool
  d-False : tmFalse ∈ tyBool
  d-Zero : tmZero ∈ tyNat
  d-Suc  : {t : Term} → t ∈ tyNat → tmSuc t ∈ tyNat
  d-Pred : {t : Term} → t ∈ tyNat → tmPred t ∈ tyNat
  d-IsZero : {t : Term} → t ∈ tyNat → tmIsZero t ∈ tyBool
  d-If   : {t1 t2 t3 : Term} {T : Type} → t1 ∈ tyBool → t2 ∈ T → t3 ∈ T → tmIf t1 t2 t3 ∈ T
-- insert more constructors here (one for each typing rule on TAPL p. 93)

-- As a test, prove that the term `if (iszero 0) then 0 else (pred 0)`
-- has type Nat.
test-typing : tmIf (tmIsZero tmZero) tmZero (tmPred tmZero) ∈ tyNat
test-typing = d-If (d-IsZero d-Zero ) d-Zero (d-Pred d-Zero)

-- Inversion lemmas (see TAPL p. 94):
inversion-true : {tyR : Type} → tmTrue ∈ tyR → tyR ≡ tyBool
inversion-true {.tyBool} d-True = refl

-- Exercise: state and prove at least two more inversion lemmas

inversion-false : {tyR : Type} → tmFalse ∈ tyR → tyR ≡ tyBool
inversion-false d-False = refl

inversion-if : {t1 t2 t3 : Term} {tyR : Type} → (tmIf t1 t2 t3) ∈ tyR → t1 ∈ tyBool × (t2 ∈ tyR × t3 ∈ tyR)
inversion-if (d-If t1b t2r t3r) =  t1b , t2r , t3r

inversion-zero : {tyR : Type} → tmZero ∈ tyR → tyR ≡ tyNat
inversion-zero d-Zero = refl

inversion-succ : {t : Term} {tyR : Type} → tmSuc t ∈ tyR → t ∈ tyNat × tyR ≡ tyNat
inversion-succ (d-Suc suct_nat) = suct_nat , refl

inversion-pred : {t : Term} {tyR : Type} → tmPred t ∈ tyR → t ∈ tyNat × tyR ≡ tyNat
inversion-pred (d-Pred predt_nat) = predt_nat , refl

inversion-iszero : {t : Term} {tyR : Type} → tmIsZero t ∈ tyR → t ∈ tyNat × tyR ≡ tyBool
inversion-iszero (d-IsZero t_nat) = t_nat , refl

-- Uniqueness of types (see TAPL p. 94):
uniqueness-of-types : {t : Term} {tyT1 tyT2 : Type} → t ∈ tyT1 → t ∈ tyT2 → tyT1 ≡ tyT2
uniqueness-of-types d-True d-True = refl
uniqueness-of-types d-False d-False = refl
uniqueness-of-types d-Zero d-Zero = refl
uniqueness-of-types (d-Suc d1) (d-Suc d2) = refl
uniqueness-of-types (d-Pred d1) (d-Pred d2) = refl
uniqueness-of-types (d-IsZero d1) (d-IsZero d2) = refl
uniqueness-of-types (d-If d1 d3 d4) (d-If d2 d5 d6) = uniqueness-of-types d4 d6

-- Part 4: Safety = progress + preservation (see TAPL p. 96-97)
--=============================================================

-- First, prove the canonical forms lemma (lemma 8.3.1):
canonical-forms-bool : {t : Term} → (IsValue t) → (t ∈ tyBool) → (t ≡ tmTrue) ⊎ (t ≡ tmFalse)
canonical-forms-bool vt d-True = left refl
canonical-forms-bool vt d-False = right refl
canonical-forms-bool (valNum ()) (d-IsZero dt)
canonical-forms-bool (valNum ()) (d-If dt dt₁ dt₂)

-- Also state and prove the canonical forms lemma for the Nat type:
-- (i.e. prove that any value of type Nat is a numeric value)
canonical-forms-nat : {t : Term} → t ∈ tyNat → IsValue t → (IsNum t)
canonical-forms-nat d-Zero _                          = numZero
canonical-forms-nat (d-Suc t_nat) (valNum (numSuc x)) = numSuc x
canonical-forms-nat (d-Pred t_nat) (valNum ())
canonical-forms-nat (d-If t_nat t_nat₁ t_nat₂) (valNum ())

-- Now you are ready to prove progress and preservation of this language.


preservation : {t t' : Term} {tyT : Type} → (t ↝ t') → (t ∈ tyT) → (t' ∈ tyT)
preservation () d-True
preservation () d-False
preservation () d-Zero
preservation (e-Suc e1) (d-Suc d1)          = d-Suc (preservation e1 d1)
preservation (e-PredSuc x) (d-Pred d1)      = proj₁ (inversion-succ d1)
preservation e-PredZero (d-Pred d1)         = d1
preservation (e-Pred e1) (d-Pred d1)        = d-Pred (preservation e1 d1)
preservation e-IsZeroZero (d-IsZero d1)     = d-True
preservation (e-IsZeroSuc x) (d-IsZero d1)  = d-False
preservation (e-IsZero e1) (d-IsZero d1)    = d-IsZero (preservation e1 d1)
preservation e-IfTrue (d-If d1 d2 d3)       = d2
preservation e-IfFalse (d-If d1 d2 d3)      = d3
preservation (e-If e1) (d-If d1 d2 d3)      = d-If (preservation e1 d1) d2 d3

-- Hint: you can use the `with` syntax to pattern match on the value of a
-- function call. For an example of how to use `with`, you can look at
-- the solution of the first exercise session.

-- Hint: you can write _ as an expression; Agda will then infer its value.
-- This is only possible when only one value would type-check (e.g. the first
-- component of a dependent pair).

progress : {tyT : Type} (t : Term) → t ∈ tyT → (IsValue t) ⊎ (Σ[ t' ∈ Term ] (t ↝ t'))
progress t d-True                    = left valTrue
progress t d-False                   = left valFalse
progress t d-Zero                    = left (valNum numZero)
progress (tmSuc t) (d-Suc d1) with progress t d1
progress (tmSuc t) (d-Suc ()) | left valTrue
progress (tmSuc t) (d-Suc ()) | left valFalse
... | left (valNum num_t)          = left (valNum (numSuc num_t))
... | (right ( t' , t↝t' ))        = right (( tmSuc t' , e-Suc t↝t' ))
progress (tmPred t) (d-Pred d1) with progress t d1
progress (tmPred t) (d-Pred ()) | left valTrue
progress (tmPred t) (d-Pred ()) | left valFalse
... | left (valNum numZero)        = right ( tmZero , e-PredZero )
progress (tmPred (tmSuc t1)) (d-Pred d1) | left (valNum (numSuc num_t)) = right ( t1 , e-PredSuc num_t )
... | (right (t' , t↝t'))                 = right ( tmPred t' , e-Pred t↝t' )
progress (tmIsZero t) (d-IsZero d1) with progress t d1
progress (tmIsZero .tmTrue) (d-IsZero ()) | left valTrue
progress (tmIsZero .tmFalse) (d-IsZero ()) | left valFalse
... | left (valNum numZero) = right (tmTrue , e-IsZeroZero)
... | left (valNum (numSuc num_t)) = right (tmFalse , e-IsZeroSuc num_t)
... | (right (t' , t↝t')) = right ((tmIsZero t') , e-IsZero t↝t')
progress (tmIf t1 t2 t3) (d-If d1 d2 d3) with progress t1 d1
... | left valTrue = right (t2 , e-IfTrue)
... | left valFalse = right (t3 , e-IfFalse)
progress (tmIf .tmZero t2 t3) (d-If () d2 d3) | left (valNum numZero)
progress (tmIf .(tmSuc _) t2 t3) (d-If () d2 d3) | left (valNum (numSuc x))
... | (right (t1' , t1↝t1')) = right (tmIf t1' t2 t3 , e-If t1↝t1')

-------------------------------------------------------
-- Challenge: Prove normalization of this calculus.

-- The following lemmas are straightforward
-- to prove in terms of their counterparts that operate on ↝ instead of ↝*,
-- and may come in handy.

preservation* : {t t' : Term} {tyT : Type} → (t ↝* t') → (t ∈ tyT) → (t' ∈ tyT)
preservation* done dt = dt
preservation* (step t↝x , x↝*t') dt = preservation* x↝*t' (preservation t↝x dt)

map* : {f : Term → Term}
  → (f↝ : {t t' : Term} → t ↝ t' → f t ↝ f t')
  → {t t' : Term} → t ↝* t' → f t ↝* f t'
map* f↝ done = done
map* f↝ (step t↝x , et*) = step f↝ t↝x , (map* f↝ et*)

step*_,_ : ∀ {t t' t''} → t ↝* t' → t' ↝* t'' → t ↝* t''
step* done , et*' = et*'
step* step t↝x , et* , et*' = step t↝x , (step* et* , et*')

--now prove normalization

normalization : ∀ {tyT} (t : Term) → t ∈ tyT → Σ[ t' ∈ Term ] ((t ↝* t') × IsValue t')
normalization t d-True = tmTrue , done , valTrue
normalization t d-False = tmFalse , done , valFalse
normalization t d-Zero = tmZero , done , valNum numZero
normalization (tmSuc t) (d-Suc dt) with normalization t dt
normalization (tmSuc .tmTrue) (d-Suc ()) | .tmTrue , done , valTrue
normalization (tmSuc .tmFalse) (d-Suc ()) | .tmFalse , done , valFalse
... | .t , done , valNum num_t = tmSuc t , done , valNum (numSuc num_t)
normalization (tmSuc t) (d-Suc dt) | .tmTrue , (step t↝x , x↝*t') , valTrue with preservation* (step t↝x , x↝*t') dt
... | ()
normalization (tmSuc t) (d-Suc dt) | .tmFalse , (step t↝x , x↝*t') , valFalse with preservation* (step t↝x , x↝*t') dt
... | ()
normalization (tmSuc t) (d-Suc dt) | t' , (step t↝x , x↝*t') , valNum x = tmSuc t' , (step e-Suc t↝x , map* e-Suc x↝*t') , valNum (numSuc x)
normalization (tmPred t) (d-Pred dt) with normalization t dt
normalization (tmPred t) (d-Pred dt) | tmTrue , t↝*t' , isVal_t' with preservation* t↝*t' dt
... | ()
normalization (tmPred t) (d-Pred dt) | tmFalse , t↝*t' , isVal_t' with preservation* t↝*t' dt
... | ()
normalization (tmPred t) (d-Pred dt) | tmIf t1 t2 t3 , t↝*t' , valNum ()
normalization (tmPred t) (d-Pred dt) | tmZero , t↝*t' , isVal_t' = tmZero , (step* map* e-Pred t↝*t' , (step e-PredZero , done)) , isVal_t'
normalization (tmPred t) (d-Pred dt) | tmSuc t'' , t↝*t' , valNum (numSuc x) = t'' , (step* map* e-Pred t↝*t' , (step e-PredSuc x , done)) , valNum x
normalization (tmPred .(tmIsZero t'')) (d-Pred ()) | tmIsZero t'' , done , isVal_t'
normalization (tmPred t) (d-Pred dt) | tmIsZero t'' , (step x , t↝*t') , valNum ()
normalization (tmPred t) (d-Pred dt) | tmPred t'' , t↝*t' , valNum ()
normalization (tmIsZero t) (d-IsZero dt) with normalization t dt
normalization (tmIsZero t) (d-IsZero dt) | tmTrue , t↝*t' , isVal_t' with preservation* t↝*t' dt
... | ()
normalization (tmIsZero t) (d-IsZero dt) | tmFalse , t↝*t' , isVal_t' with preservation* t↝*t' dt
... | ()
normalization (tmIsZero t) (d-IsZero dt) | tmIf t1 t2 t3 , t↝*t' , valNum ()
normalization (tmIsZero t) (d-IsZero dt) | tmZero , t↝*t' , isVal_t' = tmTrue , (step* map* e-IsZero t↝*t' , (step e-IsZeroZero , done)) , valTrue
normalization (tmIsZero t) (d-IsZero dt) | tmSuc t'' , t↝*t' , valNum (numSuc x) = tmFalse , (step* map* e-IsZero t↝*t' , (step e-IsZeroSuc x , done)) , valFalse
normalization (tmIsZero t) (d-IsZero dt) | tmIsZero t'' , t↝*t' , valNum ()
normalization (tmIsZero t) (d-IsZero dt) | tmPred t'' , t↝*t' , valNum ()
normalization (tmIf t1 t2 t3) (d-If dt₁ dt₂ dt₃) with normalization t1 dt₁
normalization (tmIf t1 t2 t3) (d-If dt₁ dt₂ dt₃) | tmTrue , t1↝*t1' , isVal_t1' with normalization t2 dt₂
... | t2' , t2↝*t2' , isVal_t2' = t2' , (step* map* e-If t1↝*t1' , (step e-IfTrue , t2↝*t2')) , isVal_t2'
normalization (tmIf t1 t2 t3) (d-If dt₁ dt₂ dt₃) | tmFalse , t1↝*t1' , isVal_t1' with normalization t3 dt₃
... | t3' , t3↝*t3' , isVal_t3' = t3' , (step* map* e-If t1↝*t1' , (step e-IfFalse , t3↝*t3')) , isVal_t3'
normalization (tmIf t1 t2 t3) (d-If dt₁ dt₂ dt₃) | tmIf t1' t2' t3' , t1↝*t1' , valNum ()
normalization (tmIf t1 t2 t3) (d-If dt₁ dt₂ dt₃) | tmZero , t1↝*t1' , isVal_t1' with preservation* t1↝*t1' dt₁
... | ()
normalization (tmIf t1 t2 t3) (d-If dt₁ dt₂ dt₃) | tmSuc t1' , t1↝*t1' , isVal_t1' with preservation* t1↝*t1' dt₁
... | ()
normalization (tmIf t1 t2 t3) (d-If dt₁ dt₂ dt₃) | tmIsZero t1' , t1↝*t1' , valNum ()
normalization (tmIf t1 t2 t3) (d-If dt₁ dt₂ dt₃) | tmPred t1' , t1↝*t1' , valNum ()
