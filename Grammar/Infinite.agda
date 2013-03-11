------------------------------------------------------------------------
-- Infinite grammars
------------------------------------------------------------------------

module Grammar.Infinite where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.Bool
open import Data.Char
open import Data.Empty
open import Data.List as List
open import Data.List.NonEmpty as List⁺
  using (List⁺; _∷_; _∷⁺_; head; tail)
open import Data.List.Properties as List-prop using (module List-solver)
open import Data.Maybe as Maybe
open import Data.Nat
open import Data.Product as Prod
open import Data.String as String using (String)
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Nullary

private
  module LM {A : Set} = Monoid (List.monoid A)
  open module MM {f} = RawMonadPlus (Maybe.monadPlus {f = f})
    using () renaming (_<$>_ to _<$>M_; _⊛_ to _⊛M_)

open import Utilities

------------------------------------------------------------------------
-- A simple grammar language

module Basic where

  ----------------------------------------------------------------------
  -- Simple, potentially infinite grammars

  -- These grammars are very general. Every language that can be
  -- recursively enumerated using an Agda function s : ℕ → List Char
  -- can be expressed using one of these grammars:
  -- ♯ ⟦ string (s 0) ⟧ ∣ ♯ (♯ ⟦ string (s 1) ⟧ ∣ …). (The string
  -- combinator is defined below.)
  --
  -- In practice one may want to restrict attention to, say, recursive
  -- languages. I use general grammars to illustrate that this
  -- approach to pretty-printing is not restricted to a small class of
  -- languages.

  infixl 15 _>>=_
  infixl 10 _∣_

  data Grammar : Set → Set₁ where

    -- The empty string.

    return : ∀ {A} → A → Grammar A

    -- A single, arbitrary token.

    token  : Grammar Char

    -- Monadic sequencing.

    _>>=_  : ∀ {A B} → ∞ (Grammar A) → (A → ∞ (Grammar B)) → Grammar B

    -- Symmetric choice.

    _∣_    : ∀ {A} → ∞ (Grammar A) → ∞ (Grammar A) → Grammar A

  -- Semantics of grammars (parse trees). Here x ∈ g ∙ s means that x
  -- is one of the possible results of parsing the string s using the
  -- grammar g.

  infix 4 _∈_∙_

  data _∈_∙_ : ∀ {A} → A → Grammar A → List Char → Set₁ where
    return-sem  : ∀ {A} {x : A} → x ∈ return x ∙ []
    token-sem   : ∀ {t} → t ∈ token ∙ [ t ]
    >>=-sem     : ∀ {A B} {g₁ : ∞ (Grammar A)} {g₂ : A → ∞ (Grammar B)}
                    {x y s₁ s₂} →
                  x ∈ ♭ g₁ ∙ s₁ → y ∈ ♭ (g₂ x) ∙ s₂ →
                  y ∈ g₁ >>= g₂ ∙ s₁ ++ s₂
    ∣-left-sem  : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x s} →
                  x ∈ ♭ g₁ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
    ∣-right-sem : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x s} →
                  x ∈ ♭ g₂ ∙ s → x ∈ g₁ ∣ g₂ ∙ s

  ----------------------------------------------------------------------
  -- Some grammar and semantics combinators

  -- Cast lemma.

  cast : ∀ {A} {g : Grammar A} {x s₁ s₂} →
         s₁ ≡ s₂ → x ∈ g ∙ s₁ → x ∈ g ∙ s₂
  cast refl = id

  -- Failure.

  fail : ∀ {A} → Grammar A
  fail = ♯ fail ∣ ♯ fail

  fail-sem : ∀ {A} {x : A} {s} → ¬ (x ∈ fail {A = A} ∙ s)
  fail-sem (∣-left-sem  ∈fail) = fail-sem ∈fail
  fail-sem (∣-right-sem ∈fail) = fail-sem ∈fail

  -- Map.

  infixl 20 _<$>_

  _<$>_ : ∀ {A B} → (A → B) → Grammar A → Grammar B
  f <$> g = ♯ g >>= λ x → ♯ return (f x)

  <$>-sem : ∀ {A B} {f : A → B} {g : Grammar A} {x s} →
            x ∈ g ∙ s → f x ∈ f <$> g ∙ s
  <$>-sem x∈ =
    cast (proj₂ LM.identity _)
         (>>=-sem x∈ return-sem)

  -- The empty string if the argument is true, otherwise failure.

  if-true : Bool → Grammar ⊤
  if-true true  = return tt
  if-true false = fail

  if-true-sem : tt ∈ if-true true ∙ []
  if-true-sem = return-sem

  -- A token satisfying a given predicate.

  sat : (p : Char → Bool) → Grammar Char
  sat p = ♯ token >>= λ t → ♯ (const t <$> if-true (p t))

  sat-sem : ∀ {p : Char → Bool} {t} → T (p t) →
            t ∈ sat p ∙ [ t ]
  sat-sem {p} {t} pt = >>=-sem token-sem (<$>-sem lemma)
    where
    lemma : tt ∈ if-true (p t) ∙ []
    lemma with p t | pt
    lemma | true  | _  = if-true-sem
    lemma | false | ()

  -- A specific token.

  tok : Char → Grammar Char
  tok t = sat (λ t′ → t ≟C t′)

  tok-sem : ∀ {t} → t ∈ tok t ∙ [ t ]
  tok-sem = sat-sem ≟C-refl

------------------------------------------------------------------------
-- A less minimal grammar language

mutual

  -- Grammar combinators that could be defined using the ones above.
  --
  -- There are two reasons for introducing this data type, which may
  -- seem superfluous:
  --
  -- ⑴ The function final-whitespace? below analyses the structure of
  --   a grammar, and can in some cases automatically prove a certain
  --   theorem. It is quite hard to analyse grammars defined using the
  --   higher-order bind combinator.
  --
  -- ⑵ This data type can make it easier to convince Agda's
  --   termination checker that certain infinite grammars are
  --   productive.

  infix  30 _⋆
  infixl 20 _<$>_ _⊛_ _<⊛_ _⊛>_
  infixl 15 _>>=_
  infixl 10 _∣_

  data Grammar : Set → Set₁ where

    -- The empty string.

    return : ∀ {A} → A → Grammar A

    -- A single, arbitrary token.

    token  : Grammar Char

    -- Monadic sequencing.

    _>>=_  : ∀ {c₁ c₂ A B} →
             ∞Grammar c₁ A → (A → ∞Grammar c₂ B) → Grammar B

    -- Symmetric choice.

    _∣_    : ∀ {c₁ c₂ A} → ∞Grammar c₁ A → ∞Grammar c₂ A → Grammar A

    -- Failure.

    fail   : ∀ {A} → Grammar A

    -- A specific token.

    tok    : Char → Grammar Char

    -- Map.

    _<$>_  : ∀ {c A B} → (A → B) → ∞Grammar c A → Grammar B

    -- Applicative sequencing.

    _⊛_    : ∀ {c₁ c₂ A B} →
             ∞Grammar c₁ (A → B) → ∞Grammar c₂ A → Grammar B
    _<⊛_   : ∀ {c₁ c₂ A B} → ∞Grammar c₁ A → ∞Grammar c₂ B → Grammar A
    _⊛>_   : ∀ {c₁ c₂ A B} → ∞Grammar c₁ A → ∞Grammar c₂ B → Grammar B

    -- Kleene star.

    _⋆     : ∀ {c A} → ∞Grammar c A → Grammar (List A)

  -- Coinductive if the argument is true.

  ∞Grammar : Bool → Set → Set₁
  ∞Grammar true  A = ∞ (Grammar A)
  ∞Grammar false A =    Grammar A

-- Families of grammars for specific values.

Grammar-for : Set → Set₁
Grammar-for A = (x : A) → Grammar (∃ λ x′ → x′ ≡ x)

-- Forcing of a conditionally coinductive grammar.

♭? : ∀ {c A} → ∞Grammar c A → Grammar A
♭? {true}  = ♭
♭? {false} = id

-- The semantics of "extended" grammars is given by translation to
-- simple grammars.

⟦_⟧ : ∀ {A} → Grammar A → Basic.Grammar A
⟦ return x  ⟧ = Basic.return x
⟦ token     ⟧ = Basic.token
⟦ g₁ >>= g₂ ⟧ = ♯ ⟦ ♭? g₁ ⟧ Basic.>>= λ x → ♯ ⟦ ♭? (g₂ x) ⟧
⟦ g₁ ∣ g₂   ⟧ = ♯ ⟦ ♭? g₁ ⟧ Basic.∣ ♯ ⟦ ♭? g₂ ⟧
⟦ fail      ⟧ = Basic.fail
⟦ tok t     ⟧ = Basic.tok t
⟦ f <$> g   ⟧ = ♯ ⟦ ♭? g ⟧ Basic.>>= λ x → ♯ Basic.return (f x)
⟦ g₁ ⊛ g₂   ⟧ =    ♯ ⟦ ♭? g₁ ⟧ Basic.>>= λ f →
                ♯ (♯ ⟦ ♭? g₂ ⟧ Basic.>>= λ x →
                   ♯ Basic.return (f x))
⟦ g₁ <⊛ g₂  ⟧ =    ♯ ⟦ ♭? g₁ ⟧ Basic.>>= λ x →
                ♯ (♯ ⟦ ♭? g₂ ⟧ Basic.>>= λ _ →
                   ♯ Basic.return x)
⟦ g₁ ⊛> g₂  ⟧ =    ♯ ⟦ ♭? g₁ ⟧ Basic.>>= λ _ →
                ♯ (♯ ⟦ ♭? g₂ ⟧ Basic.>>= λ x →
                   ♯ Basic.return x)
⟦ g ⋆       ⟧ =   ♯ Basic.return []
                Basic.∣
                  ♯ (♯ ⟦ ♭? g ⟧ Basic.>>= λ x →
                  ♯ (♯ ⟦ g ⋆  ⟧ Basic.>>= λ xs →
                     ♯ Basic.return (x ∷ xs)))

infix 4 _∈_∙_

_∈_∙_ : ∀ {A} → A → Grammar A → List Char → Set₁
x ∈ g ∙ s = x Basic.∈ ⟦ g ⟧ ∙ s

------------------------------------------------------------------------
-- Grammar combinators

-- The result of _<$_ always returns the same result.

infixr 20 _<$_

_<$_ : ∀ {A B} → A → Grammar B → Grammar A
x <$ g = return x <⊛ g

-- Kleene plus.

infix 30 _+

_+ : ∀ {c A} → ∞Grammar c A → Grammar (List⁺ A)
p + = _∷_ <$> p ⊛ p ⋆

mutual

  -- Combinators that transform families of grammars for certain
  -- elements to families of grammars for certain lists.

  list : ∀ {A} → Grammar-for A → Grammar-for (List A)
  list elem []       = return ([] , refl)
  list elem (x ∷ xs) =
    Prod.map List⁺.toList
             (λ eq → P.cong₂ _∷_ (P.cong head eq) (P.cong tail eq)) <$>
      list⁺ elem (x ∷ xs)

  list⁺ : ∀ {A} → Grammar-for A → Grammar-for (List⁺ A)
  list⁺ elem (x ∷ xs) =
    Prod.zip _∷_ (P.cong₂ _∷_) <$> elem x ⊛ list elem xs

-- Elements preceded by something.

infixl 18 _prec-by_

_prec-by_ : ∀ {A B} → Grammar A → Grammar B → Grammar (List A)
g prec-by prec = (prec ⊛> g) ⋆

-- Elements separated by something.

infixl 18 _sep-by_

_sep-by_ : ∀ {A B} → Grammar A → Grammar B → Grammar (List⁺ A)
g sep-by sep = _∷_ <$> g ⊛ (g prec-by sep)

-- The empty string if the argument is true, otherwise failure.

if-true : (b : Bool) → Grammar (T b)
if-true true  = return tt
if-true false = fail

-- A token satisfying a given predicate.

sat : (p : Char → Bool) → Grammar (∃ λ t → T (p t))
sat p = token >>= λ t → _,_ t <$> if-true (p t)

-- A given token satisfying a given predicate.

tok-sat : (p : Char → Bool) → Grammar-for (∃ (T ∘ p))
tok-sat p (t , pt) = ((t , pt) , refl) <$ tok t

-- Whitespace.

whitespace : Grammar Char
whitespace = tok ' ' ∣ tok '\n'

-- The given string.

string : List Char → Grammar (List Char)
string []      = return []
string (t ∷ s) = _∷_ <$> tok t ⊛ string s

string′ : String → Grammar (List Char)
string′ = string ∘ String.toList

-- The given string, possibly followed by some whitespace.

symbol : List Char → Grammar (List Char)
symbol s = string s <⊛ whitespace ⋆

symbol′ : String → Grammar (List Char)
symbol′ = symbol ∘ String.toList

------------------------------------------------------------------------
-- Semantics combinators

open Basic public
  using (cast; return-sem; token-sem; >>=-sem;
         ∣-left-sem; ∣-right-sem; fail-sem; tok-sem)

<$>-sem : ∀ {c A B} {f : A → B} {g : ∞Grammar c A} {x s} →
          x ∈ ♭? g ∙ s → f x ∈ f <$> g ∙ s
<$>-sem x∈ =
  cast (proj₂ LM.identity _)
       (>>=-sem x∈ return-sem)

⊛-sem : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ (A → B)} {g₂ : ∞Grammar c₂ A}
          {f x s₁ s₂} →
        f ∈ ♭? g₁ ∙ s₁ → x ∈ ♭? g₂ ∙ s₂ → f x ∈ g₁ ⊛ g₂ ∙ s₁ ++ s₂
⊛-sem {s₁ = s₁} f∈ x∈ =
  cast (solve 2 (λ a b → a ⊕ b ⊕ nil ⊜ a ⊕ b) refl s₁ _)
             (>>=-sem f∈ (>>=-sem x∈ return-sem))
  where open List-solver

<⊛-sem : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B}
           {x y s₁ s₂} →
         x ∈ ♭? g₁ ∙ s₁ → y ∈ ♭? g₂ ∙ s₂ → x ∈ g₁ <⊛ g₂ ∙ s₁ ++ s₂
<⊛-sem {s₁ = s₁} x∈ y∈ =
  cast (solve 2 (λ a b → a ⊕ b ⊕ nil ⊜ a ⊕ b) refl s₁ _)
             (>>=-sem x∈ (>>=-sem y∈ return-sem))
  where open List-solver

⊛>-sem : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B}
           {x y s₁ s₂} →
         x ∈ ♭? g₁ ∙ s₁ → y ∈ ♭? g₂ ∙ s₂ → y ∈ g₁ ⊛> g₂ ∙ s₁ ++ s₂
⊛>-sem {s₁ = s₁} x∈ y∈ =
  cast (solve 2 (λ a b → a ⊕ b ⊕ nil ⊜ a ⊕ b) refl s₁ _)
             (>>=-sem x∈ (>>=-sem y∈ return-sem))
  where open List-solver

<$-sem : ∀ {A B} {x : A} {y : B} {g s} →
         y ∈ g ∙ s → x ∈ x <$ g ∙ s
<$-sem y∈ = <⊛-sem return-sem y∈

⋆-[]-sem : ∀ {c A} {g : ∞Grammar c A} →
           [] ∈ g ⋆ ∙ []
⋆-[]-sem = ∣-left-sem return-sem

⋆-+-sem : ∀ {c A} {g : ∞Grammar c A} {x xs s} →
          (x ∷ xs) ∈ g + ∙ s → x ∷ xs ∈ g ⋆ ∙ s
⋆-+-sem (>>=-sem (>>=-sem x∈ return-sem)
                       (>>=-sem xs∈ return-sem)) =
  ∣-right-sem
    (>>=-sem (cast (P.sym $ proj₂ LM.identity _) x∈)
                   (>>=-sem xs∈ return-sem))

+-sem : ∀ {c A} {g : ∞Grammar c A} {x xs s₁ s₂} →
        x ∈ ♭? g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → (x ∷ xs) ∈ g + ∙ s₁ ++ s₂
+-sem x∈ xs∈ = ⊛-sem (<$>-sem x∈) xs∈

⋆-∷-sem : ∀ {c A} {g : ∞Grammar c A} {x xs s₁ s₂} →
          x ∈ ♭? g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → x ∷ xs ∈ g ⋆ ∙ s₁ ++ s₂
⋆-∷-sem x∈ xs∈ = ⋆-+-sem (+-sem x∈ xs∈)

⋆-⋆-sem : ∀ {c A} {g : ∞Grammar c A} {xs₁ xs₂ s₁ s₂} →
          xs₁ ∈ g ⋆ ∙ s₁ → xs₂ ∈ g ⋆ ∙ s₂ → xs₁ ++ xs₂ ∈ g ⋆ ∙ s₁ ++ s₂
⋆-⋆-sem (∣-left-sem return-sem)                      xs₂∈ = xs₂∈
⋆-⋆-sem (∣-right-sem (>>=-sem {s₁ = s₁} x∈
                              (>>=-sem {s₁ = s₂} xs₁∈
                                       return-sem))) xs₂∈ =
  cast (solve 3 (λ a b c → a ⊕ b ⊕ c ⊜ (a ⊕ b ⊕ nil) ⊕ c) refl s₁ s₂ _)
       (⋆-∷-sem x∈ (⋆-⋆-sem xs₁∈ xs₂∈))
  where open List-solver

+-∷-sem : ∀ {c A} {g : ∞Grammar c A} {x xs s₁ s₂} →
          x ∈ ♭? g ∙ s₁ → xs ∈ g + ∙ s₂ → x ∷⁺ xs ∈ g + ∙ s₁ ++ s₂
+-∷-sem x∈ xs∈ = +-sem x∈ (⋆-+-sem xs∈)

mutual

  list-sem : ∀ {A} {g : Grammar-for A} {s : A → List Char} →
             (∀ x → (x , refl) ∈ g x ∙ s x) →
             ∀ xs → (xs , refl) ∈ list g xs ∙ concat (List.map s xs)
  list-sem         elem []       = return-sem
  list-sem {g = g} elem (x ∷ xs) = <$>-sem (list⁺-sem g elem (x ∷ xs))

  list⁺-sem :
    ∀ {A} (g : Grammar-for A) {s : A → List Char} →
    (∀ x → (x , refl) ∈ g x ∙ s x) →
    ∀ xs → (xs , refl) ∈ list⁺ g xs ∙
           concat (List.map s (List⁺.toList xs))
  list⁺-sem _ elem (x ∷ xs) =
    ⊛-sem (<$>-sem (elem x)) (list-sem elem xs)

sep-by-sem-singleton :
  ∀ {A B} {g : Grammar A} {sep : Grammar B} {x s} →
  x ∈ g ∙ s → x ∷ [] ∈ g sep-by sep ∙ s
sep-by-sem-singleton x∈ =
  cast (proj₂ LM.identity _)
             (⊛-sem (<$>-sem x∈) ⋆-[]-sem)

sep-by-sem-∷ :
  ∀ {A B} {g : Grammar A} {sep : Grammar B} {x y xs s₁ s₂ s₃} →
  x ∈ g ∙ s₁ → y ∈ sep ∙ s₂ → xs ∈ g sep-by sep ∙ s₃ →
  x ∷⁺ xs ∈ g sep-by sep ∙ s₁ ++ s₂ ++ s₃
sep-by-sem-∷
  {s₁ = s₁} {s₂} x∈ y∈
  (>>=-sem (>>=-sem x′∈ return-sem) (>>=-sem xs∈ return-sem)) =
  cast (solve 4 (λ a b c d → a ⊕ (b ⊕ c) ⊕ d ⊜
                             a ⊕ b ⊕ (c ⊕ nil) ⊕ d ⊕ nil)
                refl s₁ s₂ _ _)
       (⊛-sem (<$>-sem x∈) (⋆-∷-sem (⊛>-sem y∈ x′∈) xs∈))
  where open List-solver

if-true-sem : ∀ {b} (t : T b) → t ∈ if-true b ∙ []
if-true-sem {b = true}  _  = return-sem
if-true-sem {b = false} ()

sat-sem : ∀ {p : Char → Bool} {t} (pt : T (p t)) →
          (t , pt) ∈ sat p ∙ [ t ]
sat-sem pt = >>=-sem token-sem (<$>-sem (if-true-sem pt))

tok-sat-sem : ∀ {p : Char → Bool} {t} (pt : T (p t)) →
              ((t , pt) , refl) ∈ tok-sat p (t , pt) ∙ [ t ]
tok-sat-sem _ = <$-sem tok-sem

list-sem-lemma : ∀ {A} {x : A} {g s} →
                 x ∈ g ∙ concat (List.map [_] s) → x ∈ g ∙ s
list-sem-lemma = cast (List-prop.Monad.right-identity _)

single-space-sem : (' ' ∷ []) ∈ whitespace + ∙ String.toList " "
single-space-sem = +-sem (∣-left-sem tok-sem) ⋆-[]-sem

string-sem : ∀ {s} → s ∈ string s ∙ s
string-sem {s = []}    = return-sem
string-sem {s = t ∷ s} = ⊛-sem (<$>-sem tok-sem) string-sem

------------------------------------------------------------------------
-- Detecting the whitespace combinator

-- A predicate for the whitespace combinator.

data Is-whitespace : ∀ {A} → Grammar A → Set₁ where
  is-whitespace : Is-whitespace whitespace

-- Detects the whitespace combinator.

is-whitespace? : ∀ {A} (g : Grammar A) → Maybe (Is-whitespace g)
is-whitespace? (_∣_ {c₁ = false} {c₂ = false} (tok ' ') g) =
  helper _ refl
  where
  helper : ∀ {A} (g : Grammar A) (eq : A ≡ Char) →
           Maybe (Is-whitespace (tok ' ' ∣ P.subst Grammar eq g))
  helper (tok '\n') refl = just is-whitespace
  helper _          _    = nothing

is-whitespace? _ = nothing

------------------------------------------------------------------------
-- Final whitespace

-- A predicate for grammars that can "swallow" extra whitespace at the
-- end.

Final-whitespace : ∀ {A} → Grammar A → Set₁
Final-whitespace g =
  ∀ {x s₁ s₂ s} →
  x ∈ g ∙ s₁ → s ∈ whitespace ⋆ ∙ s₂ → x ∈ g ∙ s₁ ++ s₂

-- A similar but weaker property.

Final-whitespace′ : ∀ {A} → Grammar A → Set₁
Final-whitespace′ g =
  ∀ {x s₁ s₂ s} →
  x ∈ g ∙ s₁ → s ∈ whitespace ⋆ ∙ s₂ → ∃ λ y → y ∈ g ∙ s₁ ++ s₂

-- A heuristic (and rather incomplete) procedure that either proves
-- that a production can swallow final whitespace (in the weaker
-- sense), or returns "don't know" as the answer.
--
-- The natural number n is used to ensure termination.

final-whitespace′? : ∀ (n : ℕ) {A} (g : Grammar A) →
                     Maybe (Final-whitespace′ g)
final-whitespace′? = final?
  where
  open List-solver

  ++-lemma = solve 3 (λ a b c → a ⊕ b ⊕ c ⊜ (a ⊕ b ⊕ nil) ⊕ c) refl

  <$>-lemma : ∀ {c A B} {f : A → B} {g : ∞Grammar c A} →
              Final-whitespace′ (♭? g) →
              Final-whitespace′ (f <$> g)
  <$>-lemma f (>>=-sem {s₁ = s₁} x∈ return-sem) w =
    , cast (solve 2 (λ a b → a ⊕ b ⊜ (a ⊕ nil) ⊕ b) refl s₁ _)
           (<$>-sem (proj₂ $ f x∈ w))

  ⊛-lemma : ∀ {c₁ c₂ A B}
              {g₁ : ∞Grammar c₁ (A → B)} {g₂ : ∞Grammar c₂ A} →
            Final-whitespace′ (♭? g₂) →
            Final-whitespace′ (g₁ ⊛ g₂)
  ⊛-lemma f₂ (>>=-sem {s₁ = s₁} f∈
                      (>>=-sem {s₁ = s₂} x∈ return-sem)) w =
    , cast (++-lemma s₁ s₂ _)
           (⊛-sem f∈ (proj₂ $ f₂ x∈ w))

  <⊛-lemma : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
             Final-whitespace′ (♭? g₂) →
             Final-whitespace′ (g₁ <⊛ g₂)
  <⊛-lemma f₂ (>>=-sem {s₁ = s₁} x∈
                       (>>=-sem {s₁ = s₂} y∈ return-sem)) w =
    , cast (++-lemma s₁ s₂ _)
           (<⊛-sem x∈ (proj₂ $ f₂ y∈ w))

  ⊛>-lemma : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
             Final-whitespace′ (♭? g₂) →
             Final-whitespace′ (g₁ ⊛> g₂)
  ⊛>-lemma f₂ (>>=-sem {s₁ = s₁} x∈
                       (>>=-sem {s₁ = s₂} y∈ return-sem)) w =
    , cast (++-lemma s₁ s₂ _)
           (⊛>-sem x∈ (proj₂ $ f₂ y∈ w))

  ∣-lemma : ∀ {c₁ c₂ A} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ A} →
            Final-whitespace′ (♭? g₁) →
            Final-whitespace′ (♭? g₂) →
            Final-whitespace′ (g₁ ∣ g₂)
  ∣-lemma f₁ f₂ (∣-left-sem  x∈) w = , ∣-left-sem  (proj₂ $ f₁ x∈ w)
  ∣-lemma f₁ f₂ (∣-right-sem x∈) w = , ∣-right-sem (proj₂ $ f₂ x∈ w)

  whitespace⋆-lemma :
    ∀ {A} {g : Grammar A} →
    Is-whitespace g →
    Final-whitespace′ (g ⋆)
  whitespace⋆-lemma is-whitespace xs∈ w = , ⋆-⋆-sem xs∈ w

  final? : ℕ → ∀ {A} (g : Grammar A) → Maybe (Final-whitespace′ g)
  final? (suc n) fail               = just (⊥-elim ∘ fail-sem)
  final? (suc n) (f <$> g)          = <$>-lemma <$>M final? n (♭? g)
  final? (suc n) (g₁ ⊛ g₂)          = ⊛-lemma   <$>M final? n (♭? g₂)
  final? (suc n) (g₁ <⊛ g₂)         = <⊛-lemma  <$>M final? n (♭? g₂)
  final? (suc n) (g₁ ⊛> g₂)         = ⊛>-lemma  <$>M final? n (♭? g₂)
  final? (suc n) (g₁ ∣ g₂)          = ∣-lemma   <$>M final? n (♭? g₁)
                                                  ⊛M final? n (♭? g₂)
  final? (suc n) (_⋆ {c = false} g) = whitespace⋆-lemma <$>M
                                        is-whitespace? g
  final? _       _                  = nothing

-- A heuristic (and rather incomplete) procedure that either proves
-- that a production can swallow final whitespace, or returns "don't
-- know" as the answer.
--
-- The natural number n is used to ensure termination.

final-whitespace? : ∀ (n : ℕ) {A} (g : Grammar A) →
                    Maybe (Final-whitespace g)
final-whitespace? = final?
  where
  open List-solver

  ++-lemma  = solve 3 (λ a b c → a ⊕ b ⊕ c ⊜ (a ⊕ b ⊕ nil) ⊕ c) refl
  ++-lemma₁ = solve 2 (λ a b → (a ⊕ b) ⊕ nil ⊜ (a ⊕ nil) ⊕ b) refl
  ++-lemma₂ = solve 3 (λ a b c → (a ⊕ b ⊕ nil) ⊕ c ⊜ (a ⊕ b) ⊕ c) refl
  ++-lemma₃ = solve 2 (λ a b → a ⊕ b ⊜ a ⊕ b ⊕ nil) refl

  <$>-lemma : ∀ {c A B} {f : A → B} {g : ∞Grammar c A} →
              Final-whitespace (♭? g) →
              Final-whitespace (f <$> g)
  <$>-lemma f (>>=-sem {s₁ = s₁} x∈ return-sem) w =
    cast (solve 2 (λ a b → a ⊕ b ⊜ (a ⊕ nil) ⊕ b) refl s₁ _)
         (<$>-sem (f x∈ w))

  ⊛-return-lemma :
    ∀ {c A B} {g : ∞Grammar c (A → B)} {x} →
    Final-whitespace (♭? g) →
    Final-whitespace (g ⊛ return x)
  ⊛-return-lemma f (>>=-sem {s₁ = s₁}
                            f∈ (>>=-sem return-sem return-sem)) w =
    cast (++-lemma₁ s₁ _)
         (⊛-sem (f f∈ w) return-sem)

  +-lemma :
    ∀ {c A} {g : ∞Grammar c A} →
    Final-whitespace (♭? g) →
    ∀ {x xs s₁ s₂ s₃ s} →
    x ∈ ♭? g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → s ∈ whitespace ⋆ ∙ s₃ →
    x ∷ xs ∈ g ⋆ ∙ s₁ ++ s₂ ++ s₃
  +-lemma f x∈ (∣-left-sem return-sem) w =
    cast (proj₂ LM.identity _)
         (⋆-∷-sem (f x∈ w) ⋆-[]-sem)
  +-lemma f {s₁ = s₁} x∈
          (∣-right-sem (>>=-sem {s₁ = s₂} x′∈
                                (>>=-sem {s₁ = s₃} xs∈ return-sem))) w =
    cast (solve 4 (λ a b c d → a ⊕ b ⊕ c ⊕ d ⊜ a ⊕ (b ⊕ c ⊕ nil) ⊕ d)
                  refl s₁ s₂ s₃ _)
         (⋆-∷-sem x∈ (+-lemma f x′∈ xs∈ w))

  ⊛-⋆-lemma :
    ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ (List A → B)} {g₂ : ∞Grammar c₂ A} →
    Final-whitespace (♭? g₁) →
    Final-whitespace (♭? g₂) →
    Final-whitespace (g₁ ⊛ g₂ ⋆)
  ⊛-⋆-lemma f₁ f₂ (>>=-sem {s₁ = s₁} f∈
                     (>>=-sem (∣-left-sem return-sem) return-sem)) w =
    cast (++-lemma₁ s₁ _)
         (⊛-sem (f₁ f∈ w) ⋆-[]-sem)
  ⊛-⋆-lemma f₁ f₂ (>>=-sem {s₁ = s₁} f∈
                     (>>=-sem
                        (∣-right-sem (>>=-sem {s₁ = s₂} x∈
                                        (>>=-sem {s₁ = s₃} xs∈
                                                 return-sem)))
                        return-sem)) w =
    cast (solve 4 (λ a b c d → a ⊕ b ⊕ c ⊕ d ⊜
                               (a ⊕ (b ⊕ c ⊕ nil) ⊕ nil) ⊕ d)
                  refl s₁ s₂ s₃ _)
         (⊛-sem f∈ (+-lemma f₂ x∈ xs∈ w))

  ⊛-∣-lemma : ∀ {c₁ c₂₁ c₂₂ A B} {g₁ : ∞Grammar c₁ (A → B)}
                {g₂₁ : ∞Grammar c₂₁ A} {g₂₂ : ∞Grammar c₂₂ A} →
              Final-whitespace (g₁ ⊛ g₂₁) →
              Final-whitespace (g₁ ⊛ g₂₂) →
              Final-whitespace (g₁ ⊛ (g₂₁ ∣ g₂₂))
  ⊛-∣-lemma f₁₂ f₁₃ {s₂ = s₃}
            (>>=-sem {x = f} {s₁ = s₁} f∈
                     (>>=-sem {x = x} {s₁ = s₂}
                              (∣-left-sem x∈) return-sem)) w
    rewrite ++-lemma₂ s₁ s₂ s₃
    with f x | (s₁ ++ s₂) ++ s₃ | f₁₂ (⊛-sem f∈ x∈) w
  ... | ._ | ._ | >>=-sem {s₁ = s₁′} f∈′ (>>=-sem x∈′ return-sem) =
    cast (++-lemma₃ s₁′ _)
         (⊛-sem f∈′ (∣-left-sem x∈′))
  ⊛-∣-lemma f₁₂ f₁₃ {s₂ = s₃}
            (>>=-sem {x = f} {s₁ = s₁} f∈
                     (>>=-sem {x = x} {s₁ = s₂}
                              (∣-right-sem x∈) return-sem)) w
    rewrite ++-lemma₂ s₁ s₂ s₃
    with f x | (s₁ ++ s₂) ++ s₃ | f₁₃ (⊛-sem f∈ x∈) w
  ... | ._ | ._ | >>=-sem {s₁ = s₁′} f∈′ (>>=-sem x∈′ return-sem) =
    cast (++-lemma₃ s₁′ _)
         (⊛-sem f∈′ (∣-right-sem x∈′))

  ⊛-lemma : ∀ {c₁ c₂ A B}
              {g₁ : ∞Grammar c₁ (A → B)} {g₂ : ∞Grammar c₂ A} →
            Final-whitespace (♭? g₂) →
            Final-whitespace (g₁ ⊛ g₂)
  ⊛-lemma f₂ (>>=-sem {s₁ = s₁} f∈
                      (>>=-sem {s₁ = s₂} x∈ return-sem)) w =
    cast (solve 3 (λ a b c → a ⊕ b ⊕ c ⊜ (a ⊕ b ⊕ nil) ⊕ c)
                  refl s₁ s₂ _)
         (⊛-sem f∈ (f₂ x∈ w))

  <⊛-return-lemma :
    ∀ {c A B} {g : ∞Grammar c A} {x : B} →
    Final-whitespace (♭? g) →
    Final-whitespace (g <⊛ return x)
  <⊛-return-lemma f (>>=-sem {s₁ = s} y∈
                             (>>=-sem return-sem return-sem)) w =
    cast (solve 2 (λ a b → (a ⊕ b) ⊕ nil ⊜ (a ⊕ nil) ⊕ b) refl s _)
         (<⊛-sem (f y∈ w) return-sem)

  <⊛-lemma : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
             Final-whitespace′ (♭? g₂) →
             Final-whitespace (g₁ <⊛ g₂)
  <⊛-lemma f₂ (>>=-sem {s₁ = s₁} x∈
                       (>>=-sem {s₁ = s₂} y∈ return-sem)) w =
    cast (++-lemma s₁ s₂ _)
         (<⊛-sem x∈ (proj₂ $ f₂ y∈ w))

  ⊛>-lemma : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
             Final-whitespace (♭? g₂) →
             Final-whitespace (g₁ ⊛> g₂)
  ⊛>-lemma f₂ (>>=-sem {s₁ = s₁} x∈
                       (>>=-sem {s₁ = s₂} y∈ return-sem)) w =
    cast (++-lemma s₁ s₂ _)
         (⊛>-sem x∈ (f₂ y∈ w))

  ∣-lemma : ∀ {c₁ c₂ A} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ A} →
            Final-whitespace (♭? g₁) →
            Final-whitespace (♭? g₂) →
            Final-whitespace (g₁ ∣ g₂)
  ∣-lemma f₁ f₂ (∣-left-sem  x∈) w = ∣-left-sem  (f₁ x∈ w)
  ∣-lemma f₁ f₂ (∣-right-sem x∈) w = ∣-right-sem (f₂ x∈ w)

  final? : ℕ → ∀ {A} (g : Grammar A) → Maybe (Final-whitespace g)

  final? (suc n) fail = just (⊥-elim ∘ fail-sem)

  final? (suc n) (f <$> g) = <$>-lemma <$>M final? n (♭? g)

  final? (suc n) (_⊛_ {c₂ = false} g  (return x))  = ⊛-return-lemma <$>M final? n (♭? g)
  final? (suc n) (_⊛_ {c₂ = false} g₁ (g₂ ⋆))      = ⊛-⋆-lemma      <$>M final? n (♭? g₁)
                                                                      ⊛M final? n (♭? g₂)
  final? (suc n) (_⊛_ {c₂ = false} g₁ (g₂₁ ∣ g₂₂)) = ⊛-∣-lemma      <$>M final? n (g₁ ⊛ g₂₁)
                                                                      ⊛M final? n (g₁ ⊛ g₂₂)
  final? (suc n) (_⊛_              g₁ g₂)          = ⊛-lemma        <$>M final? n (♭? g₂)

  final? (suc n) (_<⊛_ {c₂ = false} g  (return x)) = <⊛-return-lemma <$>M final? n (♭? g)
  final? (suc n) (_<⊛_              g₁ g₂)         = <⊛-lemma <$>M
                                                       final-whitespace′? (suc n) (♭? g₂)

  final? (suc n) (g₁ ⊛> g₂) = ⊛>-lemma <$>M final? n (♭? g₂)

  final? (suc n) (g₁ ∣ g₂) = ∣-lemma <$>M final? n (♭? g₁)
                                       ⊛M final? n (♭? g₂)

  final? _ _ = nothing

private

  -- Some unit tests.

  test₁ : IsJust (final-whitespace′? 1 (whitespace ⋆))
  test₁ = _

  test₂ : IsJust (final-whitespace′? 2 (whitespace +))
  test₂ = _

  test₃ : IsJust (final-whitespace? 1 (tt <$ whitespace ⋆))
  test₃ = _

  test₄ : IsJust (final-whitespace? 2 (tt <$ whitespace +))
  test₄ = _
