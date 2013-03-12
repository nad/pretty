------------------------------------------------------------------------
-- Infinite grammars
------------------------------------------------------------------------

-- The grammar language introduced below is not more expressive than
-- the one in Grammar.Infinite.Basic. There are two reasons for
-- introducing this new language:
--
-- ⑴ The function final-whitespace? below analyses the structure of
--   a grammar, and can in some cases automatically prove a certain
--   theorem. It is quite hard to analyse grammars defined using the
--   higher-order bind combinator.
--
-- ⑵ The new language can make it easier to convince Agda's
--   termination checker that certain infinite grammars are
--   productive.

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

private
  module LM {A : Set} = Monoid (List.monoid A)
  open module MM {f} = RawMonadPlus (Maybe.monadPlus {f = f})
    using () renaming (_<$>_ to _<$>M_; _⊛_ to _⊛M_)

import Grammar.Infinite.Basic as Basic; open Basic._∈_∙_
open import Utilities

------------------------------------------------------------------------
-- A grammar language that is less minimal than the one in
-- Grammar.Infinite.Basic

mutual

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
  --
  -- Conditional coinduction is used to avoid having to write the
  -- delay operator (♯_) all the time.

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

------------------------------------------------------------------------
-- Grammar combinators

-- The result of _<$_ always returns the same result.

infixr 20 _<$_

_<$_ : ∀ {A B} → A → Grammar B → Grammar A
x <$ g = return x <⊛ g

-- Kleene plus.

infix 30 _+

_+ : ∀ {c A} → ∞Grammar c A → Grammar (List⁺ A)
g + = _∷_ <$> g ⊛ g ⋆

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
-- Alternative definition of the semantics

-- Pattern matching on values of type x Basic.∈ ⟦ g₁ ⊛ g₂ ⟧ ∙ s (say)
-- is somewhat inconvenient: the patterns have the form
-- (>>=-sem _ (>>=-sem _ return-sem)). The following, direct
-- definition of the semantics may be easier to use.

infix 4 _∈_∙_

data _∈_∙_ : ∀ {A} → A → Grammar A → List Char → Set₁ where
  return-sem  : ∀ {A} {x : A} → x ∈ return x ∙ []
  token-sem   : ∀ {t} → t ∈ token ∙ [ t ]
  >>=-sem     : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A}
                  {g₂ : A → ∞Grammar c₂ B} {x y s₁ s₂} →
                x ∈ ♭? g₁ ∙ s₁ → y ∈ ♭? (g₂ x) ∙ s₂ →
                y ∈ g₁ >>= g₂ ∙ s₁ ++ s₂
  ∣-left-sem  : ∀ {c₁ c₂ A} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ A}
                  {x s} →
                x ∈ ♭? g₁ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  ∣-right-sem : ∀ {c₁ c₂ A} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ A}
                  {x s} →
                x ∈ ♭? g₂ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  tok-sem     : ∀ {t} → t ∈ tok t ∙ [ t ]
  <$>-sem     : ∀ {c A B} {f : A → B} {g : ∞Grammar c A} {x s} →
                x ∈ ♭? g ∙ s → f x ∈ f <$> g ∙ s
  ⊛-sem       : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ (A → B)}
                  {g₂ : ∞Grammar c₂ A} {f x s₁ s₂} →
                f ∈ ♭? g₁ ∙ s₁ → x ∈ ♭? g₂ ∙ s₂ →
                f x ∈ g₁ ⊛ g₂ ∙ s₁ ++ s₂
  <⊛-sem      : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B}
                  {x y s₁ s₂} →
                x ∈ ♭? g₁ ∙ s₁ → y ∈ ♭? g₂ ∙ s₂ →
                x ∈ g₁ <⊛ g₂ ∙ s₁ ++ s₂
  ⊛>-sem      : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B}
                  {x y s₁ s₂} →
                x ∈ ♭? g₁ ∙ s₁ → y ∈ ♭? g₂ ∙ s₂ →
                y ∈ g₁ ⊛> g₂ ∙ s₁ ++ s₂
  ⋆-[]-sem    : ∀ {c A} {g : ∞Grammar c A} →
                [] ∈ g ⋆ ∙ []
  ⋆-+-sem     : ∀ {c A} {g : ∞Grammar c A} {x xs s} →
                (x ∷ xs) ∈ g + ∙ s → x ∷ xs ∈ g ⋆ ∙ s

-- Cast lemma.

cast : ∀ {A} {g : Grammar A} {x s₁ s₂} →
       s₁ ≡ s₂ → x ∈ g ∙ s₁ → x ∈ g ∙ s₂
cast refl = id

-- The alternative semantics is sound with respect to the one above.

sound : ∀ {A x s} {g : Grammar A} → x ∈ g ∙ s → x Basic.∈ ⟦ g ⟧ ∙ s
sound return-sem       = return-sem
sound token-sem        = token-sem
sound (>>=-sem x∈ y∈)  = >>=-sem (sound x∈) (sound y∈)
sound (∣-left-sem x∈)  = ∣-left-sem (sound x∈)
sound (∣-right-sem x∈) = ∣-right-sem (sound x∈)
sound tok-sem          = Basic.tok-sem
sound (<$>-sem x∈)     = Basic.cast (proj₂ LM.identity _)
                           (>>=-sem (sound x∈) return-sem)
sound (⊛-sem f∈ x∈)    = >>=-sem
                           (sound f∈)
                           (Basic.cast (proj₂ LM.identity _)
                              (>>=-sem (sound x∈)
                                             return-sem))
sound (<⊛-sem x∈ y∈)   = >>=-sem
                           (sound x∈)
                           (Basic.cast (proj₂ LM.identity _)
                              (>>=-sem (sound y∈)
                                             return-sem))
sound (⊛>-sem x∈ y∈)   = >>=-sem
                           (sound x∈)
                           (Basic.cast (proj₂ LM.identity _)
                              (>>=-sem (sound y∈)
                                             return-sem))
sound ⋆-[]-sem         = ∣-left-sem return-sem
sound (⋆-+-sem xs∈)    with sound xs∈
... | >>=-sem (>>=-sem x∈ return-sem)
                    (>>=-sem xs∈′ return-sem) =
  ∣-right-sem
    (>>=-sem (Basic.cast (P.sym $ proj₂ LM.identity _) x∈)
                   (>>=-sem xs∈′ return-sem))

-- The alternative semantics is complete with respect to the one above.

complete : ∀ {A x s} {g : Grammar A} → x Basic.∈ ⟦ g ⟧ ∙ s → x ∈ g ∙ s
complete {g = return x}  return-sem       = return-sem
complete {g = token}     token-sem        = token-sem
complete {g = g₁ >>= g₂} (>>=-sem x∈ y∈)  = >>=-sem (complete x∈)
                                                    (complete y∈)
complete {g = g₁ ∣ g₂}   (∣-left-sem x∈)  = ∣-left-sem (complete x∈)
complete {g = g₁ ∣ g₂}   (∣-right-sem x∈) = ∣-right-sem (complete x∈)

complete {g = fail}  ∈fail = ⊥-elim (Basic.fail-sem⁻¹ ∈fail)
complete {g = tok t} t∈    with Basic.tok-sem⁻¹ t∈
... | (refl , refl) = tok-sem

complete {g = f <$> g} (>>=-sem x∈ return-sem) =
  cast (P.sym $ proj₂ LM.identity _)
       (<$>-sem (complete x∈))
complete {g = g₁ ⊛ g₂} (>>=-sem {s₁ = s₁} f∈ (>>=-sem x∈ return-sem)) =
  cast (P.sym $ P.cong (_++_ s₁) $ proj₂ LM.identity _)
       (⊛-sem (complete f∈) (complete x∈))
complete {g = g₁ <⊛ g₂} (>>=-sem {s₁ = s₁} x∈ (>>=-sem y∈ return-sem)) =
  cast (P.sym $ P.cong (_++_ s₁) $ proj₂ LM.identity _)
       (<⊛-sem (complete x∈) (complete y∈))
complete {g = g₁ ⊛> g₂} (>>=-sem {s₁ = s₁} x∈ (>>=-sem y∈ return-sem)) =
  cast (P.sym $ P.cong (_++_ s₁) $ proj₂ LM.identity _)
       (⊛>-sem (complete x∈) (complete y∈))

complete {g = g ⋆} (∣-left-sem return-sem) = ⋆-[]-sem
complete {g = g ⋆} (∣-right-sem (>>=-sem x∈ (>>=-sem xs∈ return-sem))) =
  ⋆-+-sem (⊛-sem (<$>-sem (complete x∈))
                 (cast (P.sym $ proj₂ LM.identity _) (complete xs∈)))

------------------------------------------------------------------------
-- Semantics combinators

<$-sem : ∀ {A B} {x : A} {y : B} {g s} →
         y ∈ g ∙ s → x ∈ x <$ g ∙ s
<$-sem y∈ = <⊛-sem return-sem y∈

+-sem : ∀ {c A} {g : ∞Grammar c A} {x xs s₁ s₂} →
        x ∈ ♭? g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → (x ∷ xs) ∈ g + ∙ s₁ ++ s₂
+-sem x∈ xs∈ = ⊛-sem (<$>-sem x∈) xs∈

⋆-∷-sem : ∀ {c A} {g : ∞Grammar c A} {x xs s₁ s₂} →
          x ∈ ♭? g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → x ∷ xs ∈ g ⋆ ∙ s₁ ++ s₂
⋆-∷-sem x∈ xs∈ = ⋆-+-sem (+-sem x∈ xs∈)

⋆-⋆-sem : ∀ {c A} {g : ∞Grammar c A} {xs₁ xs₂ s₁ s₂} →
          xs₁ ∈ g ⋆ ∙ s₁ → xs₂ ∈ g ⋆ ∙ s₂ → xs₁ ++ xs₂ ∈ g ⋆ ∙ s₁ ++ s₂
⋆-⋆-sem ⋆-[]-sem xs₂∈ = xs₂∈
⋆-⋆-sem (⋆-+-sem (⊛-sem (<$>-sem {s = s₁} x∈) xs₁∈)) xs₂∈ =
  cast (P.sym $ LM.assoc s₁ _ _)
       (⋆-∷-sem x∈ (⋆-⋆-sem xs₁∈ xs₂∈))

+-∷-sem : ∀ {c A} {g : ∞Grammar c A} {x xs s₁ s₂} →
          x ∈ ♭? g ∙ s₁ → xs ∈ g + ∙ s₂ → x ∷⁺ xs ∈ g + ∙ s₁ ++ s₂
+-∷-sem x∈ xs∈ = +-sem x∈ (⋆-+-sem xs∈)

mutual

  list-sem : ∀ {A} {g : Grammar-for A} {s : A → List Char} →
             (∀ x → (x , refl) ∈ g x ∙ s x) →
             ∀ xs → (xs , refl) ∈ list g xs ∙ concat (List.map s xs)
  list-sem elem []       = return-sem
  list-sem elem (x ∷ xs) = <$>-sem (list⁺-sem elem (x ∷ xs))

  list⁺-sem :
    ∀ {A} {g : Grammar-for A} {s : A → List Char} →
    (∀ x → (x , refl) ∈ g x ∙ s x) →
    ∀ xs → (xs , refl) ∈ list⁺ g xs ∙
           concat (List.map s (List⁺.toList xs))
  list⁺-sem elem (x ∷ xs) = ⊛-sem (<$>-sem (elem x)) (list-sem elem xs)

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
sep-by-sem-∷ {s₂ = s₂} x∈ y∈ (⊛-sem (<$>-sem x′∈) xs∈) =
  ⊛-sem (<$>-sem x∈)
        (cast (LM.assoc s₂ _ _)
              (⋆-∷-sem (⊛>-sem y∈ x′∈) xs∈))

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
  <$>-lemma : ∀ {c A B} {f : A → B} {g : ∞Grammar c A} →
              Final-whitespace′ (♭? g) →
              Final-whitespace′ (f <$> g)
  <$>-lemma f (<$>-sem x∈) w = , <$>-sem (proj₂ $ f x∈ w)

  ⊛-lemma : ∀ {c₁ c₂ A B}
              {g₁ : ∞Grammar c₁ (A → B)} {g₂ : ∞Grammar c₂ A} →
            Final-whitespace′ (♭? g₂) →
            Final-whitespace′ (g₁ ⊛ g₂)
  ⊛-lemma f₂ (⊛-sem {s₁ = s₁} f∈ x∈) w =
    , cast (P.sym $ LM.assoc s₁ _ _)
           (⊛-sem f∈ (proj₂ $ f₂ x∈ w))

  <⊛-lemma : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
             Final-whitespace′ (♭? g₂) →
             Final-whitespace′ (g₁ <⊛ g₂)
  <⊛-lemma f₂ (<⊛-sem {s₁ = s₁} x∈ y∈) w =
    , cast (P.sym $ LM.assoc s₁ _ _)
           (<⊛-sem x∈ (proj₂ $ f₂ y∈ w))

  ⊛>-lemma : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
             Final-whitespace′ (♭? g₂) →
             Final-whitespace′ (g₁ ⊛> g₂)
  ⊛>-lemma f₂ (⊛>-sem {s₁ = s₁} x∈ y∈) w =
    , cast (P.sym $ LM.assoc s₁ _ _)
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
  final? (suc n) fail               = just (λ ())
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
  ++-lemma = solve 2 (λ a b → (a ⊕ b) ⊕ nil ⊜ (a ⊕ nil) ⊕ b) refl
    where open List-solver

  <$>-lemma : ∀ {c A B} {f : A → B} {g : ∞Grammar c A} →
              Final-whitespace (♭? g) →
              Final-whitespace (f <$> g)
  <$>-lemma f (<$>-sem x∈) w = <$>-sem (f x∈ w)

  ⊛-return-lemma :
    ∀ {c A B} {g : ∞Grammar c (A → B)} {x} →
    Final-whitespace (♭? g) →
    Final-whitespace (g ⊛ return x)
  ⊛-return-lemma f (⊛-sem {s₁ = s₁} f∈ return-sem) w =
    cast (++-lemma s₁ _)
         (⊛-sem (f f∈ w) return-sem)

  +-lemma :
    ∀ {c A} {g : ∞Grammar c A} →
    Final-whitespace (♭? g) →
    Final-whitespace (g +)
  +-lemma f (⊛-sem {s₁ = s₁} (<$>-sem x∈) ⋆-[]-sem) w =
    cast (++-lemma s₁ _)
         (+-sem (f x∈ w) ⋆-[]-sem)
  +-lemma f (⊛-sem {s₁ = s₁} (<$>-sem x∈) (⋆-+-sem xs∈)) w =
    cast (P.sym $ LM.assoc s₁ _ _)
         (+-∷-sem x∈ (+-lemma f xs∈ w))

  ⊛-⋆-lemma :
    ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ (List A → B)} {g₂ : ∞Grammar c₂ A} →
    Final-whitespace (♭? g₁) →
    Final-whitespace (♭? g₂) →
    Final-whitespace (g₁ ⊛ g₂ ⋆)
  ⊛-⋆-lemma f₁ f₂ (⊛-sem {s₁ = s₁} f∈ ⋆-[]-sem) w =
    cast (++-lemma s₁ _)
         (⊛-sem (f₁ f∈ w) ⋆-[]-sem)
  ⊛-⋆-lemma f₁ f₂ (⊛-sem {s₁ = s₁} f∈ (⋆-+-sem xs∈)) w =
    cast (P.sym $ LM.assoc s₁ _ _)
         (⊛-sem f∈ (⋆-+-sem (+-lemma f₂ xs∈ w)))

  ⊛-∣-lemma : ∀ {c₁ c₂₁ c₂₂ A B} {g₁ : ∞Grammar c₁ (A → B)}
                {g₂₁ : ∞Grammar c₂₁ A} {g₂₂ : ∞Grammar c₂₂ A} →
              Final-whitespace (g₁ ⊛ g₂₁) →
              Final-whitespace (g₁ ⊛ g₂₂) →
              Final-whitespace (g₁ ⊛ (g₂₁ ∣ g₂₂))
  ⊛-∣-lemma f₁₂ f₁₃ {s₂ = s₃}
            (⊛-sem {f = f} {x = x} {s₁ = s₁} {s₂ = s₂}
                   f∈ (∣-left-sem x∈)) w
    with f x | (s₁ ++ s₂) ++ s₃ | f₁₂ (⊛-sem f∈ x∈) w
  ... | ._ | ._ | ⊛-sem f∈′ x∈′ = ⊛-sem f∈′ (∣-left-sem x∈′)
  ⊛-∣-lemma f₁₂ f₁₃ {s₂ = s₃}
            (⊛-sem {f = f} {x = x} {s₁ = s₁} {s₂ = s₂}
                   f∈ (∣-right-sem x∈)) w
    with f x | (s₁ ++ s₂) ++ s₃ | f₁₃ (⊛-sem f∈ x∈) w
  ... | ._ | ._ | ⊛-sem f∈′ x∈′ = ⊛-sem f∈′ (∣-right-sem x∈′)

  ⊛-lemma : ∀ {c₁ c₂ A B}
              {g₁ : ∞Grammar c₁ (A → B)} {g₂ : ∞Grammar c₂ A} →
            Final-whitespace (♭? g₂) →
            Final-whitespace (g₁ ⊛ g₂)
  ⊛-lemma f₂ (⊛-sem {s₁ = s₁} f∈ x∈) w =
    cast (P.sym $ LM.assoc s₁ _ _)
         (⊛-sem f∈ (f₂ x∈ w))

  <⊛-return-lemma :
    ∀ {c A B} {g : ∞Grammar c A} {x : B} →
    Final-whitespace (♭? g) →
    Final-whitespace (g <⊛ return x)
  <⊛-return-lemma f (<⊛-sem {s₁ = s₁} f∈ return-sem) w =
    cast (++-lemma s₁ _)
         (<⊛-sem (f f∈ w) return-sem)

  <⊛-lemma : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
             Final-whitespace′ (♭? g₂) →
             Final-whitespace (g₁ <⊛ g₂)
  <⊛-lemma f₂ (<⊛-sem {s₁ = s₁} x∈ y∈) w =
    cast (P.sym $ LM.assoc s₁ _ _)
         (<⊛-sem x∈ (proj₂ $ f₂ y∈ w))

  ⊛>-lemma : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
             Final-whitespace (♭? g₂) →
             Final-whitespace (g₁ ⊛> g₂)
  ⊛>-lemma f₂ (⊛>-sem {s₁ = s₁} x∈ y∈) w =
    cast (P.sym $ LM.assoc s₁ _ _)
         (⊛>-sem x∈ (f₂ y∈ w))

  ∣-lemma : ∀ {c₁ c₂ A} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ A} →
            Final-whitespace (♭? g₁) →
            Final-whitespace (♭? g₂) →
            Final-whitespace (g₁ ∣ g₂)
  ∣-lemma f₁ f₂ (∣-left-sem  x∈) w = ∣-left-sem  (f₁ x∈ w)
  ∣-lemma f₁ f₂ (∣-right-sem x∈) w = ∣-right-sem (f₂ x∈ w)

  final? : ℕ → ∀ {A} (g : Grammar A) → Maybe (Final-whitespace g)

  final? (suc n) fail = just (λ ())

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
