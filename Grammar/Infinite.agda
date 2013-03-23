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
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (_↔_; module Inverse)
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
  infixl 20 _<$>_ _<$_ _⊛_ _<⊛_ _⊛>_
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
    _<$_   : ∀ {c A B} → A → ∞Grammar c B → Grammar A

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

-- A grammar combinator: Kleene plus.

infix 30 _+

_+ : ∀ {c A} → ∞Grammar c A → Grammar (List⁺ A)
g + = _∷_ <$> g ⊛ g ⋆

-- The semantics of "extended" grammars is given by translation to
-- simple grammars.

⟦_⟧ : ∀ {A} → Grammar A → Basic.Grammar A
⟦ return x  ⟧ = Basic.return x
⟦ token     ⟧ = Basic.token
⟦ g₁ >>= g₂ ⟧ = ♯ ⟦ ♭? g₁ ⟧ Basic.>>= λ x → ♯ ⟦ ♭? (g₂ x) ⟧
⟦ g₁ ∣ g₂   ⟧ = ♯ ⟦ ♭? g₁ ⟧ Basic.∣ ♯ ⟦ ♭? g₂ ⟧
⟦ fail      ⟧ = Basic.fail
⟦ tok t     ⟧ = Basic.tok t
⟦ f <$> g   ⟧ = ♯ ⟦ ♭? g  ⟧ Basic.>>= λ x → ♯ Basic.return (f x)
⟦ x <$ g    ⟧ = ♯ ⟦ ♭? g  ⟧ Basic.>>= λ _ → ♯ Basic.return x
⟦ g₁ ⊛ g₂   ⟧ = ♯ ⟦ ♭? g₁ ⟧ Basic.>>= λ f → ♯ ⟦ f <$> g₂ ⟧
⟦ g₁ <⊛ g₂  ⟧ = ♯ ⟦ ♭? g₁ ⟧ Basic.>>= λ x → ♯ ⟦ x <$  g₂ ⟧
⟦ g₁ ⊛> g₂  ⟧ = ♯ ⟦ ♭? g₁ ⟧ Basic.>>= λ _ → ♯ ⟦    ♭? g₂ ⟧
⟦ g ⋆       ⟧ = ♯ Basic.return [] Basic.∣ ♯ ⟦ uncurry _∷_ <$> g + ⟧

------------------------------------------------------------------------
-- More grammar combinators

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

-- A variant of string that takes a String rather than a list of
-- characters.

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
  return-sem : ∀ {A} {x : A} → x ∈ return x ∙ []
  token-sem  : ∀ {t} → t ∈ token ∙ [ t ]
  >>=-sem    : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A}
                 {g₂ : A → ∞Grammar c₂ B} {x y s₁ s₂} →
               x ∈ ♭? g₁ ∙ s₁ → y ∈ ♭? (g₂ x) ∙ s₂ →
               y ∈ g₁ >>= g₂ ∙ s₁ ++ s₂
  left-sem   : ∀ {c₁ c₂ A} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ A}
                 {x s} →
               x ∈ ♭? g₁ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  right-sem  : ∀ {c₁ c₂ A} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ A}
                 {x s} →
               x ∈ ♭? g₂ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  tok-sem    : ∀ {t} → t ∈ tok t ∙ [ t ]
  <$>-sem    : ∀ {c A B} {f : A → B} {g : ∞Grammar c A} {x s} →
               x ∈ ♭? g ∙ s → f x ∈ f <$> g ∙ s
  <$-sem     : ∀ {c A B} {x : A} {g : ∞Grammar c B} {y s} →
               y ∈ ♭? g ∙ s → x ∈ x <$ g ∙ s
  ⊛-sem      : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ (A → B)}
                 {g₂ : ∞Grammar c₂ A} {f x s₁ s₂} →
               f ∈ ♭? g₁ ∙ s₁ → x ∈ ♭? g₂ ∙ s₂ →
               f x ∈ g₁ ⊛ g₂ ∙ s₁ ++ s₂
  <⊛-sem     : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B}
                 {x y s₁ s₂} →
               x ∈ ♭? g₁ ∙ s₁ → y ∈ ♭? g₂ ∙ s₂ →
               x ∈ g₁ <⊛ g₂ ∙ s₁ ++ s₂
  ⊛>-sem     : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B}
                 {x y s₁ s₂} →
               x ∈ ♭? g₁ ∙ s₁ → y ∈ ♭? g₂ ∙ s₂ →
               y ∈ g₁ ⊛> g₂ ∙ s₁ ++ s₂
  ⋆-[]-sem   : ∀ {c A} {g : ∞Grammar c A} →
               [] ∈ g ⋆ ∙ []
  ⋆-+-sem    : ∀ {c A} {g : ∞Grammar c A} {x xs s} →
               (x ∷ xs) ∈ g + ∙ s → x ∷ xs ∈ g ⋆ ∙ s

-- Cast lemma.

cast : ∀ {A} {g : Grammar A} {x s₁ s₂} →
       s₁ ≡ s₂ → x ∈ g ∙ s₁ → x ∈ g ∙ s₂
cast refl = id

-- The alternative semantics is isomorphic to the one above.

isomorphic : ∀ {A x s} {g : Grammar A} →
             x ∈ g ∙ s ↔ x Basic.∈ ⟦ g ⟧ ∙ s
isomorphic {g = g} = record
  { to         = P.→-to-⟶ sound
  ; from       = P.→-to-⟶ (complete g)
  ; inverse-of = record
    { left-inverse-of  = complete∘sound
    ; right-inverse-of = sound∘complete g
    }
  }
  where

  -- Some short lemmas.

  lemma₁ : ∀ s → s ++ [] ≡ s
  lemma₁ = proj₂ LM.identity

  lemma₂ : ∀ s₁ s₂ → s₁ ++ s₂ ++ [] ≡ s₁ ++ s₂
  lemma₂ s₁ s₂ = P.cong (_++_ s₁) (lemma₁ s₂)

  lemma₃ : ∀ s₁ s₂ → s₁ ++ s₂ ≡ ((s₁ ++ []) ++ s₂ ++ []) ++ []
  lemma₃ s₁ s₂ = begin
    s₁ ++ s₂                        ≡⟨ P.cong₂ _++_ (P.sym $ lemma₁ s₁) (P.sym $ lemma₁ s₂) ⟩
    (s₁ ++ []) ++ s₂ ++ []          ≡⟨ P.sym $ lemma₁ _ ⟩
    ((s₁ ++ []) ++ s₂ ++ []) ++ []  ∎
    where open P.≡-Reasoning

  tok-lemma : ∀ {t t′ s} → t ≡ t′ × s ≡ [ t ] → t′ ∈ tok t ∙ s
  tok-lemma (refl , refl) = tok-sem

  -- Soundness.

  sound : ∀ {A x s} {g : Grammar A} → x ∈ g ∙ s → x Basic.∈ ⟦ g ⟧ ∙ s
  sound return-sem               = return-sem
  sound token-sem                = token-sem
  sound (>>=-sem x∈ y∈)          = >>=-sem (sound x∈) (sound y∈)
  sound (left-sem x∈)            = left-sem (sound x∈)
  sound (right-sem x∈)           = right-sem (sound x∈)
  sound tok-sem                  = Inverse.from Basic.tok-sem
                                     ⟨$⟩ (refl , refl)
  sound (<$>-sem x∈)             = Basic.cast (lemma₁ _)
                                     (>>=-sem (sound x∈) return-sem)
  sound (<$-sem x∈)              = Basic.cast (lemma₁ _)
                                     (>>=-sem (sound x∈) return-sem)
  sound (⊛-sem {s₁ = s₁} f∈ x∈)  = Basic.cast (lemma₂ s₁ _)
                                     (>>=-sem (sound f∈)
                                        (>>=-sem (sound x∈) return-sem))
  sound (<⊛-sem {s₁ = s₁} x∈ y∈) = Basic.cast (lemma₂ s₁ _)
                                     (>>=-sem (sound x∈)
                                        (>>=-sem (sound y∈) return-sem))
  sound (⊛>-sem {s₁ = s₁} x∈ y∈) = >>=-sem (sound x∈) (sound y∈)
  sound ⋆-[]-sem                 = left-sem return-sem
  sound (⋆-+-sem xs∈)            = Basic.cast (lemma₁ _)
                                     (right-sem
                                        (>>=-sem (sound xs∈)
                                                 return-sem))

  -- Completeness.

  complete : ∀ {A x s} (g : Grammar A) → x Basic.∈ ⟦ g ⟧ ∙ s → x ∈ g ∙ s
  complete (return x)  return-sem      = return-sem
  complete token       token-sem       = token-sem
  complete (g₁ >>= g₂) (>>=-sem x∈ y∈) = >>=-sem (complete _ x∈)
                                                 (complete _ y∈)
  complete (g₁ ∣ g₂)   (left-sem x∈)   = left-sem  (complete _ x∈)
  complete (g₁ ∣ g₂)   (right-sem x∈)  = right-sem (complete _ x∈)

  complete fail    ∈fail = ⊥-elim (Basic.fail-sem⁻¹ ∈fail)
  complete (tok t) t∈    = tok-lemma (Inverse.to Basic.tok-sem ⟨$⟩ t∈)

  complete (f <$> g) (>>=-sem x∈ return-sem) =
    cast (P.sym $ lemma₁ _)
         (<$>-sem (complete _ x∈))
  complete (x <$ g) (>>=-sem x∈ return-sem) =
    cast (P.sym $ lemma₁ _)
         (<$-sem (complete _ x∈))
  complete (g₁ ⊛ g₂) (>>=-sem {s₁ = s₁} f∈ (>>=-sem x∈ return-sem)) =
    cast (P.sym $ lemma₂ s₁ _)
         (⊛-sem (complete _ f∈) (complete _ x∈))
  complete (g₁ <⊛ g₂) (>>=-sem {s₁ = s₁} x∈ (>>=-sem y∈ return-sem)) =
    cast (P.sym $ lemma₂ s₁ _)
         (<⊛-sem (complete _ x∈) (complete _ y∈))
  complete (g₁ ⊛> g₂) (>>=-sem x∈ y∈) =
    ⊛>-sem (complete _ x∈) (complete _ y∈)

  complete (g ⋆) (left-sem return-sem) = ⋆-[]-sem
  complete (g ⋆) (right-sem (>>=-sem
                    (>>=-sem (>>=-sem {s₁ = s₁} x∈  return-sem)
                             (>>=-sem           xs∈ return-sem))
                    return-sem)) =
    cast (lemma₃ s₁ _)
         (⋆-+-sem (⊛-sem (<$>-sem (complete _ x∈)) (complete _ xs∈)))

  -- More short lemmas.

  sound-cast :
    ∀ {A x s₁ s₂}
    (g : Grammar A) (eq : s₁ ≡ s₂) (x∈ : x ∈ g ∙ s₁) →
    sound (cast eq x∈) ≡ Basic.cast eq (sound x∈)
  sound-cast _ refl _ = refl

  complete-cast :
    ∀ {A x s₁ s₂}
    (g : Grammar A) (eq : s₁ ≡ s₂) (x∈ : x Basic.∈ ⟦ g ⟧ ∙ s₁) →
    complete g (Basic.cast eq x∈) ≡ cast eq (complete g x∈)
  complete-cast _ refl _ = refl

  cast-cast :
    ∀ {A} {x : A} {s₁ s₂ g} (eq : s₁ ≡ s₂) {x∈ : x Basic.∈ g ∙ s₁} →
    Basic.cast (P.sym eq) (Basic.cast eq x∈) ≡ x∈
  cast-cast refl = refl

  cast-cast′ :
    ∀ {A} {x : A} {s₁ s₂ g}
    (eq₁ : s₂ ≡ s₁) (eq₂ : s₁ ≡ s₂) {x∈ : x Basic.∈ g ∙ s₁} →
    Basic.cast eq₁ (Basic.cast eq₂ x∈) ≡ x∈
  cast-cast′ refl refl = refl

  -- The functions sound and complete are inverses.

  complete∘sound : ∀ {A x s} {g : Grammar A} (x∈ : x ∈ g ∙ s) →
                   complete g (sound x∈) ≡ x∈
  complete∘sound return-sem      = refl
  complete∘sound token-sem       = refl
  complete∘sound (>>=-sem x∈ y∈) = P.cong₂ >>=-sem (complete∘sound x∈)
                                                   (complete∘sound y∈)
  complete∘sound (left-sem x∈)   = P.cong left-sem (complete∘sound x∈)
  complete∘sound (right-sem x∈)  = P.cong right-sem (complete∘sound x∈)

  complete∘sound (tok-sem {t = t})
    rewrite Inverse.right-inverse-of (Basic.tok-sem {t = t})
                                     (refl , refl)
    = refl

  complete∘sound (<$>-sem {s = s} x∈) with sound x∈ | complete∘sound x∈
  complete∘sound (<$>-sem {f = f} {g = g} {s = s}
                          .(complete _ x∈′)) | x∈′ | refl
    rewrite complete-cast (f <$> g) (lemma₁ s) (>>=-sem x∈′ return-sem)
          | lemma₁ s
    = refl

  complete∘sound (<$-sem {x = x} {g = g} {s = s} x∈) with sound x∈ | complete∘sound x∈
  complete∘sound (<$-sem {x = x} {g = g} {s = s}
                         .(complete _ x∈′)) | x∈′ | refl
    rewrite complete-cast (x <$ g) (lemma₁ s) (>>=-sem x∈′ return-sem)
          | lemma₁ s
    = refl

  complete∘sound (⊛-sem f∈ x∈) with sound f∈ | complete∘sound f∈
                                  | sound x∈ | complete∘sound x∈
  complete∘sound (⊛-sem {g₁ = g₁} {g₂ = g₂} {s₁ = s₁} {s₂ = s₂}
                        .(complete _ f∈′) .(complete _ x∈′))
    | f∈′ | refl | x∈′ | refl
    rewrite complete-cast (g₁ ⊛ g₂) (lemma₂ s₁ s₂)
                          (>>=-sem f∈′ (>>=-sem x∈′ return-sem))
          | lemma₁ s₂
    = refl

  complete∘sound (<⊛-sem x∈ y∈) with sound x∈ | complete∘sound x∈
                                   | sound y∈ | complete∘sound y∈
  complete∘sound (<⊛-sem {g₁ = g₁} {g₂ = g₂} {s₁ = s₁} {s₂ = s₂}
                        .(complete _ x∈′) .(complete _ y∈′))
    | x∈′ | refl | y∈′ | refl
    rewrite complete-cast (g₁ <⊛ g₂) (lemma₂ s₁ s₂)
                          (>>=-sem x∈′ (>>=-sem y∈′ return-sem))
          | lemma₁ s₂
    = refl

  complete∘sound (⊛>-sem x∈ y∈) with sound x∈ | complete∘sound x∈
                                   | sound y∈ | complete∘sound y∈
  complete∘sound (⊛>-sem .(complete _ x∈′) .(complete _ y∈′))
    | x∈′ | refl | y∈′ | refl
    = refl

  complete∘sound ⋆-[]-sem      = refl
  complete∘sound (⋆-+-sem xs∈) with sound xs∈ | complete∘sound xs∈
  complete∘sound (⋆-+-sem {g = g}
                    .(complete _ (>>=-sem (>>=-sem x∈   return-sem)
                                          (>>=-sem xs∈′ return-sem))))
    | >>=-sem (>>=-sem {s₁ = s₁} x∈   return-sem)
              (>>=-sem {s₁ = s₂} xs∈′ return-sem)
    | refl
    rewrite complete-cast (g ⋆) (lemma₁ ((s₁ ++ []) ++ s₂ ++ []))
                          (right-sem
                            (>>=-sem (>>=-sem (>>=-sem x∈   return-sem)
                                              (>>=-sem xs∈′ return-sem))
                                     return-sem))
          | lemma₁ s₁ | lemma₁ s₂ | lemma₁ (s₁ ++ s₂)
    = refl

  sound∘complete : ∀ {A x s}
                   (g : Grammar A) (x∈ : x Basic.∈ ⟦ g ⟧ ∙ s) →
                   sound (complete g x∈) ≡ x∈
  sound∘complete (return x)  return-sem      = refl
  sound∘complete token       token-sem       = refl
  sound∘complete (g₁ >>= g₂) (>>=-sem x∈ y∈) = P.cong₂ >>=-sem (sound∘complete (♭? g₁) x∈)
                                                               (sound∘complete (♭? (g₂ _)) y∈)
  sound∘complete (g₁ ∣ g₂)   (left-sem x∈)   = P.cong left-sem  (sound∘complete (♭? g₁) x∈)
  sound∘complete (g₁ ∣ g₂)   (right-sem x∈)  = P.cong right-sem (sound∘complete (♭? g₂) x∈)

  sound∘complete fail    ∈fail = ⊥-elim (Basic.fail-sem⁻¹ ∈fail)
  sound∘complete (tok t) t∈    =
    helper _ (Inverse.left-inverse-of Basic.tok-sem t∈)
    where
    helper : ∀ {t t′ s} {t∈ : t′ Basic.∈ Basic.tok t ∙ s}
             (eqs : t ≡ t′ × s ≡ [ t ]) →
             Inverse.from Basic.tok-sem ⟨$⟩ eqs ≡ t∈ →
             sound (tok-lemma eqs) ≡ t∈
    helper (refl , refl) ≡t∈ = ≡t∈

  sound∘complete (f <$> g) (>>=-sem x∈ return-sem)
    with complete (♭? g) x∈ | sound∘complete (♭? g) x∈
  sound∘complete (f <$> g) (>>=-sem {s₁ = s₁} .(sound x∈′) return-sem)
    | x∈′ | refl
    rewrite sound-cast (f <$> g) (P.sym $ lemma₁ s₁) (<$>-sem x∈′)
    = cast-cast (lemma₁ s₁)

  sound∘complete (x <$ g) (>>=-sem x∈ return-sem)
    with complete (♭? g) x∈ | sound∘complete (♭? g) x∈
  sound∘complete (x <$ g) (>>=-sem {s₁ = s₁} .(sound x∈′) return-sem)
    | x∈′ | refl
    rewrite sound-cast (x <$ g) (P.sym $ lemma₁ s₁) (<$-sem x∈′)
    = cast-cast (lemma₁ s₁)

  sound∘complete (g₁ ⊛ g₂) (>>=-sem f∈ (>>=-sem x∈ return-sem))
    with complete (♭? g₁) f∈ | sound∘complete (♭? g₁) f∈
       | complete (♭? g₂) x∈ | sound∘complete (♭? g₂) x∈
  sound∘complete (g₁ ⊛ g₂)
    (>>=-sem {s₁ = s₁} .(sound f∈′)
             (>>=-sem {s₁ = s₂} .(sound x∈′) return-sem))
    | f∈′ | refl | x∈′ | refl
    rewrite sound-cast (g₁ ⊛ g₂) (P.sym $ lemma₂ s₁ s₂) (⊛-sem f∈′ x∈′)
    = cast-cast (lemma₂ s₁ s₂)

  sound∘complete (g₁ <⊛ g₂) (>>=-sem x∈ (>>=-sem y∈ return-sem))
    with complete (♭? g₁) x∈ | sound∘complete (♭? g₁) x∈
       | complete (♭? g₂) y∈ | sound∘complete (♭? g₂) y∈
  sound∘complete (g₁ <⊛ g₂)
    (>>=-sem {s₁ = s₁} .(sound x∈′)
             (>>=-sem {s₁ = s₂} .(sound y∈′) return-sem))
    | x∈′ | refl | y∈′ | refl
    rewrite sound-cast (g₁ <⊛ g₂) (P.sym $ lemma₂ s₁ s₂) (<⊛-sem x∈′ y∈′)
    = cast-cast (lemma₂ s₁ s₂)

  sound∘complete (g₁ ⊛> g₂) (>>=-sem x∈ y∈)
    with complete (♭? g₁) x∈ | sound∘complete (♭? g₁) x∈
       | complete (♭? g₂) y∈ | sound∘complete (♭? g₂) y∈
  sound∘complete (g₁ ⊛> g₂) (>>=-sem .(sound x∈′) .(sound y∈′))
    | x∈′ | refl | y∈′ | refl
    = refl

  sound∘complete (g ⋆) (left-sem return-sem) = refl
  sound∘complete (g ⋆)
    (right-sem
       (>>=-sem (>>=-sem (>>=-sem x∈  return-sem)
                         (>>=-sem xs∈ return-sem))
                return-sem))
    with complete (♭? g) x∈ | sound∘complete (♭? g) x∈
       | complete (g ⋆) xs∈ | sound∘complete (g ⋆) xs∈
  sound∘complete (g ⋆)
    (right-sem
       (>>=-sem (>>=-sem (>>=-sem {s₁ = s₁} .(sound x∈′)  return-sem)
                         (>>=-sem {s₁ = s₂} .(sound xs∈′) return-sem))
                return-sem))
    | x∈′ | refl | xs∈′ | refl
    rewrite sound-cast (g ⋆) (lemma₃ s₁ s₂)
                       (⋆-+-sem (⊛-sem (<$>-sem x∈′) xs∈′))
    = lemma g (lemma₃ s₁ s₂) (lemma₁ (s₁ ++ s₂))
              (lemma₂ s₁ s₂) (lemma₁ s₁)
              (>>=-sem (sound x∈′)  return-sem)
              (>>=-sem (sound xs∈′) return-sem)
    where
    lemma :
      ∀ {c A} {f : List A → List⁺ A} {xs s₁ s₁++s₂ s₁++[] s₂++[]}
      (g   : ∞Grammar c A)
      (eq₁ : s₁++s₂ ≡ (s₁++[] ++ s₂++[]) ++ [])
      (eq₂ : (s₁++s₂) ++ [] ≡ s₁++s₂)
      (eq₃ : s₁ ++ s₂++[] ≡ s₁++s₂)
      (eq₄ : s₁++[] ≡ s₁)
      (f∈  : f  Basic.∈ ⟦ _∷_ <$> g ⟧ ∙ s₁++[])
      (xs∈ : xs Basic.∈ ⟦ f <$> g ⋆ ⟧ ∙ s₂++[]) →
      _≡_ {A = List⁺.toList xs Basic.∈ ⟦ g ⋆ ⟧ ∙ _}
          (Basic.cast eq₁
             (Basic.cast eq₂
                (right-sem
                   (>>=-sem
                      (Basic.cast eq₃ (>>=-sem (Basic.cast eq₄ f∈) xs∈))
                      return-sem))))
          (right-sem (>>=-sem (>>=-sem f∈ xs∈) return-sem))
    lemma _ eq₁ eq₂ refl refl _ _ = cast-cast′ eq₁ eq₂

------------------------------------------------------------------------
-- Semantics combinators

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
single-space-sem = +-sem (left-sem tok-sem) ⋆-[]-sem

string-sem′ : ∀ {s s′ s″} → s ∈ string s′ ∙ s″ ↔ (s ≡ s′ × s′ ≡ s″)
string-sem′ = record
  { to         = P.→-to-⟶ (to _)
  ; from       = P.→-to-⟶ (from _)
  ; inverse-of = record
    { left-inverse-of  = from∘to _
    ; right-inverse-of = to∘from _
    }
  }
  where
  to : ∀ {s} s′ {s″} → s ∈ string s′ ∙ s″ → s ≡ s′ × s′ ≡ s″
  to []       return-sem                   = (refl , refl)
  to (c ∷ s′) (⊛-sem (<$>-sem tok-sem) s∈) =
    Prod.map (P.cong (_∷_ c)) (P.cong (_∷_ c)) $ to s′ s∈

  from : ∀ {s} s′ {s″} → s ≡ s′ × s′ ≡ s″ → s ∈ string s′ ∙ s″
  from []       (refl , refl) = return-sem
  from (c ∷ s′) (refl , refl) =
    ⊛-sem (<$>-sem tok-sem) (from s′ (refl , refl))

  from∘to : ∀ {s} s′ {s″} (s∈ : s ∈ string s′ ∙ s″) →
            from s′ (to s′ s∈) ≡ s∈
  from∘to []       return-sem                   = refl
  from∘to (c ∷ s′) (⊛-sem (<$>-sem tok-sem) s∈)
    with to s′ s∈ | from∘to s′ s∈
  from∘to (c ∷ s′) (⊛-sem (<$>-sem tok-sem) .(from s′ (refl , refl)))
    | (refl , refl) | refl = refl

  to∘from : ∀ {s} s′ {s″} (eqs : s ≡ s′ × s′ ≡ s″) →
            to s′ (from s′ eqs) ≡ eqs
  to∘from []       (refl , refl) = refl
  to∘from (c ∷ s′) (refl , refl)
    rewrite to∘from s′ (refl , refl)
    = refl

string-sem : ∀ {s} → s ∈ string s ∙ s
string-sem = Inverse.from string-sem′ ⟨$⟩ (refl , refl)

------------------------------------------------------------------------
-- Expressiveness

-- Every language that can be recursively enumerated in Agda can be
-- represented by a (unit-valued) grammar.

expressive : (enumeration : ℕ → Maybe (List Char)) →
             ∃ λ (g : Grammar ⊤) →
               ∀ {s} → tt ∈ g ∙ s ↔ ∃ λ n → enumeration n ≡ just s
expressive f = (g f , g-sem f)
  where
  maybe-string : Maybe (List Char) → Grammar ⊤
  maybe-string nothing  = fail
  maybe-string (just s) = tt <$ string s

  g : (ℕ → Maybe (List Char)) → Grammar ⊤
  g f = maybe-string (f 0) ∣ ♯ g (f ∘ suc)

  maybe-string-sem : ∀ {m s} → tt ∈ maybe-string m ∙ s ↔ m ≡ just s
  maybe-string-sem {nothing} = record
    { to         = P.→-to-⟶ (λ ())
    ; from       = P.→-to-⟶ (λ ())
    ; inverse-of = record
      { left-inverse-of  = λ ()
      ; right-inverse-of = λ ()
      }
    }
  maybe-string-sem {just s} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = from∘to
      ; right-inverse-of = to∘from
      }
    }
    where
    to : ∀ {s′} → tt ∈ tt <$ string s ∙ s′ → just s ≡ just s′
    to (<$-sem s∈) =
      P.cong just $ proj₂ (Inverse.to string-sem′ ⟨$⟩ s∈)

    from : ∀ {s′} →
           Maybe.Maybe.just s ≡ just s′ → tt ∈ tt <$ string s ∙ s′
    from refl = <$-sem (Inverse.from string-sem′ ⟨$⟩ (refl , refl))

    from∘to : ∀ {s′} (tt∈ : tt ∈ tt <$ string s ∙ s′) →
              from (to tt∈) ≡ tt∈
    from∘to (<$-sem s∈)
      with Inverse.to string-sem′ ⟨$⟩ s∈
         | Inverse.left-inverse-of string-sem′ s∈
    from∘to (<$-sem .(Inverse.from string-sem′ ⟨$⟩ (refl , refl)))
      | (refl , refl) | refl = refl

    to∘from : ∀ {s′} (eq : Maybe.Maybe.just s ≡ just s′) →
              to (from eq) ≡ eq
    to∘from refl
      rewrite Inverse.right-inverse-of
                (string-sem′ {s = s}) (refl , refl)
      = refl

  g-sem : ∀ f {s} → tt ∈ g f ∙ s ↔ ∃ λ n → f n ≡ just s
  g-sem f {s} = record
    { to         = P.→-to-⟶ (to   f)
    ; from       = P.→-to-⟶ (from f)
    ; inverse-of = record
      { left-inverse-of  = from∘to f
      ; right-inverse-of = to∘from f
      }
    }
    where
    to : ∀ f {s} → tt ∈ g f ∙ s → ∃ λ n → f n ≡ just s
    to f (left-sem  tt∈) = (zero , Inverse.to maybe-string-sem ⟨$⟩
                                     tt∈)
    to f (right-sem tt∈) = Prod.map suc id $ to (f ∘ suc) tt∈

    from : ∀ f {s} → (∃ λ n → f n ≡ just s) → tt ∈ g f ∙ s
    from f (zero  , eq) = left-sem  (Inverse.from maybe-string-sem ⟨$⟩
                                       eq)
    from f (suc n , eq) = right-sem (from (f ∘ suc) (n , eq))

    from∘to : ∀ f {s} (tt∈ : tt ∈ g f ∙ s) → from f (to f tt∈) ≡ tt∈
    from∘to f (right-sem tt∈) = P.cong right-sem $
                                  from∘to (f ∘ suc) tt∈
    from∘to f (left-sem  tt∈) =
      P.cong left-sem (Inverse.left-inverse-of maybe-string-sem tt∈)

    to∘from : ∀ f {s} (eq : ∃ λ n → f n ≡ just s) →
              to f (from f eq) ≡ eq
    to∘from f (suc n , eq) = P.cong (Prod.map suc id) $
                               to∘from (f ∘ suc) (n , eq)
    to∘from f (zero  , eq) =
      P.cong (_,_ 0) (Inverse.right-inverse-of maybe-string-sem eq)

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
-- Trailing whitespace

-- A predicate for grammars that can "swallow" extra trailing
-- whitespace.

Trailing-whitespace : ∀ {A} → Grammar A → Set₁
Trailing-whitespace g =
  ∀ {x s} → x ∈ g <⊛ whitespace ⋆ ∙ s → x ∈ g ∙ s

-- A similar but weaker property.

Trailing-whitespace′ : ∀ {A} → Grammar A → Set₁
Trailing-whitespace′ g =
  ∀ {x s s₁ s₂} →
  x ∈ g ∙ s₁ → s ∈ whitespace ⋆ ∙ s₂ → ∃ λ y → y ∈ g ∙ s₁ ++ s₂

-- A heuristic (and rather incomplete) procedure that either proves
-- that a production can swallow trailing whitespace (in the weaker
-- sense), or returns "don't know" as the answer.
--
-- The natural number n is used to ensure termination.

trailing-whitespace′? : ∀ (n : ℕ) {A} (g : Grammar A) →
                        Maybe (Trailing-whitespace′ g)
trailing-whitespace′? = trailing?
  where
  <$>-lemma : ∀ {c A B} {f : A → B} {g : ∞Grammar c A} →
              Trailing-whitespace′ (♭? g) →
              Trailing-whitespace′ (f <$> g)
  <$>-lemma t (<$>-sem x∈) w = , <$>-sem (proj₂ $ t x∈ w)

  <$-lemma : ∀ {c A B} {x : A} {g : ∞Grammar c B} →
             Trailing-whitespace′ (♭? g) →
             Trailing-whitespace′ (x <$ g)
  <$-lemma t (<$-sem x∈) w = , <$-sem (proj₂ $ t x∈ w)

  ⊛-lemma : ∀ {c₁ c₂ A B}
              {g₁ : ∞Grammar c₁ (A → B)} {g₂ : ∞Grammar c₂ A} →
            Trailing-whitespace′ (♭? g₂) →
            Trailing-whitespace′ (g₁ ⊛ g₂)
  ⊛-lemma t₂ (⊛-sem {s₁ = s₁} f∈ x∈) w =
    , cast (P.sym $ LM.assoc s₁ _ _)
           (⊛-sem f∈ (proj₂ $ t₂ x∈ w))

  <⊛-lemma : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
             Trailing-whitespace′ (♭? g₂) →
             Trailing-whitespace′ (g₁ <⊛ g₂)
  <⊛-lemma t₂ (<⊛-sem {s₁ = s₁} x∈ y∈) w =
    , cast (P.sym $ LM.assoc s₁ _ _)
           (<⊛-sem x∈ (proj₂ $ t₂ y∈ w))

  ⊛>-lemma : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
             Trailing-whitespace′ (♭? g₂) →
             Trailing-whitespace′ (g₁ ⊛> g₂)
  ⊛>-lemma t₂ (⊛>-sem {s₁ = s₁} x∈ y∈) w =
    , cast (P.sym $ LM.assoc s₁ _ _)
           (⊛>-sem x∈ (proj₂ $ t₂ y∈ w))

  ∣-lemma : ∀ {c₁ c₂ A} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ A} →
            Trailing-whitespace′ (♭? g₁) →
            Trailing-whitespace′ (♭? g₂) →
            Trailing-whitespace′ (g₁ ∣ g₂)
  ∣-lemma t₁ t₂ (left-sem  x∈) w = , left-sem  (proj₂ $ t₁ x∈ w)
  ∣-lemma t₁ t₂ (right-sem x∈) w = , right-sem (proj₂ $ t₂ x∈ w)

  whitespace⋆-lemma :
    ∀ {A} {g : Grammar A} →
    Is-whitespace g →
    Trailing-whitespace′ (g ⋆)
  whitespace⋆-lemma is-whitespace xs∈ w = , ⋆-⋆-sem xs∈ w

  trailing? : ℕ → ∀ {A} (g : Grammar A) → Maybe (Trailing-whitespace′ g)
  trailing? (suc n) fail               = just (λ ())
  trailing? (suc n) (f <$> g)          = <$>-lemma <$>M trailing? n (♭? g)
  trailing? (suc n) (x <$ g)           = <$-lemma  <$>M trailing? n (♭? g)
  trailing? (suc n) (g₁ ⊛ g₂)          = ⊛-lemma   <$>M trailing? n (♭? g₂)
  trailing? (suc n) (g₁ <⊛ g₂)         = <⊛-lemma  <$>M trailing? n (♭? g₂)
  trailing? (suc n) (g₁ ⊛> g₂)         = ⊛>-lemma  <$>M trailing? n (♭? g₂)
  trailing? (suc n) (g₁ ∣ g₂)          = ∣-lemma   <$>M trailing? n (♭? g₁)
                                                     ⊛M trailing? n (♭? g₂)
  trailing? (suc n) (_⋆ {c = false} g) = whitespace⋆-lemma <$>M
                                           is-whitespace? g
  trailing? _       _                  = nothing

-- A heuristic (and rather incomplete) procedure that either proves
-- that a production can swallow trailing whitespace, or returns
-- "don't know" as the answer.
--
-- The natural number n is used to ensure termination.

trailing-whitespace? : ∀ (n : ℕ) {A} (g : Grammar A) →
                       Maybe (Trailing-whitespace g)
trailing-whitespace? n g = convert <$>M trailing? n g
  where
  -- An alternative formulation of Trailing-whitespace.

  Trailing-whitespace″ : ∀ {A} → Grammar A → Set₁
  Trailing-whitespace″ g =
    ∀ {x s s₁ s₂} →
    x ∈ g ∙ s₁ → s ∈ whitespace ⋆ ∙ s₂ → x ∈ g ∙ s₁ ++ s₂

  convert : ∀ {A} {g : Grammar A} →
            Trailing-whitespace″ g → Trailing-whitespace g
  convert t (<⊛-sem x∈ w) = t x∈ w

  ++-lemma = solve 2 (λ a b → (a ⊕ b) ⊕ nil ⊜ (a ⊕ nil) ⊕ b) refl
    where open List-solver

  <$>-lemma : ∀ {c A B} {f : A → B} {g : ∞Grammar c A} →
              Trailing-whitespace″ (♭? g) →
              Trailing-whitespace″ (f <$> g)
  <$>-lemma t (<$>-sem x∈) w = <$>-sem (t x∈ w)

  <$-lemma : ∀ {c A B} {x : A} {g : ∞Grammar c B} →
             Trailing-whitespace′ (♭? g) →
             Trailing-whitespace″ (x <$ g)
  <$-lemma t (<$-sem x∈) w = <$-sem (proj₂ $ t x∈ w)

  ⊛-return-lemma :
    ∀ {c A B} {g : ∞Grammar c (A → B)} {x} →
    Trailing-whitespace″ (♭? g) →
    Trailing-whitespace″ (g ⊛ return x)
  ⊛-return-lemma t (⊛-sem {s₁ = s₁} f∈ return-sem) w =
    cast (++-lemma s₁ _)
         (⊛-sem (t f∈ w) return-sem)

  +-lemma :
    ∀ {c A} {g : ∞Grammar c A} →
    Trailing-whitespace″ (♭? g) →
    Trailing-whitespace″ (g +)
  +-lemma t (⊛-sem {s₁ = s₁} (<$>-sem x∈) ⋆-[]-sem) w =
    cast (++-lemma s₁ _)
         (+-sem (t x∈ w) ⋆-[]-sem)
  +-lemma t (⊛-sem {s₁ = s₁} (<$>-sem x∈) (⋆-+-sem xs∈)) w =
    cast (P.sym $ LM.assoc s₁ _ _)
         (+-∷-sem x∈ (+-lemma t xs∈ w))

  ⊛-⋆-lemma :
    ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ (List A → B)} {g₂ : ∞Grammar c₂ A} →
    Trailing-whitespace″ (♭? g₁) →
    Trailing-whitespace″ (♭? g₂) →
    Trailing-whitespace″ (g₁ ⊛ g₂ ⋆)
  ⊛-⋆-lemma t₁ t₂ (⊛-sem {s₁ = s₁} f∈ ⋆-[]-sem) w =
    cast (++-lemma s₁ _)
         (⊛-sem (t₁ f∈ w) ⋆-[]-sem)
  ⊛-⋆-lemma t₁ t₂ (⊛-sem {s₁ = s₁} f∈ (⋆-+-sem xs∈)) w =
    cast (P.sym $ LM.assoc s₁ _ _)
         (⊛-sem f∈ (⋆-+-sem (+-lemma t₂ xs∈ w)))

  ⊛-∣-lemma : ∀ {c₁ c₂₁ c₂₂ A B} {g₁ : ∞Grammar c₁ (A → B)}
                {g₂₁ : ∞Grammar c₂₁ A} {g₂₂ : ∞Grammar c₂₂ A} →
              Trailing-whitespace″ (g₁ ⊛ g₂₁) →
              Trailing-whitespace″ (g₁ ⊛ g₂₂) →
              Trailing-whitespace″ (g₁ ⊛ (g₂₁ ∣ g₂₂))
  ⊛-∣-lemma t₁₂ t₁₃ {s₂ = s₃}
            (⊛-sem {f = f} {x = x} {s₁ = s₁} {s₂ = s₂}
                   f∈ (left-sem x∈)) w
    with f x | (s₁ ++ s₂) ++ s₃ | t₁₂ (⊛-sem f∈ x∈) w
  ... | ._ | ._ | ⊛-sem f∈′ x∈′ = ⊛-sem f∈′ (left-sem x∈′)
  ⊛-∣-lemma t₁₂ t₁₃ {s₂ = s₃}
            (⊛-sem {f = f} {x = x} {s₁ = s₁} {s₂ = s₂}
                   f∈ (right-sem x∈)) w
    with f x | (s₁ ++ s₂) ++ s₃ | t₁₃ (⊛-sem f∈ x∈) w
  ... | ._ | ._ | ⊛-sem f∈′ x∈′ = ⊛-sem f∈′ (right-sem x∈′)

  ⊛-lemma : ∀ {c₁ c₂ A B}
              {g₁ : ∞Grammar c₁ (A → B)} {g₂ : ∞Grammar c₂ A} →
            Trailing-whitespace″ (♭? g₂) →
            Trailing-whitespace″ (g₁ ⊛ g₂)
  ⊛-lemma t₂ (⊛-sem {s₁ = s₁} f∈ x∈) w =
    cast (P.sym $ LM.assoc s₁ _ _)
         (⊛-sem f∈ (t₂ x∈ w))

  <⊛-return-lemma :
    ∀ {c A B} {g : ∞Grammar c A} {x : B} →
    Trailing-whitespace″ (♭? g) →
    Trailing-whitespace″ (g <⊛ return x)
  <⊛-return-lemma t (<⊛-sem {s₁ = s₁} f∈ return-sem) w =
    cast (++-lemma s₁ _)
         (<⊛-sem (t f∈ w) return-sem)

  <⊛-lemma : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
             Trailing-whitespace′ (♭? g₂) →
             Trailing-whitespace″ (g₁ <⊛ g₂)
  <⊛-lemma t₂ (<⊛-sem {s₁ = s₁} x∈ y∈) w =
    cast (P.sym $ LM.assoc s₁ _ _)
         (<⊛-sem x∈ (proj₂ $ t₂ y∈ w))

  ⊛>-lemma : ∀ {c₁ c₂ A B} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
             Trailing-whitespace″ (♭? g₂) →
             Trailing-whitespace″ (g₁ ⊛> g₂)
  ⊛>-lemma t₂ (⊛>-sem {s₁ = s₁} x∈ y∈) w =
    cast (P.sym $ LM.assoc s₁ _ _)
         (⊛>-sem x∈ (t₂ y∈ w))

  ∣-lemma : ∀ {c₁ c₂ A} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ A} →
            Trailing-whitespace″ (♭? g₁) →
            Trailing-whitespace″ (♭? g₂) →
            Trailing-whitespace″ (g₁ ∣ g₂)
  ∣-lemma t₁ t₂ (left-sem  x∈) w = left-sem  (t₁ x∈ w)
  ∣-lemma t₁ t₂ (right-sem x∈) w = right-sem (t₂ x∈ w)

  trailing? : ℕ → ∀ {A} (g : Grammar A) → Maybe (Trailing-whitespace″ g)

  trailing? (suc n) fail = just (λ ())

  trailing? (suc n) (f <$> g) = <$>-lemma <$>M trailing? n (♭? g)
  trailing? (suc n) (x <$ g)  = <$-lemma  <$>M trailing-whitespace′? (suc n) (♭? g)

  trailing? (suc n) (_⊛_ {c₂ = false} g  (return x))  = ⊛-return-lemma <$>M trailing? n (♭? g)
  trailing? (suc n) (_⊛_ {c₂ = false} g₁ (g₂ ⋆))      = ⊛-⋆-lemma      <$>M trailing? n (♭? g₁)
                                                                         ⊛M trailing? n (♭? g₂)
  trailing? (suc n) (_⊛_ {c₂ = false} g₁ (g₂₁ ∣ g₂₂)) = ⊛-∣-lemma      <$>M trailing? n (g₁ ⊛ g₂₁)
                                                                         ⊛M trailing? n (g₁ ⊛ g₂₂)
  trailing? (suc n) (_⊛_              g₁ g₂)          = ⊛-lemma        <$>M trailing? n (♭? g₂)

  trailing? (suc n) (_<⊛_ {c₂ = false} g  (return x)) = <⊛-return-lemma <$>M trailing? n (♭? g)
  trailing? (suc n) (_<⊛_              g₁ g₂)         = <⊛-lemma <$>M
                                                          trailing-whitespace′? (suc n) (♭? g₂)

  trailing? (suc n) (g₁ ⊛> g₂) = ⊛>-lemma <$>M trailing? n (♭? g₂)

  trailing? (suc n) (g₁ ∣ g₂) = ∣-lemma <$>M trailing? n (♭? g₁)
                                          ⊛M trailing? n (♭? g₂)

  trailing? _ _ = nothing

private

  -- Some unit tests.

  test₁ : IsJust (trailing-whitespace′? 1 (whitespace ⋆))
  test₁ = _

  test₂ : IsJust (trailing-whitespace′? 2 (whitespace +))
  test₂ = _

  test₃ : IsJust (trailing-whitespace? 1 (tt <$ whitespace ⋆))
  test₃ = _

  test₄ : IsJust (trailing-whitespace? 2 (tt <$ whitespace +))
  test₄ = _
