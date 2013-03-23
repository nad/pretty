------------------------------------------------------------------------
-- Grammars defined as functions from non-terminals to productions
------------------------------------------------------------------------

module Grammar.Non-terminal where

open import Algebra
open import Category.Monad
open import Data.Bool
open import Data.Bool.Properties
open import Data.Char
open import Data.Empty
open import Data.List as List hiding (unfold)
open import Data.List.Properties
open import Data.Maybe as Maybe
open import Data.Nat
open import Data.Product as Product
open import Data.Unit
open import Function
open import Level using (Lift; lift)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)
open import Relation.Nullary

private
  module LM {A : Set} = Monoid (List.monoid A)
  open module MM {f} = RawMonadPlus (Maybe.monadPlus {f = f})
    using ()
    renaming (_<$>_ to _<$>M_; _⊛_ to _⊛M_;
              _>>=_ to _>>=M_; _∣_ to _∣M_)

open import Utilities

------------------------------------------------------------------------
-- Grammars

-- Productions. (Note that productions can contain choices.)

infix  30 _⋆
infixl 20 _⊛_ _<⊛_
infixl 15 _>>=_
infixl 10 _∣_

data Prod (NT : Set → Set₁) : Set → Set₁ where
  !      : ∀ {A} → NT A → Prod NT A
  fail   : ∀ {A} → Prod NT A
  return : ∀ {A} → A → Prod NT A
  token  : Prod NT Char
  tok    : Char → Prod NT Char
  _⊛_    : ∀ {A B} → Prod NT (A → B) → Prod NT A → Prod NT B
  _<⊛_   : ∀ {A B} → Prod NT A → Prod NT B → Prod NT A
  _>>=_  : ∀ {A B} → Prod NT A → (A → Prod NT B) → Prod NT B
  _∣_    : ∀ {A} → Prod NT A → Prod NT A → Prod NT A
  _⋆     : ∀ {A} → Prod NT A → Prod NT (List A)

-- Grammars.

Grammar : (Set → Set₁) → Set₁
Grammar NT = ∀ A → NT A → Prod NT A

-- An empty non-terminal type.

Empty-NT : Set → Set₁
Empty-NT _ = Lift ⊥

-- A corresponding grammar.

empty-grammar : Grammar Empty-NT
empty-grammar _ (lift ())

------------------------------------------------------------------------
-- Production combinators

-- Map.

infixl 20 _<$>_ _<$_

_<$>_ : ∀ {NT A B} → (A → B) → Prod NT A → Prod NT B
f <$> p = return f ⊛ p

_<$_ : ∀ {NT A B} → A → Prod NT B → Prod NT A
x <$ p = return x <⊛ p

-- Various sequencing operators.

infixl 20 _⊛>_
infixl 15 _>>_

_>>_ : ∀ {NT A B} → Prod NT A → Prod NT B → Prod NT B
p₁ >> p₂ = (λ _ x → x) <$> p₁ ⊛ p₂

_⊛>_ : ∀ {NT A B} → Prod NT A → Prod NT B → Prod NT B
_⊛>_ = _>>_

-- Kleene plus.

infix 30 _+

_+ : ∀ {NT A} → Prod NT A → Prod NT (List A)
p + = _∷_ <$> p ⊛ p ⋆

-- Elements separated by something.

infixl 18 _sep-by_

_sep-by_ : ∀ {NT A B} → Prod NT A → Prod NT B → Prod NT (List A)
g sep-by sep = _∷_ <$> g ⊛ (sep >> g) ⋆

-- A production for tokens satisfying a given predicate.

if-true : ∀ {NT} (b : Bool) → Prod NT (T b)
if-true true  = return tt
if-true false = fail

sat : ∀ {NT} (p : Char → Bool) → Prod NT (∃ λ t → T (p t))
sat p = token >>= λ t → _,_ t <$> if-true (p t)

-- A production for whitespace.

whitespace : ∀ {NT} → Prod NT Char
whitespace = tok ' ' ∣ tok '\n'

-- A production for a given string.

string : ∀ {NT} → List Char → Prod NT (List Char)
string []      = return []
string (t ∷ s) = _∷_ <$> tok t ⊛ string s

-- A production for the given string, possibly followed by some
-- whitespace.

symbol : ∀ {NT} → List Char → Prod NT (List Char)
symbol s = string s <⊛ whitespace ⋆

------------------------------------------------------------------------
-- Semantics

infix 4 [_]_∈_∙_

data [_]_∈_∙_ {NT : Set → Set₁} (g : Grammar NT) :
              ∀ {A} → A → Prod NT A → List Char → Set₁ where
  !-sem      : ∀ {A} {nt : NT A} {x s} →
               [ g ] x ∈ g A nt ∙ s → [ g ] x ∈ ! nt ∙ s
  return-sem : ∀ {A} {x : A} → [ g ] x ∈ return x ∙ []
  token-sem  : ∀ {t} → [ g ] t ∈ token ∙ [ t ]
  tok-sem    : ∀ {t} → [ g ] t ∈ tok t ∙ [ t ]
  ⊛-sem      : ∀ {A B} {p₁ : Prod NT (A → B)} {p₂ : Prod NT A}
                 {f x s₁ s₂} →
               [ g ] f ∈ p₁ ∙ s₁ → [ g ] x ∈ p₂ ∙ s₂ →
               [ g ] f x ∈ p₁ ⊛ p₂ ∙ s₁ ++ s₂
  <⊛-sem     : ∀ {A B} {p₁ : Prod NT A} {p₂ : Prod NT B} {x y s₁ s₂} →
               [ g ] x ∈ p₁ ∙ s₁ → [ g ] y ∈ p₂ ∙ s₂ →
               [ g ] x ∈ p₁ <⊛ p₂ ∙ s₁ ++ s₂
  >>=-sem    : ∀ {A B} {p₁ : Prod NT A} {p₂ : A → Prod NT B}
                 {x y s₁ s₂} →
               [ g ] x ∈ p₁ ∙ s₁ → [ g ] y ∈ p₂ x ∙ s₂ →
               [ g ] y ∈ p₁ >>= p₂ ∙ s₁ ++ s₂
  left-sem   : ∀ {A} {p₁ p₂ : Prod NT A} {x s} →
               [ g ] x ∈ p₁ ∙ s → [ g ] x ∈ p₁ ∣ p₂ ∙ s
  right-sem  : ∀ {A} {p₁ p₂ : Prod NT A} {x s} →
               [ g ] x ∈ p₂ ∙ s → [ g ] x ∈ p₁ ∣ p₂ ∙ s
  ⋆-[]-sem   : ∀ {A} {p : Prod NT A} →
               [ g ] [] ∈ p ⋆ ∙ []
  ⋆-+-sem    : ∀ {A} {p : Prod NT A} {xs s} →
               [ g ] xs ∈ p + ∙ s → [ g ] xs ∈ p ⋆ ∙ s

-- Cast lemma.

cast : ∀ {NT g A} {p : Prod NT A} {x s₁ s₂} →
       s₁ ≡ s₂ → [ g ] x ∈ p ∙ s₁ → [ g ] x ∈ p ∙ s₂
cast P.refl = id

------------------------------------------------------------------------
-- Semantics combinators

<$>-sem : ∀ {NT} {g : Grammar NT} {A B} {f : A → B} {x p s} →
          [ g ] x ∈ p ∙ s → [ g ] f x ∈ f <$> p ∙ s
<$>-sem x∈ = ⊛-sem return-sem x∈

<$-sem : ∀ {NT g A B} {p : Prod NT B} {x : A} {y s} →
         [ g ] y ∈ p ∙ s → [ g ] x ∈ x <$ p ∙ s
<$-sem y∈ = <⊛-sem return-sem y∈

>>-sem : ∀ {NT g A B} {p₁ : Prod NT A} {p₂ : Prod NT B} {x y s₁ s₂} →
         [ g ] x ∈ p₁ ∙ s₁ → [ g ] y ∈ p₂ ∙ s₂ →
         [ g ] y ∈ p₁ >> p₂ ∙ s₁ ++ s₂
>>-sem x∈ y∈ = ⊛-sem (⊛-sem return-sem x∈) y∈

⊛>-sem : ∀ {NT g A B} {p₁ : Prod NT A} {p₂ : Prod NT B} {x y s₁ s₂} →
         [ g ] x ∈ p₁ ∙ s₁ → [ g ] y ∈ p₂ ∙ s₂ →
         [ g ] y ∈ p₁ ⊛> p₂ ∙ s₁ ++ s₂
⊛>-sem = >>-sem

+-sem : ∀ {NT g A} {p : Prod NT A} {x xs s₁ s₂} →
        [ g ] x ∈ p ∙ s₁ → [ g ] xs ∈ p ⋆ ∙ s₂ →
        [ g ] x ∷ xs ∈ p + ∙ s₁ ++ s₂
+-sem x∈ xs∈ = ⊛-sem (⊛-sem return-sem x∈) xs∈

⋆-∷-sem : ∀ {NT g A} {p : Prod NT A} {x xs s₁ s₂} →
          [ g ] x ∈ p ∙ s₁ → [ g ] xs ∈ p ⋆ ∙ s₂ →
          [ g ] x ∷ xs ∈ p ⋆ ∙ s₁ ++ s₂
⋆-∷-sem x∈ xs∈ = ⋆-+-sem (+-sem x∈ xs∈)

⋆-⋆-sem : ∀ {NT g A} {p : Prod NT A} {xs₁ xs₂ s₁ s₂} →
          [ g ] xs₁ ∈ p ⋆ ∙ s₁ → [ g ] xs₂ ∈ p ⋆ ∙ s₂ →
          [ g ] xs₁ ++ xs₂ ∈ p ⋆ ∙ s₁ ++ s₂
⋆-⋆-sem ⋆-[]-sem xs₂∈ = xs₂∈
⋆-⋆-sem (⋆-+-sem (⊛-sem (⊛-sem {s₂ = s₁} return-sem x∈) xs₁∈)) xs₂∈ =
  cast (P.sym $ LM.assoc s₁ _ _)
       (⋆-∷-sem x∈ (⋆-⋆-sem xs₁∈ xs₂∈))

+-∷-sem : ∀ {NT g A} {p : Prod NT A} {x xs s₁ s₂} →
          [ g ] x ∈ p ∙ s₁ → [ g ] xs ∈ p + ∙ s₂ →
          [ g ] x ∷ xs ∈ p + ∙ s₁ ++ s₂
+-∷-sem x∈ xs∈ = +-sem x∈ (⋆-+-sem xs∈)

+-⋆-sem : ∀ {NT g A} {p : Prod NT A} {xs₁ xs₂ s₁ s₂} →
          [ g ] xs₁ ∈ p + ∙ s₁ → [ g ] xs₂ ∈ p ⋆ ∙ s₂ →
          [ g ] xs₁ ++ xs₂ ∈ p + ∙ s₁ ++ s₂
+-⋆-sem (⊛-sem (⊛-sem {s₂ = s₁} return-sem x∈) xs₁∈) xs₂∈ =
  cast (P.sym $ LM.assoc s₁ _ _)
       (+-sem x∈ (⋆-⋆-sem xs₁∈ xs₂∈))

sep-by-sem-singleton :
  ∀ {NT g A B} {p : Prod NT A} {sep : Prod NT B} {x s} →
  [ g ] x ∈ p ∙ s → [ g ] [ x ] ∈ p sep-by sep ∙ s
sep-by-sem-singleton x∈ =
  cast (proj₂ LM.identity _) (⊛-sem (<$>-sem x∈) ⋆-[]-sem)

sep-by-sem-∷ :
  ∀ {NT g A B} {p : Prod NT A} {sep : Prod NT B} {x y xs s₁ s₂ s₃} →
  [ g ] x ∈ p ∙ s₁ → [ g ] y ∈ sep ∙ s₂ → [ g ] xs ∈ p sep-by sep ∙ s₃ →
  [ g ] x ∷ xs ∈ p sep-by sep ∙ s₁ ++ s₂ ++ s₃
sep-by-sem-∷ {s₂ = s₂} x∈ y∈ (⊛-sem (⊛-sem return-sem x′∈) xs∈) =
  ⊛-sem (<$>-sem x∈)
        (cast (LM.assoc s₂ _ _) (⋆-∷-sem (>>-sem y∈ x′∈) xs∈))

if-true-sem : ∀ {NT} {g : Grammar NT} {b}
              (t : T b) → [ g ] t ∈ if-true b ∙ []
if-true-sem {b = true}  _  = return-sem
if-true-sem {b = false} ()

sat-sem : ∀ {NT} {g : Grammar NT} {p t}
          (pt : T (p t)) → [ g ] (t , pt) ∈ sat p ∙ [ t ]
sat-sem pt = >>=-sem token-sem (<$>-sem (if-true-sem pt))

whitespace-sem-space : ∀ {NT} {g : Grammar NT} →
                       [ g ] ' ' ∈ whitespace ∙ [ ' ' ]
whitespace-sem-space = left-sem tok-sem

whitespace-sem-newline : ∀ {NT} {g : Grammar NT} →
                         [ g ] '\n' ∈ whitespace ∙ [ '\n' ]
whitespace-sem-newline = right-sem tok-sem

string-sem : ∀ {NT} {g : Grammar NT} {s} →
             [ g ] s ∈ string s ∙ s
string-sem {s = []}    = return-sem
string-sem {s = t ∷ s} = ⊛-sem (<$>-sem tok-sem) string-sem

symbol-sem : ∀ {NT} {g : Grammar NT} {s s′ s″} →
             [ g ] s″ ∈ whitespace ⋆ ∙ s′ → [ g ] s ∈ symbol s ∙ s ++ s′
symbol-sem s″∈ = <⊛-sem string-sem s″∈

------------------------------------------------------------------------
-- Some production transformers

-- Replaces all non-terminals with non-terminal-free productions.

replace : ∀ {NT A} → (∀ {A} → NT A → Prod Empty-NT A) →
          Prod NT A → Prod Empty-NT A
replace f (! nt)      = f nt
replace f fail        = fail
replace f (return x)  = return x
replace f token       = token
replace f (tok x)     = tok x
replace f (p₁ ⊛ p₂)   = replace f p₁ ⊛ replace f p₂
replace f (p₁ <⊛ p₂)  = replace f p₁ <⊛ replace f p₂
replace f (p₁ >>= p₂) = replace f p₁ >>= λ x → replace f (p₂ x)
replace f (p₁ ∣ p₂)   = replace f p₁ ∣ replace f p₂
replace f (p ⋆)       = replace f p ⋆

-- A lemma relating the resulting production with the original one in
-- case every non-terminal is replaced by fail.

replace-fail :
  ∀ {NT A g} (p : Prod NT A) {x s} →
  [ empty-grammar ] x ∈ replace (λ _ → fail) p ∙ s →
  [ g             ] x ∈                      p ∙ s
replace-fail (! nt)      ()
replace-fail fail        ()
replace-fail (return x)  return-sem      = return-sem
replace-fail token       token-sem       = token-sem
replace-fail (tok t)     tok-sem         = tok-sem
replace-fail (p₁ ⊛ p₂)   (⊛-sem f∈ x∈)   = ⊛-sem   (replace-fail p₁ f∈) (replace-fail p₂     x∈)
replace-fail (p₁ <⊛ p₂)  (<⊛-sem x∈ y∈)  = <⊛-sem  (replace-fail p₁ x∈) (replace-fail p₂     y∈)
replace-fail (p₁ >>= p₂) (>>=-sem x∈ y∈) = >>=-sem (replace-fail p₁ x∈) (replace-fail (p₂ _) y∈)
replace-fail (p₁ ∣ p₂)   (left-sem  x∈)  = left-sem  (replace-fail p₁ x∈)
replace-fail (p₁ ∣ p₂)   (right-sem x∈)  = right-sem (replace-fail p₂ x∈)
replace-fail (p ⋆)       ⋆-[]-sem        = ⋆-[]-sem
replace-fail (p ⋆)       (⋆-+-sem xs∈)   = ⋆-+-sem (replace-fail (p +) xs∈)

-- Unfolds every non-terminal. At most n /nested/ unfoldings are
-- performed.

unfold : ∀ {NT A} → (n : ℕ) → Grammar NT → Prod NT A → Prod NT A
unfold zero    g p           = p
unfold (suc n) g (! nt)      = unfold n g (g _ nt)
unfold n       g fail        = fail
unfold n       g (return x)  = return x
unfold n       g token       = token
unfold n       g (tok x)     = tok x
unfold n       g (p₁ ⊛ p₂)   = unfold n g p₁ ⊛ unfold n g p₂
unfold n       g (p₁ <⊛ p₂)  = unfold n g p₁ <⊛ unfold n g p₂
unfold n       g (p₁ >>= p₂) = unfold n g p₁ >>= λ x → unfold n g (p₂ x)
unfold n       g (p₁ ∣ p₂)   = unfold n g p₁ ∣ unfold n g p₂
unfold n       g (p ⋆)       = unfold n g p ⋆

-- Unfold is semantics-preserving.

unfold-to : ∀ {NT A} {g : Grammar NT} {x s} n (p : Prod NT A) →
            [ g ] x ∈ p ∙ s → [ g ] x ∈ unfold n g p ∙ s
unfold-to zero    p           x∈              = x∈
unfold-to (suc n) (! nt)      (!-sem x∈)      = unfold-to n _ x∈
unfold-to (suc n) fail        x∈              = x∈
unfold-to (suc n) (return x)  x∈              = x∈
unfold-to (suc n) token       x∈              = x∈
unfold-to (suc n) (tok x)     x∈              = x∈
unfold-to (suc n) (p₁ ⊛ p₂)   (⊛-sem f∈ x∈)   = ⊛-sem (unfold-to (suc n) p₁ f∈)
                                                      (unfold-to (suc n) p₂ x∈)
unfold-to (suc n) (p₁ <⊛ p₂)  (<⊛-sem x∈ y∈)  = <⊛-sem (unfold-to (suc n) p₁ x∈)
                                                       (unfold-to (suc n) p₂ y∈)
unfold-to (suc n) (p₁ >>= p₂) (>>=-sem x∈ y∈) = >>=-sem (unfold-to (suc n) p₁ x∈)
                                                        (unfold-to (suc n) (p₂ _) y∈)
unfold-to (suc n) (p₁ ∣ p₂)   (left-sem x∈)   = left-sem  (unfold-to (suc n) p₁ x∈)
unfold-to (suc n) (p₁ ∣ p₂)   (right-sem x∈)  = right-sem (unfold-to (suc n) p₂ x∈)
unfold-to (suc n) (p ⋆)       ⋆-[]-sem        = ⋆-[]-sem
unfold-to (suc n) (p ⋆)       (⋆-+-sem xs∈)   = ⋆-+-sem (unfold-to (suc n) (p +) xs∈)

unfold-from : ∀ {NT A} {g : Grammar NT} {x s} n (p : Prod NT A) →
              [ g ] x ∈ unfold n g p ∙ s → [ g ] x ∈ p ∙ s
unfold-from zero    p           x∈              = x∈
unfold-from (suc n) (! nt)      x∈              = !-sem (unfold-from n _ x∈)
unfold-from (suc n) fail        x∈              = x∈
unfold-from (suc n) (return x)  x∈              = x∈
unfold-from (suc n) token       x∈              = x∈
unfold-from (suc n) (tok x)     x∈              = x∈
unfold-from (suc n) (p₁ ⊛ p₂)   (⊛-sem f∈ x∈)   = ⊛-sem (unfold-from (suc n) p₁ f∈)
                                                        (unfold-from (suc n) p₂ x∈)
unfold-from (suc n) (p₁ <⊛ p₂)  (<⊛-sem x∈ y∈)  = <⊛-sem (unfold-from (suc n) p₁ x∈)
                                                         (unfold-from (suc n) p₂ y∈)
unfold-from (suc n) (p₁ >>= p₂) (>>=-sem x∈ y∈) = >>=-sem (unfold-from (suc n) p₁ x∈)
                                                          (unfold-from (suc n) (p₂ _) y∈)
unfold-from (suc n) (p₁ ∣ p₂)   (left-sem x∈)   = left-sem  (unfold-from (suc n) p₁ x∈)
unfold-from (suc n) (p₁ ∣ p₂)   (right-sem x∈)  = right-sem (unfold-from (suc n) p₂ x∈)
unfold-from (suc n) (p ⋆)       ⋆-[]-sem        = ⋆-[]-sem
unfold-from (suc n) (p ⋆)       (⋆-+-sem xs∈)   = ⋆-+-sem (unfold-from (suc n) (p +) xs∈)

------------------------------------------------------------------------
-- Nullability

-- A production is nullable (with respect to a given grammar) if the
-- empty string is a member of the language defined by the production.

Nullable : ∀ {NT A} → Grammar NT → Prod NT A → Set₁
Nullable g p = ∃ λ x → [ g ] x ∈ p ∙ []

-- Nullability is not decidable, not even for productions without
-- non-terminals. If nullability were decidable, then we could decide
-- if a given function of type ℕ → Bool always returns false.

nullability-not-decidable :
  (∀ {A} (p : Prod Empty-NT A) → Dec (Nullable empty-grammar p)) →
  (f : ℕ → Bool) → Dec (∀ n → f n ≡ false)
nullability-not-decidable dec f = goal
  where
  p : Prod Empty-NT ℕ
  p = return tt ⋆ >>= λ tts →
      let n = length tts in
      if f n then return n else fail

  true-lemma : ∀ {n s} → [ empty-grammar ] n ∈ p ∙ s → f n ≡ true
  true-lemma (>>=-sem {x = tts} _ _)
    with f (length tts) | P.inspect f (length tts)
  true-lemma (>>=-sem _ return-sem) | true  | P.[ fn≡true ] = fn≡true
  true-lemma (>>=-sem _ ())         | false | _

  no-lemma : ∀ {n} → f n ≡ true → ¬ (∀ n → f n ≡ false)
  no-lemma {n} ≡true ≡false with begin
    true   ≡⟨ P.sym ≡true ⟩
    f n    ≡⟨ ≡false n ⟩
    false  ∎
    where open P.≡-Reasoning
  ... | ()

  to-tts : ℕ → List ⊤
  to-tts n = replicate n tt

  n∈₁ : ∀ n → [ empty-grammar ] to-tts n ∈ return tt ⋆ ∙ []
  n∈₁ zero    = ⋆-[]-sem
  n∈₁ (suc n) = ⋆-∷-sem return-sem (n∈₁ n)

  n∈₂ : ∀ n → f n ≡ true →
        let n′ = length (replicate n tt) in
        [ empty-grammar ] n ∈ if f n′ then return n′ else fail ∙ []
  n∈₂ n fn≡true rewrite length-replicate n {x = tt} | fn≡true =
    return-sem

  yes-lemma : ∀ n → ¬ ([ empty-grammar ] n ∈ p ∙ []) → f n ≢ true
  yes-lemma n n∉ fn≡true = n∉ (>>=-sem (n∈₁ n) (n∈₂ n fn≡true))

  goal : Dec (∀ n → f n ≡ false)
  goal with dec p
  ... | yes (_ , n∈) = no (no-lemma (true-lemma n∈))
  ... | no ¬[]∈      = yes λ n → ¬-not (yes-lemma n (¬[]∈ ∘ ,_))

-- However, we can implement a procedure that either proves that a
-- production is nullable, or returns "don't know" as the answer.
--
-- Note that, in the case of bind, the second argument is only applied
-- to one input—the first argument could give rise to infinitely many
-- results (as in the example above).
--
-- Note also that no attempt is made to memoise non-terminals—the
-- grammar could consist of an infinite number of non-terminals.
-- Instead the grammar is unfolded a certain number of times (n).
-- Memoisation still seems like a useful heuristic, but requires that
-- equality of non-terminals is decidable.

nullable? : ∀ {NT A} (n : ℕ) (g : Grammar NT) (p : Prod NT A) →
            Maybe (Nullable g p)
nullable? {NT} n g p =
  Product.map id (unfold-from n _) <$>M null? (unfold n g p)
  where
  null? : ∀ {A} (p : Prod NT A) → Maybe (Nullable g p)
  null? (! nt)        = nothing
  null? fail          = nothing
  null? token         = nothing
  null? (tok t)       = nothing
  null? (return x)    = just (x , return-sem)
  null? (p ⋆)         = just ([] , ⋆-[]-sem)
  null? (p₁ ⊛ p₂)     = Product.zip _$_   ⊛-sem  <$>M null? p₁ ⊛M null? p₂
  null? (p₁ <⊛ p₂)    = Product.zip const <⊛-sem <$>M null? p₁ ⊛M null? p₂
  null? (p₁ >>= p₂)   = null? p₁                  >>=M λ { (x , x∈) →
                        null? (p₂ x)              >>=M λ { (y , y∈) →
                        just (y , >>=-sem x∈ y∈)  }}
  null? (p₁ ∣ p₂)     = (Product.map id left-sem  <$>M null? p₁)
                          ∣M
                        (Product.map id right-sem <$>M null? p₂)

------------------------------------------------------------------------
-- Detecting the whitespace combinator

-- A predicate for the whitespace combinator.

data Is-whitespace {NT} : ∀ {A} → Prod NT A → Set₁ where
  is-whitespace : Is-whitespace whitespace

-- Detects the whitespace combinator.

is-whitespace? : ∀ {NT A} (p : Prod NT A) → Maybe (Is-whitespace p)
is-whitespace? {NT} (tok ' ' ∣ p) = helper p P.refl
  where
  helper : ∀ {A} (p : Prod NT A) (eq : A ≡ Char) →
           Maybe (Is-whitespace (tok ' ' ∣ P.subst (Prod NT) eq p))
  helper (tok '\n') P.refl = just is-whitespace
  helper _          _      = nothing

is-whitespace? _ = nothing

------------------------------------------------------------------------
-- Trailing whitespace

-- A predicate for productions that can "swallow" extra trailing
-- whitespace.

Trailing-whitespace : ∀ {NT A} → Grammar NT → Prod NT A → Set₁
Trailing-whitespace g p =
  ∀ {x s} → [ g ] x ∈ p <⊛ whitespace ⋆ ∙ s → [ g ] x ∈ p ∙ s

-- A heuristic procedure that either proves that a production can
-- swallow trailing whitespace, or returns "don't know" as the answer.

trailing-whitespace? :
  ∀ {NT A} (n : ℕ) (g : Grammar NT) (p : Prod NT A) →
  Maybe (Trailing-whitespace g p)
trailing-whitespace? {NT} n g p =
  convert ∘ unfold-lemma <$>M trailing? (unfold n g p)
  where
  -- An alternative formulation of Trailing-whitespace.

  Trailing-whitespace′ : ∀ {NT A} → Grammar NT → Prod NT A → Set₁
  Trailing-whitespace′ g p =
    ∀ {x s₁ s₂ s} →
    [ g ] x ∈ p ∙ s₁ → [ g ] s ∈ whitespace ⋆ ∙ s₂ →
    [ g ] x ∈ p ∙ s₁ ++ s₂

  convert : ∀ {NT A} {g : Grammar NT} {p : Prod NT A} →
            Trailing-whitespace′ g p → Trailing-whitespace g p
  convert t (<⊛-sem x∈ w) = t x∈ w

  ++-lemma = solve 2 (λ a b → (a ⊕ b) ⊕ nil ⊜ (a ⊕ nil) ⊕ b) P.refl
    where open List-solver

  unfold-lemma : Trailing-whitespace′ g (unfold n g p) →
                 Trailing-whitespace′ g p
  unfold-lemma t x∈ white = unfold-from n _ (t (unfold-to n _ x∈) white)

  ⊛-return-lemma :
    ∀ {A B} {p : Prod NT (A → B)} {x} →
    Trailing-whitespace′ g p →
    Trailing-whitespace′ g (p ⊛ return x)
  ⊛-return-lemma t (⊛-sem {s₁ = s₁} f∈ return-sem) white =
    cast (++-lemma s₁ _) (⊛-sem (t f∈ white) return-sem)

  +-lemma :
    ∀ {A} {p : Prod NT A} →
    Trailing-whitespace′ g p →
    Trailing-whitespace′ g (p +)
  +-lemma t (⊛-sem (⊛-sem {s₂ = s₁} return-sem x∈) ⋆-[]-sem) white =
    cast (++-lemma s₁ _) (+-sem (t x∈ white) ⋆-[]-sem)
  +-lemma t (⊛-sem (⊛-sem {s₂ = s₁} return-sem x∈) (⋆-+-sem xs∈))
          white =
    cast (P.sym $ LM.assoc s₁ _ _)
         (+-∷-sem x∈ (+-lemma t xs∈ white))

  ⊛-⋆-lemma :
    ∀ {A B} {p₁ : Prod NT (List A → B)} {p₂ : Prod NT A} →
    Trailing-whitespace′ g p₁ →
    Trailing-whitespace′ g p₂ →
    Trailing-whitespace′ g (p₁ ⊛ p₂ ⋆)
  ⊛-⋆-lemma t₁ t₂ (⊛-sem {s₁ = s₁} f∈ ⋆-[]-sem) white =
    cast (++-lemma s₁ _) (⊛-sem (t₁ f∈ white) ⋆-[]-sem)
  ⊛-⋆-lemma t₁ t₂ (⊛-sem {s₁ = s₁} f∈ (⋆-+-sem xs∈)) white =
    cast (P.sym $ LM.assoc s₁ _ _)
         (⊛-sem f∈ (⋆-+-sem (+-lemma t₂ xs∈ white)))

  ⊛-∣-lemma : ∀ {A B} {p₁ : Prod NT (A → B)} {p₂ p₃ : Prod NT A} →
              Trailing-whitespace′ g (p₁ ⊛ p₂) →
              Trailing-whitespace′ g (p₁ ⊛ p₃) →
              Trailing-whitespace′ g (p₁ ⊛ (p₂ ∣ p₃))
  ⊛-∣-lemma t₁₂ t₁₃ {s₂ = s₃}
    (⊛-sem {f = f} {x = x} {s₁ = s₁} {s₂ = s₂} f∈ (left-sem x∈))
    white
    with f x | (s₁ ++ s₂) ++ s₃ | t₁₂ (⊛-sem f∈ x∈) white
  ... | ._ | ._ | ⊛-sem f∈′ x∈′ = ⊛-sem f∈′ (left-sem x∈′)
  ⊛-∣-lemma t₁₂ t₁₃ {s₂ = s₃}
    (⊛-sem {f = f} {x = x} {s₁ = s₁} {s₂ = s₂} f∈ (right-sem x∈))
    white
    with f x | (s₁ ++ s₂) ++ s₃ | t₁₃ (⊛-sem f∈ x∈) white
  ... | ._ | ._ | ⊛-sem f∈′ x∈′ = ⊛-sem f∈′ (right-sem x∈′)

  ⊛-lemma : ∀ {A B} {p₁ : Prod NT (A → B)} {p₂ : Prod NT A} →
            Trailing-whitespace′ g p₂ →
            Trailing-whitespace′ g (p₁ ⊛ p₂)
  ⊛-lemma t₂ (⊛-sem {s₁ = s₁} f∈ x∈) white =
    cast (P.sym $ LM.assoc s₁ _ _)
         (⊛-sem f∈ (t₂ x∈ white))

  <⊛-return-lemma :
    ∀ {A B} {p : Prod NT A} {x : B} →
    Trailing-whitespace′ g p →
    Trailing-whitespace′ g (p <⊛ return x)
  <⊛-return-lemma t (<⊛-sem {s₁ = s₁} f∈ return-sem) white =
    cast (++-lemma s₁ _) (<⊛-sem (t f∈ white) return-sem)

  <⊛-⋆-lemma :
    ∀ {A B} {p₁ : Prod NT A} {p₂ : Prod NT B} →
    Is-whitespace p₂ →
    Trailing-whitespace′ g (p₁ <⊛ p₂ ⋆)
  <⊛-⋆-lemma is-whitespace (<⊛-sem {s₁ = s₁} x∈ white₁) white₂ =
    cast (P.sym $ LM.assoc s₁ _ _)
         (<⊛-sem x∈ (⋆-⋆-sem white₁ white₂))

  <⊛-lemma : ∀ {A B} {p₁ : Prod NT A} {p₂ : Prod NT B} →
             Trailing-whitespace′ g p₂ →
             Trailing-whitespace′ g (p₁ <⊛ p₂)
  <⊛-lemma t₂ (<⊛-sem {s₁ = s₁} f∈ x∈) white =
    cast (P.sym $ LM.assoc s₁ _ _)
         (<⊛-sem f∈ (t₂ x∈ white))

  fail->>=-lemma : ∀ {A B} {p : A → Prod NT B} →
                   Trailing-whitespace′ g (fail >>= p)
  fail->>=-lemma (>>=-sem () _)

  return->>=-lemma : ∀ {A B} {p : A → Prod NT B} {x} →
                     Trailing-whitespace′ g (p x) →
                     Trailing-whitespace′ g (return x >>= p)
  return->>=-lemma t (>>=-sem return-sem y∈) white =
    >>=-sem return-sem (t y∈ white)

  tok->>=-lemma : ∀ {A} {p : Char → Prod NT A} {t} →
                  Trailing-whitespace′ g (p t) →
                  Trailing-whitespace′ g (tok t >>= p)
  tok->>=-lemma t (>>=-sem tok-sem y∈) white =
    >>=-sem tok-sem (t y∈ white)

  ∣-lemma : ∀ {A} {p₁ p₂ : Prod NT A} →
            Trailing-whitespace′ g p₁ →
            Trailing-whitespace′ g p₂ →
            Trailing-whitespace′ g (p₁ ∣ p₂)
  ∣-lemma t₁ t₂ (left-sem  x∈) white = left-sem  (t₁ x∈ white)
  ∣-lemma t₁ t₂ (right-sem x∈) white = right-sem (t₂ x∈ white)

  trailing? : ∀ {A} (p : Prod NT A) →
              Maybe (Trailing-whitespace′ g p)
  trailing? fail             = just (λ ())
  trailing? (p ⊛ return x)   = ⊛-return-lemma <$>M trailing? p
  trailing? (p₁ ⊛ p₂ ⋆)      = ⊛-⋆-lemma <$>M trailing? p₁ ⊛M trailing? p₂
  trailing? (p₁ ⊛ (p₂ ∣ p₃)) = ⊛-∣-lemma <$>M trailing? (p₁ ⊛ p₂)
                                           ⊛M trailing? (p₁ ⊛ p₃)
  trailing? (p₁ ⊛ p₂)        = ⊛-lemma <$>M trailing? p₂
  trailing? (p <⊛ return x)  = <⊛-return-lemma <$>M trailing? p
  trailing? (p₁ <⊛ p₂ ⋆)     = <⊛-⋆-lemma <$>M is-whitespace? p₂
  trailing? (p₁ <⊛ p₂)       = <⊛-lemma <$>M trailing? p₂
  trailing? (fail >>= p)     = just fail->>=-lemma
  trailing? (return x >>= p) = return->>=-lemma <$>M trailing? (p x)
  trailing? (tok t >>= p)    = tok->>=-lemma <$>M trailing? (p t)
  trailing? (p₁ ∣ p₂)        = ∣-lemma <$>M trailing? p₁ ⊛M trailing? p₂
  trailing? _                = nothing
