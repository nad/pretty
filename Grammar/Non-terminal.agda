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

open import Tests

------------------------------------------------------------------------
-- Grammars

-- Productions. (Note that productions can contain choices.)

infix  30 _⋆
infixl 20 _⊛_
infixl 15 _>>=_
infixl 10 _∣_

data Prod (NT : Set → Set₁) : Set → Set₁ where
  !      : ∀ {A} → NT A → Prod NT A
  fail   : ∀ {A} → Prod NT A
  return : ∀ {A} → A → Prod NT A
  token  : Prod NT Char
  tok    : Char → Prod NT Char
  _⊛_    : ∀ {A B} → Prod NT (A → B) → Prod NT A → Prod NT B
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

infixl 20 _<$>_
infixr 20 _<$_

_<$>_ : ∀ {NT A B} → (A → B) → Prod NT A → Prod NT B
f <$> p = return f ⊛ p

_<$_ : ∀ {NT A B} → A → Prod NT B → Prod NT A
x <$ p = const x <$> p

-- Various sequencing operators.

infixl 20 _<⊛_ _⊛>_
infixl 15 _>>_

_>>_ : ∀ {NT A B} → Prod NT A → Prod NT B → Prod NT B
p₁ >> p₂ = (λ _ x → x) <$> p₁ ⊛ p₂

_<⊛_ : ∀ {NT A B} → Prod NT A → Prod NT B → Prod NT A
p₁ <⊛ p₂ = (λ x _ → x) <$> p₁ ⊛ p₂

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
  !-sem       : ∀ {A} {nt : NT A} {x s} →
                [ g ] x ∈ g A nt ∙ s → [ g ] x ∈ ! nt ∙ s
  return-sem  : ∀ {A} {x : A} → [ g ] x ∈ return x ∙ []
  token-sem   : ∀ {t} → [ g ] t ∈ token ∙ t ∷ []
  tok-sem     : ∀ {t} → [ g ] t ∈ tok t ∙ t ∷ []
  ⊛-sem       : ∀ {A B} {p₁ : Prod NT (A → B)} {p₂ : Prod NT A}
                  {f x s₁ s₂} →
                [ g ] f ∈ p₁ ∙ s₁ → [ g ] x ∈ p₂ ∙ s₂ →
                [ g ] f x ∈ p₁ ⊛ p₂ ∙ s₁ ++ s₂
  >>=-sem     : ∀ {A B} {p₁ : Prod NT A} {p₂ : A → Prod NT B}
                  {x y s₁ s₂} →
                [ g ] x ∈ p₁ ∙ s₁ → [ g ] y ∈ p₂ x ∙ s₂ →
                [ g ] y ∈ p₁ >>= p₂ ∙ s₁ ++ s₂
  ∣-left-sem  : ∀ {A} {p₁ p₂ : Prod NT A} {x s} →
                [ g ] x ∈ p₁ ∙ s → [ g ] x ∈ p₁ ∣ p₂ ∙ s
  ∣-right-sem : ∀ {A} {p₁ p₂ : Prod NT A} {x s} →
                [ g ] x ∈ p₂ ∙ s → [ g ] x ∈ p₁ ∣ p₂ ∙ s
  ⋆-[]-sem    : ∀ {A} {p : Prod NT A} →
                [ g ] [] ∈ p ⋆ ∙ []
  ⋆-∷-sem     : ∀ {A} {p : Prod NT A} {x xs s₁ s₂} →
                [ g ] x ∈ p ∙ s₁ → [ g ] xs ∈ p ⋆ ∙ s₂ →
                [ g ] x ∷ xs ∈ p ⋆ ∙ s₁ ++ s₂

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
<$-sem = <$>-sem

>>-sem : ∀ {NT g A B} {p₁ : Prod NT A} {p₂ : Prod NT B} {x y s₁ s₂} →
         [ g ] x ∈ p₁ ∙ s₁ → [ g ] y ∈ p₂ ∙ s₂ →
         [ g ] y ∈ p₁ >> p₂ ∙ s₁ ++ s₂
>>-sem x∈ y∈ = ⊛-sem (⊛-sem return-sem x∈) y∈

<⊛-sem : ∀ {NT g A B} {p₁ : Prod NT A} {p₂ : Prod NT B}
           {x y s₁ s₂} →
         [ g ] x ∈ p₁ ∙ s₁ → [ g ] y ∈ p₂ ∙ s₂ →
         [ g ] x ∈ p₁ <⊛ p₂ ∙ s₁ ++ s₂
<⊛-sem x∈ y∈ = ⊛-sem (⊛-sem return-sem x∈) y∈

⊛>-sem : ∀ {NT g A B} {p₁ : Prod NT A} {p₂ : Prod NT B} {x y s₁ s₂} →
         [ g ] x ∈ p₁ ∙ s₁ → [ g ] y ∈ p₂ ∙ s₂ →
         [ g ] y ∈ p₁ ⊛> p₂ ∙ s₁ ++ s₂
⊛>-sem = >>-sem

+-sem : ∀ {NT g A} {p : Prod NT A} {x xs s₁ s₂} →
        [ g ] x ∈ p ∙ s₁ → [ g ] xs ∈ p ⋆ ∙ s₂ →
        [ g ] x ∷ xs ∈ p + ∙ s₁ ++ s₂
+-sem x∈ xs∈ = ⊛-sem (<$>-sem x∈) xs∈

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
          (pt : T (p t)) → [ g ] (t , pt) ∈ sat p ∙ t ∷ []
sat-sem pt = >>=-sem token-sem (<$>-sem (if-true-sem pt))

whitespace-sem-space : ∀ {NT} {g : Grammar NT} →
                       [ g ] ' ' ∈ whitespace ∙ [ ' ' ]
whitespace-sem-space = ∣-left-sem tok-sem

whitespace-sem-newline : ∀ {NT} {g : Grammar NT} →
                         [ g ] '\n' ∈ whitespace ∙ [ '\n' ]
whitespace-sem-newline = ∣-right-sem tok-sem

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
replace-fail (return x)  return-sem       = return-sem
replace-fail token       token-sem        = token-sem
replace-fail (tok t)     tok-sem          = tok-sem
replace-fail (p₁ ⊛ p₂)   (⊛-sem f∈ x∈)    = ⊛-sem   (replace-fail p₁ f∈) (replace-fail p₂     x∈)
replace-fail (p₁ >>= p₂) (>>=-sem x∈ y∈)  = >>=-sem (replace-fail p₁ x∈) (replace-fail (p₂ _) y∈)
replace-fail (p₁ ∣ p₂)   (∣-left-sem  x∈) = ∣-left-sem  (replace-fail p₁ x∈)
replace-fail (p₁ ∣ p₂)   (∣-right-sem x∈) = ∣-right-sem (replace-fail p₂ x∈)
replace-fail (p ⋆)       ⋆-[]-sem         = ⋆-[]-sem
replace-fail (p ⋆)       (⋆-∷-sem x∈ xs∈) =
  ⋆-∷-sem (replace-fail p x∈) (replace-fail (p ⋆) xs∈)

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
unfold n       g (p₁ >>= p₂) = unfold n g p₁ >>= λ x → unfold n g (p₂ x)
unfold n       g (p₁ ∣ p₂)   = unfold n g p₁ ∣ unfold n g p₂
unfold n       g (p ⋆)       = unfold n g p ⋆

-- Unfold is semantics-preserving.

unfold-to : ∀ {NT A} {g : Grammar NT} {x s} n (p : Prod NT A) →
            [ g ] x ∈ p ∙ s → [ g ] x ∈ unfold n g p ∙ s
unfold-to zero    p           x∈               = x∈
unfold-to (suc n) (! nt)      (!-sem x∈)       = unfold-to n _ x∈
unfold-to (suc n) fail        x∈               = x∈
unfold-to (suc n) (return x)  x∈               = x∈
unfold-to (suc n) token       x∈               = x∈
unfold-to (suc n) (tok x)     x∈               = x∈
unfold-to (suc n) (p₁ ⊛ p₂)   (⊛-sem f∈ x∈)    = ⊛-sem (unfold-to (suc n) p₁ f∈)
                                                       (unfold-to (suc n) p₂ x∈)
unfold-to (suc n) (p₁ >>= p₂) (>>=-sem x∈ y∈)  = >>=-sem (unfold-to (suc n) p₁ x∈)
                                                         (unfold-to (suc n) (p₂ _) y∈)
unfold-to (suc n) (p₁ ∣ p₂)   (∣-left-sem x∈)  = ∣-left-sem  (unfold-to (suc n) p₁ x∈)
unfold-to (suc n) (p₁ ∣ p₂)   (∣-right-sem x∈) = ∣-right-sem (unfold-to (suc n) p₂ x∈)
unfold-to (suc n) (p ⋆)       ⋆-[]-sem         = ⋆-[]-sem
unfold-to (suc n) (p ⋆)       (⋆-∷-sem x∈ xs∈) = ⋆-∷-sem (unfold-to (suc n) p x∈)
                                                         (unfold-to (suc n) (p ⋆) xs∈)

unfold-from : ∀ {NT A} {g : Grammar NT} {x s} n (p : Prod NT A) →
              [ g ] x ∈ unfold n g p ∙ s → [ g ] x ∈ p ∙ s
unfold-from zero    p           x∈               = x∈
unfold-from (suc n) (! nt)      x∈               = !-sem (unfold-from n _ x∈)
unfold-from (suc n) fail        x∈               = x∈
unfold-from (suc n) (return x)  x∈               = x∈
unfold-from (suc n) token       x∈               = x∈
unfold-from (suc n) (tok x)     x∈               = x∈
unfold-from (suc n) (p₁ ⊛ p₂)   (⊛-sem f∈ x∈)    = ⊛-sem (unfold-from (suc n) p₁ f∈)
                                                         (unfold-from (suc n) p₂ x∈)
unfold-from (suc n) (p₁ >>= p₂) (>>=-sem x∈ y∈)  = >>=-sem (unfold-from (suc n) p₁ x∈)
                                                           (unfold-from (suc n) (p₂ _) y∈)
unfold-from (suc n) (p₁ ∣ p₂)   (∣-left-sem x∈)  = ∣-left-sem  (unfold-from (suc n) p₁ x∈)
unfold-from (suc n) (p₁ ∣ p₂)   (∣-right-sem x∈) = ∣-right-sem (unfold-from (suc n) p₂ x∈)
unfold-from (suc n) (p ⋆)       ⋆-[]-sem         = ⋆-[]-sem
unfold-from (suc n) (p ⋆)       (⋆-∷-sem x∈ xs∈) = ⋆-∷-sem (unfold-from (suc n) p x∈)
                                                           (unfold-from (suc n) (p ⋆) xs∈)

------------------------------------------------------------------------
-- Nullability

-- A production is nullable (with respect to a given grammar) if the
-- empty string is a member of the language defined by the production.

Nullable : ∀ {NT A} → Grammar NT → Prod NT A → Set₁
Nullable g p = ∃ λ x → [ g ] x ∈ p ∙ []

-- Nullability is not decidable. If nullability were decidable, then
-- we could decide if a given function of type ℕ → Bool always returns
-- false.

nullability-not-decidable :
  (∀ {NT A} (g : Grammar NT) (p : Prod NT A) →
   Dec (Nullable g p)) →
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
  goal with dec empty-grammar p
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
nullable? n g p =
  Product.map id (unfold-from n _ ∘ replace-fail _) <$>M
    null? (replace (λ _ → fail) (unfold n g p))
  where
  null? : ∀ {A} (p : Prod Empty-NT A) → Maybe (Nullable empty-grammar p)
  null? fail          = nothing
  null? token         = nothing
  null? (tok t)       = nothing
  null? (return x)    = just (x , return-sem)
  null? (p ⋆)         = just ([] , ⋆-[]-sem)
  null? (p₁ ⊛ p₂)     = Product.zip _$_ ⊛-sem <$>M null? p₁ ⊛M null? p₂
  null? (p₁ >>= p₂)   = null? p₁                  >>=M λ { (x , x∈) →
                        null? (p₂ x)              >>=M λ { (y , y∈) →
                        just (y , >>=-sem x∈ y∈)  }}
  null? (p₁ ∣ p₂)     = (Product.map id ∣-left-sem  <$>M null? p₁)
                          ∣M
                        (Product.map id ∣-right-sem <$>M null? p₂)
  null? (! (lift ()))