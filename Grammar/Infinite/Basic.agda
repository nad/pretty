------------------------------------------------------------------------
-- "Basic" infinite grammars
------------------------------------------------------------------------

-- For a larger and possibly more convenient, but equivalent, grammar
-- interface, see Grammar.Infinite.

{-# OPTIONS --guardedness #-}

module Grammar.Infinite.Basic where

open import Algebra
open import Category.Monad
open import Codata.Musical.Notation
open import Data.Bool
open import Data.Char
open import Data.Empty
open import Data.List as List
import Data.List.Any as Any
open import Data.List.Any.Properties
import Data.List.Categorical
open import Data.List.Membership.Propositional
import Data.List.Membership.Propositional.Properties as ∈
open import Data.List.Properties
open import Data.Nat
open import Data.Nat.Properties as NatP
open import Data.Product as Prod
import Data.Product.Function.Dependent.Propositional as Σ
open import Data.Product.Function.NonDependent.Propositional
open import Data.Sum
open import Data.Unit using (tt)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; module Inverse)
import Function.Related as Related
open import Function.Related.TypeIsomorphisms
import Level
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
import Relation.Binary.PropositionalEquality.WithK as P
open import Relation.Nullary

private
  module LMi {A : Set} = Monoid (++-monoid A)
  module LMa = RawMonad (Data.List.Categorical.monad {ℓ = Level.zero})
open Any.Any

------------------------------------------------------------------------
-- Simple, potentially infinite grammars

-- These grammars are very general: they can represent every
-- recursively enumerable language (see Grammars.Infinite.expressive).
-- In practice one may want to restrict attention to languages that
-- can be parsed. I use general grammars to illustrate that this
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

-- Semantics of grammars (parse trees). Here x ∈ g · s means that the
-- value x and string s are generated by the grammar g.

infix 4 _∈_·_

data _∈_·_ : ∀ {A} → A → Grammar A → List Char → Set₁ where
  return-sem : ∀ {A} {x : A} → x ∈ return x · []
  token-sem  : ∀ {t} → t ∈ token · [ t ]
  >>=-sem    : ∀ {A B x y s₁ s₂} {g₁ : ∞ (Grammar A)}
                 {g₂ : A → ∞ (Grammar B)} →
               x ∈ ♭ g₁ · s₁ → y ∈ ♭ (g₂ x) · s₂ →
               y ∈ g₁ >>= g₂ · s₁ ++ s₂
  left-sem   : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x s} →
               x ∈ ♭ g₁ · s → x ∈ g₁ ∣ g₂ · s
  right-sem  : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x s} →
               x ∈ ♭ g₂ · s → x ∈ g₁ ∣ g₂ · s

----------------------------------------------------------------------
-- Some grammar combinators

-- Failure.

fail : ∀ {A} → Grammar A
fail = ♯ fail ∣ ♯ fail

-- Map.

infixl 20 _<$>_ _<$_

_<$>_ : ∀ {A B} → (A → B) → Grammar A → Grammar B
f <$> g = ♯ g >>= λ x → ♯ return (f x)

_<$_ : ∀ {A B} → A → Grammar B → Grammar A
x <$ g = const x <$> g

-- The empty string if the argument is true, otherwise failure.

if-true : (b : Bool) → Grammar (T b)
if-true true  = return tt
if-true false = fail

-- A token satisfying a given predicate.

sat : (p : Char → Bool) → Grammar (∃ λ t → T (p t))
sat p = ♯ token >>= λ t → ♯ (_,_ t <$> if-true (p t))

-- A specific token.

tok : Char → Grammar Char
tok t = t <$ sat (λ t′ → t == t′)

------------------------------------------------------------------------
-- Some semantics combinators

-- Cast lemma.

cast : ∀ {A} {g : Grammar A} {x s₁ s₂} →
       s₁ ≡ s₂ → x ∈ g · s₁ → x ∈ g · s₂
cast refl = id

fail-sem⁻¹ : ∀ {A} {x : A} {s} → ¬ (x ∈ fail · s)
fail-sem⁻¹ (left-sem  ∈fail) = fail-sem⁻¹ ∈fail
fail-sem⁻¹ (right-sem ∈fail) = fail-sem⁻¹ ∈fail

<$>-sem : ∀ {A B} {f : A → B} {g : Grammar A} {y s} →
          y ∈ f <$> g · s ↔ ∃ λ x → x ∈ g · s × y ≡ f x
<$>-sem {A} {B} {f} {g} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
  lemma : ∀ s → s ++ [] ≡ s
  lemma s = proj₂ LMi.identity s

  to : ∀ {s g y} → y ∈ f <$> g · s → ∃ λ x → x ∈ g · s × y ≡ f x
  to (>>=-sem x∈ return-sem) =
    _ , cast (P.sym $ lemma _) x∈ , refl

  from : ∀ {s y g} → (∃ λ x → x ∈ g · s × y ≡ f x) → y ∈ f <$> g · s
  from (x , x∈ , refl) = cast (lemma _) (>>=-sem x∈ return-sem)

  >>=-cast : ∀ {x y s₁ s₂ s}
               {g₁ : ∞ (Grammar A)} {g₂ : A → ∞ (Grammar B)}
             (eq : s₁ ≡ s₂)
             (x∈ : x ∈ ♭ g₁ · s₁) (y∈ : y ∈ ♭ (g₂ x) · s) →
             >>=-sem {g₁ = g₁} {g₂ = g₂} (cast eq x∈) y∈ ≡
             cast (P.cong (λ s′ → s′ ++ s) eq) (>>=-sem x∈ y∈)
  >>=-cast refl _ _ = refl

  cast-cast : ∀ {A g s₁ s₂} {z : A} {z∈ : z ∈ g · s₂}
              (eq₁ : s₁ ≡ s₂) (eq₂ : s₂ ≡ s₁) →
              cast eq₁ (cast eq₂ z∈) ≡ z∈
  cast-cast refl refl = refl

  from∘to : ∀ {s g y} (y∈ : y ∈ f <$> g · s) → from (to y∈) ≡ y∈
  from∘to (>>=-sem {s₁ = s} x∈ return-sem) = begin
    cast (lemma (s ++ []))
         (>>=-sem (cast (P.sym $ lemma s) x∈) return-sem)  ≡⟨ P.cong (cast (lemma (s ++ []))) $
                                                                     >>=-cast (P.sym (lemma s)) x∈ return-sem ⟩
    cast (lemma (s ++ []))
         (cast (P.cong (λ s → s ++ []) (P.sym $ lemma s))
               (>>=-sem x∈ return-sem))                    ≡⟨ cast-cast (lemma (s ++ []))
                                                                        (P.cong (λ s → s ++ []) (P.sym $ lemma s)) ⟩
    >>=-sem x∈ return-sem                                  ∎
    where open P.≡-Reasoning

  to-cast : ∀ {s₁ s₂ y g} (eq : s₁ ≡ s₂) (y∈ : y ∈ f <$> g · s₁) →
            to (cast eq y∈) ≡
            P.subst (λ s → ∃ λ x → x ∈ g · s × y ≡ f x) eq (to y∈)
  to-cast refl y∈ = refl

  to∘from : ∀ {s y g}
            (x∈ : ∃ λ x → x ∈ g · s × y ≡ f x) → to (from x∈) ≡ x∈
  to∘from {s} (x , x∈ , refl)
    rewrite to-cast (lemma s) (>>=-sem x∈ return-sem)
          | lemma s
    = refl

if-true-sem : ∀ {b} x {s} → x ∈ if-true b · s ↔ s ≡ []
if-true-sem x = record
  { to         = P.→-to-⟶ (to _)
  ; from       = P.→-to-⟶ (from _ _)
  ; inverse-of = record
    { left-inverse-of  = from∘to _
    ; right-inverse-of = to∘from _ x
    }
  }
  where
  to : ∀ b {x s} → x ∈ if-true b · s → s ≡ []
  to true  return-sem = refl
  to false ∈fail      = ⊥-elim $ fail-sem⁻¹ ∈fail

  from : ∀ b x {s} → s ≡ [] → x ∈ if-true b · s
  from true  _  refl = return-sem
  from false () refl

  from∘to : ∀ b {x s} (x∈ : x ∈ if-true b · s) → from b x (to b x∈) ≡ x∈
  from∘to true  return-sem = refl
  from∘to false ∈fail      = ⊥-elim $ fail-sem⁻¹ ∈fail

  to∘from : ∀ b x {s} (eq : s ≡ []) → to b (from b x eq) ≡ eq
  to∘from true  _  refl = refl
  to∘from false () refl

sat-sem : ∀ {p : Char → Bool} {t pt s} →
          (t , pt) ∈ sat p · s ↔ s ≡ [ t ]
sat-sem {p} {t} {pt} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
  to : ∀ {s} → (t , pt) ∈ sat p · s → s ≡ [ t ]
  to (>>=-sem token-sem (>>=-sem tt∈ return-sem)) =
    P.cong (λ s → t ∷ s ++ []) (Inverse.to (if-true-sem pt) ⟨$⟩ tt∈)

  from : ∀ {s} → s ≡ [ t ] → (t , pt) ∈ sat p · s
  from refl =
    >>=-sem token-sem
            (>>=-sem (Inverse.from (if-true-sem pt) ⟨$⟩ refl)
                     return-sem)

  from∘to : ∀ {s} (t∈ : (t , pt) ∈ sat p · s) → from (to t∈) ≡ t∈
  from∘to (>>=-sem token-sem (>>=-sem tt∈ return-sem))
    with Inverse.to (if-true-sem pt) ⟨$⟩ tt∈
       | Inverse.left-inverse-of (if-true-sem pt) tt∈
  from∘to (>>=-sem token-sem
             (>>=-sem .(Inverse.from (if-true-sem pt) ⟨$⟩ refl)
                      return-sem))
    | refl | refl = refl

  to∘from : ∀ {s} (eq : s ≡ [ t ]) → to (from eq) ≡ eq
  to∘from refl
    rewrite Inverse.right-inverse-of (if-true-sem pt) refl
    = refl

abstract

  -- Grammar.Infinite requires a lot more memory to type-check if this
  -- definition is made concrete (at the time of writing).

  tok-sem : ∀ {t′ t s} → t′ ∈ tok t · s ↔ (t ≡ t′ × s ≡ [ t ])
  tok-sem {t′} {t} {s} =
    t′ ∈ tok t · s                                   ↔⟨ <$>-sem ⟩
    (∃ λ p → p ∈ sat (λ t′ → t == t′) · s × t′ ≡ t)  ↔⟨ Σ.cong Inv.id (sat-sem ×-cong Inv.id) ⟩
    (∃ λ p → s ≡ [ proj₁ p ] × t′ ≡ t)               ↔⟨ Σ-assoc ⟩
    (∃ λ t″ → T (t == t″) × s ≡ [ t″ ] × t′ ≡ t)     ↔⟨ Σ.cong Inv.id (True↔ _ P.≡-irrelevant ×-cong Inv.id) ⟩
    (∃ λ t″ → t ≡ t″ × s ≡ [ t″ ] × t′ ≡ t)          ↔⟨ lemma ⟩
    (t ≡ t′ × s ≡ [ t ])                             ∎
    where
    open Related.EquationalReasoning

    lemma : (∃ λ t″ → t ≡ t″ × s ≡ [ t″ ] × t′ ≡ t) ↔
            (t ≡ t′ × s ≡ [ t ])
    lemma = record
      { to         = P.→-to-⟶ to
      ; from       = P.→-to-⟶ from
      ; inverse-of = record
        { left-inverse-of  = from∘to
        ; right-inverse-of = to∘from
        }
      }
      where
      to : ∀ {t′ t : Char} {s} →
           (∃ λ t″ → t ≡ t″ × s ≡ [ t″ ] × t′ ≡ t) → t ≡ t′ × s ≡ [ t ]
      to (_ , refl , refl , refl) = (refl , refl)

      from : ∀ {t′ t : Char} {s} →
             t ≡ t′ × s ≡ [ t ] → ∃ λ t″ → t ≡ t″ × s ≡ [ t″ ] × t′ ≡ t
      from (refl , refl) = (_ , refl , refl , refl)

      from∘to : ∀ {t′ t : Char} {s}
                (eqs : ∃ λ t″ → t ≡ t″ × s ≡ [ t″ ] × t′ ≡ t) →
                from (to eqs) ≡ eqs
      from∘to (_ , refl , refl , refl) = refl

      to∘from : ∀ {t′ t : Char} {s} (eqs : t ≡ t′ × s ≡ [ t ]) →
                to (from eqs) ≡ eqs
      to∘from (refl , refl) = refl

------------------------------------------------------------------------
-- An aside: An inductive version of the grammar type above wouldn't
-- be very useful (assuming that Char is finite)

module Aside (finite-number-of-tokens :
                ∃ λ (ts : List Char) → ∀ t → t ∈ ts) where

  open ≤-Reasoning

  infixl 15 _>>=_
  infixl 10 _∣_

  data GrammarI : Set → Set₁ where
    return : ∀ {A} → A → GrammarI A
    token  : GrammarI Char
    _>>=_  : ∀ {A B} → GrammarI A → (A → GrammarI B) → GrammarI B
    _∣_    : ∀ {A} → GrammarI A → GrammarI A → GrammarI A

  infix 4 _∈I_·_

  data _∈I_·_ : ∀ {A} → A → GrammarI A → List Char → Set₁ where
    return-sem : ∀ {A} {x : A} → x ∈I return x · []
    token-sem  : ∀ {t} → t ∈I token · [ t ]
    >>=-sem    : ∀ {A B x y s₁ s₂} {g₁ : GrammarI A}
                   {g₂ : A → GrammarI B} →
                 x ∈I g₁ · s₁ → y ∈I g₂ x · s₂ →
                 y ∈I g₁ >>= g₂ · s₁ ++ s₂
    left-sem   : ∀ {A} {g₁ g₂ : GrammarI A} {x s} →
                 x ∈I g₁ · s → x ∈I g₁ ∣ g₂ · s
    right-sem  : ∀ {A} {g₁ g₂ : GrammarI A} {x s} →
                 x ∈I g₂ · s → x ∈I g₁ ∣ g₂ · s

  -- A kind of parser for the inductive grammars, used to prove
  -- finite-number-of-results. Note that the "parser" is not quite
  -- correct when seen as a parser: it sometimes returns too many
  -- results. (The derivative of return x should be a failing
  -- grammar.)

  initial-bag : ∀ {A} (g : GrammarI A) →
                ∃ λ xs → ∀ {x} → x ∈I g · [] → x ∈ xs

  derivative : ∀ {A} (g : GrammarI A) t →
               ∃ λ g′ → ∀ {x s} → x ∈I g · t ∷ s → x ∈I g′ · s

  parse : ∀ {A} (g : GrammarI A) s →
          ∃ λ xs → ∀ {x} → x ∈I g · s → x ∈ xs
  parse g []      = initial-bag g
  parse g (t ∷ s) with derivative g t
  ... | g′ , ok₁ with parse g′ s
  ...   | xs , ok₂ = xs , ok₂ ∘ ok₁

  initial-bag (return x) = [ x ] , λ { .{x = x} return-sem → here refl }
  initial-bag token      = []    , λ ()
  initial-bag (g₁ ∣ g₂)  =
    Prod.zip
      _++_
      (λ {xs} i₁ i₂ →
       λ { (left-sem  ∈g₁) → Inverse.to ++↔             ⟨$⟩ inj₁ (i₁ ∈g₁)
         ; (right-sem ∈g₂) → Inverse.to (++↔ {xs = xs}) ⟨$⟩ inj₂ (i₂ ∈g₂)
         })
      (initial-bag g₁)
      (initial-bag g₂)
  initial-bag (_>>=_ {A = A} {B = B} g₁ g₂) with initial-bag g₁
  ... | xs , xs-ok = ys xs , λ ∈g₁>>=g₂ → lemma₁ ∈g₁>>=g₂ refl
    where
    ys : List A → List B
    ys xs = xs LMa.>>= λ x → proj₁ (initial-bag (g₂ x))

    lemma₂ : ∀ {x y} xs → x ∈ xs → y ∈I g₂ x · [] → y ∈ ys xs
    lemma₂ (x ∷ xs) (here refl) ∈g₂ =
      Inverse.to ++↔ ⟨$⟩ inj₁ (proj₂ (initial-bag (g₂ x)) ∈g₂)
    lemma₂ (z ∷ xs) (there x∈) ∈g₂ =
      Inverse.to (++↔ {xs = proj₁ (initial-bag (g₂ z))}) ⟨$⟩
        inj₂ (lemma₂ xs x∈ ∈g₂)

    lemma₁ : ∀ {x s} → x ∈I g₁ >>= g₂ · s → s ≡ [] → x ∈ ys xs
    lemma₁ (>>=-sem {s₁ = []}    ∈g₁ ∈g₂) refl = lemma₂ xs (xs-ok ∈g₁) ∈g₂
    lemma₁ (>>=-sem {s₁ = _ ∷ _} ∈g₁ ∈g₂) ()

  derivative (return x) t = return x , λ ()
  derivative token      t = return t , λ { .{s = []} token-sem → return-sem }
  derivative (g₁ ∣ g₂)  t =
    Prod.zip _∣_
             (λ {g₁′ g₂′} ok₁ ok₂ →
              λ { (left-sem  ∈g₁) → left-sem  (ok₁ ∈g₁)
                ; (right-sem ∈g₂) → right-sem (ok₂ ∈g₂)
                })
             (derivative g₁ t)
             (derivative g₂ t)
  derivative (_>>=_ {A = A} {B = B} g₁ g₂) t
    with derivative g₁ t | initial-bag g₁
  ... | g₁′ , g₁′-ok | xs , xs-ok =
    g′ xs , λ ∈g₁>>=g₂ → lemma₁ ∈g₁>>=g₂ refl
    where
    g′ : List A → GrammarI B
    g′ []       = g₁′ >>= g₂
    g′ (x ∷ xs) = return x >>= (λ x → proj₁ (derivative (g₂ x) t))
                ∣ g′ xs

    lemma₂ : ∀ {x y s} xs →
             x ∈ xs → y ∈I g₂ x · t ∷ s → y ∈I g′ xs · s
    lemma₂ (x ∷ xs) (here refl) ∈g₂ = left-sem (>>=-sem return-sem
                                        (proj₂ (derivative (g₂ x) t) ∈g₂))
    lemma₂ (z ∷ xs) (there x∈)  ∈g₂ = right-sem (lemma₂ xs x∈ ∈g₂)

    lemma₃ : ∀ {x y s₁ s₂} xs →
             x ∈I g₁′ · s₁ → y ∈I g₂ x · s₂ → y ∈I g′ xs · s₁ ++ s₂
    lemma₃ []       ∈g₁′ ∈g₂ = >>=-sem ∈g₁′ ∈g₂
    lemma₃ (x ∷ xs) ∈g₁′ ∈g₂ = right-sem (lemma₃ xs ∈g₁′ ∈g₂)

    lemma₁ : ∀ {y s s′} →
             y ∈I g₁ >>= g₂ · s → s ≡ t ∷ s′ → y ∈I g′ xs · s′
    lemma₁ (>>=-sem {s₁ = []}     ∈g₁ ∈g₂) refl = lemma₂ xs (xs-ok  ∈g₁) ∈g₂
    lemma₁ (>>=-sem {s₁ = .t ∷ _} ∈g₁ ∈g₂) refl = lemma₃ xs (g₁′-ok ∈g₁) ∈g₂

  -- If strings are restricted to have a given maximum length, then an
  -- inductive grammar generates a finite number of distinct results.

  finite-number-of-results :
    ∀ {A} (g : GrammarI A) n →
    ∃ λ xs → ∀ {x s} → length s ≤ n → x ∈I g · s → x ∈ xs
  finite-number-of-results g n =
    (all-strings n LMa.>>= proj₁ ∘ parse g) ,
    λ {_} {s} ≤n ∈g →
      Inverse.to ∈.>>=-∈↔ ⟨$⟩
        (_ , all-strings-ok s n ≤n , proj₂ (parse g s) ∈g)
    where
    all-strings : ℕ → List (List Char)
    all-strings 0       = [ [] ]
    all-strings (suc n) = all-strings n ++
                          (proj₁ finite-number-of-tokens LMa.>>= λ t →
                           List.map (_∷_ t) (all-strings n))

    all-strings-ok : ∀ s n → length s ≤ n → s ∈ all-strings n
    all-strings-ok []      zero    z≤n      = here refl
    all-strings-ok []      (suc n) z≤n      = Inverse.to ++↔ ⟨$⟩
                                                inj₁ (all-strings-ok [] n z≤n)
    all-strings-ok (t ∷ s) (suc n) (s≤s ≤n) =
      Inverse.to (++↔ {xs = all-strings n}) ⟨$⟩
        inj₂ (Inverse.to ∈.>>=-∈↔ ⟨$⟩
                (_ , proj₂ finite-number-of-tokens t
                   , Inverse.to (∈.map-∈↔ _) ⟨$⟩
                       (_ , all-strings-ok s n ≤n , refl)))

  -- No inductive grammar can generate strings of unbounded length.

  bounded-length :
    ∀ {A} (g : GrammarI A) →
    ∃ λ n → ∀ {x s} → x ∈I g · s → length s ≤ n
  bounded-length (return x) = 0 , λ { .{s = []}    return-sem → z≤n }
  bounded-length token      = 1 , λ { .{s = [ _ ]} token-sem  → s≤s z≤n }
  bounded-length (g₁ ∣ g₂)  =
    Prod.zip _+_
             (λ {n₁ n₂} b₁ b₂ →
              λ { {s = s} (left-sem ∈g₁) → begin
                  length s  ≤⟨ b₁ ∈g₁ ⟩
                  n₁        ≤⟨ m≤m+n _ _ ⟩
                  n₁ + n₂   ∎
                ; {s = s} (right-sem ∈g₂) → begin
                  length s  ≤⟨ b₂ ∈g₂ ⟩
                  n₂        ≤⟨ n≤m+n n₁ _ ⟩
                  n₁ + n₂   ∎
                })
             (bounded-length g₁)
             (bounded-length g₂)
  bounded-length (_>>=_ {A = A} g₁ g₂) with bounded-length g₁
  ... | n₁ , b₁ with finite-number-of-results g₁ n₁
  ...   | xs , xs-ok =
    n₁ + n₂ xs ,
    λ { .{s = _} (>>=-sem {s₁ = s₁} {s₂ = s₂} ∈g₁ ∈g₂) → begin
        length (s₁ ++ s₂)      ≡⟨ length-++ s₁ ⟩
        length s₁ + length s₂  ≤⟨ +-mono-≤ (b₁ ∈g₁) (lemma xs (xs-ok (b₁ ∈g₁) ∈g₁) ∈g₂) ⟩
        n₁        + n₂ xs      ∎ }
    where
    n₂ : List A → ℕ
    n₂ = foldr _⊔_ 0 ∘ List.map (λ x → proj₁ (bounded-length (g₂ x)))

    lemma : ∀ {x y s} xs → x ∈ xs → y ∈I g₂ x · s → length s ≤ n₂ xs
    lemma {s = s} (x ∷ xs) (here refl) y∈ = begin
      length s                               ≤⟨ proj₂ (bounded-length (g₂ x)) y∈ ⟩
      proj₁ (bounded-length (g₂ x))          ≤⟨ m≤m⊔n _ _ ⟩
      proj₁ (bounded-length (g₂ x)) ⊔ n₂ xs  ∎
    lemma {s = s} (z ∷ xs) (there x∈) y∈ = begin
      length s                               ≤⟨ lemma xs x∈ y∈ ⟩
      n₂ xs                                  ≤⟨ m≤m⊔n _ _ ⟩
      n₂ xs ⊔ proj₁ (bounded-length (g₂ z))  ≡⟨ ∧-comm (n₂ xs) _ ⟩
      proj₁ (bounded-length (g₂ z)) ⊔ n₂ xs  ∎
      where open DistributiveLattice NatP.⊓-⊔-distributiveLattice
