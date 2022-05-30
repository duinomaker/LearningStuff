open import Agda.Builtin.String
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.String.Properties renaming (_==_ to _==st_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List using (List; _++_; []; _∷_; map; filter; any)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans)

data Sym : Set where
  Term    : String → Sym
  NonTerm : String → Sym
  Empty   : Sym
  End     : Sym

Sentence : Set
Sentence = List Sym

Rule : Set
Rule = Sym × Sentence

Grammar : Set
Grammar = List Rule × Sym

LL₁Table : Set
LL₁Table = List ((Sym × Sym) × ℕ)

_==_ : ∀ (m n : Sym) → Bool
(Term x)    == (Term y)    = x ==st y
(NonTerm x) == (NonTerm y) = x ==st y
Empty       == Empty       = true
End         == End         = true
_           == _           = false

_==s_ : ∀ (m n : Sentence) → Bool
[] ==s [] = true
(hm ∷ tm) ==s (hn ∷ tn) with hm == hn
... | true  = tm ==s tn
... | false = false
_ ==s _ = false

derive₁ : Rule → Sentence → Sentence
derive₁ (n , p) [] = []
derive₁ (n , p) (h ∷ t) with n == h
... | true  = p ++ t
... | false = h ∷ (derive₁ (n , p) t)

derive : List Rule → Sentence → Sentence
derive [] s = s
derive (h ∷ t) s = derive t (derive₁ h s)

listItem : ∀ {A : Set} → ℕ → List A → A → A
listItem zero (h ∷ t) _ = h
listItem (suc n) (h ∷ t) = listItem n t
listItem _ [] d = d

ruleListItem : ℕ → List Rule → Rule
ruleListItem n l = listItem n l (End , End ∷ [])

listItems : ∀ {A : Set} → List ℕ → List A → A → List A
listItems [] _ _ = []
listItems (h ∷ t) l d = (listItem h l d) ∷ listItems t l d

grammarDerive : Grammar → List ℕ → Sentence
grammarDerive (rs , n) ns = derive gRules (n ∷ []) where
  gRules = listItems ns rs (End , End ∷ [])

data _∈_ (s : Sentence) (g : Grammar) : Set where
  derivation : (ns : List ℕ) → grammarDerive g ns ==s s ≡ true → s ∈ g

isTerminal : Sym → Bool
isTerminal (Term _) = true
isTerminal _ = false

isNonTerminal : Sym → Bool
isNonTerminal (NonTerm _) = true
isNonTerminal _ = false

unique : List Sym → List Sym → List Sym
unique [] res' = res'
unique (h ∷ t) res' with any (λ x → x == h) res'
... | true  = unique t res'
... | false = unique t (h ∷ res')

allSymbols : Grammar → (Sym → Bool) → List Sym
allSymbols (rs , s) f = helper rs [] where
  helper : List Rule → List Sym → List Sym
  helper [] res = unique res []
  helper ((n , p) ∷ t) res = helper t (n ∷ p ++ res)

terminals : Grammar → List Sym
terminals g = allSymbols g isTerminal

nonTerminals : Grammar → List Sym
nonTerminals g = allSymbols g isNonTerminal

uniqueInsert : Sym → List Sym → List Sym
uniqueInsert a [] = a ∷ []
uniqueInsert a (h ∷ t) with a == h
... | true  = h ∷ t
... | false = h ∷ uniqueInsert a t

hasEmpty : List Sym → Bool
hasEmpty lst = any (λ x → x == Empty) lst

excludeEmpty : List Sym → List Sym
excludeEmpty [] = []
excludeEmpty (h ∷ t) with h == Empty
... | true  = excludeEmpty t
... | false = h ∷ excludeEmpty t

ll₁first : List Rule → Sym → List Sym
ll₁follow : Grammar → Sym → List Sym

{-# TERMINATING #-}
ll₁first rs s with isTerminal s
... | true  = s ∷ []
... | false = iter rs where
  iter : List Rule → List Sym
  iter [] = []
  iter ((n , st) ∷ t) with n == s
  ... | true = (helper st) ++ iter t where
    helper : Sentence → List Sym
    helper [] = Empty ∷ []
    helper (h ∷ _) with isTerminal h
    ... | true  = h ∷ []
    ... | false = ll₁first rs h
  ... | false = iter t

ll₁follow (rs , sn) s = unique (iterhelper (iter rs)) [] where
  iterhelper : List Sym → List Sym
  iterhelper symbs with s == sn
  ... | true  = uniqueInsert End symbs
  ... | false = symbs
  iteriter : Sentence → Sym → List Sym
  iteriter [] _ = []
  iteriter (h ∷ []) n with h == s | n == s
  ... | true  | false = ll₁follow (rs , sn) n
  ... | _     | _     = []
  iteriter (h₁ ∷ h₂ ∷ t) n with h₁ == s
  ... | true  = helper (ll₁first rs h₂) where
    helper : List Sym → List Sym
    helper lst with hasEmpty lst
    ... | true  = (excludeEmpty lst) ++ ll₁follow (rs , sn) h₂
    ... | false = lst
  ... | false = iteriter (h₂ ∷ t) n
  iter : List Rule → List Sym
  iter [] = []
  iter ((n , st) ∷ t) = (iteriter st n) ++ iter t

ll₁table : Grammar → LL₁Table
ll₁table (rs , sn) = iter rs 0 where
  helper : Sym → ℕ → Sym → (Sym × Sym) × ℕ
  helper n num s = ((n , s) , num)
  impl : Rule → ℕ → LL₁Table
  impl (n , []) num = map (helper n num) (ll₁follow (rs , sn) n)
  impl (n , h ∷ t) num = map (helper n num) (ll₁first rs h)
  iter : List Rule → ℕ → LL₁Table
  iter [] _ = []
  iter (h ∷ t) num = (impl h num) ++ iter t (suc num)

tableItem : ∀ {A B : Set} →
  List (A × B) → (A → A → Bool) → A → B → B
tableItem [] _ _ d = d
tableItem ((a , b) ∷ t) f i d with f a i
... | true  = b
... | false = tableItem t f i d

ll₁tableItem : LL₁Table → Sym × Sym → ℕ
ll₁tableItem tbl i = tableItem tbl eq i 0 where
  eq : Sym × Sym → Sym × Sym → Bool
  eq (a , b) (c , d) = a == c ∧ b == d

-- An inqury into well-foundedness

Rel : Set → Set₁
Rel A = A → A → Set

data Acc {A : Set} (_<_ : Rel A) (x : A) : Set where
  acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

WellFounded : ∀ {A : Set} → Rel A → Set
WellFounded _<_ = ∀ x → Acc _<_ x

foldAcc : ∀ {A : Set} {_<_ : Rel A} (P : A → Set) →
  (∀ x → (∀ y → y < x → P y) → P x) →
  ∀ z → Acc _<_ z → P z
foldAcc P acc' = go where
  go : ∀ z → Acc _ z → P z
  go _ (acc a) = acc' _ (λ _ y<z → go _ (a _ y<z))

rec : ∀ {A : Set} {_<_ : Rel A} → WellFounded _<_ →
  (P : A → Set) → (∀ x → (∀ y → y < x → P y) → P x) →
  ∀ z → P z
rec wf P acc' z = foldAcc P acc' _ (wf z)

module NatExample where
  <-wf : WellFounded _<_
  <-wf n = acc (go n) where
    go : ∀ (n m : ℕ) → m < n → Acc _<_ m
    go zero m ()
    go (suc n) zero _ = acc (λ _ ())
    go (suc n) (suc m) (s≤s m<n) =
      acc (λ o o<sm → go n o (≤-trans o<sm m<n))

  _/2 : ℕ → ℕ
  zero /2 = zero
  (suc zero) /2 = zero
  (suc (suc n)) /2 = suc (n /2)

  /2-less : ∀ (n : ℕ) → (suc n) /2 ≤ n
  /2-less zero = z≤n
  /2-less (suc zero) = s≤s z≤n
  /2-less (suc (suc n)) = s≤s (≤-trans (/2-less n) (right _)) where
    right : ∀ (n : ℕ) → n ≤ suc n
    right zero = z≤n
    right (suc n) = s≤s (right n)

  log₂ : ℕ → ℕ
  log₂ n = go _ (<-wf n) where
    go : ∀ (n : ℕ) → Acc _<_ n → ℕ
    go zero _ = zero
    go (suc n) (acc a) = suc (go ((suc n) /2) (a _ (s≤s (/2-less n))))

analyze : Grammar → LL₁Table → Sentence → List ℕ
{-# TERMINATING #-}
analyze (rs , n) tbl s = helper (n ∷ []) s where
  helper : List Sym → Sentence → List ℕ
  helper (sh ∷ st) (h ∷ t) with sh == h
  ... | true  = helper st t
  ... | false = i ∷ helper (derive₁ r (sh ∷ st)) (h ∷ t) where
    i = ll₁tableItem tbl (sh , h)
    r = ruleListItem i rs
  helper (sh ∷ st) [] = i ∷ helper (derive₁ r (sh ∷ st)) [] where
    i = ll₁tableItem tbl (sh , End)
    r = ruleListItem i rs
  helper _ _ = []

-- Concrete implementation

grammar : Grammar
grammar = rules , NonTerm "E" where
  rules = (NonTerm "E"  , NonTerm "T" ∷ NonTerm "E'" ∷ [])             -- 0
        ∷ (NonTerm "E'" , Term "+" ∷ NonTerm "T" ∷ NonTerm "E'" ∷ [])  -- 1
        ∷ (NonTerm "E'" , [])                                          -- 2
        ∷ (NonTerm "T"  , NonTerm "F" ∷ NonTerm "T'" ∷ [])             -- 3
        ∷ (NonTerm "T'" , Term "*" ∷ NonTerm "F" ∷ NonTerm "T'" ∷ [])  -- 4
        ∷ (NonTerm "T'" , [])                                          -- 5
        ∷ (NonTerm "F"  , Term "(" ∷ NonTerm "E" ∷ Term ")" ∷ [])      -- 6
        ∷ (NonTerm "F"  , Term "id" ∷ [])                              -- 7
        ∷ []

sentence : Sentence
sentence = map Term ("id" ∷ "*" ∷ "(" ∷ "id" ∷ "+" ∷ "id" ∷ ")" ∷ [])

-- Show that `sentence' is a sentence of `grammar' using a manually crafted
-- derivation list
testM : sentence ∈ grammar
testM = derivation ns refl where
  ns = 0 ∷ 3 ∷ 7 ∷ 4 ∷ 6 ∷ 0 ∷ 3 ∷ 7 ∷ 5 ∷ 1 ∷ 3 ∷ 7 ∷ 5 ∷ 2 ∷ 5 ∷ 2 ∷ []

-- Show that `sentence' is a sentence of `grammar' semi-automatically using
-- a manually crafted LL(1) table
testS : sentence ∈ grammar
testS = derivation ns refl where
  ns = analyze grammar table sentence where
    table = ((NonTerm "E"  , Term "id")  , 0)
          ∷ ((NonTerm "E"  , Term "(" )  , 0)
          ∷ ((NonTerm "E'" , Term "+" )  , 1)
          ∷ ((NonTerm "E'" , Term ")" )  , 2)
          ∷ ((NonTerm "E'" , End      )  , 2)
          ∷ ((NonTerm "T"  , Term "id")  , 3)
          ∷ ((NonTerm "T"  , Term "(" )  , 3)
          ∷ ((NonTerm "T'" , Term "+" )  , 5)
          ∷ ((NonTerm "T'" , Term "*" )  , 4)
          ∷ ((NonTerm "T'" , Term ")" )  , 5)
          ∷ ((NonTerm "T'" , End      )  , 5)
          ∷ ((NonTerm "F"  , Term "id")  , 7)
          ∷ ((NonTerm "F"  , Term "(" )  , 6)
          ∷ []

-- Show that `sentence' is a sentence of `grammar' without hand-crafting
testA : sentence ∈ grammar
testA = derivation ns refl where
  ns = analyze grammar (ll₁table grammar) sentence
