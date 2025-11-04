
def Set (α : Type u) := α -> Prop

-- inspired by mathlib
class Fintype (α : Type u) where
  elems : List α
  complete : ∀ a : α, a ∈ elems

/-

Leeres Wort: Länge 0 -> kann man dafür das symbol ε reservieren?
Neutrales Element der konkatenation für Wörter (ist das Definition oder muss man das beweisen? )
Präfix
Infix
Suffix
Sprache: Menge von Wörtern über Alphabet
Kleinste sprache: leere sprache
Teilmenge jeder anderen sprache
Größte Sprache: Sigma Stern
Jede sprache über sigma ist Teilmenge davon

-/


-- The following type class instances are just allowing us to use some basic notation like ∅, ∈ or ∪ with the right definitions..
instance : EmptyCollection (Set α) where
  emptyCollection := fun _ => False

instance : Membership α (Set α) where
  mem S a := S a

instance : Union (Set α) where
  union A B := fun e => e ∈ A ∨ e ∈ B

instance : Inter (Set α) where
  inter A B := fun e => e ∈ A ∧ e ∈ B

instance : HasSubset (Set α) where
  Subset A B := ∀ e, e ∈ A -> e ∈ B

instance : HasSSubset (Set α) where
  SSubset A B := A ⊆ B ∧ ¬ B ⊆ A

instance : SDiff (Set α) where
  sdiff A B := fun e => e ∈ A ∧ ¬(e ∈ B)

-- Set extensionality: Two sets are equal if they contain the same elements. This is not something we define but we can prove it!
theorem Set.ext (X Y : Set α) : (∀ e, e ∈ X ↔ e ∈ Y) -> X = Y := by
  intro h; apply funext; intro e; apply propext; specialize h e; exact h

-- From now on, we pick some alphabet Sigma. In fact, we do not even care about the type of Sigma. In can basically be anything.
variable {Sigma : Type u}

-- Words are merely lists over some alphabet Sigma. In fact, we do not even care about the type of Sigma.
abbrev Word (Sigma : Type u) := List Sigma

-- Example:
def Alphabet : Set Char := fun σ : Char => σ = 'a' ∨ σ = 'b'

-- Words: Properties and Operations (Slides 29-...)

-- Let's define concatenation as multiplication.
instance : Mul (Word Sigma) where
  mul u v := List.append u v

instance [BEq Sigma] : HMul Sigma (Word Sigma) (Word Sigma) where
  hMul σ w := List.insert σ w

-- Examples
#eval ['a','b'] * ['b','a']

def some_word : Word Char := ['S','t','a','u','b','e','c','k','e','n']

#eval List.IsPrefix ['S','t','a','u','b'] some_word
--#eval List.IsInfix ['t','a','u','b'] some_word
#eval List.IsSuffix ['e','c','k','e','n'] some_word

#eval 'a'::some_word

-- für alle alphabete sigma existiert ein leeres wort []
-- [] * w = w für alle w ∈ sigma* (mit List.concat ?)

-- evtl.: für alle nichtleeren wörter gilt: w = u*v (v darf leer sein)
-- kann man zeigen: head::tail = head * tail ?

theorem nonempty_prefix [BEq Sigma] (σ : Sigma) (w : Word Sigma) : σ::w = σ * w := by

  sorry

theorem epsilon_concat : ∀ (w : Word Sigma), w * [] = w := by
  intro w
  induction w with
  | nil =>
    trivial
  | cons σ u ih =>

    sorry


-- A language is in turn just a set of words.
abbrev Language (Sigma : Type u) := Set (Word Sigma)

-- The "biggest language" Σ* contains all words over Σ
def sigma_star : Language Sigma := fun w : Word Sigma => True

-- Every language over Σ is a subset of Σ*
theorem sigma_star_subset : ∀ (L: Language Sigma), L ⊆ sigma_star := by
  sorry

-- Concatenation of Languages
instance : Mul (Language Sigma) where
  mul L1 L2 := fun w => ∃ u ∈ L1, ∃ v ∈ L2, w = u * v

-- Complement
def Language.complement (L : Language Sigma) : Language Sigma :=
  sigma_star \ L

-- For languages we can also execute concatenation multiple times and define this via Powers.
def Language.pow (L : Language Sigma) : Nat -> Language Sigma
| .zero => fun w => w = []
| .succ n => L * L.pow n

instance : NatPow (Language Sigma) where
  pow L n := L.pow n

-- Finally we define the Kleene Star and notation for it.
def Language.kstar (L : Language Sigma) : Language Sigma := fun w => ∃ n, w ∈ L^n
postfix:max "*" => Language.kstar
