set_option linter.unusedSectionVars false

def Set (α : Type u) := α -> Prop

-- inspired by mathlib
class Fintype (α : Type u) where
  elems : List α
  complete : ∀ a : α, a ∈ elems

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


-- TO DO: für Mengen
/-
- assoziativität ???
- distributivgesetze
- de morgansche regeln
-/

theorem Set.inter_commutative (X Y : Set α) : X ∩ Y = Y ∩ X := by
  apply Set.ext
  intro e
  constructor
  . intro e_mem
    constructor
    . rcases e_mem with ⟨e_x, e_y⟩
      exact e_y
    . rcases e_mem with ⟨e_x, e_y⟩
      exact e_x
  . intro e_mem
    constructor
    . rcases e_mem with ⟨e_x, e_y⟩
      exact e_y
    . rcases e_mem with ⟨e_x, e_y⟩
      exact e_x

theorem Set.union_commutative (X Y : Set α) : X ∪ Y = Y ∪ X := by
  apply Set.ext
  intro e
  constructor
  . intro e_mem
    apply Or.elim e_mem
    . intro e_mem_x
      apply Or.inr
      exact e_mem_x
    . intro e_mem_y
      apply Or.inl
      exact e_mem_y
  . intro e_mem
    apply Or.elim e_mem
    . intro e_mem_x
      apply Or.inr
      exact e_mem_x
    . intro e_mem_y
      apply Or.inl
      exact e_mem_y

-- From now on, we pick some alphabet Sigma. In fact, we do not even care about the type of Sigma. In can basically be anything.
variable {Sigma : Type u} [BEq Sigma] -- geht auch decidable equality

-- Words are merely lists over some alphabet Sigma. In fact, we do not even care about the type of Sigma.
abbrev Word (Sigma : Type u) := List Sigma

-- Example:
def Alphabet : Set Char := fun σ : Char => σ = 'a' ∨ σ = 'b'

-- Words: Properties and Operations (Slides 29-...)

-- Let's define concatenation as multiplication.
instance : Mul (Word Sigma) where
  mul u v := List.append u v

theorem Word.mul_eq (u v : Word Sigma) : u * v = u++v := by
  trivial

theorem Word.mul_assoc (u v w : Word Sigma) : (u * v) * w = u * (v * w) := by
  simp only [mul_eq]; rw [List.append_assoc]

/-instance [BEq Sigma] : HMul Sigma (Word Sigma) (Word Sigma) where
  hMul σ w := List.insert σ w -/

-- Examples
#eval ['a','b'] * ['b','a']

def some_word : Word Char := ['S','t','a','u','b','e','c','k','e','n']
def another_word : Word Char := ['A','l','t','b','a','u','c','h','a','r','m','e']

#eval List.IsPrefix ['S','t','a','u','b'] some_word
---#eval List.IsInfix ['t','a','u','b'] some_word
#eval List.IsSuffix ['e','c','k','e','n'] some_word

#eval 'a'::some_word
#eval some_word.splitAt 1
#eval some_word.append []

def expl : List (Word Char) := [['a'], [], ['b']]
#eval expl.removeAll [[]]
#eval (expl.removeAll [[]]).flatten = expl.flatten


-- For every alphabet Sigma, there is an empty word ε. As we defined words as Lists
-- with elements of type Sigma, ε is just the empty list [].
-- ε is the identity element for concatenation of words:

-- Auxiliary result for the actual theorem
theorem append_nil : ∀ (L : List α), L.append [] = L := by
  intro L
  simp

-- w * ε = w
theorem epsilon_concat : ∀ (w : Word Sigma), w * [] = w := by
  intro w
  induction w with
  | nil =>
    trivial
  | cons σ u ih =>
    apply append_nil

-- ε * w = w
theorem concat_epsilon : ∀ (w : Word Sigma), [] * w = w := by
  intro w
  induction w with
  | nil =>
    trivial
  | cons σ u ih =>
     trivial

-- A language is in turn just a set of words.
abbrev Language (Sigma : Type u) := Set (Word Sigma)

-- The "biggest language" Σ* contains all words over Σ
def sigma_star : Language Sigma := fun _ => True
-- The empty language contains no words
def L_empty : Language Sigma := fun _ => False
-- The language containing only ε is not empty
def L_eps : Language Sigma := fun w => w = []

-- Every language over Σ is a subset of Σ*
theorem sigma_star_subset : ∀ (L : Language Sigma), L ⊆ sigma_star := by
  intro L
  unfold sigma_star
  intro w w_mem
  trivial

-- The empty language is a subset of any language.
theorem L_eps_subset : ∀ (L : Language Sigma), L_empty ⊆ L := by
  intro L
  unfold L_empty
  intro w w_mem
  trivial

theorem L_eps_mem : w ∈ (@L_eps Sigma) ↔ w = [] := by
  constructor
  . intro w_mem
    unfold L_eps at w_mem
    simp only [Membership.mem] at w_mem
    exact w_mem
  . intro w_eq
    unfold L_eps
    simp only [Membership.mem]
    exact w_eq

-- Concatenation of Languages
instance : Mul (Language Sigma) where
  mul L1 L2 := fun w => ∃ u ∈ L1, ∃ v ∈ L2, w = u * v

theorem Language.mul_assoc (L₁ L₂ L₃ : Language Sigma) : (L₁ * L₂) * L₃ = L₁ * (L₂ * L₃) := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
    rcases u_mem with ⟨x, x_mem, y, y_mem, u_eq⟩
    exists x
    constructor
    . exact x_mem
    . exists y*v
      constructor
      . exists y
        constructor
        . exact y_mem
        . exists v
      . rw [← Word.mul_assoc]
        subst u
        exact w_eq
  . intro w_mem
    rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
    rcases v_mem with ⟨x, x_mem, y, y_mem, v_eq⟩
    exists u*x
    constructor
    . exists u
      constructor
      . exact u_mem
      . exists x
    . exists y
      constructor
      . exact y_mem
      . subst v
        rw [Word.mul_assoc]
        exact w_eq

-- Complement
def Language.complement (L : Language Sigma) : Language Sigma :=
  sigma_star \ L

-- The difference between two languages can be expressed with intersection and complement.
theorem diff_via_inter (L₁ L₂ : Language Sigma) : L₁ \ L₂ = L₁ ∩ L₂.complement := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨w_mem, w_nmem⟩
    unfold Language.complement
    trivial
  . intro w_mem
    rcases w_mem with ⟨w_1, w_2⟩
    unfold Language.complement at w_2
    constructor
    . exact w_1
    . rcases w_2 with ⟨ws, nw⟩
      exact nw

theorem de_morgan_rule1 (L₁ L₂ : Language Sigma) : (L₁ ∪ L₂).complement = L₁.complement ∩ L₂.complement := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    unfold Language.complement at w_mem
    rcases w_mem with ⟨w_mem, w_nmem⟩
    unfold Language.complement
    constructor
    . constructor
      . exact w_mem
      . simp [Membership.mem] at w_nmem
        intro f
        have contra : w ∈ L₁ ∪ L₂ := Or.inl f
        contradiction
    . constructor
      . exact w_mem
      . intro f
        have contra : w ∈ L₁ ∪ L₂ := Or.inr f
        contradiction
  . intro w_mem
    unfold Language.complement at w_mem
    rcases w_mem with ⟨w_mem1, w_mem2⟩
    unfold Language.complement
    rcases w_mem1 with ⟨w_mem, w_nmem1⟩
    rcases w_mem2 with ⟨w_mem, w_nmem2⟩
    constructor
    . exact w_mem
    . intro f
      cases f with
      | inl w_mem1 =>
        contradiction
      | inr w_mem2 =>
        contradiction

theorem de_morgan_rule2 (L₁ L₂ : Language Sigma) : (L₁ ∩ L₂).complement = L₁.complement ∪ L₂.complement := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    unfold Language.complement at w_mem
    rcases w_mem with ⟨w_mem, w_nmem⟩
    unfold Language.complement
    have w_nmem_inter : w ∉ L₁ ∨ w ∉ L₂ := by
      false_or_by_contra
      simp_all; contradiction -- to do: wie bekomme ich das simp_all weg?
    rcases w_nmem_inter with inl | inr
    . apply Or.inl
      constructor
      exact w_mem; exact inl
    . apply Or.inr
      constructor
      exact w_mem; exact inr
  . intro w_mem
    rcases w_mem with w_mem1 | w_mem2
    rcases w_mem1 with ⟨w_mem1, w_nmem1⟩
    . unfold Language.complement
      constructor
      . exact w_mem1
      . intro f
        rcases f with ⟨l, r⟩
        contradiction
    rcases w_mem2 with ⟨w_mem2, w_nmem2⟩
    . unfold Language.complement
      constructor
      . exact w_mem2
      . intro f
        rcases f with ⟨l, r⟩
        contradiction

theorem double_complement (L : Language Sigma) : (L.complement).complement = L := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    unfold Language.complement at w_mem
    rcases w_mem with ⟨w_mem, w_nmem⟩
    unfold Not at w_nmem
    have not_w_nmem : w ∉ L → False := by
      intro w_nmem_L
      have w_nmem_c : w ∈ sigma_star \ L := by
        constructor
        . exact w_mem
        . exact w_nmem_L
      apply w_nmem; exact w_nmem_c
    simp_all
  . intro w_mem
    unfold Language.complement
    constructor
    . unfold sigma_star
      trivial
    . intro f
      rcases f with ⟨w_mem_s, w_nmem⟩
      contradiction

-- For languages we can also execute concatenation multiple times and define this via Powers.
def Language.pow (L : Language Sigma) : Nat -> Language Sigma
| .zero => fun w => w = []
| .succ n => L * L.pow n

instance : NatPow (Language Sigma) where
  pow L n := L.pow n

-- Finally we define the Kleene Star and notation for it.
def Language.kstar (L : Language Sigma) : Language Sigma := fun w => ∃ n, w ∈ L^n
postfix:max "*" => Language.kstar

-- Additionally, one can define a "⁺" operator which is basically the Kleene Star without n=0.
def Language.plus (L : Language Sigma) : Language Sigma := fun w => ∃ n > 0, w ∈ L^n
postfix:max "⁺" => Language.plus

-- muss man das wirklich beweisen, oder bin ich nur zu blöd, die definition richtig anzuwenden?
theorem pow_as_concat (L : Language Sigma) : n > 0 → L^n = L * L^(n-1) := by
        intro gt
        apply Set.ext
        intro y
        constructor
        . intro y_mem
          induction n with
          | zero =>
            contradiction
          | succ n ih =>
            exact y_mem
        . intro y_mem
          rcases y_mem with ⟨p, p_mem, q, q_mem, y_eq⟩
          induction n with
          | zero =>
            contradiction
          | succ n ih =>
            exists p
            constructor
            . exact p_mem
            . exists q

theorem Language.mem_pow (L : Language Sigma) (w : Word Sigma) : w ∈ L^n ↔ ∃ l : (List (Word Sigma)), w = l.flatten ∧ l.length = n ∧ (∀ u ∈ l, u ∈ L) := by
  constructor
  intro w_mem
  . induction n generalizing w with
    | zero =>
      exists []
      constructor
      . rw [List.flatten_nil]; exact w_mem
      . simp
    | succ n ih =>
      rcases w_mem with ⟨v, v_mem, x, x_mem, w_eq⟩
      rcases ih x x_mem with ⟨l_x, x_eq, l_x_length, x_mem⟩
      exists v :: l_x
      constructor
      . rw [List.flatten_cons, ← x_eq]; exact w_eq
      constructor
      . rw [List.length_cons, l_x_length]
      . intro u u_mem
        rw [List.mem_cons] at u_mem
        cases u_mem with
        | inl u_mem => rw [u_mem]; exact v_mem
        | inr u_mem => apply x_mem; exact u_mem
  . rintro ⟨l, w_eq, w_l, u_mem⟩
    induction l generalizing n w with
    | nil =>
      rw [List.flatten_nil] at w_eq
      rw [List.length_nil] at w_l
      rw [w_eq, ← w_l]
      rfl
    | cons v l lh =>
      have v_mem : v ∈ L := by
        apply u_mem
        simp
      have gtz : n > 0 := by
        rw [List.length_cons] at w_l
        rw [← w_l]; simp
      rw [pow_as_concat _ gtz]
      exists v
      constructor
      . exact v_mem
      . exists l.flatten
        constructor
        . apply lh
          . rfl
          . rw [List.length_cons] at w_l; rw [← w_l]; simp
          . intro u u_mem'; apply u_mem; simp [u_mem']
        . exact w_eq

theorem Language.mem_kstar (L : Language Sigma) (w : Word Sigma) : w ∈ L* ↔ ∃ l : (List (Word Sigma)), w = l.flatten ∧ (∀ u ∈ l, u ∈ L) := by
    constructor
    . intro w_mem
      unfold Language.kstar at w_mem
      rcases w_mem with ⟨n, w_mem⟩
      induction n generalizing w with
      | zero =>
        exists []
        simp only [List.flatten_nil]
        constructor
        . exact w_mem
        . intro u u_mem
          contradiction
      | succ n ih =>
        rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
        rcases ih v v_mem with ⟨l_w, v_eq, l_mem⟩
        exists u::l_w
        constructor
        . rw [List.flatten_cons, ←v_eq]
          exact w_eq
        . intro x x_mem
          rw [List.mem_cons] at x_mem
          rcases x_mem
          . subst x
            exact u_mem
          . apply l_mem
            simp_all
    . intro h
      rcases h with ⟨l, w_eq, l_mem⟩
      induction l generalizing w with
      | nil =>
        exists 0
      | cons v l' ih =>
        simp only [List.mem_cons, forall_eq_or_imp] at l_mem
        rcases l_mem with ⟨v_mem, l'_mem⟩
        rw [w_eq]
        have h_tail : l'.flatten ∈ L* := ih (l'.flatten) rfl l'_mem
        rcases h_tail with ⟨n, h_tail⟩
        exists n+1
        exists v
        constructor
        . exact v_mem
        . exists l'.flatten

-- TO DO: rechenregeln für sprachen
/-
- konkatenation ist rechts- und linksassoziativ
- K⁺ = K * K* = K* * K
- K* = K⁺ ∪ {ε} = (K\{e}})*
- Lⁿ * Lᵐ = Lⁿ⁺ᵐ (????)
-/

theorem kstar_subset (L : Language Sigma) : ∀ (n : Nat), L^n ⊆ L* := by
  intro n w w_mem
  cases n with
  | zero =>
    exists 0
  | succ n =>
    exists n+1

theorem first_power (L : Language Sigma) : L^1 = L := by
    apply Set.ext
    intro w
    constructor
    . intro w_mem
      rcases w_mem with ⟨v, v_mem, u, u_mem, w_eq⟩
      unfold Language.pow at u_mem
      rcases u_mem
      rw [epsilon_concat] at w_eq
      subst w_eq
      exact v_mem
    . intro w_mem
      exists w
      constructor
      . exact w_mem
      . exists []
        constructor
        . unfold Language.pow
          simp [Membership.mem]
        . symm
          apply epsilon_concat

theorem mul_eq_append (u v : Word Sigma) : u * v = u++v := by rfl

-- product rule for exponents
theorem add_exp [BEq Sigma] (L : Language Sigma) (m n : Nat) : (L^n) * L^m = L^(n+m) := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨v, v_mem, u, u_mem, w_eq⟩
    rw [Language.mem_pow] at v_mem u_mem
    rcases v_mem with ⟨l_v, v_eq, v_length, l_v_mem⟩
    rcases u_mem with ⟨l_u, u_eq, u_length, l_u_mem⟩
    rw [Language.mem_pow]
    exists l_v*l_u
    constructor
    . rw [mul_eq_append]
      subst w v u
      rw [List.flatten_append]
      rfl
    . constructor
      . rw [mul_eq_append]
        rw [List.length_append]
        subst v_length u_length
        rfl
      . intro x x_mem
        rw [mul_eq_append] at x_mem
        have x_mem_l : ∀ (u : Word Sigma), u ∈ l_v++l_u → u ∈ L := by
          intro y y_mem
          rw [List.mem_append] at y_mem
          rcases y_mem with inl | inr
          . apply l_v_mem; exact inl
          . apply l_u_mem; exact inr
        apply x_mem_l
        exact x_mem
  . intro w_mem
    rw [Language.mem_pow] at w_mem
    rcases w_mem with ⟨l, l_eq, l_len, b⟩
    exists (l.take n).flatten
    constructor
    . rw [Language.mem_pow]
      exists l.take n
      constructor
      . rfl
      . constructor
        . simp_all
        . intro z z_mem
          have z_mem_l : z ∈ l := by apply List.mem_of_mem_take z_mem
          apply b z z_mem_l
    . exists (l.extract n).flatten
      constructor
      . rw [Language.mem_pow]
        exists l.extract n
        constructor
        . rfl
        . constructor
          . simp_all
          . intro z z_mem
            have z_mem_l : z ∈ l := by
              simp at z_mem
              have mem_drop : z ∈ (List.drop n l) := List.mem_of_mem_take z_mem
              apply List.mem_of_mem_drop mem_drop
            apply b z z_mem_l
      . subst w
        rw [mul_eq_append]
        rw [← List.flatten_append]
        apply congrArg
        simp
        rw [← List.length_drop]
        conv => right; right; rw [List.take_length]
        rw [List.take_append_drop]

-- gleicher beweis wie in übung nur andersrum?
theorem kstar_plus (L : Language Sigma) : L⁺ = L* * L := by
  sorry

-- concatenation of languages is distributive over union
theorem distr_concat_union_l (L₁ L₂ L₃ : Language Sigma) : (L₁ ∪ L₂) * L₃ = (L₁ * L₃) ∪ (L₂ * L₃) := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
    cases u_mem with
    | inl u_mem =>
      apply Or.inl
      exists u
      constructor
      . exact u_mem
      . exists v
    | inr u_mem =>
      apply Or.inr
      exists u
      constructor
      . exact u_mem
      . exists v
  . intro w_mem
    cases w_mem with
    | inl w_mem =>
      rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
      exists u
      constructor
      . apply Or.inl
        exact u_mem
      . exists v
    | inr w_mem =>
      rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
      exists u
      constructor
      . apply Or.inr
        exact u_mem
      . exists v

theorem distr_concat_union_r (L₁ L₂ L₃ : Language Sigma) : L₁ * (L₂ ∪ L₃) = (L₁ * L₂) ∪ (L₁ * L₃) := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨v, v_mem, x, x_mem, w_eq⟩
    cases x_mem with
    | inl x_mem =>
      apply Or.inl
      exists v
      constructor
      . exact v_mem
      . exists x
    | inr x_mem =>
      apply Or.inr
      exists v
      constructor
      exact v_mem
      exists x
  . intro w_mem
    cases w_mem with
    | inl w_mem =>
      rcases w_mem with ⟨v, v_mem, x, x_mem, w_eq⟩
      exists v
      constructor
      . exact v_mem
      . exists x
        constructor
        . apply Or.inl x_mem
        . exact w_eq
    | inr w_mem =>
      rcases w_mem with ⟨v, v_mem, x, x_mem, w_eq⟩
      exists v
      constructor
      . exact v_mem
      . exists x
        constructor
        . apply Or.inr
          exact x_mem
        . exact w_eq

theorem L_eps_mul : ∀ (L : Language Sigma), L ≠ L_empty → L_eps * L = L := by
  intro L ln
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨v, v_mem, u, u_mem, _, _⟩
    unfold L_eps at v_mem
    cases v_mem
    rw [concat_epsilon]
    exact u_mem
  . intro w_mem
    unfold L_eps
    exists []
    constructor
    . trivial
    . exists w

theorem mul_L_eps : ∀ (L : Language Sigma), L ≠ L_empty → L * L_eps = L := by
  intro L ln
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨v, v_mem, u, u_mem, _, _⟩
    unfold L_eps at u_mem
    cases u_mem
    rw [epsilon_concat]
    exact v_mem
  . intro w_mem
    unfold L_eps
    exists w
    constructor
    . exact w_mem
    . exists []
      rw [epsilon_concat]
      simp
      trivial

-- The empty language ∅ is an annihilating element for concatenation.
-- Since concatenation is not a commutative operation, we need a proof for ∅ * l = ∅ and for L * ∅ = ∅:
theorem empty_mul : ∀ (L : Language Sigma), L_empty * L = L_empty := by
  intro L
  unfold L_empty
  apply funext
  intro w
  simp
  intro h
  rcases h with ⟨u, u_mem, v, v_mem, h⟩
  contradiction

theorem mul_empty : ∀ (L : Language Sigma), L * L_empty = L_empty := by
  intro L
  unfold L_empty
  apply funext
  intro w
  simp
  intro h
  rcases h with ⟨u, u_mem, v, v_mem, h⟩
  contradiction

-- All powers of ∅ (except ∅⁰) are ∅.
theorem succ_pow_empty : ∀ n, n > 0 → Language.pow L_empty n = @L_empty Sigma := by
  intro n n₁
  unfold Language.pow
  cases n₁ with
  | refl =>
    simp
    unfold L_empty
    apply empty_mul
  | step =>
    simp
    apply empty_mul
