import FormaleSystemeInLean.LectureAndExercise.lecture1

/-def Set (α : Type u) := α -> Prop

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

-- Set extensionality: Two sets are equal if they contain the same elements. This is not something we define but we can prove it!
theorem Set.ext (X Y : Set α) : (∀ e, e ∈ X ↔ e ∈ Y) -> X = Y := by
  intro h; apply funext; intro e; apply propext; specialize h e; exact h


-- Words are merely lists over some alphabet Sigma. In fact, we do not even care about the type of Sigma.
abbrev Word (Sigma : Type u) := List Sigma

-- A language is in turn just a set of words.
abbrev Language (Sigma : Type u) := Set (Word Sigma)

-- From now on, we pick some alphabet Sigma. In fact, we do not even care about the type of Sigma. In can basically be anything.
variable {Sigma : Type u}

-- Let's define concatenation as multiplication.
instance : Mul (Word Sigma) where
  mul u v := List.append u v

-- Also for Languages
instance : Mul (Language Sigma) where
  mul L1 L2 := fun w => ∃ u ∈ L1, ∃ v ∈ L2, w = u * v

-- For languages we can also execute concatenation multiple times and define this via Powers.
def Language.pow (L : Language Sigma) : Nat -> Language Sigma
| .zero => fun w => w = []
| .succ n => L * L.pow n

instance : NatPow (Language Sigma) where
  pow L n := L.pow n

-- Finally we define the Kleene Star and notation for it.
def Language.kstar (L : Language Sigma) : Language Sigma := fun w => ∃ n, w ∈ L^n
postfix:max "*" => Language.kstar
-/

-- NOW FOR THE ACTUAL EXERCISE

variable {Sigma : Type u}

section Exercise1

  variable {L1 L2 L3 L4 : Language Sigma}

  theorem a : L1 ⊆ L3 -> L2 ⊆ L4 -> L1 ∪ L2 ⊆ L3 ∪ L4 := by
    intro sub1 sub2 w w_mem
    cases w_mem with
    | inl w_mem => apply Or.inl; apply sub1; exact w_mem
    | inr w_mem => apply Or.inr; apply sub2; exact w_mem

  theorem b : L1 ⊆ L3 -> L2 ⊆ L4 -> L1 * L2 ⊆ L3 * L4 := by
    intro sub1 sub2 w w_mem
    rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
    exists u
    constructor
    . exact sub1 _ u_mem
    exists v
    constructor
    . exact sub2 _ v_mem
    . exact w_eq

  theorem c : L1 ⊆ L3 -> L1* ⊆ L3* := by
    intro sub w w_mem
    -- In general it might be helpful to unfold definitions manually to see what is underneath.
    unfold Language.kstar at w_mem
    rcases w_mem with ⟨n, w_mem⟩
    exists n

    -- We show something more general now.
    have general_claim : ∀ n, L1^n ⊆ L3^n := by
      intro n
      induction n with
      | zero => intro w w_mem; exact w_mem
      | succ n ih =>
        intro w w_mem
        rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
        exists u
        constructor
        . apply sub; exact u_mem
        exists v
        constructor
        . apply ih; exact v_mem
        . exact w_eq

    apply general_claim
    exact w_mem

end Exercise1

section Exercise2

  theorem ex_2_a1 {L1 L2 L3 : Language Sigma} : L1 * (L2 ∪ L3) = L1 * L2 ∪ L1 * L3 := by
    apply Set.ext
    intro w
    constructor
    . intro w_mem
      rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
      cases v_mem with
      | inl v_mem =>
        apply Or.inl
        exists u
        constructor
        . exact u_mem
        exists v
      | inr v_mem =>
        apply Or.inr
        exists u
        constructor
        . exact u_mem
        exists v
    . intro w_mem
      cases w_mem with
      | inl w_mem =>
        rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
        exists u
        constructor
        . exact u_mem
        exists v
        constructor
        . apply Or.inl; exact v_mem
        . exact w_eq
      | inr w_mem =>
        rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
        exists u
        constructor
        . exact u_mem
        exists v
        constructor
        . apply Or.inr; exact v_mem
        . exact w_eq

  section a2

    def L1 : Language Char := fun w => w = ['a'] ∨ w = ['a','b']
    def L2 : Language Char := fun w => w = ['c']
    def L3 : Language Char := fun w => w = ['b', 'c']

    theorem ex_2_a2 : L1 * (L2 ∩ L3) ≠ (L1 * L2) ∩ (L1 * L3) := by
      let prob_word := ['a', 'b', 'c']

      have n_mem : prob_word ∉ L1 * (L2 ∩ L3) := by
        intro contra
        rcases contra with ⟨_, _, _, v_mem, _⟩
        simp only [Inter.inter, Membership.mem, L2, L3] at v_mem
        rcases v_mem with ⟨l, r⟩
        rw [l] at r
        simp at r

      have mem : prob_word ∈ (L1 * L2) ∩ (L1 * L3) := by
        constructor
        . exists ['a', 'b']; simp [Membership.mem, L1]; exists ['c']
        . exists ['a']; simp [Membership.mem, L1]; exists ['b', 'c']

      intro contra
      apply n_mem
      rw [contra]
      exact mem

    def L5 : Language Char := fun w => w = ['a', 'b'] ∨ w = ['a']
    def L6 : Language Char := fun w => w = ['a']
    def L4 : Language Char := fun w => w ∈ L6 * L5*
    def L7 : Language Char := fun w => w ∈ L5* * L6

    theorem ex_2_b : L4 = L7 := by
      unfold L4 L7 L5 L6
      apply Set.ext
      intro w
      constructor
      . intro w_mem
        simp [Membership.mem]

        sorry
      . sorry


    theorem ex_2d_1 : (@L_empty Sigma)* = L_eps := by
      unfold L_empty L_eps Language.kstar
      apply Set.ext
      intro w
      constructor
      . intro w_mem
        rcases w_mem with ⟨n, w_mem⟩
        cases n
        . trivial
        . exfalso
          rcases w_mem with ⟨v, v_mem, x, x_mem, w_eq⟩
          unfold Language.pow at x_mem
          exact v_mem
      . intro h
        apply Exists.intro 0
        trivial

    theorem ex_2d_2 : ((@L_empty Sigma) ∪ L)* = L* := by
      apply Set.ext
      intro w
      constructor
      . intro w_mem
        rcases w_mem with ⟨n, w_mem⟩
        exists n
        rw [Language.mem_pow] at w_mem
        rcases w_mem with ⟨l, w_eq, l_len, l_mem⟩
        rw [Language.mem_pow]
        exists l
        constructor
        . exact w_eq
        .
          sorry
      . intro w_mem
        rcases w_mem with ⟨n, w_mem⟩
        exists n
        rw [Language.mem_pow] at w_mem
        rcases w_mem with ⟨l, w_eq, l_len, l_mem⟩
        rw [Language.mem_pow]
        exists l
        constructor
        . exact w_eq
        . constructor
          . exact l_len
          . intro u u_mem
            apply Or.inr
            apply l_mem u; exact u_mem

    theorem ex_2f_2 [BEq Sigma] : ∀ (L : Language Sigma), L* * L* = L* := by
      intro L
      apply Set.ext
      intro w
      constructor
      . intro h1
        unfold Language.kstar at h1
        unfold Language.kstar
        rcases h1 with ⟨u, u_mem, v, v_mem, w_eq⟩
        rcases u_mem with ⟨n, u_mem⟩
        rcases v_mem with ⟨m, v_mem⟩
        exists m+n
        rw [← add_exp]
        exists u
        constructor
        . exact u_mem
        . exists v
      . intro w_mem
        exists w
        constructor
        . exact w_mem
        . exists []
          constructor
          . exists 0
          . rw [epsilon_concat]

    def L_ab : Language Char := fun w => w = ['a'] ∨ w = ['b']
    def L_a : Language Char := fun w => w = ['a']
    def L_b : Language Char := fun w => w = ['b']

    theorem ex_2c : L_ab* ≠ L_a* ∪  L_b* := by
      let ab_word := ['a','b']

      have n_mem : ab_word ∉ L_a* ∪ L_b* := by
        intro contra
        unfold ab_word at contra
        rcases contra with inl | inr
        . rw [Language.mem_kstar] at inl
          rcases inl with ⟨l, ab_eq, l_mem⟩
          unfold L_a at l_mem
          simp only [Membership.mem] at l_mem
          have b_mem_f : 'b' ∈ l.flatten := by
            grind
          have exists_sublist : ∃ v, v ∈ l ∧ 'b' ∈ v := by
            apply List.exists_of_mem_flatten b_mem_f
          have not_exists_sublist : ¬(∃ u ∈ l, 'b' ∈ u) := by
            intro contra
            rcases contra with ⟨u, u_mem, b_mem⟩
            have a : u = ['a'] := by apply l_mem u; exact u_mem
            grind
          contradiction
        . rw [Language.mem_kstar] at inr
          rcases inr with ⟨l, ab_eq, l_mem⟩
          unfold L_b at l_mem
          simp [Membership.mem] at l_mem
          have a_mem_f : 'a' ∈ l.flatten := by
            grind
          have exists_sublist : ∃ v, v ∈ l ∧ 'a' ∈ v := by
            apply List.exists_of_mem_flatten a_mem_f
          have not_exists_sublist : ¬(∃ u ∈ l, 'a' ∈ u) := by
            intro contra
            rcases contra with ⟨u, u_mem, a_mem⟩
            have b : u = ['b'] := by apply l_mem u; exact u_mem
            grind
          contradiction

      have mem : ab_word ∈ L_ab* := by
        unfold ab_word
        unfold Language.kstar L_ab
        exists 2
        rw [Language.mem_pow]
        exists [['a'],['b']]
        constructor
        . trivial
        . constructor
          . simp
          . intro w w_mem
            simp only [Membership.mem]
            simp_all

      intro contra
      apply n_mem
      symm at contra
      rw [contra]
      exact mem

theorem ex_2d_3 (L : Language Sigma) : (L*)* = L* := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rw [Language.mem_kstar] at w_mem
    rcases w_mem with ⟨l, w_eq, l_mem⟩
    --have u_flatten :

    sorry
  . intro w_mem
    exists 1
    rw [first_power]
    exact w_mem

theorem ex_2e (L₁ L₂ : Language Sigma) : (L₁* ∪ L₂*)* = (L₁ ∪ L₂)* := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rw [Language.mem_kstar] at w_mem
    rcases w_mem with ⟨l, w_eq, l_mem⟩
    -- die us in l können wiederum als liste von wörtern betrachtet werden
    have kstar_union (u : Word Sigma) : u ∈ L₁* ∪ L₂* → ∃ (l' : List (Word Sigma)), u = l'.flatten ∧ ((∀ v ∈ l', v ∈ L₁) ∨ (∀ v ∈ l', v ∈ L₂)) := by
      intro u_mem
      rcases u_mem with inl | inr
      . rw [Language.mem_kstar] at inl
        rcases inl with ⟨l', u_eq, l'_mem⟩
        exists l'
        constructor
        . exact u_eq
        . apply Or.inl
          exact l'_mem
      . rw [Language.mem_kstar] at inr
        rcases inr with ⟨l', u_eq, l'_mem⟩
        exists l'
        constructor
        . exact u_eq
        . apply Or.inr
          exact l'_mem

    rw [Language.mem_kstar]
    sorry
  . intro w_mem
    have L1_subset : L₁ ⊆ L₁* := by
        intro y y_mem
        exists 1
        rw [first_power]
        exact y_mem
    have L2_subset : L₂ ⊆ L₂* := by
      intro y y_mem
      exists 1
      rw [first_power]
      exact y_mem
    have union_subset : L₁ ∪ L₂ ⊆ L₁* ∪ L₂* := by
      intro x x_mem
      rcases x_mem with inl | inr
      . constructor
        apply L1_subset; exact inl
      . apply Or.inr
        apply L2_subset; exact inr
    rw [Language.mem_kstar] at w_mem
    rcases w_mem with ⟨l, w_eq, l_mem⟩
    rw [Language.mem_kstar]
    exists l
    constructor
    . exact w_eq
    . intro u u_mem
      have u_mem_union : u ∈ L₁ ∪ L₂ := by
        apply l_mem u; exact u_mem
      apply union_subset
      exact u_mem_union

  theorem ex_2f_1 (L : Language Sigma) : L * L* = L⁺ := by
    apply Set.ext
    intro w
    constructor
    . intro w_mem
      rcases w_mem with ⟨v, v_mem, u, u_mem, w_eq⟩
      rcases u_mem with ⟨n, u_mem⟩
      exists n+1
      constructor
      . simp
      . rw [pow_as_concat]
        . exists v
          constructor
          . exact v_mem
          . exists u
        . simp
    . intro w_mem
      rcases w_mem with ⟨n, gtz, w_mem⟩
      rw [pow_as_concat] at w_mem
      . rcases w_mem with ⟨v, v_mem, u, u_mem, w_eq⟩
        exists v
        constructor
        . exact v_mem
        . exists u
          constructor
          . exists n-1
          . exact w_eq
      . exact gtz

  theorem ex_2f_3 (L : Language Sigma) : L* ∪ L = L* := by
    apply Set.ext
    intro w
    constructor
    . intro w_mem
      rcases w_mem with inl | inr
      . exact inl
      . exists 1
        rw [first_power]; exact inr
    . intro w_mem
      apply Or.inl; exact w_mem

  end a2

  -- If you are up for a challenge, you can try to formalize and solve the remainder of Exercise 2.

end Exercise2
